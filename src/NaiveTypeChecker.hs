module NaiveTypeChecker where

import Syntax

import Control.Monad.Except
import Control.Monad.State
import Data.Fix

data CheckerTrace
  = Check Context (Term Name) (Type Var) Int
  | Infer Context (Term Name) Int
  | Conv Context (Type Var) (Type Var) Int
  | Complete Int

instance Show CheckerTrace where
  show (Check gamma t tty i) =
    "Check: (" ++ show i ++ ") " ++ show gamma ++ " ⊢ " ++ prettyPrintTerm (map fst (types gamma)) t ++ " : "
      ++ prettyPrintTerm (map fst (types gamma)) tty
  show (Infer gamma t i) =
    "Infer: (" ++ show i ++ ") " ++ show gamma ++ " ⊢ " ++ prettyPrintTerm (map fst (types gamma)) t
  show (Conv gamma t t' i) =
    "Convert: (" ++ show i ++ ") " ++ show gamma ++ " ⊢ " ++ prettyPrintTerm (map fst (types gamma)) t ++ " ≡ "
      ++ prettyPrintTerm (map fst (types gamma)) t'
  show (Complete i) = "Completed item: " ++ show i

type Checker a = StateT ([CheckerTrace], Int) (Except (String, [CheckerTrace])) a

addTrace :: (Int -> CheckerTrace) -> Checker Int
addTrace t = do
  (trace, i) <- get
  put (t i : trace, i + 1)
  pure i

completeTrace :: Int -> Checker ()
completeTrace i = do
  (trace, curr) <- get
  put (Complete i : trace, curr)

throwErrorWithTrace :: String -> Checker a
throwErrorWithTrace e = do
  (trace, _) <- get
  throwError (e, trace)

data Var
  = Bound (Ix, Name)
  | Free Lvl

instance VarShowable Var where
  showsVar (Bound (Ix i, n)) _ = showString n . shows i
  showsVar (Free (Lvl l)) _ = showParen True (showString "free " . shows l)

whnf :: Term v -> Bool
whnf (U _) = True
whnf (Lambda {}) = True
whnf (Pi {}) = True
whnf Zero = True
whnf (Succ _) = True
whnf Nat = True
whnf (Exists {}) = True
whnf Empty = True
whnf Unit = True
whnf e = irrelevant e || neutral e

irrelevant :: Term v -> Bool
irrelevant (Pair {}) = True
irrelevant (Fst _) = True
irrelevant (Snd _) = True
irrelevant One = True
irrelevant (Refl _) = True
irrelevant (Transp {}) = True
irrelevant (CastRefl {}) = True
irrelevant _ = False

neutral :: Term v -> Bool
neutral (Var _) = True
neutral (App t _) = neutral t
neutral (NElim _ _ _ n) = neutral n
neutral (Abort {}) = True
neutral (Eq _ a _) | neutral a = True
neutral (Eq t Nat _) | neutral t = True
neutral (Eq Zero Nat t) = neutral t
neutral (Eq (Succ _) Nat t) = neutral t
neutral (Eq t (U Relevant) _) | neutral t = True
neutral (Eq Nat (U Relevant) t) = neutral t
neutral (Eq (Pi {}) (U Relevant) t) = neutral t
neutral (Cast Nat Nat _ t) = neutral t
neutral (Cast n _ _ _) | neutral n = True
neutral (Cast Nat n _ _) | neutral n = True
neutral (Cast (Pi {}) n _ _) | neutral n = True
neutral (Cast Nat (Pi {}) _ _) = True
neutral (Cast Nat (U _) _ _) = True
neutral (Cast (Pi {}) Nat _ _) = True
neutral (Cast (Pi {}) (U _) _ _) = True
neutral (Cast (U _) Nat _ _) = True
neutral (Cast (U _) (Pi {}) _ _) = True
neutral _ = False

subst :: Ix -> Term Var -> Term Var -> Term Var
subst x e (Var (Bound (x', _))) | x == x' = e
subst x e (Lambda x' a t) = Lambda x' (subst x e a) (subst (x + 1) e t)
subst x e (Pi s x' a b) = Pi s x' (subst x e a) (subst (x + 1) e b)
subst x e (Exists x' a b) = Exists x' (subst x e a) (subst (x + 1) e b)
subst x e (Let x' a t u) = Let x' (subst x e a) (subst x e t) (subst (x + 1) e u)
subst x e (Fix e') = Fix (fmap (subst x e) e')

shift :: Ix -> Term Var -> Term Var
shift i (Var (Bound (x, n))) | i <= x = Var (Bound (x + 1, n))
shift i (Lambda x a e) = Lambda x (shift i a) (shift (i + 1) e)
shift i (Pi s x a b) = Pi s x (shift i a) (shift (i + 1) b)
shift i (Exists x a b) = Exists x (shift i a) (shift (i + 1) b)
shift i (Let x' a t u) = Let x' (shift i a) (shift i t) (shift (i + 1) u)
shift i (Fix e) = Fix (fmap (shift i) e)

-- type Env = [Term Var]

eval :: Term Var -> Term Var
eval (Var x) = Var x
eval (U s) = U s
eval (Lambda x a e) = Lambda x a e
eval (App t u) =
  case eval t of
    Lambda _ _ e -> eval (subst 0 (eval u) e)
    t -> App t u
eval (Pi s x a b) = Pi s x a b
eval Zero = Zero
eval (Succ n) = Succ n
eval (NElim a t0 ts n) = recurse (eval n)
  where
    recurse :: Term Var -> Term Var
    recurse Zero = eval t0
    recurse (Succ n) =
      let vn = eval n
       in eval (App (App ts vn) (recurse vn))
    recurse n' = NElim a t0 ts n'
eval Nat = Nat
-- Cannot evaluate pairs (proof-irrelevant)
eval e@(Pair {}) = e
-- Cannot evaluate fst (proof-irrelevant)
eval e@(Fst {}) = e
-- Cannot evaluate snd (proof-irrelevant)
eval e@(Snd {}) = e
eval (Exists x a b) = Exists x a b
eval (Abort a t) = Abort a t
eval Empty = Empty
-- Cannot evaluate one (proof-irrelevant)
eval e@One = e
eval Unit = Unit
eval (Eq t a u) =
  case eval a of
    Pi s x a b -> Pi s x a (Eq (App t (Var (Bound (0, x)))) b (App u (Var (Bound (0, x)))))
    U Irrelevant -> Exists "_" (Pi Irrelevant "_" t u) (Pi Irrelevant "_" u t)
    U Relevant ->
      case (eval t, eval u) of
        (Nat, Nat) -> Unit
        (U s, U s') | s == s' -> Unit
        (Nat, Pi {}) -> Empty
        (Nat, U _) -> Empty
        (Pi {}, Nat) -> Empty
        (Pi {}, U _) -> Empty
        (U _, Nat) -> Empty
        (U _, Pi {}) -> Empty
        (U s, U s') | s /= s' -> Empty
        (Pi s _ a b, Pi s' _ a' b')
          | s == s' ->
            let va' = Cast a a' (Var (Bound (1, "$e"))) (Var (Bound (0, "$a")))
             in Exists
                  "$e"
                  (Eq a (U Relevant) a')
                  ( Pi
                      s
                      "$a"
                      (shift 0 a)
                      (Eq (shift 1 b) (U Relevant) (subst 0 va' (shift 1 b')))
                  )
        (t, u) -> Eq t (U Relevant) u
    Nat ->
      case (eval t, eval u) of
        (Zero, Zero) -> Unit
        (Zero, Succ _) -> Empty
        (Succ _, Zero) -> Empty
        (Succ m, Succ n) -> eval (Eq m Nat n)
        (m, n) -> Eq m Nat n
    a -> Eq t a u
-- Cannot evaluate refl (proof-irrelevant)
eval e@(Refl {}) = e
-- Cannot evaluate transp (proof-irrelevant)
eval e@(Transp {}) = e
eval (Cast a b e t) =
  case (eval a, eval b, eval t) of
    (Nat, Nat, Zero) -> Zero
    (Nat, Nat, Succ n) -> Succ (eval (Cast Nat Nat e n))
    (U s, U s', a) | s == s' -> a
    (Pi _ x a b, Pi _ _ a' b', f) ->
      Lambda x a (Cast b (subst 0 (Cast a a' (Fst e) (Var (Bound (0, x)))) b') (Snd e) (App f (Var (Bound (0, x)))))
    (a, b, t) -> Cast a b e t
-- Cannot evaluate castrefl (proof-irrelevant)
eval e@(CastRefl {}) = e
eval (Let _ _ t u) = eval (subst 0 (eval t) u)

type Types = [(Name, (Relevance, Type Var))]

data Context = Context
  { types :: Types,
    lvl :: Lvl
  }

instance Show Context where
  show gamma =
    let typeStrings = foldr (\(_, (_, t)) ls -> prettyPrintTerm ls t : ls) [] (types gamma)
        showAsTuple [] = ""
        showAsTuple [x] = x
        showAsTuple (x:xs) = x ++ ", " ++ showAsTuple xs
     in "(" ++ showAsTuple (reverse (zipWith (\t (x, _) -> x ++ " : " ++ t) typeStrings (types gamma))) ++ ")"

emptyContext :: Context
emptyContext =
  Context
    { types = [],
      lvl = 0
    }

bind :: Name -> Relevance -> Type Var -> Context -> Context
bind x s tty ctx =
  ctx
    { types = (x, (s, tty)) : types ctx,
      lvl = 1 + lvl ctx
    }

bindWithVar :: Name -> Relevance -> Type Var -> Context -> (Context, Term Var)
bindWithVar x s tty ctx = (bind x s tty ctx, Var (Free (lvl ctx)))

lookupFree :: Lvl -> Context -> Type Var
lookupFree l gamma =
  let Lvl index = lvl gamma - l - 1
      (_, (_, ty)) = types gamma !! index
   in ty

lookupBound :: Ix -> Context -> Type Var
lookupBound (Ix x) gamma =
  let (_, (_, ty)) = types gamma !! x
   in ty

-- Precondition for bi-directional type-directed conversion checking:
-- (1) The two input terms are both well-typed
--     at the same type [A].
-- (2) (For the Nf variants) both terms are in weak head normal form
typeEq :: Context -> Type Var -> Type Var -> Checker ()
typeEq gamma t t' = do
  tid <- addTrace (Conv gamma t t')
  typeNfEq gamma (eval t) (eval t')
  completeTrace tid

typeNfEq :: Context -> Type Var -> Type Var -> Checker ()
typeNfEq _ (U s) (U s')
  | s == s' = pure ()
  | otherwise = throwErrorWithTrace "Cannot convert between universes"
typeNfEq gamma (Pi s x a b) (Pi s' _ a' b')
  | s == s' = do
    typeEq gamma a a'
    typeEq (bind x s a gamma) b b'
typeNfEq _ Nat Nat = pure ()
typeNfEq _ Empty Empty = pure ()
typeNfEq _ Unit Unit = pure ()
typeNfEq gamma (Eq t a u) (Eq t' a' u') = do
  -- TODO: This unnecessarily re-evaluates some terms to whnf
  typeEq gamma a a'
  convTypedNf gamma t t' a
  convTypedNf gamma u u' a
typeNfEq gamma t t' = void (convStruct gamma t t')

convStructNf :: Context -> Term Var -> Term Var -> Checker (Type Var)
convStructNf gamma n n' = eval <$> convStruct gamma n n'

convStruct :: Context -> Term Var -> Term Var -> Checker (Type Var)
convStruct gamma (Var (Bound (x, _))) (Var (Bound (x', _)))
  | x == x' = pure (lookupBound x gamma)
convStruct gamma (Var (Free x)) (Var (Free x'))
  | x == x' = pure (lookupFree x gamma)
convStruct gamma (App n u) (App n' u') = do
  nty <- convStructNf gamma n n'
  case nty of
    Pi s _ a b -> do
      when (s == Relevant) (convTyped gamma u u' a)
      pure (eval (subst 0 u b))
    _ -> throwErrorWithTrace "BUG: Ill-typed application term"
convStruct gamma (NElim a t0 ts n) (NElim a' t0' ts' n') = do
  -- We already know the type of n and n'
  void (convStruct gamma n n')
  aty <- convStructNf gamma a a'
  case aty of
    Pi _ _ _ (U s) -> do
      convTyped gamma t0 t0' (App a Zero)
      convTypedNf gamma ts ts' (Pi Relevant "$n" Nat (Pi s "_" (App a (Var (Bound (0, "$n")))) (App a (Var (Bound (1, "$n"))))))
      pure (App a n)
    _ -> throwErrorWithTrace "BUG: Ill-typed nat eliminator"
convStruct gamma (Abort a _) (Abort a' _) = do
  typeEq gamma a a'
  -- We know the aborted terms are both of type [⊥], and therefore
  -- definitionally equal
  pure a
convStruct gamma (Cast a b _ t) (Cast a' b' _ t') = do
  typeEq gamma a a'
  typeEq gamma b b'
  convTyped gamma t t' a
  pure b
convStruct gamma t t' =
  throwErrorWithTrace
    ( "Type conversion ["
        ++ prettyPrintTerm (map fst (types gamma)) t
        ++ " ≡ "
        ++ prettyPrintTerm (map fst (types gamma)) t'
        ++ "] failed"
    )

convTyped :: Context -> Term Var -> Term Var -> Type Var -> Checker ()
convTyped gamma t t' ty = convTypedNf gamma t t' (eval ty)

convTypedNf :: Context -> Term Var -> Term Var -> Type Var -> Checker ()
convTypedNf gamma (Lambda x _ e) (Lambda _ _ e') (Pi s _ a b) =
  convTyped (bind x s a gamma) e e' b
-- Eta rule for pi type
convTypedNf gamma t t' (Pi s x a b) =
  let (gamma', xvar) = bindWithVar x s a gamma
   in convTyped gamma' (App t xvar) (App t' xvar) b
convTypedNf _ Zero Zero Nat = pure ()
convTypedNf gamma (Succ n) (Succ n') Nat = convTypedNf gamma n n' Nat
-- We ignore eta expansion for sum types to avoid exponential expansion (TODO: check)
convTypedNf _ _ _ (Exists {}) = pure ()
convTypedNf _ (Fst _) _ _ = pure ()
convTypedNf _ _ (Fst _) _ = pure ()
convTypedNf _ (Snd _) _ _ = pure ()
convTypedNf _ _ (Snd _) _ = pure ()
convTypedNf _ _ _ Unit = pure ()
convTypedNf _ _ _ (Eq {}) = pure ()
convTypedNf _ (Transp {}) _ _ = pure ()
convTypedNf _ _ (Transp {}) _ = pure ()
convTypedNf gamma t t' (U _) = typeEq gamma t t'
convTypedNf gamma t t' _ = void (convStruct gamma (eval t) (eval t'))

inferVar :: Types -> Name -> Checker (Term Var, Relevance, Type Var)
inferVar types name = do
  (i, s, ty) <- find types name
  pure (Var (Bound (i, name)), s, ty)
  where
    find :: Types -> Name -> Checker (Ix, Relevance, Type Var)
    find [] name = throwErrorWithTrace ("Variable not in scope: \"" ++ name ++ "\"")
    find ((x, (s, a)) : types) x'
      | x == x' = pure (0, s, a)
      | otherwise = do
        (i, s, a) <- find types x'
        pure (i + 1, s, a)

infer :: Context -> Term Name -> Checker (Term Var, Relevance, Type Var)
infer gamma e = do
  tid <- addTrace (Infer gamma e)
  infer' gamma e <* completeTrace tid

infer' :: Context -> Term Name -> Checker (Term Var, Relevance, Type Var)
infer' gamma (Var x) = inferVar (types gamma) x
infer' _ (U s) = pure (U s, Relevant, U Relevant)
infer' gamma (Lambda x a e) = do
  (a, s) <- checkType gamma a
  (e, s', b) <- infer (bind x s a gamma) e
  pure (Lambda x a e, s', Pi s x a b)
infer' gamma (App t u) = do
  (t, s, tty) <- infer gamma t
  case tty of
    Pi _ _ a b -> do
      u <- check gamma u a
      let vu = eval u
      pure (App t u, s, eval (subst 0 vu b))
    _ -> throwErrorWithTrace "Expected pi type"
infer' gamma (Pi s x a b) = do
  a <- check gamma a (U s)
  (b, s') <- checkType (bind x s a gamma) b
  pure (Pi s x a b, Relevant, U s')
infer' _ Zero = pure (Zero, Relevant, Nat)
infer' gamma (Succ n) = do
  n <- check gamma n Nat
  pure (Succ n, Relevant, Nat)
infer' gamma (NElim a t0 ts n) = do
  (a, _, aty) <- infer gamma a
  case aty of
    Pi _ _ Nat (U s) -> do
      t0 <- check gamma t0 (App a Zero)
      ts <- check gamma ts (Pi Relevant "n" Nat (Pi s "_" (App a (Var (Bound (0, "n")))) (App a (Succ (Var (Bound (1, "n")))))))
      n <- check gamma n Nat
      pure (NElim a t0 ts n, s, App a n)
    _ -> throwErrorWithTrace "Expected type family in ℕ recursor"
infer' _ Nat = pure (Nat, Relevant, U Relevant)
infer' _ (Pair {}) = throwErrorWithTrace "Cannot infer type of existential pair"
infer' gamma (Fst p) = do
  (p, _, pty) <- infer gamma p
  case pty of
    Exists _ a _ -> pure (Fst p, Irrelevant, a)
    _ -> throwErrorWithTrace "Expected exists type in first projection"
infer' gamma (Snd p) = do
  (p, _, pty) <- infer gamma p
  case pty of
    Exists _ _ b -> do
      let vfst = eval (Fst p)
      pure (Snd p, Irrelevant, eval (subst 0 vfst b))
    _ -> throwErrorWithTrace "Expected exists type in second projection"
infer' gamma (Exists x a b) = do
  a <- check gamma a (U Irrelevant)
  b <- check (bind x Irrelevant a gamma) b (U Irrelevant)
  pure (Exists x a b, Relevant, U Irrelevant)
infer' gamma (Abort a t) = do
  (a, s) <- checkType gamma a
  t <- check gamma t Empty
  pure (Abort a t, s, a)
infer' _ Empty = pure (Empty, Relevant, U Irrelevant)
infer' _ One = pure (One, Irrelevant, Unit)
infer' _ Unit = pure (Unit, Relevant, U Irrelevant)
infer' gamma (Eq t a u) = do
  a <- check gamma a (U Relevant)
  t <- check gamma t a
  u <- check gamma u a
  pure (Eq t a u, Relevant, U Irrelevant)
infer' gamma (Refl t) = do
  (t, s, a) <- infer gamma t
  unless (s == Relevant) (throwErrorWithTrace "Can only form equality type on proof-relevant types")
  pure (Refl t, Irrelevant, Eq t a t)
infer' gamma (Transp t b u t' e) = do
  (t, s, a) <- infer gamma t
  unless (s == Relevant) (throwErrorWithTrace "Can only transport along equality of proof-relevant types")
  t' <- check gamma t' a
  b <- check gamma b (Pi Relevant "$x" a (Pi Irrelevant "_" (Eq (shift 0 t) (shift 0 a) (Var (Bound (0, "$x")))) (U Irrelevant)))
  u <- check gamma u (App (App b t) (Refl t))
  e <- check gamma e (Eq t a t')
  pure (Transp t b u t' e, Irrelevant, App (App b t') e)
infer' gamma (Cast a b e t) = do
  (a, s) <- checkType gamma a
  (b, s') <- checkType gamma b
  unless (s == s') (throwErrorWithTrace "Cast types must live in the same universe")
  e <- check gamma e (Eq a (U s) b)
  t <- check gamma t a
  pure (Cast a b e t, s, b)
infer' gamma (CastRefl a t) = do
  (a, _) <- checkType gamma a
  t <- check gamma t a
  pure (CastRefl a t, Irrelevant, Eq t a (Cast a a (Refl t) t))
infer' gamma (Let x a t u) = do
  (a, s) <- checkType gamma a
  t <- check gamma t a
  -- TODO: Pretty sure this is wrong as-is
  (u, s, uty) <- infer (bind x s a gamma) u
  pure (Let x a t u, s, uty)

checkType :: Context -> Type Name -> Checker (Term Var, Relevance)
checkType gamma t = do
  (t, _, tty) <- infer gamma t
  case tty of
    U s -> pure (t, s)
    _ -> throwErrorWithTrace "Expected type, but found term."

check :: Context -> Term Name -> Type Var -> Checker (Term Var)
check gamma t tty = do
  tid <- addTrace (Check gamma t tty)
  check' gamma t tty <* completeTrace tid

check' :: Context -> Term Name -> Type Var -> Checker (Term Var)
check' gamma t tty =
  case (t, eval tty) of
    (Pair t u, Exists _ a b) -> do
      t <- check gamma t a
      u <- check gamma u (eval (subst 0 t b))
      pure (Pair t u)
    (Let x a t u, uty) -> do
      (a, s) <- checkType gamma a
      t <- check gamma t a
      -- TODO: Pretty sure this is wrong as-is
      u <- check (bind x s a gamma) u uty
      pure (Let x a t u)
    (t, tty) -> do
      (t, _, tty') <- infer gamma t
      typeEq gamma tty tty'
      pure t
