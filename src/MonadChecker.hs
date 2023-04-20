{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module MonadChecker (
  CheckState (..),
  emptyCheckState,
  Checker (..),
  freshMeta,
  freshSortMeta,
  freshTag,
  addSolution,
  addSortSolution,
) where

import MonadEvaluator
import PrettyPrinter
import Syntax

import Control.Lens hiding (Context, Empty, Refl, (:>))
import Control.Monad.Except
import Control.Monad.Oops
import Control.Monad.State
import Data.IntMap qualified as IM

newtype Checker e a = Checker {runChecker :: ExceptT e (State CheckState) a}
  deriving (Functor, Applicative, Monad, MonadState CheckState, MonadError e)

instance MonadEvaluator (Checker e) where
  evaluate e = gets (runEvaluator e . _metaCtx)

-- Ideally, this would be split into a distinct MetaContext and CheckState.
data CheckState = CheckState
  { _fresh :: MetaVar
  , _freshSort :: MetaVar
  , _nextTag :: Tag
  , _metaCtx :: MetaContext
  }

makeLenses ''CheckState

instance Show CheckState where
  show mctx =
    "{ "
      ++ showEntries showMeta (IM.assocs (mctx ^. metaCtx . metas))
      ++ " }"
      ++ "\n{ "
      ++ showEntries showSort (IM.assocs (mctx ^. metaCtx . sortMetas))
      ++ " }"
    where
      showMeta :: (Int, MetaEntry) -> String
      showMeta (m, Unsolved _) = "?" ++ show m
      showMeta (m, Solved ns t) =
        "?"
          ++ show m
          ++ " := "
          ++ prettyPrintTerm ns t

      showSort :: (Int, SortMetaEntry) -> String
      showSort (m, UnsolvedSort) = "?" ++ show m
      showSort (m, SolvedSort s) =
        "?"
          ++ show m
          ++ " := "
          ++ show s

      showEntries :: (a -> String) -> [a] -> String
      showEntries _ [] = ""
      showEntries f [e] = f e
      showEntries f (es :> e) = showEntries f es ++ "\n, " ++ f e

emptyCheckState :: CheckState
emptyCheckState = CheckState {_fresh = 0, _freshSort = 0, _nextTag = 0, _metaCtx = emptyMetaContext}

freshMeta :: [Binder] -> Checker (Variant e) MetaVar
freshMeta ns = do
  mv@(MetaVar v) <- gets (^. fresh)
  fresh += 1
  modify (metaCtx . metas %~ IM.insert v (Unsolved ns))
  pure mv

freshSortMeta :: Checker (Variant e) MetaVar
freshSortMeta = do
  mv@(MetaVar v) <- gets (^. freshSort)
  freshSort += 1
  modify (metaCtx . sortMetas %~ IM.insert v UnsolvedSort)
  pure mv

freshTag :: Checker (Variant e) Tag
freshTag = do
  tag <- gets (^. nextTag)
  nextTag += 1
  pure tag
addSolution :: MetaVar -> Term Ix -> Checker (Variant e) ()
addSolution (MetaVar v) solution = do
  entry <- gets (IM.lookup v . (^. metaCtx . metas))
  case entry of
    Nothing -> error "BUG: IMPOSSIBLE!"
    -- We only solve metas with definitionally unique solutions, so if we
    -- re-solve the meta, we must have something equivalent to what we already
    -- had, so we do nothing (ideally this will never even happen)
    Just (Solved {}) -> pure ()
    Just (Unsolved ns) -> modify (metaCtx . metas %~ IM.insert v (Solved ns solution))

addSortSolution :: MetaVar -> Relevance -> Checker (Variant e) ()
addSortSolution (MetaVar v) solution = do
  entry <- gets (IM.lookup v . (^. metaCtx . sortMetas))
  case entry of
    Nothing -> error "BUG: IMPOSSIBLE!"
    Just (SolvedSort _) -> pure ()
    Just UnsolvedSort -> modify (metaCtx . sortMetas %~ IM.insert v (SolvedSort solution))
