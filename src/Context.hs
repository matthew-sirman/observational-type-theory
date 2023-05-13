module Context (
  Types,
  Context (..),
  names,
  emptyContext,
  bind,
  bindR,
  bindP,
  define,
) where

import Syntax
import Value

type Types = [(Binder, (Relevance, VTy))]

data Context = Context
  { env :: Env
  , types :: Types
  , lvl :: Lvl
  }

names :: Context -> [Binder]
names = map fst . types

emptyContext :: Context
emptyContext = Context {env = [], types = [], lvl = 0}

bind :: Binder -> Relevance -> VTy -> Context -> Context
bind x s tty ctx =
  let s' = case s of
        Relevant -> Relevant
        Irrelevant -> Irrelevant
        _ -> Relevant
   in ctx
        { types = types ctx :> (x, (s, tty))
        , lvl = lvl ctx + 1
        , -- This is slightly imprecise -- we might have a sort meta which resolves to
          -- irrelevant, and still have a relevant variable in the context. This doesn't
          -- break anything, but could possibly lead to bugs which do not throw runtime
          -- errors (making them harder to find)
          env = extend s' (lvl ctx) (env ctx)
        }

bindR, bindP :: Binder -> VTy -> Context -> Context
bindR x = bind x Relevant
bindP x = bind x Irrelevant

define :: Binder -> EnvEntry -> Relevance -> VTy -> Context -> Context
define x t s tty ctx =
  ctx
    { types = types ctx :> (x, (s, tty))
    , lvl = lvl ctx + 1
    , env = env ctx :> (Defined, t)
    }
