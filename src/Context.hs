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
  ctx
    { types = types ctx :> (x, (s, tty))
    , lvl = lvl ctx + 1
    , env = env ctx :> (Bound, VVar (lvl ctx))
    }

bindR, bindP :: Binder -> VTy -> Context -> Context
bindR x = bind x Relevant
bindP x = bind x Irrelevant

define :: Binder -> Val -> Relevance -> VTy -> Context -> Context
define x t s tty ctx =
  ctx
    { types = types ctx :> (x, (s, tty))
    , lvl = lvl ctx + 1
    , env = env ctx :> (Defined, t)
    }
