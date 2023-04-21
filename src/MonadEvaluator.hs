{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TemplateHaskell #-}

module MonadEvaluator (
  Evaluator (..),
  MonadEvaluator (..),
  MetaEntry (..),
  SortMetaEntry (..),
  MetaContext (..),
  metas,
  sortMetas,
  emptyMetaContext,
  lookupMeta,
  lookupSortMeta,
  makeFnClosure',
) where

import Syntax
import Value

import Control.Lens hiding (Context, Empty, Refl, (:>))
import Control.Monad.Reader
import Data.IntMap qualified as IM

data MetaEntry
  = Unsolved [Binder]
  | Solved [Binder] (Term Ix)

data SortMetaEntry
  = UnsolvedSort
  | SolvedSort Relevance

data MetaContext = MetaContext
  { _metas :: IM.IntMap MetaEntry
  , _sortMetas :: IM.IntMap SortMetaEntry
  }

makeLenses ''MetaContext

emptyMetaContext :: MetaContext
emptyMetaContext = MetaContext {_metas = IM.empty, _sortMetas = IM.empty}

newtype Evaluator a = Evaluator {runEvaluator :: MetaContext -> a}
  deriving (Functor, Applicative, Monad, MonadReader MetaContext)

class Monad m => MonadEvaluator m where
  evaluate :: Evaluator a -> m a

lookupMeta :: MonadEvaluator m => MetaVar -> m (Maybe (Term Ix))
lookupMeta (MetaVar m) = evaluate $ do
  mctx <- ask
  case IM.lookup m (mctx ^. metas) of
    Nothing -> pure Nothing
    Just (Unsolved _) -> pure Nothing
    Just (Solved _ t) -> pure (Just t)

lookupSortMeta :: MonadEvaluator m => MetaVar -> m (Maybe Relevance)
lookupSortMeta (MetaVar m) = evaluate $ do
  mctx <- ask
  case IM.lookup m (mctx ^. sortMetas) of
    Nothing -> pure Nothing
    Just UnsolvedSort -> pure Nothing
    Just (SolvedSort s) -> pure (Just s)

instance MonadEvaluator Evaluator where
  evaluate = id

instance PushArgument Evaluator where
  push f = do
    ctx <- ask
    pure (\a -> runEvaluator (f a) ctx)

makeFnClosure' :: (MonadEvaluator m, ClosureApply Evaluator n cl val cod) => cl -> m (Closure n val cod)
makeFnClosure' c = evaluate (makeFnClosure c)
