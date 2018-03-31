{-# LANGUAGE NoImplicitPrelude #-}

module MonadTrans where

import Monad

class MonadTrans t where
  lift :: Monad m => m a -> t m a

