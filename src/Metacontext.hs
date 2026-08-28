module Metacontext where

import Common
import Data.IORef
import qualified Data.IntMap as IM
import System.IO.Unsafe
import Value

--------------------------------------------------------------------------------

data MetaEntry = Solved Marker Val ~VTy | Unsolved Marker ~VTy

metaType :: MetaEntry -> VTy
metaType = \case
  Solved _ _ a -> a
  Unsolved _ a -> a

nextMeta :: IORef Int
nextMeta = unsafeDupablePerformIO $ newIORef 0
{-# NOINLINE nextMeta #-}

mcxt :: IORef (IM.IntMap MetaEntry)
mcxt = unsafeDupablePerformIO $ newIORef mempty
{-# NOINLINE mcxt #-}

lookupMeta :: MetaVar -> MetaEntry
lookupMeta (MetaVar m) = unsafeDupablePerformIO $ do
  ms <- readIORef mcxt
  case IM.lookup m ms of
    Just e -> pure e
    Nothing -> error "impossible"

reset :: IO ()
reset = do
  writeIORef nextMeta 0
  writeIORef mcxt mempty

anyUnsolved :: IO Bool
anyUnsolved = do
  ms <- readIORef mcxt
  pure $ any isUnsolved (IM.elems ms)
  where
    isUnsolved (Unsolved _ _) = True
    isUnsolved _ = False
