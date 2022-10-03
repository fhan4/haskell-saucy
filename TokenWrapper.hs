{-# LANGUAGE ImplicitParams, ScopedTypeVariables, Rank2Types,
             ConstraintKinds
  #-}


module TokenWrapper where

import ProcessIO
import StaticCorruptions
import Multisession

import Safe
import Control.Concurrent.MonadIO
import Control.Monad (forever)

import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map



type MonadAdversaryToken m = (MonadAdversary m,
                              -- ?sendToken :: m () -> m (),
                              ?getToken :: m Int)

-- sendToken :: MonadAdversaryToken m => m () -> m ()
-- sendToken = ?sendToken

getToken :: MonadAdversaryToken m => m Int
getToken = ?getToken



runTokenA :: MonadAdversary m => (MonadAdversaryToken m => Adversary (SttCruptZ2A a b) a2z p2a a2p f2a a2f m)
          -> Adversary (SttCruptZ2A a b) a2z p2a a2p f2a a2f m
runTokenA a (z2a, a2z) (p2a, a2p) (f2a, a2f) = do

  tokens <- newIORef 0

  z2a' <- newChan

  fork $ forever $ do
    mf <- readChan z2a
    case mf of
      SttCruptZ2A_TokenSend -> do
        modifyIORef tokens (+1)
        ?pass
      _ -> writeChan z2a' mf

  let _getToken = do
        tk <- readIORef tokens
        return tk

  let ?getToken = _getToken in
    a (z2a', a2z) (p2a, a2p) (f2a, a2f)
  return ()

dummyAdversaryToken :: MonadAdversaryToken m => Adversary (SttCruptZ2A b d) (SttCruptA2Z a c) a b c d m
dummyAdversaryToken (z2a, a2z) (p2a, a2p) (f2a, a2f) = dummyAdversary (z2a, a2z) (p2a, a2p) (f2a, a2f)