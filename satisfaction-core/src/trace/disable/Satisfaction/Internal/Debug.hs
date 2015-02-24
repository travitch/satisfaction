module Satisfaction.Internal.Debug ( traceIO ) where

traceIO :: String -> IO ()
traceIO _ = return ()
{-# INLINE traceIO #-}
