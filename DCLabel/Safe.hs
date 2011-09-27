{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 702)
{-# LANGUAGE Trustworthy #-}
#else
#warning "This module is not using SafeHaskell"
#endif
{-|
This module exports a safe-subset of "DCLabel.Core",
implementing Disjunction Category Labels. 
The exported functions and constructors may be used by  
untrusted code, guaranteeing that they cannot perform
anything unsafe.
-}


module DCLabel.Safe ( -- * DC Labels with EDSL
	              join, meet, top, bottom, canflowto
	            , Label(..), DCLabel(..), Disj(..), Conj(..)
                    , principal, singleton
                    , listToDisj, disjToList
		    , listToLabel, labelToList
                    , (.\/.), (./\.)
                    , (<>), (><)
                    , newDC
                      -- * Privilegies 
                    , TCBPriv, Priv
                    , canflowto_p
                    , delegatePriv
                    , canDelegate, owns
                    , newPriv, NewPriv, newTCBPriv
                    ) where

import DCLabel.Core

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 702)
import safe DCLabel.NanoEDSL
#else
import DCLabel.NanoEDSL
#endif
