{-|
This module exports a safe-subset of "DCLabel.Core",
implementing Disjunction Category Labels. 
The exported functions and constructors may be used by  
untrusted code, guaranteeing that they cannot perform
anything unsafe.
-}


module DCLabel.Safe ( -- * DC Labels with EDSL
	              join, meet, top, bottom, canflowto
	            , Label, DCLabel, secrecy, integrity
                    , principal
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
                    , newPriv, newTCBPriv
                    ) where

import DCLabel.Core
import DCLabel.NanoEDSL









