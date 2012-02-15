{-|
This module exports an unsafe-subset of "DCLabel.Core",
implementing Disjunction Category Labels. 
A subset of the exported functions and constructors
shoul not be exposed to untrusted code; instead, 
untursted code should import the "DCLabel.Safe"
module.
-}


module DCLabel.TCB ( module DCLabel.Core
                   , module DCLabel.NanoEDSL
                   ) where

import DCLabel.Core
import DCLabel.NanoEDSL
