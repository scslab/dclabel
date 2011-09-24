{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 702)
{-# LANGUAGE Trustworthy #-}
#else
#warning "This module is not using SafeHaskell"
#endif
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module DCLabel.Secrecy ( SLabel(..) ) where

import DCLabel.Core

-- | A secrecy-only DC label.
newtype SLabel = MkSLabel DCLabel
	deriving (Eq, Show, Read)

instance ToLNF SLabel where
	toLNF (MkSLabel l) = MkSLabel (toLNF l)

instance Lattice SLabel where
  bottom = MkSLabel bottom
  top = MkSLabel top
  join (MkSLabel l1) (MkSLabel l2) = MkSLabel $
    join l1 { integrity = emptyLabel } l2 { integrity = emptyLabel }
  meet (MkSLabel l1) (MkSLabel l2) = MkSLabel $ 
    meet l1 { integrity = emptyLabel } l2 { integrity = emptyLabel }
  canflowto (MkSLabel l1) (MkSLabel l2) =
    canflowto l1 { integrity = emptyLabel } l2 { integrity = emptyLabel }

instance RelaxedLattice SLabel where
  canflowto_p p (MkSLabel l1) (MkSLabel l2) =
    canflowto_p p l1 { integrity = emptyLabel } l2 { integrity = emptyLabel }
