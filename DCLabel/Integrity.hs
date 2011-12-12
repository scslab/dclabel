{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 702)
{-# LANGUAGE Trustworthy #-}
#endif
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module DCLabel.Integrity ( ILabel(..) ) where

import DCLabel.Core

-- | An integrity-only DC label.
newtype ILabel = MkILabel DCLabel
	deriving (Eq, Show, Read)

instance ToLNF ILabel where
	toLNF (MkILabel l) = MkILabel (toLNF l)

instance Lattice ILabel where
  bottom = MkILabel bottom
  top = MkILabel top
  join (MkILabel l1) (MkILabel l2) = MkILabel $
    join l1 { secrecy = emptyLabel } l2 { secrecy = emptyLabel }
  meet (MkILabel l1) (MkILabel l2) = MkILabel $ 
    meet l1 { secrecy = emptyLabel } l2 { secrecy = emptyLabel }
  canflowto (MkILabel l1) (MkILabel l2) =
    canflowto l1 { secrecy = emptyLabel } l2 { secrecy = emptyLabel }

instance RelaxedLattice ILabel where
  canflowto_p p (MkILabel l1) (MkILabel l2) =
    canflowto_p p l1 { secrecy = emptyLabel } l2 { secrecy = emptyLabel }
