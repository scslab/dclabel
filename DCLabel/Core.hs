{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 702)
{-# LANGUAGE SafeImports #-}
#endif
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-|
This module implements Disjunction Category labels.

A DCLabel is a pair of 'secrecy' and 'integrity' category sets (of type
'Label').  A category set (of type 'Conj') is a conjunction of categories
(of type 'Disj').  Each category, in turn, is a disjunction of 'Principal's,
where a 'Principal' is just a 'String' whose meaning is up to the application.

A category imposes an information flow restriction. In the case of secrecy,
a category restricts who can read, receive, or propagate the information,
while in the case of integrity it restricts who can modify a piece of
data. The principals constructing a category are said to /own/ the category.

For information to flow from a source labeled @L_1@ to a sink @L_2@, the
restrictions imposed by the categories of @L_2@ must at least as restrictive as
all the restrictions imposed by the categories of @L_1@ (hence the conjunction)
in the case of secrecy, and at least as permissive in the case of integrity.
More specifically, for information to flow from @L_1@ to @L_2@, the labels
must satisfy the \"can-flow-to\" relation: @L_1 &#8849; L_2@.  The &#8849;
label check is implemented by the 'canflowto' function.  For labels
@L_1=\<S_1, I_1\>@, @L_2=\<S_2, I_2\>@ the can-flow-to relation is satisfied
if the secrecy category set @S_2@ 'implies' @S_1@ and @I_1@ 'implies' @I_2@
(recall that a category set is a conjunction of disjunctions of principals).
For example, @\<{[P_1 &#8897; P_2]},{}\> &#8849; \<{[P_1]},{}\>@ because data
that can be read by @P_1@ is more restricting than that readable by @P_1@
or @P_2@. Conversely, @\<{{},[P_1]}\> &#8849; \<{},[P_1 &#8897; P_2]},{}\>@
because data vouched for by @P_1@ or @P_2@ is more permissive than just @P_1@
(note the same idea holds when writing to sinks with such labeling).

A piece of a code running with a privilege object (of type 'TCBPriv'), i.e.,
owning a 'Principal' confers the right to modify labels by removing any
'secrecy' categories containing that 'Principal' and adding any 'integrity'
categories containing the 'Principal' (hence the name disjunction categories:
the category @[P1 &#8897; P2]@ can be /downgraded/ by either 'Principal'
@P1@ or @P2@).  More specifically, privileges can be used to bypass
information flow restrictions by using the more permissive \"can-flow-to given
permission\" relation:&#8849;&#7528;. The label check function implementing
this restriction is 'canflowto_p', taking an additional argument (of type
'TCBPriv'). For example, if @L_1=\<{[P_1 &#8897; P_2] &#8896; [P_3]},{}\>@,
and @L_2=\<{[P_1]},{}\>@, then @L_1 &#8930; L_2@, but given a privilege
object corresponding to @[P_3]@ the @L_1 &#8849;&#7528; L_2@ holds.

To construct DC labels and privilege objects the constructors exported by
this module may be used, but we strongly suggest using "DCLabel.NanoEDSL"
as exported by "DCLabel.TCB" and "DCLabel.Safe". The former is to be used by
trusted code only, while the latter module should be imported by untrusted
code as it prevents the creation of arbitrary privileges.

-}

module DCLabel.Core ( -- * Labels 
		      -- $labels
                      Disj(..), Conj(..), Label(..)
                    , emptyLabel, allLabel
                    , Lattice(..)
 		    , ToLNF(..)
                      -- ** DC Labels
                    , DCLabel(..)
                      -- * Principals
                    , Principal(..), principal
                      -- * Privileges
		      -- $privs
                    , TCBPriv(..), Priv
                    , RelaxedLattice(..)
                    , noPriv, rootPrivTCB
                    , delegatePriv, createPrivTCB
                    , CanDelegate(..), Owns(..)
                      -- * Label/internal operations
                    , and_label, or_label, cleanLabel, implies
		    , DisjToFromList(..)
		    , listToLabel, labelToList
                    ) where


#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 702)
import safe Data.List (nub, sort, (\\))
import safe Data.Maybe (fromJust)
import safe Data.Monoid
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
#else
import Data.List (nub, sort, (\\))
import Data.Maybe (fromJust)
import Data.Monoid
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
#endif

--
-- Categories
--

-- | A category, i.e., disjunction, of 'Principal's.
-- The empty list '[]' corresponds to the disjunction of all principals.
-- Conceptually, @[] =  [P_1 &#8897;  P_2 &#8897; ...]@
newtype Disj = MkDisj { disj :: [Principal] }
        deriving (Eq, Ord, Show, Read)


-- | A category set, i.e., a conjunction of disjunctions. 
-- The empty list '[]' corresponds to the single disjunction of all principals.
-- In other words, conceptually, @[] =  {[P_1 &#8897; P_2 &#8897; ...]}@
newtype Conj = MkConj { conj :: [Disj] }
        deriving (Eq, Ord, Show, Read)

--
-- Labels
--

{- $labels
A label is a conjunction of disjunctions of principals. A 'DCLabel' is simply a 
pair of such labels. Hence, we define almost all operations in terms of this 
construct, from which the 'DCLabel' implementation follows almost trivially.
Moreover, we note that secrecy-only and integrity-only labels are implemented 
in "DCLabel.Secrecy" and "DCLabel.Integrity", respectively.
-}

-- | Labels forma a partial order according to the &#8849; relation.
-- Specifically, this means that for any two labels @L_1@ and @L_2@ there is a 
-- unique label @L_3 = L_1 &#8852; L_2@, known as the /join/, such that
-- @L_1 &#8849; L_3@ and @L_2 &#8849; L_3@. Similarly, there is a unique label 
-- @L_3' = L_1 &#8851; L_2@, known as the /meet/, such that
-- @L_3 &#8849; L_1@ and @L_3 &#8849; L_2@. This class defines a /bounded/ 
-- lattice, which further requires the definition of the /bottom/ &#8869; and 
-- /top/ &#8868; elements of the lattice, such that @&#8869; &#8849; L@ and
-- @L &#8849; &#8868;@ for any label @L@.
class Eq a => Lattice a where
  bottom    :: a  -- ^ Bottom of lattice, &#8869;
  top       :: a  -- ^ Top of lattice, &#8868;
  join      :: a -> a -> a  -- ^ Join of two elements, &#8852;
  meet      :: a -> a -> a  -- ^ Meet of two elements, &#8851;
  canflowto :: a -> a -> Bool -- ^ Partial order relation, &#8849;


-- | A label is a conjunction of disjunctions, where @MkLabelAll@ is 
-- the constructor that is associated with the conjunction of all
-- possible disjunctions.
data Label = MkLabelAll
           | MkLabel { label :: Conj }
     deriving (Show, Read)

-- | Labels have a unique LNF (see 'ToLNF') form, and equality testing is
-- perfomed on labels of this form.
instance Eq Label where
  (==) MkLabelAll MkLabelAll = True
  (==) MkLabelAll _ = False
  (==) _ MkLabelAll = False
  (==) l1 l2 = (label . toLNF $ l1) == (label . toLNF $ l2)

-- | A label without any disjunctions or conjunctions. This label, conceptually
-- corresponds to the label consisting of a single category containing all
-- principals. Conceptually,
-- @emptyLabel = \<{[P_1 &#8897; P_2 &#8897; ...]}\>@
emptyLabel :: Label
emptyLabel = MkLabel (MkConj [])

-- | The dual of 'emptyLabel', 'allLabel' consists of the conjunction of
-- all possible disjunctions, i.e., it is the label that implies all
-- other labels. Conceptually,
-- @allLabel = \<{[P_1] &#8896; [P_2] &#8896; ...}\>@
allLabel :: Label
allLabel = MkLabelAll

-- | Predicate function that returns @True@ if the label corresponds to
-- the 'emptyLabel'.
isEmptyLabel :: Label -> Bool
isEmptyLabel MkLabelAll = False
isEmptyLabel l = and [ null (disj d) | d <- conj (label l) ]

-- | Predicate function that retuns @True@ if the label corresponds to
-- the 'allLabel'.
isAllLabel :: Label -> Bool
isAllLabel MkLabelAll = True
isAllLabel _ = False


--
-- Helper functions
--


-- | Given two labels, take the union of the disjunctions, i.e., simply 
-- perform an \"and\". Note the new label is not necessarily in LNF.
and_label :: Label -> Label -> Label
and_label l1 l2 | isAllLabel l1 || isAllLabel l2 = allLabel
                | otherwise = MkLabel
                        {label = MkConj $ conj (label l1) ++ conj (label l2)}

-- | Given two labels, perform an \"or\".
-- Note that the new label is not necessarily in LNF.
or_label :: Label -> Label -> Label 
or_label l1 l2 | isEmptyLabel l1 || isEmptyLabel l2 = emptyLabel
               | isAllLabel l2 = l1 
               | isAllLabel l1 = l2 
               | otherwise = MkLabel . MkConj $ [ MkDisj (disj d1 ++ disj d2)
                                                | d1 <- (conj (label l1)) 
                                                , d2 <- (conj (label l2))
                                                , not . null . disj $ d1
                                                , not . null . disj $ d2] 

-- | Determines if a conjunction of disjunctions, i.e., a label, implies
-- (in the logical sense) a disjunction. In other words, it checks if
-- d_1 &#8896; ... &#8896; d_n => d_1.
--
-- Properties:
--
--      * &#8704; X, 'allLabel' \``impliesDisj`\` X = True
--
--      * &#8704; X, X \``impliesDisj`\` 'emptyLabel'  = True
--
--      * &#8704; X&#8800;'emptyLabel', 'emptyLabel' \``impliesDisj`\` X = False
--
-- Note that the first two guards are only included 
-- for safety; the function is always called with a non-ALL label and 
-- non-null disjunction.
impliesDisj :: Label -> Disj -> Bool 
impliesDisj l d | isAllLabel l = True   -- Asserts 1
                | null (disj d) = True  -- Asserts 2
                | otherwise = or [ and [ e `elem` (disj d) | e <- disj d1 ]
                                 | d1 <- conj (label l)
                                 , not (isEmptyLabel l) ] -- Asserts 3

-- | Determines if a label implies (in the logical sense) another label. 
-- In other words, d_1 &#8896; ... &#8896; d_n => d_1' &#8896; ... &#8896; d_n'.
--
-- Properties:
--
-- 	* &#8704; X, 'allLabel' \``implies`\` X := True
--
--      * &#8704; X&#8800;'allLabel', X \``implies`\` 'allLabel' := False
--
--      * &#8704; X, X \``implies`\` 'emptyLabel' := True
--
--      * &#8704; X&#8800;'emptyLabel', 'emptyLabel' \``implies`\` X := False
implies :: Label -> Label -> Bool 
implies l1 l2 | isAllLabel l1 = True -- Asserts 1
              | isAllLabel l2 = False -- Asserts 2
              | otherwise = and [ impliesDisj (toLNF l1) d 
                                | d <- conj . label . toLNF $ l2 ]


-- | Removes any duplicate principals from categories, and any duplicate
-- categories from the label. To return a clean label, it sorts the label
-- and removes empty disjunctions.
cleanLabel :: Label -> Label
cleanLabel MkLabelAll = MkLabelAll 
cleanLabel l = MkLabel . MkConj . sort . nub $
               [ MkDisj ( (sort . nub) (disj d) ) | d <- conj (label l)
                                                , not . null $ disj d ] 
-- | Class used to reduce labels to a unique label normal form (LNF), which 
-- corresponds to conjunctive normal form of principals. We use this class 
-- to overload the reduce function used by the 'Label', 'DCLabel', etc.
class ToLNF a where
  toLNF :: a -> a

-- | Reduce a 'Label' to LNF.
-- First it applies @cleanLabel@ to remove duplicate principals and categories.
-- Following, it removes extraneous/redundant categories. A category is said to
-- be extraneous if there is another category in the label that implies it.
instance ToLNF Label where
  toLNF MkLabelAll = MkLabelAll 
  toLNF l = MkLabel . MkConj $ l' \\ extraneous 
    where l' = conj . label $ cleanLabel l
          extraneous = [ d2 | d1 <- l', d2 <- l', d1 /= d2
                            , impliesDisj ((MkLabel . MkConj) [d1]) d2 ]

--
-- DC Labels
--


--
-- DC Labels : (Secrecy, Integrity)
--

-- | A @DCLabel@ is a pair of secrecy and integrity category sets, i.e., 
-- a pair of 'Label's.
data DCLabel = MkDCLabel { secrecy :: Label    -- ^  Integrity category set.
                         , integrity :: Label  -- ^ Secrecy category set.
			 } 
  deriving (Eq, Show, Read)

-- | Each 'DCLabel' can be reduced a unique label representation in LNF, using 
-- the 'toLNF' function.
instance ToLNF DCLabel where
  toLNF l = MkDCLabel { secrecy = toLNF (secrecy l)
                      , integrity = toLNF (integrity l)}

-- | Elements of 'DCLabel' form a bounded lattice, where:
--
-- 	* @&#8869; = \<'emptyLabel', 'allLabel'\>@
--
-- 	* @&#8868; = \<'allLabel', 'emptyLabel'\>@
--
-- 	* @ \<S_1, I_1\> &#8852; \<S_2, I_2\> = \<S_1 &#8896; S_2, I_1 &#8897; I_2\>@
--
-- 	* @ \<S_1, I_1\> &#8851; \<S_2, I_2\> = \<S_1 &#8897; S_2, I_1 &#8896; I_2\>@
--
-- 	* @ \<S_1, I_1\> &#8849; \<S_2, I_2\> = S_2 => S_1 &#8896; I_1 => I_2@
instance Lattice DCLabel where
  bottom = MkDCLabel { secrecy = emptyLabel
                     , integrity = allLabel }
  top = MkDCLabel { secrecy = allLabel
                  , integrity = emptyLabel }
  join l1 l2 = let s3 = (secrecy l1) `and_label` (secrecy l2)
                   i3 = (integrity l1) `or_label` (integrity l2)
               in toLNF $ MkDCLabel { secrecy = s3
                                    , integrity = i3 }
  meet l1 l2 = let s3 = (secrecy l1) `or_label` (secrecy l2)
                   i3 = (integrity l1) `and_label` (integrity l2)
               in toLNF $ MkDCLabel { secrecy = s3
                                    , integrity = i3 }
  canflowto l1 l2 = let l1' = toLNF l1
                        l2' = toLNF l2
                    in ((secrecy l2') `implies` (secrecy l1')) &&
                       ((integrity l1') `implies` (integrity l2'))


--
-- Principals
-- 

-- | Principal is a simple string representing a source of authority. Any piece 
-- of code can create principals, regarless of how untrusted it is. However, 
-- for principals to be used in integrity labels or be ignoerd a corresponding 
-- privilege ('TCBPriv') must be created (by trusted code) or delegated.
newtype Principal = MkPrincipal { name :: B.ByteString }
                  deriving (Eq, Ord, Show, Read)

-- | Generates a principal from an string. 
principal :: B.ByteString -> Principal 
principal = MkPrincipal 


--
-- Privileges
-- 

{- $privs
As previously mentioned privileges allow a piece of code to bypass certain 
information flow restrictions. Like principals, privileges of type 'Priv'
may be created by any piece of code. A privilege is simply a conjunction of 
disjunctions, i.e., a 'Label' where a category consisting of a single principal 
corresponds to the notion of /owning/ that principal. We, however, allow for 
the more general notion of ownership of a category as to create a 
privilege-hierarchy. Specifically, a piece of code exercising a privilege @P@ 
can always exercise privilege @P'@ (instead), if @P' => P@. This is similar to 
the DLM notion of \"can act for\", and, as such, we provide a function which 
tests if one privilege may be use in pace of another: 'canDelegate'.

Note that the privileges form a partial order over @=>@, such that
@'rootPrivTCB' => P@ and @P => 'noPriv'@ for any privilege @P@.
As such we have a privilege hierarchy which can be concretely built through 
delegation, with 'rootPrivTCB' corresponding to the /root/, or all, privileges
from which all others may be created. More specifically, given a minted
privilege @P'@ of type 'TCBPriv', and an un-minted privilege @P@ of type 'Priv',
any piece of code can use 'delegatePriv' to mint @P@, assuming @P' => P@.

Finally, given a set of privileges a piece of code can check if it owns a 
category using the 'owns' function.
-}

-- | Privilege object is just a conjunction of disjunctions, i.e., a 'Label'.
-- A trusted privileged object must be introduced by trusted code, after which
-- trusted privileged objects can be created by delegation.
data TCBPriv = MkTCBPriv { priv :: Label } 
     deriving (Eq, Show)

-- | Untrusted privileged object, which can be converted to a 'TCBPriv' with
-- 'delegatePriv'.
type Priv = Label

-- | Class extending 'Lattice', by allowing for the more relaxed label
-- comparison  @canflowto_p@.
class (Lattice a) => RelaxedLattice a where
        -- | Relaxed partial-order relation
        canflowto_p :: TCBPriv -> a -> a -> Bool


instance RelaxedLattice DCLabel where
  canflowto_p p l1 l2 =
    let l1' =  MkDCLabel { secrecy = (secrecy l1)
                         , integrity = (and_label (priv p) (integrity l1)) }
        l2' =  MkDCLabel { secrecy = (and_label (priv p) (secrecy l2))
                         , integrity = (integrity l2) }
    in canflowto l1' l2' 


-- | Given trusted privilege and a \"desired\" untrusted privilege,
-- return a trusted version of the untrusted privilege, if the
-- provided (trusted) privilege implies it.
delegatePriv :: TCBPriv -> Priv -> Maybe TCBPriv
delegatePriv tPriv rPriv = let rPriv' = toLNF rPriv
                           in case (priv tPriv) `implies` rPriv' of
                                True -> Just (MkTCBPriv rPriv')
                                False -> Nothing

-- | Privilege object corresponding to no privileges.
noPriv :: TCBPriv
noPriv = MkTCBPriv { priv = emptyLabel }

-- | Privilege object corresponding to the \"root\", or all privileges.
-- Any other privilege may be delegated using this privilege object and it must
-- therefore not be exported to untrusted code. 
rootPrivTCB :: TCBPriv
rootPrivTCB = MkTCBPriv { priv = allLabel }

-- | This function creates any privilege object given an untrusted 
-- privilege 'Priv'. Note that this function should not be exported
-- to untrusted code.
createPrivTCB :: Priv -> TCBPriv
createPrivTCB = fromJust . (delegatePriv rootPrivTCB)

-- | @TCBPriv@ is an instance of 'Monoid'.
instance Monoid TCBPriv where
  mempty = noPriv
  mappend p1 p2 = createPrivTCB $ toLNF ((priv p1) `and_label` (priv p2))

  		
-- | Class used for checking if a computation can use a privilege in place of
-- the other. This notion is similar to the DLM \"can-act-for\".
class CanDelegate a b where
        -- | Can use first privilege in place of second.
        canDelegate :: a -> b -> Bool

instance CanDelegate Priv Priv where
  canDelegate p1 p2 = p1 `implies` p2

instance CanDelegate Priv TCBPriv where
  canDelegate p1 p2 = p1 `implies` (priv p2)

instance CanDelegate TCBPriv Priv where
  canDelegate p1 p2 = (priv p1) `implies` p2

instance CanDelegate TCBPriv TCBPriv where
  canDelegate p1 p2 = (priv p1) `implies` (priv p2)


-- | We say a 'TCBPriv' privilege object owns a category when the privileges
-- allow code to bypass restrictions implied by the category. This is the
-- case if and only if the 'TCBPriv' object contains one of the 'Principal's
-- in the 'Disj'. This class is used to check ownership
class Owns a where
	-- | Checks if category restriction can be bypassed given the privilege.
        owns :: TCBPriv -> a -> Bool 

instance Owns Disj where
  owns p d = priv p `impliesDisj` d 

instance Owns Label where
  owns p l = priv p `implies` l 



-- | Class used to convert list of principals to a disjunction category and
-- vice versa.
class DisjToFromList a where 
  	listToDisj :: [a] -> Disj -- ^ Given list return category.
  	disjToList :: Disj -> [a] -- ^ Given category return list.

-- | To/from 'Principal's and 'Disj'unction categories.
instance DisjToFromList Principal where
  listToDisj ps = MkDisj ps
  disjToList d = disj d
  	
-- | To/from 'String's and 'Disj'unction categories.
instance DisjToFromList String where
  listToDisj ps = MkDisj $ map (principal . C.pack) ps
  disjToList d = map (C.unpack . name) $ disj d

-- | To/from 'ByteString's and 'Disj'unction categories.
instance DisjToFromList B.ByteString where
  listToDisj ps = MkDisj $ map principal ps
  disjToList d = map name $ disj d

-- | Given a list of categories, return a label.
listToLabel :: [Disj] -> Label -- ^ Given list return category.
listToLabel = MkLabel . MkConj 

-- | Given a label return a list of categories.
labelToList :: Label -> [Disj] -- ^ Given category return list.
labelToList = conj . label
