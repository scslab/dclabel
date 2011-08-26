{-| This module implements a ``nano``, very simple, embedded domain specific
  language to create 'Label's and 'Priv'ilages from conjunctions of
  principal disjunctions.
  
  A 'Label'/'Priv' is created using the ('.\/.') and ('./\.') operators.
  The disjunction operator ('.\/.') is used to create a category from
  'Principal's, 'String's, or a disjunctive sub-expression. For example:

  @
     p1 = 'principal' \"p1\"
     p2 = 'principal' \"p2\"
     p3 = 'principal' \"p3\"
     e1 = p1 '.\/.' p2
     e2 = e1 '.\/.' \"p4\"
  @

  Similarly, the conjunction operator ('./\.') is used to create category-sets
  from 'Principals', 'Strings', and conjunctive or disjunctive sub-expressions.
  For example:

  @
     e3 = p1 '.\/.' p2
     e4 = e1 './\.' \"p4\" './\.' p3
  @

  /Note/ that because a category consists of a disjunction of principals, and a
  category set is composed of the conjunction of categories, ('.\/.') binds
  more tightly than ('./\.').

  Given two 'Label's, one for secrecy and one for integrity, you can
  create a 'DCLabel' with 'newDC'. And, similarly, given a 'TCBPriv' and 'Priv' 
  you can create a new minted privilege with 'newTCBPriv'.
  
  
  Consider the following, example:

  @
     l1 = \"Alice\" '.\/.' \"Bob\" './\.' \"Carla\" 
     l2 = \"Alice\" './\.' \"Carla\" 
     dc1 = 'newDC' l1 l2
     dc2 = 'newDC' \"Deian\" \"Alice\"
     pr = 'createPrivTCB' $ 'newPriv' (\"Alice\" './\.' \"Carla\")
  @

where

  * @ dc1 = \<{[\"Alice\" &#8897; \"Bob\"] &#8896; [\"Carla\"]} , {[\"Alice\"] &#8896; [\"Carla\"]}\>@
  
  * @ dc2 = \<{[\"Deian\"]} , {[\"Alice\"]}\>@

  * @ 'canflowto' dc1 dc2 = False @

  * @ 'canflowto_p' pr dc1 dc2 = True@

-}


{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module DCLabel.NanoEDSL ( -- * Operators
			  (.\/.), (./\.)
                        , (<>), (><)
                        , singleton
                          -- * DCLabel creation
                        , newDC
                          -- * Privilege object creation
                        , NewPriv, newPriv, newTCBPriv
                        ) where

import DCLabel.Core

infixl 7 .\/.
infixl 6 ./\.

-- | Class used to create single-principal labels.
class Singleton a where 
      singleton :: a -> Label -- ^ Creates a singleton label.

instance Singleton Principal where 
      singleton p = MkLabel $ MkConj [ MkDisj [p] ]

instance Singleton String where 
      singleton s = MkLabel $ MkConj [ MkDisj [principal s] ]


-- | Class used to create disjunctions.
class DisjunctionOf a b where
  (.\/.) :: a -> b -> Label -- ^ Given two elements it joins them with &#8897;

instance DisjunctionOf Principal Principal where
 p1 .\/. p2 = MkLabel $ MkConj [ MkDisj [p1,p2] ]

instance DisjunctionOf Principal Label where
 p .\/. l = (singleton p) `or_label` l 

instance DisjunctionOf Label Principal where
 l .\/. p = p .\/. l

instance DisjunctionOf Label Label where
 l1 .\/. l2 = l1 `or_label` l2

instance DisjunctionOf String String where
 s1 .\/. s2 = singleton s1 .\/. singleton s2

instance DisjunctionOf String Label where
  s .\/. l = singleton s .\/. l 

instance DisjunctionOf Label String where
  l .\/. p = p .\/. l  


-- | Class used to create conjunctions.
class ConjunctionOf a b where
  (./\.) :: a -> b -> Label -- ^ Given two elements it joins them with &#8896;

instance ConjunctionOf Principal Principal where
   p1 ./\. p2 = MkLabel $ MkConj [ MkDisj [p1], MkDisj [p2] ] 

instance ConjunctionOf Principal Label where
   p ./\. l = singleton p `and_label` l 

instance ConjunctionOf Label Principal where
   l ./\. p = p ./\. l 

instance ConjunctionOf Label Label where
   l1 ./\. l2 = l1 `and_label` l2 

-- | Instances using strings and not principals
instance ConjunctionOf String String where
   s1 ./\. s2 = singleton s1 ./\. singleton s2 

instance ConjunctionOf String Label where
   s ./\. l = singleton s `and_label` l 

instance ConjunctionOf Label String where
   l ./\. s = s ./\. l 

-- | Instances using disjunctions.
instance ConjunctionOf Disj Disj where
   d1 ./\. d2 = MkLabel $ MkConj [ d1, d2 ] 

instance ConjunctionOf Disj Label where
   d ./\. l = (MkLabel $ MkConj [d]) `and_label` l 

instance ConjunctionOf Label Disj where
   l ./\. d = d ./\. l 

instance ConjunctionOf Principal Disj where
   p ./\. d = singleton p ./\. d

instance ConjunctionOf Disj Principal where
   d ./\. p = p ./\. d 

instance ConjunctionOf String Disj where
   p ./\. d = singleton p ./\. d

instance ConjunctionOf Disj String where
   d ./\. p = p ./\. d 
   


-- | Empty label.
(<>) :: Label
(<>) = emptyLabel

-- | All label.
(><) :: Label
(><) = allLabel

---
--- Creating 'DCLabel's
---

-- | Class used to create 'DCLabel's.
class NewDC a b where
  newDC :: a -> b -> DCLabel -- ^ Given two elements create label.

instance NewDC Label Label where
  newDC l1 l2 = MkDCLabel l1 l2 

instance NewDC Principal Label where
  newDC p l = MkDCLabel (singleton p) l 

instance NewDC Label Principal where
  newDC l p = MkDCLabel l (singleton p) 

instance NewDC Principal Principal where
  newDC p1 p2 = MkDCLabel (singleton p1) (singleton p2) 

instance NewDC String Label where
  newDC p l = MkDCLabel (singleton p) l 

instance NewDC Label String where
  newDC l p = MkDCLabel l (singleton p) 

instance NewDC String String where
  newDC p1 p2 = MkDCLabel (singleton p1) (singleton p2) 

--
-- Creating 'Priv's and 'TCBPriv's.
--

-- | Class used to create 'Priv's and 'TCBPriv's.
class NewPriv a where
  -- | Given element create privilege.
  newPriv :: a -> Priv 
  -- | Given privilege and new element, create (maybe) trusted privileged object.
  newTCBPriv :: TCBPriv -> a -> Maybe TCBPriv
  newTCBPriv p = delegatePriv p . newPriv

instance NewPriv Label where
  newPriv = id

instance NewPriv Principal where
  newPriv p = singleton p

instance NewPriv String where
  newPriv p = singleton p
