module Main (main) where

import Test.QuickCheck hiding (label) 
import Control.Monad (liftM)
import DCLabel.TCB
import DCLabel.PrettyShow
import DCLabel.Secrecy
import DCLabel.Integrity
import Data.List (tails)
import System (getArgs)

instance Arbitrary Principal where 
     arbitrary = do p <- oneof $ map return ["A", "B", "C"]
                    return $ principal p


instance Arbitrary Disj where 
     arbitrary = sized disjunction 
                 where disjunction 0 = return $ MkDisj { disj = [] }
                       disjunction n = do a  <- arbitrary
                                          m  <- choose (0, n-1) 
                                          djs <- disjunction m
                                          return $ MkDisj $ a:(disj djs)     


instance Arbitrary Conj where 
     arbitrary = sized conjunction 
                 where conjunction 0 = oneof [return $ MkConj { conj = [] } , 
                                              return $ MkConj { conj = [MkDisj []] },
                                              return $ MkConj { conj = [MkDisj [], MkDisj []] } ] 
                       conjunction n = do a  <- arbitrary
                                          m  <- choose (0, n-1) 
                                          cjs <- conjunction m
                                          return $ MkConj $ a:(conj cjs)     
     shrink (MkConj ls) = [MkConj ll | l <- tails ls, ll <- shrink l]

instance Arbitrary Label where
  arbitrary = do m <- choose (0, 1) :: Gen Int
                 if m==0 then mkArbLbl arbitrary
			 else return MkLabelAll
    where mkArbLbl :: Gen Conj -> Gen Label
          mkArbLbl = liftM MkLabel

instance Arbitrary (SLabel) where
  arbitrary = do s <- arbitrary
                 return $ MkSLabel s

instance Arbitrary (ILabel) where
  arbitrary = do s <- arbitrary
                 return $ MkILabel s
          
instance Arbitrary DCLabel where
  arbitrary = do s <- arbitrary
                 i <- arbitrary 
                 return $ MkDCLabel { secrecy = s, integrity = i }

instance Arbitrary TCBPriv where
  arbitrary = do p <- arbitrary
                 return $ MkTCBPriv p

-- cleanLabel does not modify the semantics of the label 
prop_cleanLabel :: Label -> Bool
prop_cleanLabel l = let l' = cleanLabel l 
                    in l `implies` l' && l' `implies` l

-- Reduction function toLNF does not modify the semantics of the label
prop_toLNF :: Label -> Bool
prop_toLNF l = let l' = toLNF l 
               in  l `implies` l' && l' `implies` l 

-- Idempotenncy of toLNF
prop_toLNF_idem :: Property
prop_toLNF_idem = forAll (arbitrary :: Gen Label) $ \l->
  let l'  = toLNF l 
      l'' = toLNF l' 
  in l' == l''

-- Partial order for DCLabels
prop_dc_porder :: (DCLabel, DCLabel) -> Bool
prop_dc_porder (l1,l2) = let l1' = toLNF l1
                             l2' = toLNF l2
                             ge = l1' `canflowto` l2'
                             le = l2' `canflowto` l1'
                             eq = l2' == l1'
                         in (eq && ge && le) ||  -- ==
                            ((not eq) && (ge || le) && (ge /= le)) || -- < or >
                            (not (eq || ge || le)) -- incomparable

-- Check that labels flow to their join for DCLabels
prop_DC_join :: (DCLabel, DCLabel) -> Bool
prop_DC_join (l1,l2) = let l3 = l1 `join` l2
                           t1 = l1 `canflowto` l3
                           t2 = l2 `canflowto` l3
                       in t1 && t2

-- Check that join is the least upper bound for DCLabels
-- TODO: we need to fix this since it is difficult to satisfy the
-- hypothesis. 
prop_dc_join_lub :: (DCLabel, DCLabel) -> Property
prop_dc_join_lub (l1,l2) = forAll (arbitrary :: Gen DCLabel) $ \l3' ->
 (l1 `canflowto` l3') && (l2 `canflowto` l3') ==> (l1 `join` l2) `canflowto` l3'
                  

-- Check that meet flows to the labels making it, for DCLabels
prop_dc_meet :: (DCLabel, DCLabel) -> Bool
prop_dc_meet (l1,l2) = let l3 = l1 `meet` l2
                           t1 = l3 `canflowto` l1
                           t2 = l3 `canflowto` l2
                       in t1 && t2

-- Check that meet the greatest lower bound for DCLabels
prop_dc_meet_glb :: (DCLabel, DCLabel) -> Property
prop_dc_meet_glb (l1,l2) = forAll (arbitrary :: Gen DCLabel) $ \l3' ->
 (l3' `canflowto` l1) && (l3' `canflowto` l2) ==> l3' `canflowto` (l1 `meet` l2)

-- Check that the top is indeed indeed the highest element in the lattice
prop_dc_top :: DCLabel -> Property
prop_dc_top l1 = forAll (gen l1) $ \l -> l `canflowto` top
    where gen :: DCLabel -> Gen DCLabel
          gen _ = arbitrary

-- Check that the bottom is indeed indeed the lowest element in the lattice
prop_dc_bottom :: DCLabel -> Property
prop_dc_bottom l1 = forAll (arbitrary :: Gen DCLabel) $ \l -> bottom `canflowto` l

-- LIO's lostar
lostar :: TCBPriv -> DCLabel -> DCLabel -> DCLabel
lostar p li lg = 
  let lip = newDC (secrecy li) ((integrity li) ./\. lp)
      lgp = newDC ((secrecy lg) ./\. lp) (integrity lg)
      lp  = priv p
  in join lip lgp

{-
lr = lostar p li lg satisfies:
   - canflowto lg lr
   - canflowto_p p li lr
   - lr is the greatest lower bound
-}
prop_lostar :: TCBPriv -> DCLabel -> DCLabel -> Property
prop_lostar p li lg = 
  let lr = lostar p li lg 
  in forAll (arbitrary :: Gen DCLabel) $ \lr' -> 
   	canflowto lg lr &&
   	canflowto_p p li lr &&
	not ( canflowto lg lr' &&
              canflowto_p p li lr' &&
	      lr' /= lr &&
	      canflowto lr' lr)
main = do 
  putStrLn "Run program with number of runs"
  n <- getArgs >>= return . read . head
  let args = stdArgs { maxSuccess = n, maxSize = n, maxDiscard = 10000}
  putStrLn "Checking function cleanLabel..."
  quickCheckWith args (prop_cleanLabel :: Label -> Bool)
  putStrLn "Checking function toLNF..."
  quickCheckWith args (prop_toLNF :: Label -> Bool)
  putStrLn "Checking idempotence of function toLNF..."
  quickCheckWith args (prop_toLNF_idem :: Property)
  putStrLn "Checking the property of top..."
  quickCheckWith args (prop_dc_top :: DCLabel -> Property)
  putStrLn "Checking the property of bottom..."
  quickCheckWith args (prop_dc_bottom :: DCLabel -> Property)
  putStrLn "Checking the join operation..."
  quickCheckWith args (prop_DC_join ::  (DCLabel, DCLabel) -> Bool)
  putStrLn "Checking the join operation is indeed the least upper bound..."
  quickCheckWith args (prop_dc_join_lub :: (DCLabel, DCLabel) -> Property)
  putStrLn "Checking the meet operation..."
  quickCheckWith args (prop_dc_meet :: (DCLabel, DCLabel) -> Bool)
  putStrLn "Checking the meet operation is indeed the greatest lower bound..."
  quickCheckWith args (prop_dc_meet_glb :: (DCLabel, DCLabel) -> Property)
  putStrLn "Checking DC labels form a partial order..."
  quickCheckWith args (prop_dc_porder :: (DCLabel, DCLabel) -> Bool)
  putStrLn "Checking lostar implementation..."
  quickCheckWith args (prop_lostar :: TCBPriv -> DCLabel -> DCLabel -> Property)
