{-# LANGUAGE Safe #-}
module Labels where 

import DCLabel.Safe
import DCLabel.PrettyShow

-- Creating categories
c1 = "Alice"

c2 = "Alice" .\/. "Bob"

c3 = (<>)

-- Labels, i.e. conjunctions of disjunctions
-- Observe the precedence of .\/. is higher than ./\.

l1 =  "Alice" .\/. "Bob" ./\. "Carla" 

l2 = "Alice" ./\. "Carla" 

-- DCLabels 

dc1 = newDC l1 l2

dc2 = newDC ("Deian") ("Alice") 

main = do
  putStrLn . prettyShow $ dc1
  putStrLn . prettyShow $ dc2
  putStrLn . prettyShow $ join dc1 dc2
  putStrLn . prettyShow $ meet dc1 dc2

  putStrLn . prettyShow $ dc1
  putStrLn . prettyShow $ join dc1 top
  putStrLn . show $ canflowto dc1 top
  putStrLn . show $ canflowto bottom dc1
{-
<{["Alice" \/ "Bob"] /\ ["Carla"]} , {["Alice"] /\ ["Carla"]}>
<{["Deain"]} , {["Alice"]}>
<{["Alice" \/ "Bob"] /\ ["Carla"] /\ ["Deain"]} , {["Alice"]}>
<{["Alice" \/ "Bob" \/ "Deain"] /\ ["Carla" \/ "Deain"]} , {["Alice"] /\ ["Carla"]}>
<{["Alice" \/ "Bob"] /\ ["Carla"]} , {["Alice"] /\ ["Carla"]}>
<{ALL} , {}>
True
True
-}
