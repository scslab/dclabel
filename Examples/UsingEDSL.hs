{-# LANGUAGE Safe #-}
module UsingEDSL where 

import DCLabel.Safe
import DCLabel.PrettyShow

-- Creating categories:
c1 = "Alice"

c2 = "Alice" .\/. "Bob"

c3 = (<>)

-- Labels, i.e. conjunctions of disjunctions
-- Observe the precedence of .\/. is higher than ./\.

l1 = "Alice" .\/. "Bob" ./\. "Carla" 
l2 = "Alice" ./\. "Carla" 
l3 = "Alice" .\/. ("Bob" ./\. "Carla")

-- DCLabels 

dc1 = newDC l1 l2
dc2 = newDC ("Deian") ("Alice") 
dc3 = newDC l3 (<>)
dc4 = newDC c3 (><)


main = do
  putStrLn $ prettyShow dc1
  putStrLn $ prettyShow dc2
  putStrLn $ prettyShow dc3
  putStrLn $ prettyShow dc4
  
