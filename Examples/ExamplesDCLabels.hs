module ExamplesDCLabels where 

import DCLabel.TCB
import DCLabel.PrettyShow

l1 =  "Alice" .\/. "Bob" ./\. "Carla" 

l2 = "Alice" ./\. "Carla" 

dc1 = newDC l1 l2

dc2 = newDC ("Deian") ("Alice") 

pr = createPrivTCB (newPriv ("Alice" ./\. "Carla"))

main = do
  putStrLn . prettyShow $ dc1
  putStrLn . prettyShow $ dc2
  putStrLn . show $ canflowto dc1 dc2
  putStrLn . show $ canflowto_p pr dc1 dc2
{-
<{["Alice" \/ "Bob"] /\ ["Carla"]} , {["Alice"] /\ ["Carla"]}>
<{["Deian"]} , {["Alice"]}>
False
True
-}
