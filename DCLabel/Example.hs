module Example where 

import DCLabel.Core

--
--Tests
--

a = MkSLabel $ MkLabel $ MkConj [MkDisj { disj = ["A"] }]
b = MkSLabel $ MkLabel $ MkConj [MkDisj { disj = ["B"] }]
c = MkILabel $ MkLabel $ MkConj [MkDisj { disj = ["C"] }]
e = MkILabel $ MkLabel $ MkConj []

ac = MkDCLabel (a,c)
bempty = MkDCLabel (b,e) 

j = join ac bempty

first_test  = ac `canflowto` j
second_test = bempty `canflowto` j
