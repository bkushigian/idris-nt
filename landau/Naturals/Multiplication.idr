module Naturals.Multiplication

import Logic
import Naturals.PNat
import Naturals.Addition
import Naturals.Order

%access export
%default total

-- Definition 6 (multiplication) can be found in Naturals.PNat as multPNat
-- 2) is defined alternatively as x' * y = y + x * y
theorem28Uniqueness : (x * y = u, x * y = v) -> u = v
theorem28Uniqueness (prf1, prf2) = trans (sym prf1) prf2

theorem29 : {x : PNat} -> x * y = y * x


multCommutative : {x : PNat} -> x * y = y * x
multCommutative = theorem29

theorem30 : {x : PNat} -> x * (y + z) = (x * y) + (x * z)


theorem31 : {x : PNat} -> (x * y) * z = x * (y * z)


mutual
    theorem32 : (x .> y -> x*z .> y*z, x = y -> x*z = y*z, x .< y -> x*z .< y*z)
    theorem32 = (_32a, _32b, _32c)
    
    _32a : x .> y -> x*z .> y*z
 
    _32b : {x : PNat} -> x = y -> x*z = y*z
    
    _32c : x .< y -> x*z .< y*z

mutual
    theorem33 : (x*z .> y*z -> x .> y, x*z = y*z -> x = y, x*z .< y*z -> x .< y)
    theorem33 = (_33a, _33b, _33c)
    
    _33a : x*z .> y*z -> x .> y
 
    _33b : {x : PNat} -> x*z = y*z -> x = y
    
    _33c : x*z .< y*z -> x .< y

theorem34 : (x .> y, z .> u) -> x*z .> y*u

theorem35 : Either (x .>= y, z .> u) (x .> y, z .>= u) -> x*z .> y*u

theorem36 : (x .>= y, z .>= y) -> x*z .>= y*u
