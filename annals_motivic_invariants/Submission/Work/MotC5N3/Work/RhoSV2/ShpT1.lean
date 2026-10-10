import Mathlib
import Submission.Work.MotC5N3.Work.RhoSV2.W
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Work.MotV5.ASLocal

open Polynomial

set_option maxHeartbeats 4000000 in
theorem shp_19 {K : Type} [CommRing K] (a b g : K) :
    Wa2 a b g * (Wa3 a b g * Wa4 a b g) = 0 := by
  simp only [Wa0, Wa1, Wa2, Wa3, Wa4]
  first | refl_ring1 | ring

set_option maxHeartbeats 4000000 in
theorem shp_21 {K : Type} [CommRing K] (a b g : K) :
    Wa2 a b g * (Wa4 a b g)^2 = 0 := by
  simp only [Wa0, Wa1, Wa2, Wa3, Wa4]
  first | refl_ring1 | ring

set_option maxHeartbeats 4000000 in
theorem shp_23 {K : Type} [CommRing K] (a b g : K) :
    (Wa2 a b g)^2 * Wa4 a b g = 0 := by
  simp only [Wa0, Wa1, Wa2, Wa3, Wa4]
  first | refl_ring1 | ring

set_option maxHeartbeats 4000000 in
theorem shp_25 {K : Type} [CommRing K] (a b g : K) :
    Wa3 a b g * (Wa4 a b g)^2 = 0 := by
  simp only [Wa0, Wa1, Wa2, Wa3, Wa4]
  first | refl_ring1 | ring

set_option maxHeartbeats 4000000 in
theorem shp_26 {K : Type} [CommRing K] (a b g : K) :
    (Wa3 a b g)^2 * Wa4 a b g = 0 := by
  simp only [Wa0, Wa1, Wa2, Wa3, Wa4]
  first | refl_ring1 | ring

set_option maxHeartbeats 4000000 in
theorem shp_28 {K : Type} [CommRing K] (a b g : K) :
    (Wa4 a b g)^3 = 0 := by
  simp only [Wa0, Wa1, Wa2, Wa3, Wa4]
  first | refl_ring1 | ring

end Work.MotV5.ASLocal
