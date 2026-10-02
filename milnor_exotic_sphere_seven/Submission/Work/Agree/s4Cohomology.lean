import Mathlib
import Submission.Work.Agree.crux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cohomology of `S⁴ = OnePoint ℝ⁴`

`Submission/Work/Cohomology/sphereCohomologyZero` computes the singular cohomology of the sphere
`Sⁿ = Metric.sphere (0 : ℝ^(n+1)) 1`.  This module transports that computation to the workspace's
model `S4 = OnePoint (EuclideanSpace ℝ (Fin 4))` of `S⁴` (the base of `Agree.clutchBundle`), via the
homeomorphism `OnePoint V ≅ Metric.sphere (0 : ℝ^(finrank V + 1)) 1` of Mathlib.

The result needed by the characteristic-class argument is that `H²(S⁴; ℤ) = 0` (so that every
`c₁ = 0` over `S⁴`), together with the vanishing in the other degrees `≠ 0, 4` (in particular
`H⁸(S⁴) = 0`).
-/

open scoped Topology

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-- **`S⁴ = ℝ⁴ ∪ {∞}` is homeomorphic to the unit sphere of `ℝ⁵`.** -/
def homeoS4Sphere : S4 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 :=
  onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin 4)) (ι := Fin 5) (by simp)

/-- **The singular cohomology of `S⁴` vanishes away from the degrees `0` and `4`.** -/
theorem subsingleton_cohomology_S4 (k : ℕ) (h0 : k ≠ 0) (h4 : k ≠ 4) :
    Subsingleton (Work.Thom.Coh ℤ k S4) := by
  obtain ⟨e⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    (homeoS4Sphere.toHomotopyEquiv) k
  exact ModuleCat.subsingleton_of_isZero
    (CategoryTheory.Limits.IsZero.of_iso
      (Work.Cohomology.sphereCohomologyZero 4 k (by norm_num) h0 h4) e)

theorem subsingleton_cohomology_S4_one : Subsingleton (Work.Thom.Coh ℤ 1 S4) :=
  subsingleton_cohomology_S4 1 (by norm_num) (by norm_num)

theorem subsingleton_cohomology_S4_two : Subsingleton (Work.Thom.Coh ℤ 2 S4) :=
  subsingleton_cohomology_S4 2 (by norm_num) (by norm_num)

theorem subsingleton_cohomology_S4_three : Subsingleton (Work.Thom.Coh ℤ 3 S4) :=
  subsingleton_cohomology_S4 3 (by norm_num) (by norm_num)

theorem subsingleton_cohomology_S4_five : Subsingleton (Work.Thom.Coh ℤ 5 S4) :=
  subsingleton_cohomology_S4 5 (by norm_num) (by norm_num)

theorem subsingleton_cohomology_S4_six : Subsingleton (Work.Thom.Coh ℤ 6 S4) :=
  subsingleton_cohomology_S4 6 (by norm_num) (by norm_num)

theorem subsingleton_cohomology_S4_seven : Subsingleton (Work.Thom.Coh ℤ 7 S4) :=
  subsingleton_cohomology_S4 7 (by norm_num) (by norm_num)

theorem subsingleton_cohomology_S4_eight : Subsingleton (Work.Thom.Coh ℤ 8 S4) :=
  subsingleton_cohomology_S4 8 (by norm_num) (by norm_num)

/-- `H²(S⁴;ℤ) = 0`, hence every first Chern class on `S⁴` vanishes. -/
theorem eq_zero_of_mem_cohomology_S4_two {x : Work.Thom.Coh ℤ 2 S4} : x = 0 := by
  haveI : Subsingleton (Work.Thom.Coh ℤ 2 S4) := subsingleton_cohomology_S4_two
  exact Subsingleton.elim x 0

end

end Work.Agree
