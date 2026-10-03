import Mathlib
import Submission.Work.ORTorsion.Defs

namespace Work.ORTorsion.Support

open scoped TensorProduct
open Work.ORTorsion
open Work.ORTorsion.LaurentBase

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Algebra K U]
variable {gen : G →* Uˣ} {D : Subgroup G → Subalgebra K U} {H : Subgroup G}
  {φ : H →* Multiplicative ℤ}

/-- `mapSubAlg` acts on a `single` by re-indexing the group element. -/
theorem mapSubAlg_single' {H H' : Subgroup G} (f : H ≤ H') (k : H) (c : K) :
    mapSubAlg f (MonoidAlgebra.single k c) = MonoidAlgebra.single (⟨(k : G), f k.2⟩ : H') c := by
  rw [mapSubAlg, MonoidAlgebra.lift_single]
  simp [MonoidAlgebra.smul_single]

/-- The re-indexed element `h * s ^ (-b)` multiplied back by `s ^ b` recovers `h`. -/
theorem incl_mul_zpow (Lb : LaurentBase K U G gen D H φ) {b : ℤ} {h : H}
    (hc : φ h = Multiplicative.ofAdd b) :
    (⟨((h * Lb.s ^ (-b) : H) : G), Lb.N_le_H (Lb.mem_N_of_mem_ker (Lb.mem_ker_mul_zpow hc))⟩ : H)
      * Lb.s ^ b = h := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
  rw [mul_assoc, ← zpow_add]
  simp

theorem mapSubAlg_degCoeff_mul {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*}
    [Ring U] [Algebra K U] (L : TorsionData K G U) {H : Subgroup G}
    {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ) (b : ℤ)
    (x : MonoidAlgebra K H) :
    mapSubAlg (LaurentBase.N_le_H Lb) (LaurentBase.degCoeff Lb b x)
        * MonoidAlgebra.single (Lb.s ^ b) (1 : K) = degPart φ b x := by
  classical
  have h1 : LaurentBase.degCoeff Lb b x =
      ∑ h ∈ x.coeff.support, (if hc : φ h = Multiplicative.ofAdd b then
        MonoidAlgebra.single (⟨((h * Lb.s ^ (-b) : H) : G),
          Lb.mem_N_of_mem_ker (Lb.mem_ker_mul_zpow hc)⟩ : ↥Lb.N) (x.coeff h)
        else 0) := by
    rw [LaurentBase.degCoeff, MonoidAlgebra.ofCoeff_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    by_cases hc : φ h = Multiplicative.ofAdd b
    · simp only [dif_pos hc, MonoidAlgebra.ofCoeff_single]
    · simp only [dif_neg hc, MonoidAlgebra.ofCoeff_zero]
  have h2 : degPart φ b x =
      ∑ h ∈ x.coeff.support, (if φ h = Multiplicative.ofAdd b then
        MonoidAlgebra.single h (x.coeff h) else 0) := by
    rw [degPart, MonoidAlgebra.ofCoeff_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    by_cases hc : φ h = Multiplicative.ofAdd b
    · simp only [if_pos hc, MonoidAlgebra.ofCoeff_single]
    · simp only [if_neg hc, MonoidAlgebra.ofCoeff_zero]
  rw [h1, h2, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  by_cases hc : φ h = Multiplicative.ofAdd b
  · simp only [dif_pos hc, if_pos hc]
    rw [mapSubAlg_single', MonoidAlgebra.single_mul_single, mul_one, incl_mul_zpow Lb hc]
  · simp only [dif_neg hc, if_neg hc]
    simp

end Work.ORTorsion.Support
