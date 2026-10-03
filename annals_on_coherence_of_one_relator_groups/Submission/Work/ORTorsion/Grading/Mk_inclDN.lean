import Mathlib
import Submission.Work.ORTorsion.Defs

namespace Work.ORTorsion.Grading

open scoped TensorProduct

open Work.ORTorsion

open Work.ORTorsion.LaurentBase

theorem Mk_inclDN {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Algebra K U]
    (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (i : ℤ) (z : V ⊗[K] ↥(L.D Lb.N)) :
    Mk Lb i (inclDN Lb z) = if i = 0 then z else 0 := by
  -- `D(N)` sits in `R` in degree `0`: its degree-`i` coordinate is itself when `i = 0` and `0`
  -- otherwise.
  have key : ∀ d : ↥(L.D Lb.N),
      Lb.coord i ⟨(d : U), Lb.DN_le_R d.2⟩ = if i = 0 then d else 0 := by
    intro d
    have h0 : (⟨(d : U), Lb.DN_le_R d.2⟩ : ↥Lb.R)
        = Lb.rightMulU 0 ⟨(d : U), Lb.DN_le_R d.2⟩ := by
      apply Subtype.ext
      rw [Lb.rightMulU_coe]
      simp
    rw [h0]
    exact Lb.coord_base i 0 d
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero]
      by_cases h : i = 0 <;> simp [h]
  | tmul v d =>
      rw [inclDN_tmul, Mk_tmul, key d]
      by_cases h : i = 0
      · simp [h]
      · simp [h, TensorProduct.tmul_zero]
  | add z w hz hw =>
      rw [map_add, map_add, hz, hw]
      by_cases h : i = 0 <;> simp [h]

end Work.ORTorsion.Grading
