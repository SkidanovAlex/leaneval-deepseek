import Mathlib
import Submission.Work.ConCohomology.Kummer
import Submission.Work.ConCohomology.GaloisUnits

namespace Work.ConCohomology

/-- Over a separably closed field `L`, every unit of `L` is an `n`-th power as soon as
`n` is invertible in `L`; hence the subgroup of `n`-th powers of the Galois module
`Additive Lˣ` is everything. -/
lemma nPowers_units_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L] (n : ℕ)
    [IsSepClosed L] (hn : (n : L) ≠ 0) :
    nPowers (G := Gal(L/K)) (B := Additive Lˣ) n = ⊤ := by
  have hne : NeZero (n : L) := ⟨hn⟩
  rw [eq_top_iff]
  rintro x -
  show x ∈ (nsmulEqHom (G := Gal(L/K)) (B := Additive Lˣ) n).toAddMonoidHom.range
  rw [AddMonoidHom.mem_range]
  obtain ⟨z, hz⟩ := IsSepClosed.exists_pow_nat_eq (x.toMul : L) n
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hz0 : z ≠ 0 := by
    intro h
    have h2 : (0 : L) = (x.toMul : L) := by
      rw [← hz, h]
      exact (zero_pow hn0).symm
    exact Units.ne_zero x.toMul h2.symm
  refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
  rw [nsmulEqHom_apply, ← ofMul_pow]
  have hv : (Units.mk0 z hz0 : Lˣ) ^ n = x.toMul := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hz
  exact congrArg Additive.ofMul hv

end Work.ConCohomology
