import Mathlib

/-!
# The kernel of `M → ℚ ⊗[ℤ] M` is the torsion subgroup (pure-tensor form)

For an abelian group `M` and `h : M`, the pure tensor `1 ⊗ₜ[ℤ] h` vanishes in `ℚ ⊗[ℤ] M`
exactly when `h` has finite order.  This is the orientation in which the statement is consumed
downstream (the mirror image, `h ⊗ 1 = 0`, is `Work.Stems.RankOne.torsion_of_tmul_one_eq_zero`).

The proof goes through the localisation `ℚ ⊗[ℤ] M ≅ LocalizedModule (nonZeroDivisors ℤ) M`: the
element `1 ⊗ h` corresponds to the fraction `h / 1`, which is zero there exactly when a nonzero
integer kills `h` (`IsLocalizedModule.eq_zero_iff`).
-/

namespace Work.Stems.RankOne

noncomputable section

open TensorProduct

/-- **Torsion is exactly what dies in the rationalisation.**  If `1 ⊗ h = 0` in `ℚ ⊗[ℤ] M`, then
some positive integer multiple of `h` is zero. -/
theorem torsion_of_one_tmul_eq_zero {M : Type*} [AddCommGroup M] (h : M)
    (hzero : (1 : ℚ) ⊗ₜ[ℤ] h = 0) : ∃ N : ℕ, 0 < N ∧ N • h = 0 := by
  have hloc := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ)
      ((TensorProduct.mk ℤ ℚ M) 1)).mp hzero
  obtain ⟨s, hs⟩ := hloc
  have hs' : (s : ℤ) • h = 0 := by simpa only [Submonoid.smul_def] using hs
  have hne : (s : ℤ) ≠ 0 := (mem_nonZeroDivisors_iff_ne_zero).mp s.2
  refine ⟨s.val.natAbs, (Int.natAbs_pos).mpr hne, ?_⟩
  rw [← natCast_zsmul h s.val.natAbs]
  rcases lt_trichotomy (s : ℤ) 0 with hneg | hz | hpos
  · have h1 : (s.val.natAbs : ℤ) = -s.val := by
      rw [← Int.natAbs_neg s.val, Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ -s.val)]
    rw [h1, neg_zsmul, hs', neg_zero]
  · exact absurd hz hne
  · have h1 : (s.val.natAbs : ℤ) = s.val := Int.natAbs_of_nonneg hpos.le
    rw [h1]
    exact hs'

end

end Work.Stems.RankOne
