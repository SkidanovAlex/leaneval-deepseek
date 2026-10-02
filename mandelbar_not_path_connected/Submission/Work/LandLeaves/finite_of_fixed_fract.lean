import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- The fixed points in `[0,1)` of `x ↦ Int.fract (M * x)` (`M ≥ 2`) are finite: they are the
`j / (M - 1)` for `0 ≤ j ≤ M - 2`. -/
theorem finite_of_fixed_fract {M : ℕ} (hM : 2 ≤ M) :
    {x : ℝ | x ∈ Set.Ico 0 1 ∧ Int.fract ((M : ℝ) * x) = x}.Finite := by
  have hMge1 : 1 ≤ M := by omega
  have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub hMge1]; norm_num
  have hpos : (0 : ℝ) < (M : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  refine Set.Finite.subset
    (Finset.finite_toSet ((Finset.range M).image (fun j : ℕ => (j : ℝ) / ((M - 1 : ℕ) : ℝ)))) ?_
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  obtain ⟨hxIco, hf⟩ := hx
  rw [Set.mem_Ico] at hxIco
  obtain ⟨hx0, hx1⟩ := hxIco
  obtain ⟨-, -, z, hz⟩ := (Int.fract_eq_iff.mp hf)
  have hzx : ((M : ℝ) - 1) * x = (z : ℝ) := by linarith
  have hz0R : (0 : ℝ) ≤ (z : ℝ) := by
    rw [← hzx]; exact mul_nonneg (le_of_lt hpos) hx0
  have hz0 : (0 : ℤ) ≤ z := Int.cast_nonneg_iff.mp hz0R
  have h1 : ((M : ℝ) - 1) * x < ((M : ℝ) - 1) := by
    have := mul_lt_mul_of_pos_left hx1 hpos
    rwa [mul_one] at this
  have hzltR : (z : ℝ) < (M : ℝ) := by linarith [hzx, h1]
  have hzltM : z < (M : ℤ) := by exact_mod_cast hzltR
  rw [Finset.mem_coe, Finset.mem_image]
  refine ⟨z.toNat, ?_, ?_⟩
  · rw [Finset.mem_range, Int.toNat_lt hz0]; exact hzltM
  · have hM1ne : ((M - 1 : ℕ) : ℝ) ≠ 0 := by
      have hpos1 : (0 : ℕ) < M - 1 := by omega
      exact_mod_cast (ne_of_gt hpos1)
    rw [div_eq_iff hM1ne]
    have hzcast : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hz0)
    rw [hzcast, ← hzx, hcast]; ring

end Work.LandLeaves
