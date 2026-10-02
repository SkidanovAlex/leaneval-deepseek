import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The vertical slice of a near-identity map is a bijection

If `ψ : ℂ → ℂ` is a small perturbation of the identity on the right half-plane
`{Re > N}` — precisely, `‖ψ w₂ - ψ w₁ - (w₂ - w₁)‖ ≤ C ‖w₂ - w₁‖` for all `w₁, w₂`
with `N < Re wᵢ` and some `C < 1` — then for every `s > N` the real map

  `t ↦ Im (ψ (s + t·i))`

is a bijection `ℝ → ℝ`.

Indeed the deviation `F t - t` is `C`-Lipschitz in `t` (with `C < 1`), so `F` is
`(1-C)`-expanding, hence injective, and `(1+C)`-Lipschitz, hence continuous; the same
`(1-C)`-expansion forces `F t → ±∞` as `t → ±∞`, so the intermediate value theorem
supplies the unique preimage of every point.
-/

namespace Work.GATE2.PL

/-- The imaginary part of `ψ w₂ - ψ w₁ - (w₂ - w₁)` is bounded by `C ‖w₂ - w₁‖`
whenever `ψ` is a `C`-near-identity on `{Re > N}` and both points lie there. -/
lemma abs_im_sub_le_of_pair {ψ : ℂ → ℂ} {N C : ℝ}
    (hpair : ∀ w₁ w₂ : ℂ, N < w₁.re → N < w₂.re →
      ‖ψ w₂ - ψ w₁ - (w₂ - w₁)‖ ≤ C * ‖w₂ - w₁‖)
    {w₁ w₂ : ℂ} (h₁ : N < w₁.re) (h₂ : N < w₂.re) :
    |(ψ w₂).im - (ψ w₁).im - (w₂ - w₁).im| ≤ C * ‖w₂ - w₁‖ := by
  have h := hpair w₁ w₂ h₁ h₂
  have him : (ψ w₂ - ψ w₁ - (w₂ - w₁)).im = (ψ w₂).im - (ψ w₁).im - (w₂ - w₁).im := by
    simp [Complex.sub_im]
  rw [← him]
  exact (Complex.abs_im_le_norm _).trans h

theorem existsUnique_im_eq_of_pair {ψ : ℂ → ℂ} {N C : ℝ} (hC : C < 1)
    (hpair : ∀ w₁ w₂ : ℂ, N < w₁.re → N < w₂.re →
      ‖ψ w₂ - ψ w₁ - (w₂ - w₁)‖ ≤ C * ‖w₂ - w₁‖)
    {s : ℝ} (hs : N < s) (y : ℝ) : ∃! t : ℝ, (ψ (s + (t : ℂ) * Complex.I)).im = y := by
  -- `hpair` forces `0 ≤ C`: it says `‖·‖ ≤ C * 1` for a pair of points one apart.
  have hC0 : 0 ≤ C := by
    have h := hpair (s : ℂ) ((s + 1 : ℝ) : ℂ) (by simpa using hs) (by
      simp only [Complex.ofReal_re]; linarith)
    have hsub : ((s + 1 : ℝ) : ℂ) - (s : ℂ) = 1 := by
      rw [← Complex.ofReal_sub]; norm_num
    have hnorm : ‖ψ (((s + 1 : ℝ) : ℂ)) - ψ (s : ℂ) - 1‖ ≤ C := by
      rwa [hsub, norm_one, mul_one] at h
    exact le_trans (norm_nonneg _) hnorm
  -- The vertical line `t ↦ s + t·i` and the slice `F t = Im (ψ (s + t·i))`.
  let w : ℝ → ℂ := fun t => s + (t : ℂ) * Complex.I
  let F : ℝ → ℝ := fun t => (ψ (w t)).im
  have hwre : ∀ t, (w t).re = s := fun t => by simp [w]
  have hwsub : ∀ t t', w t - w t' = ((t - t' : ℝ) : ℂ) * Complex.I := by
    intro t t'; apply Complex.ext <;> simp [w]
  have hwnorm : ∀ t t', ‖w t - w t'‖ = |t - t'| := by
    intro t t'
    rw [hwsub t t', norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have himsub : ∀ t t', (w t - w t').im = t - t' := by
    intro t t'; rw [hwsub t t', Complex.mul_I_im, Complex.ofReal_re]
  -- The deviation of `F` from the identity is `C`-Lipschitz.
  have hkey : ∀ t t', |F t - F t' - (t - t')| ≤ C * |t - t'| := by
    intro t t'
    have h := abs_im_sub_le_of_pair (w₁ := w t') (w₂ := w t) hpair
      (by rw [hwre t']; exact hs) (by rw [hwre t]; exact hs)
    rw [hwnorm t t'] at h
    have heq : |F t - F t' - (t - t')| = |(ψ (w t)).im - (ψ (w t')).im - (w t - w t').im| := by
      dsimp only [F]; rw [himsub t t']
    rw [heq]; exact h
  -- Upper Lipschitz bound, hence continuity.
  have hUp : ∀ t t', |F t - F t'| ≤ (C + 1) * |t - t'| := by
    intro t t'
    have h := hkey t t'
    calc |F t - F t'| = |(F t - F t' - (t - t')) + (t - t')| := by congr 1; ring
      _ ≤ |F t - F t' - (t - t')| + |t - t'| := abs_add_le _ _
      _ ≤ C * |t - t'| + |t - t'| := add_le_add h (le_refl _)
      _ = (C + 1) * |t - t'| := by ring
  -- Lower expansive bound, hence injectivity.
  have hLow : ∀ t t', (1 - C) * |t - t'| ≤ |F t - F t'| := by
    intro t t'
    have h := hkey t t'
    have hsplit : |t - t'| ≤ |(t - t') - (F t - F t')| + |F t - F t'| := by
      calc |t - t'| = |((t - t') - (F t - F t')) + (F t - F t')| := by congr 1; ring
        _ ≤ |(t - t') - (F t - F t')| + |F t - F t'| := abs_add_le _ _
    have habs : |(t - t') - (F t - F t')| = |F t - F t' - (t - t')| := by rw [abs_sub_comm]
    rw [habs] at hsplit
    linarith
  have hinj : ∀ t t', F t = F t' → t = t' := by
    intro t t' h
    have hl := hLow t t'
    rw [h, sub_self, abs_zero] at hl
    have h1 : (1 - C) * |t - t'| = 0 := le_antisymm hl (mul_nonneg (by linarith) (abs_nonneg _))
    have h2 : |t - t'| = 0 := by
      rcases mul_eq_zero.mp h1 with hh | hh
      · linarith
      · exact hh
    exact sub_eq_zero.mp (abs_eq_zero.mp h2)
  have hcont : Continuous F := by
    have hLip : LipschitzWith (Real.toNNReal (C + 1)) F := by
      rw [lipschitzWith_iff_dist_le_mul]
      intro t t'
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by linarith)]
      exact hUp t t'
    exact hLip.continuous
  -- The identity-deviation bound based at `0`, used for the far-field limits.
  have hbnd : ∀ t, |F t - F 0 - t| ≤ C * |t| := by
    intro t; have h := hkey t 0; simpa using h
  set R : ℝ := (y - F 0) / (1 - C)
  have hpos : 0 < 1 - C := by linarith
  have hR : (1 - C) * R = y - F 0 := by
    simp only [R]; field_simp
  set tP : ℝ := max R 0 + 1
  set tM : ℝ := min R 0 - 1
  have htPpos : 0 < tP := by have : 0 ≤ max R 0 := le_max_right _ _; simp only [tP]; linarith
  have htPR : R < tP := by have : R ≤ max R 0 := le_max_left _ _; simp only [tP]; linarith
  have htMneg : tM < 0 := by have : min R 0 ≤ 0 := min_le_right _ _; simp only [tM]; linarith
  have htMR : tM < R := by have : min R 0 ≤ R := min_le_left _ _; simp only [tM]; linarith
  have hFP : y < F tP := by
    have h := hbnd tP
    rw [abs_of_nonneg htPpos.le] at h
    have h2 : -(C * tP) ≤ F tP - F 0 - tP := neg_le_of_abs_le h
    have : (1 - C) * R < (1 - C) * tP := mul_lt_mul_of_pos_left htPR hpos
    rw [hR] at this
    linarith
  have hFM : F tM < y := by
    have h := hbnd tM
    rw [abs_of_nonpos htMneg.le] at h
    have h2 : F tM - F 0 - tM ≤ C * (-tM) := (abs_le.mp h).2
    have : (1 - C) * tM < (1 - C) * R := mul_lt_mul_of_pos_left htMR hpos
    rw [hR] at this
    linarith
  have htMtP : tM < tP := by linarith
  obtain ⟨t, hFt⟩ : ∃ t, F t = y := by
    have hy : y ∈ Set.Icc (F tM) (F tP) := ⟨le_of_lt hFM, le_of_lt hFP⟩
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc htMtP.le hcont.continuousOn hy
    exact ⟨t, ht⟩
  refine ⟨t, ?_, ?_⟩
  · exact hFt
  · intro t' ht'
    exact hinj t' t (ht'.trans hFt.symm)

end Work.GATE2.PL
