import Mathlib
import Submission.Work.FatouCoord.Flower.GermDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SatFree

open Work.FatouCoord.Flower

/-! ## Elementary estimates for the wide gauge `sgauge W = Re W + |Im W|` -/

/-- The wide gauge is dominated by twice the norm: `|Re W| ≤ ‖W‖` and `|Im W| ≤ ‖W‖`. -/
lemma sgauge_le_two_mul_norm (W : ℂ) : sgauge W ≤ 2 * ‖W‖ := by
  have h1 : W.re ≤ ‖W‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm W)
  have h2 : |W.im| ≤ ‖W‖ := Complex.abs_im_le_norm W
  simp only [sgauge]
  linarith

/-- The gauge is invariant under complex conjugation (hence under `star`). -/
lemma sgauge_star (W : ℂ) : sgauge (star W) = sgauge W := by
  rw [Complex.star_def, sgauge, sgauge, Complex.conj_re, Complex.conj_im, abs_neg]

/-- `sgauge` is `2`-Lipschitz for the Euclidean norm (one-sided form). -/
lemma sgauge_sub_le (w η : ℂ) : sgauge w - sgauge (w + η) ≤ 2 * ‖η‖ := by
  have hkey : |w.im| - |η.im| ≤ |w.im + η.im| := by
    have h := abs_sub (w.im + η.im) η.im
    rw [add_sub_cancel_right] at h
    linarith
  have h2 : sgauge w - sgauge (w + η) ≤ -η.re + |η.im| := by
    simp only [sgauge, Complex.add_re, Complex.add_im]
    linarith
  have h3 : -η.re ≤ ‖η‖ := by
    have h := Complex.abs_re_le_norm η
    rw [abs_le] at h
    linarith
  have h4 : |η.im| ≤ ‖η‖ := Complex.abs_im_le_norm η
  linarith

/-- A point of the wide sector of level `M > 0` has chart coordinate `-1/u` of norm `> M/2`,
equivalently `‖u‖ < 2/M`. -/
lemma norm_lt_of_sgauge {M : ℝ} (hM : 0 < M) {u : ℂ} (hu : u ≠ 0)
    (h : M < sgauge (-1 / u)) : ‖u‖ < 2 / M := by
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hWnorm : ‖(-1 : ℂ) / u‖ = 1 / ‖u‖ := by rw [norm_div]; simp
  have h1 : M < 2 / ‖u‖ := by
    have h2 : M < 2 * ‖(-1 : ℂ) / u‖ := lt_of_lt_of_le h (sgauge_le_two_mul_norm _)
    rwa [hWnorm, mul_one_div] at h2
  rw [lt_div_iff₀ hM]
  rw [lt_div_iff₀ hu_pos] at h1
  linarith

/-- In particular, if `M ≥ 2/ρ` then the wide sector of level `M` sits inside the ball of
radius `ρ`. -/
lemma widePetal_norm_lt {M ρ : ℝ} (hρ : 0 < ρ) (hM2 : 2 / ρ ≤ M) {u : ℂ} (hu : u ≠ 0)
    (h : M < sgauge (-1 / u)) : ‖u‖ < ρ := by
  have hMpos : 0 < M := lt_of_lt_of_le (div_pos two_pos hρ) hM2
  have h1 : ‖u‖ < 2 / M := norm_lt_of_sgauge hMpos hu h
  have h2 : 2 / M ≤ ρ := by
    rw [div_le_iff₀ hMpos]
    have h3 := mul_le_mul_of_nonneg_left hM2 hρ.le
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hρ)] at h3
    linarith
  linarith

/-- **An antiholomorphic square root tangent to conjugation loses only `O(1)` of `sgauge`.**

Setting: `gU` is an antiholomorphic square root of the parabolic germ, tangent to conjugation in
the quantitative form `‖gU z - star z‖ ≤ G₀ * ‖z‖²` for `‖z‖ < ρ`.

Claim: in the parabolic chart `W = -1/u`, the induced map `gU` moves the *wide* gauge `sgauge` by
at most a bounded amount: there are `M C` with `0 ≤ C` such that
`sgauge (-1/(gU u)) ≥ sgauge (-1/u) - C` for every `u ≠ 0` with `sgauge (-1/u) > M`.

Proof: `sgauge (-1/u) > M` forces `‖u‖ ≤ 2/M < ρ`, so `‖gU u - star u‖ ≤ G₀ ‖u‖²`; then
`-1/(gU u) + 1/(star u) = (gU u - star u) / (gU u * star u)` has norm `≤ G₀‖u‖² / (‖u‖²/2)
= 2G₀` (using `‖gU u‖ ≥ ‖u‖ - G₀‖u‖² ≥ ‖u‖/2`), and `-1/(star u) = star (-1/u)` has the same
`sgauge` as `-1/u`; finally `|sgauge (w + η) - sgauge w| ≤ 2 ‖η‖`.  In particular `gU` maps the
wide petal of level `M + C` into the wide petal of level `M`. -/
theorem gU_sgauge_loss {gU : ℂ → ℂ} {G₀ ρ : ℝ} (hρ : 0 < ρ)
    (hgl : ∀ z : ℂ, ‖z‖ < ρ → ‖gU z - star z‖ ≤ G₀ * ‖z‖ ^ 2) :
    ∃ M C : ℝ, 0 ≤ C ∧ ∀ u : ℂ, u ≠ 0 → M < Work.FatouCoord.Flower.sgauge (-1 / u) →
      Work.FatouCoord.Flower.sgauge (-1 / (gU u)) ≥
        Work.FatouCoord.Flower.sgauge (-1 / u) - C := by
  by_cases hG : 0 ≤ G₀
  · -- The interesting case: `G₀ ≥ 0`, we may take `C = 4 G₀`.
    refine ⟨max 1 (max (2 / ρ) (4 * G₀ + 1)), 4 * G₀, by linarith, ?_⟩
    set M : ℝ := max 1 (max (2 / ρ) (4 * G₀ + 1)) with hMdef
    have hM2 : 2 / ρ ≤ M := by
      rw [hMdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hM3 : 4 * G₀ + 1 ≤ M := by
      rw [hMdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hMpos : 0 < M := lt_of_lt_of_le (div_pos two_pos hρ) hM2
    intro u hu hMu
    have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hu_rho : ‖u‖ < ρ := widePetal_norm_lt hρ hM2 hu hMu
    have hu_bound : ‖u‖ < 2 / M := norm_lt_of_sgauge hMpos hu hMu
    -- `G₀ ‖u‖ < 1/2`
    have hG0u : G₀ * ‖u‖ < 1 / 2 := by
      have hden : 0 < 4 * G₀ + 1 := by linarith
      have h2M' : 2 / M ≤ 2 / (4 * G₀ + 1) :=
        div_le_div_of_nonneg_left (by norm_num) hden hM3
      have h1 : G₀ * ‖u‖ ≤ G₀ * (2 / M) :=
        mul_le_mul_of_nonneg_left (le_of_lt hu_bound) hG
      have h2 : G₀ * (2 / M) ≤ G₀ * (2 / (4 * G₀ + 1)) :=
        mul_le_mul_of_nonneg_left h2M' hG
      have h3 : G₀ * (2 / (4 * G₀ + 1)) < 1 / 2 := by
        rw [← mul_div_assoc, div_lt_iff₀ hden]
        linarith
      linarith
    have hnum : ‖gU u - star u‖ ≤ G₀ * ‖u‖ ^ 2 := hgl u hu_rho
    -- `‖gU u‖ ≥ ‖u‖/2`
    have hx_lower : ‖u‖ / 2 ≤ ‖gU u‖ := by
      have h1 : ‖star u‖ ≤ ‖gU u‖ + ‖gU u - star u‖ := by
        calc ‖star u‖ = ‖gU u - (gU u - star u)‖ := by ring_nf
          _ ≤ ‖gU u‖ + ‖gU u - star u‖ := norm_sub_le _ _
      rw [norm_star] at h1
      have hsq : G₀ * ‖u‖ ^ 2 < ‖u‖ / 2 := by
        have h := mul_lt_mul_of_pos_right hG0u hu_pos
        nlinarith [h]
      linarith
    have hx_pos : 0 < ‖gU u‖ := lt_of_lt_of_le (by linarith : (0 : ℝ) < ‖u‖ / 2) hx_lower
    have hy_pos : 0 < ‖star u‖ := by rw [norm_star]; exact hu_pos
    have hx_ne : gU u ≠ 0 := norm_pos_iff.mp hx_pos
    have hy_ne : star u ≠ 0 := norm_pos_iff.mp hy_pos
    have hquot : -1 / (gU u) + 1 / (star u) = (gU u - star u) / (gU u * star u) := by
      field_simp
      ring
    -- `η = -1/(gU u) - (-1/(star u)) = -1/(gU u) + 1/(star u)` has norm `≤ 2 G₀`.
    have hη_bound : ‖-1 / (gU u) + 1 / (star u)‖ ≤ 2 * G₀ := by
      rw [hquot, norm_div, norm_mul]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < ‖gU u‖ * ‖star u‖)]
      have hden : (‖u‖ / 2) * ‖u‖ ≤ ‖gU u‖ * ‖star u‖ := by
        rw [norm_star]
        exact mul_le_mul_of_nonneg_right hx_lower (norm_nonneg u)
      have h2G : 0 ≤ 2 * G₀ := by linarith
      have hbase : (2 * G₀) * ((‖u‖ / 2) * ‖u‖) ≤ (2 * G₀) * (‖gU u‖ * ‖star u‖) :=
        mul_le_mul_of_nonneg_left hden h2G
      have heq : (2 * G₀) * ((‖u‖ / 2) * ‖u‖) = G₀ * ‖u‖ ^ 2 := by ring
      linarith [hnum, hbase, heq]
    have hb : (-1 : ℂ) / (star u) = star ((-1 : ℂ) / u) := by
      rw [Complex.star_def]
      simp only [map_div₀]
      simp
    have hkey := sgauge_sub_le ((-1 : ℂ) / (star u)) (-1 / (gU u) + 1 / (star u))
    have hsum : (-1 : ℂ) / (star u) + (-1 / (gU u) + 1 / (star u)) = -1 / (gU u) := by ring
    rw [hsum, hb, sgauge_star] at hkey
    have h2 : 2 * ‖-1 / (gU u) + 1 / (star u)‖ ≤ 4 * G₀ := by linarith
    linarith
  · -- If `G₀ < 0` the tangency hypothesis is contradictory inside the ball of radius `ρ`,
    -- so the statement holds vacuously.
    have hGneg : G₀ < 0 := lt_of_not_ge hG
    refine ⟨max 1 (max (2 / ρ) (4 * G₀ + 1)), 0, le_refl 0, ?_⟩
    set M : ℝ := max 1 (max (2 / ρ) (4 * G₀ + 1)) with hMdef
    have hM2 : 2 / ρ ≤ M := by
      rw [hMdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    intro u hu hMu
    exfalso
    have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hu_rho : ‖u‖ < ρ := widePetal_norm_lt hρ hM2 hu hMu
    have h1 : ‖gU u - star u‖ ≤ G₀ * ‖u‖ ^ 2 := hgl u hu_rho
    have h2 : 0 ≤ ‖gU u - star u‖ := norm_nonneg _
    have h3 : G₀ * ‖u‖ ^ 2 < 0 := by
      have hp : 0 < ‖u‖ ^ 2 := pow_pos hu_pos 2
      nlinarith
    linarith

end Work.SatFree
