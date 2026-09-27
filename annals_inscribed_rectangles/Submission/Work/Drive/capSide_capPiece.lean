import Mathlib
import Submission.Work.Drive.planePt

/-!
# A cap-side projective class is a point of the cap piece

`Work.Drive.cappingSpaceHomeoProj : CappingSpace ≃ₜ (0,∞) × ℝP³` presents the four-dimensional
capping space of Hugelmeyer's Lemma 5 through the transparent coordinates.  Its `ℝP³`-coordinate is
divided by the Clifford torus `{|c₁| = |c₂|}` into the *configuration side* `{|c₁| ≥ |c₂|}` (the image
of `ConfigPiece`) and the *cap side* `{|c₁| ≤ |c₂|}` (the image of `CapPiece`), the two sides meeting
exactly on the torus.

This file proves the direction needed for the piece-by-piece constructions of the capped plane: every
projective class on the cap side (with the boundary `‖c₁ V‖ = ‖c₂ V‖` included) is the image of an
explicit point of the cap piece `(0,∞) × S¹ × D²`.  The construction inverts the cap chart
`capProjVecOf w d = (d·w/√2, w̄·√(1-‖d‖²/2))`: for a unit vector `v = (a, b)` with `‖a‖ ≤ ‖b‖` one
takes

* `w = b̄/‖b‖` (a unit complex number, the `S¹`-coordinate of the cap point, up to the square root
  `circOf (w²)`);
* `d = √2 · a · b/‖b‖` (whose norm is `√2·‖a‖ ≤ 1`),
* `Work.Drive.capProjVecOf w d = v`.

Equivalently, from the side of `Work.Drive.capSideLift`: `{|c₁| < |c₂|}` is the interior of the cap
disk `‖d‖ < 1` (`isCapVec_capProjVecOf`), `{|c₁| = |c₂|}` is its boundary `‖d‖ = 1`, and every point
of the cap side is represented as computed here.
-/

namespace Work.Drive

noncomputable section

private lemma c₁_smul_real_coe (t : ℝ) (v : Eucl 3) : c₁ (t • v) = (t : ℂ) * c₁ v := by
  simp only [c₁, PiLp.smul_apply]
  rw [smul_eq_mul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_mul]
  ring

private lemma c₂_smul_real_coe (t : ℝ) (v : Eucl 3) : c₂ (t • v) = (t : ℂ) * c₂ v := by
  simp only [c₂, PiLp.smul_apply]
  rw [smul_eq_mul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_mul]
  ring

/-- **Every cap-side projective class lies in the image of the cap piece.**  For a radius `r > 0` and
a nonzero lift `V` whose second complex coordinate dominates the first, the capping-space point
`(r, [V])` in transparent coordinates is the class of an explicit `CapPiece` element.  The disk
coordinate of that element is `√2·(a/‖V‖)·(b/‖b‖)` and its `S¹`-coordinate has square `(b̄/‖b‖)²`,
where `a = c₁ V`, `b = c₂ V`. -/
theorem capSide_capPiece {r : ℝ} (hr : 0 < r) {V : Eucl 3} (hV : V ≠ 0)
    (hside : ‖c₁ V‖ ≤ ‖c₂ V‖) :
    ∃ c : CapPiece,
      cappingSpaceHomeoProj.symm (⟨r, hr⟩, Projectivization.mk ℝ V hV) =
        Quotient.mk'' (Sum.inr c) := by
  have hVn : ‖V‖ ≠ 0 := norm_ne_zero_iff.mpr hV
  set t : ℝ := (‖V‖)⁻¹ with ht
  have htpos : 0 < t := by rw [ht]; exact inv_pos.mpr (norm_pos_iff.mpr hV)
  set v : Eucl 3 := t • V with hvt
  have hv1 : ‖v‖ = 1 := by
    rw [hvt, norm_smul, Real.norm_of_nonneg htpos.le, ht, inv_mul_cancel₀ hVn]
  have hsq : ‖c₁ v‖ ^ 2 + ‖c₂ v‖ ^ 2 = 1 := by
    rw [← norm_sq_c₁_c₂ v, hv1]; norm_num
  set a : ℂ := c₁ v with ha
  set b : ℂ := c₂ v with hb
  have hc1v : c₁ v = (t : ℂ) * c₁ V := by rw [hvt, c₁_smul_real_coe]
  have hc2v : c₂ v = (t : ℂ) * c₂ V := by rw [hvt, c₂_smul_real_coe]
  have hside' : ‖a‖ ≤ ‖b‖ := by
    rw [ha, hb, hc1v, hc2v, norm_mul, norm_mul, Complex.norm_of_nonneg htpos.le]
    exact mul_le_mul_of_nonneg_left hside htpos.le
  have ha_le : ‖a‖ ≤ 1 / Real.sqrt 2 := norm_le_inv_sqrt_two hside' hsq
  have hbne : b ≠ 0 := ne_zero_of_norm_le hside' hsq
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hbne
  set w : ℂ := star b / (‖b‖ : ℂ) with hw
  have hw1 : ‖w‖ = 1 := by
    rw [hw, norm_div, norm_star, Complex.norm_of_nonneg hbpos.le, div_self (ne_of_gt hbpos)]
  set dc : ℂ := ((Real.sqrt 2 : ℝ) : ℂ) * a * b / ((‖b‖ : ℝ) : ℂ) with hdc
  have hdc_le : ‖dc‖ ≤ 1 := by rw [hdc]; exact norm_sqrt_two_mul_div_le a b hbne ha_le
  have hdcnorm : ‖dc‖ = Real.sqrt 2 * ‖a‖ := by
    rw [hdc, norm_div, norm_mul, norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg 2),
      Complex.norm_of_nonneg hbpos.le]
    rw [mul_div_assoc, div_self (ne_of_gt hbpos), mul_one]
  have hm0 : ((‖b‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hbpos)
  have hr20 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  have hbb : b * star b = ((‖b‖ : ℝ) : ℂ) * ((‖b‖ : ℝ) : ℂ) := by
    rw [show b * star b = ((‖b‖ ^ 2 : ℝ) : ℂ) by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]]
    push_cast; ring
  have hkey1 : c₁ (capProjVecOf w dc) = a := by
    rw [c₁_capProjVecOf, hdc, hw]
    field_simp [hm0, hr20]
    rw [mul_assoc, hbb]; ring
  have hsq' : 1 - ‖dc‖ ^ 2 / 2 = ‖b‖ ^ 2 := by
    rw [hdcnorm]
    have h2 : (Real.sqrt 2 * ‖a‖) ^ 2 = 2 * ‖a‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
    rw [h2]; nlinarith [hsq]
  have hkey2 : c₂ (capProjVecOf w dc) = b := by
    rw [c₂_capProjVecOf, hw, hsq']
    rw [Real.sqrt_sq (norm_nonneg b)]
    rw [show star (star b / ((‖b‖ : ℝ) : ℂ)) = b / ((‖b‖ : ℝ) : ℂ) by
          rw [Complex.star_def, map_div₀, Complex.conj_conj, Complex.conj_ofReal]]
    field_simp [hm0]
  have hkey : capProjVecOf w dc = v := by
    refine eq_of_c₁_c₂_eq ?_ ?_
    · rw [hkey1, ha]
    · rw [hkey2, hb]
  have hw2 : ‖w ^ 2‖ = 1 := by rw [norm_pow, hw1, one_pow]
  set θ : UnitAddCircle := circOf (w ^ 2) hw2 with hθdef
  have hθ : circleOf θ = w ^ 2 := by rw [hθdef]; exact circleOf_circOf _ _
  refine ⟨⟨(r, θ, dc), hr, hdc_le⟩, ?_⟩
  have hcap := cappingSpaceHomeoProj_capPiece (r, θ, dc) hr hdc_le (w := w) hθ.symm
  apply cappingSpaceHomeoProj.injective
  rw [Homeomorph.apply_symm_apply, hcap]
  have hscal : ‖V‖ • capProjVecOf w dc = V := by
    rw [hkey, hvt, smul_smul, ht, mul_inv_cancel₀ hVn, one_smul]
  refine Prod.ext rfl ?_
  exact (Projectivization.mk_eq_mk_iff ℝ V (capProjVecOf w dc) hV _).mpr
    ⟨Units.mk0 ‖V‖ hVn, by simpa using hscal⟩

end

end Work.Drive
