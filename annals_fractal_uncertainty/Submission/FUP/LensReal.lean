import Submission.FUP.Lens

open MeasureTheory Metric Set Complex Filter
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The real lens map

`Submission/FUP/Lens.lean` defines the elementary conformal map
`lensMap q ε w = Ψ_q((1-ε)w)`, `Ψ_q = (2q/π)log((1+w)/(1-w))`, from the unit disk onto the
bounded lens `Ω_ε = Ψ_q((1-ε)𝔻)`.  Here we record its restriction to the real axis:

* `phiLens q ε : ℝ → ℝ` — the explicit formula
  `phiLens q ε x = (2q/π)·log((1+(1-ε)x)/(1-(1-ε)x))`, with
  `lensMap q ε (x:ℂ) = (phiLens q ε x : ℂ)` for `|x| < 1`;
* `hasDerivAt_phiLens` — its derivative `(2q/π)·2(1-ε)/(1-((1-ε)x)²)`;
* `phiLens_deriv_bounds` — `(1-ε)q/π ≤ phiLens' x ≤ 4q/(πε)` (the distortion bounds);
* `phiLens_strictMono` / `phiLens_injective` — it is an increasing bijection `(-1,1) → ℝ`;
* `phiLens_inv_bounds` — the same bounds for the inverse derivative.
-/

namespace Submission.FUP

/-- The restriction of the lens map to the real axis, in closed form. -/
noncomputable def phiLens (q ε x : ℝ) : ℝ :=
  (2 * q / Real.pi) * Real.log ((1 + (1-ε) * x) / (1 - (1-ε) * x))

lemma phiLens_eq_stripMap (q ε x : ℝ) :
    phiLens q ε x = (2 * q / Real.pi) *
      Real.log ((1 + (1-ε) * x) / (1 - (1-ε) * x)) := rfl

/-- On the real axis the lens map is real and given by `phiLens`. -/
lemma lensMap_ofReal_eq (q ε x : ℝ) (hx : |x| < 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    lensMap q ε (x : ℂ) = ((phiLens q ε x : ℝ) : ℂ) := by
  have ha : |(1 - ε) * x| < 1 := by
    rw [abs_mul]
    have h1 : |1 - ε| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
    nlinarith [abs_nonneg x, hx, h1, abs_nonneg (1 - ε)]
  rw [lensMap, stripMap]
  have hpos : 0 < (1 + (1 - ε) * x) / (1 - (1 - ε) * x) := by
    apply div_pos <;> linarith [abs_lt.mp ha]
  have hcast : (1 + ((((1 - ε) * x : ℝ)) : ℂ)) / (1 - ((((1 - ε) * x : ℝ)) : ℂ))
      = (((1 + (1 - ε) * x) / (1 - (1 - ε) * x) : ℝ) : ℂ) := by push_cast; ring
  have hco : ((1 - ε : ℝ) : ℂ) * (x : ℂ) = (((1 - ε) * x : ℝ) : ℂ) := by push_cast; ring
  rw [hco, hcast, ← Complex.ofReal_log hpos.le]
  simp only [phiLens]
  push_cast
  ring

/-- The derivative of the real lens map. -/
lemma hasDerivAt_phiLens {q ε x : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hx : |x| < 1) :
    HasDerivAt (phiLens q ε) ((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*x)^2))) x := by
  unfold phiLens
  set a := 1 - ε with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have ha1 : a < 1 := by rw [ha]; linarith
  have hlt : a * x < 1 := by nlinarith [(abs_lt.mp hx).2, ha0]
  have hgt : -1 < a * x := by nlinarith [(abs_lt.mp hx).1, ha0]
  have hpos : 0 < (1 + a * x) / (1 - a * x) := div_pos (by linarith) (by linarith)
  have hnum : HasDerivAt (fun x : ℝ => 1 + a * x) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).const_add 1
  have hden : HasDerivAt (fun x : ℝ => 1 - a * x) (-a) x := by
    simpa using ((hasDerivAt_id x).const_mul a).const_sub 1
  have hne : (1 - a * x) ≠ 0 := by linarith
  have hquot : HasDerivAt (fun x : ℝ => (1 + a * x) / (1 - a * x)) (2*a/(1 - a * x)^2) x := by
    refine (hnum.div hden hne).congr_deriv ?_
    field_simp
    ring
  have hlog := hquot.log (ne_of_gt hpos)
  have hfin := hlog.const_mul (2 * q / Real.pi)
  refine hfin.congr_deriv ?_
  rw [ha]
  field_simp
  ring

/-- The derivative of the real lens map is positive on `(-1,1)`. -/
lemma phiLens_deriv_pos {q ε x : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hx : |x| < 1) : 0 < (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*x)^2)) := by
  have ha : |(1-ε) * x| < 1 := by
    rw [abs_mul]
    have h1 : |1 - ε| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
    nlinarith [abs_nonneg x, hx, h1, abs_nonneg (1 - ε)]
  have h2 : 0 < 1 - ((1-ε)*x)^2 := by nlinarith [abs_lt.mp ha]
  have h3 : 0 < 1 - ε := by linarith
  positivity

end Submission.FUP

namespace Submission.FUP

/-- `phiLens q ε` is strictly increasing on `[-1,1]`. -/
lemma phiLens_strictMonoOn {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1) :
    StrictMonoOn (phiLens q ε) (Set.Icc (-1) 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
  · unfold phiLens
    refine continuousOn_const.mul ?_
    refine ContinuousOn.log ?_ ?_
    · exact (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).div
        (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)) (by
          intro x hx
          have h2 : 0 < 1 - (1-ε) * x := by nlinarith [hx.2, hε0, hε1]
          exact ne_of_gt h2)
    · intro x hx
      have h1 : 0 < 1 + (1-ε) * x := by nlinarith [hx.1, hε0, hε1]
      have h2 : 0 < 1 - (1-ε) * x := by nlinarith [hx.2, hε0, hε1]
      exact ne_of_gt (div_pos h1 h2)
  · intro x hx
    rw [interior_Icc] at hx
    have hx' : |x| < 1 := by rw [abs_lt]; exact hx
    rw [(hasDerivAt_phiLens hq hε0 hε1 hx').deriv]
    exact phiLens_deriv_pos hq hε0 hε1 hx'

/-- `phiLens q ε` is injective on `[-1,1]`. -/
lemma phiLens_injOn {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε < 1) :
    InjOn (phiLens q ε) (Set.Icc (-1) 1) :=
  (phiLens_strictMonoOn hq hε0 hε1).injOn

end Submission.FUP

namespace Submission.FUP

/-- The derivative of `phiLens` at a real point, written with the complex expression. -/
lemma lensMap_deriv_eq_phiLens_deriv {q ε x : ℝ} :
    (((1 - ε : ℝ) : ℂ) * (((2 * q / Real.pi : ℝ) : ℂ) *
        (2 / (1 - (((1 - ε : ℝ) : ℂ) * (x:ℂ)) ^ 2))))
      = (((2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*x)^2)) : ℝ) : ℂ) := by
  push_cast
  ring

/-- **Distortion bounds for the real lens map.** -/
lemma phiLens_deriv_bounds {q ε x : ℝ} (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1/2)
    (hx : |x| < 1) :
    (1-ε)*q/Real.pi ≤ (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*x)^2)) ∧
      (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*x)^2)) ≤ 4*q/(Real.pi*ε) := by
  have hnorm : ‖(x : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hle := lensMap_deriv_le hq hε0 (by linarith : ε < 1) hnorm
  have hge := lensMap_deriv_ge hq hε0 hε1 hnorm
  rw [lensMap_deriv_eq_phiLens_deriv] at hle hge
  rw [Complex.norm_real, Real.norm_eq_abs] at hle hge
  have hpos : 0 < (2*q/Real.pi) * (2*(1-ε)/(1 - ((1-ε)*x)^2)) :=
    phiLens_deriv_pos hq hε0 (by linarith : ε < 1) hx
  constructor
  · rwa [abs_of_pos hpos] at hge
  · rwa [abs_of_pos hpos] at hle

end Submission.FUP

namespace Submission.FUP
