import Mathlib
import Submission.Work.Drive.N2Lead.mobiusArcDefs
import Submission.Work.Drive.N2Lead.mobiusArcSmooth
import Submission.Work.Drive.N2Lead.upperArcSigmaDeriv
import Submission.Work.Drive.N2.saddleModelPsi
import Submission.Work.Drive.N2.modelFlowDefs

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter
open Work.Drive.N2

noncomputable section

/-! ## Algebraic preliminaries for the angular-rate identity -/

/-- `√z · √z = z` for `z ≠ 0`. -/
lemma sqrt_mul_self_of_ne_zero {z : ℂ} (hz : z ≠ 0) : z.sqrt * z.sqrt = z := by
  rw [sqrt_eq_exp hz, ← Complex.exp_add]
  rw [show Complex.log z / 2 + Complex.log z / 2 = Complex.log z by ring]
  exact Complex.exp_log hz

/-- The model `ζ` never vanishes. -/
lemma modelZeta_ne_zero {η δ s : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (hs : 0 < s) (w : ℝ) :
    modelZeta η δ s w ≠ 0 := by
  have h : modelZeta η δ s w ∈ Complex.slitPlane :=
    modelZeta_mem_slitPlane (η := η) (δ := δ) (s := s) hδ hδ₂ hs w
  rw [Complex.mem_slitPlane_iff] at h
  intro h0
  rcases h with h | h
  · rw [h0] at h; simp at h
  · rw [h0] at h; simp at h

/-- The real part of the principal square root, in closed form. -/
lemma sqrt_re_eq (z : ℂ) : z.sqrt.re = Real.sqrt ((‖z‖ + z.re) / 2) :=
  Complex.cpow_inv_two_re z

/-- The imaginary part of `y * ↑r` for real `r`. -/
lemma im_mul_ofReal (y : ℂ) (r : ℝ) : (y * (r : ℂ)).im = y.im * r := by
  rw [Complex.mul_im]; simp

/-- `Im (conj (a - b) * (σ' + i)) = (a.re - b.re) - σ' (a.im - b.im)`. -/
lemma im_conj_sub_mul (a b : ℂ) (σ' : ℝ) :
    (star (a - b) * ((σ' : ℂ) + Complex.I)).im = (a.re - b.re) - σ' * (a.im - b.im) := by
  have h1 : (star (a - b)).re = a.re - b.re := by simp
  have h2 : (star (a - b)).im = (-a.im + b.im) := by simp
  rw [Complex.mul_im, h1, h2, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **The angular-rate identity.**  If `ρ² = ζ` and `2 ρ ρ' = σ' + i`, then
`Im (conj (ρ - 1) · ρ') = [(ζ.re - ρ.re) - σ' (ζ.im - ρ.im)] / (2 |ρ|²)`. -/
lemma im_star_sub_one_mul {ρ ρ' ζ : ℂ} {σ' : ℝ} (hζ : ρ * ρ = ζ)
    (h2 : 2 * ρ * ρ' = (σ' : ℂ) + Complex.I) :
    (star (ρ - 1) * ρ').im
      = ((ζ.re - ρ.re) - σ' * (ζ.im - ρ.im)) / (2 * (ρ.re ^ 2 + ρ.im ^ 2)) := by
  have hρ : ρ ≠ 0 := by
    intro h0
    have h := congrArg Complex.im h2
    rw [h0] at h
    simp at h
  have hpos : 0 < ρ.re ^ 2 + ρ.im ^ 2 := by
    rw [show ρ.re ^ 2 + ρ.im ^ 2 = Complex.normSq ρ by rw [Complex.normSq_apply]; ring]
    rw [Complex.normSq_pos]; exact hρ
  have hd : ρ * star ρ = ((ρ.re ^ 2 + ρ.im ^ 2 : ℝ) : ℂ) := by
    rw [show star ρ = (starRingEnd ℂ) ρ from rfl, Complex.mul_conj]
    congr 1
    rw [Complex.normSq_apply]; ring
  have hd' : 2 * (ρ * star ρ) = ((2 * (ρ.re ^ 2 + ρ.im ^ 2) : ℝ) : ℂ) := by
    rw [hd]; push_cast; ring
  have h1 : star (ρ - 1) * star ρ = star (ζ - ρ) := by
    rw [mul_comm (star (ρ - 1)) (star ρ), ← star_mul]
    congr 1
    rw [← hζ]; ring
  have hmain : star (ρ - 1) * ρ' * (2 * (ρ * star ρ)) = star (ζ - ρ) * ((σ' : ℂ) + Complex.I) := by
    have e1 : star (ρ - 1) * ρ' * (2 * (ρ * star ρ)) = star (ρ - 1) * (2 * ρ * ρ') * star ρ := by
      ring
    rw [e1, h2]
    rw [← h1]
    ring
  rw [hd'] at hmain
  have hi := congrArg Complex.im hmain
  rw [im_mul_ofReal, im_conj_sub_mul] at hi
  rw [eq_div_iff (by positivity : (2 * (ρ.re ^ 2 + ρ.im ^ 2)) ≠ 0)]
  exact hi

/-- The triangle inequality for `√(a²+b²)`. -/
lemma sqrt_sq_add_sq_le_abs (a b : ℝ) : Real.sqrt (a ^ 2 + b ^ 2) ≤ |a| + |b| := by
  have h : a ^ 2 + b ^ 2 ≤ (|a| + |b|) ^ 2 := by
    rw [add_sq, sq_abs, sq_abs]; nlinarith [abs_nonneg a, abs_nonneg b]
  calc Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt ((|a| + |b|) ^ 2) := Real.sqrt_le_sqrt h
    _ = |a| + |b| := Real.sqrt_sq (by positivity)

/-! ## The level coordinate and its derivative -/

lemma contDiff_modelSigma' (η δ s : ℝ) (hδ : 0 < δ) (h2 : 0 < 2 - 4 * δ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (modelSigma η δ s) := by
  rw [show modelSigma η δ s = fun y => s + saddleM δ y * (-η - s)
      from funext fun y => modelSigma_eq η δ s y]
  exact contDiff_const.add ((contDiff_saddleM hδ h2).mul contDiff_const)

lemma deriv_modelSigma' {η δ s : ℝ} (hδ : 0 < δ) (h2 : 0 < 2 - 4 * δ) (x : ℝ) :
    deriv (modelSigma η δ s) x = deriv (saddleM δ) x * (-η - s) := by
  have hdiff : DifferentiableAt ℝ (saddleM δ) x :=
    ((contDiff_saddleM hδ h2).differentiable (by simp)).differentiableAt
  rw [show modelSigma η δ s = fun y => s + saddleM δ y * (-η - s)
      from funext fun y => modelSigma_eq η δ s y, deriv_const_add]
  exact deriv_mul_const hdiff _

/-- On the whole window `[-2,2]` the derivative of the level coordinate `σ` is bounded by
`C₀ η / δ`.  Off the transition zone `σ` is locally constant (the derivative vanishes), and on
the transition zone `σ' = (smoothTransition' / 2δ)(-η-s)`. -/
lemma abs_deriv_modelSigma_le' {η δ s C₀ : ℝ} (hδ : 0 < δ) (h2 : 0 < 2 - 4 * δ)
    (hη : 0 < η) (hs : 0 < s) (hsη : s ≤ η)
    (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀) {w : ℝ}
    (hw : w ∈ Set.Icc (-2) 2) :
    |deriv (modelSigma η δ s) w| ≤ C₀ * η / δ := by
  have hC0nn : 0 ≤ C₀ := by
    have h := hC₀ 0; rw [uasd_st_deriv_zero, abs_zero] at h; exact h
  have hb : 0 ≤ C₀ * η / δ := div_nonneg (mul_nonneg hC0nn hη.le) hδ.le
  have hpos : ∀ {x : ℝ}, 0 < x → x ≤ 2 → |deriv (modelSigma η δ s) x| ≤ C₀ * η / δ := by
    intro x hx0 hx2
    have hηs : 0 < η + s := by linarith
    have h2δ : (0 : ℝ) < 2 * δ := by linarith
    rw [deriv_modelSigma' hδ h2 x, uasd_deriv_saddleM hx0 hx2, abs_mul, abs_div,
      abs_of_pos h2δ]
    have habs : |-η - s| = η + s := by
      rw [show -η - s = -(η + s) by ring, abs_neg, abs_of_pos hηs]
    rw [habs]
    have h1 : |deriv Real.smoothTransition ((x - (2 - 4 * δ)) / (2 * δ))| / (2 * δ)
        ≤ C₀ / (2 * δ) := div_le_div_of_nonneg_right (hC₀ _) h2δ.le
    have h2' : η + s ≤ 2 * η := by linarith
    have h3 : |deriv Real.smoothTransition ((x - (2 - 4 * δ)) / (2 * δ))| / (2 * δ) * (η + s)
        ≤ C₀ / (2 * δ) * (2 * η) :=
      mul_le_mul h1 h2' (by linarith) (by positivity)
    have h4 : C₀ / (2 * δ) * (2 * η) = C₀ * η / δ := by
      rw [div_mul_eq_mul_div]
      rw [div_eq_div_iff (by linarith : (2 * δ) ≠ 0) (ne_of_gt hδ)]
      ring
    rw [← h4]
    exact h3
  rcases lt_trichotomy w 0 with hw0 | hw0 | hw0
  · have he : (fun x : ℝ => modelSigma η δ s (-x)) = modelSigma η δ s :=
      funext (fun x => modelSigma_even η δ s x)
    have hcomp := deriv_comp_neg (modelSigma η δ s) w
    rw [he] at hcomp
    rw [hcomp, abs_neg]
    have hw1 : (0 : ℝ) < -w := by linarith
    have hw2 : -w ≤ 2 := by linarith [hw.1]
    exact hpos hw1 hw2
  · subst hw0
    have hev : modelSigma η δ s =ᶠ[𝓝 (0 : ℝ)] (fun _ => s) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) h2] with y hy
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
      rw [modelSigma_eq, saddleM_eq_zero_of_abs_le hδ (le_of_lt hy), zero_mul, add_zero]
    rw [hev.deriv_eq, deriv_const, abs_zero]
    exact hb
  · exact hpos hw0 hw.2

end

open scoped Manifold ContDiff in
/-- The model-arc rate estimate about the centre `1` of the split upper certificate
(`NOTES_LEAD_saddlePacket.md` §4.3): the model arc `w ↦ √(σ(s,w) + i w)` of the level `Re ζ = s`
has negative angular rate about the point `1`.  With `ζ = σ + iw` and `√ζ = α + iβ` the imaginary
part of `conj(√ζ − 1) · (d/dw √ζ)` is `[(σ − α) − σ′(w − β)]/(2|ζ|)`, which is negative because
`σ′ = 0` on the plateaus (where `σ = s < α` resp. `σ = −η < α`) and `|σ′|(|w| + |β|) ≤ 3C₀η/δ` in
the transition zone `|w| ∈ [2 − 4δ, 2 − 2δ]`, where `α ≥ 0.9`. -/
theorem modelArc_cross_about_one {η δ s C₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η)
    (hη' : η < 1 / 10) (hs : 0 < s) (hsη : s ≤ η) (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀)
    (hsmall : 8 * C₀ * η ≤ δ) (w : ℝ) (hw : w ∈ Set.Icc (-2) 2) :
    (star (Work.Drive.N2Lead.mobiusRho η δ s w - 1)
      * deriv (fun u : ℝ => Work.Drive.N2Lead.mobiusRho η δ s u) w).im < 0 := by
  have hδ₂ : δ < 1 / 2 := by linarith
  have h2δ : 0 < 2 - 4 * δ := by linarith
  set ρ : ℂ := mobiusRho η δ s w with hρdef
  set ρ' : ℂ := deriv (fun u : ℝ => mobiusRho η δ s u) w with hρ'def
  set ζ : ℂ := modelZeta η δ s w with hζdef
  set σ : ℝ := modelSigma η δ s w with hσdef
  set σ' : ℝ := deriv (modelSigma η δ s) w with hσ'def
  have hζeq : ρ * ρ = ζ := by
    rw [hρdef, hζdef]
    exact sqrt_mul_self_of_ne_zero (modelZeta_ne_zero hδ hδ₂ hs w)
  have hrel : 2 * ρ * ρ' = (σ' : ℂ) + Complex.I := by
    have hdiff : DifferentiableAt ℝ (fun u : ℝ => mobiusRho η δ s u) w :=
      ((mobiusRho_contDiff (η := η) hδ hδ₂ hs).differentiable (by simp)).differentiableAt
    have hfun : (fun u : ℝ => (mobiusRho η δ s u) ^ 2) = (fun u : ℝ => modelZeta η δ s u) := by
      funext u
      rw [pow_two]
      exact sqrt_mul_self_of_ne_zero (modelZeta_ne_zero hδ hδ₂ hs u)
    have hL : HasDerivAt (fun u : ℝ => (mobiusRho η δ s u) ^ 2) (2 * ρ * ρ') w := by
      have hd := hdiff.hasDerivAt.pow 2
      refine hd.congr_deriv ?_
      rw [hρdef, hρ'def]
      simp
    have hσdiff : DifferentiableAt ℝ (modelSigma η δ s) w :=
      ((contDiff_modelSigma' η δ s hδ h2δ).differentiable (by simp)).differentiableAt
    have hR : HasDerivAt (fun u : ℝ => modelZeta η δ s u) ((σ' : ℂ) + Complex.I) w := by
      have h1 : HasDerivAt (fun u : ℝ => ((modelSigma η δ s u : ℂ))) ((σ' : ℂ)) w := by
        rw [hσ'def]
        exact HasDerivAt.ofReal_comp hσdiff.hasDerivAt
      have h2' : HasDerivAt (fun u : ℝ => (u : ℂ) * Complex.I) Complex.I w := by
        have hh := HasDerivAt.ofReal_comp (hasDerivAt_id w)
        have hh2 := hh.mul_const Complex.I
        simpa using hh2
      have hsum := h1.add h2'
      have hfun2 : (fun u : ℝ => modelZeta η δ s u)
          = (fun u : ℝ => ((modelSigma η δ s u : ℂ)) + (u : ℂ) * Complex.I) := rfl
      rw [hfun2]
      exact hsum
    exact (hfun ▸ hL).unique hR
  -- the coordinate relation `α² - β² = σ`
  have hα2β2 : ρ.re ^ 2 - ρ.im ^ 2 = σ := by
    have h := congrArg Complex.re hζeq
    rw [Complex.mul_re] at h
    rw [hζdef, modelZeta_re] at h
    rw [hσdef]
    rw [pow_two, pow_two]
    exact h
  have hN : ρ.re ^ 2 + ρ.im ^ 2 = ‖ζ‖ := by
    have h1 : ‖ρ‖ ^ 2 = ‖ζ‖ := by rw [← hζeq, norm_mul]; ring
    rw [Complex.sq_norm, Complex.normSq_apply] at h1
    rw [← h1]; ring
  have hαnn : 0 ≤ ρ.re := by
    have h : ρ.re = Real.sqrt ((‖ζ‖ + ζ.re) / 2) := by
      rw [hρdef, hζdef]
      exact sqrt_re_eq _
    rw [h]; positivity
  have hσabs : |σ| ≤ η := by rw [hσdef]; exact uasd_abs_modelSigma_le hη hs hsη w
  have hσle : σ ≤ η := (abs_le.mp hσabs).2
  have hwabs : |w| ≤ 2 := abs_le.mpr hw
  have hσ'bound : |σ'| ≤ C₀ * η / δ := by
    rw [hσ'def]; exact abs_deriv_modelSigma_le' hδ h2δ hη hs hsη hC₀ hw
  have hζre : ζ.re = σ := by rw [hζdef, modelZeta_re, hσdef]
  have hζim : ζ.im = w := by rw [hζdef, modelZeta_im]
  -- the numerator is negative
  have hNum : (ζ.re - ρ.re) - σ' * (ζ.im - ρ.im) < 0 := by
    rw [hζre, hζim]
    rcases lt_or_ge |w| (2 - 4 * δ) with hwlt | hwge
    · -- the small plateau: `σ = s`, `σ' = 0` and `s < α`
      have hσeq : σ = s := by
        rw [hσdef, modelSigma_eq, saddleM_eq_zero_of_abs_le hδ (le_of_lt hwlt), zero_mul,
          add_zero]
      have hσ'eq : σ' = 0 := by
        rw [hσ'def]
        have hr : 0 < (2 - 4 * δ - |w|) / 2 := by linarith [abs_nonneg w]
        have hev : modelSigma η δ s =ᶠ[𝓝 w] (fun _ => s) := by
          filter_upwards [Metric.ball_mem_nhds w hr] with y hy
          rw [Metric.mem_ball, Real.dist_eq] at hy
          have hy2 : |y| < 2 - 4 * δ := by
            have h2' : |y| ≤ |y - w| + |w| := by
              calc |y| = |(y - w) + w| := by ring_nf
                _ ≤ |y - w| + |w| := abs_add_le _ _
            linarith
          rw [modelSigma_eq, saddleM_eq_zero_of_abs_le hδ hy2.le, zero_mul, add_zero]
        rw [hev.deriv_eq, deriv_const]
      rw [hσeq, hσ'eq, zero_mul, sub_zero]
      have hαgt : s < ρ.re := by
        have h1 : s ≤ ρ.re ^ 2 := by nlinarith [hα2β2, hσeq, sq_nonneg ρ.im]
        have h2 : Real.sqrt s ≤ ρ.re := by
          rw [← Real.sqrt_sq hαnn]
          exact Real.sqrt_le_sqrt h1
        have h3 : s < Real.sqrt s := by
          rw [Real.lt_sqrt hs.le]
          nlinarith [hs, hη']
        linarith
      linarith
    · -- the transition zone and the far plateau
      have hσ'' : |σ'| ≤ 1 / 8 := by
        have h : C₀ * η / δ ≤ 1 / 8 := by
          rw [div_le_iff₀ hδ]; linarith
        linarith [hσ'bound]
      have hα2 : (3 : ℝ) / 4 < ρ.re ^ 2 := by
        have h1 : |w| ≤ ‖ζ‖ := by
          have h := Complex.abs_im_le_norm ζ
          rw [hζdef, modelZeta_im] at h
          rw [hζdef]
          exact h
        have h5 : σ ≥ -η := (abs_le.mp hσabs).1
        have h3 : (3 : ℝ) / 2 < ‖ζ‖ + σ := by linarith [h1, hwge, h5, hδ', hη']
        have h6 : 2 * ρ.re ^ 2 = ‖ζ‖ + σ := by linarith
        linarith
      have hαgt : (0.85 : ℝ) < ρ.re := by nlinarith [hαnn, hα2]
      have hασ : (3 : ℝ) / 4 < ρ.re - σ := by linarith [hαgt, hσle, hη']
      have hβ2 : ρ.im ^ 2 < 4 := by
        have h1 : ρ.im ^ 2 ≤ ‖ζ‖ := by linarith [hN, sq_nonneg ρ.re]
        have h2 : ‖ζ‖ < 3 := by
          have h3 : ‖ζ‖ = Real.sqrt (σ ^ 2 + w ^ 2) := by
            rw [hζdef, norm_modelZeta, hσdef]
          rw [h3]
          have h4 : Real.sqrt (σ ^ 2 + w ^ 2) ≤ |σ| + |w| := sqrt_sq_add_sq_le_abs σ w
          linarith [hσabs, hwabs]
        linarith
      have hβabs : |ρ.im| < 2 := by
        rw [abs_lt]
        constructor <;> nlinarith [hβ2]
      have hwβ : |w - ρ.im| < 4 := by
        have h1 : |w - ρ.im| ≤ |w| + |ρ.im| := by
          calc |w - ρ.im| = |w + (-ρ.im)| := by ring_nf
            _ ≤ |w| + |-ρ.im| := abs_add_le _ _
            _ = |w| + |ρ.im| := by rw [abs_neg]
        linarith
      have hterm : -(σ' * (w - ρ.im)) ≤ 1 / 2 := by
        have h1 : |σ' * (w - ρ.im)| ≤ (1 / 8) * 4 := by
          rw [abs_mul]
          exact mul_le_mul hσ'' hwβ.le (abs_nonneg _) (by norm_num)
        have h2 : -(σ' * (w - ρ.im)) ≤ |σ' * (w - ρ.im)| := neg_le_abs _
        linarith
      linarith
  have him : (star (ρ - 1) * ρ').im
      = ((ζ.re - ρ.re) - σ' * (ζ.im - ρ.im)) / (2 * ‖ζ‖) := by
    rw [im_star_sub_one_mul hζeq hrel, hN]
  have hpos : (0 : ℝ) < 2 * ‖ζ‖ := by
    rw [hζdef]
    exact mul_pos two_pos (norm_pos_iff.mpr (modelZeta_ne_zero hδ hδ₂ hs w))
  rw [him]
  exact div_neg_of_neg_of_pos hNum hpos

end Work.Drive.N2Lead
