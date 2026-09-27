import Mathlib
import Submission.Work.Drive.N2.saddleModelPsi
import Submission.Work.Drive.N2Lead.mobiusGeomDefs
import Submission.Work.Drive.N2Lead.modelArc_im_strictMonoOn
import Submission.Work.Drive.N2Lead.modelArc_cross_about_one

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter
open Work.Drive.N2

noncomputable section

/-! ## Helpers valid at levels of either sign

The sibling `modelArc_cross_about_one` is stated for positive levels `0 < s ≤ η`; the result below
extends it to `s ∈ [-η, η]`.  Only three inputs of the sibling's argument are sign-sensitive, and
each is replaced here by a version valid on the whole window `[-η, η]`:

* the level coordinate is bounded, `|σ| ≤ η` (the sibling's `uasd_abs_modelSigma_le` takes `0 < s`);
* its derivative is bounded by `C₀ η / δ` (the sibling's `abs_deriv_modelSigma_le'` takes `0 < s`);
* in the plateau, `σ = s` must be strictly below the real part of `ρ = √ζ` — at a level `s ≤ 0`
  this is the elementary `re_lt_re_sqrt` below (there `ρ.re ≥ 0`, and `= 0` is excluded by `w ≠ 0`,
  since `ζ = σ + i w` is then non-real).

The branch-cut problem at `w = 0` (where `ζ = s ≤ 0` and `√` is discontinuous) is exactly what the
hypothesis `w ≠ 0` removes: for `w ≠ 0` the imaginary part of `ζ` is `w ≠ 0`, so `ζ` lies in
`Complex.slitPlane` and `√` is smooth there. -/

/-- **`Re √z > Re z` for `z ≠ 0` with `Re z < 1`.**  If `Re z < 0` this is `Re √z ≥ 0 > Re z`; if
`Re z = 0` then `Re √z > 0` (the root cannot vanish); and if `0 < Re z < 1` then
`Re z < √(Re z) ≤ Re √z`. -/
lemma re_lt_re_sqrt {z : ℂ} (hz : z ≠ 0) (hre : z.re < 1) : z.re < z.sqrt.re := by
  have hsq : z.sqrt.re ^ 2 - z.sqrt.im ^ 2 = z.re := by
    have h := congrArg Complex.re (sqrt_mul_self_of_ne_zero hz)
    rw [Complex.mul_re] at h
    rw [pow_two, pow_two]
    exact h
  have hnn : 0 ≤ z.sqrt.re := by
    rw [sqrt_re_eq]; positivity
  rcases lt_or_ge z.re 0 with hlt | hge
  · linarith
  · rcases eq_or_lt_of_le hge with heq | hgt
    · have hpos : 0 < z.sqrt.re := by
        by_contra hcon
        have hre_sqrt : z.sqrt.re = 0 := le_antisymm (le_of_not_gt hcon) hnn
        have him : z.sqrt.im = 0 := by
          have h2 : z.sqrt.im ^ 2 = 0 := by nlinarith [hsq, heq, hre_sqrt]
          have h2' : z.sqrt.im * z.sqrt.im = 0 := by simpa [sq] using h2
          exact mul_self_eq_zero.mp h2'
        have hz0 : z.sqrt = 0 := Complex.ext (by simpa using hre_sqrt) (by simpa using him)
        exact hz (by rw [← sqrt_mul_self_of_ne_zero hz, hz0]; ring)
      linarith
    · have h1 : z.re ≤ z.sqrt.re ^ 2 := by linarith [hsq, sq_nonneg z.sqrt.im]
      have h2 : Real.sqrt z.re ≤ z.sqrt.re := by
        rw [← Real.sqrt_sq hnn]; exact Real.sqrt_le_sqrt h1
      have h3 : z.re < Real.sqrt z.re := by
        rw [Real.lt_sqrt hgt.le]; nlinarith
      linarith

/-- The model `ζ w = σ + i w` never vanishes when `w ≠ 0` (its imaginary part is `w`). -/
lemma modelZeta_ne_zero_of_ne {η δ s w : ℝ} (hw0 : w ≠ 0) : modelZeta η δ s w ≠ 0 := by
  intro h
  have h2 := congrArg Complex.im h
  rw [modelZeta_im] at h2
  exact hw0 h2

/-- The level coordinate is bounded by `η` in absolute value on the whole window `s ∈ [-η, η]`
(the sibling `uasd_abs_modelSigma_le` for `0 < s ≤ η`). -/
lemma abs_modelSigma_le_Icc {η δ s : ℝ} (hs : s ∈ Set.Icc (-η) η) (w : ℝ) :
    |modelSigma η δ s w| ≤ η := by
  have hM := uasd_saddleM_mem_Icc δ w
  have hc : -η - s ≤ 0 := by linarith [hs.1]
  rw [abs_le]
  constructor
  · have h1 : (1:ℝ) * (-η - s) ≤ saddleM δ w * (-η - s) :=
      mul_le_mul_of_nonpos_right hM.2 hc
    rw [modelSigma_eq]
    linarith [hs.1]
  · have h2 : saddleM δ w * (-η - s) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM.1 hc
    rw [modelSigma_eq]
    linarith [hs.2]

/-- The derivative of the level coordinate is bounded by `C₀ η / δ` on the whole window
`s ∈ [-η, η]` (the sibling `abs_deriv_modelSigma_le'` for `0 < s ≤ η`; the only sign-sensitive
ingredients are `|−η − s| ≤ 2η`, used in place of `η + s ≤ 2η`). -/
lemma abs_deriv_modelSigma_le_Icc {η δ s C₀ : ℝ} (hδ : 0 < δ) (h2 : 0 < 2 - 4 * δ)
    (hη : 0 < η) (hs : s ∈ Set.Icc (-η) η)
    (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀) {w : ℝ} (hw : w ∈ Set.Icc (-2) 2) :
    |deriv (modelSigma η δ s) w| ≤ C₀ * η / δ := by
  have hC0nn : 0 ≤ C₀ := by
    have h := hC₀ 0; rw [uasd_st_deriv_zero, abs_zero] at h; exact h
  have hb : 0 ≤ C₀ * η / δ := div_nonneg (mul_nonneg hC0nn hη.le) hδ.le
  have hηs : |η + s| ≤ 2 * η := by
    rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have hpos : ∀ {x : ℝ}, 0 < x → x ≤ 2 → |deriv (modelSigma η δ s) x| ≤ C₀ * η / δ := by
    intro x hx0 hx2
    have h2δ : (0:ℝ) < 2 * δ := by linarith
    rw [deriv_modelSigma' hδ h2 x, uasd_deriv_saddleM hx0 hx2, abs_mul, abs_div, abs_of_pos h2δ]
    have habs : |-η - s| = |η + s| := by
      rw [show -η - s = -(η + s) by ring, abs_neg]
    rw [habs]
    have h1 : |deriv Real.smoothTransition ((x - (2 - 4 * δ)) / (2 * δ))| / (2 * δ)
        ≤ C₀ / (2 * δ) := div_le_div_of_nonneg_right (hC₀ _) h2δ.le
    have h3 := mul_le_mul h1 hηs (abs_nonneg _) (by positivity)
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
    exact hpos (by linarith) (by linarith [hw.1])
  · subst hw0
    have hev : modelSigma η δ s =ᶠ[𝓝 (0 : ℝ)] (fun _ => s) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) h2] with y hy
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
      rw [modelSigma_eq, saddleM_eq_zero_of_abs_le hδ (le_of_lt hy), zero_mul, add_zero]
    rw [hev.deriv_eq, deriv_const, abs_zero]
    exact hb
  · exact hpos hw0 hw.2

/-! ## The rate estimate at levels `s ≤ 0` -/

/-- **The model-arc rate estimate about the centre `1`, at levels `s ∈ [-η, 0]`.**  This is the
sibling `modelArc_cross_about_one` with the plateau sub-case `σ = s ≤ 0` handled by
`re_lt_re_sqrt`; everything else (the transition zone and the outer plateau, where
`σ ∈ [-η, η]` and `ρ.re ≥ 0.85`) is sign-independent. -/
theorem modelArcCross_nonpos {η δ s C₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η)
    (hη' : η < 1 / 10) (hs0 : s ≤ 0) (hsη : s ≤ η) (hsη' : -η ≤ s)
    (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀) (hsmall : 8 * C₀ * η ≤ δ)
    (w : ℝ) (hw : w ∈ Set.Icc (-2) 2) (hw0 : w ≠ 0) :
    (star (mobiusRho η δ s w - 1) * deriv (fun u : ℝ => mobiusRho η δ s u) w).im < 0 := by
  have hδ₂ : δ < 1 / 2 := by linarith
  have h2δ : 0 < 2 - 4 * δ := by linarith
  have hsIcc : s ∈ Set.Icc (-η) η := ⟨hsη', hsη⟩
  set ρ : ℂ := mobiusRho η δ s w with hρdef
  set ρ' : ℂ := deriv (fun u : ℝ => mobiusRho η δ s u) w with hρ'def
  set ζ : ℂ := modelZeta η δ s w with hζdef
  set σ : ℝ := modelSigma η δ s w with hσdef
  set σ' : ℝ := deriv (modelSigma η δ s) w with hσ'def
  have hζne : modelZeta η δ s w ≠ 0 := modelZeta_ne_zero_of_ne hw0
  have hζeq : ρ * ρ = ζ := by
    rw [hρdef, hζdef]
    exact sqrt_mul_self_of_ne_zero hζne
  have hζmem : modelZeta η δ s w ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inr (by rw [modelZeta_im]; exact hw0)
  have hrel : 2 * ρ * ρ' = (σ' : ℂ) + Complex.I := by
    have hcd : ContDiffAt ℝ ∞ (mobiusRho η δ s) w :=
      (contDiffAt_sqrt_of_mem_slitPlane hζmem).comp w
        ((contDiff_modelZeta (η := η) (s := s) hδ hδ₂).contDiffAt)
    have hdiff : DifferentiableAt ℝ (fun u : ℝ => mobiusRho η δ s u) w :=
      hcd.differentiableAt (by simp)
    have hev : (fun u : ℝ => (mobiusRho η δ s u) ^ 2) =ᶠ[𝓝 w]
        (fun u : ℝ => modelZeta η δ s u) := by
      filter_upwards [eventually_ne_nhds hw0] with u hu
      rw [pow_two]
      exact sqrt_mul_self_of_ne_zero (modelZeta_ne_zero_of_ne hu)
    have hL : HasDerivAt (fun u : ℝ => (mobiusRho η δ s u) ^ 2) (2 * ρ * ρ') w := by
      have hd := hdiff.hasDerivAt.pow 2
      refine hd.congr_deriv ?_
      rw [hρdef, hρ'def]
      simp
    have hL' : HasDerivAt (fun u : ℝ => modelZeta η δ s u) (2 * ρ * ρ') w :=
      (hev.hasDerivAt_iff).mp hL
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
    exact hL'.unique hR
  have hα2β2 : ρ.re ^ 2 - ρ.im ^ 2 = σ := by
    have h := congrArg Complex.re hζeq
    rw [Complex.mul_re] at h
    rw [hζdef, modelZeta_re] at h
    rw [hσdef, pow_two, pow_two]
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
  have hσabs : |σ| ≤ η := by
    rw [hσdef]; exact abs_modelSigma_le_Icc hsIcc w
  have hσle : σ ≤ η := (abs_le.mp hσabs).2
  have hwabs : |w| ≤ 2 := abs_le.mpr hw
  have hσ'bound : |σ'| ≤ C₀ * η / δ := by
    rw [hσ'def]; exact abs_deriv_modelSigma_le_Icc hδ h2δ hη hsIcc hC₀ hw
  have hζre : ζ.re = σ := by rw [hζdef, modelZeta_re, hσdef]
  have hζim : ζ.im = w := by rw [hζdef, modelZeta_im]
  have hNum : (ζ.re - ρ.re) - σ' * (ζ.im - ρ.im) < 0 := by
    rw [hζre, hζim]
    rcases lt_or_ge |w| (2 - 4 * δ) with hwlt | hwge
    · -- the plateau: `σ = s`, `σ' = 0`, and `s < ρ.re`
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
        have h1 := re_lt_re_sqrt (z := ζ) (by rw [hζdef]; exact hζne)
          (by rw [hζre, hσeq]; linarith)
        have h2 : ζ.sqrt.re = ρ.re := by rw [hρdef, hζdef]; rfl
        rw [h2, hζre, hσeq] at h1
        exact h1
      linarith
    · -- the transition zone and the outer plateau
      have hσ'' : |σ'| ≤ 1 / 8 := by
        have h : C₀ * η / δ ≤ 1 / 8 := by rw [div_le_iff₀ hδ]; linarith
        linarith [hσ'bound]
      have hα2 : (3 : ℝ) / 4 < ρ.re ^ 2 := by
        have h1 : |w| ≤ ‖ζ‖ := by
          have h := Complex.abs_im_le_norm ζ
          rw [hζdef, modelZeta_im] at h
          rw [hζdef]; exact h
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
    exact mul_pos two_pos (norm_pos_iff.mpr hζne)
  rw [him]
  exact div_neg_of_neg_of_pos hNum hpos

end

open scoped Manifold ContDiff Topology in
/-- **The model-arc rate estimate of `Work.Drive.N2Lead.modelArc_cross_about_one`, extended from the levels `0 < s ≤ η` to all levels `s ∈ [-η, η]`.**  For `ρ w = Work.Drive.N2Lead.mobiusRho η δ s w = √(σ(s,w) + i w)` (`σ = Work.Drive.N2.saddleSigma η δ`) and `w ∈ [-2,2] \ {0}`:
`Im (conj (ρ w - 1) · ρ'(w)) < 0`.

WHY THE EXTENSION IS NEEDED (a gap in the §4.3 design of `NOTES_LEAD_saddlePacket.md`).  The upper certificate's picture at the level `f p + 3η/2` has two kinds of points drawn "by the model", and the design says both are covered by `modelArc_cross_about_one`:

* the points **inside** the model region: `(Z x)² = η + i w`, picture `cE3 (Ψ (Z x)) = cE3 (ρ w)` with level coordinate `σ(η, w)` — this is `s = +η`, covered by the existing result (with all `w ∈ [-2,2]`, including `w = 0`);
* the **remnant** points (the design's own words: "`foot y` is a remnant point (`c₀ ≤ |w| ≤ m`, value `cE3 ρ(w)` again, **since `σ = −ηs`**)") — here the picture is `A (foot y)`, and since `foot y` is an *anchor*-level point (`f (foot y) = f p − 3η/2`, hence `(Z (foot y))² = −η + i w`) whose `w` is the same, the value is `cE3 (ρ w)` for the level coordinate `s = −η`, i.e. the estimate is needed on the **negative** level.  The hypothesis `0 < s` of the existing result excludes exactly this case (there `|w| ≥ c₀ > 2 − 2δ > 0`, so the extra hypothesis `hw0` is free).

The claim is TRUE (checked numerically over `δ ∈ {0.001, 0.01, 0.05, 0.099}`, `η ∈ {1e-5, …, δ/15}`, `s/η ∈ {−1, −0.9, …, 1}` and `w` on a 200-point grid of `[−2,2]`: the cross is strictly negative throughout).  The hypothesis `w ≠ 0` is **necessary** for `s < 0`: there `w ↦ √(σ(s,w) + i w)` is *discontinuous* at `w = 0` (the argument crosses the negative real axis, the branch cut of the principal square root), so `deriv` there is `0` and the inequality would read `0 < 0`.

ROUTE: the argument of the sibling `modelArc_cross_about_one` (same file, 200 lines) goes through with `0 < s` replaced by `s ∈ Icc (-η) η` and `w ≠ 0`.  Its key identity is
`Im (conj (ρ-1) ρ') = [(σ − ρ.re) − σ'(w − ρ.im)] / (2‖ρ‖²)`,
with `2ρρ' = σ' + i`; for `w ≠ 0` one has `ζ = σ + iw` non-real, so `ζ ≠ 0`, `ρ = √ζ ≠ 0` and `ρ.re > 0` (this is what replaces `0 < s` in the plateau case: `σ = s ≤ η < ρ.re`), and `σ = s + M(w)(−η − s) ∈ [−η, η]` for `s ∈ [−η, η]`, `M ∈ [0,1]`.  The transition-zone bound `ρ.re ≥ 0.9`, `|σ'| ≤ 1/8`, `|w − ρ.im| < 4` is sign-independent.  WARNING: the helpers used by the sibling (`modelZeta_mem_slitPlane`, `mobiusRho_contDiff`, `uasd_abs_modelSigma_le`) are stated with `0 < s`; the prover must re-derive non-branch-cut membership and `|σ| ≤ η` for `s ≤ 0` (short, and independent of the main estimate). -/
theorem modelArcCross_absLe {η δ s C₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hη : 0 < η)
    (hη' : η < 1 / 10) (hs : s ∈ Set.Icc (-η) η)
    (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀) (hsmall : 8 * C₀ * η ≤ δ)
    (w : ℝ) (hw : w ∈ Set.Icc (-2) 2) (hw0 : w ≠ 0) :
    (star (Work.Drive.N2Lead.mobiusRho η δ s w - 1)
      * deriv (fun u : ℝ => Work.Drive.N2Lead.mobiusRho η δ s u) w).im < 0 := by
  rcases lt_or_ge (0 : ℝ) s with hs0 | hs0
  · exact modelArc_cross_about_one hδ hδ' hη hη' hs0 hs.2 hC₀ hsmall w hw
  · exact modelArcCross_nonpos hδ hδ' hη hη' hs0 hs.2 hs.1 hC₀ hsmall w hw hw0

end Work.Drive.N2Lead
