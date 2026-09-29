import Mathlib
import Submission.Work.TMComp.MAnalytic.amoM_strip
import Submission.Work.TMComp.MAnalytic.section_unique_real

/-!
# The Cayley transform of AJ's `m`-function on a horizontal strip

For `z` with `Im z ≥ 4` and `σ > 0` with `2 λ sinh (2 π σ) ≤ Im z / 2 - 2 / Im z`, the strip
section `stripLim α λ z` (the bounded fixed point of the almost Mathieu section equation on
`{|Im x| < σ}`) is 1-periodic, analytic on the strip, and has positive imaginary part there.
Consequently its Cayley transform is a bounded analytic 1-periodic function on the strip which
agrees, on the real line, with the Cayley transform of `amoM α λ z`.

The main point of this file is the identification `amoM α λ z x = stripLim α λ z x` on the real
line (uniqueness of the bounded `ℍ`-valued solution of the section equation on `ℝ`,
`section_unique_real`), together with the periodicity/holomorphicity/positivity of `stripLim`.
-/

open Filter Topology
open scoped Topology

namespace Work.RedProj

open Work.TMComp.MAnalytic

noncomputable section

/-! ## 1. Periodicity of the strip iteration -/

lemma stripA_add_one (α lam : ℝ) (z : ℂ) (x : ℂ) :
    stripA α lam z (x + 1) = stripA α lam z x := by
  have hcos : Complex.cos (2 * (Real.pi : ℂ) * (x + 1 - α))
      = Complex.cos (2 * (Real.pi : ℂ) * (x - α)) := by
    have h : 2 * (Real.pi : ℂ) * (x + 1 - α)
        = 2 * (Real.pi : ℂ) * (x - α) + 2 * (Real.pi : ℂ) := by ring
    rw [h, Complex.cos_add_two_pi]
  simp only [stripA]
  rw [hcos]

lemma stripIter_add_one (α lam : ℝ) (z : ℂ) (n : ℕ) (x : ℂ) :
    stripIter (stripA α lam z) α n (x + 1) = stripIter (stripA α lam z) α n x := by
  induction n generalizing x with
  | zero => exact stripA_add_one α lam z x
  | succ n ih =>
    rw [stripIter_succ]
    simp only [stripStep_apply]
    rw [stripA_add_one, show (x + 1 - α) = (x - α) + 1 by ring, ih (x - α)]

lemma stripLim_add_one (α lam : ℝ) (z : ℂ) (x : ℂ) :
    stripLim α lam z (x + 1) = stripLim α lam z x := by
  have h : (fun k : ℕ => stripIter (stripA α lam z) α (k + 1) (x + 1)
        - stripIter (stripA α lam z) α k (x + 1))
      = (fun k : ℕ => stripIter (stripA α lam z) α (k + 1) x
        - stripIter (stripA α lam z) α k x) := by
    funext k
    rw [stripIter_add_one, stripIter_add_one]
  simp only [stripLim]
  rw [h, stripA_add_one]

/-! ## 2. Holomorphicity of the limiting section on the strip -/

lemma stripLim_analyticOnNhd {α lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 4 ≤ z.im) {σ : ℝ}
    (hσ : 0 < σ) (hσz : 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ z.im / 2 - 2 / z.im) :
    AnalyticOnNhd ℂ (stripLim α lam z) {x : ℂ | |x.im| < σ} := by
  have hlam0 : (0:ℝ) ≤ lam := le_of_lt hlam
  have hUopen : IsOpen {x : ℂ | |x.im| < σ} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ
      (fun w : ℂ => stripIter (stripA α lam z) α (n+1) w - stripIter (stripA α lam z) α n w)
      {x : ℂ | |x.im| < σ} := by
    intro n
    exact (stripIter_differentiable hlam0 hz hσ hσz (n+1)).sub
      (stripIter_differentiable hlam0 hz hσ hσz n)
  have hgeo : Summable (fun n : ℕ => (4 / z.im^2)^n * (2/z.im)) := by
    refine (summable_geometric_of_lt_one (by positivity) ?_).mul_right (2/z.im)
    rw [div_lt_one (by positivity : (0:ℝ) < z.im^2)]
    nlinarith
  have hbound : ∀ (n : ℕ) (w : ℂ), w ∈ {x : ℂ | |x.im| < σ} →
      ‖stripIter (stripA α lam z) α (n+1) w - stripIter (stripA α lam z) α n w‖
        ≤ (4 / z.im^2)^n * (2/z.im) := by
    intro n w hw
    exact stripIter_diff hlam0 hz hσ hσz n w hw
  have htsum : DifferentiableOn ℂ
      (fun w : ℂ => ∑' n : ℕ,
        (stripIter (stripA α lam z) α (n+1) w - stripIter (stripA α lam z) α n w))
      {x : ℂ | |x.im| < σ} :=
    Complex.differentiableOn_tsum_of_summable_norm
      (F := fun n w => stripIter (stripA α lam z) α (n+1) w - stripIter (stripA α lam z) α n w)
      hgeo hdiff hUopen hbound
  have hA : DifferentiableOn ℂ (stripA α lam z) {x : ℂ | |x.im| < σ} :=
    (stripA_differentiable α lam z).differentiableOn
  have hlimdiff : DifferentiableOn ℂ (stripLim α lam z) {x : ℂ | |x.im| < σ} := by
    have heq : stripLim α lam z = fun w => stripA α lam z w +
        ∑' n : ℕ, (stripIter (stripA α lam z) α (n+1) w - stripIter (stripA α lam z) α n w) := rfl
    rw [heq]
    exact hA.add htsum
  rwa [Complex.analyticOnNhd_iff_differentiableOn hUopen]

/-! ## 3. Bounds, the functional equation, and positivity of the imaginary part -/

lemma stripLim_spec {α lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 4 ≤ z.im) {σ : ℝ}
    (hσ : 0 < σ) (hσz : 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ z.im / 2 - 2 / z.im) :
    (∀ x : ℂ, |x.im| < σ → z.im / 2 ≤ ‖stripLim α lam z x‖) ∧
    (∀ x : ℂ, |x.im| < σ → ‖stripLim α lam z x‖ ≤
        ‖z‖ + 2 * lam * Real.cosh (2 * Real.pi * σ) + 2 / z.im) ∧
    (∀ x : ℂ, |x.im| < σ → stripLim α lam z x =
        (z - 2 * lam * Complex.cos (2 * Real.pi * (x - α))) - 1 / stripLim α lam z (x - α)) ∧
    (∀ x : ℂ, |x.im| < σ → 0 < (stripLim α lam z x).im) := by
  have hlam0 : (0:ℝ) ≤ lam := le_of_lt hlam
  have hδ : z.im / 2 ≤ z.im - 2 * lam * Real.sinh (2 * Real.pi * σ) := by
    have h2 : (0:ℝ) < 2 / z.im := by positivity
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ge_of_tendsto' (stripLim_tendsto hlam0 hz hσ hσz hx).norm
      (fun n => stripIter_norm_lower hlam0 hz hσ hσz n x hx)
  · intro x hx
    exact le_of_tendsto' (stripLim_tendsto hlam0 hz hσ hσz hx).norm
      (fun n => stripIter_norm_upper hlam0 hz hσ hσz n x hx)
  · intro x hx
    have hx' : |(x - α).im| < σ := by simpa [Complex.sub_im] using hx
    have hlim := stripLim_tendsto (α := α) hlam0 hz hσ hσz hx
    have hlim' := stripLim_tendsto (α := α) hlam0 hz hσ hσz hx'
    have hne : stripLim α lam z (x - α) ≠ 0 := by
      intro h0
      have h1 : z.im / 2 ≤ ‖stripLim α lam z (x - α)‖ :=
        ge_of_tendsto' hlim'.norm (fun n => stripIter_norm_lower hlam0 hz hσ hσz n (x-α) hx')
      rw [h0, norm_zero] at h1
      linarith
    have hL : Tendsto (fun n : ℕ => stripIter (stripA α lam z) α (n+1) x) atTop
        (nhds (stripLim α lam z x)) := hlim.comp (tendsto_add_atTop_nat 1)
    have hR : Tendsto (fun n : ℕ => stripA α lam z x - (stripIter (stripA α lam z) α n (x - α))⁻¹)
        atTop (nhds (stripA α lam z x - (stripLim α lam z (x - α))⁻¹)) :=
      tendsto_const_nhds.sub (hlim'.inv₀ hne)
    have hfun : (fun n : ℕ => stripIter (stripA α lam z) α (n+1) x)
        = (fun n : ℕ => stripA α lam z x - (stripIter (stripA α lam z) α n (x - α))⁻¹) := by
      funext n
      rw [stripIter_succ_apply]
    rw [hfun] at hL
    have key := tendsto_nhds_unique hL hR
    simpa [stripA, one_div] using key
  · intro x hx
    have hlim := stripLim_tendsto (α := α) hlam0 hz hσ hσz hx
    have hcont : Tendsto (fun n : ℕ => (stripIter (stripA α lam z) α n x).im) atTop
        (nhds ((stripLim α lam z x).im)) :=
      (Complex.continuous_im.tendsto (stripLim α lam z x)).comp hlim
    have hge : z.im / 2 ≤ (stripLim α lam z x).im :=
      ge_of_tendsto' hcont (fun n => le_trans hδ (stripIter_im_lower hlam0 hz hσ hσz n x hx))
    linarith

/-! ## 4. The Cayley transform is bounded on the upper half plane -/

lemma norm_sub_I_div_add_I_lt_one {w : ℂ} (hw : 0 < w.im) :
    ‖(w - Complex.I) / (w + Complex.I)‖ < 1 := by
  have hne : w + Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hne)]
  have h1 : ‖w - Complex.I‖^2 = w.re^2 + (w.im - 1)^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have h2 : ‖w + Complex.I‖^2 = w.re^2 + (w.im + 1)^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have hlt : ‖w - Complex.I‖^2 < ‖w + Complex.I‖^2 := by
    rw [h1, h2]
    nlinarith [hw, sq_nonneg w.re, sq_nonneg (w.im - 1), sq_nonneg (w.im + 1)]
  have h3 := abs_lt_of_sq_lt_sq hlt (norm_nonneg (w + Complex.I))
  rwa [abs_of_nonneg (norm_nonneg (w - Complex.I))] at h3

/-! ## 5. `amoM` agrees with the strip section on the real line -/

lemma amoM_eq_stripLim {α lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 4 ≤ z.im) {σ : ℝ}
    (hσ : 0 < σ) (hσz : 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ z.im / 2 - 2 / z.im) (x : ℝ) :
    Work.TMContract.amoM α lam z x = stripLim α lam z (x : ℂ) := by
  obtain ⟨M, hM_an, hM_bd, hM_eq, hMlim⟩ := amoM_strip hlam hz hσ hσz
  obtain ⟨hlo, hup, heq, him⟩ := stripLim_spec (α := α) hlam hz hσ hσz
  have hamoM : ∀ y : ℝ, Work.TMContract.amoM α lam z y = M (y : ℂ) :=
    fun y => (hMlim y).limUnder_eq
  have key : ∀ y : ℝ, M (y : ℂ) = stripLim α lam z (y : ℂ) :=
    section_unique_real (α := α) (lam := lam) hz
      (‖z‖ + 2 * lam * Real.cosh (2 * Real.pi * σ) + 2 / z.im)
      (fun y : ℝ => M (y : ℂ)) (fun y : ℝ => stripLim α lam z (y : ℂ))
      (fun y => hM_bd (y:ℂ) (by simpa using hσ))
      (fun y => by rw [hM_eq (y:ℂ) (by simpa using hσ), Complex.ofReal_sub])
      (fun y => ⟨hlo (y:ℂ) (by simpa using hσ), hup (y:ℂ) (by simpa using hσ)⟩)
      (fun y => by rw [heq (y:ℂ) (by simpa using hσ), Complex.ofReal_sub])
  rw [hamoM x, key x]

/-! ## 6. The main statement -/

theorem amoM_cayley_strip {α lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 4 ≤ z.im) {σ : ℝ}
    (hσ : 0 < σ) (hσz : 2 * lam * Real.sinh (2 * Real.pi * σ) ≤ z.im / 2 - 2 / z.im) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {x : ℂ | |x.im| < σ} ∧
      (∀ x : ℂ, |x.im| < σ → ‖G x‖ < 1) ∧
      (∀ x : ℂ, G (x + 1) = G x) ∧
      (∀ x : ℝ, G (x : ℂ) = (Work.TMContract.amoM α lam z x - Complex.I) /
        (Work.TMContract.amoM α lam z x + Complex.I)) := by
  obtain ⟨hlo, hup, heq, him⟩ := stripLim_spec (α := α) hlam hz hσ hσz
  refine ⟨fun x => (stripLim α lam z x - Complex.I) / (stripLim α lam z x + Complex.I),
    ?_, ?_, ?_, ?_⟩
  · have hana : AnalyticOnNhd ℂ (stripLim α lam z) {x : ℂ | |x.im| < σ} :=
      stripLim_analyticOnNhd hlam hz hσ hσz
    have hne : ∀ x ∈ {x : ℂ | |x.im| < σ}, stripLim α lam z x + Complex.I ≠ 0 := by
      intro x hx h
      have h1 : (stripLim α lam z x).im + 1 = 0 := by
        have := congrArg Complex.im h; simpa using this
      have h2 := him x hx
      linarith
    exact (hana.sub analyticOnNhd_const).div (hana.add analyticOnNhd_const) hne
  · intro x hx
    exact norm_sub_I_div_add_I_lt_one (him x hx)
  · intro x
    show (stripLim α lam z (x + 1) - Complex.I) / (stripLim α lam z (x + 1) + Complex.I)
        = (stripLim α lam z x - Complex.I) / (stripLim α lam z x + Complex.I)
    rw [stripLim_add_one α lam z x]
  · intro x
    show (stripLim α lam z (x:ℂ) - Complex.I) / (stripLim α lam z (x:ℂ) + Complex.I)
        = (Work.TMContract.amoM α lam z x - Complex.I) /
          (Work.TMContract.amoM α lam z x + Complex.I)
    rw [amoM_eq_stripLim (α := α) hlam hz hσ hσz x]

end

end Work.RedProj
