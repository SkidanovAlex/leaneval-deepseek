import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.explicit_formula_smoothed_upper_lapX
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_ne_zero_of_one_lt_re
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_shift_identity_gen
import Submission.Commons.NumberTheory.DirichletCharacter.norm_logDeriv_LFunction_le_re_gt_one
import Submission.Commons.NumberTheory.DirichletCharacter.divisorSum_summable_and_tendsto
import Submission.Commons.NumberTheory.Linnik.tentMellin_bridge_scale
import Submission.Commons.Analysis.Complex.lapX_sub_inv_bound
import Submission.Commons.Analysis.Complex.regularized_kernel_bound_negRe
import Submission.Commons.NumberTheory.DirichletCharacter.rectInt_logDeriv_completed_mul_simplePole
import Submission.Commons.NumberTheory.DirichletCharacter.rectInt_logDeriv_gammaFactor_mul_simplePole

open Complex MeasureTheory intervalIntegral Filter Set Topology
open scoped Real Topology BigOperators
open Commons.Analysis.Complex

attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.DirichletCharacter

noncomputable def rdcKernel (x₀ L : ℝ) (f : ℝ → ℂ) (s u : ℂ) : ℂ :=
  (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ))) * f t)
    - f 0 / ((s - u) * (L : ℂ))

lemma rdcKernel_eq_lapX (x₀ L : ℝ) (f : ℝ → ℂ) (s u : ℂ) :
    rdcKernel x₀ L f s u
      = lapX x₀ f ((s - u) * (L : ℂ)) - f 0 / ((s - u) * (L : ℂ)) := by
  simp only [rdcKernel, lapX]

lemma rdcKernel_sub_pole {x₀ L : ℝ} (f : ℝ → ℂ) (s u : ℂ) :
    rdcKernel x₀ L f s u - (f 0 / (L : ℂ)) / (u - s)
      = lapX x₀ f ((s - u) * (L : ℂ)) := by
  rw [rdcKernel_eq_lapX]
  have h1 : (L : ℂ) * (u - s) = -((s - u) * (L : ℂ)) := by ring
  have h : (f 0 / (L : ℂ)) / (u - s) = -(f 0 / ((s - u) * (L : ℂ))) := by
    rw [div_div, h1, div_neg]
  rw [h]
  ring

lemma rdcKernel_sub_pole_differentiable {x₀ L : ℝ} (hx₀ : 0 ≤ x₀) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (s : ℂ) :
    Differentiable ℂ (fun u : ℂ => rdcKernel x₀ L f s u - (f 0 / (L : ℂ)) / (u - s)) := by
  have h : (fun u : ℂ => rdcKernel x₀ L f s u - (f 0 / (L : ℂ)) / (u - s))
      = fun u : ℂ => lapX x₀ f ((s - u) * (L : ℂ)) := by
    funext u; exact rdcKernel_sub_pole f s u
  rw [h]
  exact differentiable_lapX_affine hx₀ hcont s L

lemma rdcKernel_entire_part_bound {x₀ : ℝ} (hx₀ : 0 < x₀) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) {L : ℝ} (hL : 0 < L) {s : ℂ} {α : ℝ} (hασ : s.re < α) :
    ∃ M : ℝ, 0 < M ∧ ∀ u : ℂ, u.re ≤ α → ‖lapX x₀ f ((s - u) * (L : ℂ))‖ ≤ M := by
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, ∀ t ∈ Set.Icc (0:ℝ) x₀, ‖f t‖ ≤ Cf := by
    have hb : Bornology.IsBounded (f '' Set.Icc (0:ℝ) x₀) :=
      (isCompact_Icc (a := (0:ℝ)) (b := x₀)).image_of_continuousOn hcont |>.isBounded
    obtain ⟨C, hC⟩ := hb.exists_norm_le
    exact ⟨C, fun t ht => hC (f t) (Set.mem_image_of_mem f ht)⟩
  have hCfnn : 0 ≤ Cf := le_trans (norm_nonneg (f 0)) (hCf 0 ⟨le_refl 0, hx₀.le⟩)
  refine ⟨Real.exp (L * (α - s.re) * x₀) * (Cf + 1) * x₀, ?_, ?_⟩
  · apply mul_pos (mul_pos (Real.exp_pos _) _) hx₀
    linarith only [hCfnn]
  · intro u hu
    rw [lapX]
    have hb : ∀ t ∈ Set.uIcc (0:ℝ) x₀,
        ‖Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ))) * f t‖
          ≤ Real.exp (L * (α - s.re) * x₀) * (Cf + 1) := by
      intro t ht
      rw [norm_mul]
      have htI : t ∈ Set.Icc (0:ℝ) x₀ := by
        rwa [Set.uIcc_of_le hx₀.le] at ht
      have hft := hCf t htI
      have hexp : ‖Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ)))‖
          ≤ Real.exp (L * (α - s.re) * x₀) := by
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        have hre : (-(((s - u) * (L : ℂ)) * (t : ℂ))).re = -(L * (s.re - u.re) * t) := by
          simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            mul_zero, sub_zero, Complex.sub_re, Complex.sub_im]
          ring
        rw [hre]
        have ht0 : 0 ≤ t := htI.1
        have h1 : L * (s.re - u.re) ≥ L * (s.re - α) :=
          mul_le_mul_of_nonneg_left (by linarith only [hu]) hL.le
        have h2 : L * (s.re - α) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hL.le (by linarith only [hασ])
        have h3 : L * (s.re - u.re) * t ≥ L * (s.re - α) * t :=
          mul_le_mul_of_nonneg_right h1 ht0
        have h4 : L * (s.re - α) * t ≥ L * (s.re - α) * x₀ := by
          nlinarith only [h2, ht0, htI.2, htI]
        linarith only [h3, h4]
      calc ‖Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ)))‖ * ‖f t‖
          ≤ Real.exp (L * (α - s.re) * x₀) * Cf :=
            mul_le_mul hexp hft (norm_nonneg _) (Real.exp_pos _).le
        _ ≤ Real.exp (L * (α - s.re) * x₀) * (Cf + 1) := by
            linarith only [hCfnn, (Real.exp_pos (L * (α - s.re) * x₀))]
    calc ‖∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ))) * f t‖
        ≤ (Real.exp (L * (α - s.re) * x₀) * (Cf + 1)) * |x₀ - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const
            (fun t ht => hb t (by
              rw [Set.uIoc_of_le hx₀.le] at ht
              rw [Set.uIcc_of_le hx₀.le]
              exact ⟨le_of_lt ht.1, ht.2⟩))
      _ = Real.exp (L * (α - s.re) * x₀) * (Cf + 1) * x₀ := by
          rw [sub_zero, abs_of_pos hx₀]

lemma rdcKernel_norm_le_inv_sq {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    {L : ℝ} (hL : 1 < L) {s : ℂ} {α : ℝ} (hsre : -(1/2 : ℝ) < s.re) (hασ : s.re < α)
    (hα2 : α ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ, -(1/2 : ℝ) ≤ u.re → u.re ≤ α → u ≠ s →
      ‖rdcKernel x₀ L f s u‖ ≤ C / ‖u - s‖ ^ 2 := by
  have hLpos : 0 < L := by linarith only [hL]
  set C0 : ℝ := Real.exp (3 * L * x₀) * (5 * B * x₀ + 2 * ‖f 0‖ / x₀)
    + (3 * B * x₀ + 2 * ‖f 0‖ / x₀) + 1 with hC0def
  have hC0pos : 0 < C0 := by rw [hC0def]; positivity
  refine ⟨C0 / L ^ 2, by positivity, ?_⟩
  intro u hu1 hu2 hus
  have hsu : s - u ≠ 0 := sub_ne_zero.mpr (fun h => hus h.symm)
  have hz : (s - u) * (L : ℂ) ≠ 0 := mul_ne_zero hsu (Complex.ofReal_ne_zero.mpr hLpos.ne')
  have hre : ((s - u) * (L : ℂ)).re = L * (s.re - u.re) := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.sub_re]
    ring
  have hnorm : ‖(s - u) * (L : ℂ)‖ ^ 2 = L ^ 2 * ‖s - u‖ ^ 2 := by
    rw [norm_mul, Complex.norm_of_nonneg hLpos.le, mul_pow, mul_comm]
  have hnorm_us : ‖u - s‖ = ‖s - u‖ := by rw [← norm_neg, neg_sub]
  have hzre_le : |((s - u) * (L : ℂ)).re| ≤ 3 * L := by
    rw [hre, abs_mul, abs_of_nonneg hLpos.le]
    have h : |s.re - u.re| ≤ 3 := by rw [abs_le]; constructor <;> linarith only [hsre, hα2, hu2, hασ, hu1]
    nlinarith only [hLpos, h, hL]
  have hC0_ge2 : 3 * B * x₀ + 2 * ‖f 0‖ / x₀ ≤ C0 := by
    rw [hC0def]
    have hnum : 0 ≤ 5 * B * x₀ + 2 * ‖f 0‖ / x₀ := by positivity
    have := mul_nonneg (Real.exp_pos (3 * L * x₀)).le hnum
    linarith only [this]
  rw [rdcKernel_eq_lapX]
  have hval : lapX x₀ f ((s - u) * (L : ℂ)) - f 0 / ((s - u) * (L : ℂ))
      = (∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ))) * f t)
          - f 0 / ((s - u) * (L : ℂ)) := by rw [lapX]
  rw [hval, hnorm_us]
  rcases le_or_gt ((s - u) * (L : ℂ)).re 0 with hneg | hpos
  · have h := regularized_kernel_bound_negRe (x₀ := x₀) (B := B) (f := f) hx₀ hB hcont hf2
      hBnd hvan (z := (s - u) * (L : ℂ)) hz hneg
    have hexp : Real.exp (|((s - u) * (L : ℂ)).re| * x₀) ≤ Real.exp (3 * L * x₀) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hzre_le, hx₀]
    have hnum : 0 ≤ 5 * B * x₀ + 2 * ‖f 0‖ / x₀ := by positivity
    have hEN : Real.exp (|((s - u) * (L : ℂ)).re| * x₀) * (5 * B * x₀ + 2 * ‖f 0‖ / x₀) ≤ C0 := by
      have h1 : Real.exp (|((s - u) * (L : ℂ)).re| * x₀) * (5 * B * x₀ + 2 * ‖f 0‖ / x₀)
          ≤ Real.exp (3 * L * x₀) * (5 * B * x₀ + 2 * ‖f 0‖ / x₀) :=
        mul_le_mul_of_nonneg_right hexp hnum
      have h2 : Real.exp (3 * L * x₀) * (5 * B * x₀ + 2 * ‖f 0‖ / x₀) ≤ C0 := by
        rw [hC0def]
        have h3 : 0 ≤ 3 * B * x₀ + 2 * ‖f 0‖ / x₀ := by positivity
        linarith only [h3]
      linarith only [h1, h2]
    calc ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ))) * f t)
          - f 0 / ((s - u) * (L : ℂ))‖
        ≤ Real.exp (|((s - u) * (L : ℂ)).re| * x₀) * (5 * B * x₀ + 2 * ‖f 0‖ / x₀)
            / ‖(s - u) * (L : ℂ)‖ ^ 2 := h
      _ ≤ C0 / ‖(s - u) * (L : ℂ)‖ ^ 2 := div_le_div_of_nonneg_right hEN (by positivity)
      _ = C0 / L ^ 2 / ‖s - u‖ ^ 2 := by rw [hnorm, div_div]
  · have h := lapX_sub_inv_bound (x₀ := x₀) (B := B) (f := f) hx₀ hB hcont hf2 hBnd hvan
      (z := (s - u) * (L : ℂ)) hpos
    calc ‖(∫ t in (0:ℝ)..x₀, Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ))) * f t)
          - f 0 / ((s - u) * (L : ℂ))‖
        ≤ (3 * B * x₀ + 2 * ‖f 0‖ / x₀) / ‖(s - u) * (L : ℂ)‖ ^ 2 := h
      _ ≤ C0 / ‖(s - u) * (L : ℂ)‖ ^ 2 := div_le_div_of_nonneg_right hC0_ge2 (by positivity)
      _ = C0 / L ^ 2 / ‖s - u‖ ^ 2 := by rw [hnorm, div_div]

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

/-- The divisor sum of `div Λ · Φ` is summable and the truncated sums converge to it, as long as
`Φ` decays like `‖u‖⁻²` away from a neighbourhood of `s₀` whose radius `δ` separates `s₀` from
the zeros of `Λ`. -/
lemma divisorSum_summable_and_tendsto_hole {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {Φ : ℂ → ℂ} {s₀ : ℂ} {A δ : ℝ}
    (hA : 0 < A) (hδ : 0 < δ)
    (hsep : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ ‖ρ - s₀‖)
    (hΦ : ∀ u : ℂ, 0 < u.re → u.re < 1 → 2 ≤ ‖u‖ → δ ≤ ‖u - s₀‖ → ‖Φ u‖ ≤ A / ‖u‖ ^ 2) :
    Summable (fun u : ℂ =>
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ) * Φ u)
      ∧ Filter.Tendsto (fun T : ℝ => ∑ᶠ u : ℂ, (if |u.im| < T then
          (((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℂ) * Φ u) else 0))
        Filter.atTop (nhds (∑' u : ℂ,
          (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ) * Φ u)) := by
  classical
  let Φ' : ℂ → ℂ := fun u => if ‖u - s₀‖ < δ then 0 else Φ u
  have hΦ' : ∀ u : ℂ, 0 < u.re → u.re < 1 → 2 ≤ ‖u‖ → ‖Φ' u‖ ≤ A / ‖u‖ ^ 2 := by
    intro u h1 h2 h3
    by_cases h : ‖u - s₀‖ < δ
    · simp only [Φ', if_pos h, norm_zero]; positivity
    · simp only [Φ', if_neg h]; exact hΦ u h1 h2 h3 (not_lt.mp h)
  obtain ⟨hsum, hten⟩ := divisorSum_summable_and_tendsto χ hχ hχprim hA hΦ'
  have hΛdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction hχ
  have hkey : ∀ u : ℂ,
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ) * Φ' u
      = (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ) * Φ u := by
    intro u
    by_cases hD : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u = 0
    · simp [hD]
    · have hz : DirichletCharacter.completedLFunction χ u = 0 :=
        eq_zero_of_divisor_ne_zero (fun z _ => hΛdiff.analyticAt z) (Set.mem_univ u) hD
      have hle : δ ≤ ‖u - s₀‖ := hsep u hz
      simp only [Φ', if_neg (not_lt.mpr hle)]
  have hkey2 : ∀ u : ℂ,
      ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℂ) * Φ' u
      = ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℂ) * Φ u := by
    intro u
    by_cases h0 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u = 0
    · simp [h0]
    · have hz : DirichletCharacter.completedLFunction χ u = 0 :=
        apply_eq_zero_of_analyticOrderNatAt_ne_zero h0
      have hle : δ ≤ ‖u - s₀‖ := hsep u hz
      simp only [Φ', if_neg (not_lt.mpr hle)]
  refine ⟨?_, ?_⟩
  · rw [show (fun u : ℂ =>
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ) * Φ u)
        = (fun u : ℂ =>
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ) * Φ' u)
        by funext u; exact (hkey u).symm]
    exact hsum
  · have htsum : (∑' u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ) * Φ u)
        = (∑' u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ) * Φ' u) :=
      (tsum_congr (fun u => hkey u)).symm
    have hfin : (fun T : ℝ => ∑ᶠ u : ℂ, (if |u.im| < T then
        ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℂ) * Φ u else 0))
        = (fun T : ℝ => ∑ᶠ u : ℂ, (if |u.im| < T then
        ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℂ) * Φ' u else 0)) := by
      funext T
      refine finsum_congr (fun u => ?_)
      by_cases h : |u.im| < T <;> simp only [h, if_true, if_false]
      exact (hkey2 u).symm
    rw [htsum, hfin]
    exact hten

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

lemma rdcKernel_continuousOn_vertical {x₀ L α : ℝ} (hx₀ : 0 ≤ x₀) (hL : L ≠ 0) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) {s : ℂ} (hsre : s.re ≠ α) :
    Continuous (fun t : ℝ => rdcKernel x₀ L f s ((α : ℂ) + (t : ℂ) * Complex.I)) := by
  have h1 : Continuous (fun u : ℂ => lapX x₀ f ((s - u) * (L : ℂ))) :=
    (differentiable_lapX_affine hx₀ hcont s L).continuous
  have hden : ∀ t : ℝ, (s - ((α : ℂ) + (t : ℂ) * Complex.I)) * (L : ℂ) ≠ 0 := by
    intro t h
    rcases mul_eq_zero.mp h with h' | h'
    · have := congrArg Complex.re (sub_eq_zero.mp h')
      simp at this
      exact hsre this
    · exact (Complex.ofReal_ne_zero.mpr hL) h'
  have heq : (fun t : ℝ => rdcKernel x₀ L f s ((α : ℂ) + (t : ℂ) * Complex.I))
      = fun t : ℝ => lapX x₀ f ((s - ((α : ℂ) + (t : ℂ) * Complex.I)) * (L : ℂ))
          - f 0 / ((s - ((α : ℂ) + (t : ℂ) * Complex.I)) * (L : ℂ)) := by
    funext t; rw [rdcKernel_eq_lapX]
  rw [heq]
  exact (h1.comp (by fun_prop)).sub
    (Continuous.div continuous_const (by fun_prop) hden)

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

lemma inv_one_add_sq_sub_le (a t : ℝ) :
    1 / (1 + (t - a) ^ 2) ≤ (3 + 2 * a ^ 2) / (1 + t ^ 2) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have h : t ^ 2 ≤ 2 * (t - a) ^ 2 + 2 * a ^ 2 := by
    linarith only [sq_nonneg (a - (t - a)), sq_nonneg a, sq_nonneg (t - a)]
  have hexp : (3 + 2 * a ^ 2) * (1 + (t - a) ^ 2)
      = 3 + 2 * a ^ 2 + 3 * (t - a) ^ 2 + 2 * a ^ 2 * (t - a) ^ 2 := by ring
  rw [hexp]
  linarith only [h, sq_nonneg (t - a), sq_nonneg a, mul_nonneg (sq_nonneg a) (sq_nonneg (t - a))]

lemma lorentzian_le (δ z : ℝ) (hδ : 0 < δ) :
    1 / (δ ^ 2 + z ^ 2) ≤ (1 + δ ^ 2) / δ ^ 2 / (1 + z ^ 2) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hq : (1 : ℝ) ≤ (1 + δ ^ 2) / δ ^ 2 := by
    rw [le_div_iff₀ hδ2]; linarith only [sq_nonneg δ]
  have hq2 : (1 + δ ^ 2) / δ ^ 2 * δ ^ 2 = 1 + δ ^ 2 := by field_simp
  have hz : z ^ 2 ≤ (1 + δ ^ 2) / δ ^ 2 * z ^ 2 := by
    linarith only [mul_le_mul_of_nonneg_right hq (sq_nonneg z), hq]
  linarith only [hq2, hz, sq_nonneg z, sq_nonneg δ, hδ2]

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

lemma integrable_logDeriv_LFunction_mul_rdc_alpha {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B)
    {f : ℝ → ℂ} (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {L : ℝ} (hL : 1 < L) {s : ℂ} {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hασ : s.re < α)
    (hsre : -(1/2:ℝ) < s.re) :
    Integrable (fun t : ℝ => logDeriv (DirichletCharacter.LFunction χ)
      ((α:ℂ)+(t:ℂ)*Complex.I) * rdcKernel x₀ L f s ((α:ℂ)+(t:ℂ)*Complex.I)) := by
  obtain ⟨C, hCpos, hCb⟩ := rdcKernel_norm_le_inv_sq hx₀ hB hcont hf2 hBnd hvan hL hsre hασ (le_of_lt hα2)
  set δ : ℝ := α - s.re with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith only [hασ]
  set Cfin : ℝ := (100/(α-1)^2 + 100) * (C * (1+δ^2)/δ^2 * (3 + 2*s.im^2)) with hCfindef
  have hCfinnn : 0 ≤ Cfin := by rw [hCfindef]; positivity
  refine Commons.NumberTheory.Linnik.integrable_of_log_bound hCfinnn ?_ ?_
  · have hc1 : Continuous (fun t : ℝ => rdcKernel x₀ L f s ((α:ℂ)+(t:ℂ)*Complex.I)) :=
      rdcKernel_continuousOn_vertical hx₀.le (by linarith only [hL, hα1, hα2] : L ≠ 0) hcont (ne_of_lt hασ)
    have hm1 : AEStronglyMeasurable (fun t : ℝ =>
        logDeriv (DirichletCharacter.LFunction χ) ((α:ℂ)+(t:ℂ)*Complex.I)) volume :=
      (((measurable_logDeriv_LFunction' χ hχ).comp (by fun_prop))).aestronglyMeasurable
    exact hm1.mul hc1.aestronglyMeasurable
  · intro t
    rw [norm_mul]
    have h1log : ‖logDeriv (DirichletCharacter.LFunction χ) ((α:ℂ)+(t:ℂ)*Complex.I)‖
        ≤ 100/(α-1)^2 + 100 := by
      have h := norm_logDeriv_LFunction_le_re_gt_one χ (s := (α:ℂ)+(t:ℂ)*Complex.I) ?_ ?_
      · simpa using h
      · simpa using hα1
      · have : ((α:ℂ)+(t:ℂ)*Complex.I).re = α := by simp
        rw [this]; linarith only [hα2]
    have h2 : ‖rdcKernel x₀ L f s ((α:ℂ)+(t:ℂ)*Complex.I)‖
        ≤ C * (1+δ^2)/δ^2 * (3+2*s.im^2) / (1+t^2) := by
      have hure : ((α:ℂ)+(t:ℂ)*Complex.I).re = α := by simp
      have hne : ((α:ℂ)+(t:ℂ)*Complex.I) ≠ s := by
        intro hh
        have := congrArg Complex.re hh
        rw [hure] at this
        linarith only [hασ, this]
      have h := hCb ((α:ℂ)+(t:ℂ)*Complex.I)
        (by rw [hure]; linarith only [hα1, hα2]) (by rw [hure]) hne
      have hnsq : ‖((α:ℂ)+(t:ℂ)*Complex.I) - s‖^2 = δ^2 + (t - s.im)^2 := by
        have hre : (((α:ℂ)+(t:ℂ)*Complex.I) - s).re = α - s.re := by simp
        have him : (((α:ℂ)+(t:ℂ)*Complex.I) - s).im = t - s.im := by simp
        rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
        rw [hδdef]; ring
      rw [hnsq] at h
      calc ‖rdcKernel x₀ L f s ((α:ℂ)+(t:ℂ)*Complex.I)‖ ≤ C / (δ^2 + (t-s.im)^2) := h
        _ ≤ C * (1+δ^2)/δ^2 / (1+(t-s.im)^2) := by
            have hlr := lorentzian_le δ (t-s.im) hδpos
            calc C / (δ^2+(t-s.im)^2) = C * (1/(δ^2+(t-s.im)^2)) := by ring
              _ ≤ C * ((1+δ^2)/δ^2/(1+(t-s.im)^2)) :=
                    mul_le_mul_of_nonneg_left hlr hCpos.le
              _ = C * (1+δ^2)/δ^2 / (1+(t-s.im)^2) := by ring_nf
        _ ≤ C * (1+δ^2)/δ^2 * (3+2*s.im^2) / (1+t^2) := by
            rw [show C * (1+δ^2)/δ^2 / (1+(t-s.im)^2)
                = C * (1+δ^2)/δ^2 * (1/(1+(t-s.im)^2)) by ring_nf]
            rw [show C * (1+δ^2)/δ^2 * (3+2*s.im^2) / (1+t^2)
                = C * (1+δ^2)/δ^2 * ((3+2*s.im^2)/(1+t^2)) by ring_nf]
            apply mul_le_mul_of_nonneg_left (inv_one_add_sq_sub_le s.im t)
            positivity
    calc ‖logDeriv (DirichletCharacter.LFunction χ) ((α:ℂ)+(t:ℂ)*Complex.I)‖
            * ‖rdcKernel x₀ L f s ((α:ℂ)+(t:ℂ)*Complex.I)‖
        ≤ (100/(α-1)^2 + 100) * (C * (1+δ^2)/δ^2 * (3+2*s.im^2) / (1+t^2)) :=
          mul_le_mul h1log h2 (norm_nonneg _) (by positivity)
      _ ≤ Cfin * (Real.log (2+|t|) + 1) / (1+t^2) := by
          rw [hCfindef]
          have h1 : (1:ℝ) ≤ Real.log (2+|t|) + 1 := by
            have := Real.log_nonneg (show (1:ℝ) ≤ 2 + |t| by linarith only [abs_nonneg t, hα1, hα2]); linarith only [this]
          have hK : 0 ≤ 100/(α-1)^2 + 100 := by positivity
          have hD : 0 ≤ C * (1+δ^2)/δ^2 * (3 + 2*s.im^2) := by positivity
          rw [show (100/(α-1)^2 + 100) * (C * (1+δ^2)/δ^2 * (3+2*s.im^2) / (1+t^2))
              = (100/(α-1)^2 + 100) * (C * (1+δ^2)/δ^2 * (3+2*s.im^2)) / (1+t^2) by ring_nf]
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith only [mul_le_mul_of_nonneg_left h1 (mul_nonneg hK hD), h1, hK, hD]

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

lemma integrable_logDeriv_LFunction_mul_rdc_left {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B)
    {f : ℝ → ℂ} (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {L : ℝ} (hL : 1 < L) {s : ℂ} {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hασ : s.re < α)
    (hsre : -(1/2:ℝ) < s.re) :
    Integrable (fun t : ℝ => logDeriv (DirichletCharacter.LFunction χ)
      (((-1/2:ℝ):ℂ)+(t:ℂ)*Complex.I) * rdcKernel x₀ L f s (((-1/2:ℝ):ℂ)+(t:ℂ)*Complex.I)) := by
  obtain ⟨C, hCpos, hCb⟩ := rdcKernel_norm_le_inv_sq hx₀ hB hcont hf2 hBnd hvan hL hsre hασ
    (le_of_lt hα2)
  set δ : ℝ := s.re + 1/2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith only [hsre]
  have hlogN : 0 ≤ Real.log (N:ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  set Cfin : ℝ := 100 * (Real.log (N:ℝ) + 1) * (C * (1+δ^2)/δ^2 * (3 + 2*s.im^2)) with hCfindef
  have hCfinnn : 0 ≤ Cfin := by rw [hCfindef]; positivity
  refine Commons.NumberTheory.Linnik.integrable_of_log_bound hCfinnn ?_ ?_
  · have hc1 : Continuous (fun t : ℝ => rdcKernel x₀ L f s (((-1/2:ℝ):ℂ)+(t:ℂ)*Complex.I)) :=
      rdcKernel_continuousOn_vertical (α := (-1/2:ℝ)) hx₀.le (by linarith only [hL, hα1, hα2] : L ≠ 0) hcont
        (by linarith only [hsre] : s.re ≠ (-1/2:ℝ))
    have hm1 : AEStronglyMeasurable (fun t : ℝ =>
        logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ)+(t:ℂ)*Complex.I)) volume :=
      (((measurable_logDeriv_LFunction' χ hχ).comp (by fun_prop))).aestronglyMeasurable
    exact hm1.mul hc1.aestronglyMeasurable
  · intro t
    rw [norm_mul]
    have hlog0 : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t, hα1, hα2])
    have h1log : ‖logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ)+(t:ℂ)*Complex.I)‖
        ≤ 100 * (Real.log (N:ℝ) + 1) * (Real.log (2+|t|) + 1) := by
      have h := Commons.NumberTheory.Linnik.logDeriv_LFunction_leftEdge_uniform χ hχ hχprim t
      have h1 : (1:ℝ) ≤ Real.log (2+|t|) + 1 := by linarith only [hlog0]
      have hexp : 100 * (Real.log (N:ℝ) + Real.log (2+|t|) + 1)
          ≤ 100 * (Real.log (N:ℝ) + 1) * (Real.log (2+|t|) + 1) := by
        nlinarith only [hlogN, hlog0, hα1, hα2]
      linarith [h, hexp]
    have h2 : ‖rdcKernel x₀ L f s (((-1/2:ℝ):ℂ)+(t:ℂ)*Complex.I)‖
        ≤ C * (1+δ^2)/δ^2 * (3+2*s.im^2) / (1+t^2) := by
      have hure : (((-1/2:ℝ):ℂ)+(t:ℂ)*Complex.I).re = -1/2 := by simp
      have hne : (((-1/2:ℝ):ℂ)+(t:ℂ)*Complex.I) ≠ s := by
        intro hh
        have := congrArg Complex.re hh
        rw [hure] at this
        linarith only [hsre, this]
      have h := hCb (((-1/2:ℝ):ℂ)+(t:ℂ)*Complex.I)
        (by rw [hure]; linarith only []) (by rw [hure]; linarith only [hα1, hα2]) hne
      have hnsq : ‖(((-1/2:ℝ):ℂ)+(t:ℂ)*Complex.I) - s‖^2 = δ^2 + (t - s.im)^2 := by
        have hre : ((((-1/2:ℝ):ℂ)+(t:ℂ)*Complex.I) - s).re = -1/2 - s.re := by simp
        have him : ((((-1/2:ℝ):ℂ)+(t:ℂ)*Complex.I) - s).im = t - s.im := by simp
        rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
        rw [hδdef]; ring
      rw [hnsq] at h
      calc ‖rdcKernel x₀ L f s (((-1/2:ℝ):ℂ)+(t:ℂ)*Complex.I)‖ ≤ C / (δ^2 + (t-s.im)^2) := h
        _ ≤ C * (1+δ^2)/δ^2 / (1+(t-s.im)^2) := by
            have hlr := lorentzian_le δ (t-s.im) hδpos
            calc C / (δ^2+(t-s.im)^2) = C * (1/(δ^2+(t-s.im)^2)) := by ring
              _ ≤ C * ((1+δ^2)/δ^2/(1+(t-s.im)^2)) :=
                    mul_le_mul_of_nonneg_left hlr hCpos.le
              _ = C * (1+δ^2)/δ^2 / (1+(t-s.im)^2) := by ring_nf
        _ ≤ C * (1+δ^2)/δ^2 * (3+2*s.im^2) / (1+t^2) := by
            rw [show C * (1+δ^2)/δ^2 / (1+(t-s.im)^2)
                = C * (1+δ^2)/δ^2 * (1/(1+(t-s.im)^2)) by ring_nf]
            rw [show C * (1+δ^2)/δ^2 * (3+2*s.im^2) / (1+t^2)
                = C * (1+δ^2)/δ^2 * ((3+2*s.im^2)/(1+t^2)) by ring_nf]
            apply mul_le_mul_of_nonneg_left (inv_one_add_sq_sub_le s.im t)
            positivity
    calc ‖logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ)+(t:ℂ)*Complex.I)‖
            * ‖rdcKernel x₀ L f s (((-1/2:ℝ):ℂ)+(t:ℂ)*Complex.I)‖
        ≤ (100 * (Real.log (N:ℝ) + 1) * (Real.log (2+|t|) + 1))
            * (C * (1+δ^2)/δ^2 * (3+2*s.im^2) / (1+t^2)) :=
          mul_le_mul h1log h2 (norm_nonneg _) (by positivity)
      _ ≤ Cfin * (Real.log (2+|t|) + 1) / (1+t^2) := by
          rw [hCfindef]
          have heq : 100 * (Real.log (N:ℝ) + 1) * (Real.log (2+|t|) + 1)
                * (C * (1+δ^2)/δ^2 * (3+2*s.im^2) / (1+t^2))
              = (100 * (Real.log (N:ℝ) + 1) * (C * (1+δ^2)/δ^2 * (3+2*s.im^2)))
                * (Real.log (2+|t|) + 1) / (1+t^2) := by ring
          rw [heq]

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

lemma integral_norm_logDeriv_LFunction_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ {A B v δ : ℝ}, (-1/2:ℝ) ≤ A → A ≤ B → B ≤ 2 → 2 ≤ |v| → 0 < δ → δ ≤ 1 →
      (∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ |ρ.im - v|) →
      (∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ |ρ.im + v|) →
      (∫ x in A..B, ‖logDeriv (DirichletCharacter.LFunction χ) ((x:ℂ) + (v:ℂ)*Complex.I)‖)
        ≤ C * Real.log (N*(|v|+3)) * (Real.log (N*(|v|+3)) + Real.log (1/δ)) := by
  obtain ⟨C1, hC1pos, hC1⟩ := exists_bound_integral_logDeriv_completedL_horizontal χ hχ hχprim
  obtain ⟨C2, hC2pos, hC2⟩ := horizontalGamma_logDeriv_bound χ
  refine ⟨C1 + C2 + 1, by positivity, ?_⟩
  intro A B v δ hA hAB hB2 hv2 hδ hδ1 hsepA hsepB
  have hvT : 2 ≤ |v| := hv2
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast NeZero.one_le
  have hv3 : (5:ℝ) ≤ (N:ℝ) * (|v| + 3) := by nlinarith only [hN1, abs_nonneg v, hv2]
  have hL1 : 1 ≤ Real.log ((N:ℝ) * (|v| + 3)) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have he : Real.exp 1 < 5 := by linarith only [Real.exp_one_lt_d9]
    linarith only [hv3, he]
  have hLpos : 0 < Real.log ((N:ℝ) * (|v| + 3)) := lt_of_lt_of_le one_pos hL1
  have hδlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ, one_mul]; exact hδ1)
  let FΛ : ℝ → ℝ := fun x => ‖logDeriv (DirichletCharacter.completedLFunction χ) ((x:ℂ) + (v:ℂ)*Complex.I)‖
  let Fγ : ℝ → ℝ := fun x => ‖logDeriv (DirichletCharacter.gammaFactor χ) ((x:ℂ) + (v:ℂ)*Complex.I)‖
  let FL : ℝ → ℝ := fun x => ‖logDeriv (DirichletCharacter.LFunction χ) ((x:ℂ) + (v:ℂ)*Complex.I)‖
  have hre : ∀ x : ℝ, (((x:ℂ) + (v:ℂ)*Complex.I)).re = x := fun x => by simp
  have him : ∀ x : ℝ, (((x:ℂ) + (v:ℂ)*Complex.I)).im = v := fun x => by simp
  have hmemΛ : ∀ x ∈ Set.uIcc (-1/2 : ℝ) 2, DirichletCharacter.completedLFunction χ
      ((x:ℂ) + (v:ℂ)*Complex.I) ≠ 0 := by
    intro x hx h0
    have hle := hsepA _ h0
    rw [him x, sub_self, abs_zero] at hle
    linarith only [hδ, hle]
  have hne0 : ∀ x : ℝ, ((x:ℂ) + (v:ℂ)*Complex.I) ≠ 0 := by
    intro x h0
    have := congrArg Complex.im h0
    rw [him x] at this; simp at this
    rw [this, abs_zero] at hvT; linarith only [hvT]
  have hle_half : ∀ x ∈ Set.uIcc (-1/2 : ℝ) 2, -(1 : ℝ) < x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-1/2:ℝ) ≤ 2)] at hx
    linarith only [hx.1, hx]
  have hmemγ : ∀ x ∈ Set.uIcc (-1/2 : ℝ) 2,
      ((x:ℂ) + (v:ℂ)*Complex.I) ∈ {z : ℂ | -(1 : ℝ) < z.re ∧ z ≠ 0} := by
    intro x hx
    exact ⟨by rw [hre x]; exact hle_half x hx, hne0 x⟩
  have hmemL : ∀ x ∈ Set.uIcc (-1/2 : ℝ) 2, DirichletCharacter.LFunction χ
      ((x:ℂ) + (v:ℂ)*Complex.I) ≠ 0 := by
    intro x hx h0
    have hprod := completedL_eq_gammaFactor_mul_L χ (hne0 x) (by rw [hre x]; exact hle_half x hx)
    rw [h0, mul_zero] at hprod
    exact hmemΛ x hx hprod
  have hpt : ∀ x ∈ Set.uIcc (-1/2 : ℝ) 2, FL x ≤ FΛ x + Fγ x := by
    intro x hx
    have hs0 : ((x:ℂ) + (v:ℂ)*Complex.I) ≠ 0 := hne0 x
    have hsplit : logDeriv (DirichletCharacter.LFunction χ) ((x:ℂ) + (v:ℂ)*Complex.I)
        = logDeriv (DirichletCharacter.completedLFunction χ) ((x:ℂ) + (v:ℂ)*Complex.I)
          - logDeriv (DirichletCharacter.gammaFactor χ) ((x:ℂ) + (v:ℂ)*Complex.I) := by
      have h := logDeriv_completedL_eq_add χ hχ hs0 (by rw [hre x]; exact hle_half x hx) (hmemL x hx)
      rw [h]; ring
    show ‖logDeriv (DirichletCharacter.LFunction χ) ((x:ℂ) + (v:ℂ)*Complex.I)‖ ≤ _
    rw [hsplit]
    exact norm_sub_le _ _
  have hcontΛ : ContinuousOn FΛ (Set.uIcc (-1/2 : ℝ) 2) :=
    ((continuousOn_logDeriv_completedL χ hχ).comp (by fun_prop) (fun x hx => hmemΛ x hx)).norm
  have hcontγ : ContinuousOn Fγ (Set.uIcc (-1/2 : ℝ) 2) :=
    ((continuousOn_logDeriv_gammaFactor χ).comp (by fun_prop) (fun x hx => hmemγ x hx)).norm
  have hcontL : ContinuousOn FL (Set.uIcc (-1/2 : ℝ) 2) :=
    ((continuousOn_logDeriv_L χ hχ).comp (by fun_prop) (fun x hx => hmemL x hx)).norm
  have hsub : Set.uIcc A B ⊆ Set.uIcc (-1/2 : ℝ) 2 := by
    intro x hx
    rw [Set.uIcc_of_le hAB] at hx
    rw [Set.uIcc_of_le (by norm_num : (-1/2:ℝ) ≤ 2)]
    exact ⟨by linarith only [hx.1, hA, hx], by linarith only [hx.2, hB2, hx]⟩
  have h1 : (∫ x in A..B, FL x) ≤ ∫ x in A..B, (FΛ x + Fγ x) := by
    apply intervalIntegral.integral_mono_on hAB
    · exact (hcontL.mono hsub).intervalIntegrable
    · exact ((hcontΛ.add hcontγ).mono hsub).intervalIntegrable
    · intro x hx; exact hpt x (hsub (by rw [Set.uIcc_of_le hAB]; exact hx))
  have h2 : (∫ x in A..B, (FΛ x + Fγ x)) ≤ (∫ x in (-1/2)..2, FΛ x) + (∫ x in (-1/2)..2, Fγ x) := by
    rw [intervalIntegral.integral_add ((hcontΛ.mono hsub).intervalIntegrable)
      ((hcontγ.mono hsub).intervalIntegrable)]
    have h1' : (∫ x in A..B, FΛ x) ≤ ∫ x in (-1/2)..2, FΛ x :=
      intervalIntegral.integral_mono_interval hA hAB hB2
        (Filter.Eventually.of_forall (fun x => norm_nonneg _)) hcontΛ.intervalIntegrable
    have h2' : (∫ x in A..B, Fγ x) ≤ ∫ x in (-1/2)..2, Fγ x :=
      intervalIntegral.integral_mono_interval hA hAB hB2
        (Filter.Eventually.of_forall (fun x => norm_nonneg _)) hcontγ.intervalIntegrable
    linarith only [h1', h2']
  have hvabs : 2 ≤ |v| := hvT
  have hΛb : (∫ x in (-1/2)..2, FΛ x) ≤ C1 * Real.log (N*(|v|+3)) * (Real.log (N*(|v|+3)) + Real.log (1/δ)) := by
    change (∫ x in (-1/2)..2, ‖logDeriv (DirichletCharacter.completedLFunction χ) ((x:ℂ) + (v:ℂ)*Complex.I)‖) ≤ _
    rcases le_or_gt 0 v with hv | hv
    · have hv' : |v| = v := abs_of_nonneg hv
      have hA' : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ abs (ρ.im - |v|) := by
        intro ρ hρ; rw [hv']; exact hsepA ρ hρ
      have hB' : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ abs (ρ.im + |v|) := by
        intro ρ hρ; rw [hv']; exact hsepB ρ hρ
      have h := (hC1 |v| hvabs δ hδ hδ1 hA' hB').1
      simpa [hv'] using h
    · have hv' : |v| = -v := abs_of_neg hv
      have hA' : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ abs (ρ.im - |v|) := by
        intro ρ hρ
        rw [hv', show ρ.im - (-v) = ρ.im + v by ring]
        exact hsepB ρ hρ
      have hB' : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ abs (ρ.im + |v|) := by
        intro ρ hρ
        rw [hv', show ρ.im + (-v) = ρ.im - v by ring]
        exact hsepA ρ hρ
      have h := (hC1 |v| (by rw [hv']; linarith only [hv2, hv']) δ hδ hδ1 hA' hB').2
      simpa [hv', neg_neg] using h
  have hγb : (∫ x in (-1/2)..2, Fγ x) ≤ C2 * Real.log (N*(|v|+3)) := by
    change (∫ x in (-1/2)..2, ‖logDeriv (DirichletCharacter.gammaFactor χ) ((x:ℂ) + (v:ℂ)*Complex.I)‖) ≤ _
    rcases le_or_gt 0 v with hv | hv
    · have hv' : |v| = v := abs_of_nonneg hv
      have h := (hC2 |v| hvabs).1
      simpa [hv'] using h
    · have hv' : |v| = -v := abs_of_neg hv
      have h := (hC2 |v| (by rw [hv']; linarith only [hv2, hv'])).2
      simpa [hv', neg_neg] using h
  have hLD : 1 ≤ Real.log (N*(|v|+3)) + Real.log (1/δ) := by linarith only [hL1, hδlog]
  have hLDnn : 0 ≤ Real.log (N*(|v|+3)) + Real.log (1/δ) := by linarith only [hL1, hδlog]
  have hC2b : C2 * Real.log (N*(|v|+3)) ≤ C2 * Real.log (N*(|v|+3)) * (Real.log (N*(|v|+3)) + Real.log (1/δ)) := by
    nlinarith only [mul_le_mul_of_nonneg_left hLD hC2pos.le, hC2pos, hLpos, hLD, hL1]
  have hC1b : C1 * Real.log (N*(|v|+3)) * (Real.log (N*(|v|+3)) + Real.log (1/δ))
      ≤ (C1 + C2 + 1) * Real.log (N*(|v|+3)) * (Real.log (N*(|v|+3)) + Real.log (1/δ)) := by
    have hnn : 0 ≤ Real.log (N*(|v|+3)) * (Real.log (N*(|v|+3)) + Real.log (1/δ)) := mul_nonneg hLpos.le hLDnn
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : C1 ≤ C1 + C2 + 1) hnn]
  nlinarith [h1, h2, hΛb, hγb, hC2b, hC1b, hC1pos, hC2pos, hL1, hLD, hLDnn, hδlog]

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

lemma rdcKernel_horiz_bound {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    {L : ℝ} (hL : 1 < L) {s : ℂ} {α : ℝ}
    (hsre : (-1/2:ℝ) < s.re) (hασ : s.re < α) (hα2 : α < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x v : ℝ), (-1/2:ℝ) ≤ x → x ≤ α → 2 * |s.im| + 2 ≤ |v| →
      ‖rdcKernel x₀ L f s ((x:ℂ) + (v:ℂ)*Complex.I)‖ ≤ C / v ^ 2 := by
  obtain ⟨C, hCpos, hCb⟩ := rdcKernel_norm_le_inv_sq hx₀ hB hcont hf2 hBnd hvan hL
    (by linarith only [hsre] : -(1/2:ℝ) < s.re) hασ (le_of_lt hα2)
  refine ⟨4 * C, by positivity, ?_⟩
  intro x v hx1 hx2 hv
  have hne : ((x:ℂ)+(v:ℂ)*Complex.I) ≠ s := by
    intro hh
    have him := congrArg Complex.im hh
    rw [show (((x:ℂ)+(v:ℂ)*Complex.I)).im = v by simp] at him
    have : |v| = |s.im| := by rw [him]
    linarith only [abs_nonneg s.im, hv, this]
  have hxre : (((x:ℂ)+(v:ℂ)*Complex.I)).re = x := by simp
  have h := hCb ((x:ℂ)+(v:ℂ)*Complex.I)
    (by rw [hxre]; linarith only [hx1]) (by rw [hxre]; linarith only [hx2]) hne
  have hnsq : ‖((x:ℂ)+(v:ℂ)*Complex.I) - s‖^2 = (x - s.re)^2 + (v - s.im)^2 := by
    have h1 : (((x:ℂ)+(v:ℂ)*Complex.I) - s).re = x - s.re := by simp
    have h2 : (((x:ℂ)+(v:ℂ)*Complex.I) - s).im = v - s.im := by simp
    rw [Complex.sq_norm, Complex.normSq_apply, h1, h2]; ring
  rw [hnsq] at h
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hv
    linarith only [abs_nonneg s.im, hv]
  have hvpos : (0:ℝ) < v^2/4 := by positivity
  have hquarter : v^2/4 ≤ (v - s.im)^2 := by
    have h1 : |v| - |s.im| ≤ |v - s.im| := by
      have h := abs_add_le (v - s.im) s.im
      rw [sub_add_cancel] at h
      linarith only [h]
    have h2 : |v|/2 ≤ |v - s.im| := by linarith only [h1, abs_nonneg s.im, hv]
    calc v^2/4 = (|v|/2)^2 := by rw [div_pow, sq_abs]; ring
      _ ≤ (v - s.im)^2 := by
          calc (|v|/2)^2 ≤ |v - s.im|^2 := pow_le_pow_left₀ (by positivity) h2 2
            _ = (v - s.im)^2 := sq_abs _
  have hApos : (0:ℝ) < (x - s.re)^2 + (v - s.im)^2 := by linarith only [sq_nonneg (x - s.re), hquarter, hvpos]
  calc ‖rdcKernel x₀ L f s ((x:ℂ) + (v:ℂ)*Complex.I)‖
      ≤ C / ((x - s.re)^2 + (v - s.im)^2) := h
    _ ≤ C / (v^2/4) := by
        rw [div_le_div_iff₀ hApos hvpos]
        nlinarith only [hCpos.le, hquarter, sq_nonneg (x - s.re), hvpos, hCpos]
    _ = 4*C / v^2 := by
        rw [div_eq_div_iff (by positivity : (v^2/4) ≠ 0) (by positivity : v^2 ≠ 0)]
        ring

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

lemma rdcKernel_continuousOn_ne {x₀ L : ℝ} (hx₀ : 0 ≤ x₀) (hL : L ≠ 0) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (s : ℂ) :
    ContinuousOn (fun u : ℂ => rdcKernel x₀ L f s u) {u : ℂ | u ≠ s} := by
  have h1 : Continuous (fun u : ℂ => lapX x₀ f ((s - u) * (L : ℂ))) :=
    (differentiable_lapX_affine hx₀ hcont s L).continuous
  have h2 : ContinuousOn (fun u : ℂ => f 0 / ((s - u) * (L : ℂ))) {u : ℂ | u ≠ s} := by
    have hnum : ContinuousOn (fun _ : ℂ => f 0) {u : ℂ | u ≠ s} := continuousOn_const
    have hden : ContinuousOn (fun u : ℂ => (s - u) * (L : ℂ)) {u : ℂ | u ≠ s} := by
      have hc : Continuous (fun u : ℂ => (s - u) * (L:ℂ)) := by fun_prop
      exact (hc.continuousOn).mono (Set.subset_univ _)
    exact ContinuousOn.div hnum hden (fun u hu => by
      have h1 : s - u ≠ 0 := by intro h; exact hu (sub_eq_zero.mp h).symm
      have h2 : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
      exact mul_ne_zero h1 h2)
  have heq : (fun u : ℂ => rdcKernel x₀ L f s u)
      = fun u : ℂ => lapX x₀ f ((s - u) * (L : ℂ)) - f 0 / ((s - u) * (L : ℂ)) := by
    funext u; rw [rdcKernel_eq_lapX]
  rw [heq]
  exact h1.continuousOn.sub h2

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

lemma rdc_horiz_integral_bound {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {L : ℝ} (hL : 1 < L) {s : ℂ} {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hασ : s.re < α)
    (hsre : -(1/2:ℝ) < s.re) {c : ℝ} (hc : 0 < c) :
    ∃ Kk : ℝ, 0 < Kk ∧ ∀ (V : ℝ), 2 * |s.im| + 2 ≤ |V| →
      (∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
        min c 1 / Real.log ((N:ℝ) * (|V| + 3)) ≤ |ρ.im - V|) →
      (∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
        min c 1 / Real.log ((N:ℝ) * (|V| + 3)) ≤ |ρ.im + V|) →
      ‖∫ x in (-1/2)..α, logDeriv (DirichletCharacter.LFunction χ) ((x:ℂ) + (V:ℂ)*Complex.I)
          * rdcKernel x₀ L f s ((x:ℂ) + (V:ℂ)*Complex.I)‖
        ≤ Kk * (Real.log ((N:ℝ)*(|V|+3)))^2 / (1 + V^2) := by
  obtain ⟨CΦ, hCΦpos, hCΦb⟩ := rdcKernel_horiz_bound hx₀ hB hcont hf2 hBnd hvan hL
    (by linarith only [hsre] : (-1/2:ℝ) < s.re) hασ hα2
  obtain ⟨CL, hCLpos, hCLb⟩ := integral_norm_logDeriv_LFunction_le χ hχ hχprim
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast NeZero.one_le
  have hmin : 0 < min c 1 := lt_min hc zero_lt_one
  have hminle1 : min c 1 ≤ 1 := min_le_right _ _
  have hminle : min c 1 ≤ c := min_le_left _ _
  have hminlog : Real.log (min c 1) ≤ 0 := Real.log_nonpos hmin.le hminle1
  set K0 : ℝ := |Real.log (min c 1)| with hK0def
  have hK0le : -Real.log (min c 1) ≤ K0 := by rw [hK0def, abs_of_nonpos hminlog]
  have hK0nn : 0 ≤ K0 := abs_nonneg _
  refine ⟨2 * CΦ * CL * (3 + K0), by positivity, ?_⟩
  intro V hV hsp hsp'
  set Lg : ℝ := Real.log ((N:ℝ)*(|V|+3)) with hLgdef
  have hVne : V ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hV
    linarith only [abs_nonneg s.im, hα1, hα2, hV]
  have hV2 : 4 ≤ V^2 := by nlinarith only [hV, abs_nonneg s.im, sq_abs V]
  have hLp : 0 < Lg := by
    rw [hLgdef]; apply Real.log_pos; nlinarith only [hN1, abs_nonneg V, hα1, hα2]
  have hL1 : 1 ≤ Lg := by
    rw [hLgdef, Real.le_log_iff_exp_le (by positivity)]
    have he : Real.exp 1 < 5 := by linarith only [Real.exp_one_lt_d9, hα1, hα2]
    have h5 : (5:ℝ) ≤ (N:ℝ) * (|V| + 3) := by nlinarith only [hN1, abs_nonneg V, hV, abs_nonneg s.im]
    linarith only [he, h5]
  set δ : ℝ := min c 1 / Lg with hδdef
  have hδpos : 0 < δ := div_pos hmin hLp
  have hδle1 : δ ≤ 1 := by rw [hδdef, div_le_one hLp]; linarith only [hminle1, hL1]
  have hδA : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ |ρ.im - V| := by
    intro ρ hρ; rw [hδdef, hLgdef]; exact hsp ρ hρ
  have hδB : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ |ρ.im + V| := by
    intro ρ hρ; rw [hδdef, hLgdef]; exact hsp' ρ hρ
  have hCLb' := hCLb le_rfl (by linarith only [hα1, hα2] : (-1/2:ℝ) ≤ α) (le_of_lt hα2)
    (by linarith only [hV, abs_nonneg s.im] : 2 ≤ |V|) hδpos hδle1 hδA hδB
  have hkern : ∀ x ∈ Set.uIcc (-1/2:ℝ) α,
      ‖rdcKernel x₀ L f s ((x:ℂ) + (V:ℂ)*Complex.I)‖ ≤ CΦ / V^2 := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith only [hα1, hα2] : (-1/2:ℝ) ≤ α)] at hx
    exact hCΦb x V hx.1 hx.2 hV
  have hneV : ∀ x : ℝ, ((x:ℂ) + (V:ℂ)*Complex.I) ≠ s := by
    intro x hx
    have him := congrArg Complex.im hx
    rw [show (((x:ℂ) + (V:ℂ)*Complex.I)).im = V by simp] at him
    have : |V| = |s.im| := by rw [him]
    linarith only [abs_nonneg s.im, hV, hα1, hα2, this]
  have hmemΛ : ∀ x ∈ Set.uIcc (-1/2:ℝ) α, DirichletCharacter.completedLFunction χ
      ((x:ℂ) + (V:ℂ)*Complex.I) ≠ 0 := by
    intro x hx h0
    have hle := hδA _ h0
    have him : (((x:ℂ) + (V:ℂ)*Complex.I)).im = V := by simp
    rw [him, sub_self, abs_zero] at hle; linarith only [hδpos, hle]
  have hmemL : ∀ x ∈ Set.uIcc (-1/2:ℝ) α, DirichletCharacter.LFunction χ
      ((x:ℂ) + (V:ℂ)*Complex.I) ≠ 0 := by
    intro x hx h0
    have hx' := hx
    rw [Set.uIcc_of_le (by linarith only [hα1, hα2] : (-1/2:ℝ) ≤ α)] at hx'
    have hu0 : ((x:ℂ) + (V:ℂ)*Complex.I) ≠ 0 := by
      intro hz
      have him := congrArg Complex.im hz
      rw [show (((x:ℂ) + (V:ℂ)*Complex.I)).im = V by simp] at him
      rw [him] at hV
      simp at hV
      linarith only [abs_nonneg s.im, hα1, hα2, hV]
    have hprod := completedL_eq_gammaFactor_mul_L χ hu0 (by simp; linarith only [hx'.1, hα1, hα2, hx'])
    rw [h0, mul_zero] at hprod
    exact hmemΛ x hx hprod
  have hcont1 : ContinuousOn (fun x : ℝ => logDeriv (DirichletCharacter.LFunction χ)
      ((x:ℂ)+(V:ℂ)*Complex.I)) (Set.uIcc (-1/2:ℝ) α) :=
    (continuousOn_logDeriv_L χ hχ).comp (by fun_prop) (fun x hx => hmemL x hx)
  have hcont2 : ContinuousOn (fun x : ℝ => rdcKernel x₀ L f s ((x:ℂ)+(V:ℂ)*Complex.I))
      (Set.uIcc (-1/2:ℝ) α) :=
    (rdcKernel_continuousOn_ne hx₀.le (by linarith only [hL, hα1, hα2] : L ≠ 0) hcont s).comp (by fun_prop)
      (fun x hx => hneV x)
  have hintF : IntervalIntegrable (fun x : ℝ => logDeriv (DirichletCharacter.LFunction χ)
      ((x:ℂ)+(V:ℂ)*Complex.I) * rdcKernel x₀ L f s ((x:ℂ)+(V:ℂ)*Complex.I)) volume (-1/2) α :=
    (hcont1.mul hcont2).intervalIntegrable
  have hintg : IntervalIntegrable (fun x : ℝ => (CΦ/V^2) * ‖logDeriv (DirichletCharacter.LFunction χ)
      ((x:ℂ)+(V:ℂ)*Complex.I)‖) volume (-1/2) α :=
    ((hcont1.norm).const_mul (CΦ/V^2)).intervalIntegrable
  have hpt : ∀ x ∈ Set.uIcc (-1/2:ℝ) α, ‖logDeriv (DirichletCharacter.LFunction χ)
        ((x:ℂ)+(V:ℂ)*Complex.I) * rdcKernel x₀ L f s ((x:ℂ)+(V:ℂ)*Complex.I)‖
      ≤ (CΦ/V^2) * ‖logDeriv (DirichletCharacter.LFunction χ) ((x:ℂ)+(V:ℂ)*Complex.I)‖ := by
    intro x hx
    rw [norm_mul]
    have hb := hkern x hx
    calc ‖logDeriv (DirichletCharacter.LFunction χ) ((x:ℂ) + (V:ℂ)*Complex.I)‖
            * ‖rdcKernel x₀ L f s ((x:ℂ) + (V:ℂ)*Complex.I)‖
        ≤ ‖logDeriv (DirichletCharacter.LFunction χ) ((x:ℂ) + (V:ℂ)*Complex.I)‖ * (CΦ/V^2) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = (CΦ/V^2) * ‖logDeriv (DirichletCharacter.LFunction χ) ((x:ℂ) + (V:ℂ)*Complex.I)‖ := by ring
  have hlogδ : Real.log (1/δ) ≤ Real.log Lg + K0 := by
    have h1 : (1:ℝ)/δ = Lg / min c 1 := by rw [hδdef, one_div, inv_div]
    rw [h1, Real.log_div hLp.ne' hmin.ne']
    linarith only [hK0le]
  have hloglog : Real.log Lg ≤ Lg := Real.log_le_self hLp.le
  have hsum : Lg * (Lg + Real.log (1/δ)) ≤ (3 + K0) * Lg^2 := by
    have h1 : Real.log (1/δ) ≤ Lg + K0 := by linarith only [hlogδ, hloglog]
    have h2 : Lg * (Lg + Real.log (1/δ)) ≤ Lg * (Lg + (Lg + K0)) := by
      apply mul_le_mul_of_nonneg_left _ hLp.le; linarith only [hlogδ, hloglog]
    have h3 : Lg * (Lg + (Lg + K0)) = 2*Lg^2 + K0*Lg := by ring
    have h4 : K0 * Lg ≤ K0 * Lg^2 := by nlinarith only [mul_nonneg hK0nn hLp.le, hL1, hK0nn, hLp, sq_nonneg Lg, hα1, hα2]
    nlinarith only [h2, h3, h4]
  calc ‖∫ x in (-1/2)..α, logDeriv (DirichletCharacter.LFunction χ) ((x:ℂ) + (V:ℂ)*Complex.I)
          * rdcKernel x₀ L f s ((x:ℂ) + (V:ℂ)*Complex.I)‖
      ≤ ∫ x in (-1/2)..α, ‖logDeriv (DirichletCharacter.LFunction χ) ((x:ℂ) + (V:ℂ)*Complex.I)
          * rdcKernel x₀ L f s ((x:ℂ) + (V:ℂ)*Complex.I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith only [hα1, hα2] : (-1/2:ℝ) ≤ α)
    _ ≤ ∫ x in (-1/2)..α, (CΦ/V^2) * ‖logDeriv (DirichletCharacter.LFunction χ)
          ((x:ℂ) + (V:ℂ)*Complex.I)‖ := by
        apply intervalIntegral.integral_mono_on (by linarith only [hα1, hα2] : (-1/2:ℝ) ≤ α) hintF.norm hintg
        intro x hx
        exact hpt x (by rw [Set.uIcc_of_le (by linarith only [hα1, hα2] : (-1/2:ℝ) ≤ α)]; exact hx)
    _ = (CΦ/V^2) * ∫ x in (-1/2)..α, ‖logDeriv (DirichletCharacter.LFunction χ)
          ((x:ℂ) + (V:ℂ)*Complex.I)‖ := intervalIntegral.integral_const_mul _ _
    _ ≤ (CΦ/V^2) * (CL * Lg * (Lg + Real.log (1/δ))) :=
        mul_le_mul_of_nonneg_left hCLb' (by positivity)
    _ = (CΦ * CL * Lg * (Lg + Real.log (1/δ))) / V^2 := by ring
    _ ≤ (CΦ * CL * ((3 + K0) * Lg^2)) / V^2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [show CΦ * CL * Lg * (Lg + Real.log (1/δ))
            = CΦ * CL * (Lg * (Lg + Real.log (1/δ))) by ring]
        exact mul_le_mul_of_nonneg_left hsum (by positivity : (0:ℝ) ≤ CΦ * CL)
    _ ≤ (2 * CΦ * CL * (3 + K0)) * Lg^2 / (1 + V^2) := by
        rw [div_le_div_iff₀ (by positivity : (0:ℝ) < V^2) (by positivity : (0:ℝ) < 1 + V^2)]
        have hfac : 1 + V^2 ≤ 2 * V^2 := by linarith only [hV2, hα1, hα2]
        have hpos : 0 ≤ CΦ * CL * (3 + K0) * Lg^2 := by positivity
        nlinarith only [hfac, hpos, hCΦpos, hCLpos, hK0nn, sq_nonneg Lg, hα1, hα2, hV2]

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

lemma horizontal_rdc_tendsto {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {L : ℝ} (hL : 1 < L) {s : ℂ} {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hασ : s.re < α)
    (hsre : -(1/2:ℝ) < s.re)
    {c : ℝ} (hc : 0 < c) {Tf : ℝ → ℝ} (hTftend : Filter.Tendsto Tf Filter.atTop Filter.atTop)
    (hTfbig : ∀ᶠ T : ℝ in Filter.atTop, 2 * |s.im| + 2 ≤ |Tf T|)
    (hsep : ∀ᶠ T : ℝ in Filter.atTop, ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
      c / Real.log ((N:ℝ) * (|Tf T| + 3)) ≤ |ρ.im - Tf T|)
    (hsep' : ∀ᶠ T : ℝ in Filter.atTop, ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
      c / Real.log ((N:ℝ) * (|Tf T| + 3)) ≤ |ρ.im + Tf T|) :
    (Filter.Tendsto (fun T : ℝ => ∫ x in (-1/2)..α, logDeriv (DirichletCharacter.LFunction χ)
        ((x:ℂ) + (Tf T:ℂ)*Complex.I) * rdcKernel x₀ L f s ((x:ℂ) + (Tf T:ℂ)*Complex.I))
      Filter.atTop (nhds 0))
    ∧ (Filter.Tendsto (fun T : ℝ => ∫ x in (-1/2)..α, logDeriv (DirichletCharacter.LFunction χ)
        ((x:ℂ) - (Tf T:ℂ)*Complex.I) * rdcKernel x₀ L f s ((x:ℂ) - (Tf T:ℂ)*Complex.I))
      Filter.atTop (nhds 0)) := by
  obtain ⟨Kk, hKkpos, hbound⟩ := rdc_horiz_integral_bound hx₀ hB hcont hf2 hBnd hvan χ hχ hχprim
    hL hα1 hα2 hασ hsre hc
  have hmin : 0 < min c 1 := lt_min hc zero_lt_one
  have hminle : min c 1 ≤ c := min_le_left _ _
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast NeZero.one_le
  have habs : Filter.Tendsto (fun T : ℝ => |Tf T|) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop] at hTftend ⊢
    intro b
    filter_upwards [hTftend b, hTftend 0] with T h1 h2
    rw [abs_of_nonneg h2]; exact h1
  have hg : Filter.Tendsto (fun T : ℝ => Kk * (Real.log ((N:ℝ)*(|Tf T|+3)))^2
      / (1 + (Tf T)^2)) Filter.atTop (nhds 0) := by
    have h := ((Commons.NumberTheory.Linnik.tendsto_log_N_sq_div (N := N)).comp habs).const_mul Kk
    have heq : (fun T : ℝ => Kk * (Real.log ((N:ℝ)*(|Tf T|+3)))^2 / (1 + (Tf T)^2))
        = (fun T : ℝ => Kk * ((Real.log ((N:ℝ)*(|Tf T|+3)))^2 / (1 + |Tf T|^2))) := by
      funext T; rw [sq_abs]; ring
    rw [heq]; simpa using h
  have hlogv : ∀ᶠ T : ℝ in Filter.atTop, 0 ≤ Real.log ((N:ℝ)*(|Tf T|+3)) := by
    filter_upwards with T
    exact Real.log_nonneg (by nlinarith only [hN1, abs_nonneg (Tf T), hα1, hα2])
  have hkeyP : ∀ᶠ T : ℝ in Filter.atTop, ‖∫ x in (-1/2)..α,
      logDeriv (DirichletCharacter.LFunction χ) ((x:ℂ) + (Tf T:ℂ)*Complex.I)
        * rdcKernel x₀ L f s ((x:ℂ) + (Tf T:ℂ)*Complex.I)‖
      ≤ Kk * (Real.log ((N:ℝ)*(|Tf T|+3)))^2 / (1 + (Tf T)^2) := by
    filter_upwards [hTfbig, hsep, hsep', hlogv] with T hbig hsp hsp' hlog
    exact hbound (Tf T) hbig
      (fun ρ hρ => le_trans (div_le_div_of_nonneg_right hminle hlog) (hsp ρ hρ))
      (fun ρ hρ => le_trans (div_le_div_of_nonneg_right hminle hlog) (hsp' ρ hρ))
  have hkeyM : ∀ᶠ T : ℝ in Filter.atTop, ‖∫ x in (-1/2)..α,
      logDeriv (DirichletCharacter.LFunction χ) ((x:ℂ) - (Tf T:ℂ)*Complex.I)
        * rdcKernel x₀ L f s ((x:ℂ) - (Tf T:ℂ)*Complex.I)‖
      ≤ Kk * (Real.log ((N:ℝ)*(|Tf T|+3)))^2 / (1 + (Tf T)^2) := by
    filter_upwards [hTfbig, hsep, hsep', hlogv] with T hbig hsp hsp' hlog
    have hbig' : 2 * |s.im| + 2 ≤ |(-(Tf T))| := by rw [abs_neg]; exact hbig
    have h := hbound (-(Tf T)) hbig'
      (fun ρ hρ => by
        have hE : ρ.im - (-(Tf T)) = ρ.im + Tf T := by ring
        have hE2 : (N:ℝ) * (|(-(Tf T))| + 3) = (N:ℝ) * (|Tf T| + 3) := by rw [abs_neg]
        rw [hE, hE2]
        exact le_trans (div_le_div_of_nonneg_right hminle hlog) (hsp' ρ hρ))
      (fun ρ hρ => by
        have hE : ρ.im + (-(Tf T)) = ρ.im - Tf T := by ring
        have hE2 : (N:ℝ) * (|(-(Tf T))| + 3) = (N:ℝ) * (|Tf T| + 3) := by rw [abs_neg]
        rw [hE, hE2]
        exact le_trans (div_le_div_of_nonneg_right hminle hlog) (hsp ρ hρ))
    rw [show (Real.log ((N:ℝ)*(|-(Tf T)|+3)))^2 = (Real.log ((N:ℝ)*(|Tf T|+3)))^2 by rw [abs_neg]] at h
    rw [show ((-(Tf T))^2) = (Tf T)^2 by ring] at h
    simpa [sub_eq_add_neg] using h
  refine ⟨?_, ?_⟩
  · have h00 : ∀ᶠ T : ℝ in Filter.atTop, (0:ℝ) ≤ ‖∫ x in (-1/2)..α,
        logDeriv (DirichletCharacter.LFunction χ) ((x:ℂ) + (Tf T:ℂ)*Complex.I)
          * rdcKernel x₀ L f s ((x:ℂ) + (Tf T:ℂ)*Complex.I)‖ :=
      Filter.Eventually.of_forall (fun T => norm_nonneg _)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' h00 hkeyP hg
  · have h00 : ∀ᶠ T : ℝ in Filter.atTop, (0:ℝ) ≤ ‖∫ x in (-1/2)..α,
        logDeriv (DirichletCharacter.LFunction χ) ((x:ℂ) - (Tf T:ℂ)*Complex.I)
          * rdcKernel x₀ L f s ((x:ℂ) - (Tf T:ℂ)*Complex.I)‖ :=
      Filter.Eventually.of_forall (fun T => norm_nonneg _)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' h00 hkeyM hg

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

lemma analyticAt_GammaR_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.Gammaℝ z := by
  have hinv : Differentiable ℂ (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) :=
    Complex.differentiable_Gammaℝ_inv
  have hinvz : (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) z ≠ 0 :=
    inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hz)
  have han0 : AnalyticAt ℂ (fun s : ℂ => ((Complex.Gammaℝ s)⁻¹)⁻¹) z :=
    (hinv.analyticAt z).inv hinvz
  exact han0.congr (Filter.Eventually.of_forall (fun s => inv_inv _))

lemma GammaR_ne_zero_of {z : ℂ} (hz0 : z ≠ 0) (hzre : -(1:ℝ) < z.re) :
    Complex.Gammaℝ z ≠ 0 := by
  intro h
  rw [Complex.Gammaℝ_eq_zero_iff] at h
  rcases h with ⟨n, hn⟩
  rcases Nat.eq_zero_or_pos n with hh | hh
  · subst hh
    simp only [Nat.cast_zero, mul_zero, neg_zero] at hn
    exact hz0 hn
  · have h2 : (2:ℤ) ≤ 2 * (n:ℤ) := by
      have h1 : (1:ℤ) ≤ (n:ℤ) := by exact_mod_cast hh
      omega
    have hlt : (-(2 * (n:ℝ))) ≤ -2 := by
      have : (2:ℝ) ≤ 2 * (n:ℝ) := by exact_mod_cast h2
      linarith only [this]
    have hre : z.re = -(2 * (n:ℝ)) := by
      rw [hn]; push_cast; simp
    linarith only [hzre, hlt, hre]

lemma analyticAt_GammaR_of {z : ℂ} (hz0 : z ≠ 0) (hzre : -(1:ℝ) < z.re) :
    AnalyticAt ℂ Complex.Gammaℝ z := by
  have hinv : Differentiable ℂ (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) :=
    Complex.differentiable_Gammaℝ_inv
  have hinvz : (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) z ≠ 0 :=
    inv_ne_zero (GammaR_ne_zero_of hz0 hzre)
  have han0 : AnalyticAt ℂ (fun s : ℂ => ((Complex.Gammaℝ s)⁻¹)⁻¹) z :=
    (hinv.analyticAt z).inv hinvz
  exact han0.congr (Filter.Eventually.of_forall (fun s => inv_inv _))

lemma gammaFactor_analyticAt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) [Decidable χ.Even]
    {s : ℂ} (hsre : -(1/2:ℝ) < s.re) (hs0 : χ.Even → s ≠ 0) :
    AnalyticAt ℂ (DirichletCharacter.gammaFactor χ) s := by
  rcases χ.even_or_odd with hE | hO
  · have hγ : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := by
      funext z; exact DirichletCharacter.Even.gammaFactor_def hE z
    rw [hγ]
    exact analyticAt_GammaR_of (hs0 hE) (by linarith only [hsre])
  · have hγ : DirichletCharacter.gammaFactor χ = (fun z : ℂ => Complex.Gammaℝ (z + 1)) := by
      funext z; exact DirichletCharacter.Odd.gammaFactor_def hO z
    rw [hγ]
    have h1 : (0:ℝ) < (s + 1).re := by simp; linarith only [hsre]
    exact AnalyticAt.comp (g := Complex.Gammaℝ) (f := fun z : ℂ => z + 1) (x := s)
      (analyticAt_GammaR_of_re_pos h1) (by fun_prop)

lemma gammaFactor_ne_zero' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) [Decidable χ.Even]
    {s : ℂ} (hsre : -(1/2:ℝ) < s.re) (hs0 : χ.Even → s ≠ 0) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with hE | hO
  · have hγ : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := by
      funext z; exact DirichletCharacter.Even.gammaFactor_def hE z
    rw [hγ]
    exact GammaR_ne_zero_of (hs0 hE) (by linarith only [hsre])
  · have hγ : DirichletCharacter.gammaFactor χ = (fun z : ℂ => Complex.Gammaℝ (z + 1)) := by
      funext z; exact DirichletCharacter.Odd.gammaFactor_def hO z
    rw [hγ]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.one_re]; linarith only [hsre]

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

lemma gammaFactor_analyticAt_rect {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) [Decidable χ.Even]
    {z : ℂ} (hz0 : z ≠ 0) (hzre : -(1:ℝ) < z.re) :
    AnalyticAt ℂ (DirichletCharacter.gammaFactor χ) z ∧ DirichletCharacter.gammaFactor χ z ≠ 0 := by
  rcases χ.even_or_odd with hE | hO
  · have hγ : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ := by
      funext w; exact DirichletCharacter.Even.gammaFactor_def hE w
    rw [hγ]
    exact ⟨analyticAt_GammaR_of hz0 hzre, GammaR_ne_zero_of hz0 hzre⟩
  · have hγ : DirichletCharacter.gammaFactor χ = (fun w : ℂ => Complex.Gammaℝ (w + 1)) := by
      funext w; exact DirichletCharacter.Odd.gammaFactor_def hO w
    rw [hγ]
    have hz1 : z + 1 ≠ 0 := by
      intro hh; have := congrArg Complex.re hh; simp at this; linarith only [hzre, this]
    have h1 : AnalyticAt ℂ Complex.Gammaℝ (z + 1) :=
      analyticAt_GammaR_of hz1 (by simp; linarith only [hzre])
    have h2 : Complex.Gammaℝ (z + 1) ≠ 0 :=
      GammaR_ne_zero_of hz1 (by simp; linarith only [hzre])
    exact ⟨AnalyticAt.comp (g := Complex.Gammaℝ) (f := fun w : ℂ => w + 1) (x := z) h1
      (by fun_prop), h2⟩

lemma zeros_far_from {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) {s : ℂ} (hs : DirichletCharacter.completedLFunction χ s ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ ‖ρ - s‖ := by
  have hfin : ({ρ : ℂ | DirichletCharacter.completedLFunction χ ρ = 0 ∧ ‖ρ - s‖ ≤ 1} : Set ℂ).Finite := by
    refine Set.Finite.subset (Commons.NumberTheory.Linnik.grg_zeroSet_finite χ hχ hχprim
      (B := ‖s‖ + 1) (by positivity)) ?_
    intro u hu
    refine ⟨hu.1, ?_⟩
    have h1 : ‖u‖ ≤ ‖u - s‖ + ‖s‖ := by
      simpa [sub_add_cancel] using norm_add_le (u - s) s
    linarith [hu.2, h1]
  have hmem : ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → ρ ≠ s := by
    intro ρ hρ h0; exact hs (h0 ▸ hρ)
  set S : Finset ℂ := hfin.toFinset with hSdef
  have hSmem : ∀ ρ : ℂ, ρ ∈ S ↔ DirichletCharacter.completedLFunction χ ρ = 0 ∧ ‖ρ - s‖ ≤ 1 := by
    intro ρ; simp only [hSdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hS : ∀ ρ ∈ S, 0 < ‖ρ - s‖ := by
    intro ρ hρ
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr (hmem ρ ((hSmem ρ).mp hρ).1)
  rcases S.eq_empty_or_nonempty with hem | hne
  · refine ⟨1, one_pos, fun ρ hρ => ?_⟩
    by_contra hcon
    push_neg at hcon
    have : ρ ∈ S := (hSmem ρ).mpr ⟨hρ, le_of_lt hcon⟩
    rw [hem] at this; exact absurd this (by simp)
  · refine ⟨S.inf' hne (fun ρ => ‖ρ - s‖), ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro ρ hρ
      exact hS ρ hρ
    · have hδ1 : S.inf' hne (fun ρ => ‖ρ - s‖) ≤ 1 := by
        calc S.inf' hne (fun ρ => ‖ρ - s‖) ≤ ‖hne.choose - s‖ :=
              Finset.inf'_le _ hne.choose_spec
          _ ≤ 1 := ((hSmem _).mp hne.choose_spec).2
      intro ρ hρ
      by_cases h1 : ‖ρ - s‖ ≤ 1
      · exact Finset.inf'_le _ ((hSmem ρ).mpr ⟨hρ, h1⟩)
      · push_neg at h1; linarith only [hne, hδ1, h1]

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

lemma rectInt_sub'' {z w : ℂ} {f g : ℂ → ℂ}
    (hf1 : IntervalIntegrable (fun x : ℝ => f (x + z.im * Complex.I)) volume z.re w.re)
    (hg1 : IntervalIntegrable (fun x : ℝ => g (x + z.im * Complex.I)) volume z.re w.re)
    (hf2 : IntervalIntegrable (fun x : ℝ => f (x + w.im * Complex.I)) volume z.re w.re)
    (hg2 : IntervalIntegrable (fun x : ℝ => g (x + w.im * Complex.I)) volume z.re w.re)
    (hf3 : IntervalIntegrable (fun y : ℝ => f (w.re + y * Complex.I)) volume z.im w.im)
    (hg3 : IntervalIntegrable (fun y : ℝ => g (w.re + y * Complex.I)) volume z.im w.im)
    (hf4 : IntervalIntegrable (fun y : ℝ => f (z.re + y * Complex.I)) volume z.im w.im)
    (hg4 : IntervalIntegrable (fun y : ℝ => g (z.re + y * Complex.I)) volume z.im w.im) :
    rectInt z w (fun s => f s - g s) = rectInt z w f - rectInt z w g := by
  have h : (fun s : ℂ => f s - g s) = fun s : ℂ => f s + (-1) * g s := by funext s; ring
  rw [h, rectInt_add'' hf1 (hg1.const_mul (-1)) hf2 (hg2.const_mul (-1)) hf3 (hg3.const_mul (-1))
    hf4 (hg4.const_mul (-1))]
  rw [rectInt_const_mul' (-1) g]
  ring

lemma completedL_ne_zero_of_re_eq_neg_half {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (τ : ℝ) :
    DirichletCharacter.completedLFunction χ (((-1/2:ℝ):ℂ) + (τ:ℂ)*Complex.I) ≠ 0 := by
  set u : ℂ := ((-1/2:ℝ):ℂ) + (τ:ℂ)*Complex.I with hudef
  have hu0 : u ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hudef] at this
    simp at this
  have hure : -(1:ℝ) < u.re := by rw [hudef]; simp; norm_num
  rw [completedL_eq_gammaFactor_mul_L χ hu0 hure]
  refine mul_ne_zero ?_ ?_
  · exact gammaFactor_ne_zero_of_re_gt_neg_one χ hure hu0
  · rw [hudef]; exact LFunction_ne_zero_of_re_eq_neg_half χ hχ hχprim τ

lemma completedL_ne_zero_of_one_lt_re' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {τ : ℝ} {σ : ℝ} (hσ : 1 < σ) :
    DirichletCharacter.completedLFunction χ ((σ:ℂ) + (τ:ℂ)*Complex.I) ≠ 0 :=
  completedLFunction_ne_zero_of_one_lt_re χ (by simp; linarith only [hσ])

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

lemma logDeriv_completedL_eq_add' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {s : ℂ} (hsre : -(1/2:ℝ) < s.re) (hLs : DirichletCharacter.LFunction χ s ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      logDeriv (DirichletCharacter.gammaFactor χ) s + logDeriv (DirichletCharacter.LFunction χ) s := by
  by_cases hs0 : s = 0
  · subst hs0
    rcases χ.even_or_odd with hE | hO
    · have hN1 : N ≠ 1 := by intro h; exact hχ (by subst h; exact Subsingleton.elim χ 1)
      have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 0 (Or.inr hN1)
      rw [hE.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by simp⟩, div_zero] at h
      exact absurd h hLs
    · have hN1 : N ≠ 1 := by intro h; exact hχ (by subst h; exact Subsingleton.elim χ 1)
      have hγ0 : DirichletCharacter.gammaFactor χ 0 = 1 := by
        rw [hO.gammaFactor_def]; simpa using Complex.Gammaℝ_one
      have hL0 : DirichletCharacter.LFunction χ 0 = DirichletCharacter.completedLFunction χ 0 := by
        rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 0 (Or.inr hN1), hγ0, div_one]
      have hev : DirichletCharacter.completedLFunction χ =ᶠ[𝓝 (0:ℂ)]
          (fun u => DirichletCharacter.gammaFactor χ u * DirichletCharacter.LFunction χ u) := by
        refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨{u : ℂ | -(1:ℝ) < u.re}, ?_, ?_⟩
        · exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
        · intro u hu
          by_cases hu0 : u = 0
          · subst hu0
            change DirichletCharacter.completedLFunction χ 0 =
              DirichletCharacter.gammaFactor χ 0 * DirichletCharacter.LFunction χ 0
            rw [hγ0, hL0, one_mul]
          · exact completedL_eq_gammaFactor_mul_L χ hu0 hu
      have h1 : logDeriv (fun u => DirichletCharacter.gammaFactor χ u * DirichletCharacter.LFunction χ u) 0
          = logDeriv (DirichletCharacter.completedLFunction χ) 0 :=
        (logDeriv_congr_nhds hev.symm).eq_of_nhds
      rw [← h1]
      have hγan0 : AnalyticAt ℂ (DirichletCharacter.gammaFactor χ) 0 := by
        have hfun : DirichletCharacter.gammaFactor χ = fun u : ℂ => Complex.Gammaℝ (u + 1) :=
          funext (fun u => hO.gammaFactor_def u)
        rw [hfun]
        exact AnalyticAt.comp (g := Complex.Gammaℝ) (f := fun u : ℂ => u + 1) (x := 0)
          (analyticAt_GammaR_of_re_pos (by norm_num)) (by fun_prop)
      exact logDeriv_mul 0 (by rw [hγ0]; norm_num) hLs hγan0.differentiableAt
        ((DirichletCharacter.differentiable_LFunction hχ) 0)
  · rw [logDeriv_completedL_eq_add χ hχ hs0 (by linarith only [hsre]) hLs]



end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

theorem rdc_shift_identity {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B)
    {f : ℝ → ℂ} (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {L : ℝ} (hL : 1 < L) {s : ℂ} {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hασ : s.re < α)
    (hsre : -(1/2 : ℝ) < s.re) (hLs : DirichletCharacter.LFunction χ s ≠ 0) :
    (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) *
        rdcKernel x₀ L f s u)
      = (1 / (2 * (Real.pi : ℂ))) *
          ((∫ τ : ℝ, logDeriv (DirichletCharacter.LFunction χ) ((α : ℂ) + (τ : ℂ) * Complex.I) *
              rdcKernel x₀ L f s ((α : ℂ) + (τ : ℂ) * Complex.I))
           - (∫ τ : ℝ, logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I) *
              rdcKernel x₀ L f s (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)))
        - logDeriv (DirichletCharacter.LFunction χ) s * (f 0 / (L : ℂ))
        - (if χ.Even then rdcKernel x₀ L f s 0 else 0) := by
  classical
  have hLpos : 0 < L := by linarith only [hL, hα1, hα2]
  set Λ := DirichletCharacter.completedLFunction χ with hΛdef
  set γ := DirichletCharacter.gammaFactor χ with hγdef
  set Lf := DirichletCharacter.LFunction χ with hLfdef
  set Φ : ℂ → ℂ := fun u => rdcKernel x₀ L f s u with hΦdef
  set r : ℂ := f 0 / (L : ℂ) with hrdef
  -- basic facts about s
  have hΛs : Λ s ≠ 0 := by
    by_cases hs0 : s = 0
    · subst hs0
      exact Commons.NumberTheory.Linnik.completedLFunction_zero_ne_zero χ hχ hχprim
    · rw [hΛdef, completedL_eq_gammaFactor_mul_L χ hs0 (by linarith only [hα1, hα2, hsre])]
      exact mul_ne_zero (gammaFactor_ne_zero_of_re_gt_neg_one χ (by linarith only [hα1, hα2, hsre]) hs0) hLs
  have hEven0 : χ.Even → s ≠ 0 := by
    intro hE hs0
    have hN1 : N ≠ 1 := by
      intro h
      exact hχ (by subst h; exact Subsingleton.elim χ 1)
    have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN1)
    rw [hs0] at h
    rw [hE.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff.mpr ⟨0, by simp⟩, div_zero] at h
    exact hLs (by rw [hs0]; exact h)
  have hγan : AnalyticAt ℂ γ s := by
    rw [hγdef]; exact gammaFactor_analyticAt χ (by linarith only [hsre]) hEven0
  have hγne : γ s ≠ 0 := by
    rw [hγdef]; exact gammaFactor_ne_zero' χ (by linarith only [hsre]) hEven0
  obtain ⟨δ, hδpos, hδsep⟩ := zeros_far_from χ hχ hχprim hΛs
  -- good heights
  obtain ⟨c, hc0, hgood⟩ := goodHeight_separated χ hχ hχprim
  have hex : ∀ T : ℝ, ∃ T' : ℝ, 1 ≤ T → T + 1 ≤ T' ∧ T' ≤ T + 2 ∧
      (∀ ρ : ℂ, Λ ρ = 0 → c / Real.log ((N:ℝ) * (T' + 3)) ≤ |ρ.im - T'|) ∧
      (∀ ρ : ℂ, Λ ρ = 0 → c / Real.log ((N:ℝ) * (T' + 3)) ≤ |ρ.im + T'|) := by
    intro T
    by_cases hT : 1 ≤ T
    · obtain ⟨T', h1, h2, h3, h4⟩ := hgood T hT
      exact ⟨T', fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨1, fun hh => absurd hh hT⟩
  choose Tf hTf using hex
  have hTftend : Filter.Tendsto Tf Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ), Filter.eventually_ge_atTop (b - 1)] with T h1 h2
    exact le_trans (by linarith only [h2]) ((hTf T h1).1)
  -- bounds on the entire part
  obtain ⟨CΦ, hCΦpos, hCΦb⟩ := rdcKernel_norm_le_inv_sq hx₀ hB hcont hf2 hBnd hvan hL hsre hασ (le_of_lt hα2)
  have hsub_pole : ∀ u : ℂ, Φ u - r / (u - s) = lapX x₀ f ((s - u) * (L : ℂ)) := by
    intro u; rw [hΦdef, hrdef]; exact rdcKernel_sub_pole f s u
  have hGdiff : Differentiable ℂ (fun u => Φ u - r / (u - s)) := by
    have : (fun u : ℂ => Φ u - r / (u - s)) = fun u : ℂ => lapX x₀ f ((s - u) * (L : ℂ)) := by
      funext u; exact hsub_pole u
    rw [this]
    exact differentiable_lapX_affine hx₀.le hcont s L
  obtain ⟨M0, hM0pos, hM0b⟩ := rdcKernel_entire_part_bound hx₀ hcont hLpos hασ
  -- the divisor sum
  have hΦbd : ∀ u : ℂ, 0 < u.re → u.re < 1 → 2 ≤ ‖u‖ → δ ≤ ‖u - s‖ →
      ‖Φ u‖ ≤ CΦ * (‖s‖/δ + 1)^2 / ‖u‖^2 := by
    intro u h1 h2 h3 h4
    have hus : u ≠ s := by
      intro h; rw [h, sub_self, norm_zero] at h4; linarith only [hδpos, h4]
    have h := hCΦb u (by linarith only [hα1, hα2, h1]) (by linarith only [hα1, h2]) hus
    have h5 : ‖u‖ ≤ (‖s‖/δ + 1) * ‖u - s‖ := by
      have h6 : ‖u‖ ≤ ‖s‖ + ‖u - s‖ := by
        have := norm_add_le (u - s) s
        simpa [sub_add_cancel, add_comm] using this
      have h7 : ‖u - s‖ ≠ 0 := by
        intro h8; rw [h8] at h4; linarith only [hδpos, h4]
      have h8 : ‖s‖ ≤ ‖s‖/δ * ‖u - s‖ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδpos]
        exact mul_le_mul_of_nonneg_left h4 (norm_nonneg s)
      linarith only [h6, h8, hδpos, norm_nonneg (u - s), norm_nonneg s, div_nonneg (norm_nonneg s) hδpos.le]
    rw [hΦdef]
    have hpos1 : (0:ℝ) < ‖u - s‖^2 := by
      have : ‖u - s‖ ≠ 0 := by intro hz; rw [hz] at h4; linarith only [hδpos, h4]
      positivity
    have hpos2 : (0:ℝ) < ‖u‖^2 := pow_pos (by linarith only [hα1, hα2, h3] : (0:ℝ) < ‖u‖) 2
    have h9 : CΦ / ‖u - s‖^2 ≤ CΦ * (‖s‖/δ + 1)^2 / ‖u‖^2 := by
      rw [div_le_div_iff₀ hpos1 hpos2]
      have h10 : ‖u‖^2 ≤ ((‖s‖/δ + 1) * ‖u - s‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg u) h5 2
      have h11 : ((‖s‖/δ + 1) * ‖u - s‖)^2 = (‖s‖/δ + 1)^2 * ‖u - s‖^2 := by ring
      nlinarith only [h10, h11, hCΦpos, hα1, hα2]
    exact le_trans h h9
  obtain ⟨hsumm, hten⟩ := divisorSum_summable_and_tendsto_hole χ hχ hχprim
    (Φ := Φ) (s₀ := s) (A := CΦ * (‖s‖/δ + 1)^2) (δ := δ) (by positivity) hδpos hδsep hΦbd
  -- integrability
  have hIα : Integrable (fun τ : ℝ => logDeriv Lf ((α:ℂ)+(τ:ℂ)*Complex.I) * Φ ((α:ℂ)+(τ:ℂ)*Complex.I)) := by
    rw [hLfdef, hΦdef]
    exact integrable_logDeriv_LFunction_mul_rdc_alpha hx₀ hB hcont hf2 hBnd hvan χ hχ hL hα1 hα2 hασ hsre
  have hIl : Integrable (fun τ : ℝ => logDeriv Lf (((-1/2:ℝ):ℂ)+(τ:ℂ)*Complex.I) * Φ (((-1/2:ℝ):ℂ)+(τ:ℂ)*Complex.I)) := by
    rw [hLfdef, hΦdef]
    exact integrable_logDeriv_LFunction_mul_rdc_left hx₀ hB hcont hf2 hBnd hvan χ hχ hχprim hL hα1 hα2 hασ hsre
  -- horizontal vanishing
  have hTfbig : ∀ᶠ T : ℝ in Filter.atTop, 2 * |s.im| + 2 ≤ |Tf T| := by
    filter_upwards [Filter.eventually_ge_atTop (2 * |s.im| + 2)] with T hT
    have h1 : 1 ≤ T := by linarith only [hT, abs_nonneg s.im, hα1, hα2]
    have h2 : T + 1 ≤ Tf T := (hTf T h1).1
    have h3 : (0:ℝ) ≤ Tf T := by linarith only [abs_nonneg s.im, hα1, hα2, h1, h2]
    rw [abs_of_nonneg h3]
    linarith only [hα1, hα2, hT, h2]
  have hsepE : ∀ᶠ T : ℝ in Filter.atTop, ∀ ρ : ℂ, Λ ρ = 0 →
      c / Real.log ((N:ℝ) * (|Tf T| + 3)) ≤ |ρ.im - Tf T| := by
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with T hT ρ hρ
    have h1 : Tf T ≥ T + 1 := (hTf T hT).1
    have h2 := (hTf T hT).2.2.1 ρ hρ
    rwa [abs_of_nonneg (by linarith only [hα1, hα2, hT, h1] : (0:ℝ) ≤ Tf T)]
  have hsepE' : ∀ᶠ T : ℝ in Filter.atTop, ∀ ρ : ℂ, Λ ρ = 0 →
      c / Real.log ((N:ℝ) * (|Tf T| + 3)) ≤ |ρ.im + Tf T| := by
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with T hT ρ hρ
    have h1 : Tf T ≥ T + 1 := (hTf T hT).1
    have h2 := (hTf T hT).2.2.2 ρ hρ
    rwa [abs_of_nonneg (by linarith only [hα1, hα2, hT, h1] : (0:ℝ) ≤ Tf T)]
  obtain ⟨huv, hdv⟩ := horizontal_rdc_tendsto hx₀ hB hcont hf2 hBnd hvan χ hχ hχprim hL hα1 hα2 hασ hsre
    hc0 hTftend hTfbig hsepE hsepE'
  -- vertical limit
  have hlimrect : Filter.Tendsto (fun T : ℝ => rectInt (((-1/2:ℝ):ℂ) - ((Tf T : ℝ):ℂ) * Complex.I)
      ((α : ℂ) + ((Tf T : ℝ):ℂ) * Complex.I) (fun u => logDeriv Lf u * Φ u)) Filter.atTop
      (nhds (Complex.I * ((∫ τ : ℝ, logDeriv Lf ((α : ℂ) + (τ : ℂ) * Complex.I) * Φ ((α:ℂ)+(τ:ℂ)*Complex.I)) -
        (∫ τ : ℝ, logDeriv Lf (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I) * Φ (((-1/2:ℝ):ℂ)+(τ:ℂ)*Complex.I))))) := by
    have := rectInt_tendsto_vertical_gen_comp (F := fun u => logDeriv Lf u * Φ u)
      (A := (-1/2:ℝ)) (B := α) (by linarith only [hα1, hα2]) hTftend
      (by simpa [hLfdef, hΦdef] using hIα)
      (by simpa [hLfdef, hΦdef] using hIl)
      (by simpa [hLfdef, hΦdef] using huv) (by simpa [hLfdef, hΦdef] using hdv)
    exact this
  -- (8) residue identity at a good height
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (NeZero.one_le (n := N))
  have hπne : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have h : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero h
  -- (8) residue identity at a good height
  have hres : ∀ T : ℝ, max 1 (|s.im| + 1) ≤ T →
      rectInt (((-1/2:ℝ):ℂ) - ((Tf T : ℝ):ℂ) * Complex.I)
        ((α : ℂ) + ((Tf T : ℝ):ℂ) * Complex.I) (fun u => logDeriv Lf u * Φ u)
      = 2 * (Real.pi : ℂ) * Complex.I *
          ((∑ᶠ ρ : ℂ, (if |ρ.im| < Tf T then
              ((analyticOrderNatAt Λ ρ : ℕ) : ℂ) * Φ ρ else 0))
            + logDeriv Lf s * r + (if χ.Even then Φ 0 else 0)) := by
    intro T hT
    have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
    have hTf1 : T + 1 ≤ Tf T := (hTf T hT1).1
    have hTfpos : 0 < Tf T := by linarith only [hα1, hα2, hT1, hTf1]
    have hTfabs : |s.im| < Tf T := by
      have h2 : |s.im| + 1 ≤ T := le_trans (le_max_right _ _) hT
      linarith only [hTf1, h2, hα1, hα2]
    set z : ℂ := (((-1/2:ℝ)):ℂ) - ((Tf T : ℝ):ℂ) * Complex.I with hzdef
    set w : ℂ := ((α:ℝ):ℂ) + ((Tf T : ℝ):ℂ) * Complex.I with hwdef
    have hzre : z.re = (-1/2:ℝ) := by rw [hzdef]; simp
    have hzim : z.im = -(Tf T) := by rw [hzdef]; simp
    have hwre : w.re = α := by rw [hwdef]; simp
    have hwim : w.im = Tf T := by rw [hwdef]; simp
    have hzrlt : z.re < w.re := by rw [hzre, hwre]; linarith only [hα1, hα2]
    have hzimlt : z.im < w.im := by rw [hzim, hwim]; linarith only [hα1, hα2, hT1, hTf1]
    have h0in : z.re < 0 ∧ 0 < w.re ∧ z.im < 0 ∧ 0 < w.im := by
      rw [hzre, hwre, hzim, hwim]
      exact ⟨by norm_num, by linarith only [hα1, hα2], by linarith only [hα1, hα2, hT1, hTf1], by linarith only [hα1, hα2, hT1, hTf1]⟩
    have hs0in : z.re < s.re ∧ s.re < w.re ∧ z.im < s.im ∧ s.im < w.im := by
      rw [hzre, hwre, hzim, hwim]
      exact ⟨by linarith only [hsre], by linarith only [hασ], (abs_lt.mp hTfabs).1, (abs_lt.mp hTfabs).2⟩
    have hins : ∀ ρ : ℂ, Λ ρ = 0 → z.re < ρ.re ∧ ρ.re < w.re := by
      intro ρ hρ
      have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hχprim hρ
      rw [hzre, hwre]
      exact ⟨by linarith only [hstrip.1, hα1, hα2, hstrip], by linarith only [hstrip.2, hα1, hstrip]⟩
    have hnz : ∀ u ∈ rectBoundary z w, Λ u ≠ 0 := by
      intro u hu h0
      rcases hu with ⟨hre, him | him⟩ | ⟨him, hre | hre⟩
      · have h2 := (hTf T hT1).2.2.2 u h0
        have him' : u.im = -(Tf T) := by rw [him, hzim]
        rw [him'] at h2
        rw [show |(-(Tf T)) + Tf T| = 0 by rw [neg_add_cancel, abs_zero]] at h2
        have hlogp : 0 < Real.log ((N:ℝ) * (Tf T + 3)) := by
          apply Real.log_pos; nlinarith only [hN1, hTfpos, hα1, hα2, hT1, hTf1]
        have : 0 < c / Real.log ((N:ℝ) * (Tf T + 3)) := div_pos hc0 hlogp
        linarith only [h2, this]
      · have h2 := (hTf T hT1).2.2.1 u h0
        have him' : u.im = Tf T := by rw [him, hwim]
        rw [him'] at h2
        rw [show |Tf T - Tf T| = 0 by rw [sub_self, abs_zero]] at h2
        have hlogp : 0 < Real.log ((N:ℝ) * (Tf T + 3)) := by
          apply Real.log_pos; nlinarith only [hN1, hTfpos, hα1, hα2, hT1, hTf1]
        have : 0 < c / Real.log ((N:ℝ) * (Tf T + 3)) := div_pos hc0 hlogp
        linarith only [h2, this]
      · have hre' : u.re = (-1/2:ℝ) := by rw [hre, hzre]
        have hu' : u = (((-1/2:ℝ)):ℂ) + (u.im:ℂ)*Complex.I := by
          apply Complex.ext <;> simp [hre']
        rw [hu'] at h0
        exact completedL_ne_zero_of_re_eq_neg_half χ hχ hχprim u.im h0
      · have hre' : u.re = α := by rw [hre, hwre]
        have hu' : u = (α:ℂ) + (u.im:ℂ)*Complex.I := by
          apply Complex.ext <;> simp [hre']
        rw [hu'] at h0
        exact completedL_ne_zero_of_one_lt_re' χ hχ hα1 h0
    have hMb : ∀ u ∈ rectSet z w, ‖Φ u - r / (u - s)‖ ≤ M0 := by
      intro u hu
      rw [hsub_pole u]
      apply hM0b u
      obtain ⟨hre, -⟩ := Complex.mem_reProdIm.mp hu
      rw [Set.uIcc_of_le (le_of_lt hzrlt), hzre, hwre] at hre
      linarith only [hre.2, hre]
    have hne_s : ∀ u ∈ rectBoundary z w, u ≠ s := by
      intro u hu
      exact ne_of_mem_rectBoundary_of_inside hs0in hu
    have hΦdiff_at : ∀ u : ℂ, u ≠ s → DifferentiableAt ℂ Φ u := by
      intro u hu
      have h1 : DifferentiableAt ℂ (fun v => Φ v - r / (v - s)) u := hGdiff u
      have h2 : DifferentiableAt ℂ (fun v => r / (v - s)) u :=
        (differentiableAt_const r).div (differentiableAt_id.sub_const s)
          (by intro h; exact hu (sub_eq_zero.mp h))
      have h3 : DifferentiableAt ℂ (fun v => (Φ v - r/(v-s)) + r/(v-s)) u := h1.add h2
      convert h3 using 1
      funext v; ring
    have hG1 := rectInt_logDeriv_completed_mul_simplePole χ hχ hχprim
      (G := fun u => rdcKernel x₀ L f s u) (s₀ := s) (r := f 0/(L:ℂ))
      (by simpa [hΦdef, hrdef] using hGdiff) hzrlt hzimlt h0in hs0in hΛs hins hnz
      (by simpa [hΦdef, hrdef] using hMb)
    have hG2 := rectInt_logDeriv_gammaFactor_mul_simplePole χ
      (G := fun u => rdcKernel x₀ L f s u) (s₀ := s) (r := f 0/(L:ℂ))
      (by simpa [hΦdef, hrdef] using hGdiff) hγan hγne hzrlt hzimlt
      (by rw [hzre]; norm_num) h0in hs0in (by simpa [hΦdef, hrdef] using hMb)
    -- boundary facts
    have hre1 : ∀ u ∈ rectBoundary z w, -(1:ℝ) < u.re := by
      intro u hu
      have hset := rectBoundary_subset_rectSet hzrlt hzimlt hu
      obtain ⟨hre, -⟩ := Complex.mem_reProdIm.mp hset
      rw [Set.uIcc_of_le (le_of_lt hzrlt), hzre, hwre] at hre
      linarith only [hre.1, hα1, hα2, hre]
    have hne0b : ∀ u ∈ rectBoundary z w, u ≠ 0 := by
      intro u hu h0
      rw [h0] at hu
      rcases hu with ⟨hre, him | him⟩ | ⟨him, hre | hre⟩
      · rw [hzim] at him; simp at him; linarith only [hTfpos, him, hα1, hα2, hT1, hTf1]
      · rw [hwim] at him; simp at him; linarith only [hTfpos, him, hα1, hα2, hT1, hTf1]
      · rw [hzre] at hre; simp only [Complex.zero_re] at hre; norm_num at hre
      · rw [hwre] at hre; simp only [Complex.zero_re] at hre; linarith only [hα1, hα2, hre]
    have hγne_b : ∀ u ∈ rectBoundary z w, γ u ≠ 0 := by
      intro u hu
      rw [hγdef]
      rcases χ.even_or_odd with hE | hO
      · rw [hE.gammaFactor_def]
        exact GammaR_ne_zero_of (hne0b u hu) (hre1 u hu)
      · rw [hO.gammaFactor_def]
        apply Complex.Gammaℝ_ne_zero_of_re_pos
        simp only [Complex.add_re, Complex.one_re]; linarith only [hre1 u hu, hre1, hu]
    have hLfne : ∀ u ∈ rectBoundary z w, Lf u ≠ 0 := by
      intro u hu h0
      have hN1' : N ≠ 1 := by intro h; exact hχ (by subst h; exact Subsingleton.elim χ 1)
      have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ u (Or.inr hN1')
      have h2 : Λ u / γ u = 0 := by rw [← h]; exact h0
      rw [div_eq_zero_iff] at h2
      rcases h2 with h2 | h2
      · exact hnz u hu h2
      · exact hγne_b u hu h2
    have hcontΛ : ∀ u ∈ rectBoundary z w, ContinuousAt (fun v => logDeriv Λ v * Φ v) u := by
      intro u hu
      have hlog : ContinuousAt (fun v => logDeriv Λ v) u := by
        rw [show (fun v => logDeriv Λ v) = fun v => deriv Λ v / Λ v by
          funext x; rw [logDeriv_apply]]
        refine ContinuousAt.div ?_ ?_ (hnz u hu)
        · rw [hΛdef]
          exact ((DirichletCharacter.differentiable_completedLFunction hχ).deriv.continuous).continuousAt
        · rw [hΛdef]
          exact (DirichletCharacter.differentiable_completedLFunction hχ).continuous.continuousAt
      exact hlog.mul ((hΦdiff_at u (hne_s u hu)).continuousAt)
    have hcontγ : ∀ u ∈ rectBoundary z w, ContinuousAt (fun v => logDeriv γ v * Φ v) u := by
      intro u hu
      have hlog : ContinuousAt (fun v => logDeriv γ v) u := by
        rw [show (fun v => logDeriv γ v) = fun v => deriv γ v / γ v by
          funext x; rw [logDeriv_apply]]
        refine ContinuousAt.div ?_ ?_ (hγne_b u hu)
        · exact (((gammaFactor_analyticAt_rect χ (hne0b u hu) (hre1 u hu)).1).deriv).continuousAt
        · exact ((gammaFactor_analyticAt_rect χ (hne0b u hu) (hre1 u hu)).1).continuousAt
      exact hlog.mul ((hΦdiff_at u (hne_s u hu)).continuousAt)
    have hintΛ := intervalIntegrable_of_boundary_continuousAt hcontΛ
    have hintγ := intervalIntegrable_of_boundary_continuousAt hcontγ
    have hsplit : rectInt z w (fun u => logDeriv Lf u * Φ u)
        = rectInt z w (fun u => logDeriv Λ u * Φ u) - rectInt z w (fun u => logDeriv γ u * Φ u) := by
      have h1 : rectInt z w (fun u => logDeriv Λ u * Φ u - logDeriv γ u * Φ u)
          = rectInt z w (fun u => logDeriv Λ u * Φ u) - rectInt z w (fun u => logDeriv γ u * Φ u) :=
        rectInt_sub'' hintΛ.1 hintγ.1 hintΛ.2.1 hintγ.2.1 hintΛ.2.2.1 hintγ.2.2.1
          hintΛ.2.2.2 hintγ.2.2.2
      have h2 : rectInt z w (fun u => logDeriv Lf u * Φ u)
          = rectInt z w (fun u => logDeriv Λ u * Φ u - logDeriv γ u * Φ u) := by
        apply rectInt_congr_boundary'
        intro u hu
        have h := logDeriv_completedL_eq_add χ hχ (hne0b u hu) (hre1 u hu) (hLfne u hu)
        simp only [hΛdef, hγdef, hLfdef]
        rw [h]; ring
      rw [h2, h1]
    have hsum_eq : (∑ᶠ ρ : ℂ, (if z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im then
          ((analyticOrderNatAt Λ ρ : ℕ) : ℂ) * Φ ρ else 0))
        = (∑ᶠ ρ : ℂ, (if |ρ.im| < Tf T then ((analyticOrderNatAt Λ ρ : ℕ) : ℂ) * Φ ρ else 0)) := by
      refine finsum_congr (fun ρ => ?_)
      by_cases hzρ : Λ ρ = 0
      · have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hχprim hzρ
        have hcond : (z.re < ρ.re ∧ ρ.re < w.re ∧ z.im < ρ.im ∧ ρ.im < w.im) ↔ |ρ.im| < Tf T := by
          rw [hzre, hwre, hzim, hwim]
          constructor
          · intro ⟨_, _, h1, h2⟩; exact abs_lt.mpr ⟨h1, h2⟩
          · intro h1
            exact ⟨by linarith only [hstrip.1, hα1, hα2, hstrip], by linarith only [hstrip.2, hα1, hstrip],
              (abs_lt.mp h1).1, (abs_lt.mp h1).2⟩
        exact if_congr hcond rfl rfl
      · have hord : analyticOrderNatAt Λ ρ = 0 := by
          simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hzρ)]
        rw [hord]; simp
    have hLss : logDeriv Λ s = logDeriv γ s + logDeriv Lf s := by
      rw [hΛdef, hγdef, hLfdef]
      exact logDeriv_completedL_eq_add' χ hχ (by linarith only [hsre]) hLs
    rw [hsplit, hG1, hG2, hsum_eq]
    rw [hLss]
    ring
  -- (9) the limit
  have hreslim : Filter.Tendsto (fun T : ℝ => rectInt (((-1/2:ℝ):ℂ) - ((Tf T : ℝ):ℂ) * Complex.I)
      ((α : ℂ) + ((Tf T : ℝ):ℂ) * Complex.I) (fun u => logDeriv Lf u * Φ u)) Filter.atTop
      (nhds (2 * (Real.pi : ℂ) * Complex.I *
        ((∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) * Φ u)
          + logDeriv Lf s * r + (if χ.Even then Φ 0 else 0)))) := by
    have h1 : Filter.Tendsto (fun T : ℝ => (∑ᶠ ρ : ℂ, (if |ρ.im| < Tf T then
        ((analyticOrderNatAt Λ ρ : ℕ) : ℂ) * Φ ρ else 0))) Filter.atTop
        (nhds (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) * Φ u)) :=
      hten.comp hTftend
    have h1' : Filter.Tendsto (fun T : ℝ => (∑ᶠ ρ : ℂ, (if |ρ.im| < Tf T then
        ((analyticOrderNatAt Λ ρ : ℕ) : ℂ) * Φ ρ else 0)) + logDeriv Lf s * r + (if χ.Even then Φ 0 else 0))
        Filter.atTop
        (nhds ((∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) * Φ u)
          + logDeriv Lf s * r + (if χ.Even then Φ 0 else 0))) :=
      (h1.add_const (logDeriv Lf s * r)).add_const (if χ.Even then Φ 0 else 0)
    have h2 : Filter.Tendsto (fun T : ℝ => 2 * (Real.pi : ℂ) * Complex.I *
        ((∑ᶠ ρ : ℂ, (if |ρ.im| < Tf T then ((analyticOrderNatAt Λ ρ : ℕ) : ℂ) * Φ ρ else 0))
          + logDeriv Lf s * r + (if χ.Even then Φ 0 else 0))) Filter.atTop
        (nhds (2 * (Real.pi : ℂ) * Complex.I *
          ((∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) * Φ u)
            + logDeriv Lf s * r + (if χ.Even then Φ 0 else 0)))) :=
      h1'.const_mul (2 * (Real.pi : ℂ) * Complex.I)
    refine h2.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (max 1 (|s.im| + 1))] with T hT
    exact (hres T hT).symm
  have huniq := tendsto_nhds_unique hlimrect hreslim
  have hgoal : (1/(2*(Real.pi:ℂ))) * ((∫ τ : ℝ, logDeriv Lf ((α:ℂ)+(τ:ℂ)*Complex.I) * Φ ((α:ℂ)+(τ:ℂ)*Complex.I))
        - (∫ τ : ℝ, logDeriv Lf (((-1/2:ℝ):ℂ)+(τ:ℂ)*Complex.I) * Φ (((-1/2:ℝ):ℂ)+(τ:ℂ)*Complex.I)))
      = (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) * Φ u)
        + logDeriv Lf s * r + (if χ.Even then Φ 0 else 0) := by
    have h2 : (∫ τ : ℝ, logDeriv Lf ((α:ℂ)+(τ:ℂ)*Complex.I) * Φ ((α:ℂ)+(τ:ℂ)*Complex.I))
        - (∫ τ : ℝ, logDeriv Lf (((-1/2:ℝ):ℂ)+(τ:ℂ)*Complex.I) * Φ (((-1/2:ℝ):ℂ)+(τ:ℂ)*Complex.I))
        = 2 * (Real.pi : ℂ) * ((∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) * Φ u)
          + logDeriv Lf s * r + (if χ.Even then Φ 0 else 0)) := by
      apply mul_left_cancel₀ Complex.I_ne_zero
      rw [huniq]; ring
    rw [show (1/(2*(Real.pi:ℂ))) * ((∫ τ : ℝ, logDeriv Lf ((α:ℂ)+(τ:ℂ)*Complex.I) * Φ ((α:ℂ)+(τ:ℂ)*Complex.I))
        - (∫ τ : ℝ, logDeriv Lf (((-1/2:ℝ):ℂ)+(τ:ℂ)*Complex.I) * Φ (((-1/2:ℝ):ℂ)+(τ:ℂ)*Complex.I)))
        = ((∫ τ : ℝ, logDeriv Lf ((α:ℂ)+(τ:ℂ)*Complex.I) * Φ ((α:ℂ)+(τ:ℂ)*Complex.I))
        - (∫ τ : ℝ, logDeriv Lf (((-1/2:ℝ):ℂ)+(τ:ℂ)*Complex.I) * Φ (((-1/2:ℝ):ℂ)+(τ:ℂ)*Complex.I))) / (2*(Real.pi:ℂ)) by ring]
    rw [div_eq_iff hπne]
    rw [h2]; ring
  rw [hgoal]; ring
end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

/-- Contour-shift identity for the `f(0)`-regularized Laplace kernel
`Φ u = ∫_0^{x₀} e^{-(s-u)Lt} f t dt - f 0/((s-u)L)` with `1 < α < 2` and `-1/2 < s.re < α`
(so the simple pole of `Φ` at `u = s`, of residue `f 0/L`, lies *strictly inside* the rectangle
`[-1/2, α] × [-T,T]`; note `s` is then not a zero of `Λ = completedL χ`):

`Σ'_u div Λ(u) · Φ u = (1/2π)(∫_τ (L'/L)(α+iτ) Φ(α+iτ) dτ - ∫_τ (L'/L)(-1/2+iτ) Φ(-1/2+iτ) dτ)
 - (L'/L)(s) · f 0/L - (if χ.Even then Φ 0 else 0)`.

Route: apply the meromorphic rectangle residue identity (simple pole at `u = s` of residue
`f 0/L`) plus the companion gamma-factor version to the rectangle at good heights `T'`
separating the zeros of `Λ`, then let `T' → ∞` using `rectInt_tendsto_vertical_gen` (horizontal
parts vanish since `Φ(x ± iT) = O(1/T)` uniformly for `x ∈ [-1/2, α]`; use
`Φ u = ((s-u)L)^{-2}(f'(0)-f'(x₀)e^{-(s-u)Lx₀}) + ((s-u)L)^{-2}∫_0^{x₀}e^{-(s-u)Lt}f'' t dt`)
and `divisorSum_summable_and_tendsto` (the divisor sum is absolutely summable since
`‖Φ u‖ ≤ C/(1+‖s-u‖²)` for zeros `u` in the strip).  Splitting `(L'/L) = (Λ'/Λ) - (γ'/γ)`
(valid on both vertical lines) gives `Ia - Il = 2π(Σ'_u div Λ(u) Φ u + (if χ.Even then Φ 0 else 0)
+ (L'/L)(s) f 0/L)`. -/
theorem regularized_divisor_contour_shift_gen {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B)
    {f : ℝ → ℂ} (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {L : ℝ} (hL : 1 < L) {s : ℂ} {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (hασ : s.re < α)
    (hsre : -(1/2 : ℝ) < s.re)
    (hLs : DirichletCharacter.LFunction χ s ≠ 0) :
    (∑' u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) *
        ((∫ t in (0:ℝ)..x₀,
            Complex.exp (-(((s - u) * (L : ℂ)) * (t : ℂ))) * f t)
          - f 0 / ((s - u) * (L : ℂ))))
      = (1 / (2 * (Real.pi : ℂ))) *
          ((∫ τ : ℝ, logDeriv (DirichletCharacter.LFunction χ) ((α : ℂ) + (τ : ℂ) * Complex.I) *
              ((∫ t in (0:ℝ)..x₀,
                  Complex.exp (-(((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
                - f 0 / ((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ))))
           - (∫ τ : ℝ, logDeriv (DirichletCharacter.LFunction χ) (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I) *
              ((∫ t in (0:ℝ)..x₀,
                  Complex.exp (-(((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
                - f 0 / ((s - (((-1/2:ℝ):ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)))))
        - logDeriv (DirichletCharacter.LFunction χ) s * (f 0 / (L : ℂ))
        - (if χ.Even then
            ((∫ t in (0:ℝ)..x₀, Complex.exp (-((s - 0) * (L : ℂ) * (t : ℂ))) * f t)
              - f 0 / ((s - 0) * (L : ℂ)))
           else 0) :=
  rdc_shift_identity hx₀ hB hcont hf2 hBnd hvan χ hχ hχprim hL hα1 hα2 hασ hsre hLs

end Commons.NumberTheory.DirichletCharacter
