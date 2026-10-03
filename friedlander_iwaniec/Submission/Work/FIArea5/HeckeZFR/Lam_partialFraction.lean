/-
# `Submission.Work.FIArea5.HeckeZFR.Lam_partialFraction`

The **Hadamard partial fraction** for an entire function of order `≤ 1`:

for an entire `Λ`, not identically zero, whose circle growth satisfies
`log ‖Λ z‖ ≤ C·R·(log (R+2) + K)` on `‖z‖ = R ≥ 1`, and for any two points
`s, s₁` with `Λ s ≠ 0 ≠ Λ s₁`, the divisor-weighted partial sums

  `Σ_{|u| ≤ R} ord(u)·(1/(s-u) − 1/(s₁-u))`

tend, as `R → ∞`, to the logarithmic-derivative difference `Λ'/Λ(s) − Λ'/Λ(s₁)`.

## Strategy

Writing `Λ = P_T · g_T` on the ball of radius `T` (`factorization_open`), with `P_T` the
canonical product over the zeros `|u| ≤ T` and `g_T` zero-free, the residue identity
(`logDeriv_decompose`) gives, for every `T`,

  `Λ'/Λ(s) − Λ'/Λ(s₁) = Σ_{|u|≤T} ord(u)(1/(s-u) − 1/(s₁-u)) + (g_T'/g_T(s) − g_T'/g_T(s₁))`.

The correction term is bounded by `1024·max M0 1·(‖s‖+‖s₁‖)/T²` (`pf_logDeriv_sub_of_sup`),
where `M0` is a sup bound for `log ‖g_T‖`; at a *good* radius `T ∈ [A,2A]` (no zero within
`(log(A+2)+K+1)⁻²` of the circle) one has `M0 = O(T (log T)²)`, so the correction is
`O((log T)²/T) → 0` and the partial sums converge to the target along the good radii.  The
full family of partial sums is Cauchy (the zero count from Jensen's formula makes
`Σ ord(u)‖u‖^{-2}` convergent), so the limit is the target.

The sub-lemmas are `Lam_zeroCount`, `Lam_goodRadius`, `Lam_cofactorBound`, `Lam_pfConv`
(zero count, good radius, cofactor bound, convergence) and `Lam_factorZero` (reduction to the
case `Λ 0 ≠ 0`).
-/
import Mathlib
import Submission.Commons.NumberTheory.Linnik.logDeriv_circle_residue
import Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect
import Submission.Commons.NumberTheory.Linnik.goodRadius_geometric
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
import Submission.Work.FIArea5.HeckeZFR.Lam_zeroCount
import Submission.Port.LogDerivCompat

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea5.HeckeZFR

open Complex Metric Filter
open scoped Topology Real BigOperators

noncomputable section

/-- `(log (2A+2) + K + 1)² / A → 0` as `A → ∞`. -/
lemma tendsto_logSq_div (K : ℝ) :
    Filter.Tendsto (fun A : ℝ => (Real.log (2 * A + 2) + K + 1) ^ 2 / A)
      Filter.atTop (nhds 0) := by
  -- base: `(log x + K + 1)² / x → 0`
  have hbase : Filter.Tendsto (fun x : ℝ => (Real.log x + K + 1) ^ 2 / x)
      Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun x : ℝ => (Real.log x) ^ 2 / x) Filter.atTop (nhds 0) := by
      have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 (by norm_num : (1 : ℝ) ≠ 0)
      simpa using this
    have h1 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
      have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1 : ℝ) ≠ 0)
      simpa using this
    have h0 : Filter.Tendsto (fun x : ℝ => (1 : ℝ) / x) Filter.atTop (nhds 0) := by
      have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 (by norm_num : (1 : ℝ) ≠ 0)
      simpa using this
    have hsum : Filter.Tendsto
        (fun x : ℝ => (Real.log x) ^ 2 / x + 2 * (K + 1) * (Real.log x / x)
          + (K + 1) ^ 2 * ((1 : ℝ) / x)) Filter.atTop (nhds 0) := by
      have a := h2
      have b : Filter.Tendsto (fun x : ℝ => 2 * (K + 1) * (Real.log x / x)) Filter.atTop (nhds 0) := by
        simpa using ((tendsto_const_nhds (x := 2 * (K + 1))).mul h1)
      have c : Filter.Tendsto (fun x : ℝ => (K + 1) ^ 2 * ((1 : ℝ) / x)) Filter.atTop (nhds 0) := by
        simpa using ((tendsto_const_nhds (x := (K + 1) ^ 2)).mul h0)
      simpa only [add_assoc, zero_add] using (a.add (b.add c))
    refine hsum.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hxne : x ≠ 0 := ne_of_gt hx
    field_simp
    ring
  -- compose with `A ↦ 2A+2`
  have hshift : Filter.Tendsto (fun A : ℝ => 2 * A + 2) Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun A : ℝ => 2 * A) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id
    simpa using (Filter.tendsto_atTop_add_const_right Filter.atTop (2 : ℝ) h1)
  have hcomp := hbase.comp hshift
  have hratio : Filter.Tendsto (fun A : ℝ => (2 * A + 2) / A) Filter.atTop (nhds 2) := by
    have hinv : Filter.Tendsto (fun A : ℝ => A⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
    have h : Filter.Tendsto (fun A : ℝ => 2 + 2 * A⁻¹) Filter.atTop (nhds 2) := by
      simpa using ((tendsto_const_nhds (x := (2 : ℝ))).add
        ((tendsto_const_nhds (x := (2 : ℝ))).mul hinv))
    refine h.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with A hA
    field_simp
  have hprod : Filter.Tendsto
      (fun A : ℝ => ((Real.log (2 * A + 2) + K + 1) ^ 2 / (2 * A + 2)) * ((2 * A + 2) / A))
      Filter.atTop (nhds 0) := by
    have := hcomp.mul hratio
    simpa using this
  refine hprod.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with A hA
  have h2A : (2 : ℝ) * A + 2 ≠ 0 := by positivity
  have hAne : A ≠ 0 := ne_of_gt hA
  field_simp

/-- **Assembly of the partial fraction in the case `Λ 0 ≠ 0`.**  The four analytic inputs
(zero count, good radius, cofactor bound, existence of the limit of the partial sums) are taken
as hypotheses; here they are combined and the limit is identified. -/
theorem Lam_aux_of (Λ : ℂ → ℂ) (hDiff : Differentiable ℂ Λ) (h0 : Λ 0 ≠ 0)
    (C K : ℝ) (hC : 0 < C) (hK : 0 ≤ K)
    (hgrowth : ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, ‖z‖ = R →
      Real.log ‖Λ z‖ ≤ C * R * (Real.log (R + 2) + K))
    (c : ℝ) (hc : 0 ≤ c)
    (hcount : ∀ R : ℝ, 1 ≤ R →
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℝ)) ≤
        c * R * (Real.log (R + 2) + K))
    (hGood : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      ∃ T : ℝ, A ≤ T ∧ T ≤ 2 * A ∧
        ∀ u : ℂ, Λ u = 0 → (Real.log (A + 2) + K + 1) ^ 2 * |‖u‖ - T| ≥ 1)
    (hCof : ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ A T : ℝ, 1 ≤ A → A ≤ T → T ≤ 2 * A →
      (∀ u : ℂ, Λ u = 0 → (Real.log (A + 2) + K + 1) ^ 2 * |‖u‖ - T| ≥ 1) →
      ∃ (g : ℂ → ℂ) (ε M0 : ℝ), 0 < ε ∧ 0 ≤ M0 ∧
        AnalyticOnNhd ℂ g (Metric.ball 0 (T + ε)) ∧
        (∀ w : ℂ, w ∈ Metric.ball 0 (T + ε) → g w ≠ 0) ∧
        (∀ z : ℂ, z ∈ Metric.ball 0 (T + ε) →
          Λ z = (∏ᶠ u : ℂ, (z - u) ^ (MeromorphicOn.divisor Λ (Metric.closedBall 0 T) u)) * g z) ∧
        (∀ w : ℂ, w ∈ Metric.ball 0 T → Real.log ‖g w‖ ≤ M0) ∧
        |Real.log ‖g 0‖| ≤ M0 ∧
        M0 ≤ (C + 4 * c) * T * (Real.log (T + 2) + K + 1) ^ 2 + A₀)
    (hConv : ∀ s s₁ : ℂ, ∃ L : ℂ, Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ)
          * (1 / (s - u) - 1 / (s₁ - u)))) Filter.atTop (nhds L)) :
    ∀ s s₁ : ℂ, Λ s ≠ 0 → Λ s₁ ≠ 0 →
      Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
          (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ)
            * (1 / (s - u) - 1 / (s₁ - u)))
        Filter.atTop (nhds (deriv Λ s / Λ s - deriv Λ s₁ / Λ s₁)) := by
  classical
  intro s s₁ hs hs₁
  set G : ℝ → ℂ := fun R => ∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ)
        * (1 / (s - u) - 1 / (s₁ - u)) with hG
  set tgt : ℂ := deriv Λ s / Λ s - deriv Λ s₁ / Λ s₁ with htgt
  have htgt' : tgt = logDeriv Λ s - logDeriv Λ s₁ := by
    simp only [htgt, logDeriv_apply]
  obtain ⟨L, hL⟩ := hConv s s₁
  have hL' : Filter.Tendsto G Filter.atTop (nhds L) := hL
  obtain ⟨B₀, hB₀1, hB₀⟩ := hGood
  obtain ⟨B₁, hB₁0, hB₁⟩ := hCof
  set α : ℝ := ‖s‖ + ‖s₁‖ with hα
  have hα0 : 0 ≤ α := by simp only [hα]; positivity
  -- the range of good radii
  let Astart : ℝ := max (max B₀ B₁) (max 1 (8 * (α + 1)))
  have hAstB₀ : B₀ ≤ Astart := le_trans (le_max_left B₀ B₁) (le_max_left _ _)
  have hAst1 : 1 ≤ Astart := le_trans (le_max_left 1 (8 * (α + 1))) (le_max_right _ _)
  have hAst8 : 8 * (α + 1) ≤ Astart := le_trans (le_max_right 1 (8 * (α + 1))) (le_max_right _ _)
  have hAst0 : 0 ≤ Astart := le_trans (by norm_num : (0 : ℝ) ≤ 1) hAst1
  have hex : ∀ A : ℝ, Astart ≤ A → ∃ T : ℝ, A ≤ T ∧ T ≤ 2 * A ∧
      ∀ u : ℂ, Λ u = 0 → (Real.log (A + 2) + K + 1) ^ 2 * |‖u‖ - T| ≥ 1 :=
    fun A hA => hB₀ A (le_trans hAstB₀ hA)
  let Tt : ℝ → ℝ := fun A => if h : Astart ≤ A then (hex A h).choose else 1
  have hTt : ∀ A : ℝ, Astart ≤ A → A ≤ Tt A ∧ Tt A ≤ 2 * A ∧
      (∀ u : ℂ, Λ u = 0 → (Real.log (A + 2) + K + 1) ^ 2 * |‖u‖ - Tt A| ≥ 1) := by
    intro A hA
    have := (hex A hA).choose_spec
    simpa only [Tt, dif_pos hA] using this
  have hTt_top : Filter.Tendsto Tt Filter.atTop Filter.atTop := by
    have hev : ∀ᶠ A : ℝ in Filter.atTop, A ≤ Tt A := by
      filter_upwards [Filter.eventually_ge_atTop Astart] with A hA
      exact (hTt A hA).1
    exact tendsto_atTop_mono' Filter.atTop hev tendsto_id
  -- the explicit decay bound
  let E : ℝ → ℝ := fun A => 1024 * ((C + 4 * c) * (2 * A) * (Real.log (2 * A + 2) + K + 1) ^ 2
      + (B₁ + 1)) * α / A ^ 2
  have hE : Filter.Tendsto E Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun A : ℝ => (Real.log (2 * A + 2) + K + 1) ^ 2 / A)
        Filter.atTop (nhds 0) := tendsto_logSq_div K
    have h2 : Filter.Tendsto (fun A : ℝ => (1 : ℝ) / A ^ 2) Filter.atTop (nhds 0) := by
      have hinv : Filter.Tendsto (fun A : ℝ => A⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
      have hmul := hinv.mul hinv
      have heq : (fun A : ℝ => A⁻¹ * A⁻¹) =ᶠ[Filter.atTop] fun A : ℝ => (1 : ℝ) / A ^ 2 := by
        filter_upwards with A
        by_cases hA : A = 0
        · subst hA; simp
        · field_simp
      simpa using (Tendsto.congr' heq hmul)
    have hsum : Filter.Tendsto (fun A : ℝ =>
        2 * (C + 4 * c) * ((Real.log (2 * A + 2) + K + 1) ^ 2 / A) + (B₁ + 1) * ((1 : ℝ) / A ^ 2))
        Filter.atTop (nhds 0) := by
      have hA1 : Filter.Tendsto (fun A : ℝ => 2 * (C + 4 * c) * ((Real.log (2 * A + 2) + K + 1) ^ 2 / A))
          Filter.atTop (nhds 0) := by
        simpa using ((tendsto_const_nhds (x := 2 * (C + 4 * c))).mul h1)
      have hA2 : Filter.Tendsto (fun A : ℝ => (B₁ + 1) * ((1 : ℝ) / A ^ 2)) Filter.atTop (nhds 0) := by
        simpa using ((tendsto_const_nhds (x := B₁ + 1)).mul h2)
      simpa using hA1.add hA2
    have hmain : Filter.Tendsto (fun A : ℝ => 1024 * α *
        (2 * (C + 4 * c) * ((Real.log (2 * A + 2) + K + 1) ^ 2 / A)
          + (B₁ + 1) * ((1 : ℝ) / A ^ 2))) Filter.atTop (nhds 0) := by
      simpa using ((tendsto_const_nhds (x := 1024 * α)).mul hsum)
    refine Tendsto.congr' ?_ hmain
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with A hA
    simp only [E]
    have hAne : A ≠ 0 := ne_of_gt hA
    field_simp
  -- the correction estimate
  have hcorr : ∀ᶠ A : ℝ in Filter.atTop, ‖G (Tt A) - tgt‖ ≤ E A := by
    filter_upwards [Filter.eventually_ge_atTop Astart] with A hA
    obtain ⟨hAle, hTle, hmargin⟩ := hTt A hA
    set T : ℝ := Tt A with hTdef
    have hA1 : 1 ≤ A := le_trans hAst1 hA
    have hA0 : 0 ≤ A := le_trans hAst0 hA
    have hT8 : 8 * (α + 1) ≤ T := le_trans (le_trans hAst8 hA) hAle
    have hTpos : 0 < T := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_trans hA1 hAle)
    have hT0 : 0 ≤ T := le_of_lt hTpos
    have hsT : ‖s‖ ≤ T / 8 := by
      have hsα : ‖s‖ ≤ α := by
        simp only [hα]
        exact le_add_of_nonneg_right (norm_nonneg _)
      nlinarith [hT8]
    have hs₁T : ‖s₁‖ ≤ T / 8 := by
      have hsα : ‖s₁‖ ≤ α := by
        simp only [hα]
        exact le_add_of_nonneg_left (norm_nonneg _)
      nlinarith [hT8]
    obtain ⟨g, ε, M0, hε, hM0nn, hg_an, hg_ne, hfac, hgM, hg0, hM0bd⟩ := hB₁ A T hA1 hAle hTle hmargin
    have hg_an_T : AnalyticOnNhd ℂ g (Metric.ball 0 T) :=
      hg_an.mono (Metric.ball_subset_ball (by linarith))
    have hg_ne_T : ∀ w : ℂ, w ∈ Metric.ball 0 T → g w ≠ 0 :=
      fun w hw => hg_ne w (Metric.ball_subset_ball (by linarith) hw)
    have hs_ball : s ∈ Metric.ball 0 (T + ε) := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      have : ‖s‖ < T + ε := by nlinarith [hsT, hTpos]
      linarith
    have hs₁_ball : s₁ ∈ Metric.ball 0 (T + ε) := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      have : ‖s₁‖ < T + ε := by nlinarith [hs₁T, hTpos]
      linarith
    have hdec_s := Commons.NumberTheory.Linnik.logDeriv_decompose (f := Λ) (g := g) (R := T) (ε := ε)
      hDiff hfac hs_ball hs ((hg_an s hs_ball).differentiableAt) (hg_ne s hs_ball)
    have hdec_s₁ := Commons.NumberTheory.Linnik.logDeriv_decompose (f := Λ) (g := g) (R := T) (ε := ε)
      hDiff hfac hs₁_ball hs₁ ((hg_an s₁ hs₁_ball).differentiableAt) (hg_ne s₁ hs₁_ball)
    -- the finsum split into the two kernels
    have hsplit : G T =
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 T)) u : ℤ) : ℂ) * (1 / (s - u)))
        - (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 T)) u : ℤ) : ℂ) * (1 / (s₁ - u))) := by
      simp only [hG]
      rw [show (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 T)) u : ℤ) : ℂ)
              * (1 / (s - u) - 1 / (s₁ - u)))
            = ∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 T)) u : ℤ) : ℂ) * (1 / (s - u))
                - (((MeromorphicOn.divisor Λ (Metric.closedBall 0 T)) u : ℤ) : ℂ) * (1 / (s₁ - u)))
          from finsum_congr (fun u => by ring)]
      rw [finsum_sub_distrib]
      · exact (MeromorphicOn.divisor Λ (Metric.closedBall 0 T)).finiteSupport (isCompact_closedBall 0 T) |>.subset
          (fun u hu => by
            rw [Function.mem_support] at hu ⊢
            intro hd
            exact hu (by simp [hd]))
      · exact (MeromorphicOn.divisor Λ (Metric.closedBall 0 T)).finiteSupport (isCompact_closedBall 0 T) |>.subset
          (fun u hu => by
            rw [Function.mem_support] at hu ⊢
            intro hd
            exact hu (by simp [hd]))
    have hGdecomp : G T - (logDeriv Λ s - logDeriv Λ s₁) = -(logDeriv g s - logDeriv g s₁) := by
      rw [hsplit, hdec_s, hdec_s₁]; ring
    have hbd_s := Commons.NumberTheory.Linnik.pf_logDeriv_sub_of_sup (g := g) (R := T) hTpos
      hg_an_T hg_ne_T hM0nn hgM hg0 hsT
    have hbd_s₁ := Commons.NumberTheory.Linnik.pf_logDeriv_sub_of_sup (g := g) (R := T) hTpos
      hg_an_T hg_ne_T hM0nn hgM hg0 hs₁T
    have hbd_s₁' : ‖logDeriv g 0 - logDeriv g s₁‖ ≤ 1024 * max M0 1 * ‖s₁‖ / T ^ 2 := by
      rw [norm_sub_rev]; exact hbd_s₁
    have hcorr1 : ‖logDeriv g s - logDeriv g s₁‖ ≤ 1024 * max M0 1 * α / T ^ 2 := by
      have he : logDeriv g s - logDeriv g s₁
          = (logDeriv g s - logDeriv g 0) + (logDeriv g 0 - logDeriv g s₁) := by ring
      have h1 : ‖logDeriv g s - logDeriv g s₁‖
          ≤ ‖logDeriv g s - logDeriv g 0‖ + ‖logDeriv g 0 - logDeriv g s₁‖ := by
        rw [he]; exact norm_add_le _ _
      have h2 := add_le_add hbd_s hbd_s₁'
      have h3 : 1024 * max M0 1 * ‖s‖ / T ^ 2 + 1024 * max M0 1 * ‖s₁‖ / T ^ 2
          = 1024 * max M0 1 * α / T ^ 2 := by
        rw [hα]; ring
      linarith [le_trans h1 h2, h3]
    -- bound `max M0 1` by the explicit quantity of `E`
    have hLTpos : 0 < Real.log (T + 2) + K + 1 := by
      have : 0 < Real.log (T + 2) := Real.log_pos (by linarith)
      linarith
    have hLT0 : 0 ≤ Real.log (T + 2) + K + 1 := le_of_lt hLTpos
    have hLTle : Real.log (T + 2) + K + 1 ≤ Real.log (2 * A + 2) + K + 1 := by
      have h1 : Real.log (T + 2) ≤ Real.log (2 * A + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      linarith
    have hC4c : 0 < C + 4 * c := by linarith
    have hMbig0 : 0 ≤ (C + 4 * c) * (2 * A) * (Real.log (2 * A + 2) + K + 1) ^ 2 + (B₁ + 1) := by
      have h1 : 0 ≤ (C + 4 * c) * (2 * A) * (Real.log (2 * A + 2) + K + 1) ^ 2 := by positivity
      linarith
    have hM0big : M0 ≤ (C + 4 * c) * (2 * A) * (Real.log (2 * A + 2) + K + 1) ^ 2 + (B₁ + 1) := by
      have h1 : (C + 4 * c) * T * (Real.log (T + 2) + K + 1) ^ 2 ≤
          (C + 4 * c) * (2 * A) * (Real.log (2 * A + 2) + K + 1) ^ 2 := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left hTle; positivity
        · exact pow_le_pow_left₀ hLT0 hLTle 2
        · positivity
        · positivity
      linarith [hM0bd, h1]
    have hM01big : max M0 1 ≤ (C + 4 * c) * (2 * A) * (Real.log (2 * A + 2) + K + 1) ^ 2 + (B₁ + 1) := by
      apply max_le hM0big
      have h1 : 0 ≤ (C + 4 * c) * (2 * A) * (Real.log (2 * A + 2) + K + 1) ^ 2 := by positivity
      linarith
    have hcorr2 : ‖logDeriv g s - logDeriv g s₁‖ ≤ E A := by
      have hA2T2 : A ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hA0 hAle 2
      refine le_trans hcorr1 ?_
      show 1024 * max M0 1 * α / T ^ 2 ≤ 1024 * ((C + 4 * c) * (2 * A)
        * (Real.log (2 * A + 2) + K + 1) ^ 2 + (B₁ + 1)) * α / A ^ 2
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < T ^ 2) (by positivity : (0 : ℝ) < A ^ 2)]
      have hstep1 : 1024 * max M0 1 * α * A ^ 2
          ≤ 1024 * ((C + 4 * c) * (2 * A) * (Real.log (2 * A + 2) + K + 1) ^ 2 + (B₁ + 1)) * α * A ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM01big (by norm_num)) hα0
      have hstep2 : 1024 * ((C + 4 * c) * (2 * A) * (Real.log (2 * A + 2) + K + 1) ^ 2 + (B₁ + 1)) * α * A ^ 2
          ≤ 1024 * ((C + 4 * c) * (2 * A) * (Real.log (2 * A + 2) + K + 1) ^ 2 + (B₁ + 1)) * α * T ^ 2 := by
        apply mul_le_mul_of_nonneg_left hA2T2
        exact mul_nonneg (mul_nonneg (by norm_num) hMbig0) hα0
      exact le_trans hstep1 hstep2
    show ‖G T - tgt‖ ≤ E A
    calc ‖G T - tgt‖ = ‖logDeriv g s - logDeriv g s₁‖ := by
            rw [htgt', hGdecomp, norm_neg]
      _ ≤ E A := hcorr2
  -- the limit along good radii
  have hnorm : Filter.Tendsto (fun A : ℝ => ‖G (Tt A) - tgt‖) Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hE
      (Filter.Eventually.of_forall (fun A => norm_nonneg _)) hcorr
  have hsub : Filter.Tendsto (fun A : ℝ => G (Tt A) - tgt) Filter.atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hfinal : Filter.Tendsto (fun A : ℝ => G (Tt A)) Filter.atTop (nhds tgt) := by
    have h := hsub.add (tendsto_const_nhds (x := tgt))
    simpa only [sub_add_cancel, zero_add] using h
  have hcomp : Filter.Tendsto (fun A : ℝ => G (Tt A)) Filter.atTop (nhds L) := hL'.comp hTt_top
  have hLeq : L = tgt := tendsto_nhds_unique hcomp hfinal
  have hmain : Filter.Tendsto G Filter.atTop (nhds tgt) := by rw [← hLeq]; exact hL'
  simpa only [hG, htgt] using hmain

/-- **Reduction to the case `Λ 0 ≠ 0`.**  If `Λ = z^k · φ` with `φ` entire and `φ 0 ≠ 0`, and the
partial fraction is known for `φ`, then it holds for `Λ`: the only new divisor contribution is the
`k`-fold zero at the origin, which matches the extra term `k/s` of the logarithmic derivative of
`z ↦ z^k`. -/
theorem Lam_reduce_of (Λ φ : ℂ → ℂ) (k : ℕ)
    (hφdiff : Differentiable ℂ φ) (hφ0 : φ 0 ≠ 0)
    (hfac : ∀ z : ℂ, Λ z = z ^ k * φ z)
    (hdiv0 : ∀ R : ℝ, 1 ≤ R → (MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) 0 = (k : ℤ))
    (hdivne : ∀ (R : ℝ) (u : ℂ), u ≠ 0 →
      (MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u =
        (MeromorphicOn.divisor φ (Metric.closedBall 0 R)) u)
    (hφpf : ∀ s s₁ : ℂ, φ s ≠ 0 → φ s₁ ≠ 0 →
      Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        ((((MeromorphicOn.divisor φ (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₁ - u))))
        Filter.atTop (nhds (deriv φ s / φ s - deriv φ s₁ / φ s₁))) :
    ∀ s s₁ : ℂ, Λ s ≠ 0 → Λ s₁ ≠ 0 →
      Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        ((((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₁ - u))))
        Filter.atTop (nhds (deriv Λ s / Λ s - deriv Λ s₁ / Λ s₁)) := by
  classical
  intro s s₁ hs hs₁
  set w : ℂ → ℂ := fun u => 1 / (s - u) - 1 / (s₁ - u) with hw
  have hφs : φ s ≠ 0 := fun h => hs (by rw [hfac s, h, mul_zero])
  have hφs₁ : φ s₁ ≠ 0 := fun h => hs₁ (by rw [hfac s₁, h, mul_zero])
  have hφlim := hφpf s s₁ hφs hφs₁
  -- finite supports
  have hfinΛ : ∀ R : ℝ, Function.HasFiniteSupport
      (fun u : ℂ => (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ) * w u) :=
    fun R => (MeromorphicOn.divisor Λ (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)
      |>.subset (fun u hu => by
        rw [Function.mem_support] at hu ⊢
        intro hd
        exact hu (by simp [hd]))
  have hfinφ : ∀ R : ℝ, Function.HasFiniteSupport
      (fun u : ℂ => (((MeromorphicOn.divisor φ (Metric.closedBall 0 R)) u : ℤ) : ℂ) * w u) :=
    fun R => (MeromorphicOn.divisor φ (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)
      |>.subset (fun u hu => by
        rw [Function.mem_support] at hu ⊢
        intro hd
        exact hu (by simp [hd]))
  -- the divisor of `φ` at `0` vanishes
  have hdivφ0 : ∀ R : ℝ, 0 ≤ R → (MeromorphicOn.divisor φ (Metric.closedBall 0 R)) 0 = 0 := by
    intro R hR
    have hφanB : AnalyticOnNhd ℂ φ (Metric.closedBall 0 R) := fun z _ => hφdiff.analyticAt z
    rw [MeromorphicOn.divisor_apply hφanB.meromorphicOn (Metric.mem_closedBall_self hR)]
    rw [Commons.Analysis.Complex.meromorphicOrderAt_eq_zero_of_ne_zero (hφdiff.analyticAt 0) hφ0]
    simp
  -- eventual identification of the two divisor sums
  have hEq : (fun R : ℝ => ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ) * w u) =ᶠ[Filter.atTop]
      fun R : ℝ => (∑ᶠ u : ℂ,
          (((MeromorphicOn.divisor φ (Metric.closedBall 0 R)) u : ℤ) : ℂ) * w u)
            + (k : ℂ) * w 0 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR
    have hdelta : Function.HasFiniteSupport (fun u : ℂ => if u = 0 then (k : ℂ) * w 0 else 0) :=
      (Set.finite_singleton (0 : ℂ)).subset (fun u hu => by
        rw [Function.mem_support] at hu
        simp only [Set.mem_singleton_iff]
        by_contra h
        exact hu (by simp [h]))
    have key : (fun u : ℂ => (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ) * w u)
        = fun u : ℂ => (((MeromorphicOn.divisor φ (Metric.closedBall 0 R)) u : ℤ) : ℂ) * w u
            + (if u = 0 then (k : ℂ) * w 0 else 0) := by
      funext u
      by_cases hu : u = 0
      · subst hu
        rw [hdiv0 R hR, hdivφ0 R (by linarith)]
        simp
      · rw [hdivne R u hu]
        simp [hu]
    rw [key, finsum_add_distrib (hfinφ R) hdelta]
    congr 1
    rw [finsum_eq_single (fun u : ℂ => if u = 0 then (k : ℂ) * w 0 else 0) 0
      (fun u hu => by simp [hu])]
    simp
  -- push the limit through
  have hpush : Filter.Tendsto (fun R : ℝ => (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor φ (Metric.closedBall 0 R)) u : ℤ) : ℂ) * w u)
          + (k : ℂ) * w 0) Filter.atTop
      (nhds (deriv φ s / φ s - deriv φ s₁ / φ s₁ + (k : ℂ) * w 0)) := by
    have := hφlim.add (tendsto_const_nhds (x := (k : ℂ) * w 0))
    simpa only [hw] using this
  have hlim : Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R)) u : ℤ) : ℂ) * w u) Filter.atTop
      (nhds (deriv φ s / φ s - deriv φ s₁ / φ s₁ + (k : ℂ) * w 0)) :=
    Tendsto.congr' hEq.symm hpush
  -- identify the target
  have hlogΛ_s : logDeriv Λ s = (k : ℂ) * (1 / s) + logDeriv φ s := by
    have hfun : Λ = fun z : ℂ => z ^ k * φ z := funext hfac
    rw [hfun, Submission.Port.logDeriv_mul_fun s _ hφs (by fun_prop) (hφdiff.differentiableAt)]
    · congr 1
      rw [logDeriv_fun_pow differentiableAt_id k, logDeriv_apply]
      simp
    · intro h
      exact hs (by rw [hfac s, h, zero_mul])
  have hlogΛ_s₁ : logDeriv Λ s₁ = (k : ℂ) * (1 / s₁) + logDeriv φ s₁ := by
    have hfun : Λ = fun z : ℂ => z ^ k * φ z := funext hfac
    rw [hfun, Submission.Port.logDeriv_mul_fun s₁ _ hφs₁ (by fun_prop) (hφdiff.differentiableAt)]
    · congr 1
      rw [logDeriv_fun_pow differentiableAt_id k, logDeriv_apply]
      simp
    · intro h
      exact hs₁ (by rw [hfac s₁, h, zero_mul])
  have hval : deriv Λ s / Λ s - deriv Λ s₁ / Λ s₁
      = (deriv φ s / φ s - deriv φ s₁ / φ s₁) + (k : ℂ) * w 0 := by
    have hlog : logDeriv Λ s - logDeriv Λ s₁
        = (logDeriv φ s - logDeriv φ s₁) + (k : ℂ) * w 0 := by
      rw [hlogΛ_s, hlogΛ_s₁, hw]
      simp only [sub_zero]
      ring
    simpa only [logDeriv_apply] using hlog
  rw [hval]
  simpa only [hw] using hlim

end

end Work.FIArea5.HeckeZFR
