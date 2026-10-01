import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l63
import Submission.Work.NumberTheory.Linnik.scratch_ws13
import Submission.Work.NumberTheory.Linnik.scratch_ws15
import Submission.Work.NumberTheory.Linnik.scratch_hzero2
import Submission.Work.NumberTheory.Linnik.scratch_far2real
import Submission.Work.NumberTheory.Linnik.scratch_far
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity
import Submission.Work.NumberTheory.Linnik.scratch_imprim
import Submission.Work.NumberTheory.Linnik.scratch_thresh

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory
open scoped Real Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.Linnik

/-- First derivative of the complexification of a real function. -/
theorem deriv_ofReal_comp (g : ℝ → ℝ) (x : ℝ) :
    deriv (fun t : ℝ => ((g t : ℝ) : ℂ)) x = ((deriv g x : ℝ) : ℂ) := by
  by_cases h : DifferentiableAt ℝ g x
  · exact h.hasDerivAt.ofReal_comp.deriv
  · have h2 : ¬ DifferentiableAt ℝ (fun t : ℝ => ((g t : ℝ) : ℂ)) x := by
      intro hc
      exact h (Complex.reCLM.differentiableAt.comp x hc)
    rw [deriv_zero_of_not_differentiableAt h2, deriv_zero_of_not_differentiableAt h]
    simp

/-- The `n`-th derivative of the complexification of a real function. -/
theorem iteratedDeriv_ofReal_comp (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun t : ℝ => ((f t : ℝ) : ℂ)) x = ((iteratedDeriv n f x : ℝ) : ℂ) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    rw [show iteratedDeriv n (fun t : ℝ => ((f t : ℝ) : ℂ)) =
        (fun t : ℝ => ((iteratedDeriv n f t : ℝ) : ℂ)) from funext ih]
    exact deriv_ofReal_comp _ x

/-- Smoothness of the complexification of a real function. -/
theorem contDiffOn_ofReal_comp {f : ℝ → ℝ} {n : ℕ∞} {s : Set ℝ} (hf : ContDiffOn ℝ n f s) :
    ContDiffOn ℝ n (fun t : ℝ => ((f t : ℝ) : ℂ)) s :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn hf

/-- The divisor of an analytic function on closed balls is independent of the radius, as long as the
point stays inside. -/
theorem divisor_closedBall_congr {F : ℂ → ℂ} (hF : ∀ z, AnalyticAt ℂ F z)
    {R₁ R₂ : ℝ} {z : ℂ} (h₁ : z ∈ Metric.closedBall 0 R₁) (h₂ : z ∈ Metric.closedBall 0 R₂) :
    (MeromorphicOn.divisor F (Metric.closedBall 0 R₁)) z
      = (MeromorphicOn.divisor F (Metric.closedBall 0 R₂)) z := by
  rw [MeromorphicOn.divisor_apply (f := F) (U := Metric.closedBall 0 R₁) (fun w _ => (hF w).meromorphicAt) h₁,
      MeromorphicOn.divisor_apply (f := F) (U := Metric.closedBall 0 R₂) (fun w _ => (hF w).meromorphicAt) h₂]

/-- A zero of positive order of `completedLFunction χ` (for `χ` non-principal) with positive real
part is a zero of `LFunction χ`. -/
theorem LFunction_eq_zero_of_divisor_completedL_ne_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {a u : ℂ} {ρ : ℝ}
    (hu : u ∈ Metric.closedBall a ρ) (hure : 0 < u.re)
    (hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall a ρ)) u ≠ 0) :
    DirichletCharacter.LFunction χ u = 0 := by
  have hgf : DirichletCharacter.gammaFactor χ u ≠ 0 := by
    have key : ∀ z : ℂ, 0 < z.re → z.Gammaℝ ≠ 0 := by
      intro z hz h0
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h0
      rw [hn] at hz
      have hre : ((-(2 * (n : ℂ)) : ℂ)).re = -(2 * (n : ℝ)) := by simp
      rw [hre] at hz
      have h2 : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
      linarith
    unfold DirichletCharacter.gammaFactor
    split_ifs with h
    · exact key u hure
    · exact key (u + 1) (by rw [Complex.add_re, Complex.one_re]; linarith)
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall a ρ) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  have hcast : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall a ρ)) u =
      ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℕ) : ℤ) :=
    Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hu
  have hnat : analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u ≠ 0 := by
    intro h0
    exact hdiv (by rw [hcast, h0]; rfl)
  have hz0 : DirichletCharacter.completedLFunction χ u = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero hnat
  have hune : u ≠ 0 := fun h => by rw [h] at hure; simp at hure
  have h0 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ u (Or.inl hune)
  have hprod : DirichletCharacter.completedLFunction χ u =
      DirichletCharacter.LFunction χ u * DirichletCharacter.gammaFactor χ u := by
    rw [h0, div_eq_mul_inv, inv_mul_cancel_right₀ hgf]
  rw [hz0] at hprod
  exact (mul_eq_zero.mp hprod.symm).resolve_right hgf

/-- **Heath-Brown Lemma 6.3**, unconditional form (§6).

For a **real** character `χ` (`χ * χ = 1`), a simple zero `ρ₁ = β₁` and a further zero
`ρ' = β' + iγ' ≠ ρ₁` of `L(·,χ*)` (`χ*` the primitive character inducing `χ`), condition 2 on `f`
and the Lemma-3.1 hypothesis `L52Hyp χ c ε δ`, one has

`2F(-λ') - 2F(λ₁-λ') - F(0) + f(0)(2c + 4ε) ≥ 0`,

where `λ = L(1-β)`, `L = log q`.  The two window hypotheses (6.13)/(6.14) of `lemma6_3` are here
discharged from the maximality of `ρ'`, the rectangle bounds and the far-decay estimate. -/
theorem lemma6_3_full (x₀ B : ℝ) (c : ℝ) (hx₀ : 0 < x₀) (hB : 0 ≤ B) :
    ∀ {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
      (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
      (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) (hf0 : 0 < f 0)
      (hfnn : ∀ t : ℝ, 0 ≤ f t)
      (hFnn : ∀ z : ℂ, 0 ≤ z.re →
        0 ≤ (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * ((f t : ℝ) : ℂ)).re)
      {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1),
      ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q →
      ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hreal : χ * χ = 1) [NeZero χ.conductor]
        {β₁ β' γ' : ℝ}
        (hβ₁ : |1 - β₁| ≤ δ) (hβ' : |1 - β'| ≤ δ) (hβ'β₁ : β' ≤ β₁)
        (hβ₁le : β₁ ≤ 1) (hβ'le : β' ≤ 1)
        (hγ' : |γ'| ≤ Real.log (q : ℝ))
        (hδle : δ ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ))
        (hdiv₁ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|γ'| + 2))) (β₁ : ℂ) ≠ 0)
        (hdiv' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|γ'| + 2))) ((β' : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0)
        (hne : ((β' : ℂ) + (γ' : ℂ) * Complex.I) ≠ (β₁ : ℂ))
        (hmult₁ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|γ'| + 2))) (β₁ : ℂ) = 1)
        (hmax : ∀ u : ℂ, DirichletCharacter.LFunction χ.primitiveCharacter u = 0 →
            |u.im| ≤ 10 * Real.log (q : ℝ) → u = (β₁ : ℂ) ∨ u.re ≤ β')
        (hrect₁ : Real.log (q : ℝ) * (1 - β₁) ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3)
        (hrect' : Real.log (q : ℝ) * (1 - β') ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3)
        (H : L52Hyp χ c ε δ),
      0 ≤ 2 * (∫ t in (0:ℝ)..x₀,
            Real.exp ((Real.log (q : ℝ) * (1 - β')) * t) * f t)
        - 2 * (∫ t in (0:ℝ)..x₀,
            Real.exp (-((Real.log (q : ℝ) * (1 - β₁)) - (Real.log (q : ℝ) * (1 - β'))) * t) * f t)
        - (∫ t in (0:ℝ)..x₀, f t)
        + f 0 * (2 * c + 4 * ε) := by
  intro f hcont hsupp hf2 hBnd hf0 hfnn hFnn ε hε δ hδ0 hδ1
  -- the far-decay threshold
  obtain ⟨Lfar, hLfar1, hfar⟩ := far_term_le_real (x₀ := x₀) (B := B) (δ := δ) hx₀ hB hδ0
    (hcont.mono Set.Icc_subset_Ici_self) (contDiffOn_ofReal_comp hf2)
    (fun t ht => by rw [iteratedDeriv_ofReal_comp]; exact_mod_cast hBnd t ht)
    (fun t ht => hsupp t ht) (ε := f 0 * ε) (mul_pos hf0 hε)
  -- the threshold making `loglog L ≤ (3δ/2) L`
  obtain ⟨Lthr, hLthr1, hthr⟩ := exists_loglog_le_mul (c := 3 * δ / 2) (by positivity)
  obtain ⟨q₀, hq₀⟩ := lemma6_3 x₀ B c hx₀ hB (f := f) hcont hsupp hf2 hBnd hf0 hfnn hFnn hε hδ0 hδ1
  refine ⟨max (max (max q₀ 3) (Nat.ceil (Real.exp Lfar) + 1))
      (Nat.ceil (Real.exp Lthr) + 1), ?_⟩
  intro q _inst hq χ hχ hreal _ic β₁ β' γ' hβ₁ hβ' hβ'β₁ hβ₁le hβ'le hγ' hδle
    hdiv₁ hdiv' hne hmult₁ hmax hrect₁ hrect' H
  have hqq₀ : q₀ ≤ q := by omega
  have hq3 : 3 ≤ q := by omega
  have hqfar : Nat.ceil (Real.exp Lfar) + 1 ≤ q := by omega
  have hqthr : Nat.ceil (Real.exp Lthr) + 1 ≤ q := by omega
  have hqpos : 0 < q := by omega
  have hlogq : (0 : ℝ) < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hLnn : (0 : ℝ) ≤ Real.log (q : ℝ) := le_of_lt hlogq
  have hlogq1 : (1 : ℝ) ≤ Real.log (q : ℝ) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    linarith [Real.exp_one_lt_three]
  have hLfar_le : Lfar ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp Lfar]
    refine Real.log_le_log (Real.exp_pos Lfar) ?_
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast (by omega : Nat.ceil (Real.exp Lfar) ≤ q)
  have hLthr_le : Lthr ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp Lthr]
    refine Real.log_le_log (Real.exp_pos Lthr) ?_
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast (by omega : Nat.ceil (Real.exp Lthr) ≤ q)
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hβ₁lo : 1 - δ ≤ β₁ := by have := (abs_le.mp hβ₁).2; linarith
  have hβ₁hi : β₁ ≤ 1 + δ := by have := (abs_le.mp hβ₁).1; linarith
  have hβ'lo : 1 - δ ≤ β' := by have := (abs_le.mp hβ').2; linarith
  have hβ'hi : β' ≤ 1 + δ := by have := (abs_le.mp hβ').1; linarith
  have hβ₁pos : 0 < β₁ := by linarith
  have hβ'pos : 0 < β' := by linarith
  have himρ : (((β' : ℂ) + (γ' : ℂ) * Complex.I)).im = γ' := by simp
  have hmem₂ : (β₁ : ℂ) ∈ Metric.closedBall (0 : ℂ) (|((β' : ℂ)).im| + 2) := by
    have him0 : ((β' : ℂ)).im = 0 := by simp
    rw [Metric.mem_closedBall, dist_zero_right, him0, abs_zero, zero_add,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith, by linarith⟩
  have hmemR : (β₁ : ℂ) ∈ Metric.closedBall (0 : ℂ) (|γ'| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [abs_nonneg γ'], by linarith [abs_nonneg γ']⟩
  have han : ∀ z : ℂ, AnalyticAt ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter) z :=
    fun z => (DirichletCharacter.differentiable_completedLFunction hχ').analyticAt z
  have hdiv₁₂ : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) (β₁ : ℂ) ≠ 0 := by
    have heq : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) (β₁ : ℂ)
        = (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|γ'| + 2))) (β₁ : ℂ) :=
      divisor_closedBall_congr han hmem₂ hmemR
    intro h0
    exact hdiv₁ (by rw [← heq]; exact h0)
  have hmemρ : ((β' : ℂ) + (γ' : ℂ) * Complex.I) ∈ Metric.closedBall (0 : ℂ) (|γ'| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖(β' : ℂ) + (γ' : ℂ) * Complex.I‖
        ≤ ‖(β' : ℂ)‖ + ‖(γ' : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |β'| + |γ'| := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |γ'| + 2 := by
          have h2 : |β'| ≤ 2 := by
            rw [abs_le]; exact ⟨by linarith, by linarith⟩
          linarith [abs_nonneg γ']
  have hzero₁' : DirichletCharacter.LFunction χ.primitiveCharacter (β₁ : ℂ) = 0 :=
    LFunction_eq_zero_of_divisor_completedL_ne_zero
      χ.primitiveCharacter hχ' (a := 0) (ρ := |γ'| + 2) hmemR (by simpa using hβ₁pos) hdiv₁
  have hzero₁ : DirichletCharacter.LFunction χ (β₁ : ℂ) = 0 := by
    simp only [Commons.NumberTheory.DirichletCharacter.LFunction_eq_primitiveCharacter_mul χ hχ,
      hzero₁', zero_mul]
  have hzero'' : DirichletCharacter.LFunction χ.primitiveCharacter
      ((β' : ℂ) + (γ' : ℂ) * Complex.I) = 0 :=
    LFunction_eq_zero_of_divisor_completedL_ne_zero
      χ.primitiveCharacter hχ' (a := 0) (ρ := |γ'| + 2) hmemρ (by simpa using hβ'pos) hdiv'
  have hzero' : DirichletCharacter.LFunction χ ((β' : ℂ) + (γ' : ℂ) * Complex.I) = 0 := by
    simp only [Commons.NumberTheory.DirichletCharacter.LFunction_eq_primitiveCharacter_mul χ hχ,
      hzero'', zero_mul]
  have hwin10₁ : |((β' : ℂ)).im| + δ ≤ 10 * Real.log (q : ℝ) := by
    have him0 : ((β' : ℂ)).im = 0 := by simp
    rw [him0, abs_zero, zero_add]
    linarith
  have hwin10' : |(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + δ ≤ 10 * Real.log (q : ℝ) := by
    rw [himρ]
    linarith
  have hzw1 : ∀ u : ℂ, (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|((β' : ℂ)).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - u‖ ≤ δ → u ≠ (β₁ : ℂ) → u.re ≤ β' := by
    intro u hu hw hne'
    have h := window_hzero_of_Lzero' χ.primitiveCharacter hχ' (L := Real.log (q : ℝ))
      (A := β') (δ := δ) (s := (β' : ℂ)) (σ := (β₁ : ℂ)) hδ1 hwin10₁ (le_of_eq rfl) hmax
    simpa using h u hu hw hne'
  have hzw2 : ∀ u : ℂ, (MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2))) u ≠ 0 →
      ‖(1:ℂ) + ((((β' : ℂ) + (γ' : ℂ) * Complex.I)).im : ℂ) * Complex.I - u‖ ≤ δ →
      u ≠ ((β' : ℂ) + (γ' : ℂ) * Complex.I) → u ≠ (β₁ : ℂ) → u.re ≤ β' := by
    intro u hu hw _ hne'
    have h := window_hzero_of_Lzero' χ.primitiveCharacter hχ' (L := Real.log (q : ℝ))
      (A := β') (δ := δ) (s := ((β' : ℂ) + (γ' : ℂ) * Complex.I)) (σ := (β₁ : ℂ))
      hδ1 hwin10' (by simp) hmax
    simpa [himρ] using h u hu hw hne'
  have hfnn' : ∀ t ∈ Set.Icc (0:ℝ) x₀, 0 ≤ f t := fun t _ => hfnn t
  have hRρ : |(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2 = |γ'| + 2 := by rw [himρ]
  have hdiv₁q : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2))) (β₁ : ℂ) ≠ 0 := by
    rw [hRρ]; exact hdiv₁
  have hdivq : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2)))
      ((β' : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0 := by
    rw [hRρ]; exact hdiv'
  have hmult₁q : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall 0 (|(((β' : ℂ) + (γ' : ℂ) * Complex.I)).im| + 2))) (β₁ : ℂ) = 1 := by
    rw [hRρ]; exact hmult₁
  have hw13 : ((∫ t in (0:ℝ)..x₀,
        Complex.exp (-((((β' : ℂ) - (β₁ : ℂ)) * (Real.log (q : ℝ))) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re)
      ≤ winSum χ.primitiveCharacter f x₀ (Real.log (q : ℝ)) δ (β' : ℂ) := by
    have hwin₁ : ‖(1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - (β₁ : ℂ)‖ ≤ δ := by
      have h1 : (1:ℂ) + (((β' : ℂ)).im : ℂ) * Complex.I - (β₁ : ℂ) = ((1 - β₁ : ℝ) : ℂ) := by
        simp
      rw [h1, Complex.norm_real, Real.norm_eq_abs]
      exact hβ₁
    simpa only [winSum] using windowSum_ge_single_real χ.primitiveCharacter hχ'
      (f := f) (x₀ := x₀) hx₀ hfnn' hFnn (L := Real.log (q : ℝ)) (δ := δ) hLnn hβ'β₁
      hdiv₁₂ hwin₁ hzw1
  have h614 : ‖(1:ℂ) + (((β' : ℂ) + (γ' : ℂ) * Complex.I).im : ℂ) * Complex.I - (β₁ : ℂ)‖ ≤ δ ∨
      (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) *
          (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re ≤ f 0 * ε := by
    by_cases hnear : ‖(1:ℂ) + (((β' : ℂ) + (γ' : ℂ) * Complex.I).im : ℂ) * Complex.I - (β₁ : ℂ)‖ ≤ δ
    · exact Or.inl hnear
    · push Not at hnear
      right
      have hfar1 : δ / 2 < |γ'| := by
        refine gt_half_delta_of_far (δ := δ) (β₁ := β₁) (γ' := γ')
          (lam₁ := Real.log (q : ℝ) * (1 - β₁)) (L := Real.log (q : ℝ)) hlogq ?_ ?_ ?_
        · have h1 : Real.log (q : ℝ) * (1 - β₁) / Real.log (q : ℝ) = 1 - β₁ := by
            field_simp
          rw [h1, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - β₁)]
        · refine le_trans hrect₁ ?_
          have h := hthr (Real.log (q : ℝ)) hLthr_le
          linarith
        · have h' : (1:ℂ) - (β₁ : ℂ) + (γ' : ℂ) * Complex.I
              = (1:ℂ) + (((β' : ℂ) + (γ' : ℂ) * Complex.I).im : ℂ) * Complex.I - (β₁ : ℂ) := by
            rw [himρ]; ring
          rw [h']
          exact hnear
      have hfar_apply := hfar (L := Real.log (q : ℝ))
        (a := (β' - β₁) * Real.log (q : ℝ)) (η := γ' * Real.log (q : ℝ))
        hLfar_le hlogq1
        (by
          rw [abs_mul, abs_of_pos hlogq]
          have h2 : β₁ - β' ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 / Real.log (q : ℝ) := by
            rw [le_div_iff₀ hlogq]
            nlinarith [hrect']
          rw [abs_of_nonpos (by linarith : β' - β₁ ≤ 0)]
          nlinarith [h2, hlogq])
        (by
          rw [abs_mul, abs_of_pos hlogq]
          nlinarith [hfar1, hlogq])
      have heqint : (∫ t in (0:ℝ)..x₀,
            Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) *
              (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ))
          = ∫ t in (0:ℝ)..x₀,
            Complex.exp (-(((((β' - β₁) * Real.log (q : ℝ) : ℝ) : ℂ) +
              (((γ' * Real.log (q : ℝ) : ℝ)) : ℂ) * Complex.I) * (t : ℂ))) *
              ((f t : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro t _
        congr 2
        push_cast
        ring
      rw [heqint]
      exact le_trans (Complex.re_le_norm _) hfar_apply
  have hw15 : ((∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) -
          ((β' : ℂ) + (γ' : ℂ) * Complex.I)) * (Real.log (q : ℝ))) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re)
      + (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) - (β₁ : ℂ)) *
          (Real.log (q : ℝ))) * (t : ℂ))) * ((f t : ℝ) : ℂ)).re - f 0 * ε
      ≤ winSum χ.primitiveCharacter f x₀ (Real.log (q : ℝ)) δ
          ((β' : ℂ) + (γ' : ℂ) * Complex.I) := by
    have h0nn : 0 ≤ (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) -
          ((β' : ℂ) + (γ' : ℂ) * Complex.I)) * (Real.log (q : ℝ))) * (t : ℂ))) *
          ((f t : ℝ) : ℂ)).re := by
      have hpt : ∀ t : ℝ, Complex.exp (-(((((β' : ℂ) + (γ' : ℂ) * Complex.I) -
            ((β' : ℂ) + (γ' : ℂ) * Complex.I)) * (Real.log (q : ℝ))) * (t : ℂ))) *
            ((f t : ℝ) : ℂ) = ((f t : ℝ) : ℂ) := by
        intro t; simp
      simp only [hpt]
      rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
      exact intervalIntegral.integral_nonneg hx₀.le (fun t _ => hfnn t)
    simpa only [winSum] using windowSum_ge_pair χ.primitiveCharacter hχ'
      (f := f) (x₀ := x₀) hx₀ hfnn' hFnn (L := Real.log (q : ℝ)) hLnn hε.le hβ' hne hf0.le
      hdiv₁q hdivq hmult₁q h0nn h614 hzw2
  exact hq₀ hqq₀ χ hχ hreal hβ₁ hβ' hβ'β₁ hβ₁le hβ'le hγ' hδle hzero₁ hzero'
    H hw13 hw15

end Commons.NumberTheory.Linnik
