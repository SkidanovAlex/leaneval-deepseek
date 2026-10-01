import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.LinnikAreas.logSum_threshold
import Submission.Work.LinnikAreas.gammaFactor_logDeriv_re_le

/-!
# Heath-Brown's Lemma 3.1 in the window form `L52Hyp`

The main analytic input is the recentred Hadamard partial-fraction expansion of the completed
`L`-function `Λ = completedLFunction χ` of a primitive non-principal character, applied at a
base point `s₀` with `Re s₀ < 0`: since every zero `ρ` of `Λ` has `0 < Re ρ < 1` and every
window zero `u` of `Λ` satisfies `Re u > 1 - δ > 0`,

* the off-window summands `-Re (1/(s-ρ) - 1/(s₀-ρ))` are `≤ 0` (both `Re (1/(s-ρ)) > 0` and
  `Re (1/(s₀-ρ)) < 0`),
* the window summands combine with the window sum `Σ_{|1+it-u|≤δ} ord(u) Re (1/(s-u))` to give
  `Σ_{|1+it-u|≤δ} ord(u) Re (1/(s₀-u)) ≤ 0` (again `Re (s₀ - u) < 0`).

Hence `-Re (L'/L)(s) + (window sum) ≤ -Re (Λ'/Λ)(s₀) + Re (γ'/γ)(s)`, and the two remaining
pieces are bounded by the functional-equation transfer at `Re s₀ = -1` and by the digamma
bound at `(s+a)/2`.
-/

namespace Work.LinnikAreas

open Complex DirichletCharacter Metric MeromorphicOn Filter
open scoped Real Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The divisor of `Λ = completedLFunction ψ` on the closed ball of radius `R`. -/
private noncomputable def divB {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (R : ℝ) (u : ℂ) : ℤ :=
  MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ) (Metric.closedBall 0 R) u

private lemma divB_def {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (R : ℝ) (u : ℂ) :
    divB ψ R u = MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ)
      (Metric.closedBall 0 R) u := rfl

private lemma divB_fun {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (R : ℝ) :
    divB ψ R = MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ)
      (Metric.closedBall 0 R) := funext (fun u => divB_def ψ R u)

/-- The twisted kernel `1/(s-u) + 1/u` has finite support away from `{0, s}`. -/
private lemma finiteSupport_kernel (f : ℂ → ℤ) (hf : (Function.support f).Finite) (s : ℂ) :
    Function.HasFiniteSupport (fun u : ℂ => ((f u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)) := by
  refine (hf.union ((Set.finite_singleton s).insert 0)).subset ?_
  intro u hu
  simp only [Function.mem_support, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
  by_contra h
  push_neg at h
  obtain ⟨hf0, -, -⟩ := h
  rw [hf0] at hu
  simpa using hu

/-- The recentred kernel `1/(s-u) - 1/(s₀-u)` has finite support away from `{s, s₀}`. -/
private lemma finiteSupport_kernel_sub (f : ℂ → ℤ) (hf : (Function.support f).Finite)
    (s s₀ : ℂ) :
    Function.HasFiniteSupport (fun u : ℂ => ((f u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₀ - u))) := by
  refine (hf.union (((Set.finite_singleton s).insert s₀).insert 0)).subset ?_
  intro u hu
  simp only [Function.mem_support, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
  by_contra h
  push_neg at h
  obtain ⟨hf0, -, -⟩ := h
  rw [hf0] at hu
  simpa using hu

/-- Pointwise sign of the summand of the comparison sum. -/
private lemma summand_le_zero {s s₀ u : ℂ} {δ : ℝ} (hs : 1 < s.re) (hs₀ : s₀.re < 0)
    (hu0 : 0 < u.re) (hu1 : u.re < 1) :
    -((1 / (s - u) - 1 / (s₀ - u)).re)
      + (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1 / (s - u)).re) else 0) ≤ 0 := by
  have h1 : 0 < (s - u).re := by rw [Complex.sub_re]; linarith
  have h2 : (s₀ - u).re < 0 := by rw [Complex.sub_re]; linarith
  have hne : s - u ≠ 0 := by intro h; rw [h] at h1; simp at h1
  have hne₀ : s₀ - u ≠ 0 := by intro h; rw [h] at h2; simp at h2
  have h3 : 0 < ((1 / (s - u) : ℂ)).re := by
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
    exact div_pos h1 (pow_pos (norm_pos_iff.mpr hne) 2)
  have h4 : ((1 / (s₀ - u) : ℂ)).re < 0 := by
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
    exact div_neg_of_neg_of_pos h2 (pow_pos (norm_pos_iff.mpr hne₀) 2)
  rw [Complex.sub_re]
  by_cases hc : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
  · rw [if_pos hc]; linarith
  · rw [if_neg hc]; linarith

/-- **Core estimate.**  For a primitive non-principal character `ψ` mod `N`, a point `s` with
`1 < Re s`, a base point `s₀` with `Re s₀ < 0` and `Im s₀ = Im s`, and any `δ < 1`:
`-Re (Λ'/Λ)(s) + Re (Λ'/Λ)(s₀) + Σ_{|1+i·Im s - u| ≤ δ} ord(u)·Re (1/(s-u)) ≤ 0`. -/
private theorem window_core {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N)
    (hψ : ψ ≠ 1) (hψprim : ψ.IsPrimitive) {s s₀ : ℂ} {δ : ℝ}
    (hs : 1 < s.re) (hs₀ : s₀.re < 0) (hs₀im : s₀.im = s.im) (hδ : δ < 1) :
    - (logDeriv (DirichletCharacter.completedLFunction ψ) s).re
      + (logDeriv (DirichletCharacter.completedLFunction ψ) s₀).re
      + (∑ᶠ u : ℂ, ((divB ψ (|s.im| + 2) u : ℤ) : ℝ) *
          (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1 / (s - u)).re) else 0))
    ≤ 0 := by
  classical
  have hΛdiff : Differentiable ℂ (DirichletCharacter.completedLFunction ψ) :=
    differentiable_completedLFunction hψ
  have hΛs : DirichletCharacter.completedLFunction ψ s ≠ 0 :=
    Commons.NumberTheory.DirichletCharacter.completedLFunction_ne_zero_of_one_lt_re ψ hs
  have hΛs₀ : DirichletCharacter.completedLFunction ψ s₀ ≠ 0 := by
    intro h
    have := (Commons.NumberTheory.DirichletCharacter.zerosInStrip ψ hψ hψprim s₀ h).1
    linarith
  have hdivfin : ∀ R : ℝ, (Function.support (divB ψ R)).Finite := by
    intro R
    have h := MeromorphicOn.divisor_support_finite_of_subset
      (f := DirichletCharacter.completedLFunction ψ)
      (U := Metric.closedBall (0 : ℂ) R) (V := Metric.closedBall (0 : ℂ) R)
      (fun z _ => (hΛdiff.analyticAt z).meromorphicAt) (isCompact_closedBall 0 R) subset_rfl
    rwa [divB_fun]
  -- Hadamard partial fractions at `s` and at `s₀`
  have hA := Commons.NumberTheory.Linnik.partialFraction_eq ψ hψ hψprim s hΛs
  have hB := Commons.NumberTheory.Linnik.partialFraction_eq ψ hψ hψprim s₀ hΛs₀
  have hdiff0 : Tendsto (fun R : ℝ =>
      (∑ᶠ u : ℂ, ((divB ψ R u : ℤ) : ℂ) * (1 / (s - u) + 1 / u))
        - (∑ᶠ u : ℂ, ((divB ψ R u : ℤ) : ℂ) * (1 / (s₀ - u) + 1 / u)))
      atTop (𝓝 (logDeriv (DirichletCharacter.completedLFunction ψ) s
        - logDeriv (DirichletCharacter.completedLFunction ψ) s₀)) := by
    have h := hA.sub hB
    have hlim : (deriv (DirichletCharacter.completedLFunction ψ) s /
          DirichletCharacter.completedLFunction ψ s
          - deriv (DirichletCharacter.completedLFunction ψ) 0 /
            DirichletCharacter.completedLFunction ψ 0)
        - (deriv (DirichletCharacter.completedLFunction ψ) s₀ /
            DirichletCharacter.completedLFunction ψ s₀
            - deriv (DirichletCharacter.completedLFunction ψ) 0 /
              DirichletCharacter.completedLFunction ψ 0)
        = logDeriv (DirichletCharacter.completedLFunction ψ) s
          - logDeriv (DirichletCharacter.completedLFunction ψ) s₀ := by
      simp only [← logDeriv_apply]
      ring
    rw [hlim] at h
    simpa only [divB] using h
  -- rewrite the difference as a single finsum
  have hS_eq : ∀ R : ℝ,
      (∑ᶠ u : ℂ, ((divB ψ R u : ℤ) : ℂ) * (1 / (s - u) + 1 / u))
        - (∑ᶠ u : ℂ, ((divB ψ R u : ℤ) : ℂ) * (1 / (s₀ - u) + 1 / u))
      = ∑ᶠ u : ℂ, ((divB ψ R u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₀ - u)) := by
    intro R
    rw [← finsum_sub_distrib (finiteSupport_kernel (divB ψ R) (hdivfin R) s)
      (finiteSupport_kernel (divB ψ R) (hdivfin R) s₀)]
    exact finsum_congr (fun u => by ring)
  have hS : Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
      ((divB ψ R u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₀ - u)))
      atTop (𝓝 (logDeriv (DirichletCharacter.completedLFunction ψ) s
        - logDeriv (DirichletCharacter.completedLFunction ψ) s₀)) :=
    hdiff0.congr' (Eventually.of_forall hS_eq)
  -- real part
  have hSre : Tendsto (fun R : ℝ =>
      (∑ᶠ u : ℂ, ((divB ψ R u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₀ - u))).re)
      atTop (𝓝 ((logDeriv (DirichletCharacter.completedLFunction ψ) s
        - logDeriv (DirichletCharacter.completedLFunction ψ) s₀).re)) :=
    (Complex.continuous_re.tendsto _).comp hS
  set W : ℝ := ∑ᶠ u : ℂ, ((divB ψ (|s.im| + 2) u : ℤ) : ℝ) *
    (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1 / (s - u)).re) else 0) with hW
  have hg : Tendsto (fun R : ℝ =>
      -(∑ᶠ u : ℂ, ((divB ψ R u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₀ - u))).re + W)
      atTop (𝓝 (-(logDeriv (DirichletCharacter.completedLFunction ψ) s
        - logDeriv (DirichletCharacter.completedLFunction ψ) s₀).re + W)) :=
    hSre.neg.add tendsto_const_nhds
  -- pointwise nonpositivity (eventually)
  have hreS : ∀ R : ℝ,
      (∑ᶠ u : ℂ, ((divB ψ R u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₀ - u))).re
      = ∑ᶠ u : ℂ, ((divB ψ R u : ℤ) : ℝ) * ((1 / (s - u) - 1 / (s₀ - u)).re) := by
    intro R
    have key := map_finsum Complex.reCLM.toAddMonoidHom
      (finiteSupport_kernel_sub (divB ψ R) (hdivfin R) s s₀)
    rw [show (∑ᶠ u : ℂ, ((divB ψ R u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₀ - u))).re
        = Complex.reCLM.toAddMonoidHom
            (∑ᶠ u : ℂ, ((divB ψ R u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₀ - u))) from rfl]
    rw [key]
    refine finsum_congr (fun u => ?_)
    show ((↑(divB ψ R u) : ℂ) * (1 / (s - u) - 1 / (s₀ - u))).re
      = ↑(divB ψ R u) * (1 / (s - u) - 1 / (s₀ - u)).re
    rw [Complex.mul_re]
    simp
  have hmem_ball : ∀ u : ℂ, ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ →
      u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2) := by
    intro u hu
    have h1 : ‖u - ((1 : ℂ) + (s.im : ℂ) * Complex.I)‖ ≤ δ := by
      rw [← norm_neg, neg_sub]; exact hu
    have h2 : ‖u‖ ≤ ‖u - ((1 : ℂ) + (s.im : ℂ) * Complex.I)‖
        + ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ := by
      have h := norm_add_le (u - ((1 : ℂ) + (s.im : ℂ) * Complex.I))
        ((1 : ℂ) + (s.im : ℂ) * Complex.I)
      have heq : (u - ((1 : ℂ) + (s.im : ℂ) * Complex.I))
          + ((1 : ℂ) + (s.im : ℂ) * Complex.I) = u := by ring
      rwa [heq] at h
    have h3 : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ ≤ |s.im| + 1 := by
      have h4 : ((1 : ℂ) + (s.im : ℂ) * Complex.I).re = 1 := by simp
      have h5 : ((1 : ℂ) + (s.im : ℂ) * Complex.I).im = s.im := by simp
      have h6 : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ = Real.sqrt (1 + s.im ^ 2) := by
        rw [Complex.norm_def, Complex.normSq_apply, h4, h5]
        ring_nf
      rw [h6]
      have h7 : Real.sqrt (1 + s.im ^ 2) ≤ Real.sqrt ((|s.im| + 1) ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith only [sq_abs s.im, abs_nonneg s.im, sq_nonneg (|s.im| + 1)]
      rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ |s.im| + 1)] at h7
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have h9 : ‖u‖ ≤ δ + (|s.im| + 1) := by linarith
    linarith
  have hdivmem : ∀ (R : ℝ) (u : ℂ), divB ψ R u ≠ 0 → u ∈ Metric.closedBall (0 : ℂ) R := by
    intro R u hd
    by_contra h
    refine hd ?_
    rw [divB_def, MeromorphicOn.divisor_def]
    exact if_neg (fun hh => h hh.2)
  have hdivzero : ∀ (R : ℝ) (u : ℂ), divB ψ R u ≠ 0 →
      DirichletCharacter.completedLFunction ψ u = 0 := by
    intro R u hd
    have hmem := hdivmem R u hd
    have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction ψ)
        (Metric.closedBall (0 : ℂ) R) := fun z _ => hΛdiff.analyticAt z
    have hcast := Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hmem
    have hk : analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) u ≠ 0 := by
      intro hk0
      exact hd (by rw [divB_def, hcast, hk0]; simp)
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hk
  have hdivnn : ∀ (R : ℝ) (u : ℂ), (0 : ℝ) ≤ ((divB ψ R u : ℤ) : ℝ) := by
    intro R u
    have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction ψ)
        (Metric.closedBall (0 : ℂ) R) := fun z _ => hΛdiff.analyticAt z
    have := Commons.Analysis.Complex.divisor_nonneg_on_closedBall han u
    simpa only [divB] using this
  -- the summand function and its sign
  have hsummand : ∀ R : ℝ, |s.im| + 2 ≤ R →
      -(∑ᶠ u : ℂ, ((divB ψ R u : ℤ) : ℂ) * (1 / (s - u) - 1 / (s₀ - u))).re + W ≤ 0 := by
    intro R hR
    rw [hreS R]
    have hW_eq : W = ∑ᶠ u : ℂ, ((divB ψ R u : ℤ) : ℝ) *
        (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1 / (s - u)).re) else 0) := by
      rw [hW]
      refine finsum_congr (fun u => ?_)
      by_cases hc : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
      · rw [if_pos hc]
        have hmem1 := hmem_ball u hc
        have hmem2 : u ∈ Metric.closedBall (0 : ℂ) R := by
          rw [Metric.mem_closedBall] at hmem1 ⊢; linarith
        have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction ψ)
            (Metric.closedBall (0 : ℂ) (|s.im| + 2) ∪ Metric.closedBall (0 : ℂ) R) :=
          fun z _ => hΛdiff.analyticAt z
        have hdeq := Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset han hmem1 hmem2
        simp only [divB]
        rw [hdeq]
      · rw [if_neg hc]; simp
    rw [hW_eq]
    rw [← finsum_neg_distrib (fun u : ℂ =>
        ((divB ψ R u : ℤ) : ℝ) * ((1 / (s - u) - 1 / (s₀ - u)).re))]
    have hfX : Function.HasFiniteSupport (fun u : ℂ =>
        -(((divB ψ R u : ℤ) : ℝ) * ((1 / (s - u) - 1 / (s₀ - u)).re))) :=
      (hdivfin R).subset (by
        intro u hu
        simp only [Function.mem_support] at hu ⊢
        intro h0
        exact hu (by rw [h0]; ring))
    have hfY : Function.HasFiniteSupport (fun u : ℂ => ((divB ψ R u : ℤ) : ℝ) *
        (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1 / (s - u)).re) else 0)) :=
      (hdivfin R).subset (by
        intro u hu
        simp only [Function.mem_support] at hu ⊢
        intro h0
        exact hu (by rw [h0]; ring))
    rw [← finsum_add_distrib hfX hfY]
    have hconcl : (∑ᶠ u : ℂ,
        (-(((divB ψ R u : ℤ) : ℝ) * ((1 / (s - u) - 1 / (s₀ - u)).re))
          + ((divB ψ R u : ℤ) : ℝ) *
            (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1 / (s - u)).re) else 0)))
        ≤ 0 := by
      have hnn : (0 : ℝ) ≤ ∑ᶠ u : ℂ, -(-(((divB ψ R u : ℤ) : ℝ) *
          ((1 / (s - u) - 1 / (s₀ - u)).re))
          + ((divB ψ R u : ℤ) : ℝ) *
            (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1 / (s - u)).re) else 0)) := by
        refine finsum_nonneg (fun u => ?_)
        by_cases hd0 : divB ψ R u = 0
        · rw [show ((divB ψ R u : ℤ) : ℝ) = 0 by rw [hd0]; simp]
          ring_nf
          norm_num
        · obtain ⟨hu0, hu1⟩ := Commons.NumberTheory.DirichletCharacter.zerosInStrip ψ hψ hψprim u (hdivzero R u hd0)
          have hh : ((divB ψ R u : ℤ) : ℝ) *
              (-(((1 / (s - u) - 1 / (s₀ - u)).re))
                + (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1 / (s - u)).re) else 0)) ≤ 0 := by
            refine mul_nonpos_of_nonneg_of_nonpos (hdivnn R u) ?_
            exact summand_le_zero (s := s) (s₀ := s₀) (u := u) (δ := δ) hs hs₀ hu0 hu1
          have hE : -(-(((divB ψ R u : ℤ) : ℝ) * ((1 / (s - u) - 1 / (s₀ - u)).re))
                + ((divB ψ R u : ℤ) : ℝ) *
                  (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1 / (s - u)).re) else 0))
              = -(((divB ψ R u : ℤ) : ℝ) *
                  (-(((1 / (s - u) - 1 / (s₀ - u)).re))
                    + (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1 / (s - u)).re) else 0))) := by
            ring
          rw [hE]
          linarith
      rw [finsum_neg_distrib] at hnn
      linarith
    exact hconcl
  -- take the limit
  have hlim_le : -(logDeriv (DirichletCharacter.completedLFunction ψ) s
      - logDeriv (DirichletCharacter.completedLFunction ψ) s₀).re + W ≤ 0 := by
    refine le_of_tendsto hg ?_
    filter_upwards [eventually_ge_atTop (|s.im| + 2)] with R hR
    exact hsummand R hR
  rw [Complex.sub_re] at hlim_le
  linarith only [hlim_le]

/-- **Heath-Brown's Lemma 3.1 in the window form `L52Hyp`** (the shape consumed by
`Commons.NumberTheory.Linnik.lemma5_2_of_logDeriv_bound_phi_imprim`), with a fixed absolute
constant `c = 1` and *every* window radius `δ`: for every non-principal `χ` modulo `q`, every
`ε > 0` and every `δ ∈ (0,1)`, and all `q ≥ q₀(ε,δ)`, the logarithmic derivative of the
primitive `L`-function satisfies
`(-L'/L)(s).re + Σ_{|1+i·Im s - u| ≤ δ} ord(u)·(1/(s-u)).re ≤ (1 + ε/4)·log q`
for `1 + 1/(L log L) ≤ Re s ≤ 1 + log log q / L`, `|Im s| ≤ 10 L` (`L = log q`).

The proof recentres the Hadamard partial fraction of `Λ = completedLFunction χ*` at
`s₀ = -1 + i·Im s` (see `window_core`), so that the whole left-hand side is bounded by
`-Re (Λ'/Λ)(s₀) + Re (γ'/γ)(s)`; the first term is controlled by the functional equation on
the line `Re = -1` (`completedLogDeriv_neg_one_tight`, giving `log N + ½log(2+|Im s|) + 3`),
the second by the digamma bound (`gammaFactor_logDeriv_re_le`).  Since `log N ≤ log q` and
`|Im s| ≤ 10 log q`, the total is `log q + O(log log q) ≤ (1 + ε/4) log q` for `q ≥ q₀(ε)`. -/
theorem L52Hyp_of_partialFraction : ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ 1 ε δ := by
  intro ε δ hε hδ0 hδ1
  obtain ⟨qA, hqA⟩ := Work.LinnikAreas.logSum_threshold (7 + Real.log Real.pi / 2) ε hε
  refine ⟨max qA 3, ?_⟩
  intro q hq
  classical
  intro _inst χ _instc hχ1 s hs1 hs2 hs3
  have hq3 : 3 ≤ q := le_trans (le_max_right qA 3) hq
  have hqAq : qA ≤ q := le_trans (le_max_left qA 3) hq
  have hq1 : 1 < q := by omega
  have hLq_pos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
  have hLgt1 : 1 < Real.log (q : ℝ) := by
    have h : Real.log 3 ≤ Real.log (q : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hq3)
    linarith
  have hloglog_pos : 0 < Real.log (Real.log (q : ℝ)) := Real.log_pos hLgt1
  have hloglog_le : Real.log (Real.log (q : ℝ)) ≤ Real.log (q : ℝ) := Real.log_le_self hLq_pos.le
  have hsre1 : 1 < s.re := by
    have hpos : 0 < 1 / (Real.log (q : ℝ) * Real.log (Real.log (q : ℝ))) :=
      div_pos one_pos (mul_pos hLq_pos hloglog_pos)
    linarith
  have hsre2 : s.re ≤ 2 := by
    have h : Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) ≤ 1 := by
      rw [div_le_one hLq_pos]; exact hloglog_le
    linarith
  -- ### the primitive character
  have hψne : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ1
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hψprim : (χ.primitiveCharacter).IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hNpos : 0 < χ.conductor := Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
  have hNq : χ.conductor ≤ q := Nat.le_of_dvd (by omega) χ.conductor_dvd_level
  have hlogN : Real.log (χ.conductor : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by exact_mod_cast hNpos) (by exact_mod_cast hNq)
  have hNne1 : χ.conductor ≠ 1 := by
    intro h
    exact hψne (DirichletCharacter.level_one' (χ.primitiveCharacter) h)
  -- ### the core estimate at the base point `s₀ = -1 + i·Im s`
  set s₀ : ℂ := (-1 : ℂ) + (s.im : ℂ) * Complex.I with hs₀def
  have hs₀re : s₀.re < 0 := by simp [hs₀def]
  have hs₀im : s₀.im = s.im := by simp [hs₀def]
  have hcore := window_core (χ.primitiveCharacter) hψne hψprim (s := s) (s₀ := s₀) (δ := δ)
    hsre1 hs₀re hs₀im hδ1
  -- ### splitting the logarithmic derivative of the ordinary `L`-function
  have hΛdiff : Differentiable ℂ (completedLFunction (χ.primitiveCharacter)) :=
    differentiable_completedLFunction hψne
  have hΛs : completedLFunction (χ.primitiveCharacter) s ≠ 0 :=
    Commons.NumberTheory.DirichletCharacter.completedLFunction_ne_zero_of_one_lt_re _ hsre1
  haveI : Decidable (χ.primitiveCharacter).Even := Classical.propDecidable _
  have hsne0 : s ≠ 0 := by
    intro h
    have h0 : s.re = 0 := by rw [h]; simp
    rw [h0] at hsre1
    exact absurd hsre1 (by norm_num)
  have hGan : AnalyticAt ℂ (gammaFactor (χ.primitiveCharacter)) s :=
    Commons.NumberTheory.DirichletCharacter.gammaFactor_analyticAt (χ.primitiveCharacter)
      (by linarith : -(1 / 2 : ℝ) < s.re) (fun _ => hsne0)
  have hGne : gammaFactor (χ.primitiveCharacter) s ≠ 0 :=
    Commons.NumberTheory.DirichletCharacter.gammaFactor_ne_zero' (χ.primitiveCharacter)
      (by linarith : -(1 / 2 : ℝ) < s.re) (fun _ => hsne0)
  have hGdiff : DifferentiableAt ℂ (gammaFactor (χ.primitiveCharacter)) s := hGan.differentiableAt
  have hsplit : logDeriv (LFunction (χ.primitiveCharacter)) s
      = logDeriv (completedLFunction (χ.primitiveCharacter)) s
        - logDeriv (gammaFactor (χ.primitiveCharacter)) s := by
    have hfun : LFunction (χ.primitiveCharacter)
        = (fun u => completedLFunction (χ.primitiveCharacter) u
            / gammaFactor (χ.primitiveCharacter) u) := by
      funext u
      exact DirichletCharacter.LFunction_eq_completed_div_gammaFactor _ u (Or.inr hNne1)
    rw [hfun]
    exact logDeriv_div (f := completedLFunction (χ.primitiveCharacter))
      (g := gammaFactor (χ.primitiveCharacter)) s hΛs hGne
      ((differentiable_completedLFunction hψne) s) hGdiff
  -- ### the two explicit bounds
  have hGbound : (logDeriv (gammaFactor (χ.primitiveCharacter)) s).re
      ≤ Real.log Real.pi / 2 + 4 + (1 / 2) * Real.log (2 + |s.im| / 2) :=
    Work.LinnikAreas.gammaFactor_logDeriv_re_le (χ.primitiveCharacter) hsre1.le hsre2
  have hΛ₀bound : -(logDeriv (completedLFunction (χ.primitiveCharacter)) s₀).re
      ≤ Real.log (χ.conductor : ℝ) + (1 / 2) * Real.log (2 + |s.im|) + 3 := by
    have ht := Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_tight
      (χ.primitiveCharacter) hψne hψprim s.im
    have hs₀eq : s₀ = (-1 : ℂ) + Complex.I * (s.im : ℂ) := by
      rw [hs₀def]; ring
    rw [hs₀eq]
    have h3 := Complex.abs_re_le_norm
      (logDeriv (completedLFunction (χ.primitiveCharacter)) ((-1 : ℂ) + Complex.I * (s.im : ℂ)))
    have h4 := neg_le_abs
      (logDeriv (completedLFunction (χ.primitiveCharacter)) ((-1 : ℂ) + Complex.I * (s.im : ℂ))).re
    linarith [h3, h4, ht]
  -- ### identify the window sum of the goal with the `divB` version
  have hWid : (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (completedLFunction (χ.primitiveCharacter))
        (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
        (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1 / (s - u)).re) else 0))
      = (∑ᶠ u : ℂ, ((divB (χ.primitiveCharacter) (|s.im| + 2) u : ℤ) : ℝ) *
        (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1 / (s - u)).re) else 0)) := by
    refine finsum_congr (fun u => ?_)
    rw [divB_def]
  rw [hWid]
  -- ### assemble
  have h1 : (-logDeriv (LFunction (χ.primitiveCharacter)) s).re
      = -(logDeriv (completedLFunction (χ.primitiveCharacter)) s).re
        + (logDeriv (gammaFactor (χ.primitiveCharacter)) s).re := by
    rw [show (-logDeriv (LFunction (χ.primitiveCharacter)) s)
        = -(logDeriv (LFunction (χ.primitiveCharacter)) s) from rfl]
    rw [hsplit]
    simp only [Complex.neg_re, Complex.sub_re]
    ring
  rw [h1]
  have h2 : -(logDeriv (completedLFunction (χ.primitiveCharacter)) s).re
      + (logDeriv (gammaFactor (χ.primitiveCharacter)) s).re
      + (∑ᶠ u : ℂ, ((divB (χ.primitiveCharacter) (|s.im| + 2) u : ℤ) : ℝ) *
        (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1 / (s - u)).re) else 0))
      ≤ (Real.log (χ.conductor : ℝ) + (1 / 2) * Real.log (2 + |s.im|) + 3)
        + (Real.log Real.pi / 2 + 4 + (1 / 2) * Real.log (2 + |s.im| / 2)) := by
    linarith only [hcore, hGbound, hΛ₀bound]
  refine h2.trans ?_
  have hLlog : (1 / 2) * Real.log (2 + |s.im|)
      ≤ (1 / 2) * Real.log (2 + 10 * Real.log (q : ℝ)) := by
    refine mul_le_mul_of_nonneg_left (Real.log_le_log ?_ ?_) (by norm_num)
    · linarith [abs_nonneg s.im]
    · linarith [hs3]
  have hLlog2 : (1 / 2) * Real.log (2 + |s.im| / 2)
      ≤ (1 / 2) * Real.log (2 + 5 * Real.log (q : ℝ)) := by
    refine mul_le_mul_of_nonneg_left (Real.log_le_log ?_ ?_) (by norm_num)
    · linarith [abs_nonneg s.im]
    · linarith [hs3]
  have hA' := hqA q hqAq
  linarith only [hLlog, hLlog2, hA', hlogN]

end Work.LinnikAreas
