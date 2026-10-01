import Mathlib
import Submission.Work.ZeroDensity.Jutila.kernelSumHalf
import Submission.Work.ZeroDensity.Jutila.linnikDensityAuxKernel
import Submission.Work.ZeroDensity.Jutila.linnikDensityLemmaConst
import Submission.Work.LinnikAreas.boxMaxZero

namespace Work.ZeroDensity.Jutila

open scoped Classical BigOperators

set_option maxHeartbeats 4000000

/-! ## A density lemma at an arbitrary real height

The proof of the per-box mass bound consumes a zero-density estimate for a square of half-width
`(1-σ)/2` centred at an *arbitrary* real height `τ`:

  `Σ_{σ ≤ Re ρ ≤ 1, |Im ρ - τ| ≤ (1-σ)/2} mult(ρ) ≤ C·((1-σ)·log(q(|τ|+2)) + 1)`.

This is Jutila's Lemma 8 in the form recorded in the literature (Pintz; Ye; Akbary-Trudgian), and
it is the natural generalisation to real `τ` of `Work.ZeroDensity.Jutila.linnikDensityLemmaConst`
(which asks `τ ≥ 1`).  The two ingredients are already in the workspace:

* `Work.ZeroDensity.Jutila.linnikDensityAuxKernel` - each box zero contributes at least
  `1/(5(1-σ))` to the Hadamard kernel at the base point `1 + (1-σ) + iτ`;
* `Work.ZeroDensity.Jutila.kernelSumHalf` - the divisor-weighted kernel sum over *any* ball is at
  most `1/(1-σ) + ½log N + ½log(2+|τ|) + 4`, uniformly in the real height `τ`.

Only the bookkeeping (box zeros lie in the ball of radius `|τ| + 2`) has to be redone for real `τ`. -/

/-- The imaginary part of a real number whose box index at scale `Δ > 0` equals `k` lies in the
half-open interval `[kΔ, (k+1)Δ)`. -/
lemma im_box_bounds {Δ : ℝ} (hΔ : 0 < Δ) {x : ℝ} {k : ℤ} (h : ⌊x / Δ⌋ = k) :
    (k : ℝ) * Δ ≤ x ∧ x < ((k : ℝ) + 1) * Δ := by
  have h1 : (k : ℝ) ≤ x / Δ := by
    have := Int.floor_le (x / Δ); rw [h] at this; exact this
  have h2 : x / Δ < (k : ℝ) + 1 := by
    have := Int.lt_floor_add_one (x / Δ); rw [h] at this; exact this
  refine ⟨?_, ?_⟩
  · calc (k : ℝ) * Δ ≤ (x / Δ) * Δ := mul_le_mul_of_nonneg_right h1 hΔ.le
      _ = x := by rw [div_mul_cancel₀ _ (ne_of_gt hΔ)]
  · calc x = (x / Δ) * Δ := by rw [div_mul_cancel₀ _ (ne_of_gt hΔ)]
      _ < ((k : ℝ) + 1) * Δ := mul_lt_mul_of_pos_right h2 hΔ

/-- Finiteness of the zero support of a rectangle sum: the points `ρ` with `zeroMult χ ρ ≠ 0`,
`σ ≤ Re ρ ≤ 1` and `|Im ρ| ≤ T` form a finite set (they lie in a compact box on which the zero
set of the fixed entire function `completedLFunction χ.primitiveCharacter` is finite, and the
completed `L`-function of `χ` vanishes at every such point). -/
lemma zeroSupport_finite' {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T : ℝ) :
    Function.HasFiniteSupport (fun ρ : ℂ =>
      if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) := by
  rw [Function.HasFiniteSupport]
  refine (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ σ T).subset ?_
  intro ρ hρ
  rw [Function.mem_support] at hρ
  by_cases h : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
  · rw [if_pos h] at hρ
    exact ⟨fun h0 => hρ (by exact_mod_cast h0), h.1, h.2.1, h.2.2⟩
  · rw [if_neg h] at hρ
    exact absurd rfl hρ

/-- A zero of `F` in the strip `0 < Re < 1` with `|Im ρ - τ| ≤ (1-σ)/2 ≤ 1/2` lies in the closed
ball of radius `|τ| + 2` about the origin; this is the geometric input of the box-count step, with
the height `τ` (possibly negative) replacing the `T ≥ 1` of the classical statement. -/
lemma mem_closedBall_of_box_gen {ρ : ℂ} {σ τ : ℝ} (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1)
    (hσ0 : 0 ≤ σ) (him : |ρ.im - τ| ≤ (1 - σ) / 2) :
    ρ ∈ Metric.closedBall (0 : ℂ) (|τ| + 2) := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have him' : |ρ.im - τ| ≤ 1 / 2 := by linarith
  have hy : |ρ.im| ≤ |τ| + 1 / 2 := by
    calc |ρ.im| = |(ρ.im - τ) + τ| := by rw [sub_add_cancel]
      _ ≤ |ρ.im - τ| + |τ| := abs_add_le _ _
      _ ≤ 1 / 2 + |τ| := by linarith
      _ = |τ| + 1 / 2 := by ring
  have hsq : ‖ρ‖ ^ 2 ≤ (|τ| + 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have h1 : ρ.im ≤ |τ| + 1 / 2 := (abs_le.mp hy).2
    have h2 : -(|τ| + 1 / 2) ≤ ρ.im := (abs_le.mp hy).1
    have h3 : ρ.im ^ 2 ≤ (|τ| + 1 / 2) ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ |τ| + 1 / 2 - ρ.im)
        (by linarith : (0:ℝ) ≤ |τ| + 1 / 2 + ρ.im)]
    have h4 : ρ.re ^ 2 ≤ (1 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hre0) (le_of_lt hre1) 2
    have hkey : (|τ| + 1 / 2) ^ 2 + (1 : ℝ) ^ 2 ≤ (|τ| + 2) ^ 2 := by
      nlinarith [abs_nonneg τ]
    nlinarith [h3, h4, hkey]
  have h2 : ‖ρ‖ ≤ |τ| + 2 := by
    have h0 : (0:ℝ) ≤ |τ| + 2 := by linarith [abs_nonneg τ]
    have h := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (norm_nonneg ρ), Real.sqrt_sq h0] at h
    exact h
  exact h2

/-- **The box-count step at a real height.**  For an entire function `F` whose zeros all lie in the
open critical strip, the multiplicity-weighted number of zeros in the box `σ ≤ Re ρ ≤ 1`,
`|Im ρ - τ| ≤ (1-σ)/2` is at most `5(1-σ)` times the divisor-weighted Hadamard kernel sum over the
closed ball of radius `|τ| + 2`. -/
theorem linnikDensityAuxBoxGen (F : ℂ → ℂ) (han : AnalyticOnNhd ℂ F Set.univ)
    (hstrip : ∀ u : ℂ, F u = 0 → 0 < u.re ∧ u.re < 1)
    {σ τ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    (∑ᶠ ρ : ℂ, (if analyticOrderNatAt F ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - τ| ≤ (1 - σ) / 2
        then (analyticOrderNatAt F ρ : ℝ) else 0))
      ≤ 5 * (1 - σ) * ∑ᶠ u : ℂ,
          ((MeromorphicOn.divisor F (Metric.closedBall 0 (|τ| + 2)) u : ℤ) : ℝ) *
            ((1 + (1 - σ) - u.re) / ((1 + (1 - σ) - u.re) ^ 2 + (τ - u.im) ^ 2)) := by
  classical
  have hUcompact : IsCompact (Metric.closedBall (0 : ℂ) (|τ| + 2)) :=
    isCompact_closedBall (0 : ℂ) (|τ| + 2)
  have hmont : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) (|τ| + 2)) :=
    fun z _ => han z (Set.mem_univ z)
  have hdiv_nonneg : ∀ u : ℂ,
      (0 : ℤ) ≤ MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (|τ| + 2)) u :=
    fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hmont u
  have hd_fin : Function.HasFiniteSupport
      (fun u : ℂ => MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (|τ| + 2)) u) :=
    (MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (|τ| + 2))).finiteSupport hUcompact
  have hDfin : Function.HasFiniteSupport
      (fun u : ℂ => ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (|τ| + 2)) u : ℤ) : ℝ)) :=
    hd_fin.subset (fun u hu => by
      rw [Function.mem_support] at hu ⊢
      intro h
      exact hu (by rw [h]; simp))
  have hRfin : Function.HasFiniteSupport (fun u : ℂ =>
      ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (|τ| + 2)) u : ℤ) : ℝ) *
        ((1 + (1 - σ) - u.re) / ((1 + (1 - σ) - u.re) ^ 2 + (τ - u.im) ^ 2))) :=
    hDfin.subset (fun u hu => by
      rw [Function.mem_support] at hu ⊢
      intro h
      exact hu (by rw [h, zero_mul]))
  have hpt : ∀ ρ : ℂ,
      (if analyticOrderNatAt F ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - τ| ≤ (1 - σ) / 2
        then (analyticOrderNatAt F ρ : ℝ) else 0)
      ≤ 5 * (1 - σ) * (((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (|τ| + 2)) ρ : ℤ) : ℝ) *
          ((1 + (1 - σ) - ρ.re) / ((1 + (1 - σ) - ρ.re) ^ 2 + (τ - ρ.im) ^ 2))) := by
    intro ρ
    by_cases hc : analyticOrderNatAt F ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - τ| ≤ (1 - σ) / 2
    · have hLval : (if analyticOrderNatAt F ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
          |ρ.im - τ| ≤ (1 - σ) / 2 then (analyticOrderNatAt F ρ : ℝ) else 0)
          = (analyticOrderNatAt F ρ : ℝ) := if_pos hc
      rw [hLval]
      obtain ⟨hm, hr1, hr2, him⟩ := hc
      have hF0 : F ρ = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hm
      obtain ⟨hz0, hz1⟩ := hstrip ρ hF0
      have hmem : ρ ∈ (Metric.closedBall (0 : ℂ) (|τ| + 2)) :=
        mem_closedBall_of_box_gen hz0 hz1 hσ0 him
      have hDval : ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (|τ| + 2)) ρ : ℤ) : ℝ)
          = (analyticOrderNatAt F ρ : ℝ) := by
        rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast hmont hmem]
        simp
      rw [hDval]
      rcases eq_or_lt_of_le (show (0:ℝ) ≤ 1 - σ by linarith) with hzero | hpos
      · exfalso
        have hσ : σ = 1 := by linarith
        linarith [hz1]
      · have hk : 1 / (5 * (1 - σ)) ≤
            ((1 + (1 - σ) - ρ.re) / ((1 + (1 - σ) - ρ.re) ^ 2 + (τ - ρ.im) ^ 2)) :=
          linnikDensityAuxKernel hpos (by linarith : 1 - σ ≤ 1)
            (by linarith : 1 - (1 - σ) ≤ ρ.re) hr2 him
        have hmnn : (0:ℝ) ≤ (analyticOrderNatAt F ρ : ℝ) := Nat.cast_nonneg _
        have hne : 5 * (1 - σ) ≠ 0 := by linarith
        calc (analyticOrderNatAt F ρ : ℝ)
            = 5 * (1 - σ) * ((analyticOrderNatAt F ρ : ℝ) * (1 / (5 * (1 - σ)))) :=
              (by field_simp)
          _ ≤ 5 * (1 - σ) * ((analyticOrderNatAt F ρ : ℝ) *
                ((1 + (1 - σ) - ρ.re) / ((1 + (1 - σ) - ρ.re) ^ 2 + (τ - ρ.im) ^ 2))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk hmnn) (by linarith)
    · have hLval : (if analyticOrderNatAt F ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
          |ρ.im - τ| ≤ (1 - σ) / 2 then (analyticOrderNatAt F ρ : ℝ) else 0) = 0 := if_neg hc
      rw [hLval]
      refine mul_nonneg (by linarith : (0:ℝ) ≤ 5 * (1 - σ)) ?_
      by_cases hDz : MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (|τ| + 2)) ρ = 0
      · rw [show ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (|τ| + 2)) ρ : ℤ) : ℝ) = 0
            by rw [hDz]; simp]
        simp
      · have hmem : ρ ∈ (Metric.closedBall (0 : ℂ) (|τ| + 2)) := by
          by_contra h
          exact hDz (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem
            (MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (|τ| + 2))) h)
        have hord : analyticOrderNatAt F ρ ≠ 0 := by
          intro h0
          refine hDz ?_
          rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast hmont hmem, h0]
          simp
        obtain ⟨hz0, hz1⟩ := hstrip ρ (apply_eq_zero_of_analyticOrderNatAt_ne_zero hord)
        have hnum : 0 < 1 + (1 - σ) - ρ.re := by linarith
        have hden : 0 < (1 + (1 - σ) - ρ.re) ^ 2 + (τ - ρ.im) ^ 2 := by
          have hh : (0:ℝ) < (1 + (1 - σ) - ρ.re) ^ 2 := pow_pos hnum 2
          nlinarith [sq_nonneg (τ - ρ.im)]
        exact mul_nonneg (by exact_mod_cast hdiv_nonneg ρ) (le_of_lt (div_pos hnum hden))
  have hSfin : Function.HasFiniteSupport (fun u : ℂ => 5 * (1 - σ) *
      (((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (|τ| + 2)) u : ℤ) : ℝ) *
        ((1 + (1 - σ) - u.re) / ((1 + (1 - σ) - u.re) ^ 2 + (τ - u.im) ^ 2)))) :=
    hRfin.subset (fun u hu => by
      rw [Function.mem_support] at hu ⊢
      intro h
      exact hu (by rw [h, mul_zero]))
  have hLfin : Function.HasFiniteSupport (fun ρ : ℂ =>
      (if analyticOrderNatAt F ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - τ| ≤ (1 - σ) / 2
        then (analyticOrderNatAt F ρ : ℝ) else 0)) :=
    hRfin.subset (fun ρ hρ => by
      rw [Function.mem_support] at hρ ⊢
      have hLnn : 0 ≤ (if analyticOrderNatAt F ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
          |ρ.im - τ| ≤ (1 - σ) / 2 then (analyticOrderNatAt F ρ : ℝ) else 0) := by
        by_cases hc : analyticOrderNatAt F ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - τ| ≤ (1 - σ) / 2
        · rw [if_pos hc]; exact Nat.cast_nonneg _
        · rw [if_neg hc]
      intro hR0
      have hle := hpt ρ
      rw [hR0, mul_zero] at hle
      exact hρ (le_antisymm hle hLnn))
  have key : 5 * (1 - σ) * (∑ᶠ u : ℂ,
      ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (|τ| + 2)) u : ℤ) : ℝ) *
        ((1 + (1 - σ) - u.re) / ((1 + (1 - σ) - u.re) ^ 2 + (τ - u.im) ^ 2)))
      = (∑ᶠ u : ℂ, 5 * (1 - σ) *
          (((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (|τ| + 2)) u : ℤ) : ℝ) *
            ((1 + (1 - σ) - u.re) / ((1 + (1 - σ) - u.re) ^ 2 + (τ - u.im) ^ 2)))) :=
    mul_finsum (fun u : ℂ =>
      ((MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) (|τ| + 2)) u : ℤ) : ℝ) *
        ((1 + (1 - σ) - u.re) / ((1 + (1 - σ) - u.re) ^ 2 + (τ - u.im) ^ 2))) (5 * (1 - σ))
  rw [key]
  exact finsum_le_finsum' hLfin hSfin hpt

/-- Elementary arithmetic for the real-height density lemma: for `q ≥ 2`, `1 ≤ N ≤ q`,
`l = 1-σ ∈ (0,1]` and real `τ`,
`5l(1/l + ½log N + ½log(2+|τ|) + 4) ≤ 25(l·log(q(|τ|+2)) + 1)`. -/
lemma linnikDensityAuxArithGen {q N : ℕ} (hq : 2 ≤ q) (hN1 : 1 ≤ N) (hNq : N ≤ q)
    {l τ : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) :
    5 * l * (1 / l + (1 / 2) * Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |τ|) + 4)
      ≤ 25 * (l * Real.log ((q : ℝ) * (|τ| + 2)) + 1) := by
  have hl_nn : (0 : ℝ) ≤ l := le_of_lt hl0
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNq' : (N : ℝ) ≤ (q : ℝ) := by exact_mod_cast hNq
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hx2 : (2 : ℝ) ≤ |τ| + 2 := by linarith [abs_nonneg τ]
  have harg : (0 : ℝ) < (q : ℝ) * (|τ| + 2) := by nlinarith
  have h4 : (4 : ℝ) ≤ (q : ℝ) * (|τ| + 2) := by nlinarith
  have hlog4 : (1 : ℝ) < Real.log ((q : ℝ) * (|τ| + 2)) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) h4
    have h2 : (1 : ℝ) < Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast
      nlinarith [Real.log_two_gt_d9]
    linarith
  have hlogN : Real.log (N : ℝ) ≤ Real.log ((q : ℝ) * (|τ| + 2)) := by
    apply Real.log_le_log hNpos
    nlinarith [hNq', hx2, hq2]
  have hlogτ : Real.log (2 + |τ|) ≤ Real.log ((q : ℝ) * (|τ| + 2)) := by
    apply Real.log_le_log (by linarith : (0 : ℝ) < 2 + |τ|)
    nlinarith [hx2, hq2]
  have hlA : l ≤ l * Real.log ((q : ℝ) * (|τ| + 2)) := by
    nlinarith [hl_nn, hlog4]
  have hdecomp : 5 * l * (1 / l + (1 / 2) * Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |τ|) + 4)
      = 5 + (5 / 2) * (l * Real.log (N : ℝ)) + (5 / 2) * (l * Real.log (2 + |τ|)) + 20 * l := by
    field_simp
    ring
  have hmain : 5 * l * (1 / l + (1 / 2) * Real.log (N : ℝ) + (1 / 2) * Real.log (2 + |τ|) + 4)
      ≤ 5 + 5 * (l * Real.log ((q : ℝ) * (|τ| + 2))) + 20 * l := by
    rw [hdecomp]
    have h1 : l * Real.log (N : ℝ) ≤ l * Real.log ((q : ℝ) * (|τ| + 2)) :=
      mul_le_mul_of_nonneg_left hlogN hl_nn
    have h2 : l * Real.log (2 + |τ|) ≤ l * Real.log ((q : ℝ) * (|τ| + 2)) :=
      mul_le_mul_of_nonneg_left hlogτ hl_nn
    nlinarith
  have hfin : 5 + 5 * (l * Real.log ((q : ℝ) * (|τ| + 2))) + 20 * l
      ≤ 25 * (l * Real.log ((q : ℝ) * (|τ| + 2)) + 1) := by nlinarith [hlA]
  linarith

/-- **Linnik's density lemma at an arbitrary real height** (Jutila's Lemma 8; Pintz; Ye;
Akbary-Trudgian).  For every non-principal Dirichlet character `χ` mod `q`, every `0 ≤ σ ≤ 1` and
every real `τ`, the multiplicity-weighted number of zeros of the completed `L`-function of the
primitive character inducing `χ` in the square `σ ≤ Re ρ ≤ 1`, `|Im ρ - τ| ≤ (1-σ)/2` is at most
`25·((1-σ)·log(q(|τ|+2)) + 1)`. -/
theorem linnikDensityRealGen :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, [NeZero q] → (χ : DirichletCharacter ℂ q) → χ ≠ 1 →
      ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ 1 →
        (∑ᶠ ρ : ℂ, if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
            |ρ.im - τ| ≤ (1 - σ) / 2 then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
          ≤ C * ((1 - σ) * Real.log ((q : ℝ) * (|τ| + 2)) + 1) := by
  refine ⟨25, by norm_num, ?_⟩
  intro q _inst χ hχ σ τ hσ0 hσ1
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with hq | hq
    · have hqne : q ≠ 0 := NeZero.ne q
      have hq1 : q = 1 := by omega
      subst hq1
      exact absurd (DirichletCharacter.level_one χ) hχ
    · exact hq
  have hN1 : 1 ≤ χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hNq : χ.conductor ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  show (∑ᶠ ρ : ℂ, (if analyticOrderNatAt (primLam χ) ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
      |ρ.im - τ| ≤ (1 - σ) / 2 then (analyticOrderNatAt (primLam χ) ρ : ℝ) else 0))
    ≤ 25 * ((1 - σ) * Real.log ((q : ℝ) * (|τ| + 2)) + 1)
  rcases lt_or_eq_of_le (show (0:ℝ) ≤ 1 - σ by linarith) with hl | hl
  · have hl1 : 1 - σ ≤ 1 := by linarith
    have hbox := linnikDensityAuxBoxGen (primLam χ) (primLam_analytic χ hχ)
      (fun u hu => primLam_zero_strip χ hχ hu) (σ := σ) (τ := τ) hσ0 hσ1
    have hK_eq : (∑ᶠ u : ℂ,
          ((MeromorphicOn.divisor (primLam χ) (Metric.closedBall 0 (|τ| + 2)) u : ℤ) : ℝ) *
            ((1 + (1 - σ) - u.re) / ((1 + (1 - σ) - u.re) ^ 2 + (τ - u.im) ^ 2)))
        = (∑ᶠ u : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
              (Metric.closedBall 0 (|τ| + 2)) u : ℤ) : ℝ) *
              (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * ((τ : ℝ) : ℂ) - u)).re) := by
      refine finsum_congr (fun u => ?_)
      rw [primLam]
      rw [← re_one_div_sub (1 + (1 - σ)) τ u]
    have hKbound : (∑ᶠ u : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 (|τ| + 2)) u : ℤ) : ℝ) *
            (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * ((τ : ℝ) : ℂ) - u)).re)
        ≤ 1 / (1 - σ) + (1 / 2) * Real.log ((χ.conductor : ℕ) : ℝ)
          + (1 / 2) * Real.log (2 + |τ|) + 4 := by
      have hks := kernelSumHalf χ.primitiveCharacter (primitiveCharacter_ne_one χ hχ)
        (DirichletCharacter.primitiveCharacter_isPrimitive χ) (σ := 1 + (1 - σ)) (τ := τ)
        (by linarith) (by linarith) (|τ| + 2)
      rw [show (1 + (1 - σ)) - 1 = 1 - σ by ring] at hks
      exact hks
    have harith := linnikDensityAuxArithGen (q := q) (N := χ.conductor) (l := 1 - σ) (τ := τ)
      hq2 hN1 hNq hl hl1
    calc (∑ᶠ ρ : ℂ, (if analyticOrderNatAt (primLam χ) ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
            |ρ.im - τ| ≤ (1 - σ) / 2 then (analyticOrderNatAt (primLam χ) ρ : ℝ) else 0))
        ≤ 5 * (1 - σ) * (∑ᶠ u : ℂ,
            ((MeromorphicOn.divisor (primLam χ) (Metric.closedBall 0 (|τ| + 2)) u : ℤ) : ℝ) *
              ((1 + (1 - σ) - u.re) / ((1 + (1 - σ) - u.re) ^ 2 + (τ - u.im) ^ 2))) := hbox
      _ = 5 * (1 - σ) * (∑ᶠ u : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
              (Metric.closedBall 0 (|τ| + 2)) u : ℤ) : ℝ) *
              (1 / (((1 + (1 - σ) : ℝ) : ℂ) + Complex.I * ((τ : ℝ) : ℂ) - u)).re) := by
            rw [hK_eq]
      _ ≤ 5 * (1 - σ) * (1 / (1 - σ) + (1 / 2) * Real.log ((χ.conductor : ℕ) : ℝ)
            + (1 / 2) * Real.log (2 + |τ|) + 4) :=
            mul_le_mul_of_nonneg_left hKbound (by linarith)
      _ ≤ 25 * ((1 - σ) * Real.log ((q : ℝ) * (|τ| + 2)) + 1) := harith
  · have hJ0 : (∑ᶠ ρ : ℂ, (if analyticOrderNatAt (primLam χ) ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
        |ρ.im - τ| ≤ (1 - σ) / 2 then (analyticOrderNatAt (primLam χ) ρ : ℝ) else 0)) = 0 := by
      rw [show (∑ᶠ ρ : ℂ, (if analyticOrderNatAt (primLam χ) ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
            |ρ.im - τ| ≤ (1 - σ) / 2 then (analyticOrderNatAt (primLam χ) ρ : ℝ) else 0))
          = ∑ᶠ ρ : ℂ, (0 : ℝ) from
        finsum_congr (fun ρ => by
          refine if_neg ?_
          rintro ⟨hzm, h1, h2, -⟩
          have hρ0 : primLam χ ρ = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hzm
          have hlt := (primLam_zero_strip χ hχ hρ0).2
          have hσeq : σ = 1 := by linarith
          linarith)]
      simp
    rw [hJ0, hl.symm]
    simp

/-! ## The per-box mass bound -/

/-- **Reduction of the per-box mass bound to a density lemma at an arbitrary real height.**

If Linnik's density lemma holds with an arbitrary real centre `τ` (the form
`C·((1-σ)·log(q(|τ|+2)) + 1)`), then the mass of a single box `⌊ρ.im/Δ⌋ = k` of width
`Δ ≤ (1-σ)/2`, intersected with `|Im ρ| ≤ T`, is bounded by `2C·((1-σ)·log(q(T+1)) + 1)`.

The box `[kΔ,(k+1)Δ) ∩ [-T,T]` is contained in the square of half-width `(1-σ)/2` centred at
`τ = max(kΔ, -T) + (1-σ)/2`; that centre satisfies `|τ| ≤ T + 1/10`, so its log is comparable
with `log(q(T+1))`. -/
theorem boxMass_le_linnikLocal_of_realBound
    (h : ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, [NeZero q] → (χ : DirichletCharacter ℂ q) → χ ≠ 1 →
      ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ 1 →
        (∑ᶠ ρ : ℂ, if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
            |ρ.im - τ| ≤ (1 - σ) / 2 then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
          ≤ C * ((1 - σ) * Real.log ((q : ℝ) * (|τ| + 2)) + 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ σ T Δ : ℝ, (4 : ℝ) / 5 ≤ σ → σ ≤ 1 → 1 ≤ T → 0 < Δ → Δ ≤ (1 - σ) / 2 → ∀ k : ℤ,
        (∑ᶠ ρ : ℂ, if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ ⌊ρ.im / Δ⌋ = k
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
        ≤ C * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1) := by
  obtain ⟨C₀, hC₀, hbnd⟩ := h
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro q hq inst χ hχ σ T Δ h45 hσ1 hT hΔpos hΔle k
  have hσ0 : 0 ≤ σ := by linarith
  have hlam0 : 0 ≤ 1 - σ := by linarith
  have hlamle : 1 - σ ≤ 1 / 5 := by linarith
  set a : ℝ := max ((k : ℝ) * Δ) (-T) with hadef
  set tau : ℝ := a + (1 - σ) / 2 with htaudef
  by_cases hbig : T < a
  · -- the box is empty: any point in it would have `Im ρ ≥ a > T`
    have ha_eq : a = (k : ℝ) * Δ := by
      rw [hadef]
      rcases le_total ((k : ℝ) * Δ) (-T) with hle | hle
      · exfalso
        have hsub : a = -T := by rw [hadef, max_eq_right hle]
        rw [hsub] at hbig; linarith
      · exact max_eq_left hle
    have hzero : (∑ᶠ ρ : ℂ, if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ ⌊ρ.im / Δ⌋ = k
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) = 0 := by
      rw [show (∑ᶠ ρ : ℂ, (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ ⌊ρ.im / Δ⌋ = k
            then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)) = ∑ᶠ ρ : ℂ, (0 : ℝ) from
        finsum_congr (fun ρ => by
          refine if_neg ?_
          rintro ⟨-, -, him, hfl⟩
          have hlb := (im_box_bounds hΔpos hfl).1
          have him' : ρ.im ≤ T := (abs_le.mp him).2
          rw [ha_eq] at hbig
          linarith)]
      simp
    rw [hzero]
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
    have hL : 0 ≤ Real.log ((q : ℝ) * (T + 1)) :=
      Real.log_nonneg (by nlinarith)
    have hpos : 0 ≤ (1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1 := by nlinarith [hL, hlam0]
    nlinarith [hpos, hC₀]
  · push_neg at hbig
    have ha_ge : -T ≤ a := by rw [hadef]; exact le_max_right _ _
    have ha_abs : |a| ≤ T := abs_le.mpr ⟨ha_ge, hbig⟩
    have htau_abs : |tau| ≤ T + (1 - σ) / 2 := by
      have h2 : |(1 - σ) / 2| = (1 - σ) / 2 := abs_of_nonneg (by linarith)
      rw [htaudef]
      calc |a + (1 - σ) / 2| ≤ |a| + |(1 - σ) / 2| := abs_add_le _ _
        _ = |a| + (1 - σ) / 2 := by rw [h2]
        _ ≤ T + (1 - σ) / 2 := by linarith
    -- containment of the box in the square of half-width `(1-σ)/2` centred at `tau`
    have hcont : ∀ ρ : ℂ, σ ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ T → ⌊ρ.im / Δ⌋ = k →
        |ρ.im - tau| ≤ (1 - σ) / 2 := by
      intro ρ _ _ him hfl
      obtain ⟨hlb, hub⟩ := im_box_bounds hΔpos hfl
      have hTlow : -T ≤ ρ.im := (abs_le.mp him).1
      have hge : a ≤ ρ.im := by rw [hadef]; exact max_le hlb hTlow
      have hΔl : Δ ≤ 1 - σ := by linarith
      have hhub : ((k : ℝ) + 1) * Δ = (k : ℝ) * Δ + Δ := by ring
      have hlt : ρ.im < a + (1 - σ) := by
        rw [hadef]
        rcases le_total ((k : ℝ) * Δ) (-T) with hle | hle
        · rw [max_eq_right hle]; rw [hhub] at hub; linarith
        · rw [max_eq_left hle]; rw [hhub] at hub; linarith
      rw [htaudef]
      rw [abs_le]
      constructor <;> linarith
    -- finite supports
    have hf_supp : Function.HasFiniteSupport (fun ρ : ℂ =>
        if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ ⌊ρ.im / Δ⌋ = k
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) :=
      (zeroSupport_finite' χ σ T).subset (by
        intro ρ hρ
        rw [Function.mem_support] at hρ ⊢
        by_cases hc : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ ⌊ρ.im / Δ⌋ = k
        · rw [if_pos hc] at hρ
          rw [if_pos ⟨hc.1, hc.2.1, hc.2.2.1⟩]
          exact hρ
        · rw [if_neg hc] at hρ; exact absurd rfl hρ)
    have hg_supp : Function.HasFiniteSupport (fun ρ : ℂ =>
        if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
            |ρ.im - tau| ≤ (1 - σ) / 2 then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) :=
      (zeroSupport_finite' χ σ (|tau| + 1)).subset (by
        intro ρ hρ
        rw [Function.mem_support] at hρ ⊢
        by_cases hc : Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
            |ρ.im - tau| ≤ (1 - σ) / 2
        · rw [if_pos hc] at hρ
          have him : |ρ.im| ≤ |tau| + 1 := by
            have h2 : (1 - σ) / 2 ≤ 1 / 2 := by linarith
            calc |ρ.im| = |(ρ.im - tau) + tau| := by ring_nf
              _ ≤ |ρ.im - tau| + |tau| := abs_add_le _ _
              _ ≤ 1 / 2 + |tau| := by linarith [hc.2.2.2]
              _ ≤ |tau| + 1 := by linarith
          rw [if_pos ⟨hc.2.1, hc.2.2.1, him⟩]
          exact hρ
        · rw [if_neg hc] at hρ; exact absurd rfl hρ)
    -- pointwise domination
    have hpoint : ∀ ρ : ℂ,
        (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ ⌊ρ.im / Δ⌋ = k
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
        ≤ (if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
            |ρ.im - tau| ≤ (1 - σ) / 2 then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) := by
      intro ρ
      by_cases hc : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ ⌊ρ.im / Δ⌋ = k
      · rw [if_pos hc]
        obtain ⟨hr1, hr2, him, hfl⟩ := hc
        have hc' := hcont ρ hr1 hr2 him hfl
        by_cases hzm : Work.LinnikContract.zeroMult χ ρ = 0
        · rw [hzm]; simp
        · rw [if_pos ⟨hzm, hr1, hr2, hc'⟩]
      · rw [if_neg hc]
        by_cases hcc : Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
            |ρ.im - tau| ≤ (1 - σ) / 2
        · rw [if_pos hcc]; exact Nat.cast_nonneg _
        · rw [if_neg hcc]
    have hle1 := finsum_le_finsum' hf_supp hg_supp hpoint
    have hle2 := hbnd q χ hχ σ tau hσ0 hσ1
    -- compare the logarithms
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hqT : (0 : ℝ) < (q : ℝ) * (T + 1) := by nlinarith
    have h3 : (3 : ℝ) ≤ (q : ℝ) * (T + 1) := by nlinarith
    have htau2 : |tau| + 2 ≤ 3 * (T + 1) := by
      have h16 : (1 - σ) / 2 ≤ 1 / 10 := by linarith
      linarith [htau_abs, hT]
    have hle_mul : (q : ℝ) * (|tau| + 2) ≤ 3 * ((q : ℝ) * (T + 1)) := by
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := by linarith
      nlinarith [htau2, hq0]
    have hlog : Real.log ((q : ℝ) * (|tau| + 2)) ≤ 2 * Real.log ((q : ℝ) * (T + 1)) := by
      have hpos : (0 : ℝ) < (q : ℝ) * (|tau| + 2) := by
        have : (0 : ℝ) < |tau| + 2 := by positivity
        nlinarith [hq1]
      calc Real.log ((q : ℝ) * (|tau| + 2)) ≤ Real.log (3 * ((q : ℝ) * (T + 1))) :=
            Real.log_le_log hpos hle_mul
        _ = Real.log 3 + Real.log ((q : ℝ) * (T + 1)) :=
            Real.log_mul (by norm_num) (ne_of_gt hqT)
        _ ≤ 2 * Real.log ((q : ℝ) * (T + 1)) := by
            have h33 : Real.log 3 ≤ Real.log ((q : ℝ) * (T + 1)) :=
              Real.log_le_log (by norm_num) h3
            linarith
    have hfinal : C₀ * ((1 - σ) * Real.log ((q : ℝ) * (|tau| + 2)) + 1)
        ≤ 2 * C₀ * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1) := by
      have h1 : (1 - σ) * Real.log ((q : ℝ) * (|tau| + 2))
          ≤ (1 - σ) * (2 * Real.log ((q : ℝ) * (T + 1))) :=
        mul_le_mul_of_nonneg_left hlog hlam0
      nlinarith [h1, hC₀]
    calc (∑ᶠ ρ : ℂ, if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ ⌊ρ.im / Δ⌋ = k
            then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
        ≤ (∑ᶠ ρ : ℂ, if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
            |ρ.im - tau| ≤ (1 - σ) / 2 then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) := hle1
      _ ≤ C₀ * ((1 - σ) * Real.log ((q : ℝ) * (|tau| + 2)) + 1) := hle2
      _ ≤ 2 * C₀ * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1) := hfinal

theorem boxMass_le_linnikLocal :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ σ T Δ : ℝ, (4 : ℝ) / 5 ≤ σ → σ ≤ 1 → 1 ≤ T → 0 < Δ → Δ ≤ (1 - σ) / 2 → ∀ k : ℤ,
        (∑ᶠ ρ : ℂ, if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ ⌊ρ.im / Δ⌋ = k
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
        ≤ C * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1) :=
  boxMass_le_linnikLocal_of_realBound linnikDensityRealGen

end Work.ZeroDensity.Jutila
