/-
# `OffAxis/invNearSum_eq_tsum_gen` — the near-zero sum `InvNearSum` is the `tsum` `nearInvSum`

HB Lemma 3.1's near-zero sum

  `InvNearSum N χ s δ = ∑ᶠ u, ((pdiv N χ s u : ℤ) : ℝ) * (if ‖1 + i·Im s - u‖ ≤ δ then (1/(s-u)).re else 0)`

is defined as a *finite* sum over the divisor of the completed `L`-function on the ball
`closedBall 0 (|s.im| + 2)`, while the engine of HB §9 uses the manifestly `tsum`-shaped

  `P9.nearInvSum N χ s δ = ∑' u, (zeroMult χ u : ℝ) * nearInd s δ u * (1/(s-u)).re`.

This file proves the two agree for **every** `s` (the companion result
`Work.ZeroFreeTables.P9.invNearSum_eq_tsum` states the same identity but carries a spurious
hypothesis `|s.im| ≤ 10`; its proof never uses it, and the argument below is the same one,
without that hypothesis). Concretely:

* for a primitive, non-principal `χ`, `pdiv N χ s` is the multiplicity function `zeroMult χ`
  on the closed ball `closedBall 0 (|s.im| + 2)`, and `0` outside it;
* every point with `‖1 + i·Im s - u‖ ≤ δ` and `δ ≤ 1` lies in that ball (indeed in
  `closedBall 0 (|s.im| + 2)`), so the `nearInd`-weighted summands are supported where the two
  multiplicity functions agree;
* the `nearInd`-weighted summand is finitely supported, so the `tsum` collapses to a `finsum`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P9.invNearSum_eq_tsum

namespace Work.ZeroFreeTables.OffAxis

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

/-- The divisor of an analytic function `f` at a point of its domain `U` equals the
vanishing order `analyticOrderNatAt f z` (as an integer). -/
private lemma divisor_eq_order {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hz : z ∈ U) :
    MeromorphicOn.divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz]
  simp only [analyticOrderNatAt]
  cases h : analyticOrderAt f z with
  | top => simp
  | coe n => simp

/-- Points within `δ ≤ 1` of `1 + i·Im s` lie in the closed ball of radius `|s.im| + 2`. -/
private lemma mem_closedBall_of_near {s u : ℂ} {δ : ℝ} (hδ1 : δ ≤ 1)
    (hnear : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ) :
    u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2) := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have h3 : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ ≤ 1 + |s.im| := by
    calc ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖
        ≤ ‖(1 : ℂ)‖ + ‖(s.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = 1 + |s.im| := by simp
  calc ‖u‖ ≤ ‖u - ((1 : ℂ) + (s.im : ℂ) * Complex.I)‖
              + ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ := by
        have hh := norm_add_le (u - ((1 : ℂ) + (s.im : ℂ) * Complex.I))
          ((1 : ℂ) + (s.im : ℂ) * Complex.I)
        simpa using hh
    _ = ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖
              + ‖(1 : ℂ) + (s.im : ℂ) * Complex.I‖ := by rw [norm_sub_rev]
    _ ≤ δ + (1 + |s.im|) := by linarith
    _ ≤ 1 + (1 + |s.im|) := by linarith
    _ = |s.im| + 2 := by ring

/-- For a primitive, non-principal `χ`, the divisor of `Λ(χ,·)` on the ball of the near-sum
equals `zeroMult` on the ball and `0` outside it. -/
private lemma pdiv_apply {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (s u : ℂ) :
    Work.ZeroFreeTables.pdiv N χ s u
      = if u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2)
          then (Work.LinnikContract.zeroMult χ u : ℤ) else 0 := by
  unfold Work.ZeroFreeTables.pdiv
  by_cases hu : u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2)
  · rw [if_pos hu]
    have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (|s.im| + 2)) :=
      fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
    rw [divisor_eq_order hAn hu,
      ← Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive χ hprim u]
  · rw [if_neg hu, MeromorphicOn.divisor_def]
    simp [hu]

theorem invNearSum_eq_tsum_gen {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {s : ℂ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Work.ZeroFreeTables.InvNearSum N χ s δ = Work.ZeroFreeTables.P9.nearInvSum N χ s δ := by
  -- the two summands agree pointwise
  have hfg : (fun u : ℂ => ((Work.ZeroFreeTables.pdiv N χ s u : ℤ) : ℝ) *
        (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1 / (s - u)).re) else 0))
      = (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * P9.nearInd s δ u
        * ((1 / (s - u)).re)) := by
    funext u
    rw [pdiv_apply χ hχ hprim s u]
    by_cases hu : u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 2)
    · rw [if_pos hu]
      by_cases hnr : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
      · rw [if_pos hnr, P9.nearInd_eq_ite, if_pos hnr]; push_cast; ring
      · rw [if_neg hnr, P9.nearInd_eq_ite, if_neg hnr]; push_cast; ring
    · rw [if_neg hu]
      have hnr : ¬ (‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ) :=
        fun hc => hu (mem_closedBall_of_near hδ1 hc)
      rw [if_neg hnr, P9.nearInd_eq_ite, if_neg hnr]; push_cast; ring
  -- the summand of `nearInvSum` is finitely supported
  have hsupp : Function.HasFiniteSupport
      (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * P9.nearInd s δ u
        * ((1 / (s - u)).re)) := by
    have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (|s.im| + 2)) :=
      fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
    have hfinDiv : (Function.support (fun u : ℂ => MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (|s.im| + 2)) u)).Finite := by
      simpa [Function.HasFiniteSupport] using
        (MeromorphicOn.divisor_support_finite_of_subset
          (f := DirichletCharacter.completedLFunction χ)
          (U := Metric.closedBall (0 : ℂ) (|s.im| + 2))
          (V := Metric.closedBall (0 : ℂ) (|s.im| + 2))
          hAn.meromorphicOn (isCompact_closedBall (0 : ℂ) (|s.im| + 2)) (le_refl _))
    rw [Function.HasFiniteSupport]
    refine hfinDiv.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    have hzm : Work.LinnikContract.zeroMult χ u ≠ 0 := by
      intro h0; exact hu (by simp [h0])
    have hni : P9.nearInd s δ u ≠ 0 := by
      intro h0; exact hu (by simp [h0])
    have hnear : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ := by
      by_contra hc
      exact hni (by rw [P9.nearInd_eq_ite, if_neg hc])
    have huU := mem_closedBall_of_near hδ1 hnear
    rw [divisor_eq_order hAn huU,
      ← Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive χ hprim u]
    exact_mod_cast hzm
  unfold Work.ZeroFreeTables.InvNearSum Work.ZeroFreeTables.P9.nearInvSum
  rw [hfg]
  exact (tsum_eq_finsum hsupp).symm

end

end Work.ZeroFreeTables.OffAxis
