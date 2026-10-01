import Mathlib
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive

open DirichletCharacter Complex
open scoped Classical BigOperators

namespace Work.ZeroFreeTables.P9.prim

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

theorem nearP3sum_split {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {s : ℂ} {a lam₁ δ L : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 1 < s.re) (hsδ : s.re ≤ 1 + δ / 2) (hsum2 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2)) (hsum3 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 3)) : Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ = ((a + lam₁) / L) * Work.ZeroFreeTables.P9.nearInvSum N χ s δ + ((a + lam₁) / L) ^ 2 * (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * Work.ZeroFreeTables.P9.nearInd s δ u * ((1 / (s - u)) ^ 2).re) + (2 / 3) * ((a + lam₁) / L) ^ 3 * (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * Work.ZeroFreeTables.P9.nearInd s δ u * ((1 / (s - u)) ^ 3).re) := by
  have hδ1' : δ ≤ 1 := le_of_lt hδ1
  -- analyticity of the completed L-function on the big ball
  have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (|s.im| + 2)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  -- the divisor has finite support on the big ball
  have hfinDiv : (Function.support (fun u : ℂ => MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (|s.im| + 2)) u)).Finite := by
    simpa [Function.HasFiniteSupport] using
      (MeromorphicOn.divisor_support_finite_of_subset
        (f := DirichletCharacter.completedLFunction χ)
        (U := Metric.closedBall (0 : ℂ) (|s.im| + 2))
        (V := Metric.closedBall (0 : ℂ) (|s.im| + 2))
        hAn.meromorphicOn (isCompact_closedBall (0 : ℂ) (|s.im| + 2)) (le_refl _))
  -- the weight `zeroMult · nearInd` has finite support
  have hfin0 : (Function.support (fun u : ℂ =>
      (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u)).Finite := by
    refine hfinDiv.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    have hzm : Work.LinnikContract.zeroMult χ u ≠ 0 := fun h0 => hu (by simp [h0])
    have hni : nearInd s δ u ≠ 0 := fun h0 => hu (by simp [h0])
    have hnear : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ := by
      by_contra hc
      exact hni (by rw [nearInd_eq_ite, if_neg hc])
    have huU := mem_closedBall_of_near hδ1' hnear
    rw [divisor_eq_order hAn huU,
      ← Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive χ hprim u]
    exact_mod_cast hzm
  -- hence any weighted product has finite support
  have hsupp : ∀ F : ℂ → ℝ, Function.HasFiniteSupport
      (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u * F u) := by
    intro F
    rw [Function.HasFiniteSupport]
    refine hfin0.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by rw [h0, zero_mul])
  have hS1 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u *
      ((1 / (s - u)).re)) := summable_of_hasFiniteSupport (hsupp _)
  have hS2 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u *
      ((1 / (s - u)) ^ 2).re) := summable_of_hasFiniteSupport (hsupp _)
  have hS3 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u *
      ((1 / (s - u)) ^ 3).re) := summable_of_hasFiniteSupport (hsupp _)
  -- pointwise splitting of the summand
  have hpt : ∀ u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u *
      ( ((a + lam₁) / L) * ((1 / (s - u))).re
        + ((a + lam₁) / L) ^ 2 * ((1 / (s - u)) ^ 2).re
        + (2 / 3) * ((a + lam₁) / L) ^ 3 * ((1 / (s - u)) ^ 3).re)
      = ((a + lam₁) / L) * ((Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u * ((1 / (s - u))).re)
        + (((a + lam₁) / L) ^ 2 * ((Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u * ((1 / (s - u)) ^ 2).re)
          + (2 / 3) * ((a + lam₁) / L) ^ 3 * ((Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u * ((1 / (s - u)) ^ 3).re)) := by
    intro u; ring
  have key : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u *
      ( ((a + lam₁) / L) * ((1 / (s - u))).re
        + ((a + lam₁) / L) ^ 2 * ((1 / (s - u)) ^ 2).re
        + (2 / 3) * ((a + lam₁) / L) ^ 3 * ((1 / (s - u)) ^ 3).re))
      = ((a + lam₁) / L) * (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u * ((1 / (s - u))).re)
        + ((a + lam₁) / L) ^ 2 * (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u * ((1 / (s - u)) ^ 2).re)
        + (2 / 3) * ((a + lam₁) / L) ^ 3 * (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u * ((1 / (s - u)) ^ 3).re) := by
    rw [tsum_congr hpt]
    rw [Summable.tsum_add (hS1.mul_left _) ((hS2.mul_left _).add (hS3.mul_left _))]
    rw [tsum_mul_left]
    rw [Summable.tsum_add (hS2.mul_left _) (hS3.mul_left _)]
    rw [tsum_mul_left, tsum_mul_left]
    ring
  unfold Work.ZeroFreeTables.P9.nearP3sum Work.ZeroFreeTables.P9.nearInvSum
  exact key

/-- Points within `δ` of `1 + i·Im s` lie in the closed ball of radius `|s.im| + 1 + δ`.
No hypothesis on `δ` is needed (the bound is vacuous when the half-space is empty). -/
private lemma mem_closedBall_of_near_gen {s u : ℂ} {δ : ℝ}
    (hnear : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ) :
    u ∈ Metric.closedBall (0 : ℂ) (|s.im| + 1 + δ) := by
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
    _ = |s.im| + 1 + δ := by ring

/-- **Structural (hypothesis-free) form of the `nearP3sum` splitting.**

The identity exhibited by `nearP3sum_split` is purely structural: it only needs that the
weight `u ↦ zeroMult χ u · nearInd s δ u` has *finite support* (the near window
`‖1 + i·Im s - u‖ ≤ δ` is bounded, the zeros of the completed `L`-function are isolated and
`zeroMult = analyticOrderNatAt` for primitive `χ`).  Consequently none of the analytic
hypotheses of `nearP3sum_split` — summability of the square/cube zero sums, `1 < Re s`,
`Re s ≤ 1 + δ/2`, `0 < δ`, `δ < 1` — is used, and the splitting holds for **arbitrary**
`δ : ℝ`, `s : ℂ`, `L : ℝ`, `a, lam₁ : ℝ`. -/
theorem nearP3sum_split_gen {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {s : ℂ} {a lam₁ δ L : ℝ} :
    Work.ZeroFreeTables.P9.nearP3sum N L χ s a lam₁ δ = ((a + lam₁) / L) * Work.ZeroFreeTables.P9.nearInvSum N χ s δ + ((a + lam₁) / L) ^ 2 * (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * Work.ZeroFreeTables.P9.nearInd s δ u * ((1 / (s - u)) ^ 2).re) + (2 / 3) * ((a + lam₁) / L) ^ 3 * (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * Work.ZeroFreeTables.P9.nearInd s δ u * ((1 / (s - u)) ^ 3).re) := by
  -- analyticity of the completed L-function on the big ball
  have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (|s.im| + 1 + δ)) :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  -- the divisor has finite support on the big ball
  have hfinDiv : (Function.support (fun u : ℂ => MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall (0 : ℂ) (|s.im| + 1 + δ)) u)).Finite := by
    simpa [Function.HasFiniteSupport] using
      (MeromorphicOn.divisor_support_finite_of_subset
        (f := DirichletCharacter.completedLFunction χ)
        (U := Metric.closedBall (0 : ℂ) (|s.im| + 1 + δ))
        (V := Metric.closedBall (0 : ℂ) (|s.im| + 1 + δ))
        hAn.meromorphicOn (isCompact_closedBall (0 : ℂ) (|s.im| + 1 + δ)) (le_refl _))
  -- the weight `zeroMult · nearInd` has finite support
  have hfin0 : (Function.support (fun u : ℂ =>
      (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u)).Finite := by
    refine hfinDiv.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    have hzm : Work.LinnikContract.zeroMult χ u ≠ 0 := fun h0 => hu (by simp [h0])
    have hni : nearInd s δ u ≠ 0 := fun h0 => hu (by simp [h0])
    have hnear : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ := by
      by_contra hc
      exact hni (by rw [nearInd_eq_ite, if_neg hc])
    have huU := mem_closedBall_of_near_gen hnear
    rw [divisor_eq_order hAn huU,
      ← Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive χ hprim u]
    exact_mod_cast hzm
  -- hence any weighted product has finite support
  have hsupp : ∀ F : ℂ → ℝ, Function.HasFiniteSupport
      (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u * F u) := by
    intro F
    rw [Function.HasFiniteSupport]
    refine hfin0.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by rw [h0, zero_mul])
  have hS1 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u *
      ((1 / (s - u)).re)) := summable_of_hasFiniteSupport (hsupp _)
  have hS2 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u *
      ((1 / (s - u)) ^ 2).re) := summable_of_hasFiniteSupport (hsupp _)
  have hS3 : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u *
      ((1 / (s - u)) ^ 3).re) := summable_of_hasFiniteSupport (hsupp _)
  -- pointwise splitting of the summand
  have hpt : ∀ u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u *
      ( ((a + lam₁) / L) * ((1 / (s - u))).re
        + ((a + lam₁) / L) ^ 2 * ((1 / (s - u)) ^ 2).re
        + (2 / 3) * ((a + lam₁) / L) ^ 3 * ((1 / (s - u)) ^ 3).re)
      = ((a + lam₁) / L) * ((Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u * ((1 / (s - u))).re)
        + (((a + lam₁) / L) ^ 2 * ((Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u * ((1 / (s - u)) ^ 2).re)
          + (2 / 3) * ((a + lam₁) / L) ^ 3 * ((Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u * ((1 / (s - u)) ^ 3).re)) := by
    intro u; ring
  have key : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u *
      ( ((a + lam₁) / L) * ((1 / (s - u))).re
        + ((a + lam₁) / L) ^ 2 * ((1 / (s - u)) ^ 2).re
        + (2 / 3) * ((a + lam₁) / L) ^ 3 * ((1 / (s - u)) ^ 3).re))
      = ((a + lam₁) / L) * (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u * ((1 / (s - u))).re)
        + ((a + lam₁) / L) ^ 2 * (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u * ((1 / (s - u)) ^ 2).re)
        + (2 / 3) * ((a + lam₁) / L) ^ 3 * (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * nearInd s δ u * ((1 / (s - u)) ^ 3).re) := by
    rw [tsum_congr hpt]
    rw [Summable.tsum_add (hS1.mul_left _) ((hS2.mul_left _).add (hS3.mul_left _))]
    rw [tsum_mul_left]
    rw [Summable.tsum_add (hS2.mul_left _) (hS3.mul_left _)]
    rw [tsum_mul_left, tsum_mul_left]
    ring
  unfold Work.ZeroFreeTables.P9.nearP3sum Work.ZeroFreeTables.P9.nearInvSum
  exact key

end Work.ZeroFreeTables.P9.prim
