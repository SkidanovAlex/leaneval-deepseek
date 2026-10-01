import Mathlib
import Submission.Work.LinnikAreas.Zeta1Aux.CommonsImports
import Submission.Work.LinnikAreas.Zeta1Aux.divisor_ne_zero_imp
import Submission.Work.LinnikAreas.Zeta1Aux.finsum_intCast_div_sub_bound

open Complex Metric
open scoped Real Topology BigOperators

namespace Work.LinnikAreas.Zeta1Aux

/-- **Bound for the divisor sum of the Borel–Carathéodory decomposition.**

Let `C₀ > 0` and suppose that for every real `t` with `|t| ≥ 1` the weighted zero count
`∑ᶠ u, d(|t|+6, u) · [|u.im - t| ≤ 3]` inside the ball `‖u‖ ≤ |t| + 6` is at most
`C₀ · log(|t| + 3)` (`d(r,·)` being `MeromorphicOn.divisor riemannZeta₁ (closedBall 0 r)`).
Then for real `v, δ, R, x` with `|v| ≥ 7`, `δ > 0`, `0 < R ≤ 6`, and such that every
zero `ρ` of `ζ₁` satisfies `δ ≤ |ρ.im - v|` one has

  `‖∑ᶠ u, d_{c,R/2}(u)/(s - u)‖ ≤ C₀/δ · log(|v| + 3)`,   `c = 2 + i v`, `s = x + i v`.

Route: the summands are supported on the zeros `u` of `ζ₁` with `‖u - c‖ ≤ R/2`;
such `u` satisfy `|u.im - v| ≤ R/2 ≤ 3`, hence `‖s - u‖ ≥ |Im(s - u)| ≥ δ`, so
`‖·‖ ≤ (1/δ) ∑ᶠ u, d_{c,R/2}(u)` by the triangle inequality applied to the (absolutely
convergent, finitely supported) finsum.  Moreover every such `u` also lies in
`closedBall 0 (|v| + 6)` (as `‖u‖ ≤ ‖c‖ + R/2 ≤ |v| + 5`) and the two divisors agree
there (`Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset`), so
`∑ᶠ u, d_{c,R/2}(u) ≤ ∑ᶠ u, d(|v|+6, u)·[|u.im - v| ≤ 3]`
and `hcount` at `t = v` finishes. -/
lemma zeta1_divisor_sum_bound {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hcount : ∀ t : ℝ, 1 ≤ |t| →
      (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|t| + 6))) u : ℤ) : ℝ) *
          (if |u.im - t| ≤ 3 then 1 else 0)) ≤ C₀ * Real.log (|t| + 3))
    {v δ R x : ℝ} (hv : 7 ≤ |v|) (hδ : 0 < δ) (hRpos : 0 < R) (hRhi : R ≤ 6)
    (hsep : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - v|) :
    ‖∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor riemannZeta₁
            (Metric.closedBall ((2 : ℂ) + Complex.I * (v : ℂ)) (R / 2))) u : ℤ) : ℂ) *
          (1 / (((x : ℂ) + (v : ℂ) * Complex.I) - u))‖ ≤ C₀ / δ * Real.log (|v| + 3) := by
  classical
  -- Abbreviate the centre `c = 2 + i v`, the point `s = x + i v` and the two divisors.
  set c : ℂ := (2 : ℂ) + Complex.I * (v : ℂ) with hc
  set s : ℂ := (x : ℂ) + (v : ℂ) * Complex.I with hs
  set S : ℂ → ℤ := ⇑(MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (R / 2))) with hS
  set T : ℂ → ℤ :=
    ⇑(MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|v| + 6))) with hT
  -- `ζ₁` is entire, so its divisors on balls are nonnegative and finitely supported.
  have han : AnalyticOnNhd ℂ riemannZeta₁ Set.univ :=
    fun z _ => differentiable_riemannZeta₁.analyticAt z
  have hSnn : ∀ u, 0 ≤ S u :=
    fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg (han.mono (Set.subset_univ _)) u
  have hTnn : ∀ u, 0 ≤ T u :=
    fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg (han.mono (Set.subset_univ _)) u
  have hTfin : T.support.Finite :=
    (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall (0 : ℂ) (|v| + 6))).finiteSupport
      (isCompact_closedBall _ _)
  have hSfin : S.support.Finite :=
    (MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (R / 2))).finiteSupport
      (isCompact_closedBall _ _)
  -- Where the divisor `S` does not vanish: the point is a zero of `ζ₁` lying in the ball.
  have hmem1 : ∀ u, S u ≠ 0 → u ∈ Metric.closedBall c (R / 2) :=
    fun u hu => (divisor_ne_zero_imp differentiable_riemannZeta₁ hu).2
  have hzero : ∀ u, S u ≠ 0 → riemannZeta₁ u = 0 :=
    fun u hu => (divisor_ne_zero_imp differentiable_riemannZeta₁ hu).1
  -- Geometric consequences of `‖u - c‖ ≤ R/2` and `R ≤ 6`.
  have hgeom : ∀ u, S u ≠ 0 → u ∈ Metric.closedBall (0 : ℂ) (|v| + 6) ∧ |u.im - v| ≤ 3 := by
    intro u hu
    have h1 := hmem1 u hu
    have h2 : ‖u - c‖ ≤ R / 2 := by
      have := Metric.mem_closedBall.mp h1; rwa [dist_eq_norm] at this
    have him : |u.im - v| ≤ R / 2 := by
      have h3 : |(u - c).im| ≤ ‖u - c‖ := Complex.abs_im_le_norm _
      have h4 : (u - c).im = u.im - v := by simp [hc]
      rw [h4] at h3
      linarith
    refine ⟨?_, by linarith⟩
    have hc6 : ‖c‖ ≤ |v| + 2 := by
      rw [hc]
      calc ‖(2 : ℂ) + Complex.I * (v : ℂ)‖
          ≤ ‖(2 : ℂ)‖ + ‖Complex.I * (v : ℂ)‖ := norm_add_le _ _
        _ = 2 + |v| := by simp
        _ = |v| + 2 := by ring
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    calc ‖u‖ = ‖(u - c) + c‖ := by ring_nf
      _ ≤ ‖u - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ |v| + 6 := by linarith
  -- On that set the two divisors agree.
  have hagree : ∀ u, S u ≠ 0 → S u = T u :=
    fun u hu => Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset (f := riemannZeta₁)
      (fun z _ => differentiable_riemannZeta₁.analyticAt z) (hmem1 u hu) (hgeom u hu).1
  -- The separation hypothesis upgrades to a lower bound for `‖s - u‖`.
  have hdist : ∀ u, S u ≠ 0 → δ ≤ ‖s - u‖ := by
    intro u hu
    have h1 : |(s - u).im| ≤ ‖s - u‖ := Complex.abs_im_le_norm _
    have h2 : (s - u).im = v - u.im := by simp [hs]
    rw [h2] at h1
    have h3 : δ ≤ |u.im - v| := hsep u (hzero u hu)
    have h4 : |v - u.im| = |u.im - v| := abs_sub_comm _ _
    linarith
  -- The `T`-weighted, window-restricted zero count dominates the `S`-sum.
  have hsupR : Function.support (fun u : ℂ => ((S u : ℤ) : ℝ)) ⊆ T.support := by
    intro u hu
    rw [Function.mem_support] at hu ⊢
    have hS0 : S u ≠ 0 := by intro h; exact hu (by rw [h]; simp)
    rw [← hagree u hS0]
    exact hS0
  have hsupT : Function.support
      (fun u : ℂ => ((T u : ℤ) : ℝ) * (if |u.im - v| ≤ 3 then 1 else 0)) ⊆ T.support := by
    intro u hu
    by_contra h
    have h0 : T u = 0 := Function.notMem_support.mp h
    rw [Function.mem_support, h0] at hu
    simp at hu
  have hfinS :=
    finsum_eq_sum_of_support_subset_of_finite (fun u : ℂ => ((S u : ℤ) : ℝ)) hsupR hTfin
  have hfinT := finsum_eq_sum_of_support_subset_of_finite
    (fun u : ℂ => ((T u : ℤ) : ℝ) * (if |u.im - v| ≤ 3 then 1 else 0)) hsupT hTfin
  have hmid : (∑ᶠ u : ℂ, ((S u : ℤ) : ℝ)) ≤
      ∑ᶠ u : ℂ, ((T u : ℤ) : ℝ) * (if |u.im - v| ≤ 3 then 1 else 0) := by
    rw [hfinS, hfinT]
    refine Finset.sum_le_sum ?_
    intro u _
    by_cases hS0 : S u = 0
    · rw [hS0]
      simp only [Int.cast_zero]
      exact mul_nonneg (Int.cast_nonneg (hTnn u)) (by split_ifs <;> norm_num)
    · rw [hagree u hS0, if_pos ((hgeom u hS0).2)]
      simp
  have hcount' : (∑ᶠ u : ℂ, ((T u : ℤ) : ℝ) * (if |u.im - v| ≤ 3 then 1 else 0))
      ≤ C₀ * Real.log (|v| + 3) := by
    have h1 : (1 : ℝ) ≤ |v| := by linarith [hv]
    have h2 := hcount v h1
    rwa [← hT] at h2
  have hsum_le : (∑ᶠ u : ℂ, ((S u : ℤ) : ℝ)) ≤ C₀ * Real.log (|v| + 3) :=
    le_trans hmid hcount'
  have hA := finsum_intCast_div_sub_bound hSfin hSnn hδ hdist
  calc ‖∑ᶠ (u : ℂ), ((S u : ℤ) : ℂ) * (1 / (s - u))‖
      ≤ (∑ᶠ u : ℂ, ((S u : ℤ) : ℝ)) / δ := hA
    _ ≤ (C₀ * Real.log (|v| + 3)) / δ := div_le_div_of_nonneg_right hsum_le hδ.le
    _ = C₀ / δ * Real.log (|v| + 3) := by ring_nf

end Work.LinnikAreas.Zeta1Aux
