import Mathlib
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset

/-!
# Divisor `finsum` tools: finite order sums, indicator transfers, positivity

Three reusable facts about the divisor of an entire function `F : ℂ → ℂ`, all stated purely in
Mathlib vocabulary (so that this module is importable from any part of the workspace, in
particular from modules that mention `DirichletCharacter.completedLFunction` only through
neutral imports):

* `finset_sum_le_finsum_of_nonneg` — a finite sum of nonnegative terms of a finitely supported
  function is at most the corresponding `finsum`;
* `indicator_divisor_le_divisorBall` / `indicator_divisorBall_le_divisorBallFinsum` — the divisor
  of `F` on a ball `B(0,ρ₀)`, cut down by the indicator of `B(a,ρ)`, is dominated by the divisor
  of `F` on `B(a,ρ)` (pointwise, hence after summation): the two divisors agree on the
  intersection `B(0,ρ₀) ∩ B(a,ρ)` and coefficients of the divisor of an analytic function are
  nonnegative;
* `finset_orderSum_le_divisorFinsum` — the "shrink the finite set into a ball" step: for a finite
  set `S` contained in `B(0,ρ₀)`, the multiplicity-weighted sum
  `∑_{u ∈ S} analyticOrderNatAt F u · w u` is at most the divisor-weighted `finsum`
  `∑ᶠ u, divisor F B(0,ρ₀) u · w u` over that ball, for the specific weight
  `w u = 1/(1 + ‖s-u‖²)`.  This is the step that lets a global `finsum` estimate (obtained by a
  dyadic argument) bound a finite sum over an arbitrary set of points.
-/

open scoped BigOperators

set_option autoImplicit false

namespace Commons.Analysis.Complex

/-- A finite sum of the values of a nonnegative, finitely supported function is at most its
`finsum`. -/
lemma finset_sum_le_finsum_of_nonneg {α : Type*} {g : α → ℝ}
    (hfin : Function.HasFiniteSupport g) (hg0 : ∀ a, 0 ≤ g a) (S : Finset α) :
    ∑ a ∈ S, g a ≤ ∑ᶠ a, g a := by
  classical
  have hSp : (Function.support g).Finite := hfin
  set t : Finset α := hSp.toFinset ∪ S with ht
  have hsub : Function.support g ⊆ (↑t : Set α) := by
    intro a ha
    rw [ht, Finset.mem_coe, Finset.mem_union]
    exact Or.inl ((Set.Finite.mem_toFinset hSp).mpr ha)
  rw [finsum_eq_sum_of_support_subset g hsub]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hg0 i)
  rw [ht]
  exact Finset.subset_union_right

/-- Pointwise domination: for `F` analytic on all of `ℂ`, the divisor of `F` on the closed ball
`B(0,ρ₀)`, restricted by the indicator of `B(a,ρ)`, is at most the divisor of `F` on `B(a,ρ)`. -/
lemma indicator_divisor_le_divisorBall (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F Set.univ)
    (ρ0 : ℝ) (a : ℂ) (ρ : ℝ) (u : ℂ) :
    Set.indicator (Metric.closedBall a ρ)
        (fun u => (((MeromorphicOn.divisor F (Metric.closedBall 0 ρ0)) u : ℤ) : ℝ)) u
      ≤ (((MeromorphicOn.divisor F (Metric.closedBall a ρ)) u : ℤ) : ℝ) := by
  classical
  have hnn : (0 : ℝ) ≤ (((MeromorphicOn.divisor F (Metric.closedBall a ρ)) u : ℤ) : ℝ) :=
    Int.cast_nonneg (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hF.mono (Set.subset_univ _)) u)
  by_cases hmem : u ∈ Metric.closedBall a ρ
  · rw [Set.indicator_of_mem hmem]
    by_cases hmem0 : u ∈ Metric.closedBall 0 ρ0
    · rw [Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset (f := F) (a := 0) (b := a)
        (ra := ρ0) (rb := ρ) (u := u) (hF.mono (Set.subset_univ _)) hmem0 hmem]
    · have hz : (MeromorphicOn.divisor F (Metric.closedBall 0 ρ0)) u = 0 := by
        rw [MeromorphicOn.divisor_def]; simp [hmem0]
      rw [hz, Int.cast_zero]; exact hnn
  · rw [Set.indicator_of_notMem hmem]; exact hnn

/-- Cutting the divisor on `B(0,ρ₀)` down to the ball `B(a,ρ)` can only decrease the `finsum`. -/
lemma indicator_divisorBall_le_divisorBallFinsum (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F Set.univ)
    (ρ0 : ℝ) (a : ℂ) (ρ : ℝ) :
    (∑ᶠ u : ℂ, Set.indicator (Metric.closedBall a ρ)
        (fun u => (((MeromorphicOn.divisor F (Metric.closedBall 0 ρ0)) u : ℤ) : ℝ)) u)
      ≤ ∑ᶠ u : ℂ, (((MeromorphicOn.divisor F (Metric.closedBall a ρ)) u : ℤ) : ℝ) := by
  classical
  set D0 : ℂ → ℝ :=
    fun u => (((MeromorphicOn.divisor F (Metric.closedBall 0 ρ0)) u : ℤ) : ℝ) with hD0
  set D1 : ℂ → ℝ :=
    fun u => (((MeromorphicOn.divisor F (Metric.closedBall a ρ)) u : ℤ) : ℝ) with hD1
  have hpt : ∀ u : ℂ, Set.indicator (Metric.closedBall a ρ) D0 u ≤ D1 u := by
    intro u
    rw [hD0, hD1]
    exact indicator_divisor_le_divisorBall F hF ρ0 a ρ u
  have hD0fin : Function.HasFiniteSupport D0 := by
    rw [hD0]
    refine ((MeromorphicOn.divisor F (Metric.closedBall 0 ρ0)).finiteSupport
      (isCompact_closedBall 0 ρ0)).subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h
    exact hu (by rw [h]; simp)
  have hD1fin : Function.HasFiniteSupport D1 := by
    rw [hD1]
    refine ((MeromorphicOn.divisor F (Metric.closedBall a ρ)).finiteSupport
      (isCompact_closedBall a ρ)).subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h
    exact hu (by rw [h]; simp)
  have hGfin : Function.HasFiniteSupport
      (fun u => Set.indicator (Metric.closedBall a ρ) D0 u) := by
    refine hD0fin.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h
    apply hu
    by_cases hmem : u ∈ Metric.closedBall a ρ
    · rw [Set.indicator_of_mem hmem]; exact h
    · rw [Set.indicator_of_notMem hmem]
  exact finsum_le_finsum' hGfin hD1fin hpt

/-- **Shrink a finite set into a ball.**  If the entire function `F` is analytic everywhere and
`S ⊆ B(0,ρ₀)`, then the multiplicity-weighted sum over `S` is at most the divisor-weighted
`finsum` over `B(0,ρ₀)`; on the ball the divisor coefficient is exactly the multiplicity
(`divisor_eq_analyticOrderNatAt_cast`), and outside the support of the divisor the summands
vanish. -/
theorem finset_orderSum_le_divisorFinsum (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F Set.univ)
    (ρ0 : ℝ) (s : ℂ) (S : Finset ℂ) (hS : ∀ u ∈ S, ‖u‖ ≤ ρ0) :
    ∑ u ∈ S, (analyticOrderNatAt F u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)) ≤
      ∑ᶠ u : ℂ, (((MeromorphicOn.divisor F (Metric.closedBall 0 ρ0)) u : ℤ) : ℝ) *
        (1 / (1 + ‖s - u‖ ^ 2)) := by
  classical
  let U : Set ℂ := Metric.closedBall 0 ρ0
  have hF' : AnalyticOnNhd ℂ F U := hF.mono (Set.subset_univ U)
  have hdiv_nonneg : ∀ u : ℂ, (0 : ℤ) ≤ MeromorphicOn.divisor F U u :=
    fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg hF' u
  let g : ℂ → ℝ :=
    fun u => (((MeromorphicOn.divisor F U) u : ℤ) : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))
  have hg_def : ∀ u : ℂ, g u =
      (((MeromorphicOn.divisor F U) u : ℤ) : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)) := fun u => rfl
  have hEq : ∀ u ∈ S, (analyticOrderNatAt F u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)) = g u := by
    intro u hu
    rw [hg_def u]
    have huU : u ∈ U := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact hS u hu
    rw [divisor_eq_analyticOrderNatAt_cast hF' huU]
    push_cast
    ring
  have hg0 : ∀ u : ℂ, 0 ≤ g u := by
    intro u
    rw [hg_def u]
    exact mul_nonneg (Int.cast_nonneg (hdiv_nonneg u)) (by positivity)
  have hfin : Function.HasFiniteSupport g := by
    have hUcompact : IsCompact U := isCompact_closedBall 0 ρ0
    have hd_fin : Function.HasFiniteSupport (fun u : ℂ => MeromorphicOn.divisor F U u) :=
      (MeromorphicOn.divisor F U).finiteSupport hUcompact
    have hRfin : Function.HasFiniteSupport
        (fun u : ℂ => ((MeromorphicOn.divisor F U u : ℤ) : ℝ)) :=
      hd_fin.subset (fun u hu => by
        rw [Function.mem_support] at hu ⊢
        intro h
        exact hu (by rw [h]; simp))
    exact hRfin.subset (fun u hu => by
      rw [Function.mem_support] at hu ⊢
      intro h
      exact hu (by rw [hg_def u, h]; ring))
  have hsum_eq : (∑ u ∈ S, (analyticOrderNatAt F u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))
      = ∑ u ∈ S, g u := Finset.sum_congr rfl hEq
  exact le_trans (le_of_eq hsum_eq) (finset_sum_le_finsum_of_nonneg hfin hg0 S)

end Commons.Analysis.Complex
