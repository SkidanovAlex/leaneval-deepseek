import Mathlib
import Submission.Work.LinnikAreas.CIDeps

/-!
# Partial divisor sums over balls converge to the full divisor sum

For a non-principal Dirichlet character `χ` the completed `L`-function `Λ = completedLFunction χ`
is entire.  Writing `o u = analyticOrderNatAt Λ u` for the multiplicity of the zero of `Λ` at
`u`, the divisor of `Λ` is

* `divisor Λ univ u = o u` on the whole plane, and
* `divisor Λ (closedBall 0 R) u = if u ∈ closedBall 0 R then o u else 0`.

Consequently, for any weight `Φ` for which the full divisor sum is summable, the partial sums
`∑ᶠ u, divisor Λ (closedBall 0 R) u * Φ u` are the ordinary finite partial sums of the summable
series `∑' u, divisor Λ univ u * Φ u` over the exhaustion of `ℂ` by the closed balls, hence tend
to it.
-/

namespace Work.LinnikAreas

open Filter Metric
open scoped BigOperators Topology

theorem tendsto_finsum_divisor_closedBall {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {Φ : ℂ → ℂ}
    (hΦ : Summable fun u : ℂ =>
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ) * Φ u) :
    Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 R)) u : ℤ) : ℂ) * Φ u)
      Filter.atTop (nhds (∑' u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ) u : ℤ) : ℂ) * Φ u)) := by
  classical
  set Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ with hΛdef
  have hΛdiff : Differentiable ℂ Λ := by
    simpa [Λ] using DirichletCharacter.differentiable_completedLFunction hχ
  have hΛan : ∀ U : Set ℂ, AnalyticOnNhd ℂ Λ U := fun U z _ => hΛdiff.analyticAt z
  -- the multiplicities of the zeros of `Λ`, viewed as complex numbers
  let o : ℂ → ℂ := fun u => ((analyticOrderNatAt Λ u : ℤ) : ℂ)
  -- the global divisor is `o`
  have huniv : ∀ u : ℂ, (((MeromorphicOn.divisor Λ Set.univ) u : ℤ) : ℂ) = o u := by
    intro u
    rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (hΛan Set.univ) (Set.mem_univ u)]
  -- the ball divisor agrees with `o` inside the ball and vanishes outside
  have hball : ∀ (R : ℝ) (u : ℂ),
      (((MeromorphicOn.divisor Λ (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℂ)
        = if u ∈ Metric.closedBall (0:ℂ) R then o u else 0 := by
    intro R u
    by_cases hu : u ∈ Metric.closedBall (0:ℂ) R
    · rw [if_pos hu, Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (hΛan _) hu]
    · rw [if_neg hu, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
      simp
  let f : ℂ → ℂ := fun u => o u * Φ u
  have hfval : ∀ u : ℂ, f u = (((MeromorphicOn.divisor Λ Set.univ) u : ℤ) : ℂ) * Φ u := by
    intro u
    show o u * Φ u = _
    rw [huniv u]
  have hfsum : Summable f := hΦ.congr (fun u => (hfval u).symm)
  -- the finite sets: the support of the divisor on the closed ball
  let S : ℝ → Finset ℂ := fun R =>
    ((MeromorphicOn.divisor Λ (Metric.closedBall (0:ℂ) R)).finiteSupport
      (isCompact_closedBall (0:ℂ) R)).toFinset
  have hSmem : ∀ (R : ℝ) (u : ℂ), u ∈ S R ↔
      MeromorphicOn.divisor Λ (Metric.closedBall (0:ℂ) R) u ≠ 0 := by
    intro R u
    show u ∈ ((MeromorphicOn.divisor Λ (Metric.closedBall (0:ℂ) R)).finiteSupport
      (isCompact_closedBall (0:ℂ) R)).toFinset ↔ _
    rw [Set.Finite.mem_toFinset, Function.mem_support]
  have hSU : ∀ (R : ℝ) (u : ℂ), u ∈ S R → u ∈ Metric.closedBall (0:ℂ) R := by
    intro R u hu
    by_contra h
    exact (hSmem R u).mp hu
      (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ h)
  -- the `finsum` is the finite sum over `S R`
  have hfins : ∀ R : ℝ, (∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor Λ (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℂ) * Φ u)
      = ∑ u ∈ S R, f u := by
    intro R
    rw [finsum_eq_sum_of_support_subset _ (s := S R) ?_]
    · refine Finset.sum_congr rfl (fun u hu => ?_)
      show (((MeromorphicOn.divisor Λ (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℂ) * Φ u = f u
      rw [hball R u, if_pos (hSU R u hu)]
    · intro u hu
      rw [Function.mem_support] at hu
      rw [Finset.mem_coe]
      exact (hSmem R u).mpr (fun h0 => hu (by rw [h0, Int.cast_zero, zero_mul]))
  -- every point of the support of `f` is eventually inside `S R`
  have hev : ∀ u : ℂ, f u ≠ 0 → ∀ᶠ R in Filter.atTop, u ∈ S R := by
    intro u hfu
    have houn : o u ≠ 0 := fun h0 => hfu (by show o u * Φ u = 0; rw [h0, zero_mul])
    have hnat : analyticOrderNatAt Λ u ≠ 0 := fun h0 => houn (by simp [o, h0])
    refine Filter.eventually_atTop.mpr ⟨‖u‖, fun R hR => ?_⟩
    rw [hSmem R u,
      Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (hΛan _) ?_]
    · exact_mod_cast hnat
    · rw [Metric.mem_closedBall, dist_zero_right]; exact hR
  have hlim : Filter.Tendsto (fun R : ℝ => ∑ u ∈ S R, f u) Filter.atTop
      (nhds (∑' u : ℂ, f u)) :=
    Commons.Analysis.InfiniteSum.hasSum_tendsto_finset_sum hfsum.hasSum hev
  have hlim2 : Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor Λ (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℂ) * Φ u)
      Filter.atTop (nhds (∑' u : ℂ, f u)) :=
    Filter.Tendsto.congr (fun R => (hfins R).symm) hlim
  have htsum : (∑' u : ℂ, f u)
      = ∑' u : ℂ, (((MeromorphicOn.divisor Λ Set.univ) u : ℤ) : ℂ) * Φ u :=
    tsum_congr (fun u => hfval u)
  rw [htsum] at hlim2
  exact hlim2

end Work.LinnikAreas
