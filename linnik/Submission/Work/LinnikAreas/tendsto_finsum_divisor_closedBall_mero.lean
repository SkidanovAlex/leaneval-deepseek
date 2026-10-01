import Mathlib
import Submission.Commons.Analysis.InfiniteSum.hasSum_tendsto_finset_sum

/-!
# Convergence of the partial divisor sums over balls (meromorphic case)

Let `f` be meromorphic on all of `ℂ` and let `Φ` be a weight for which the full divisor sum

`∑' u, (divisor f univ u) * Φ u`

is summable.  Writing `d_R := MeromorphicOn.divisor f (closedBall 0 R)` for the divisor of `f`
restricted to the ball of radius `R`, the divisor on the ball vanishes outside the ball and agrees
with the global divisor inside it.  Hence `∑ᶠ u, d_R u * Φ u` is the ordinary finite partial sum of
the summable series over the exhaustion of `ℂ` by closed balls, and therefore tends to the full
sum as `R → ∞`.

This is the general (meromorphic) companion of `Work.LinnikAreas.tendsto_finsum_divisor_closedBall`,
which treats the special case of the completed `L`-function of a non-principal Dirichlet character.
-/

namespace Work.LinnikAreas

open Filter Metric
open scoped BigOperators Topology

theorem tendsto_finsum_divisor_closedBall_mero {f : ℂ → ℂ} (hf : MeromorphicOn f Set.univ)
    {Φ : ℂ → ℂ}
    (hΦ : Summable fun u : ℂ => (((MeromorphicOn.divisor f Set.univ) u : ℤ) : ℂ) * Φ u) :
    Filter.Tendsto (fun R : ℝ => finsum (fun u : ℂ =>
        (((MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℂ) * Φ u))
      Filter.atTop (nhds (tsum (fun u : ℂ =>
        (((MeromorphicOn.divisor f Set.univ) u : ℤ) : ℂ) * Φ u))) := by
  classical
  -- the weight, with the global divisor summand
  let G : ℂ → ℂ := fun u => (((MeromorphicOn.divisor f Set.univ) u : ℤ) : ℂ) * Φ u
  -- the divisor on a closed ball is finitely supported
  have hfin : ∀ R : ℝ,
      (MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R)).support.Finite :=
    fun R => (MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R)).finiteSupport
      (isCompact_closedBall 0 R)
  -- the support of the ball divisor, as a finset
  let S : ℝ → Finset ℂ := fun R => (hfin R).toFinset
  -- the ball divisor agrees with the global divisor inside the ball
  have hdiv : ∀ (R : ℝ) (u : ℂ), u ∈ Metric.closedBall (0:ℂ) R →
      (MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R)) u
        = (MeromorphicOn.divisor f Set.univ) u := by
    intro R u hu
    rw [MeromorphicOn.divisor_apply hf (Set.mem_univ u),
      MeromorphicOn.divisor_apply (hf.mono_set (Set.subset_univ _)) hu]
  have hmem_supp : ∀ (R : ℝ) (u : ℂ),
      u ∈ S R ↔ (MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R)) u ≠ 0 := by
    intro R u
    rw [Set.Finite.mem_toFinset, Function.mem_support]
  -- the `finsum` is the finite sum over the support of the ball divisor
  have hsum : ∀ R : ℝ, (finsum fun u : ℂ =>
        (((MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R)) u : ℤ) : ℂ) * Φ u)
      = ∑ u ∈ S R, G u := by
    intro R
    rw [finsum_eq_sum_of_support_subset _ ?_]
    · apply Finset.sum_congr rfl
      intro u hu
      have hu' : u ∈ (MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R)).support :=
        Function.mem_support.mpr ((hmem_supp R u).mp hu)
      rw [hdiv R u
        ((MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R)).supportWithinDomain hu')]
    · intro u hu
      have hdu : (MeromorphicOn.divisor f (Metric.closedBall (0:ℂ) R)) u ≠ 0 := by
        intro hz
        exact hu (by simp [hz])
      exact (hmem_supp R u).mpr hdu
  -- every point of the support of `G` is eventually inside the ball
  have hcondition : ∀ u : ℂ, G u ≠ 0 → ∀ᶠ R : ℝ in atTop, u ∈ S R := by
    intro u hu
    have hdu : ((MeromorphicOn.divisor f Set.univ) u : ℤ) ≠ 0 := by
      intro hzero
      apply hu
      show (((MeromorphicOn.divisor f Set.univ) u : ℤ) : ℂ) * Φ u = 0
      rw [hzero]
      simp
    rw [eventually_atTop]
    refine ⟨‖u‖, fun R hR => ?_⟩
    rw [hmem_supp R u]
    rw [hdiv R u ?_]
    · exact hdu
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact hR
  have hmain : Tendsto (fun R : ℝ => ∑ u ∈ S R, G u) atTop (𝓝 (∑' u : ℂ, G u)) :=
    Commons.Analysis.InfiniteSum.hasSum_tendsto_finset_sum hΦ.hasSum hcondition
  exact Filter.Tendsto.congr (fun R => (hsum R).symm) hmain

end Work.LinnikAreas
