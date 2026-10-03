import Mathlib
import Submission.Commons.NumberTheory.Linnik.logDeriv_circle_residue
import Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect
import Submission.Commons.NumberTheory.Linnik.goodRadius_geometric
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset

namespace Work.FIArea5.HeckeZFR.Hadm

open Filter
open scoped Topology

/-- **Finiteness of the zero set in a ball.**  If `Λ : ℂ → ℂ` is entire and not identically zero,
then for every radius `B` the set of zeros of `Λ` inside the closed ball of radius `B` is finite.

The proof is the classical one: the zero set is closed (continuity of `Λ`) and consists of
isolated points (principle of isolated zeros, plus the identity theorem to rule out a locally
identically vanishing non-zero entire function).  If it were infinite, compactness of the closed
ball (`Set.Infinite.exists_accPt_of_subset_isCompact`) would produce an accumulation point `x` of
zeros inside the ball; closedness forces `Λ x = 0`, while isolated zeros at `x` forbids the
accumulation. -/
theorem zeroSetFinite (Λ : ℂ → ℂ) (hDiff : Differentiable ℂ Λ) (hne : ∃ z : ℂ, Λ z ≠ 0)
    (B : ℝ) : ({u : ℂ | Λ u = 0 ∧ ‖u‖ ≤ B} : Set ℂ).Finite := by
  by_contra hfin
  set S : Set ℂ := {u : ℂ | Λ u = 0 ∧ ‖u‖ ≤ B} with hS
  have hSinf : S.Infinite := hfin
  set Z : Set ℂ := {u : ℂ | Λ u = 0} with hZ
  -- The zero set is closed, being the equalizer of `Λ` and the constant `0`.
  have hZclosed : IsClosed Z := by
    rw [hZ]; exact isClosed_eq hDiff.continuous continuous_const
  have hsubZ : S ⊆ Z := fun u hu => hu.1
  have hsubK : S ⊆ Metric.closedBall (0 : ℂ) B := by
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa using hu.2
  -- Compactness of the closed ball yields an accumulation point of the zeros inside it.
  obtain ⟨x, _hxK, hacc⟩ :=
    hSinf.exists_accPt_of_subset_isCompact (isCompact_closedBall (0 : ℂ) B) hsubK
  have hxZ : x ∈ Z :=
    (isClosed_iff_accPt.mp hZclosed) x (hacc.mono (Filter.principal_mono.mpr hsubZ))
  have hfreq : ∃ᶠ y in 𝓝[≠] x, y ∈ S := accPt_iff_frequently_nhdsNE.mp hacc
  -- Principle of isolated zeros at `x`.
  have hana : AnalyticAt ℂ Λ x := hDiff.analyticAt x
  rcases hana.eventually_eq_zero_or_eventually_ne_zero with h0 | h0
  · -- `Λ` vanishes on a neighbourhood of `x`; the identity theorem makes it identically zero.
    have hA : AnalyticOnNhd ℂ Λ Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr hDiff
    have heq : Set.EqOn Λ 0 Set.univ :=
      hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ x) h0
    obtain ⟨w, hw⟩ := hne
    exact hw (heq (Set.mem_univ w))
  · -- `Λ` is non-zero near the punctured neighbourhood of `x`, contradicting the accumulation.
    have hbad : ∃ᶠ y in 𝓝[≠] x, False :=
      (hfreq.and_eventually h0).mono (fun y hy => absurd hy.1.1 hy.2)
    exact hbad (Filter.Eventually.of_forall fun _ hh => hh)

end Work.FIArea5.HeckeZFR.Hadm
