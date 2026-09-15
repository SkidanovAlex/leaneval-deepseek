import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Connected

/-
If `G` is analytic on a neighbourhood of the closed ball of radius `R > 0` around `0`, and does not
vanish identically on that closed ball, then the set of real `x ∈ [-R, R]` with `G x = 0` is finite.

The proof is the standard isolated-zero argument: if there were infinitely many such `x`, their
images under `ℝ → ℂ` would form an infinite subset of the compact set `closedBall 0 R`, hence would
have an accumulation point `z₀` there.  Analyticity at `z₀` together with the principle of isolated
zeros (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`, applied to the preconnected
closed ball) forces `G` to vanish on all of `closedBall 0 R`, contradicting the hypothesis that `G`
is non-zero somewhere on that ball.
-/

open Metric Filter
open scoped Topology

set_option linter.unusedVariables false

namespace Commons.Analysis.Complex

theorem zero_set_analyticOnNhd_closedBall_finite {R : ℝ} (hR : 0 < R) {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (Metric.closedBall (0 : ℂ) R))
    (hne : ∃ z ∈ Metric.closedBall (0 : ℂ) R, G z ≠ 0) :
    {x : ℝ | |x| ≤ R ∧ G (x : ℂ) = 0}.Finite := by
  by_contra hfin
  have hinf : {x : ℝ | |x| ≤ R ∧ G (x : ℂ) = 0}.Infinite := Set.not_finite.mp hfin
  have hinj : Set.InjOn (fun x : ℝ => (x : ℂ)) {x : ℝ | |x| ≤ R ∧ G (x : ℂ) = 0} :=
    fun a _ b _ hab => Complex.ofReal_injective hab
  set S : Set ℂ := (fun x : ℝ => (x : ℂ)) '' {x : ℝ | |x| ≤ R ∧ G (x : ℂ) = 0} with hS
  have hSinf : S.Infinite := (Set.infinite_image_iff hinj).2 hinf
  have hSsub : S ⊆ Metric.closedBall (0 : ℂ) R := by
    rintro z ⟨x, ⟨hxabs, -⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact hxabs
  obtain ⟨z₀, hz₀K, hz₀acc⟩ :=
    hSinf.exists_accPt_of_subset_isCompact (isCompact_closedBall (0 : ℂ) R) hSsub
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, G z = 0 := by
    rw [accPt_iff_frequently_nhdsNE] at hz₀acc
    exact hz₀acc.mono fun z ⟨x, hxA, hxz⟩ => hxz ▸ hxA.2
  have hzeroClosed : Set.EqOn G 0 (Metric.closedBall (0 : ℂ) R) :=
    hG.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_closedBall hz₀K hfreq
  obtain ⟨z, hz, hz0⟩ := hne
  exact hz0 (hzeroClosed hz)

end Commons.Analysis.Complex