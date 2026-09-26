/-
# The `r`-seminorm bound for the CKMRV contour transform on the funnel

This is the target module `Work.Asymptotics.kernelTransform_seminorm_funnel` (the cusp-`i∞` half
of CKMRV, Ann. of Math. 196 (2022), Theorem 1.9 / Proposition 4.6 + Corollary 4.1): the `r`-seminorms
of the naive contour integral `kernelTransform (Kfun ℓ d) τ ·` have moderate growth on the funnel
`{τ ∈ 𝒟 : 2 ≤ Im τ}`.

The definitions (`PSum`, `preT`, `spikeT`, `tailT`, `highTailClosed`, `funnelLayer`, the restricted
transfer lemma `funnel_transfer`, `funnelLayer_seminorm` and the assembly `funnel_target_of_pieces`)
live in `Submission.Work.Asymptotics.FunnelAsm.funnelDefs`; this module only assembles the four
bundles about the explicit layer and states the theorem.

The hypotheses of `funnel_target_of_pieces` are supplied by

* `Work.Asymptotics.FunnelAsm.psumData` (the smoothness and seminorm bundle for `PSum`, which
  itself rests on `funnelLayerLowSeminorm`, `funnelPreSeminorm`, `funnelSpikeSeminorm`,
  `funnelTailSeminorm` and `highTailClosedSeminorm`);
* `Work.Asymptotics.FunnelAsm.decomp` (the telescoping identity `paperLayer = PSum` on the
  convergence region);
* `Work.Asymptotics.FunnelAsm.agreement` (the agreement of `paperLayer` with the naive contour
  integral where the latter converges);
* `Work.Asymptotics.funnel_kernelTransform_zero` (the vanishing of the naive integral off the
  convergence region in dimension `24`).

The denominator `j τ - j z` of the kernel degenerates exactly on the resolution set of the
divisor, which is why the funnel estimates carry the "clean" hypothesis `j τ ≠ j (i t)`; its
failure set is Lebesgue-null (`Work.Asymptotics.jInvariant_level_null`) and is handled by the a.e.
formulations inside the pieces.
-/
import Mathlib
import Submission.Work.Asymptotics.FunnelAsm.funnelDefs
import Submission.Work.Asymptotics.funnelPreSeminorm
import Submission.Work.Asymptotics.funnelSpikeSeminorm
import Submission.Work.Asymptotics.funnelTailSeminorm
import Submission.Work.Asymptotics.FunnelAsm.funnelLayerLowSeminorm
import Submission.Work.Asymptotics.FunnelAsm.highTailClosedSeminorm
import Submission.Work.Asymptotics.FunnelAsm.psumData
import Submission.Work.Asymptotics.FunnelAsm.decomp
import Submission.Work.Asymptotics.FunnelAsm.agreement

namespace Work.Asymptotics

open UpperHalfPlane Work.Kernels MeasureTheory Filter Topology
open scoped Topology ContDiff

noncomputable section

/-- **Cohn--Kumar--Miller--Radchenko--Viazovska, Proposition 4.6 / Corollary 4.1 (the cusp-`i∞`
funnel).**  The `r`-seminorms of the naive CKMRV contour integral have moderate growth on the
funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}`. -/
theorem kernelTransform_seminorm_funnel (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖
          ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ := by
  have hP := FunnelAsm.psumData ℓ d hd
  refine funnel_target_of_pieces ℓ d hd hP.1 hP.2 ?_ ?_ ?_
  · intro τ r hτ hr hc
    exact FunnelAsm.decomp ℓ d hd τ r hτ hr hc
  · intro τ r hτ hr hc hint
    exact FunnelAsm.agreement ℓ d hd τ r hτ hr hc hint
  · intro τ r hτ hr hn
    have h24 : d = 24 := by
      rcases hd with h | h
      · exact absurd (Or.inl h) hn
      · exact h
    subst h24
    exact funnel_kernelTransform_zero ℓ τ r hτ hr (not_lt.mp (fun hlt => hn (Or.inr hlt)))

end

end Work.Asymptotics
