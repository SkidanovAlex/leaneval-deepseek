/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Deleg.i1Paper_weakMixedAux` — the assembly of the cut-off chain

`i1Paper_weakMixed_of` turns the three analytic pieces of the route

* `Deleg.mixedCollarBound` (`CollarBound Cw`),
* `Deleg.mixedTruncPairLe` (`TruncPairLe Cw`),
* `Deleg.mixedPairLimit` (`PairLimit Cw`),

plus the `χ_n ↑ 1` limit `Deleg.mixedLimitBound` into the requested `i1Paper_weakMixed`.
The rate constant is produced by `I1Wk.aeGradTrace0` from the two mixed-honesty hypotheses, and
the identification `HkSq α 0 (∂_θ(grad u)) = Vfull u` is `AeColl.Vfull_eq_HkSq`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.Deleg.i1Paper_weakMixedDefs
import Submission.Work.FTS.EllipticEst.Deleg.i1Paper_weakMixedLimit
import Submission.Work.FTS.EllipticEst.AeColl.Defs
import Submission.Work.FTS.EllipticEst.AeColl.i1PaperWeakMixed
import Submission.Work.FTS.EllipticEst.AeColl.pairFacts
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.aeGradTrace0
import Submission.Work.FTS.EllipticEst.AeI1Fts.HkSq_pth_grad
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Deleg

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The final assembly of the cut-off chain**, given its three analytic pieces: the collar bound,
the per-`(χ_n, ψ_δ)` inequality and the `ψ_δ ↓ 0` limit.  The rate constant is produced by
`I1Wk.aeGradTrace0` from the two mixed-honesty hypotheses, and the identification
`HkSq α 0 (∂_θ(grad u)) = Vfull u` is `AeColl.Vfull_eq_HkSq`. -/
theorem i1Paper_weakMixed_of
    (hcol : ∃ Cw : ℝ, 0 < Cw ∧ CollarBound Cw)
    (hpair : ∀ Cw : ℝ, 0 < Cw → CollarBound Cw → TruncPairLe Cw)
    (hplim : ∀ Cw : ℝ, 0 < Cw → PairLimit Cw) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn
          (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iz →
      ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) *
          (α ^ 2 * Work.Spaces.HkSq α 0
            (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u)))
        - C * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP
              (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u)
            + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
                (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u))
              * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
                  (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)))
      ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u) := by
  obtain ⟨Cw, hCw, hC⟩ := hcol
  obtain ⟨C1, hC1, hbound⟩ := mixedLimitBound
  refine ⟨C1, hC1, ?_⟩
  intro α u G hAe hU h1 h2
  have hmix : MixedHon u := ⟨h1, h2⟩
  -- the endpoint rate of the slices of `U`, from the two mixed-honesty hypotheses
  obtain ⟨K, hK, hrate0⟩ :=
    Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.aeGradTrace0 α u G hAe hU h1 h2
  have hrate : SliceRate K u := by
    filter_upwards [hrate0] with z hz
    exact ⟨hz.2.2.2.1, hz.2.2.2.2⟩
  have hcut : ∀ n : ℕ,
      kap * Work.FTS.EllipticEst.AeColl.Pcut u n
        ≤ Work.FTS.EllipticEst.AeColl.Dcut u n + Work.FTS.EllipticEst.AeColl.Trcut u n
          - 2 * Work.Spaces.eta * Work.FTS.EllipticEst.AeColl.Acut u n :=
    hplim Cw hCw α u G hAe hU hmix K hK hrate
      (hpair Cw hCw hC α u G hAe hU hmix K hK hrate)
  have hmain := hbound α u G hAe hU hcut
  -- rewrite the `Az`/`Uz` aliases into the target's expressions
  have hmain' : kap * Work.FTS.EllipticEst.AeColl.Vfull u
      ≤ Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
            (Work.Spaces.pthIter 2 u)
        + C1 * (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
                (Work.FTS.EllipticEst.H2W.Ae.grad u)
              + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
                    (Work.FTS.EllipticEst.H2W.Ae.grad u))
                * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                    (Work.Spaces.pthIter 2 u))) := by
    have h1 : Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Az u)
        (Work.Spaces.pthIter 2 u)
        = Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
            (Work.Spaces.pthIter 2 u) := rfl
    have h2 : Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.AeColl.Uz u)
        (Work.FTS.EllipticEst.AeColl.Uz u)
        = Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
            (Work.FTS.EllipticEst.H2W.Ae.grad u) := rfl
    rw [h1, h2] at hmain
    exact hmain
  -- identify `HkSq α 0 (∂_θ(z∂_zu))` with `Vfull u`
  have hV := Work.FTS.EllipticEst.AeColl.Vfull_eq_HkSq α u
    (Work.FTS.EllipticEst.H2W.Ae.AeData.smooth hAe)
  have hα2 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have hstep := mul_le_mul_of_nonneg_left hmain' hα2
  have hgoal : kap * (α ^ 2 * Work.FTS.EllipticEst.AeColl.Vfull u)
      - C1 * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
            (Work.FTS.EllipticEst.H2W.Ae.grad u)
          + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
                (Work.FTS.EllipticEst.H2W.Ae.grad u))
            * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                (Work.Spaces.pthIter 2 u)))
      ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
          (Work.Spaces.pthIter 2 u) := by
    have e1 : α ^ 2 * (kap * Work.FTS.EllipticEst.AeColl.Vfull u)
        = kap * (α ^ 2 * Work.FTS.EllipticEst.AeColl.Vfull u) := by ring
    have e2 : α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u)
          + C1 * (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
                (Work.FTS.EllipticEst.H2W.Ae.grad u)
              + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
                    (Work.FTS.EllipticEst.H2W.Ae.grad u))
                * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                    (Work.Spaces.pthIter 2 u))))
        = α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u)
          + C1 * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
                (Work.FTS.EllipticEst.H2W.Ae.grad u)
              + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
                    (Work.FTS.EllipticEst.H2W.Ae.grad u))
                * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 u)
                    (Work.Spaces.pthIter 2 u))) := by ring
    rw [e1, e2] at hstep
    linarith [hstep]
  rw [hV]
  simpa only [kap] using hgoal

end

end Work.FTS.EllipticEst.Deleg
