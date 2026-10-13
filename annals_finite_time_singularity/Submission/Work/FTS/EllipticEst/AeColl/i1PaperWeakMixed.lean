import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.HkSq_pth_grad
import Submission.Work.FTS.EllipticEst.AeI1Fts.I1PaperWeakMixed
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.FTS.EllipticEst.AeI1Fts.hardy_N
import Submission.Work.FTS.EllipticEst.AeI1Fts.zibp_cut
import Submission.Work.FTS.EllipticEst.AeI1Fts.identity
import Submission.Work.FTS.EllipticEst.AeI1Fts.slice_rate
import Submission.Work.FTS.EllipticEst.AeColl.Defs
import Submission.Work.FTS.EllipticEst.AeColl.aeGradTraceRateUnw
import Submission.Work.FTS.EllipticEst.AeColl.pairChain
import Submission.Work.FTS.EllipticEst.AeColl.limitBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeColl

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- `Vfull u` is the level-`0` `HkSq` of the angular derivative of the radial gradient
(`AeI1Fts.HkSq_pth_grad`), the identification used to read the target's positive term. -/
theorem Vfull_eq_HkSq (α : ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    Work.Spaces.HkSq α 0 (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u))
      = Vfull u := by
  have hinner : ∀ z : ℝ,
      (∫ θ in Set.Ioo 0 (Real.pi / 2), (Work.FTS.EllipticEst.AeI1Fts.V u z θ) ^ 2
          * Work.FTS.EllipticEst.AeI1Fts.sigE θ)
        = ∫ θ in Set.Ioo 0 (Real.pi / 2), sigθ θ * (Vz u z θ) ^ 2 := by
    intro z
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    rw [show Work.FTS.EllipticEst.AeI1Fts.sigE θ = sigθ θ from rfl,
      show Work.FTS.EllipticEst.AeI1Fts.V u z θ = Vz u z θ from rfl]
    ring
  rw [Work.FTS.EllipticEst.AeI1Fts.HkSq_pth_grad α u hu]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  rw [hinner z]
  rfl

end

theorem i1PaperWeakMixed : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
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
  obtain ⟨_, _, hchain⟩ := pairChain
  obtain ⟨K₀, hK₀pos, hrate⟩ := aeGradTraceRateUnw
  obtain ⟨C, hC, hlim⟩ := limitBound
  refine ⟨C, hC, fun α u G hA hU h3 h4 => ?_⟩
  have hsm := Work.FTS.EllipticEst.H2W.Ae.AeData.smooth hA
  have hV : Work.Spaces.HkSq α 0 (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u))
      = Vfull u := Vfull_eq_HkSq α u hsm
  set Aa : ℝ := Work.FTS.EllipticEst.AngSecond.IP
      (Work.FTS.EllipticEst.H2W.Ae.grad u) (Work.FTS.EllipticEst.H2W.Ae.grad u) with hAa
  set Bb : ℝ := Work.FTS.EllipticEst.AngSecond.IP
      (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u) with hBb
  set Dp : ℝ := Work.FTS.EllipticEst.AngSecond.IP
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u) with hDp
  -- the Hardy-type rate of the slices of `U` is the conclusion of `aeGradTraceRateUnw`
  have hK : ∃ K : ℝ, 0 < K ∧ ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        (z * Work.Spaces.pz u z θ) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta)
          * (∫ t in Set.Ioo 0 θ, (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
              * Work.FTS.EllipticEst.AngSecond.sig t)) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        (z * Work.Spaces.pz u z θ) ^ 2 ≤ K * (Real.pi / 2 - θ) ^ (1 + Work.Spaces.eta)
          * (∫ t in Set.Ioo θ (Real.pi / 2),
              (z * Work.Spaces.pz (Work.Spaces.pth u) z t) ^ 2
                * Work.FTS.EllipticEst.AngSecond.sig t)) := by
    refine ⟨K₀, hK₀pos, ?_⟩
    filter_upwards [hrate α u G hA h3 h4] with z hz
    exact ⟨hz.2.2.1, hz.2.2.2⟩
  -- the two cut-off limits: `pairChain` at fixed `n`, then `limitBound` as `n ↑ ∞`
  have hmain : ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * Vfull u
      ≤ Dp + C * (Aa + Real.sqrt Aa * Real.sqrt Bb) := by
    have h := hlim α u G hA hU h3 h4 (hchain α u G hA hU h3 h4 hK)
    have hAz : Az u = fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ := rfl
    have hUg : Uz u = Work.FTS.EllipticEst.H2W.Ae.grad u := rfl
    rw [hAz, hUg] at h
    simpa only [hAa, hBb, hDp] using h
  have hα2 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have hstep : α ^ 2 * (((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * Vfull u)
      ≤ α ^ 2 * (Dp + C * (Aa + Real.sqrt Aa * Real.sqrt Bb)) :=
    mul_le_mul_of_nonneg_left hmain hα2
  have hexp : α ^ 2 * (Dp + C * (Aa + Real.sqrt Aa * Real.sqrt Bb))
      = α ^ 2 * Dp + C * α ^ 2 * (Aa + Real.sqrt Aa * Real.sqrt Bb) := by ring
  rw [hexp] at hstep
  have hgoal : ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) *
        (α ^ 2 * Work.Spaces.HkSq α 0
          (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u)))
        - C * α ^ 2 * (Aa + Real.sqrt Aa * Real.sqrt Bb)
      = α ^ 2 * (((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * Vfull u)
        - C * α ^ 2 * (Aa + Real.sqrt Aa * Real.sqrt Bb) := by
    rw [hV]
    ring
  rw [hgoal]
  linarith [hstep]

end Work.FTS.EllipticEst.AeColl
