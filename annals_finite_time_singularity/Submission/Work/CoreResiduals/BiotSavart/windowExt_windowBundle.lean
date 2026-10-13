import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.CoreResiduals.Defs
import Submission.Work.CoreResiduals.BiotSavart.WindowExtDefs
import Submission.Work.CoreResiduals.BiotSavart.windowExt_localBdd
import Submission.Work.CoreResiduals.BiotSavart.windowExt_holder_bound
import Submission.Work.CoreResiduals.BiotSavart.exists_windowExtension_of_stripBundle

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology

namespace Work.CoreResiduals.BiotSavart

/-- **The two-sided time-extension of a bundled strip vorticity satisfies the window bundle.**
This is the statement of the already-proved
`Work.CoreResiduals.BiotSavart.exists_windowExtension_of_stripBundle`
(`Submission/Work/CoreResiduals/BiotSavart/exists_windowExtension_of_stripBundle.lean`), made
*concrete* in the extension (the explicit `windowExt ω S` constructed there, instead of an
existentially quantified `ω_ext`) and with the dead hypothesis `hα1 : (α : ℝ) < 1` deleted (Lean
itself reports `Variable name hα1 is not explicitly referenced` for that file).  The existing proof
already concludes with `refine ⟨windowExt ω S, ?_, ?_, ?_⟩` where the three goals are the agreement
clause, `BSAdmissibleOnWindow (windowExt ω S) R (S+1)` and
`TimeDerivLocallyContinuous (windowExt ω S) (S+1)`; so the proof of the conjunction below is
verbatim the second and third bullets of that proof.  It is NOT derivable from
`exists_windowExtension_of_stripBundle` by taking `.2` of the existential (that gives an
unspecified witness, and the source result assumes `hα1` anyway). -/
theorem windowExt_windowBundle {α : NNReal} (hα : 0 < (α : ℝ))
    {ω : Work.LWP.R3 → ℝ → Work.LWP.R3} {R S : ℝ} (hS : 0 < S)
    (hbun : Work.CoreResiduals.BSAdmissibleStripFull α ω R S)
    (hxH : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : Work.LWP.R3, ∀ t ∈ Set.Icc (0:ℝ) S,
      ‖FiniteTimeSingularity.timeDeriv ω a t - FiniteTimeSingularity.timeDeriv ω b t‖
        ≤ C * ‖a - b‖ ^ c) :
    Work.CoreResiduals.BSAdmissibleOnWindow (Work.CoreResiduals.BiotSavart.windowExt ω S) R (S + 1) ∧
      Work.CoreResiduals.TimeDerivLocallyContinuous
        (Work.CoreResiduals.BiotSavart.windowExt ω S) (S + 1) := by
  have hstrip := hbun.1
  have hTD := hbun.2.1
  have hTDH := hbun.2.2
  obtain ⟨hRpos, hsupp, _hbdd, _hholder, _htholder, hslices⟩ := hstrip
  have hdiff := hTD.1
  obtain ⟨M₁, hM₁⟩ := hTD.2.1
  have hdtmeas := hTD.2.2
  obtain ⟨N₁, hN₁⟩ := hTDH
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) S := ⟨le_refl 0, le_of_lt hS⟩
  have hSmem : S ∈ Set.Icc (0:ℝ) S := ⟨le_of_lt hS, le_refl S⟩
  refine ⟨?_, ?_⟩
  · refine ⟨hRpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t y hy
      by_contra hyb
      exact hy (windowExt_eq_zero_of_notMem_closedBall hS hsupp hdiff hyb t)
    · intro t₀ _
      obtain ⟨M', hM'⟩ := windowExt_localBdd hS hbun t₀
      exact ⟨1, one_pos, M', fun t ht y => hM' t ht y⟩
    · intro t₀ _
      obtain ⟨c, hc, C, hC⟩ := windowExt_holder_bound hα hS hbun hxH t₀
      exact ⟨1, one_pos, c, hc, C, fun t ht a b => hC t ht a b⟩
    · intro t₀ _
      refine ⟨1, one_pos, fun t _ => ?_⟩
      by_cases h : t ≤ 0
      · have heq : (fun y : Work.LWP.R3 => windowExt ω S y t)
            = fun y => ω y 0 + t • FiniteTimeSingularity.timeDeriv ω y 0 := by
          funext y; exact windowExt_of_nonpos h
        rw [heq]
        exact (hslices 0 h0mem).add ((hdtmeas 0 h0mem).const_smul t)
      · by_cases h2 : t ≤ S
        · have heq : (fun y : Work.LWP.R3 => windowExt ω S y t) = fun y => ω y t := by
            funext y; exact windowExt_of_mem_Icc ⟨le_of_lt (lt_of_not_ge h), h2⟩
          rw [heq]
          exact hslices t ⟨le_of_lt (lt_of_not_ge h), h2⟩
        · have heq : (fun y : Work.LWP.R3 => windowExt ω S y t)
              = fun y => ω y S + (t - S) • FiniteTimeSingularity.timeDeriv ω y S := by
            funext y; exact windowExt_of_ge hS (le_of_lt (lt_of_not_ge h2))
          rw [heq]
          exact (hslices S hSmem).add ((hdtmeas S hSmem).const_smul (t - S))
    · intro t₀ _
      refine ⟨1, one_pos, fun t _ y => ?_⟩
      rw [timeDeriv_windowExt hS hdiff y t]
      exact hasDerivAt_windowExt hS hdiff y t
    · intro t₀ _
      refine ⟨1, one_pos, max M₁ 0, fun t _ y => ?_⟩
      rw [timeDeriv_windowExt hS hdiff y t]
      by_cases h : t ≤ 0
      · rw [dtExt_of_nonpos h]
        exact le_trans (hM₁ 0 h0mem y) (le_max_left _ _)
      · by_cases h2 : t ≤ S
        · rw [dtExt_of_mem_Icc ⟨le_of_lt (lt_of_not_ge h), h2⟩]
          exact le_trans (hM₁ t ⟨le_of_lt (lt_of_not_ge h), h2⟩ y) (le_max_left _ _)
        · rw [dtExt_of_ge hS (le_of_lt (lt_of_not_ge h2))]
          exact le_trans (hM₁ S hSmem y) (le_max_left _ _)
    · intro t₀ _
      refine ⟨1, one_pos, fun t _ => ?_⟩
      have heq : (fun y : Work.LWP.R3 => FiniteTimeSingularity.timeDeriv (windowExt ω S) y t)
          = fun y => dtExt ω S y t := by
        funext y; exact timeDeriv_windowExt hS hdiff y t
      rw [heq]
      by_cases h : t ≤ 0
      · have heq2 : (fun y : Work.LWP.R3 => dtExt ω S y t)
            = fun y => FiniteTimeSingularity.timeDeriv ω y 0 := by
          funext y; exact dtExt_of_nonpos h
        rw [heq2]
        exact hdtmeas 0 h0mem
      · by_cases h2 : t ≤ S
        · have heq2 : (fun y : Work.LWP.R3 => dtExt ω S y t)
              = fun y => FiniteTimeSingularity.timeDeriv ω y t := by
            funext y; exact dtExt_of_mem_Icc ⟨le_of_lt (lt_of_not_ge h), h2⟩
          rw [heq2]
          exact hdtmeas t ⟨le_of_lt (lt_of_not_ge h), h2⟩
        · have heq2 : (fun y : Work.LWP.R3 => dtExt ω S y t)
              = fun y => FiniteTimeSingularity.timeDeriv ω y S := by
            funext y; exact dtExt_of_ge hS (le_of_lt (lt_of_not_ge h2))
          rw [heq2]
          exact hdtmeas S hSmem
  · intro t₀ _
    refine ⟨1, one_pos, fun t _ y => ?_⟩
    have heq : (fun s : ℝ => FiniteTimeSingularity.timeDeriv (windowExt ω S) y s)
        = fun s => dtExt ω S y s := by
      funext s; exact timeDeriv_windowExt hS hdiff y s
    rw [heq]
    exact continuousAt_dtExt hα hS hN₁ y t

end Work.CoreResiduals.BiotSavart
