/-
# `HardyHyp` for `CoerAdm` with `α ≤ 1`

`Work.FTS.CoercivityFix.Coer1T.hardyHyp_of_coerAdm` proves `HardyHyp f` for `f ∈ CoerAdm α`
under the (vestigial) hypothesis `α ≤ 10⁻¹⁴`; its proof in fact only ever uses `α ≤ 1`.
Since the transfer defects `E1`, `E2` are stated for `α ≤ 1`, the same proof is recorded here
with the honest hypothesis.
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Vocab
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.FTS.H2.L12densIntegrable
import Submission.Work.FM.Core
import Submission.Work.FM.Core2
import Submission.Work.FTS.CoercivityFix.Coer1T.HardyBasic
import Submission.Work.FTS.CoercivityFix.Coer1T.HardyAlt.l12dens_continuousAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer.E1Parts

theorem hardyHyp_of_coerAdm_le_one (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) :
    Work.Coercivity.HardyHyp f := by
  obtain ⟨hreg, hvan, haxis, hl12⟩ := hf
  obtain ⟨hsm, hmem5, hbdry⟩ := hreg
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.CoercivityFix.Coer1T.HkMem_four_of_five α hsm hmem5
  have hint : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K f s)
      (Set.Ioi 0) := by
    have h := Work.FTS.H2.L12densIntegrable α f hα hα1 hsm hmem
    have h2 : Work.Elliptic.L12dens f = Work.FM.L12dens Work.Spaces.K f :=
      funext (fun z => Work.FTS.H2.L12dens_eq_FM_K f z)
    rwa [h2] at h
  have hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z :=
    fun z hz => Work.FTS.CoercivityFix.Coer1T.HardyAlt.l12dens_continuousAt α hsm hmem hz
  have hl12' : Work.Coercivity.L12f f 0 = 0 := by
    simpa [Work.Coercivity.L12f, Work.FM.L12, Work.Construction.L12] using hl12
  have hU : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi (0 : ℝ) := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith [h]
    · intro h
      rcases lt_trichotomy t 1 with h' | h' | h'
      · exact Or.inl ⟨h, h'.le⟩
      · exact Or.inl ⟨h, le_of_eq h'⟩
      · exact Or.inr h'
  refine ⟨?_, ?_, hint, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact Work.FTS.CoercivityFix.Coer1T.Kslice_integrableOn α hsm hmem hz
  · exact hcont
  · intro j hj
    rw [← hU]
    refine MeasureTheory.IntegrableOn.union ?_ ?_
    · exact Work.FTS.CoercivityFix.Coer1T.L12f_sq_div_small α hsm hmem hint hl12' hcont j hj
    · exact Work.FTS.CoercivityFix.Coer1T.L12f_sq_div_large α hsm hmem hint hcont j
  · intro j hj
    exact Work.FTS.CoercivityFix.Coer1T.intB_integrableOn α hsm hmem j hj
  · intro j hj
    exact Work.FTS.CoercivityFix.Coer1T.L12f_bd0 α hsm hmem hint hl12' j hj
  · intro j hj
    exact Work.FTS.CoercivityFix.Coer1T.L12f_bdTop α hsm hmem j

end Work.FTS.CoercivityFix.Transfer.E1Parts
