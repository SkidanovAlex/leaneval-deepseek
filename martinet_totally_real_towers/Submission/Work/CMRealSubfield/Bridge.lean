import Mathlib
import Submission.Helpers
import Submission.Work.CMRealSubfield.Defs
import Submission.Work.CMRealSubfield.RootDiscr.rootDiscr_le_of_abs_discr_le
import Submission.Work.CMRealSubfield.RootDiscr.rootDiscr_maximalRealSubfield_le_rootDiscr
import Submission.Work.CMRealSubfield.RealSubfield.le_finrank_maximalRealSubfield_of_two_mul_le

/-!
# Bridge to the existing `Submission.Helpers` assembly

`Submission.Helpers` already contains the last mile of the source route: it turns a *totally
real* family of unbounded degree with bounded root discriminant
(`Submission.Helpers.rootDiscrFamily C`) into the benchmark statement
(`Submission.Helpers.exists_totallyReal_discr_le_of_rootDiscrFamily`).  This module shows that
the CM walls of `Submission.Work.CMRealSubfield.Defs` produce exactly that family, so the
whole chain

  `CMWall`  ⟶  `Submission.Helpers.rootDiscrFamily C`  ⟶  benchmark

is available with no duplication: the total-reality input that `Submission.Helpers` expects is
manufactured from the maximal real subfields of the CM witnesses.
-/

open NumberField

set_option linter.style.haveILetI false

namespace Work.CMRealSubfield

/-- A CM wall produces the totally real root-discriminant family of `Submission.Helpers`,
with the same constant. -/
theorem exists_rootDiscrFamily_of_cmWall (h : CMWall) :
    ∃ C : ℝ, 0 < C ∧ Submission.Helpers.rootDiscrFamily C := by
  obtain ⟨C, hC, hfam⟩ := h
  refine ⟨C, hC, fun N => ?_⟩
  obtain ⟨L, hF, hNF, hCM, hdeg, hdisc⟩ := hfam (2 * N)
  letI := hF
  letI := hNF
  letI := hCM
  refine ⟨Module.finrank ℚ (NumberField.maximalRealSubfield L),
    RealSubfield.le_finrank_maximalRealSubfield_of_two_mul_le L hdeg,
    NumberField.maximalRealSubfield L, inferInstance, inferInstance, inferInstance, rfl, ?_⟩
  exact le_trans (RootDiscr.rootDiscr_maximalRealSubfield_le_rootDiscr L)
    (RootDiscr.rootDiscr_le_of_abs_discr_le L rfl hC hdisc)

/-- A half-degree-real-subfield wall produces the totally real root-discriminant family of
`Submission.Helpers`, with the same constant. -/
theorem exists_rootDiscrFamily_of_halfRealSubfieldWall (h : HalfRealSubfieldWall) :
    ∃ C : ℝ, 0 < C ∧ Submission.Helpers.rootDiscrFamily C := by
  obtain ⟨C, hC, hfam⟩ := h
  refine ⟨C, hC, fun N => ?_⟩
  obtain ⟨L, hF, hNF, hdeg, hdisc, hhalf⟩ := hfam (2 * N)
  letI := hF
  letI := hNF
  refine ⟨Module.finrank ℚ (NumberField.maximalRealSubfield L), ?_,
    NumberField.maximalRealSubfield L, inferInstance, inferInstance, inferInstance, rfl, ?_⟩
  · omega
  · exact le_trans (RootDiscr.rootDiscr_maximalRealSubfield_le_rootDiscr L)
      (RootDiscr.rootDiscr_le_of_abs_discr_le L rfl hC hdisc)

/-- The CM wall gives the benchmark *through the existing `Submission.Helpers` assembly*
(this is the same statement as `Work.CMRealSubfield.benchmark_of_cmWall`, obtained by a
different route, up to the definitional equality of the two `Prop`s). -/
theorem benchmark_of_cmWall_via_helpers (h : CMWall) : Benchmark :=
  Submission.Helpers.exists_totallyReal_discr_le_of_rootDiscrFamily
    (exists_rootDiscrFamily_of_cmWall h)

end Work.CMRealSubfield
