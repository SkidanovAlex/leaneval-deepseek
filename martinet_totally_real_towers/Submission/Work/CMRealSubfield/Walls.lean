import Mathlib
import Submission.Commons.NumberTheory.NumberField.abs_discr_le_of_rootDiscr_le
import Submission.Work.CMRealSubfield.Defs
import Submission.Work.CMRealSubfield.RootDiscr.rootDiscr_le_of_abs_discr_le
import Submission.Work.CMRealSubfield.RealSubfield.finrank_eq_two_mul_finrank_maximalRealSubfield
import Submission.Work.CMRealSubfield.RealSubfield.finrank_maximalRealSubfield_eq_finrank_of_isTotallyReal
import Submission.Work.CMRealSubfield.RealSubfield.isCMField_iff_isTotallyComplex_and_finrank

/-!
# The ladder of weak walls

This module compares the walls introduced in `Submission.Work.CMRealSubfield.Defs`:

  `CMWall`  ⟹  `RealOrCMWall`-style structure  ⟹  `HalfRealSubfieldWall`  ⟹  `WeakWall`

where the implications are proved here (the first one is the definitional content of
"CM witnesses are in particular witnesses"):

* `halfRealSubfieldWall_of_cmWall` : a CM witness `L` has `[L : L⁺] = 2`, so its maximal real
  subfield has exactly half the degree;
* `halfRealSubfieldWall_of_realOrCMWall` : the same, with the totally real case handled by
  `L⁺ = L`;
* `weakWall_of_halfRealSubfieldWall` : the half-degree hypothesis is simply forgotten;
* `weakWall_iff_weakRootDiscrWall` : the bare wall is the same in absolute-discriminant and
  root-discriminant form (this uses `C > 0`).

The converse implications are **false**: the maximal real subfield of `ℚ(∜2, i)` (degree `8`)
is `ℚ(√2)` (degree `2`), so `WeakWall` does *not* imply `HalfRealSubfieldWall` by any
degree-theoretic argument.  Consequently the bare `WeakWall` cannot be fed into the elementary
real-subfield reduction; `benchmark_of_weakWall_of_halfDegreeRealSubfieldInput` in
`Submission.Work.CMRealSubfield.Reduction` records the missing input explicitly.
-/

open NumberField

set_option linter.style.haveILetI false

namespace Work.CMRealSubfield

/-- A CM wall is a half-degree-real-subfield wall: a CM field `L` satisfies
`[L : ℚ] = 2 * [L⁺ : ℚ]`. -/
theorem halfRealSubfieldWall_of_cmWall (h : CMWall) : HalfRealSubfieldWall := by
  obtain ⟨C, hC, hfam⟩ := h
  refine ⟨C, hC, fun N => ?_⟩
  obtain ⟨L, hF, hNF, hCM, hdeg, hdisc⟩ := hfam N
  letI := hF
  letI := hNF
  letI := hCM
  exact ⟨L, hF, hNF, hdeg, hdisc,
    le_of_eq (RealSubfield.finrank_eq_two_mul_finrank_maximalRealSubfield L)⟩

/-- A wall with totally real or CM witnesses is a half-degree-real-subfield wall. -/
theorem halfRealSubfieldWall_of_realOrCMWall (h : RealOrCMWall) : HalfRealSubfieldWall := by
  obtain ⟨C, hC, hfam⟩ := h
  refine ⟨C, hC, fun N => ?_⟩
  obtain ⟨L, hF, hNF, hTRorCM, hdeg, hdisc⟩ := hfam N
  letI := hF
  letI := hNF
  refine ⟨L, hF, hNF, hdeg, hdisc, ?_⟩
  rcases hTRorCM with hTR | hCM
  · letI := hTR
    rw [RealSubfield.finrank_maximalRealSubfield_eq_finrank_of_isTotallyReal L]
    omega
  · letI := hCM
    exact le_of_eq (RealSubfield.finrank_eq_two_mul_finrank_maximalRealSubfield L)

/-- The half-degree-real-subfield wall is in particular the bare weak wall. -/
theorem weakWall_of_halfRealSubfieldWall (h : HalfRealSubfieldWall) : WeakWall := by
  obtain ⟨C, hC, hfam⟩ := h
  exact ⟨C, hC, fun N => by
    obtain ⟨L, hF, hNF, hdeg, hdisc, _⟩ := hfam N
    exact ⟨L, hF, hNF, hdeg, hdisc⟩⟩

/-- A CM wall is in particular the bare weak wall. -/
theorem weakWall_of_cmWall (h : CMWall) : WeakWall :=
  weakWall_of_halfRealSubfieldWall (halfRealSubfieldWall_of_cmWall h)

/-- A totally-real-or-CM wall is in particular the bare weak wall. -/
theorem weakWall_of_realOrCMWall (h : RealOrCMWall) : WeakWall :=
  weakWall_of_halfRealSubfieldWall (halfRealSubfieldWall_of_realOrCMWall h)

/-- The bare weak wall in absolute-discriminant form implies the root-discriminant form
(here `C > 0` is used: the `d`-th root of `C ^ d` is `C`). -/
theorem weakRootDiscrWall_of_weakWall (h : WeakWall) : WeakRootDiscrWall := by
  obtain ⟨C, hC, hfam⟩ := h
  exact ⟨C, hC, fun N => by
    obtain ⟨L, hF, hNF, hdeg, hdisc⟩ := hfam N
    letI := hF
    letI := hNF
    exact ⟨L, hF, hNF, hdeg, RootDiscr.rootDiscr_le_of_abs_discr_le L rfl hC hdisc⟩⟩

/-- The bare weak wall in root-discriminant form implies the absolute-discriminant form. -/
theorem weakWall_of_weakRootDiscrWall (h : WeakRootDiscrWall) : WeakWall := by
  obtain ⟨C, hC, hfam⟩ := h
  exact ⟨C, hC, fun N => by
    obtain ⟨L, hF, hNF, hdeg, hrd⟩ := hfam N
    letI := hF
    letI := hNF
    exact ⟨L, hF, hNF, hdeg,
      Commons.NumberTheory.NumberField.abs_discr_le_of_rootDiscr_le rfl hrd⟩⟩

/-- The bare weak wall: absolute-discriminant and root-discriminant forms agree. -/
theorem weakWall_iff_weakRootDiscrWall : WeakWall ↔ WeakRootDiscrWall :=
  ⟨weakRootDiscrWall_of_weakWall, weakWall_of_weakRootDiscrWall⟩

/-- A wall whose witnesses are totally complex with a maximal real subfield of exactly half the
degree is a CM wall: `IsCMField K ↔ IsTotallyComplex K ∧ 2 * [K⁺ : ℚ] = [K : ℚ]`. -/
theorem cmWall_of_totallyComplexHalfWall (h : TotallyComplexHalfWall) : CMWall := by
  obtain ⟨C, hC, hfam⟩ := h
  refine ⟨C, hC, fun N => ?_⟩
  obtain ⟨L, hF, hNF, ⟨hTC, hhalf⟩, hdeg, hdisc⟩ := hfam N
  letI := hF
  letI := hNF
  haveI := hTC
  have hCM : NumberField.IsCMField L :=
    (RealSubfield.isCMField_iff_isTotallyComplex_and_finrank L).mpr ⟨hTC, hhalf⟩
  exact ⟨L, hF, hNF, hCM, hdeg, hdisc⟩

/-- A CM wall is a wall whose witnesses are totally complex with a maximal real subfield of
exactly half the degree. -/
theorem totallyComplexHalfWall_of_cmWall (h : CMWall) : TotallyComplexHalfWall := by
  obtain ⟨C, hC, hfam⟩ := h
  refine ⟨C, hC, fun N => ?_⟩
  obtain ⟨L, hF, hNF, hCM, hdeg, hdisc⟩ := hfam N
  letI := hF
  letI := hNF
  letI := hCM
  exact ⟨L, hF, hNF,
    ⟨NumberField.IsCMField.isTotallyComplex L,
      (RealSubfield.finrank_eq_two_mul_finrank_maximalRealSubfield L).symm⟩, hdeg, hdisc⟩

/-- `CMWall` is exactly the wall whose witnesses are totally complex with a maximal real
subfield of half the degree. -/
theorem cmWall_iff_totallyComplexHalfWall : CMWall ↔ TotallyComplexHalfWall :=
  ⟨totallyComplexHalfWall_of_cmWall, cmWall_of_totallyComplexHalfWall⟩

/-- A CM-extension wall is a CM wall (a totally complex quadratic extension of a totally real
field is CM). -/
theorem cmWall_of_cmExtensionWall (h : CMExtensionWall) : CMWall := by
  obtain ⟨C, hC, hfam⟩ := h
  refine ⟨C, hC, fun N => ?_⟩
  obtain ⟨F, hF, hNF, hTR, L, hL, hNL, hTC, hAlg, hQuad, hdeg, hdisc⟩ := hfam N
  letI := hF
  letI := hNF
  letI := hTR
  letI := hL
  letI := hNL
  letI := hTC
  letI := hAlg
  letI := hQuad
  exact ⟨L, hL, hNL, NumberField.IsCMField.ofCMExtension F L, hdeg, hdisc⟩

/-- A CM wall is a CM-extension wall: take the maximal real subfield `L⁺ ⊆ L`, which is totally
real, with `L` totally complex and `[L : L⁺] = 2`. -/
theorem cmExtensionWall_of_cmWall (h : CMWall) : CMExtensionWall := by
  obtain ⟨C, hC, hfam⟩ := h
  refine ⟨C, hC, fun N => ?_⟩
  obtain ⟨L, hF, hNF, hCM, hdeg, hdisc⟩ := hfam N
  letI := hF
  letI := hNF
  letI := hCM
  exact ⟨NumberField.maximalRealSubfield L, inferInstance, inferInstance, inferInstance,
    L, hF, hNF, NumberField.IsCMField.isTotallyComplex L,
    inferInstance, inferInstance, hdeg, hdisc⟩

/-- `CMWall` is exactly the wall with CM-extension witnesses. -/
theorem cmWall_iff_cmExtensionWall : CMWall ↔ CMExtensionWall :=
  ⟨cmExtensionWall_of_cmWall, cmWall_of_cmExtensionWall⟩

end Work.CMRealSubfield
