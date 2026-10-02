import Mathlib
import Submission.Work.Whitney.WSumChars
import Submission.Work.Whitney.continuous_tcmProj
import Submission.Work.ThomBordism.Grassmann.p1CruxRatNeZero
import Submission.Work.ThomBordism.Grassmann.isOpen_pieceFst_pieceSnd

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Whitney

/-- **The two pieces of the zero complement of a Whitney sum are open, and they cover it.**

For the two coordinate projections
`π1 p = ⟨p.1, ((sumFibreC m1 m2).symm p.2).1⟩`, `π2 p = ⟨p.1, ((sumFibreC m1 m2).symm p.2).2⟩` of the
total space of the Whitney sum, the two pieces `wsumPiece1 = π1 ⁻¹' (Z1_R ∖ 0)` and
`wsumPiece2 = π2 ⁻¹' (Z2_R ∖ 0)` (`Submission/Work/Whitney/WSumChars.lean`) are open in the total
space of `V = (Z1 (+) Z2)_R` and their union is `V ∖ 0`.  These are the three inputs that the
assembly `Work.Whitney.chernClass_whitneySum_top_of_thomProduct` and the relative formula
`Work.Whitney.thomClassRank_whitneySum_rel` take as hypotheses (`hAopen`, `hCopen`, `hset`), so this
statement packages exactly the geometric (non-cohomological) residue of the Whitney top-class
project.

ROUTE.  (a) The union: `p.2 ≠ 0` iff one of the two coordinates of `(sumFibreC m1 m2).symm p.2` is
nonzero (`Work.Whitney.sumFibreC` is a linear equivalence; use `map_eq_zero_iff`/`Prod.ext` and
`Work.ThomBordism.Grassmann.fstAB_or_sndAB_ne_zero`, or `sumFibreC_fstAB_sndAB`), and `p ∈ wsumPiece1`
iff `((sumFibreC m1 m2).symm p.2).1 ≠ 0`, so the union is `{p | p.2 ≠ 0} = zeroComplement V`.

(b) The openness: this is *immediate* from the continuity of the two projections and the openness of
the zero complement, with no chart-local input: `wsumPiece1 = π1 ⁻¹' zeroComplement (realification Z1)`
is the preimage of an open set under a continuous map.  The continuity is
`Work.Whitney.continuous_tcmProj` (`Submission/Work/Whitney/continuous_tcmProj.lean`), whose two
components are exactly the two lambda-terms of the statement, and the openness of the zero complement
of a real bundle is `Work.ThomBordism.Grassmann.isOpen_zeroComplement`
(`Submission/Work/ThomBordism/Grassmann/p1CruxRatNeZero.lean`, stated for an arbitrary `RealBundle`,
no finiteness).  Alternatively, `Work.ThomBordism.Grassmann.isOpen_pieceFst_aux` /
`isOpen_pieceSnd_aux` (`Submission/Work/ThomBordism/Grassmann/isOpen_pieceFst_pieceSnd.lean`) give
the openness on the subtype `↥(zeroComplement V)` for `[Fintype ι1] [Fintype ι2]`; the `[Fintype]`
instances in the statement are present for that route, though the first route does not need them. -/
theorem wsumPiece_open_union {B : Type} [TopologicalSpace B] {m₁ m₂ : ℕ}
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (π₁ : C((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₁).TotalSpace))
    (π₂ : C((Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂)).TotalSpace,
      (Work.Thom.realification Z₂).TotalSpace))
    (hπ₁ : ∀ p, π₁ p = ⟨p.1, ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).1⟩)
    (hπ₂ : ∀ p, π₂ p = ⟨p.1, ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).2⟩) :
    IsOpen (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁) ∧ IsOpen (Work.Whitney.wsumPiece2 Z₁ Z₂ π₂) ∧
      (Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ ∪ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂
        = Work.Thom.zeroComplement (Work.Thom.realification (Work.Whitney.whitneySum Z₁ Z₂))) := by
  -- the two pieces, read off in the fibre coordinates of the splitting `sumFibreC`
  have hmem1 : ∀ p, p ∈ Work.Whitney.wsumPiece1 Z₁ Z₂ π₁ ↔
      ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).1 ≠ 0 := by
    intro p
    rw [Work.Whitney.wsumPiece1, Set.mem_preimage, Work.Thom.mem_zeroComplement, hπ₁ p]
  have hmem2 : ∀ p, p ∈ Work.Whitney.wsumPiece2 Z₁ Z₂ π₂ ↔
      ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).2 ≠ 0 := by
    intro p
    rw [Work.Whitney.wsumPiece2, Set.mem_preimage, Work.Thom.mem_zeroComplement, hπ₂ p]
  refine ⟨?_, ?_, ?_⟩
  · -- openness: a preimage of the open zero complement under a continuous map
    exact (Work.ThomBordism.Grassmann.P1Crux.isOpen_zeroComplement
      (Work.Thom.realification Z₁)).preimage π₁.continuous
  · exact (Work.ThomBordism.Grassmann.P1Crux.isOpen_zeroComplement
      (Work.Thom.realification Z₂)).preimage π₂.continuous
  · -- the union: the vanishing of the fibre is the vanishing of both coordinates
    ext p
    rw [Set.mem_union, hmem1 p, hmem2 p, Work.Thom.mem_zeroComplement]
    have hp2 : (Work.Whitney.sumFibreC m₁ m₂) ((Work.Whitney.sumFibreC m₁ m₂).symm p.2)
        = (show EuclideanSpace ℂ (Fin (m₁ + m₂)) from p.2) :=
      (Work.Whitney.sumFibreC m₁ m₂).apply_symm_apply p.2
    have hz : (show EuclideanSpace ℂ (Fin (m₁ + m₂)) from p.2) = 0 ↔
        ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).1 = 0 ∧
        ((Work.Whitney.sumFibreC m₁ m₂).symm p.2).2 = 0 := by
      rw [← hp2, ContinuousLinearEquiv.map_eq_zero_iff]
      exact Prod.ext_iff
    constructor
    · rintro (h | h) h0
      · exact h (hz.mp h0).1
      · exact h (hz.mp h0).2
    · intro h
      by_contra hcon
      simp only [not_or, not_not] at hcon
      exact h (hz.mpr hcon)

end Work.Whitney
