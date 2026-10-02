import Mathlib
import Submission.Work.ThomBordism.absThomCompare
import Submission.Work.ThomBordism.Grassmann.Torsion.ModelGeom

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

/-- **The tautological bundle carries a norm-like function.**  The witness is the Euclidean norm
`p ↦ ‖evalVec p‖` of the vector of the plane, supplied by
`Work.ThomBordism.Grassmann.Torsion.exists_fibreNormLike`; its continuity, non-negativity,
fibrewise homogeneity, vanishing locus and compact unit ball are exactly the fields of
`Work.ThomBordism.NormLike`. -/
theorem normLikeTautological (k m : ℕ) :
    Nonempty (Work.ThomBordism.NormLike
      (Work.ThomBordism.Grassmann.tautologicalBundle k m)) := by
  obtain ⟨f, hcont, hnonneg, hsmul, hzero, hcompact⟩ :=
    Work.ThomBordism.Grassmann.Torsion.exists_fibreNormLike k m
  exact ⟨{ f := f
           continuous_f := hcont
           nonneg := hnonneg
           smul := fun c hc p => hsmul c p hc
           eq_zero := hzero
           isCompact_le_one := hcompact }⟩

end Work.ThomBordism
