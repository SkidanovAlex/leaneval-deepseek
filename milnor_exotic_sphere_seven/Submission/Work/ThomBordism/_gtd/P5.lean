import Submission.Work.ThomBordism.tubeThomRepOfEmbeddingOdd

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom
open Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The inverse of the normal-bundle homeomorphism carries the nonzero vectors to the nonzero
complement. -/
theorem gtd_mem (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    ∀ p ∈ normalNonzero E, (eucNormalHomeomorph E ND).symm p ∈
      Work.Thom.zeroComplement (normalBundle E ND) := by
  intro p hp
  rw [Work.Thom.mem_zeroComplement]
  rw [mem_normalNonzero] at hp
  intro h0
  refine hp ?_
  have h1 : Work.Thom.fibreNorm (normalBundle E ND) ((eucNormalHomeomorph E ND).symm p) = 0 := by
    rw [Work.Thom.fibreNorm, h0, norm_zero]
  have hφ : Work.Tubular.bundleToNormal E ND ((eucNormalHomeomorph E ND).symm p) = p := by
    rw [← Work.Tubular.eucNormalHomeomorph_apply]
    exact (eucNormalHomeomorph E ND).apply_symm_apply p
  rw [Work.Tubular.fibreNorm_eq_normalNorm, hφ] at h1
  exact h1

/-- The pullback of the tautological Thom class along a bundle map `G` over a Gauss map, transported
to the concrete normal bundle `NormalTotal E`. -/
noncomputable def gtdU (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (G : C((normalBundle E ND).TotalSpace,
      (Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10)) :
    Work.Thom.RelCoh ℤ k (TopCat.of (NormalTotal E)) (normalNonzero E) :=
  (Work.Thom.relCohMap ((eucNormalHomeomorph E ND).symm : C(NormalTotal E,
      (normalBundle E ND).TotalSpace)) (normalNonzero E)
    (Work.Thom.zeroComplement (normalBundle E ND)) (gtd_mem E ND) ℤ k).hom
    ((Work.Thom.relCohMap G (Work.Thom.zeroComplement (normalBundle E ND))
      (Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10)) hgm ℤ k).hom
      (Grassmann.tautologicalThomClass k 10).τ)

end

end Work.ThomBordism
