import Submission.Work.SphHomology.Defs
import Submission.Work.SphHomology.Main
import Submission.Work.Thom.sphereInDisc_homotopyEquiv
import Submission.Work.Cohomology.isZero_homology_of_homotopyEquiv
import Submission.Work.Tubular.exists_euclidean_normalBundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# From the sphere bundle of an abstract Euclidean model of the normal bundle to the concrete
complement of the zero section

`Work.SphHomology.homeo_normalTotal_zeroComplement`: a norm-preserving homeomorphism of the total
space of a Euclidean bundle with the normal total space of an embedded `8`-manifold restricts to a
homeomorphism of the complements of the zero section.

`Work.SphHomology.isZero_homology_normalTotal_compl_of_sphSub`: consequently, vanishing of the
homology of the sphere bundle of the abstract model gives vanishing of the homology of the concrete
complement of the zero section, through the deformation retraction of the complement of the zero
section onto the sphere bundle (`Work.Thom.sphereInDisc_homotopyEquiv`).
-/

open CategoryTheory AlgebraicTopology Limits
open scoped Topology
open Set

namespace Work.SphHomology

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ} {ι : Type}

/-- **The complement of the zero section in the concrete normal total space is homeomorphic to the
complement of the zero section in the abstract Euclidean model.** -/
theorem homeo_normalTotal_zeroComplement {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (nu : Work.TangentClasses.RealBundle V.pt (Work.Tubular.Euc k) ι)
    (hnu : Work.Thom.IsEuclidean nu)
    (phi : nu.TotalSpace ≃ₜ Work.Tubular.NormalTotal E)
    (hphi : ∀ p, Work.Thom.fibreNorm nu p = Work.Tubular.normalNorm E (phi p)) :
    Nonempty (↥{p : Work.Tubular.NormalTotal E | Work.Tubular.normalNorm E p ≠ 0} ≃ₜ
      ↥(Work.Thom.zeroComplement nu)) := by
  have hmem : ∀ q : nu.TotalSpace,
      phi q ∈ ({p : Work.Tubular.NormalTotal E | Work.Tubular.normalNorm E p ≠ 0}) ↔
        q ∈ Work.Thom.zeroComplement nu := by
    intro q
    simp only [Set.mem_setOf_eq, mem_zeroComplement_iff_fibreNorm_ne_zero, hphi q]
  have hmem' : ∀ p : Work.Tubular.NormalTotal E,
      phi.symm p ∈ Work.Thom.zeroComplement nu ↔
        p ∈ ({p : Work.Tubular.NormalTotal E | Work.Tubular.normalNorm E p ≠ 0}) := by
    intro p
    simp only [Set.mem_setOf_eq, mem_zeroComplement_iff_fibreNorm_ne_zero, hphi (phi.symm p),
      phi.apply_symm_apply]
  refine ⟨{ toFun := fun p => ⟨phi.symm (p : Work.Tubular.NormalTotal E),
                (hmem' (p : Work.Tubular.NormalTotal E)).mpr p.2⟩
            invFun := fun q => ⟨phi (q : nu.TotalSpace),
                (hmem (q : nu.TotalSpace)).mpr q.2⟩
            left_inv := fun p =>
              Subtype.ext (phi.apply_symm_apply (p : Work.Tubular.NormalTotal E))
            right_inv := fun q => Subtype.ext (phi.symm_apply_apply (q : nu.TotalSpace))
            continuous_toFun := (phi.symm.continuous.comp continuous_subtype_val).subtype_mk _
            continuous_invFun := (phi.continuous.comp continuous_subtype_val).subtype_mk _ }⟩

/-- **Vanishing of the homology of the concrete complement of the zero section, from the sphere
bundle of the abstract model.** -/
theorem isZero_homology_normalTotal_compl_of_sphSub
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    (nu : Work.TangentClasses.RealBundle V.pt (Work.Tubular.Euc k) ι)
    (hnu : Work.Thom.IsEuclidean nu)
    (phi : nu.TotalSpace ≃ₜ Work.Tubular.NormalTotal E)
    (hphi : ∀ p, Work.Thom.fibreNorm nu p = Work.Tubular.normalNorm E (phi p))
    (n : ℕ)
    (h : IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.Thom.SphSub nu))).homology n)) :
    IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of {p : Work.Tubular.NormalTotal E | Work.Tubular.normalNorm E p ≠ 0})).homology n) := by
  classical
  -- the sphere bundle is homotopy equivalent to the complement of the zero section
  obtain ⟨e₁⟩ := sphSub_homeo_sphereInDisc nu
  obtain ⟨e₂, -⟩ := Work.Thom.sphereInDisc_homotopyEquiv nu hnu
  have h₁ : IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(Work.Thom.sphereInDisc nu))).homology n) :=
    Work.Cohomology.isZero_homology_of_homotopyEquiv e₁.symm.toHomotopyEquiv n h
  have h₂ : IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(Work.Thom.zeroComplement nu))).homology n) :=
    Work.Cohomology.isZero_homology_of_homotopyEquiv e₂.symm n h₁
  obtain ⟨ψ⟩ := homeo_normalTotal_zeroComplement nu hnu phi hphi
  exact Work.Cohomology.isZero_homology_of_homotopyEquiv ψ.toHomotopyEquiv n h₂

end

end Work.SphHomology
