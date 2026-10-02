import Mathlib
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.Tubular.LocalDegreeAll
import Submission.Work.ThomBordism.nonempty_thomClass_normalBundle
import Submission.Work.ThomBordism.cohEightMan8
import Submission.Work.Thom.ATools
import Submission.Work.Cohomology.relComplex_empty_homology_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

/-! ## The two cases of the codimension

`Work.Tubular.NormalTotal E` is the total space of the normal bundle of the embedding
`E : EmbeddingData V (8 + k)`, and `Work.Tubular.normalNonzero E` is the complement of its zero
section.  The top relative cohomology of the pair is `ℤ` in both cases:

* for `k ≥ 1` the normal bundle is a genuine Euclidean bundle of rank `k` with an integral Thom
  class (`Work.ThomBordism.nonempty_thomClass_normalBundle`), and the Thom isomorphism
  `H^8(V) ≅ H^{8+k}(ν, ν∖0)` transfers along the homeomorphism of pairs
  `Work.Tubular.eucNormalHomeomorph`, while `H^8(V) ≅ ℤ` is `Work.ThomBordism.cohEightMan8`;
* for `k = 0` the normal space is `0`-dimensional, so the zero section is all of `ν` and `ν` is
  homeomorphic to `V`; the relative cohomology relative to the empty set is absolute cohomology
  (`Work.Cohomology.relComplex_empty_homology_iso`). -/

/-- **The codimension-zero case.**  For an embedding `E : EmbeddingData V 8` of an `8`-manifold into
`ℝ⁸` the tangent space is all of `ℝ⁸`, so the normal space is `0`-dimensional: the zero section is
all of `NormalTotal E`, the base of the pair is empty, and `H⁸(ν, ∅) = H⁸(ν) ≅ H⁸(V) ≅ ℤ`. -/
private theorem relCohThomPairNormalTotal_iso_int_zero {V : Work.ThomBordism.Man8}
    [ConnectedSpace V.pt] (E : Work.ThomBordism.PontryaginThom.EmbeddingData V 8) :
    Nonempty (Work.Thom.RelCoh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) ≅ ModuleCat.of ℤ ℤ) := by
  classical
  haveI hpc : PathConnectedSpace V.pt := Work.Tubular.pathConnectedSpace_of_man8 V
  -- the normal space is trivial
  have hbot : ∀ x : V.pt, Work.Tubular.normalSpace E x = ⊥ := by
    intro x
    have h := Work.Tubular.finrank_normalSpace E x
    have h0 : Module.finrank ℝ ↥(Work.Tubular.normalSpace E x) = 0 := by
      rw [h]
    exact Submodule.finrank_eq_zero.mp h0
  have hzero : ∀ x : V.pt, (0 : Work.Tubular.Euc 8) ∈ Work.Tubular.normalSpace E x := by
    intro x
    rw [hbot x]
    exact Submodule.zero_mem _
  -- the zero section is everything
  have hnn : Work.Tubular.normalNonzero E = (∅ : Set (Work.Tubular.NormalTotal E)) := by
    ext p
    rw [Work.Tubular.mem_normalNonzero, Set.mem_empty_iff_false, iff_false]
    intro h
    apply h
    have h3 : p.1.2 ∈ Work.Tubular.normalSpace E p.1.1 := p.2
    rw [hbot p.1.1] at h3
    have hp : p.1.2 = 0 := by simpa using h3
    show Work.Tubular.normalNorm E p = 0
    rw [Work.Tubular.normalNorm, hp, norm_zero]
  -- the projection to the base is a homeomorphism
  let hom : Work.Tubular.NormalTotal E ≃ₜ V.pt :=
    { toFun := fun p => p.1.1
      invFun := fun x => ⟨(x, 0), hzero x⟩
      left_inv := by
        intro p
        refine Subtype.ext (Prod.ext rfl ?_)
        have h3 : p.1.2 ∈ Work.Tubular.normalSpace E p.1.1 := p.2
        rw [hbot p.1.1] at h3
        have h4 : p.1.2 = 0 := by simpa using h3
        exact h4.symm
      right_inv := by
        intro x
        rfl
      continuous_toFun := continuous_subtype_val.fst
      continuous_invFun := Continuous.subtype_mk
        (continuous_id.prodMk (continuous_const : Continuous fun _ : V.pt =>
          (0 : Work.Tubular.Euc 8))) hzero }
  have htriv : ∀ x : Work.Tubular.NormalTotal E,
      (x ∈ (∅ : Set (Work.Tubular.NormalTotal E))) ↔ hom x ∈ (∅ : Set V.pt) := by
    intro x
    simp
  have hbij := Work.Thom.bijective_relCohMap_of_homeomorphA
    (∅ : Set (Work.Tubular.NormalTotal E)) (∅ : Set V.pt) hom htriv ℤ 8
  let l1 : Work.Thom.RelCoh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E))
      (∅ : Set (Work.Tubular.NormalTotal E)) ≃ₗ[ℤ]
      Work.Thom.RelCoh ℤ 8 (TopCat.of V.pt) (∅ : Set V.pt) :=
    (LinearEquiv.ofBijective _ hbij).symm
  haveI hiso : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relIncl ℤ (TopCat.of V.pt) ∅) 8) :=
    Work.Cohomology.relComplex_empty_homology_iso (TopCat.of V.pt) 8
  let e2 := CategoryTheory.asIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relIncl ℤ (TopCat.of V.pt) ∅) 8)
  let l2 : Work.Thom.RelCoh ℤ 8 (TopCat.of V.pt) (∅ : Set V.pt) ≃ₗ[ℤ]
      Work.Thom.Coh ℤ 8 V.pt :=
    Work.Cohomology.redH0_linEquivOfIso e2
  obtain ⟨e8⟩ := Work.ThomBordism.cohEightMan8 V
  let l3 : Work.Thom.Coh ℤ 8 V.pt ≃ₗ[ℤ] ℤ := Work.Cohomology.redH0_linEquivOfIso e8
  refine ⟨?_⟩
  rw [hnn]
  exact LinearEquiv.toModuleIso (l1.trans (l2.trans l3))

/-- **The positive-codimension case.**  For `k ≥ 1` the normal bundle of `E : EmbeddingData V (8+k)`
is a Euclidean real bundle of rank `k` with an integral Thom class; the Thom isomorphism
`H^8(V) ≅ H^{8+k}(ν, ν∖0)` and the homeomorphism of pairs `ν ≅ NormalTotal E` identify the top
relative cohomology with `H^8(V) ≅ ℤ`. -/
private theorem relCohThomPairNormalTotal_iso_int_pos {V : Work.ThomBordism.Man8}
    [ConnectedSpace V.pt] {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) :
    Nonempty (Work.Thom.RelCoh ℤ (8 + k) (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) ≅ ModuleCat.of ℤ ℤ) := by
  classical
  haveI hpc : PathConnectedSpace V.pt := Work.Tubular.pathConnectedSpace_of_man8 V
  obtain ⟨ND⟩ := Work.ThomBordism.PontryaginThom.exists_normalData_of_immersion (V := V) (k := k)
    E.e (E.smooth.of_le (by simp)) E.injective_mfderiv
  obtain ⟨T⟩ := Work.ThomBordism.nonempty_thomClass_normalBundle hk E ND
  -- the pair `(ν, ν∖0)` of the Euclidean bundle and its comparison with `(NormalTotal, normalNonzero)`
  have hspot : ∀ p : (Work.Tubular.normalBundle E ND).TotalSpace,
      p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND) ↔
        Work.Thom.fibreNorm (Work.Tubular.normalBundle E ND) p ≠ 0 := by
    intro p
    rw [Work.Thom.mem_zeroComplement, Work.Thom.fibreNorm, norm_ne_zero_iff]
  have hiff : ∀ p : (Work.Tubular.normalBundle E ND).TotalSpace,
      p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND) ↔
        Work.Tubular.eucNormalHomeomorph E ND p ∈ Work.Tubular.normalNonzero E := by
    intro p
    rw [hspot p, Work.Tubular.mem_normalNonzero, Work.Tubular.eucNormalHomeomorph_apply,
      ← Work.Tubular.fibreNorm_eq_normalNorm E ND p]
  let φc : C((Work.Tubular.normalBundle E ND).TotalSpace, Work.Tubular.NormalTotal E) :=
    Work.Tubular.eucNormalHomeomorph E ND
  let hf : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      φc p ∈ Work.Tubular.normalNonzero E := fun p hp => (hiff p).mp hp
  have hbij : Function.Bijective ((Work.Thom.relCohMap φc
      (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
      (Work.Tubular.normalNonzero E) hf ℤ (8 + k)).hom) :=
    Work.Thom.bijective_relCohMap_of_homeomorphA
      (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
      (Work.Tubular.normalNonzero E) (Work.Tubular.eucNormalHomeomorph E ND) hiff ℤ (8 + k)
  let eφ : Work.Thom.RelCoh ℤ (8 + k) (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E) ≃ₗ[ℤ]
      Work.Thom.OpenThom (Work.Tubular.normalBundle E ND) (8 + k) :=
    LinearEquiv.ofBijective _ hbij
  let eT : Work.Thom.Coh ℤ 8 V.pt ≃ₗ[ℤ]
      Work.Thom.OpenThom (Work.Tubular.normalBundle E ND) (8 + k) := T.thomEquiv 8
  obtain ⟨e8⟩ := Work.ThomBordism.cohEightMan8 V
  let eB : Work.Thom.Coh ℤ 8 V.pt ≃ₗ[ℤ] ℤ := Work.Cohomology.redH0_linEquivOfIso e8
  exact ⟨LinearEquiv.toModuleIso (eφ.trans (eT.symm.trans eB))⟩

/-- The top relative cohomology of the Thom pair of the normal bundle of an embedded closed
oriented smooth `8`-manifold is `ℤ`: the Thom isomorphism identifies `H^{8+k}(ν, ν∖0)` with
`H^8(V)`, which is `ℤ` for a closed connected oriented `8`-manifold
(`Work.ThomBordism.cohEightMan8`).  Here `ν = NormalTotal E` and `ν∖0 = normalNonzero E`. -/
theorem relCohThomPairNormalTotal_iso_int {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
    {k : ℕ} (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) :
    Nonempty (Work.Thom.RelCoh ℤ (8 + k) (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) ≅ ModuleCat.of ℤ ℤ) := by
  rcases k with _ | k
  · exact relCohThomPairNormalTotal_iso_int_zero E
  · exact relCohThomPairNormalTotal_iso_int_pos (Nat.succ_pos k) E

end

end Work.ThomBordism
