import Mathlib
import Submission.Work.Arithmetic.Defs
import Submission.Work.Motivic.resEquiv_of_morphism
import Submission.Work.TwistModel.resDeg_eq_zero_of_coheight_eq_zero_affineLine

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry

namespace Work.TwistModel

noncomputable section

/-- The structure morphism of `Spec 𝕜` over itself is the identity.  (The instance
`specOverSpec` gives `Spec.map (ofHom (algebraMap 𝕜 𝕜)) = Spec.map (𝟙 𝕜)`.) -/
lemma over_self_spec (𝕜 : Type) [Field 𝕜] :
    (Spec (CommRingCat.of 𝕜) ↘ Spec (CommRingCat.of 𝕜)) = 𝟙 (Spec (CommRingCat.of 𝕜)) := by
  have h : (Spec (CommRingCat.of 𝕜) ↘ Spec (CommRingCat.of 𝕜)) =
      Spec.map (𝟙 (CommRingCat.of 𝕜)) := rfl
  rw [h, Spec.map_id]

/-- Naturality of the structure map `resMap` along a section `p` of the structure morphism,
in the arithmetic vocabulary. -/
lemma resMap_naturality_arith {𝕜 : Type} [Field 𝕜] {C : Scheme}
    [C.Over (Spec (CommRingCat.of 𝕜))] (p : Spec (CommRingCat.of 𝕜) ⟶ C)
    (hp : p ≫ (C ↘ Spec (CommRingCat.of 𝕜)) = 𝟙 (Spec (CommRingCat.of 𝕜)))
    (pt : Spec (CommRingCat.of 𝕜)) :
    (p.residueFieldMap pt).hom.comp (Work.Arithmetic.resMap 𝕜 (p pt)) =
      Work.Arithmetic.resMap 𝕜 (X := Spec (CommRingCat.of 𝕜)) pt := by
  refine Work.Motivic.resMap_naturality p ?_ pt
  rw [hp, over_self_spec]

/-- **The residue field of the (unique) point of `Spec 𝕜`, as a `𝕜`-algebra, is `𝕜`.**  The
structure map `resMap 𝕜 pt : 𝕜 → κ(pt)` of `Spec 𝕜` over itself admits a retraction. -/
lemma exists_retract_resMap_spec_self (𝕜 : Type) [Field 𝕜]
    (pt : Spec (CommRingCat.of 𝕜)) :
    ∃ ψ : (Spec (CommRingCat.of 𝕜)).residueField pt →+* 𝕜,
      ψ.comp (Work.Arithmetic.resMap 𝕜 (X := Spec (CommRingCat.of 𝕜)) pt) = RingHom.id 𝕜 := by
  haveI : pt.asIdeal.IsPrime := pt.isPrime
  let R := Scheme.Spec.residueFieldIso (CommRingCat.of 𝕜) pt
  refine ⟨((pt.asIdeal.algEquivResidueFieldOfField).symm : pt.asIdeal.ResidueField →+* 𝕜).comp
    R.hom.hom, ?_⟩
  rw [resMap_spec_eq 𝕜 𝕜 pt]
  have h1 : ∀ y, R.hom.hom (R.inv.hom y) = y := by
    intro y
    have h := congrArg CommRingCat.Hom.hom (Iso.inv_hom_id R)
    rw [CommRingCat.hom_comp, CommRingCat.hom_id] at h
    exact (RingHom.ext_iff.mp h) y
  have h2 : ∀ c : 𝕜, algebraMap 𝕜 𝕜 c = c := fun c => rfl
  ext a
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [h1, h2, ← Ideal.algEquivResidueFieldOfField_apply]
  exact AlgEquiv.symm_apply_apply _ a

/-- A `𝕜`-algebra retraction of the structure map of the residue field at `x` forces the
residue degree at `x` to be `1`. -/
lemma resDeg_eq_one_of_retraction {𝕜 : Type} [Field 𝕜] {X : Scheme}
    [X.Over (Spec (CommRingCat.of 𝕜))] (x : X) (φ : X.residueField x →+* 𝕜)
    (hφ : φ.comp (Work.Arithmetic.resMap 𝕜 x) = RingHom.id 𝕜) :
    Work.Arithmetic.resDeg 𝕜 x = 1 := by
  letI : Algebra 𝕜 (X.residueField x) := (Work.Arithmetic.resMap 𝕜 x).toAlgebra
  have halg : algebraMap 𝕜 (X.residueField x) = Work.Arithmetic.resMap 𝕜 x :=
    RingHom.algebraMap_toAlgebra _
  have hφ' : ∀ c : 𝕜, φ (algebraMap 𝕜 (X.residueField x) c) = c := by
    intro c
    rw [halg]
    exact (RingHom.ext_iff.mp hφ) c
  change Module.finrank 𝕜 (X.residueField x) = 1
  let ψ : X.residueField x →ₐ[𝕜] 𝕜 := AlgHom.mk' φ fun c y => by
    rw [Algebra.smul_def, map_mul, hφ' c, Algebra.smul_def]
    simp
  have hinj : Function.Injective ψ := fun a b h => φ.injective h
  have hsurj : Function.Surjective ψ := fun c => ⟨algebraMap 𝕜 (X.residueField x) c, hφ' c⟩
  have e : X.residueField x ≃ₐ[𝕜] 𝕜 := AlgEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_self]

theorem closedPoint_resDeg_eq_one_of_hasRatPoint {𝕜 : Type} [Field 𝕜]
    {C : AlgebraicGeometry.Scheme}
    [AlgebraicGeometry.Scheme.Over C (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    (h : Work.Arithmetic.HasRatPoint 𝕜 C) :
    ∃ x : C, IsClosed ({x} : Set C) ∧ Work.Arithmetic.resDeg 𝕜 x = 1 := by
  obtain ⟨p, hp⟩ := h
  let pt : PrimeSpectrum 𝕜 := ⊥
  haveI hsub : Subsingleton ↥(Spec (CommRingCat.of 𝕜)) := inferInstance
  haveI hci : IsClosedImmersion p :=
    isClosedImmersion_of_comp_eq_id (C ↘ Spec (CommRingCat.of 𝕜)) p hp
  refine ⟨p pt, ?_, ?_⟩
  · have hclosed : IsClosed (Set.range p) := (IsClosedImmersion.isClosedEmbedding p).isClosed_range
    have hm : Set.range p = {p pt} := by
      have h1 : ∀ s : ↥(Spec (CommRingCat.of 𝕜)), p s = p pt :=
        fun s => congrArg p (Subsingleton.elim s pt)
      ext y
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨s, rfl⟩
        exact h1 s
      · intro hy
        exact ⟨pt, hy.symm⟩
    rwa [hm] at hclosed
  · obtain ⟨ψ, hψ⟩ := exists_retract_resMap_spec_self 𝕜 pt
    refine resDeg_eq_one_of_retraction (p pt) (ψ.comp (p.residueFieldMap pt).hom) ?_
    rw [RingHom.comp_assoc, resMap_naturality_arith p hp pt, hψ]

end

end Work.TwistModel
