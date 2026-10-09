/-
Copyright (c) 2025. All rights reserved.

# Realizability over `ℚ` in the language of the absolute Galois group

`Submission.RealizableOver ℚ G` says: some finite Galois extension of `ℚ` has Galois group `G`.
Classically this is stated as: `G` is a quotient of `G_ℚ = Gal(ℚ̄/ℚ)` by an *open* (equivalently
closed) subgroup, or equivalently `G` is a *continuous* quotient of `G_ℚ` (with `G` discrete).

This file proves that equivalence and records the vocabulary:

* `Work.AbsoluteGalois.IsGaloisQuotient G` — `G` is a quotient of `G_ℚ` by an open subgroup
  (topology-free in `G`, so easier to use than the `Continuous` phrasing);
* `realizableOver_iff_isGaloisQuotient` — the equivalence;
* `fixedField_ker_isGaloisQuotient` — the fixed field of the kernel of such a quotient map is a
  finite Galois extension of `ℚ` with Galois group `G`;
* `realizableOver_of_continuous_surjective`, `exists_continuous_surjective_of_realizableOver`,
  `realizableOver_iff_exists_continuous_surjective` — the same in the form asked for by the
  paper's proof (a continuous surjection `G_ℚ ↠ G` with `G` a finite discrete group);
* `IsGaloisQuotient.of_surjective` — `Submission.RealizableOver.of_surjective` (quotients of
  realizable groups are realizable) recovered in this language.

**Do not** be tempted to deduce from two surjections `G_ℚ ↠ G`, `G_ℚ ↠ H` that `G × H` is a
quotient of `G_ℚ`: the image of the product map `G_ℚ → G × H` is the fibre product over the
intersection of the fixed fields, which is in general strictly smaller than `G × H`.
-/
import Mathlib
import Submission.Realization
import Submission.Work.AbsoluteGalois.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteGalois

open scoped Classical

noncomputable section

/-! ## `G_ℚ`-quotients -/

/-- `IsGaloisQuotient G` means: `G` is a quotient of the absolute Galois group
`G_ℚ = Field.absoluteGaloisGroup ℚ` by an **open** subgroup, i.e. there is a surjective group
homomorphism `G_ℚ →* G` whose kernel is open for the Krull topology.  By infinite Galois theory
such a `φ` is precisely a continuous surjection onto the finite discrete group `G`, so this is the
classical notion of the absolute Galois group formulation of realizability. -/
def IsGaloisQuotient (G : Type*) [Group G] : Prop :=
  ∃ φ : Field.absoluteGaloisGroup ℚ →* G,
    IsOpen (φ.ker : Set (Field.absoluteGaloisGroup ℚ)) ∧ Function.Surjective φ

namespace IsGaloisQuotient

variable {G H : Type*} [Group G] [Group H]

/-- A continuous surjective homomorphism onto a discrete group is a Galois quotient. -/
theorem of_continuous_surjective [TopologicalSpace G] [DiscreteTopology G]
    (φ : Field.absoluteGaloisGroup ℚ →* G) (hcont : Continuous φ)
    (hsurj : Function.Surjective φ) : IsGaloisQuotient G := by
  refine ⟨φ, ?_, hsurj⟩
  have h1 : (φ.ker : Set (Field.absoluteGaloisGroup ℚ)) = φ ⁻¹' ({1} : Set G) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe, MonoidHom.mem_ker]
  rw [h1]
  exact hcont.isOpen_preimage {1} (isOpen_discrete {1})

set_option linter.style.haveILetI false in
/-- **The kernel of a Galois quotient is an open normal subgroup**, and the fixed field of that
kernel is a finite Galois extension of `ℚ` with Galois group `G`
(`fixedField_ker_isGaloisQuotient` below).  This is the fundamental theorem of infinite Galois
theory in the language of the absolute Galois group. -/
theorem exists_ker (h : IsGaloisQuotient G) :
    ∃ φ : Field.absoluteGaloisGroup ℚ →* G,
      IsOpen (φ.ker : Set (Field.absoluteGaloisGroup ℚ)) ∧ φ.ker.Normal ∧
        Function.Surjective φ := by
  obtain ⟨φ, hopen, hsurj⟩ := h
  exact ⟨φ, hopen, MonoidHom.normal_ker φ, hsurj⟩

/-- Conjugation by a group isomorphism preserves Galois quotients. -/
theorem of_mulEquiv (e : G ≃* H) (h : IsGaloisQuotient G) : IsGaloisQuotient H := by
  obtain ⟨φ, hopen, hsurj⟩ := h
  refine ⟨e.toMonoidHom.comp φ, ?_, e.surjective.comp hsurj⟩
  have hker : (e.toMonoidHom.comp φ).ker = φ.ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact map_eq_one_iff e.toMonoidHom e.injective (x := φ x)
  rw [hker]
  exact hopen

/-- A quotient of a Galois quotient is a Galois quotient: this is
`Submission.RealizableOver.of_surjective` in the language of `G_ℚ`. -/
theorem of_surjective (f : G →* H) (hf : Function.Surjective f)
    (h : IsGaloisQuotient G) : IsGaloisQuotient H := by
  obtain ⟨φ, hopen, hsurj⟩ := h
  refine ⟨f.comp φ, Subgroup.isOpen_mono ?_ hopen, hf.comp hsurj⟩
  intro x hx
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx ⊢
  rw [hx, map_one]

end IsGaloisQuotient

/-! ## From an open kernel surjection to a Galois extension of `ℚ` -/

/-- **The fixed field of the kernel.**  If `φ : G_ℚ →* G` is surjective with open kernel, then the
fixed field `L := fixedField φ.ker` of `ker φ` in `ℚ̄` is a finite Galois extension of `ℚ` whose
Galois group is `G`. -/
theorem fixedField_ker_isGaloisQuotient (G : Type*) [Group G]
    (φ : Field.absoluteGaloisGroup ℚ →* G)
    (hopen : IsOpen (φ.ker : Set (Field.absoluteGaloisGroup ℚ)))
    (hsurj : Function.Surjective φ) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ),
      L = IntermediateField.fixedField φ.ker ∧ FiniteDimensional ℚ L ∧ IsGalois ℚ L ∧
        Nonempty ((L ≃ₐ[ℚ] L) ≃* G) := by
  have hclosed : IsClosed (φ.ker : Set (Field.absoluteGaloisGroup ℚ)) :=
    Subgroup.isClosed_of_isOpen φ.ker hopen
  let H : ClosedSubgroup Gal(AlgebraicClosure ℚ/ℚ) := ⟨φ.ker, hclosed⟩
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField φ.ker
  have hfix : L.fixingSubgroup = φ.ker :=
    InfiniteGalois.fixingSubgroup_fixedField H
  have hfd : FiniteDimensional ℚ L := by
    refine (InfiniteGalois.isOpen_iff_finite L).mp ?_
    rw [hfix]
    exact hopen
  have hgal : IsGalois ℚ L :=
    IsGalois.of_fixedField_normal_subgroup φ.ker (hn := MonoidHom.normal_ker φ)
  haveI hnorm : (H : Subgroup Gal(AlgebraicClosure ℚ/ℚ)).Normal := MonoidHom.normal_ker φ
  refine ⟨L, rfl, hfd, hgal, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientKerEquivOfSurjective φ hsurj).symm.trans
    (InfiniteGalois.normalAutEquivQuotient H)).symm

/-- **A Galois quotient is realizable**: the converse of `isGaloisQuotient_of_realizableOver`. -/
theorem realizableOver_of_isGaloisQuotient (G : Type*) [Group G] (h : IsGaloisQuotient G) :
    Submission.RealizableOver ℚ G := by
  obtain ⟨φ, hopen, hsurj⟩ := h
  obtain ⟨L, -, hfd, hgal, ⟨e⟩⟩ := fixedField_ker_isGaloisQuotient G φ hopen hsurj
  exact ⟨↥L, inferInstance, inferInstance, hfd, hgal, ⟨e.symm⟩⟩

/-- A realization of `G` over `ℚ` gives a surjection `G_ℚ ↠ G` with open kernel. -/
theorem isGaloisQuotient_of_realizableOver (G : Type*) [Group G]
    (h : Submission.RealizableOver ℚ G) : IsGaloisQuotient G := by
  obtain ⟨L, hfd, hgal, ⟨e⟩⟩ := Submission.RealizableOver.toClosure h
  haveI : FiniteDimensional ℚ L := hfd
  haveI : IsGalois ℚ L := hgal
  haveI : Normal ℚ L := hgal.to_normal
  refine ⟨e.symm.toMonoidHom.comp (restrictHom L), ?_,
    e.symm.surjective.comp (restrictHom_surjective L)⟩
  have hker : (e.symm.toMonoidHom.comp (restrictHom L)).ker = (restrictHom L).ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact map_eq_one_iff e.symm.toMonoidHom e.symm.injective (x := (restrictHom L) x)
  rw [hker]
  exact restrictHom_ker_isOpen L

/-- **Realizability over `ℚ` in the language of the absolute Galois group**: `G` is realizable
over `ℚ` if and only if it is a quotient of `G_ℚ` by an open subgroup. -/
theorem realizableOver_iff_isGaloisQuotient (G : Type*) [Group G] :
    Submission.RealizableOver ℚ G ↔ IsGaloisQuotient G :=
  ⟨isGaloisQuotient_of_realizableOver G, realizableOver_of_isGaloisQuotient G⟩

/-! ## The same equivalence in the `Continuous` language -/

/-- The `←` direction in the form of a continuous surjection onto a finite discrete group. -/
theorem realizableOver_of_continuous_surjective (G : Type*) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (φ : Field.absoluteGaloisGroup ℚ →* G) (hcont : Continuous φ)
    (hsurj : Function.Surjective φ) : Submission.RealizableOver ℚ G :=
  realizableOver_of_isGaloisQuotient G (IsGaloisQuotient.of_continuous_surjective φ hcont hsurj)

/-- The `→` direction in the form of a continuous surjection onto a finite discrete group. -/
theorem exists_continuous_surjective_of_realizableOver (G : Type*) [Group G]
    [TopologicalSpace G] [DiscreteTopology G] (h : Submission.RealizableOver ℚ G) :
    ∃ φ : Field.absoluteGaloisGroup ℚ →* G, Continuous φ ∧ Function.Surjective φ := by
  obtain ⟨L, hfd, hgal, ⟨e⟩⟩ := Submission.RealizableOver.toClosure h
  haveI : FiniteDimensional ℚ L := hfd
  haveI : IsGalois ℚ L := hgal
  haveI : Normal ℚ L := hgal.to_normal
  haveI : DiscreteTopology (L ≃ₐ[ℚ] L) :=
    krullTopology_discreteTopology_of_finiteDimensional ℚ ↥L
  have hcont : Continuous (e.symm.toMonoidHom : (L ≃ₐ[ℚ] L) → G) := continuous_of_discreteTopology
  exact ⟨e.symm.toMonoidHom.comp (restrictHom L), hcont.comp (restrictHom_continuous L),
    e.symm.surjective.comp (restrictHom_surjective L)⟩

/-- **The absolute Galois group formulation of realizability over `ℚ`.**  A finite group `G`
(with the discrete topology) is the Galois group of a finite Galois extension of `ℚ` if and only
if there is a continuous surjective homomorphism `G_ℚ ↠ G`. -/
theorem realizableOver_iff_exists_continuous_surjective (G : Type*) [Group G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] :
    Submission.RealizableOver ℚ G ↔
      ∃ φ : Field.absoluteGaloisGroup ℚ →* G, Continuous φ ∧ Function.Surjective φ :=
  ⟨exists_continuous_surjective_of_realizableOver G,
    fun ⟨φ, hcont, hsurj⟩ => realizableOver_of_continuous_surjective G φ hcont hsurj⟩

end

end Work.AbsoluteGalois
