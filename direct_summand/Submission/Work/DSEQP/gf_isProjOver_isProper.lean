import Mathlib
import Submission.Work.DSMap.Gaps

/-!
# `Work.DSEQP.gf_isProjOver_isProper`

If `f : X ⟶ Spec A` factors as a closed immersion into a projective space `ℙᴺ_A`
(`DSMap.IsProjOver A f`), then `f` is proper: a closed immersion is proper and `ℙᴺ_A` is
proper over `Spec A`.

Mathlib has properness of `Proj 𝒜 ⟶ Spec (𝒜 0)` (`AlgebraicGeometry.Proj.toSpecZero`) as
soon as the total ring is of finite type over `𝒜 0`.  For the polynomial ring
`𝒜 = MvPolynomial.homogeneousSubmodule (Fin (N+1)) A` the one instance that is missing is

`Algebra.FiniteType ↥(𝒜 0) (MvPolynomial (Fin (N+1)) A)`,

which we supply here: the degree-zero part of the polynomial ring is the copy of `A` given
by the constants (`R → ↥(𝒜 0)`, `a ↦ C a`, is an isomorphism), and `X 0, …, X N` generate
the polynomial ring over it.  The structure map `ℙᴺ_A ⟶ Spec A` is then the composite of
`Proj.toSpecZero 𝒜` with `Spec.map` of the isomorphism `A ≅ 𝒜 0`.

## Main results

* `Work.DSEQP.bijective_algebraMap_homogeneousSubmodule_zero`
* `Work.DSEQP.finiteType_subtype_homogeneousSubmodule_zero`
* `Work.DSEQP.isProper_PSpace_toSpec`
* `Work.DSEQP.gf_isProjOver_isProper`
-/

universe a

namespace Work.DSEQP

open CategoryTheory AlgebraicGeometry

-- `MvPolynomial.homogeneousSubmodule` is a graded algebra, but Mathlib deliberately does not
-- register the instance globally (`MvPolynomial.gradedAlgebra`), so enable it locally.
attribute [local instance] MvPolynomial.gradedAlgebra

/-- For `𝒜 = MvPolynomial.homogeneousSubmodule σ R` the degree-zero part is the subring of
constants, so `a ↦ C a` is a bijection `R → ↥(𝒜 0)`. -/
lemma bijective_algebraMap_homogeneousSubmodule_zero {R : Type*} [CommRing R] {σ : Type*} :
    Function.Bijective (algebraMap R ↥(MvPolynomial.homogeneousSubmodule σ R 0)) := by
  constructor
  · intro a b h
    have h' := congrArg Subtype.val h
    simp only [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq] at h'
    exact MvPolynomial.C_injective σ R h'
  · rintro ⟨p, hp⟩
    refine ⟨p.coeff 0, Subtype.ext ?_⟩
    rw [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq]
    have h0 : p.totalDegree = 0 := le_antisymm hp.totalDegree_le (Nat.zero_le _)
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0).symm

/-- The polynomial ring is of finite type over its degree-zero part (the constants): the
variables generate it, and the constants are in the degree-zero part. -/
lemma finiteType_subtype_homogeneousSubmodule_zero {R : Type*} [CommRing R] {σ : Type*}
    [Fintype σ] :
    Algebra.FiniteType ↥(MvPolynomial.homogeneousSubmodule σ R 0) (MvPolynomial σ R) := by
  classical
  refine ⟨Finset.univ.image (MvPolynomial.X (R := R) : σ → MvPolynomial σ R), ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  refine le_antisymm le_top ?_
  intro p _
  refine MvPolynomial.induction_on p ?_ ?_ ?_
  · intro a
    have h : (algebraMap ↥(MvPolynomial.homogeneousSubmodule σ R 0) (MvPolynomial σ R))
        ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C σ a⟩ = MvPolynomial.C a :=
      SetLike.GradeZero.algebraMap_apply _ _
    rw [← h]
    exact Subalgebra.algebraMap_mem _ _
  · intro p q hp hq
    exact add_mem hp hq
  · intro p i hp
    exact mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self i))

/-- **`ℙᴺ_A` is proper over `Spec A`.**  `PSpace.toSpec A N` is `Proj.toSpecZero 𝒜`
composed with `Spec.map` of the ring isomorphism `A ≅ 𝒜 0`; the first factor is proper by
Mathlib's instance for `Proj.toSpecZero` (whose finite type hypothesis we provide by
`finiteType_subtype_homogeneousSubmodule_zero`) and the second is an isomorphism. -/
theorem isProper_PSpace_toSpec (A : Type a) [CommRing A] (N : ℕ) :
    AlgebraicGeometry.IsProper (DSMap.PSpace.toSpec A N) := by
  have hft : Algebra.FiniteType ↥(DSMap.PGr A N 0) (MvPolynomial (Fin (N + 1)) A) :=
    finiteType_subtype_homogeneousSubmodule_zero
  have hp : IsProper (Proj.toSpecZero (DSMap.PGr A N)) := inferInstance
  have hi : IsIso (Spec.map (CommRingCat.ofHom (algebraMap A (DSMap.PGr A N 0)))) := by
    rw [isIso_SpecMap_iff]
    exact bijective_algebraMap_homogeneousSubmodule_zero
  rw [DSMap.PSpace.toSpec]
  exact inferInstance

/-- A morphism `f : X ⟶ Spec A` factoring through a closed immersion into a projective
space is proper (composition of a closed immersion with the proper structure map of `ℙᴺ_A`). -/
theorem gf_isProjOver_isProper (A : Type a) [CommRing A] (X : AlgebraicGeometry.Scheme.{a})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) (hp : DSMap.IsProjOver A f) :
    AlgebraicGeometry.IsProper f := by
  obtain ⟨N, i, _hci, hfac⟩ := hp
  have hp' : IsProper (DSMap.PSpace.toSpec A N) := isProper_PSpace_toSpec A N
  rw [← hfac]
  exact inferInstance

end Work.DSEQP
