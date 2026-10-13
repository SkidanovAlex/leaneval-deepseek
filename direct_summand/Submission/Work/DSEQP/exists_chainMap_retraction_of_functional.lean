import Mathlib

namespace Work.DSEQP

open CategoryTheory Limits

universe u

-- The objects `((HomologicalComplex.single _ _ 0).obj A).X 0` and `A` are definitionally
-- equal, but not syntactically so; this option lets `rw`/`simp` use that definitional
-- equality when rewriting in the proof below (cf. `Mathlib/Algebra/Homology/Single.lean`).
set_option backward.isDefEq.respectTransparency false

/-- Component in degree `j` of the composite `g ≫ mkHomToSingle ψ hψ`.  The component of
`mkHomToSingle ψ hψ` in degree `j` is `ψ` followed by the structural isomorphism
`singleObjXSelf.inv` (see `Mathlib/Algebra/Homology/Single.lean`), and this is the composite
form needed below. -/
theorem mkHomToSingle_comp_f {V : Type*} [Category V] [HasZeroMorphisms V] [HasZeroObject V]
    {ι : Type*} [DecidableEq ι] {c : ComplexShape ι} {K K' : HomologicalComplex V c}
    {j : ι} {B : V} (g : K' ⟶ K) (ψ : K.X j ⟶ B)
    (hψ : ∀ i : ι, c.Rel i j → K.d i j ≫ ψ = 0) :
    (g ≫ HomologicalComplex.mkHomToSingle ψ hψ).f j =
      g.f j ≫ ψ ≫ (HomologicalComplex.singleObjXSelf c j B).inv := by
  rw [HomologicalComplex.comp_f, HomologicalComplex.mkHomToSingle_f]

/-- A complex `P` of `A`-modules vanishing in degree `-1`, a chain map
`c : A[0] ⟶ P` from the single complex concentrated in degree `0`, and a functional
`φ₀ : P⁰ ⟶ A` which sends the coaugmentation class `c(1)` to `1` admit a chain-level
retraction `φ : P ⟶ A[0]` of `c`.  Concretely `φ` is `φ₀` in degree `0` and `0` in all
other degrees: the only chain condition to check is at `-1 ⟶ 0`, where it holds because
`P.X (-1)` is a zero object. -/
theorem exists_chainMap_retraction_of_functional {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : IsZero (P.X (-1)))
    (c : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶ P)
    (φ₀ : P.X 0 ⟶ ModuleCat.of A A) (hφ₀ : φ₀ (c.f 0 (1 : A)) = 1) :
    ∃ φ : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A),
      c ≫ φ = 𝟙 _ := by
  -- `A[0]` is concentrated in degree `0`, so the only chain condition is at `-1 ⟶ 0`,
  -- where it holds because `P.X (-1)` is a zero object.
  have hψ : ∀ i : ℤ, (ComplexShape.up ℤ).Rel i 0 → P.d i 0 ≫ φ₀ = 0 := by
    intro i hi
    rw [ComplexShape.up_Rel] at hi
    have hi' : i = -1 := by omega
    subst hi'
    exact hP.eq_of_src _ 0
  -- The structural isomorphism identifying the degree `0` part of `A[0]` with `A`.
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)
  -- `c.f 0` read through `e` as a morphism `A ⟶ P.X 0`.
  let c₀ : ModuleCat.of A A ⟶ P.X 0 := e.inv ≫ c.f 0
  -- The crux: `φ₀` retracts `c.f 0` in degree `0`.
  have h2 : c₀ ≫ φ₀ = 𝟙 (ModuleCat.of A A) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    rw [ConcreteCategory.comp_apply]
    dsimp only [c₀]
    rw [ConcreteCategory.comp_apply]
    rw [ConcreteCategory.id_apply]
    have hei : e.inv (1 : A) = (1 : A) := by
      dsimp only [e]
      simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
        HomologicalComplex.single]
    rw [hei]
    exact hφ₀
  refine ⟨HomologicalComplex.mkHomToSingle φ₀ hψ, ?_⟩
  -- Morphisms to a single-object complex are determined by their component in that degree.
  apply HomologicalComplex.to_single_hom_ext (j := 0)
  rw [mkHomToSingle_comp_f, HomologicalComplex.id_f]
  have hcf0 : c.f 0 = e.hom ≫ c₀ := (Iso.hom_inv_id_assoc e (c.f 0)).symm
  rw [hcf0, Category.assoc]
  have h3 : c₀ ≫ (φ₀ ≫ e.inv) = e.inv := by
    rw [← Category.assoc, h2, Category.id_comp]
  rw [h3, Iso.hom_inv_id e]

end Work.DSEQP
