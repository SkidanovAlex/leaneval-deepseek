import Mathlib
import Submission.Work.DSEQ0.Basic
import Submission.Work.DSEQ0.Model

namespace Work.DSEQ0

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory

universe u

-- The objects `((HomologicalComplex.single _ _ 0).obj A).X 0` and `A` are definitionally
-- equal, but not syntactically so; this option lets `rw`/`simp` use that definitional
-- equality when rewriting in the proof below (cf. `Mathlib/Algebra/Homology/Single.lean`).
set_option backward.isDefEq.respectTransparency false

/-- Morphisms out of a single-object cochain complex are determined by their component in the
degree where the complex is supported (`HomologicalComplex.to_single_hom_ext`), and the
component of `mkHomToSingle ψ hψ` is `ψ` followed by the structural isomorphism
`singleObjXSelf.inv`. We record the composite form needed below. -/
theorem mkHomToSingle_comp_f {V : Type*} [Category V] [HasZeroMorphisms V] [HasZeroObject V]
    {ι : Type*} [DecidableEq ι] {c : ComplexShape ι} {K K' : HomologicalComplex V c}
    {j : ι} {B : V} (g : K' ⟶ K) (ψ : K.X j ⟶ B)
    (hψ : ∀ i : ι, c.Rel i j → K.d i j ≫ ψ = 0) :
    (g ≫ HomologicalComplex.mkHomToSingle ψ hψ).f j =
      g.f j ≫ ψ ≫ (HomologicalComplex.singleObjXSelf c j B).inv := by
  rw [HomologicalComplex.comp_f, HomologicalComplex.mkHomToSingle_f]

/-- A complex `P` of `A`-modules with `P` acyclic in degrees `≤ -1` (only `P.X (-1) = 0` is
needed), a chain map `c : A[0] ⟶ P` and a functional `φ₀ : P⁰ ⟶ A` which sends the
coaugmentation class `c(1)` to a nonzero natural number `χ ∈ A` (in a local ring with residue
field of characteristic zero) have a chain-level retraction `φ : P ⟶ A[0]` of `c`.
Concretely `φ` is `(χ⁻¹ : A) • φ₀` in degree `0` and `0` in all other degrees. -/
theorem chainMap_retraction_of_functional {A : Type u} [CommRing A] [IsLocalRing A]
    [CharZero (IsLocalRing.ResidueField A)]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : CategoryTheory.Limits.IsZero (P.X (-1)))
    (c : Work.DSEQ0.singleZ A ⟶ P) (φ₀ : P.X 0 ⟶ ModuleCat.of A A) (χ : ℕ) (hχ : χ ≠ 0)
    (hφ₀ : φ₀ (c.f 0 (1 : A)) = (χ : A)) :
    ∃ φ : P ⟶ Work.DSEQ0.singleZ A, c ≫ φ = 𝟙 (Work.DSEQ0.singleZ A) := by
  -- `χ` is a unit of `A`, since the residue field has characteristic zero.
  let u : Aˣ := Work.DSEQ0.unitOfNatCast χ hχ
  have hu : (u : A) = (χ : A) := Work.DSEQ0.coe_unitOfNatCast χ hχ
  -- The degree `0` component of the candidate retraction: `χ⁻¹ • φ₀`.
  let ψ : P.X 0 ⟶ ModuleCat.of A A := ((u⁻¹ : Aˣ) : A) • φ₀
  -- `A[0]` is concentrated in degree `0`, so the only chain condition is at `-1 ⟶ 0`,
  -- where it holds because `P.X (-1)` is a zero object.
  have hψ : ∀ i : ℤ, (ComplexShape.up ℤ).Rel i 0 → P.d i 0 ≫ ψ = 0 := by
    intro i hi
    rw [ComplexShape.up_Rel] at hi
    have hi' : i = -1 := by omega
    subst hi'
    exact hP.eq_of_src _ 0
  -- The structural isomorphism identifying the degree `0` part of `A[0]` with `A`.
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)
  -- `c.f 0` read through `e` as a morphism `A ⟶ P.X 0`.
  let c₀ : ModuleCat.of A A ⟶ P.X 0 := e.inv ≫ c.f 0
  -- The crux: `χ⁻¹ • φ₀` retracts `c.f 0` in degree `0`.
  have h2 : c₀ ≫ ψ = 𝟙 (ModuleCat.of A A) := by
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
    dsimp only [ψ]
    simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
    rw [hφ₀, smul_eq_mul, ← hu]
    exact Units.inv_mul u
  refine ⟨HomologicalComplex.mkHomToSingle ψ hψ, ?_⟩
  -- Morphisms to a single-object complex are determined by their component in that degree.
  apply HomologicalComplex.to_single_hom_ext (j := 0)
  rw [mkHomToSingle_comp_f, HomologicalComplex.id_f]
  have hcf0 : c.f 0 = e.hom ≫ c₀ := (Iso.hom_inv_id_assoc e (c.f 0)).symm
  rw [hcf0, Category.assoc]
  have h3 : c₀ ≫ (ψ ≫ e.inv) = e.inv := by
    rw [← Category.assoc, h2, Category.id_comp]
  rw [h3, Iso.hom_inv_id e]

end Work.DSEQ0
