import Mathlib
import Submission.Work.DescentGeom.Basic
import Submission.Work.DescentGeom.Kit
import Submission.Work.DescentGeom.Transfer
import Submission.Work.DescentGeom.Group
import Submission.Work.DescentGeom.AbelJacobi
import Submission.Work.DescentGeom.Geom
import Submission.Work.DescentGeom.JExists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `DescentGeom` — the universal property and the generation property of `AJ`

This file proves `Work.DescentGeom.univ_and_epi`: for the descended Jacobian `D.J` of the chart
datum `D : Input C P0` over the finite Galois extension `k'`,

* the Abel–Jacobi map `AJ D : C ⟶ D.J` is universal for morphisms `f : C ⟶ A` into a group
  scheme `A` over `k` which is smooth, proper and geometrically irreducible and which sends the
  base point `P0` to the origin, and
* `AJ D` is an epimorphism on such targets.

Both statements are proved by base change to `k'` and Galois descent:

* the universal property over `k'` (`Input.univ'`, applied to `A_{k'}`, whose base point condition
  is `map_eta_bc`) produces the unique `g' : G' ⟶ A_{k'}` with `f_{k'} = AJ' ≫ g'`;
* the generation property over `k'` (`Input.epi'`, applied to `A_{k'}`) shows that the conjugate
  `a ≫ g' ≫ c⁻¹` of `g'` by the Galois action is again an `Over`-morphism with `AJ' ≫ · = f_{k'}`,
  hence that `g'` is Galois-equivariant (`UnivEpi.eqv_lift`);
* the equivariance of `g'` makes `Ψ := bcIso.hom ≫ g'` a morphism of descent data, so that
  `Φ := Ψ.left ≫ bcπ k' A` is `Γ`-invariant and descends to a `k`-morphism `g : J ⟶ A` with
  `f = AJ ≫ g`;
* faithfulness of base change (`map_injective`) together with `Input.epi'` gives the uniqueness of
  `g` and the generation property.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.DescentGeom

open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory MonObj MonoidalCategory
open CartesianMonoidalCategory

universe u

namespace UnivEpi

noncomputable section

variable {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']

/-- The inverse of the Galois action of `σ` on the base change `X_{k'}` is the action of `σ⁻¹`. -/
theorem galAct_mul_inv (X : Sch k) (σ : Work.Descent.Gal k k') :
    Work.Descent.galAct X σ ≫ Work.Descent.galAct X σ⁻¹ = 𝟙 _ := by
  rw [← Work.Descent.galAct_mul, mul_inv_cancel, Work.Descent.galAct_one]

/-- `galAct_mul_inv` with the factors interchanged. -/
theorem galAct_inv_mul (X : Sch k) (σ : Work.Descent.Gal k k') :
    Work.Descent.galAct X σ⁻¹ ≫ Work.Descent.galAct X σ = 𝟙 _ := by
  rw [← Work.Descent.galAct_mul, inv_mul_cancel, Work.Descent.galAct_one]

end

end UnivEpi

noncomputable section

variable {k : Type u} [Field k] {C : Sch k} {P0 : 𝟙_ (Sch k) ⟶ C}

open UnivEpi

/-- **Equivariance of the universal lift over `k'`.**  Let `f : C ⟶ A` be a morphism to a smooth,
proper, geometrically irreducible group scheme over `k` and let `g' : G' ⟶ A_{k'}` be the unique
morphism over `k'` with `f_{k'} = AJ' ≫ g'` (which exists by the universal property over `k'`).
Then `g'` commutes with the Galois actions: it is a morphism of descent data.

The point is that the conjugate `a ≫ g' ≫ c⁻¹` of `g'` by `σ` is again a morphism over `Spec k'`
(with `a` and `c` the Galois actions on `G'` and on `A_{k'}`), and that naturality of the Galois
action applied to `f` shows that it also satisfies `AJ' ≫ (a ≫ g' ≫ c⁻¹) = f_{k'} = AJ' ≫ g'`.
By the generation property over `k'` the two morphisms are equal. -/
theorem UnivEpi.eqv_lift (D : Input C P0) {A : Sch k} [Smooth A.hom] [IsProper A.hom]
    [GeometricallyIrreducible A.hom] [GrpObj A] (f : C ⟶ A) (g' : D.G' ⟶ bc D.k' A)
    (hg' : (bcFun k D.k').map f = D.AJ' ≫ g') (σ : Work.Descent.Gal k D.k') :
    (D.galAct σ).hom ≫ g'.left = g'.left ≫ Work.Descent.galAct A σ := by
  -- `AJ' ≫ g'` is the base change of `f`, both for the action of `σ` and for its inverse.
  have hfl : D.AJ'.left ≫ g'.left = ((bcFun k D.k').map f).left := by
    rw [hg', Over.comp_left]
  have hmain : D.AJ'.left ≫ (D.galAct σ).hom ≫ g'.left =
      D.AJ'.left ≫ g'.left ≫ Work.Descent.galAct A σ := by
    calc D.AJ'.left ≫ (D.galAct σ).hom ≫ g'.left
        = (Work.Descent.galAct C σ ≫ D.AJ'.left) ≫ g'.left := by
          rw [← Category.assoc, ← D.AJ'_compat σ]
      _ = Work.Descent.galAct C σ ≫ D.AJ'.left ≫ g'.left := by simp only [Category.assoc]
      _ = Work.Descent.galAct C σ ≫ ((bcFun k D.k').map f).left := by rw [hfl]
      _ = ((bcFun k D.k').map f).left ≫ Work.Descent.galAct A σ := galAct_naturality C A f σ
      _ = D.AJ'.left ≫ g'.left ≫ Work.Descent.galAct A σ := by
          rw [← hfl]; simp only [Category.assoc]
  -- the conjugate of `g'` by `σ` is a morphism of `k'`-schemes
  have hw : (D.galAct σ).hom ≫ g'.left ≫ Work.Descent.galAct A σ⁻¹ ≫ (bc D.k' A).hom =
      D.G'.hom := by
    rw [Work.Descent.galAct_hom A σ⁻¹, Over.w_assoc g', ← Category.assoc, D.galAct_hom σ,
      Category.assoc, ← specGal_mul, mul_inv_cancel, specGal_one, Category.comp_id]
  let h' : D.G' ⟶ bc D.k' A :=
    Over.homMk ((D.galAct σ).hom ≫ g'.left ≫ Work.Descent.galAct A σ⁻¹) hw
  have hleft : h'.left = (D.galAct σ).hom ≫ g'.left ≫ Work.Descent.galAct A σ⁻¹ := rfl
  have hbridge : D.AJ'.left ≫ (D.galAct σ).hom ≫ g'.left ≫ Work.Descent.galAct A σ⁻¹ =
      (D.AJ'.left ≫ (D.galAct σ).hom ≫ g'.left) ≫ Work.Descent.galAct A σ⁻¹ := by
    simp only [Category.assoc]
  have hAJ' : (D.AJ'.left ≫ (D.galAct σ).hom ≫ g'.left) ≫ Work.Descent.galAct A σ⁻¹ =
      D.AJ'.left ≫ g'.left := by
    rw [hmain]
    simp only [Category.assoc, galAct_mul_inv A σ, Category.comp_id]
  -- it has the same composite with `AJ'` as `g'`, hence is equal to `g'` by `epi'`
  have hAJ : D.AJ' ≫ h' = D.AJ' ≫ g' := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left]
    rw [hleft, hbridge, hAJ']
  have hEq : h' = g' := D.epi' (bc D.k' A) h' g' hAJ
  have hcoe : (D.galAct σ).hom ≫ g'.left ≫ Work.Descent.galAct A σ⁻¹ = g'.left := by
    rw [← hleft, hEq]
  calc (D.galAct σ).hom ≫ g'.left
      = ((D.galAct σ).hom ≫ g'.left ≫ Work.Descent.galAct A σ⁻¹) ≫
          Work.Descent.galAct A σ := by
        simp only [Category.assoc, galAct_inv_mul A σ, Category.comp_id]
    _ = g'.left ≫ Work.Descent.galAct A σ := by rw [hcoe]

/-- The statement of the universal property over `k` and of the epimorphism property of `AJ`,
proved by base change to `k'` and Galois descent. -/
theorem univ_and_epi {k : Type u} [Field k] {C : Work.DescentGeom.Sch k}
    {P0 : 𝟙_ (Work.DescentGeom.Sch k) ⟶ C} (D : Work.DescentGeom.Input C P0)
    (A : Work.DescentGeom.Sch k) [AlgebraicGeometry.Smooth A.hom]
    [AlgebraicGeometry.IsProper A.hom] [AlgebraicGeometry.GeometricallyIrreducible A.hom]
    [GrpObj A] :
    (∀ f : C ⟶ A, P0 ≫ f = η[A] →
        ∃! g : D.J ⟶ A, f = Work.DescentGeom.AJ D ≫ g) ∧
      (∀ u v : D.J ⟶ A, Work.DescentGeom.AJ D ≫ u = Work.DescentGeom.AJ D ≫ v → u = v) := by
  constructor
  · -- existence and uniqueness of the factorisation of `f` through `AJ`
    intro f hf
    -- the base point condition after base change to `k'`
    have hf' : (bcFun k D.k').map P0 ≫ (bcFun k D.k').map f =
        (CartesianMonoidalCategory.preservesTerminalIso (bcFun k D.k')).hom ≫ η[bc D.k' A] := by
      rw [← Functor.map_comp, hf, map_eta_bc]
    -- the universal property over `k'`
    obtain ⟨g', hg', _⟩ := D.univ' (bc D.k' A) ((bcFun k D.k').map f) hf'
    have heqv := UnivEpi.eqv_lift D f g' hg'
    -- the transport of `g'` to `J_{k'}`: the morphism of descent data whose descent is `g`
    let Ψ : bc D.k' D.J ⟶ bc D.k' A := D.bcIso.hom ≫ g'
    let Φ : (bc D.k' D.J).left ⟶ A.left := Ψ.left ≫ bcπ D.k' A
    have hΦ : Φ ≫ A.hom = (bc D.k' D.J).hom ≫ Work.Descent.specMap k D.k' := by
      dsimp only [Φ]
      rw [Category.assoc, Work.Descent.baseChangeπ_hom, ← Category.assoc, Over.w Ψ]
    -- `Φ` is `Γ`-invariant, using the equivariance of `g'` and `galAct_π`
    have hInv : ∀ σ : Work.Descent.Gal k D.k', Work.Descent.galAct D.J σ ≫ Φ = Φ := by
      intro σ
      have h1 : ∀ {T : Scheme.{u}} (X : D.G'.left ⟶ T),
          Work.Descent.galAct D.J σ ≫ D.bcIso.hom.left ≫ X =
            D.bcIso.hom.left ≫ (D.galAct σ).hom ≫ X := by
        intro T X
        rw [← Category.assoc, D.bcIso_compat σ, Category.assoc]
      have h2 : ∀ {T : Scheme.{u}} (X : (bc D.k' A).left ⟶ T),
          (D.galAct σ).hom ≫ g'.left ≫ X =
            g'.left ≫ Work.Descent.galAct A σ ≫ X := by
        intro T X
        rw [← Category.assoc, heqv σ, Category.assoc]
      dsimp only [Φ, Ψ]
      simp only [Over.comp_left, Category.assoc]
      rw [h1, h2, Work.Descent.galAct_π A σ]
    -- descent of `Γ`-invariant morphisms
    obtain ⟨g, hg, _⟩ := desc_of_invariant D.J A Φ hΦ hInv
    have hmap : (bcFun k D.k').map g = Ψ := DescMul.map_eq_of_baseChange g Ψ hg
    refine ⟨g, ?_, ?_⟩
    · -- `g` factors `f`
      apply map_injective (k := k) (k' := D.k') C A
      show (bcFun k D.k').map f = (bcFun k D.k').map (AJ D ≫ g)
      rw [Functor.map_comp, map_AJ D, hmap, hg']
      dsimp only [Ψ]
      rw [Category.assoc, Iso.inv_hom_id_assoc D.bcIso]
    · -- uniqueness, from the generation property over `k'`
      intro g₁ h₁
      apply map_injective (k := k) (k' := D.k') D.J A
      show (bcFun k D.k').map g₁ = (bcFun k D.k').map g
      rw [hmap]
      dsimp only [Ψ]
      have h1a : (D.AJ' ≫ D.bcIso.inv) ≫ (bcFun k D.k').map g₁ = D.AJ' ≫ g' := by
        rw [← map_AJ D, ← Functor.map_comp, ← h₁, hg']
      have h1 : D.AJ' ≫ (D.bcIso.inv ≫ (bcFun k D.k').map g₁) = D.AJ' ≫ g' := by
        simpa only [Category.assoc] using h1a
      have h2 : D.bcIso.inv ≫ (bcFun k D.k').map g₁ = g' :=
        D.epi' (bc D.k' A) _ g' h1
      rw [← h2, Iso.hom_inv_id_assoc D.bcIso]
  · -- the generation property of `AJ`, from the generation property over `k'`
    intro u v huv
    apply map_injective (k := k) (k' := D.k') D.J A
    show (bcFun k D.k').map u = (bcFun k D.k').map v
    have h1 : (bcFun k D.k').map (AJ D ≫ u) = (bcFun k D.k').map (AJ D ≫ v) := by rw [huv]
    have hflat : (D.AJ' ≫ D.bcIso.inv) ≫ (bcFun k D.k').map u =
        (D.AJ' ≫ D.bcIso.inv) ≫ (bcFun k D.k').map v := by
      simpa only [Functor.map_comp, ← map_AJ D] using h1
    have h2 : D.AJ' ≫ (D.bcIso.inv ≫ (bcFun k D.k').map u) =
        D.AJ' ≫ (D.bcIso.inv ≫ (bcFun k D.k').map v) := by
      simpa only [Category.assoc] using hflat
    have h3 : D.bcIso.inv ≫ (bcFun k D.k').map u = D.bcIso.inv ≫ (bcFun k D.k').map v :=
      D.epi' (bc D.k' A) _ _ h2
    rw [← Category.id_comp ((bcFun k D.k').map u), ← Iso.hom_inv_id D.bcIso, Category.assoc, h3,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end

end Work.DescentGeom
