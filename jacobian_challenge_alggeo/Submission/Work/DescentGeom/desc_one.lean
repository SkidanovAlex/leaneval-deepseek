import Mathlib
import Submission.Work.DescentGeom.Basic
import Submission.Work.DescentGeom.Kit
import Submission.Work.DescentGeom.Transfer
import Submission.Work.DescentGeom.JExists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `DescentGeom` — descent of the unit of the group chunk

For a chart datum `D : Input C P0` the unit of the descended Jacobian `D.J` over `k` is obtained by
descending the `Γ`-invariant morphism

`oneΦ : (D.J)_{k'} ⟶ D.J`,   `oneΦ = tc ≫ η[G'] ≫ bcIso.inv ≫ bcπ`,

where `tc` is the terminal comparison of the base change functor `bcFun k k'` and `η[G']` is the
unit of the group chunk `G'`.

This file produces, for the requested statement `desc_one`, the witness `oneJ1` together with the
identity `bcFun.map oneJ1 = tc ≫ η[G'] ≫ bcIso.inv` — *as a morphism of `k'`-schemes*, not merely
on underlying schemes.  The latter is the content of `oneJ1_spec` (the descent identity through the
projection `bcπ`); the passage from it to the functor's `map` is the observation that the two sides
are both morphisms `(𝟙_{k'}) ⟶ (D.J)_{k'}` of `k'`-schemes, so it suffices to compare their
composites with the two projections of the defining pullback `(D.J)_{k'} = D.J ×_k Spec k'`.

The `_c` lemmas below restate the `Over.w`-identities of the structure morphisms in the form
`a ≫ b ≫ X = c ≫ X` (`X` an arbitrary tail), which is exactly the shape in which the simplifier
(right-associated normal form for `≫`) can use them.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.DescentGeom

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CategoryTheory
open CartesianMonoidalCategory

universe u

noncomputable section

variable {k : Type u} [Field k]

namespace Input

variable {C : Sch k} {P0 : 𝟙_ (Sch k) ⟶ C} (D : Input C P0)

/-- The terminal comparison of the base change functor, as a morphism of schemes. -/
abbrev tc1 : (bc D.k' (𝟙_ (Sch k))).left ⟶ (𝟙_ (Sch D.k')).left :=
  (CartesianMonoidalCategory.preservesTerminalIso (bcFun k D.k')).hom.left

/-- The `Γ`-invariant morphism whose descent is the unit of `D.J`. -/
def oneΦ1 : (bc D.k' (𝟙_ (Sch k))).left ⟶ D.J.left :=
  tc1 (D := D) ≫ (η[D.G']).left ≫ D.bcIso.inv.left ≫ bcπ D.k' D.J

/-- `tc` followed by the structure morphism of the unit. -/
lemma tc1_hom_c {T : Scheme.{u}} (X : Spec (CommRingCat.of D.k') ⟶ T) :
    tc1 (D := D) ≫ (𝟙_ (Sch D.k')).hom ≫ X = (bc D.k' (𝟙_ (Sch k))).hom ≫ X := by
  rw [← Category.assoc,
    Over.w (CartesianMonoidalCategory.preservesTerminalIso (bcFun k D.k')).hom]

/-- The unit of `G'` followed by the structure morphism of `G'`. -/
lemma eta_c {T : Scheme.{u}} (X : Spec (CommRingCat.of D.k') ⟶ T) :
    (η[D.G']).left ≫ D.G'.hom ≫ X = (𝟙_ (Sch D.k')).hom ≫ X := by
  rw [← Category.assoc, Over.w (η[D.G'])]

/-- `bcIso.inv` followed by the structure morphism of `D.J`. -/
lemma bcIso_inv_c {T : Scheme.{u}} (X : Spec (CommRingCat.of D.k') ⟶ T) :
    D.bcIso.inv.left ≫ (bc D.k' D.J).hom ≫ X = D.G'.hom ≫ X := by
  rw [← Category.assoc, Over.w D.bcIso.inv]

/-- `oneΦ1` is a morphism of `k`-schemes, i.e. satisfies the hypothesis of `desc_of_invariant`. -/
theorem oneΦ1_hom : oneΦ1 D ≫ D.J.hom =
    (bc D.k' (𝟙_ (Sch k))).hom ≫ Work.Descent.specMap k D.k' := by
  simp only [oneΦ1, tc1, Category.assoc, bcIso_inv_c D, eta_c D, tc1_hom_c D,
    Work.Descent.baseChangeπ_hom D.J]

/-- **`bcIso.inv` intertwines the Galois action on `G'` and on `D.J`.** -/
theorem galAct_bcIso_inv1 (σ : Work.Descent.Gal k D.k') :
    (D.galAct σ).hom ≫ D.bcIso.inv.left =
      D.bcIso.inv.left ≫ Work.Descent.galAct D.J σ := by
  have h := D.bcIso_compat σ
  have h1 : D.bcIso.hom.left ≫ D.bcIso.inv.left = 𝟙 (bc D.k' D.J).left := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  have h2 : D.bcIso.inv.left ≫ D.bcIso.hom.left = 𝟙 D.G'.left := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  calc (D.galAct σ).hom ≫ D.bcIso.inv.left
      = (D.bcIso.inv.left ≫ D.bcIso.hom.left) ≫
          ((D.galAct σ).hom ≫ D.bcIso.inv.left) := by
        rw [h2, Category.id_comp]
    _ = D.bcIso.inv.left ≫ ((D.bcIso.hom.left ≫ (D.galAct σ).hom) ≫ D.bcIso.inv.left) := by
        simp only [Category.assoc]
    _ = D.bcIso.inv.left ≫
          ((Work.Descent.galAct D.J σ ≫ D.bcIso.hom.left) ≫ D.bcIso.inv.left) := by
        rw [← h]
    _ = D.bcIso.inv.left ≫ Work.Descent.galAct D.J σ := by
        rw [Category.assoc, h1, Category.comp_id]

/-- **`oneΦ1` is `Γ`-invariant**, i.e. satisfies the hypothesis of `desc_of_invariant`. -/
theorem oneΦ1_galAct (σ : Work.Descent.Gal k D.k') :
    Work.Descent.galAct (𝟙_ (Sch k)) σ ≫ oneΦ1 D = oneΦ1 D := by
  have h_bcIso_inv : ∀ {T : Scheme.{u}} (X : (bc D.k' D.J).left ⟶ T),
      (D.galAct σ).hom ≫ D.bcIso.inv.left ≫ X =
        D.bcIso.inv.left ≫ Work.Descent.galAct D.J σ ≫ X := by
    intro T X
    rw [← Category.assoc, galAct_bcIso_inv1 D σ, Category.assoc]
  have h_eta : ∀ {T : Scheme.{u}} (X : D.G'.left ⟶ T),
      specGal σ ≫ (η[D.G']).left ≫ X = (η[D.G']).left ≫ (D.galAct σ).hom ≫ X := by
    intro T X
    rw [← Category.assoc, D.galAct_one_compat σ, Category.assoc]
  have h_tc : ∀ {T : Scheme.{u}} (X : (𝟙_ (Sch D.k')).left ⟶ T),
      Work.Descent.galAct (𝟙_ (Sch k)) σ ≫ tc1 (D := D) ≫ X =
        tc1 (D := D) ≫ specGal σ ≫ X := by
    intro T X
    rw [← Category.assoc, galAct_terminal, Category.assoc]
  simp only [oneΦ1, tc1, h_tc, h_eta, h_bcIso_inv, Work.Descent.galAct_π]

/-- The unit of `D.J`: the descent of `oneΦ1`. -/
def oneJ1 : 𝟙_ (Sch k) ⟶ D.J :=
  (desc_of_invariant (𝟙_ (Sch k)) D.J (oneΦ1 D) (oneΦ1_hom D) (oneΦ1_galAct D)).choose

/-- The defining property of `oneJ1`: its image under the projection is `oneΦ1`. -/
lemma oneJ1_spec : bcπ D.k' (𝟙_ (Sch k)) ≫ (oneJ1 D).left = oneΦ1 D :=
  (desc_of_invariant (𝟙_ (Sch k)) D.J (oneΦ1 D) (oneΦ1_hom D) (oneΦ1_galAct D)).choose_spec.1

/-- `oneJ1_spec` in the unfolded (`pullback`) form used by `pullback.hom_ext`. -/
lemma oneJ1_spec_pb : pullback.fst (Over.hom (𝟙_ (Sch k))) (Work.Descent.specMap k D.k') ≫
    (oneJ1 D).left = oneΦ1 D :=
  oneJ1_spec D

end Input

/-- **The unit of the descended Jacobian is the descent of the unit of the group chunk.** -/
theorem desc_one {k : Type u} [Field k] {C : Work.DescentGeom.Sch k}
    {P0 : 𝟙_ (Work.DescentGeom.Sch k) ⟶ C} (D : Work.DescentGeom.Input C P0) :
    ∃ one : 𝟙_ (Work.DescentGeom.Sch k) ⟶ D.J,
      (Work.DescentGeom.bcFun k D.k').map one =
        (CartesianMonoidalCategory.preservesTerminalIso (Work.DescentGeom.bcFun k D.k')).hom ≫
          η[D.G'] ≫ D.bcIso.inv := by
  refine ⟨Input.oneJ1 D, ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext (f := D.J.hom) (g := Work.Descent.specMap k D.k')
  · rw [Work.Descent.baseChange_map_fst', Input.oneJ1_spec_pb D]
    simp only [Input.oneΦ1, Input.tc1, bcπ, Work.Descent.baseChangeπ, Over.comp_left,
      Category.assoc]
  · rw [← Work.Descent.baseChange_hom (k := k) (k' := D.k') D.J,
      Over.w ((bcFun k D.k').map (Input.oneJ1 D)),
      Over.w ((CartesianMonoidalCategory.preservesTerminalIso (bcFun k D.k')).hom ≫
        η[D.G'] ≫ D.bcIso.inv)]

end

end Work.DescentGeom
