import Mathlib
import Submission.Work.K3.BaseChange

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3.baseChange_isoOver` — base change preserves isomorphisms over the base field

Base change along a field extension `K → L` (i.e. the fibred product `− ×_{Spec K} Spec L`) is a
functor on `K`-schemes, so it sends an isomorphism over `Spec K` to an isomorphism over `Spec L`.
This is the "transport of structure" half of the descent step of Lin–Shinder's Theorem `thm:K3`
(see the module docstring of `Work.K3.BaseChange`).

The two ingredients are proved below in the fully unfolded shape in which base change is defined
by `Work.K3.BaseChange`:

* `baseChangeMap_isIso` — the induced morphism of base changes of an isomorphism is an
  isomorphism (`pullback.map_isIso` with identities on the base `Spec K` and on `Spec L`);
* `baseChangeMap_isOver` — the induced morphism is a morphism of `L`-schemes, since its first
  projection to `Spec L` is the first projection of the source pullback (`pullback.lift_fst`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- Base change of an isomorphism over the base field is an isomorphism. -/
lemma baseChangeMap_isIso {X Y : Scheme.{0}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    (e : X ≅ Y) [e.hom.IsOver (Spec (.of K))] : IsIso (baseChangeMap K L e.hom) := by
  unfold baseChangeMap
  exact pullback.map_isIso (specMap K L) (X ↘ Spec (.of K)) (specMap K L) (Y ↘ Spec (.of K))
    (𝟙 _) e.hom (𝟙 _) _ _

/-- Base change of a morphism over the base field is a morphism over the bigger base field. -/
lemma baseChangeMap_isOver {X Y : Scheme.{0}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K))] :
    (baseChangeMap K L f).IsOver (Spec (.of L)) := by
  rw [Hom.isOver_iff]
  show (pullback.map (specMap K L) (X ↘ Spec (.of K)) (specMap K L) (Y ↘ Spec (.of K))
      (𝟙 (Spec (.of L))) f (𝟙 (Spec (.of K)))
      (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id]; exact (CategoryTheory.comp_over (S := Spec (.of K)) f).symm))
    ≫ pullback.fst (specMap K L) (Y ↘ Spec (.of K))
      = pullback.fst (specMap K L) (X ↘ Spec (.of K))
  rw [pullback.lift_fst]
  simp

/-- Base change along a field extension preserves isomorphisms over the base field. -/
theorem baseChange_isoOver (K L : Type) [Field K] [Field L] [Algebra K L]
    {X Y : Scheme.{0}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    (h : Work.K3.IsoOver K X Y) :
    Work.K3.IsoOver L (Work.K3.baseChange K L X) (Work.K3.baseChange K L Y) := by
  obtain ⟨e, he⟩ := h
  haveI : e.hom.IsOver (Spec (.of K)) := he
  haveI : IsIso (baseChangeMap K L e.hom) := baseChangeMap_isIso K L e
  exact ⟨asIso (baseChangeMap K L e.hom), baseChangeMap_isOver K L e.hom⟩

end Work.K3
