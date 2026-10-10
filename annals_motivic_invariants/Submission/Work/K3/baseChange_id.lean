import Mathlib
import Submission.Work.K3.BaseChange

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3.baseChange_id` — base change along the identity field extension

`Work.K3.baseChange K K X` is the fibred product `X ×_{Spec K} Spec K`, i.e. the base change of a
`K`-scheme along the identity field extension `K = K`.  The structure morphism

`Work.K3.specMap K K = Spec.map (algebraMap K K)`

of the identity extension is the identity of `Spec K`, so the projection of the base change

`Work.K3.baseChangeProj K K X : X ×_{Spec K} Spec K ⟶ X`

is an isomorphism: its inverse is the comparison map `X ⟶ X ×_{Spec K} Spec K` supplied by the
universal property of the pullback (with components `X ↘ Spec K` and `𝟙 X`).  This is the identity
case of the functoriality of base change used in the descent step of Lin–Shinder's Theorem
`thm:K3` (see the module docstring of `Work.K3.BaseChange`).
-/

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

/-- Base change along the identity field extension is the identity, up to isomorphism over the
base. -/
theorem baseChange_id (K : Type) [Field K] (X : Scheme.{0}) [X.Over (Spec (.of K))] :
    ∃ e : Work.K3.baseChange K K X ≅ X, e.hom.IsOver (Spec (.of K)) := by
  -- The structure morphism `Spec K ⟶ Spec K` of the identity field extension is the identity.
  have hspec : Work.K3.specMap K K = 𝟙 (Spec (.of K)) := by
    simp [Work.K3.specMap]
  -- The defining square of the base change, with `specMap K K` rewritten to the identity: the
  -- projection to `Spec K` of the base change is `baseChangeProj K K X ≫ (X ↘ Spec K)`.
  have hsq : pullback.snd (Work.K3.specMap K K) (X ↘ Spec (.of K)) ≫ (X ↘ Spec (.of K))
      = pullback.fst (Work.K3.specMap K K) (X ↘ Spec (.of K)) := by
    rw [← pullback.condition, hspec, Category.comp_id]
  -- The comparison map `X ⟶ X ×_{Spec K} Spec K` produced by the universal property.
  let ψ : X ⟶ pullback (Work.K3.specMap K K) (X ↘ Spec (.of K)) :=
    pullback.lift (X ↘ Spec (.of K)) (𝟙 X)
      (by rw [hspec, Category.comp_id, Category.id_comp])
  -- The two inverse identities.  (`baseChangeProj K K X` is `pullback.snd` of this cospan by
  -- definition, so the second one is `hom_inv_id` for the isomorphism `baseChange K K X ≅ X`.)
  have hψφ : ψ ≫ pullback.snd (Work.K3.specMap K K) (X ↘ Spec (.of K)) = 𝟙 X :=
    pullback.lift_snd _ _ _
  have hφψ : pullback.snd (Work.K3.specMap K K) (X ↘ Spec (.of K)) ≫ ψ
      = 𝟙 (pullback (Work.K3.specMap K K) (X ↘ Spec (.of K))) := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hsq, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  refine ⟨⟨Work.K3.baseChangeProj K K X, ψ, ?_, hψφ⟩, ?_⟩
  · show pullback.snd (Work.K3.specMap K K) (X ↘ Spec (.of K)) ≫ ψ = 𝟙 _
    exact hφψ
  · -- `baseChangeProj K K X` *is* the `Spec K`-structure of `baseChange K K X` (the instance
    -- `baseChangeOverK`), so being over `Spec K` is definitional.
    rw [Hom.isOver_iff]
    show Work.K3.baseChangeProj K K X ≫ (X ↘ Spec (.of K))
      = Work.K3.baseChangeProj K K X ≫ (X ↘ Spec (.of K))
    rfl

end Work.K3
