import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Submission.Work.CohomologicalShrinking.Shrinking
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v w

/-- The identity operator map `F(m) → F(m)`. -/
noncomputable def OperatorMap.id (G : Type*) [Group G] (m : ℕ) : OperatorMap G m m where
  toHom := MonoidHom.id (Work.Shrinking.freeOperatorGroup G m)
  surjective := Function.surjective_id
  equivariant := fun _ _ => rfl

@[simp]
theorem OperatorMap.id_toHom (G : Type*) [Group G] (m : ℕ) :
    (OperatorMap.id G m).toHom = MonoidHom.id (Work.Shrinking.freeOperatorGroup G m) := rfl

/-- The composite of `Φ : F(m) → F(n)` and `Ψ : F(n) → F(l)` (first `Φ`, then `Ψ`) — the
Mathlib convention `Ψ.toHom.comp Φ.toHom`. -/
noncomputable def OperatorMap.comp {G : Type*} [Group G] {m n l : ℕ}
    (Ψ : OperatorMap G n l) (Φ : OperatorMap G m n) : OperatorMap G m l where
  toHom := Ψ.toHom.comp Φ.toHom
  surjective := Ψ.surjective.comp Φ.surjective
  equivariant := fun g y => by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Φ.equivariant, Ψ.equivariant]

@[simp]
theorem OperatorMap.comp_toHom {G : Type*} [Group G] {m n l : ℕ}
    (Ψ : OperatorMap G n l) (Φ : OperatorMap G m n) :
    (Ψ.comp Φ).toHom = Ψ.toHom.comp Φ.toHom := rfl

@[simp]
theorem OperatorMap.id_comp {G : Type*} [Group G] {m n : ℕ} (Φ : OperatorMap G m n) :
    (OperatorMap.id G n).comp Φ = Φ := by
  cases Φ with
  | mk h hs he => rfl

@[simp]
theorem OperatorMap.comp_id {G : Type*} [Group G] {m n : ℕ} (Φ : OperatorMap G m n) :
    Φ.comp (OperatorMap.id G m) = Φ := by
  cases Φ with
  | mk h hs he => rfl

theorem OperatorMap.comp_assoc {G : Type*} [Group G] {m n l k : ℕ}
    (X : OperatorMap G l k) (Ψ : OperatorMap G n l) (Φ : OperatorMap G m n) :
    (X.comp Ψ).comp Φ = X.comp (Ψ.comp Φ) := by
  cases X with
  | mk xh xs xe => cases Ψ with | mk yh ys ye => cases Φ with | mk zh zs ze => rfl

/-- The retraction `F(m) ⇢ F(n)` (`n ≤ m`) as an operator map: it is the identity on the first
`n` generators and kills the rest. -/
noncomputable def OperatorMap.ofLe (G : Type*) [Group G] {m n : ℕ} (h : n ≤ m) :
    OperatorMap G m n where
  toHom := Work.Shrinking.freeOperatorRetract (G := G) h
  surjective := Work.Shrinking.freeOperatorRetract_surjective h
  equivariant := Work.Shrinking.freeOperatorRetract_smul (G := G) h

@[simp]
theorem OperatorMap.ofLe_toHom (G : Type*) [Group G] {m n : ℕ} (h : n ≤ m) :
    (OperatorMap.ofLe G h).toHom = Work.Shrinking.freeOperatorRetract (G := G) h := rfl

/-- A surjective `G`-operator homomorphism `F(m) ⇢ F(n)` exists whenever `n ≤ m`. -/
theorem exists_operatorMap_of_le (G : Type*) [Group G] {m n : ℕ} (h : n ≤ m) :
    Nonempty (OperatorMap G m n) :=
  ⟨OperatorMap.ofLe G h⟩

end Work.CohomologicalShrinking
