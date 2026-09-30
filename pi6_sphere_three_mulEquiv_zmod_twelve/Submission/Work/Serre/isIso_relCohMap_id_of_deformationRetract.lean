import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.StemsB.bijective_relCohMap_of_homotopyEquivR

namespace Work.Serre

/-- **Enlarging the relative set along a deformation retraction.**  Let `A ⊆ B ⊆ X`, and let
`H : B × I → B` be a homotopy from the identity of `B` to a map `φ : B → B` which fixes `A`
pointwise (`hfix`) and takes `B` into `A` (`hφ`).  Then the pullback of relative cohomology along
the identity of pairs `(X,B) → (X,A)`, i.e. `H^n(X,B;ℚ) → H^n(X,A;ℚ)`, is an isomorphism in every
degree.

Equivalently: the inclusion `A ↪ B` is a homotopy equivalence (its homotopy inverse is `φ` read in
`A`), so the pairs `(X,B)` and `(X,A)` are homotopy equivalent as pairs via the identity of `X`.
The proof is `Work.StemsB.bijective_relCohMap_of_homotopyEquivR` applied with `f = id_X`,
`e1` the identity homotopy equivalence of `X` and `e2 : ↥A ≃ₕ ↥B` the homotopy equivalence whose
`toFun` is the inclusion and whose `invFun` is `φ` corestricted, using `H` for the homotopy
`incl ∘ φ ≃ id`. -/
theorem isIso_relCohMap_id_of_deformationRetract {X : Type} [TopologicalSpace X]
    (A B : Set X) (hAB : A ⊆ B) (φ : C(↥B, ↥B))
    (H : ContinuousMap.Homotopy (ContinuousMap.id ↥B) φ)
    (hfix : ∀ (t : unitInterval) (y : ↥B), (y : X) ∈ A → H (t, y) = y)
    (hφ : ∀ y : ↥B, ((φ y : ↥B) : X) ∈ A) (n : ℕ) :
    CategoryTheory.IsIso (Work.Thom.relCohMap (ContinuousMap.id X) A B
      (fun x hx => hAB hx) ℚ n) := by
  -- `φ` fixes the points of `A` pointwise
  have hφfix : ∀ a : ↥A, φ ⟨(a : X), hAB a.2⟩ = ⟨(a : X), hAB a.2⟩ := by
    intro a
    rw [← H.apply_one]
    exact hfix 1 ⟨(a : X), hAB a.2⟩ a.2
  -- the inclusion `A ↪ B` and the corestriction `B → A` of `φ`, which will be the homotopy
  -- inverse of the inclusion
  let incl : C(↥A, ↥B) := ⟨Set.inclusion hAB, continuous_subtype_val.subtype_mk _⟩
  let ψ : C(↥B, ↥A) := ⟨fun y => ⟨(φ y : X), hφ y⟩,
    continuous_subtype_val.comp φ.continuous |>.subtype_mk _⟩
  have hψincl : ψ.comp incl = ContinuousMap.id ↥A := by
    ext a
    show (φ (incl a) : X) = (a : X)
    rw [show incl a = (⟨(a : X), hAB a.2⟩ : ↥B) from rfl, hφfix a]
  have hinclψ : incl.comp ψ = φ := by
    ext y
    show (incl (ψ y) : X) = (φ y : X)
    rfl
  -- so `↥A` and `↥B` are homotopy equivalent
  let e2 : ContinuousMap.HomotopyEquiv ↥A ↥B :=
    { toFun := incl
      invFun := ψ
      left_inv := by rw [hψincl]
      right_inv := by rw [hinclψ]; exact ⟨H.symm⟩ }
  -- and `X` is homotopy equivalent to itself via the identity
  let e1 : ContinuousMap.HomotopyEquiv X X := ContinuousMap.HomotopyEquiv.refl X
  have he1 : ⇑e1.toFun = ⇑(ContinuousMap.id X) := by
    funext x
    exact ContinuousMap.HomotopyEquiv.refl_apply X x
  have he2 : ∀ q : ↥A, ((e2.toFun q : ↥B) : X) = (ContinuousMap.id X) (q : X) := by
    intro q
    rfl
  have hb := Work.StemsB.bijective_relCohMap_of_homotopyEquivR ℚ A B (ContinuousMap.id X)
    (fun x hx => hAB hx) e1 he1 e2 he2 n
  exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective
    (Work.Thom.relCohMap (ContinuousMap.id X) A B (fun x hx => hAB hx) ℚ n)).mpr hb

end Work.Serre
