import Mathlib
import Submission.Work.RatHurewicz.ExcisionSetup

/-!
# The vocabulary of the pinch step of the compression property

Writing `I^{e+1} = I^e × I` with last coordinate `s`:

* `PinchSet e` is the "pinched" part `J = ∂I^{e+1} ∖ (open top face)` of the boundary: the union
  of the bottom face `{s = 0}` and the side faces;
* `IsPinchedAt e Φ a` says that `Φ` is constant `a` on `PinchSet e`; for a map of pairs
  `Φ : (I^{e+1}, ∂I^{e+1}) → (Y,A)` with `a ∈ A` this is exactly the condition under which `Φ`
  unwraps to a *based* `e`-cube in the homotopy fibre of `A ↪ Y` at `a`
  (`Work.RatHurewicz.pinchedMap_nullHomotopic`);
* `pinchBase e` is the centre of the bottom face, the base point used by
  `Work.RatHurewicz.exists_pinch`.
-/

set_option linter.unusedVariables false

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-- The midpoint of the unit interval. -/
def half : unitInterval := ⟨1 / 2, by norm_num⟩

/-- The **pinched part** `J` of the boundary of `I^{e+1}`: the bottom face `{x (Fin.last e) = 0}`
together with the side faces `{x i = 0 ∨ x i = 1}`, `i : Fin e`.  Equivalently, `∂I^{e+1}` with the
interior of the top face `{x (Fin.last e) = 1}` removed. -/
def PinchSet (e : ℕ) : Set (ICube (e + 1)) :=
  {x | x (Fin.last e) = 0 ∨ ∃ i : Fin e, x (Fin.castSucc i) = 0 ∨ x (Fin.castSucc i) = 1}

theorem pinchSet_subset_boundary (e : ℕ) : PinchSet e ⊆ Cube.boundary (Fin (e + 1)) := by
  intro x hx
  rcases hx with h | ⟨i, h | h⟩
  · exact ⟨Fin.last e, Or.inl h⟩
  · exact ⟨Fin.castSucc i, Or.inl h⟩
  · exact ⟨Fin.castSucc i, Or.inr h⟩

/-- A map `Φ : I^{e+1} → Y` is **pinched at `a`** if it is constant `a` on the bottom face and on
the side faces, i.e. on `PinchSet e`. -/
def IsPinchedAt (e : ℕ) (Φ : C(ICube (e + 1), Y)) (a : Y) : Prop :=
  (∀ u : ICube e, Φ (Fin.snoc u 0) = a) ∧
  (∀ (u : ICube e) (s : I), (∃ i : Fin e, u i = 0 ∨ u i = 1) → Φ (Fin.snoc u s) = a)

/-- The centre of the bottom face of `I^{e+1}`, the base point used by `exists_pinch`. -/
def pinchBase (e : ℕ) : ICube (e + 1) := Fin.snoc (fun _ : Fin e => half) 0

theorem pinchBase_mem_pinchSet (e : ℕ) : pinchBase e ∈ PinchSet e := by
  refine Or.inl ?_
  show pinchBase e (Fin.last e) = 0
  rw [pinchBase, Fin.snoc_last]

theorem pinchBase_mem_boundary (e : ℕ) : pinchBase e ∈ Cube.boundary (Fin (e + 1)) :=
  pinchSet_subset_boundary e (pinchBase_mem_pinchSet e)

end

end Work.RatHurewicz
