import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The normal closure from conjugates

A small group-theoretic helper: if *every* conjugate `g * i * g⁻¹` of every element `i` of a set
`s` lies in a subgroup `S`, then the whole normal closure of `s` lies in `S`.  No normality
assumption on `S` is needed, because `Subgroup.normalClosure s` is by definition the subgroup
*generated* by the conjugates of `s`.
-/

namespace Work.SSGate

/-- **The group-theoretic core of an inertia clause.**

If every conjugate `g * i * g⁻¹` of every element `i ∈ s` lies in a subgroup `S`, then the whole
normal closure of `s` lies in `S`. -/
theorem normalClosure_le_of_conj {G : Type} [Group G] (s : Set G) (S : Subgroup G)
    (h : ∀ (g : G) {i : G}, i ∈ s → g * i * g⁻¹ ∈ S) :
    Subgroup.normalClosure s ≤ S := by
  let T : Subgroup G :=
    { carrier := {x | ∀ g : G, g * x * g⁻¹ ∈ S}
      one_mem' := by intro g; simpa using S.one_mem
      mul_mem' := by
        intro x y hx hy g
        have h1 : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        rw [h1]; exact S.mul_mem (hx g) (hy g)
      inv_mem' := by
        intro x hx g
        have h1 : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
        rw [h1]; exact S.inv_mem (hx g) }
  have hTN : T.Normal := by
    refine ⟨fun x hx g => ?_⟩
    intro g'
    have h1 : g' * (g * x * g⁻¹) * g'⁻¹ = (g' * g) * x * (g' * g)⁻¹ := by group
    rw [h1]; exact hx (g' * g)
  have hsT : s ⊆ (T : Set G) := fun i hi g => h g hi
  have h1 : Subgroup.normalClosure s ≤ T := Subgroup.normalClosure_le_normal hsT
  intro x hx
  simpa using h1 hx 1

end Work.SSGate
