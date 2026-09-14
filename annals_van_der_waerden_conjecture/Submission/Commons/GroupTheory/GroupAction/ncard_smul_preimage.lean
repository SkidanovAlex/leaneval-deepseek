import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.GroupAction.Defs

namespace Commons.GroupTheory.GroupAction

/-- For `x` in the orbit of `a`, the fiber `{g : G // g • a = x}` of the action
map is in bijection with the stabilizer of `a`. -/
noncomputable def fiber_equiv_stabilizer (G : Type*) [Group G] {α : Type*} [MulAction G α]
    (a x : α) (hx : x ∈ MulAction.orbit G a) :
    {g : G // g • a = x} ≃ (MulAction.stabilizer G a : Type _) := by
  classical
  let g₀ : G := Classical.choose (MulAction.mem_orbit_iff.mp hx)
  have hg₀ : g₀ • a = x := Classical.choose_spec (MulAction.mem_orbit_iff.mp hx)
  refine
    { toFun := fun g => ⟨g₀⁻¹ * g.1, ?_⟩
      invFun := fun h => ⟨g₀ * h.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [MulAction.mem_stabilizer_iff]
    calc
      (g₀⁻¹ * g.1) • a = g₀⁻¹ • (g.1 • a) := by rw [mul_smul]
      _ = a := by rw [g.2, ← hg₀, inv_smul_smul]
  · calc
      (g₀ * h.1) • a = g₀ • (h.1 • a) := by rw [mul_smul]
      _ = x := by
        rw [MulAction.mem_stabilizer_iff.mp h.2, hg₀]
  · intro g
    apply Subtype.ext
    simp
  · intro h
    apply Subtype.ext
    simp

private lemma card_smul_preimage_subtype (G : Type*) [Group G] {α : Type*} [MulAction G α]
    [Finite G] [Finite α] (a : α) (P : Set α) :
    Nat.card {g : G // (g • a) ∈ P} =
      Nat.card (MulAction.stabilizer G a) *
        Nat.card {x : α // x ∈ P ∧ x ∈ MulAction.orbit G a} := by
  classical
  let T : Type _ := {x : α // x ∈ P ∧ x ∈ MulAction.orbit G a}
  let fiber : α → Type _ := fun x => {g : G // g • a = x}
  have h1 : {g : G // (g • a) ∈ P} ≃ (Σ x : T, fiber x.1) := by
    refine
      { toFun := fun g => ⟨⟨g.1 • a, ⟨g.2, MulAction.mem_orbit a g.1⟩⟩, ⟨g.1, rfl⟩⟩
        invFun := fun p => ⟨p.2.1, by
          rw [p.2.2]
          exact p.1.2.1⟩
        left_inv := by
          intro g
          apply Subtype.ext
          rfl
        right_inv := by
          intro p
          cases p with
          | mk x hg =>
            cases hg with
            | mk g hg_eq =>
              dsimp
              apply Sigma.ext
              · apply Subtype.ext
                exact hg_eq
              · apply (Subtype.heq_iff_coe_eq ?_).mpr
                · rfl
                · intro u
                  simp [hg_eq] }
  calc
    Nat.card {g : G // (g • a) ∈ P} = Nat.card (Σ x : T, fiber x.1) := Nat.card_congr h1
    _ = Nat.card T * Nat.card (MulAction.stabilizer G a) := by
      calc
        Nat.card (Σ x : T, fiber x.1)
            = Nat.card (Σ _x : T, (MulAction.stabilizer G a : Type _)) := by
          apply Nat.card_congr
          exact Equiv.sigmaCongrRight fun x => fiber_equiv_stabilizer G a x.1 x.2.2
        _ = Nat.card (T × (MulAction.stabilizer G a)) := by
          apply Nat.card_congr
          exact Equiv.sigmaEquivProd T (MulAction.stabilizer G a)
        _ = Nat.card T * Nat.card (MulAction.stabilizer G a) := by rw [Nat.card_prod]
    _ = Nat.card (MulAction.stabilizer G a) *
          Nat.card {x : α // x ∈ P ∧ x ∈ MulAction.orbit G a} := by
      rw [Nat.mul_comm]

theorem ncard_smul_preimage (G : Type*) [Group G] {α : Type*} [MulAction G α]
    [Finite G] [Finite α] (a : α) (P : Set α) :
    ({g : G | (g • a) ∈ P}).ncard =
      Nat.card (MulAction.stabilizer G a) *
        ({x : α | x ∈ P ∧ x ∈ MulAction.orbit G a}).ncard := by
  exact card_smul_preimage_subtype G a P

end Commons.GroupTheory.GroupAction