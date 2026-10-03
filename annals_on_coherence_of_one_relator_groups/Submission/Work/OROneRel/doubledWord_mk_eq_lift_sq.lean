import Mathlib

universe u

namespace Work.OROneRel

/-- A single letter `p = (a, b)` of a word corresponds under `mk` to `of a` when `b = true` and to
`(of a)⁻¹` when `b = false`. -/
private lemma mk_singleton {α : Type u} (p : α × Bool) :
    FreeGroup.mk [p] = bif p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹ := by
  rw [← FreeGroup.lift_of_apply (FreeGroup.mk [p]), FreeGroup.lift_mk]
  simp

/-- The two-letter word `[p, p]` represents the square of the group element represented by `[p]`. -/
private lemma mk_double_singleton {α : Type u} (p : α × Bool) :
    FreeGroup.mk [p, p] = (bif p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹) ^ 2 := by
  rw [show ([p, p] : List (α × Bool)) = [p] ++ [p] from rfl, ← FreeGroup.mul_mk, mk_singleton,
    ← pow_two]

/-- Squaring `of a` or its inverse matches the `bif`-conditional version of the square used by
`FreeGroup.lift_mk`. -/
private lemma cond_sq {α : Type u} (p : α × Bool) :
    (bif p.2 then FreeGroup.of p.1 else (FreeGroup.of p.1)⁻¹) ^ 2
      = bif p.2 then FreeGroup.of p.1 ^ (2:ℕ) else (FreeGroup.of p.1 ^ (2:ℕ))⁻¹ := by
  rcases p with ⟨a, b⟩
  cases b <;> simp [pow_two]

/-- Doubling each letter of a word `L` (each syllable repeated twice) computes, under `mk`, the
product over `L` of the squares of the individual letters. -/
private lemma mk_double_flatten {α : Type u} (L : List (α × Bool)) :
    FreeGroup.mk (L.map (fun p => [p, p])).flatten
      = (L.map (fun p => bif p.2 then FreeGroup.of p.1 ^ (2:ℕ)
          else (FreeGroup.of p.1 ^ (2:ℕ))⁻¹)).prod := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rw [List.map_cons]
    rw [List.map_cons]
    rw [List.flatten_cons, ← FreeGroup.mul_mk, ih, List.prod_cons,
      mk_double_singleton, cond_sq]

/-- The word-level "double every letter" operation agrees with the group homomorphism
`FreeGroup.lift (fun a => of a ^ 2)`. -/
private lemma mk_double_eq_lift {α : Type u} (L : List (α × Bool)) :
    FreeGroup.mk (L.map (fun p => [p, p])).flatten
      = FreeGroup.lift (fun a : α => FreeGroup.of a ^ (2 : ℕ)) (FreeGroup.mk L) := by
  rw [FreeGroup.lift_mk]
  exact mk_double_flatten L

theorem doubledWord_mk_eq_lift_sq {α : Type u} [DecidableEq α] (u : FreeGroup α) :
    FreeGroup.mk ((FreeGroup.toWord u).map (fun p : α × Bool => [p, p])).flatten
      = FreeGroup.lift (fun a : α => FreeGroup.of a ^ (2 : ℕ)) u := by
  calc FreeGroup.mk ((FreeGroup.toWord u).map (fun p : α × Bool => [p, p])).flatten
      = FreeGroup.lift (fun a : α => FreeGroup.of a ^ (2 : ℕ))
          (FreeGroup.mk (FreeGroup.toWord u)) := mk_double_eq_lift (FreeGroup.toWord u)
    _ = FreeGroup.lift (fun a : α => FreeGroup.of a ^ (2 : ℕ)) u := by
        rw [FreeGroup.mk_toWord]

end Work.OROneRel
