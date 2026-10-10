import Mathlib.Data.Nat.SuccPred
import Mathlib.Algebra.Order.Ring.Nat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.prop5

universe u

/-- The free magma (binary trees) on `X`: the set of non-associative words. -/
inductive Magma (X : Type u) : Type u where
  | gen : X → Magma X
  | mul : Magma X → Magma X → Magma X

namespace Magma

variable {X : Type u}

/-- The foliage of a tree: erase the brackets. -/
def foliage : Magma X → List X
  | gen x => [x]
  | mul a b => foliage a ++ foliage b

@[simp] lemma foliage_gen (x : X) : foliage (gen x) = [x] := rfl

@[simp] lemma foliage_mul (a b : Magma X) :
    foliage (mul a b) = foliage a ++ foliage b := rfl

lemma foliage_ne_nil (w : Magma X) : foliage w ≠ [] := by
  induction w with
  | gen x => simp
  | mul a b iha ihb => simp [iha]

/-- The number of leaves of a tree. -/
def size : Magma X → ℕ
  | gen _ => 1
  | mul a b => size a + size b

@[simp] lemma size_gen (x : X) : size (gen x) = 1 := rfl

@[simp] lemma size_mul (a b : Magma X) : size (mul a b) = size a + size b := rfl

lemma size_pos (w : Magma X) : 0 < size w := by
  induction w with
  | gen x => simp
  | mul a b iha ihb => simp [iha]

lemma size_left_lt (a b : Magma X) : size a < size (mul a b) := by
  simp only [size_mul]
  exact Nat.lt_add_of_pos_right (size_pos b)

lemma size_right_lt (a b : Magma X) : size b < size (mul a b) := by
  simp only [size_mul]
  exact Nat.lt_add_of_pos_left (size_pos a)

lemma foliage_length (w : Magma X) : (foliage w).length = size w := by
  induction w with
  | gen x => simp
  | mul a b iha ihb => simp [iha, ihb]

end Magma

variable {X : Type u} [LinearOrder X]

/-- **Viennot's Hall set** (the convention of Viennot 1978): the set of trees `x` such that either
`x` is a generator, or `x = mul a b` with `a`, `b` Hall, `foliage a < foliage b`
(lexicographically), and either `b` is a generator or `b = mul z t` with `foliage z ≤ foliage a`. -/
def IsHall : Magma X → Prop
  | Magma.gen _ => True
  | Magma.mul a b =>
      IsHall a ∧ IsHall b ∧ Magma.foliage a < Magma.foliage b ∧
        ((∃ x, b = Magma.gen x) ∨
          (∃ z t, b = Magma.mul z t ∧ ¬ (Magma.foliage a < Magma.foliage z)))

@[simp] lemma isHall_gen (x : X) : IsHall (Magma.gen x : Magma X) := trivial

lemma isHall_mul_iff {a b : Magma X} :
    IsHall (Magma.mul a b) ↔
      IsHall a ∧ IsHall b ∧ Magma.foliage a < Magma.foliage b ∧
        ((∃ x, b = Magma.gen x) ∨
          (∃ z t, b = Magma.mul z t ∧ ¬ (Magma.foliage a < Magma.foliage z))) :=
  Iff.rfl

lemma IsHall.left {a b : Magma X} (h : IsHall (Magma.mul a b)) : IsHall a :=
  ((isHall_mul_iff).1 h).1

lemma IsHall.right {a b : Magma X} (h : IsHall (Magma.mul a b)) : IsHall b :=
  ((isHall_mul_iff).1 h).2.1

lemma IsHall.foliage_lt {a b : Magma X} (h : IsHall (Magma.mul a b)) :
    Magma.foliage a < Magma.foliage b :=
  ((isHall_mul_iff).1 h).2.2.1

/-- Splitting of a Hall tree `mul a b` according to the structure of `b`. -/
lemma IsHall.exists_eq {a b : Magma X} (h : IsHall (Magma.mul a b)) :
    (∃ x, b = Magma.gen x) ∨ (∃ z t, b = Magma.mul z t ∧ IsHall z ∧ IsHall t) := by
  cases b with
  | gen x => exact Or.inl ⟨x, rfl⟩
  | mul z t =>
      refine Or.inr ⟨z, t, rfl, ?_, ?_⟩
      · exact IsHall.left (IsHall.right h)
      · exact IsHall.right (IsHall.right h)

/-- Unfolding of the Hall condition: if `mul a b` is Hall and `b = mul z t`, then
`foliage z ≤ foliage a`. -/
lemma IsHall.le_of_right_eq_mul {a b z t : Magma X} (h : IsHall (Magma.mul a b))
    (hb : b = Magma.mul z t) : ¬ (Magma.foliage a < Magma.foliage z) := by
  rcases ((isHall_mul_iff).1 h).2.2.2 with ⟨x, hx⟩ | ⟨z', t', hz', hle⟩
  · rw [hb] at hx; exact absurd hx (by simp)
  · rw [hb] at hz'
    injection hz' with h1 _
    rwa [h1]

/-- The key case distinction for the "collecting" argument: if `a`, `b` are Hall trees with
`foliage a < foliage b` then either `mul a b` is Hall, or `b` is a composite `mul z t` with
`foliage a < foliage z`. -/
lemma isHall_mul_or {a b : Magma X} (ha : IsHall a) (hb : IsHall b)
    (hab : Magma.foliage a < Magma.foliage b) :
    IsHall (Magma.mul a b) ∨ ∃ z t, b = Magma.mul z t ∧ Magma.foliage a < Magma.foliage z := by
  by_cases h : ∃ z t, b = Magma.mul z t ∧ Magma.foliage a < Magma.foliage z
  · exact Or.inr h
  · left
    rw [isHall_mul_iff]
    refine ⟨ha, hb, hab, ?_⟩
    cases b with
    | gen x => exact Or.inl ⟨x, rfl⟩
    | mul z t =>
        refine Or.inr ⟨z, t, rfl, ?_⟩
        intro hlt
        exact h ⟨z, t, rfl, hlt⟩

end Work.SSGRoute.prop5
