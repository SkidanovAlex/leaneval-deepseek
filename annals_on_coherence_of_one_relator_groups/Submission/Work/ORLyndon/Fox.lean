import Mathlib

/-!
# Fox derivatives on free groups
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

universe u v

variable {X : Type u} {K : Type v}

section FoxWord

variable [Ring K] [DecidableEq X]

/-- The letter obtained by negating the exponent of `c`. -/
abbrev flipLetter (c : X × Bool) : X × Bool := (c.1, !c.2)

/-- The element of the free group corresponding to a single letter. -/
abbrev letterGroup (c : X × Bool) : FreeGroup X :=
  if c.2 then FreeGroup.of c.1 else (FreeGroup.of c.1)⁻¹

/-- The finite set of letters occurring in a word. -/
def letters (L : List (X × Bool)) : Finset X :=
  (L.map (fun c : X × Bool => c.1)).toFinset

@[simp] theorem mem_letters {x : X} {L : List (X × Bool)} :
    x ∈ letters L ↔ ∃ b : Bool, (x, b) ∈ L := by
  simp [letters]

@[simp] theorem letters_cons (c : X × Bool) (L : List (X × Bool)) :
    letters (c :: L) = insert c.1 (letters L) := by
  ext x
  rw [mem_letters, Finset.mem_insert, mem_letters]
  constructor
  · rintro ⟨b, hb⟩
    rcases List.mem_cons.mp hb with h | h
    · exact Or.inl (by simpa using congrArg Prod.fst h)
    · exact Or.inr ⟨b, h⟩
  · rintro (h | ⟨b, hb⟩)
    · exact ⟨c.2, by rw [h]; exact List.mem_cons_self⟩
    · exact ⟨b, List.mem_cons_of_mem _ hb⟩

/-- `(y, true)` is the generator `y`. -/
@[simp] theorem mk_true (y : X) :
    FreeGroup.mk ([(y, true)] : List (X × Bool)) = FreeGroup.of y := rfl

/-- `(y, false)` is the inverse of the generator `y`. -/
@[simp] theorem mk_false (y : X) :
    FreeGroup.mk ([(y, false)] : List (X × Bool)) = (FreeGroup.of y)⁻¹ := by
  rw [← mk_true y, FreeGroup.inv_mk]
  rfl

/-- The group element of a letter, as a product. -/
theorem letterGroup_mul_mk (c : X × Bool) (L : List (X × Bool)) :
    letterGroup c * FreeGroup.mk L = FreeGroup.mk (c :: L) := by
  obtain ⟨y, b⟩ := c
  cases b
  · rw [show letterGroup (y, false) = (FreeGroup.of y)⁻¹ from rfl, ← mk_false y,
      FreeGroup.mul_mk]
    rfl
  · rw [show letterGroup (y, true) = FreeGroup.of y from rfl, ← mk_true y, FreeGroup.mul_mk]
    rfl

/-- A letter times its inverse is trivial. -/
theorem letterGroup_mul_flipLetter (c : X × Bool) :
    letterGroup c * letterGroup (flipLetter c) = 1 := by
  obtain ⟨y, b⟩ := c
  cases b
  · rw [show letterGroup (y, false) = (FreeGroup.of y)⁻¹ from rfl,
      show letterGroup (flipLetter (y, false)) = FreeGroup.of y from rfl, inv_mul_cancel]
  · rw [show letterGroup (y, true) = FreeGroup.of y from rfl,
      show letterGroup (flipLetter (y, true)) = (FreeGroup.of y)⁻¹ from rfl, mul_inv_cancel]

/-- The contribution of a single letter `c` to the Fox derivative with respect to `x`:
`δ_{xy}` for `c = (y, true)` and `-y⁻¹δ_{xy}` for `c = (y, false)`. -/
noncomputable def foxLetter (x : X) : X × Bool → MonoidAlgebra K (FreeGroup X)
  | (y, true) => if y = x then 1 else 0
  | (y, false) =>
      if y = x then -(MonoidAlgebra.of K (FreeGroup X) (letterGroup (y, false))) else 0

/-- The Fox derivative `∂w/∂x` of a word `w`, as an element of `K[F(X)]`, defined by the
recursion `D(1) = 0` and `D(c :: L) = D(c) + c * D(L)`. -/
noncomputable def foxWord (x : X) : List (X × Bool) → MonoidAlgebra K (FreeGroup X)
  | [] => 0
  | c :: L => foxLetter (K := K) x c +
      (MonoidAlgebra.of K (FreeGroup X) (letterGroup c)) * foxWord x L

@[simp] theorem foxWord_nil (x : X) : foxWord (K := K) x ([] : List (X × Bool)) = 0 := rfl

@[simp] theorem foxWord_cons (x : X) (c : X × Bool) (L : List (X × Bool)) :
    foxWord (K := K) x (c :: L) = foxLetter (K := K) x c +
      (MonoidAlgebra.of K (FreeGroup X) (letterGroup c)) * foxWord (K := K) x L := rfl

theorem foxLetter_true (x y : X) :
    foxLetter (K := K) x (y, true) = if y = x then 1 else 0 := rfl

theorem foxLetter_false (x y : X) :
    foxLetter (K := K) x (y, false) =
      if y = x then -(MonoidAlgebra.of K (FreeGroup X) ((FreeGroup.of y)⁻¹)) else 0 := rfl

theorem of_mul_of_inv (y : X) :
    (MonoidAlgebra.of K (FreeGroup X) (FreeGroup.of y)) *
      (MonoidAlgebra.of K (FreeGroup X) ((FreeGroup.of y)⁻¹)) = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

/-- `∂c/∂x + c * ∂c⁻¹/∂x = 0` for a single letter `c = (y, true)`. -/
theorem foxLetter_add_mul_foxLetter_flip_true (x y : X) :
    foxLetter (K := K) x (y, true) +
      (MonoidAlgebra.of K (FreeGroup X) (FreeGroup.of y)) *
        foxLetter (K := K) x (y, false) = 0 := by
  rw [foxLetter_true, foxLetter_false]
  by_cases hy : y = x
  · subst hy
    rw [if_pos rfl, if_pos rfl, mul_neg, of_mul_of_inv]
    simp
  · rw [if_neg hy, if_neg hy, mul_zero, add_zero]

/-- `∂c/∂x + c * ∂c⁻¹/∂x = 0` for a single letter `c = (y, false)`. -/
theorem foxLetter_add_mul_foxLetter_flip_false (x y : X) :
    foxLetter (K := K) x (y, false) +
      (MonoidAlgebra.of K (FreeGroup X) ((FreeGroup.of y)⁻¹)) *
        foxLetter (K := K) x (y, true) = 0 := by
  rw [foxLetter_true, foxLetter_false]
  by_cases hy : y = x
  · subst hy
    rw [if_pos rfl, if_pos rfl, mul_one]
    exact neg_add_cancel _
  · rw [if_neg hy, if_neg hy, mul_zero, add_zero]

/-- `∂c/∂x + c * ∂c⁻¹/∂x = 0` for a single letter. -/
theorem foxLetter_add_mul_foxLetter_flip (x : X) (c : X × Bool) :
    foxLetter (K := K) x c +
      (MonoidAlgebra.of K (FreeGroup X) (letterGroup c)) *
        foxLetter (K := K) x (flipLetter c) = 0 := by
  obtain ⟨y, b⟩ := c
  cases b
  · exact foxLetter_add_mul_foxLetter_flip_false (K := K) x y
  · exact foxLetter_add_mul_foxLetter_flip_true (K := K) x y

/-- Cancelling a `false` letter against a `true` letter does not change the Fox derivative. -/
theorem foxWord_step_cancel_false (x y : X) (L : List (X × Bool)) :
    foxWord (K := K) x ((y, false) :: (y, true) :: L) = foxWord (K := K) x L := by
  rw [foxWord_cons, foxWord_cons]
  have h1 : foxLetter (K := K) x (y, false) +
      (MonoidAlgebra.of K (FreeGroup X) (letterGroup (y, false))) *
        foxLetter (K := K) x (y, true) = 0 := by
    rw [show letterGroup (y, false) = (FreeGroup.of y)⁻¹ from rfl]
    exact foxLetter_add_mul_foxLetter_flip_false (K := K) x y
  have h2 : (MonoidAlgebra.of K (FreeGroup X) (letterGroup (y, false))) *
      (MonoidAlgebra.of K (FreeGroup X) (letterGroup (y, true))) = 1 := by
    rw [← map_mul, show letterGroup (y, false) * letterGroup (y, true) = 1 from
      inv_mul_cancel (FreeGroup.of y), map_one]
  rw [mul_add, ← mul_assoc, h2, one_mul, ← add_assoc, h1, zero_add]

/-- Cancelling a `true` letter against a `false` letter does not change the Fox derivative. -/
theorem foxWord_step_cancel_true (x y : X) (L : List (X × Bool)) :
    foxWord (K := K) x ((y, true) :: (y, false) :: L) = foxWord (K := K) x L := by
  rw [foxWord_cons, foxWord_cons]
  have h1 : foxLetter (K := K) x (y, true) +
      (MonoidAlgebra.of K (FreeGroup X) (letterGroup (y, true))) *
        foxLetter (K := K) x (y, false) = 0 := by
    rw [show letterGroup (y, true) = FreeGroup.of y from rfl]
    exact foxLetter_add_mul_foxLetter_flip_true (K := K) x y
  have h2 : (MonoidAlgebra.of K (FreeGroup X) (letterGroup (y, true))) *
      (MonoidAlgebra.of K (FreeGroup X) (letterGroup (y, false))) = 1 := by
    rw [← map_mul, show letterGroup (y, true) * letterGroup (y, false) = 1 from
      mul_inv_cancel (FreeGroup.of y), map_one]
  rw [mul_add, ← mul_assoc, h2, one_mul, ← add_assoc, h1, zero_add]

/-- Inserting a cancelling pair of letters does not change the Fox derivative. -/
theorem foxWord_step_cancel (x : X) (c : X × Bool) (L : List (X × Bool)) :
    foxWord (K := K) x (c :: (c.1, !c.2) :: L) = foxWord (K := K) x L := by
  obtain ⟨y, b⟩ := c
  cases b
  · exact foxWord_step_cancel_false (K := K) x y L
  · exact foxWord_step_cancel_true (K := K) x y L

/-- The Fox derivative of a concatenation of words. -/
theorem foxWord_append (x : X) (L₁ L₂ : List (X × Bool)) :
    foxWord (K := K) x (L₁ ++ L₂) = foxWord (K := K) x L₁ +
      (MonoidAlgebra.of K (FreeGroup X) (FreeGroup.mk L₁)) * foxWord (K := K) x L₂ := by
  induction L₁ with
  | nil =>
      simp only [List.nil_append, foxWord_nil, zero_add, ← FreeGroup.one_eq_mk, map_one, one_mul]
  | cons c L₁ ih =>
      have h : foxWord (K := K) x ((c :: L₁) ++ L₂) = foxWord (K := K) x (c :: (L₁ ++ L₂)) :=
        rfl
      rw [h, foxWord_cons, ih, foxWord_cons, ← letterGroup_mul_mk c L₁, map_mul]
      noncomm_ring

/-- The Fox derivative is invariant under free reduction: it descends to `FreeGroup X`. -/
theorem foxWord_reduce (x : X) {L₁ L₂ : List (X × Bool)} (h : FreeGroup.Red.Step L₁ L₂) :
    foxWord (K := K) x L₁ = foxWord (K := K) x L₂ := by
  cases h with
  | not =>
      rename_i L₀ L y c
      show foxWord (K := K) x (L₀ ++ (y, c) :: (y, !c) :: L) =
        foxWord (K := K) x (L₀ ++ L)
      rw [foxWord_append, foxWord_append]
      cases c with
      | false =>
          simp only [Bool.not_false]
          rw [foxWord_step_cancel_false]
      | true =>
          simp only [Bool.not_true]
          rw [foxWord_step_cancel_true]

/-- `∂c/∂x = 0` when `c` is not the letter `x`. -/
@[simp] theorem foxLetter_eq_zero_of_ne {x y : X} (h : y ≠ x) (b : Bool) :
    foxLetter (K := K) x (y, b) = 0 := by
  cases b
  · rw [foxLetter_false, if_neg h]
  · rw [foxLetter_true, if_neg h]

/-- The Fox derivative of a word not involving `x` vanishes. -/
theorem foxWord_eq_zero_of_notMem {x : X} {L : List (X × Bool)} (h : x ∉ letters L) :
    foxWord (K := K) x L = 0 := by
  induction L with
  | nil => rfl
  | cons c L ih =>
      rw [letters_cons] at h
      have hc : c.1 ≠ x := fun hc => h (by rw [hc]; exact Finset.mem_insert_self _ _)
      have hL : x ∉ letters L := fun hmem => h (Finset.mem_insert_of_mem hmem)
      rw [foxWord_cons, ih hL, foxLetter_eq_zero_of_ne hc, mul_zero, add_zero]

/-- The Fox derivative `∂w/∂x` of an element `w` of the free group, as an element of `K[F(X)]`. -/
noncomputable def foxD (x : X) : FreeGroup X → MonoidAlgebra K (FreeGroup X) :=
  Quot.lift (foxWord (K := K) x) fun _ _ h => foxWord_reduce (K := K) x h

@[simp] theorem foxD_mk (x : X) (L : List (X × Bool)) :
    foxD (K := K) x (FreeGroup.mk L) = foxWord (K := K) x L := rfl

@[simp] theorem foxD_one (x : X) : foxD (K := K) x (1 : FreeGroup X) = 0 := by
  rw [FreeGroup.one_eq_mk, foxD_mk]; rfl

@[simp] theorem foxD_of (x y : X) :
    foxD (K := K) x (FreeGroup.of y) = if y = x then 1 else 0 := by
  rw [FreeGroup.of, foxD_mk, foxWord_cons, foxWord_nil, mul_zero, add_zero, foxLetter_true]

@[simp] theorem foxD_inv_of (x y : X) :
    foxD (K := K) x ((FreeGroup.of y)⁻¹) =
      if y = x then -(MonoidAlgebra.of K (FreeGroup X) ((FreeGroup.of y)⁻¹)) else 0 := by
  conv_lhs => rw [← mk_false y]
  rw [foxD_mk, foxWord_cons, foxWord_nil, mul_zero, add_zero, foxLetter_false]

/-- The derivation property of the Fox derivative. -/
theorem foxD_mul (x : X) (g h : FreeGroup X) :
    foxD (K := K) x (g * h) = foxD (K := K) x g +
      (MonoidAlgebra.of K (FreeGroup X) g) * foxD (K := K) x h := by
  induction g using Quot.inductionOn with
  | h L₁ =>
    induction h using Quot.inductionOn with
    | h L₂ =>
      exact foxWord_append (K := K) x L₁ L₂

/-- The Fox derivative of an inverse. -/
theorem foxD_inv (x : X) (g : FreeGroup X) :
    foxD (K := K) x g⁻¹ =
      -((MonoidAlgebra.of K (FreeGroup X)) (g⁻¹) * foxD (K := K) x g) := by
  have h := foxD_mul (K := K) x g g⁻¹
  rw [mul_inv_cancel, foxD_one] at h
  have h2 : (MonoidAlgebra.of K (FreeGroup X)) g * foxD (K := K) x g⁻¹ =
      -foxD (K := K) x g := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h.symm
  have h3 : (MonoidAlgebra.of K (FreeGroup X)) (g⁻¹) *
      ((MonoidAlgebra.of K (FreeGroup X)) g * foxD (K := K) x g⁻¹) = foxD (K := K) x g⁻¹ := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  calc foxD (K := K) x g⁻¹
      = (MonoidAlgebra.of K (FreeGroup X)) (g⁻¹) *
          ((MonoidAlgebra.of K (FreeGroup X)) g * foxD (K := K) x g⁻¹) := h3.symm
    _ = (MonoidAlgebra.of K (FreeGroup X)) (g⁻¹) * (-foxD (K := K) x g) := by rw [h2]
    _ = -((MonoidAlgebra.of K (FreeGroup X)) (g⁻¹) * foxD (K := K) x g) := by rw [mul_neg]

/-- The Fox derivative vanishes on words not containing `x`. -/
theorem foxD_eq_zero_of_notMem {x : X} {L : List (X × Bool)} (h : x ∉ letters L) :
    foxD (K := K) x (FreeGroup.mk L) = 0 := by
  rw [foxD_mk, foxWord_eq_zero_of_notMem h]

/-- `x ↦ ∂w/∂x` as an element of `X →₀ K[F(X)]` (finite support). -/
noncomputable def foxFD (w : FreeGroup X) : X →₀ MonoidAlgebra K (FreeGroup X) :=
  Quot.lift
    (fun L : List (X × Bool) =>
      Finsupp.ofSupportFinite (fun x : X => foxWord (K := K) x L)
        ((letters L).finite_toSet.subset (fun x hx => by
          by_contra hmem
          rw [Function.mem_support] at hx
          exact hx (foxWord_eq_zero_of_notMem hmem))))
    (fun _ _ h => Finsupp.ext fun x => by
      rw [Finsupp.ofSupportFinite_coe, Finsupp.ofSupportFinite_coe]
      exact foxWord_reduce x h)
    w

theorem foxFD_mk (L : List (X × Bool)) (x : X) :
    foxFD (K := K) (FreeGroup.mk L) x = foxWord (K := K) x L := by
  rw [foxFD, FreeGroup.quot_lift_mk, Finsupp.ofSupportFinite_coe]

@[simp] theorem foxFD_apply (w : FreeGroup X) (x : X) :
    foxFD (K := K) w x = foxD (K := K) x w := by
  induction w using Quot.inductionOn with
  | h L =>
      change foxFD (K := K) (FreeGroup.mk L) x = foxD (K := K) x (FreeGroup.mk L)
      rw [foxFD_mk, foxD_mk]

end FoxWord

end Work.ORLyndon
