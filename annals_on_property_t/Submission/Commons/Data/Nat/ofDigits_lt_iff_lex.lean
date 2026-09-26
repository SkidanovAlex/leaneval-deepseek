import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.SuccPred

set_option linter.unusedVariables false

/-!
# The digit encoding is the lexicographic order of the reversed digit list

`Nat.ofDigits B d = ∑_{j} d_j B^{j}` reads `d` as the base-`B` expansion with the
*least* significant digit first.  For two digit lists of equal length with all
digits `< B`, comparing the encoded numbers is the same as comparing the
digit lists *reversed*, lexicographically.  This is the arithmetic core of
"positional energy" arguments (a state energy of the form
`∑_j B^{|w|-j} · rank(letter_j)` is an `ofDigits` of the reversed digit list).
-/

namespace Commons.Data.Nat

/-- The one-step unfolding of `List.Lex`: two nonempty lists are lexicographically
related iff either their heads are related, or the heads are equal and the tails are
lexicographically related. -/
private lemma list_lex_cons_iff {α : Type*} (r : α → α → Prop) (a b : α) (t u : List α) :
    List.Lex r (a :: t) (b :: u) ↔ r a b ∨ (a = b ∧ List.Lex r t u) := by
  constructor
  · intro h
    cases h with
    | cons h => exact Or.inr ⟨rfl, h⟩
    | rel h => exact Or.inl h
  · rintro (h | ⟨rfl, h⟩)
    · exact List.Lex.rel h
    · exact List.Lex.cons h

/-- Comparing two "digit blocks": if both low parts `vt, vu` are `< M`, then
`vt + M*a < vu + M*b` iff the high digits compare, or are equal and the low parts
compare.  This is the arithmetic heart of positional comparison. -/
private lemma key {M a b vt vu : ℕ} (hvt : vt < M) (hvu : vu < M) :
    vt + M * a < vu + M * b ↔ a < b ∨ (a = b ∧ vt < vu) := by
  constructor
  · intro h
    rcases lt_trichotomy a b with hab | hab | hba
    · exact Or.inl hab
    · subst hab
      exact Or.inr ⟨rfl, (Nat.add_lt_add_iff_right).mp h⟩
    · exfalso
      have hb1 : b + 1 ≤ a := hba
      have h1 : vu + M * b < M * b + M := by
        rw [Nat.add_comm vu (M * b)]
        exact Nat.add_lt_add_left hvu (M * b)
      have h2 : M * b + M ≤ M * a := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left M hb1
      have h3 : M * a ≤ M * a + vt := Nat.le_add_right _ _
      omega
  · rintro (hab | ⟨rfl, h⟩)
    · have h1 : vt + M * a < M * a + M := by
        rw [Nat.add_comm vt (M * a)]
        exact Nat.add_lt_add_left hvt (M * a)
      have h2 : M * a + M ≤ M * b := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left M (Nat.succ_le_of_lt hab)
      have h3 : M * b ≤ M * b + vu := Nat.le_add_right _ _
      omega
    · exact (Nat.add_lt_add_iff_right).mpr h

/-- The `ofDigits` value of a digit list is bounded by the base to the length. -/
private lemma ofDigits_reverse_lt_pow {B : ℕ} :
    ∀ {r : List ℕ}, (∀ x ∈ r, x < B) → Nat.ofDigits B r.reverse < B ^ r.length := by
  intro r
  induction r with
  | nil => simp
  | cons a t ih =>
    intro hd
    have hdt : ∀ x ∈ t, x < B := fun x hx => hd x (List.mem_cons_of_mem a hx)
    have IH := ih hdt
    have ha : a + 1 ≤ B := Nat.succ_le_of_lt (hd a (by simp))
    rw [Nat.ofDigits_reverse_cons, List.length_cons, pow_succ]
    have h1 : Nat.ofDigits B t.reverse + B ^ t.length * a < B ^ t.length + B ^ t.length * a :=
      Nat.add_lt_add_right IH (B ^ t.length * a)
    have h2 : B ^ t.length + B ^ t.length * a ≤ B ^ t.length * B := by
      rw [Nat.add_comm, ← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ ha
    exact lt_of_lt_of_le h1 h2

/-- The main comparison: for two digit lists `r₁, r₂` of equal length whose entries are
`< B`, the `ofDigits` of their reverses compares like `r₁` and `r₂` do lexicographically. -/
private lemma val_lt_iff_lex {B : ℕ} :
    ∀ (r₁ : List ℕ) {r₂ : List ℕ}, r₁.length = r₂.length →
      (∀ x ∈ r₁, x < B) → (∀ x ∈ r₂, x < B) →
      (Nat.ofDigits B r₁.reverse < Nat.ofDigits B r₂.reverse ↔ List.Lex (· < ·) r₁ r₂) := by
  intro r₁
  induction r₁ with
  | nil =>
    intro r₂ hlen _ _
    cases r₂ with
    | nil =>
      simp only [List.reverse_nil, Nat.ofDigits_nil]
      constructor
      · intro h; exact absurd h (lt_irrefl 0)
      · intro h; cases h
    | cons b u => simp at hlen
  | cons a t ih =>
    intro r₂ hlen hd1 hd2
    cases r₂ with
    | nil => simp at hlen
    | cons b u =>
      simp only [List.length_cons] at hlen
      have hlen' : t.length = u.length := by omega
      have hd1t : ∀ x ∈ t, x < B := fun x hx => hd1 x (List.mem_cons_of_mem a hx)
      have hd2u : ∀ x ∈ u, x < B := fun x hx => hd2 x (List.mem_cons_of_mem b hx)
      have hvt : Nat.ofDigits B t.reverse < B ^ t.length := ofDigits_reverse_lt_pow hd1t
      have hp : B ^ u.length = B ^ t.length := by rw [← hlen']
      have hvu : Nat.ofDigits B u.reverse < B ^ t.length :=
        lt_of_lt_of_eq (ofDigits_reverse_lt_pow hd2u) hp
      have ihh : Nat.ofDigits B t.reverse < Nat.ofDigits B u.reverse ↔ List.Lex (· < ·) t u :=
        ih hlen' hd1t hd2u
      rw [Nat.ofDigits_reverse_cons, Nat.ofDigits_reverse_cons, ← hlen', list_lex_cons_iff,
        ← ihh]
      exact key hvt hvu

theorem ofDigits_lt_iff_lex {B : ℕ} (hB : 0 < B) :
    ∀ {d₁ d₂ : List ℕ}, d₁.length = d₂.length →
      (∀ x ∈ d₁, x < B) → (∀ x ∈ d₂, x < B) →
      (Nat.ofDigits B d₁ < Nat.ofDigits B d₂ ↔ List.Lex (· < ·) d₁.reverse d₂.reverse) := by
  intro d₁ d₂ hlen hd1 hd2
  have h1 : ∀ x ∈ d₁.reverse, x < B := fun x hx => hd1 x (List.mem_reverse.mp hx)
  have h2 : ∀ x ∈ d₂.reverse, x < B := fun x hx => hd2 x (List.mem_reverse.mp hx)
  have hlen' : d₁.reverse.length = d₂.reverse.length := by simpa using hlen
  have hkey := val_lt_iff_lex d₁.reverse hlen' h1 h2
  simpa only [List.reverse_reverse] using hkey

end Commons.Data.Nat