/-
# The occurrence terms of the Fox expansion of `∂·/∂x`

Leaf definitions used by the level method of `Submission/Work/ORLyndon/epsNeZeroDescent.lean`.

For a word `L : List (α × Bool)` and a letter `x`, the Fox derivative `∂L/∂x` (in the form of
`Work.OROneRel.foxWord` / `Work.ORLyndon.rootVec_occurrences`) is the signed sum of the *occurrence
terms*: the prefix of `L` ending just before an occurrence of `(x, true)`, with coefficient `+1`, and
the prefix ending just after an occurrence of `(x, false)` (i.e. including the `x⁻¹`), with
coefficient `-1`.  Every letter of `L` different from `x^{±1}` contributes `0`.

* `occPref x L i` -- the prefix of `L` attached to position `i`;
* `occTerm x L i` -- its class in the free group (the group element of the term);
* `occSign x L i` -- the integer coefficient (`1`, `-1`, or `0`), field-independent;
* `occEps K x L i` -- the same coefficient in an arbitrary ring `K`.

Keeping `occSign` (integer valued) separate from `occEps` (ring valued) is what allows the
combinatorial statements about the occurrence family -- which never mention the coefficient ring --
to be stated without a `[Field K]` hypothesis.
-/
import Mathlib
import Submission.Work.OROneRel.wordOfDefs
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.MagnusGenDefs

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLyndon

variable {α : Type u} [DecidableEq α]

/-- The prefix of the word `L` attached to position `i` in the Fox expansion of `∂·/∂x`: `L` cut just
*before* the `i`-th letter when that letter is `x`, and just *after* it when the letter is `x⁻¹`.
For a letter different from `x^{±1}` the value is irrelevant, since the accompanying coefficient
`occEps` vanishes there. -/
noncomputable def occPref (x : α) (L : List (α × Bool)) (i : Fin L.length) : List (α × Bool) :=
  L.take (i.1 + if L.get i = (x, true) then 0 else 1)

/-- The `i`-th occurrence term of the Fox expansion of `∂·/∂x` along the word `L`, as an element of
the free group: `occTerm x L i = mk (occPref x L i)`.

(Classically the term is the prefix *before* a positive occurrence and `-` the prefix *after* a
negative one; here the negative occurrence carries the prefix *including* the `x⁻¹` and the sign
`occEps = -1`, which is the same group element.)

The body is written out so that it is definitionally the original form of the occurrence term; the
identification with `mk (occPref x L i)` is `occTerm_eq_mk_occPref` (a `rfl`). -/
noncomputable def occTerm (x : α) (L : List (α × Bool)) (i : Fin L.length) : FreeGroup α :=
  FreeGroup.mk (L.take (i.1 + if L.get i = (x, true) then 0 else 1))

/-- The coefficient of the `i`-th occurrence term, as an integer: `1` for an occurrence of `x`, `-1`
for an occurrence of `x⁻¹`, and `0` for a letter different from `x^{±1}`. -/
noncomputable def occSign (x : α) (L : List (α × Bool)) (i : Fin L.length) : ℤ :=
  if L.get i = (x, true) then 1 else if L.get i = (x, false) then -1 else 0

/-- The coefficient of the `i`-th occurrence term, in an arbitrary ring. -/
noncomputable def occEps (K : Type*) [Ring K] (x : α) (L : List (α × Bool))
    (i : Fin L.length) : K :=
  if L.get i = (x, true) then 1 else if L.get i = (x, false) then -1 else 0

@[simp] theorem occTerm_eq_mk_occPref (x : α) (L : List (α × Bool)) (i : Fin L.length) :
    occTerm x L i = FreeGroup.mk (occPref x L i) := rfl

theorem occPref_take (x : α) (L : List (α × Bool)) (i : Fin L.length) :
    occPref x L i = L.take (i.1 + if L.get i = (x, true) then 0 else 1) := rfl

theorem occSign_pos (x : α) (L : List (α × Bool)) (i : Fin L.length)
    (h : L.get i = (x, true)) : occSign x L i = 1 := by
  unfold occSign; rw [if_pos h]

theorem occSign_neg (x : α) (L : List (α × Bool)) (i : Fin L.length)
    (h1 : ¬ L.get i = (x, true)) (h : L.get i = (x, false)) : occSign x L i = -1 := by
  unfold occSign; rw [if_neg h1, if_pos h]

theorem occSign_zero (x : α) (L : List (α × Bool)) (i : Fin L.length)
    (h1 : ¬ L.get i = (x, true)) (h2 : ¬ L.get i = (x, false)) : occSign x L i = 0 := by
  unfold occSign; rw [if_neg h1, if_neg h2]

theorem occEps_pos (K : Type*) [Ring K] (x : α) (L : List (α × Bool)) (i : Fin L.length)
    (h : L.get i = (x, true)) : occEps K x L i = 1 := by
  unfold occEps; rw [if_pos h]

theorem occEps_neg (K : Type*) [Ring K] (x : α) (L : List (α × Bool)) (i : Fin L.length)
    (h1 : ¬ L.get i = (x, true)) (h : L.get i = (x, false)) : occEps K x L i = -1 := by
  unfold occEps; rw [if_neg h1, if_pos h]

theorem occEps_zero (K : Type*) [Ring K] (x : α) (L : List (α × Bool)) (i : Fin L.length)
    (h1 : ¬ L.get i = (x, true)) (h2 : ¬ L.get i = (x, false)) : occEps K x L i = 0 := by
  unfold occEps; rw [if_neg h1, if_neg h2]

theorem occEps_eq_intCast (K : Type*) [Ring K] (x : α) (L : List (α × Bool)) (i : Fin L.length) :
    occEps K x L i = ((occSign x L i : ℤ) : K) := by
  by_cases h1 : L.get i = (x, true)
  · rw [occSign_pos x L i h1, occEps_pos K x L i h1]; simp
  · by_cases h2 : L.get i = (x, false)
    · rw [occSign_neg x L i h1 h2, occEps_neg K x L i h1 h2]; simp
    · rw [occSign_zero x L i h1 h2, occEps_zero K x L i h1 h2]; simp

/-- The occurrence coefficient is non-zero exactly at the occurrences of `x^{±1}`. -/
theorem occSign_ne_zero_iff (x : α) (L : List (α × Bool)) (i : Fin L.length) :
    occSign x L i ≠ 0 ↔ L.get i = (x, true) ∨ L.get i = (x, false) := by
  by_cases h1 : L.get i = (x, true)
  · rw [occSign_pos x L i h1]
    exact ⟨fun _ => Or.inl h1, fun _ => one_ne_zero⟩
  · by_cases h2 : L.get i = (x, false)
    · rw [occSign_neg x L i h1 h2]
      exact ⟨fun _ => Or.inr h2, fun _ => neg_ne_zero.mpr one_ne_zero⟩
    · rw [occSign_zero x L i h1 h2]
      exact ⟨fun h => absurd rfl h,
        fun h => h.elim (fun hp => absurd hp h1) (fun hq => absurd hq h2)⟩

/-- The occurrence coefficient of a ring is non-zero exactly at the occurrences of `x^{±1}`
(valid in every non-trivial ring: only `±1` occurs). -/
theorem occEps_ne_zero_iff (K : Type*) [Ring K] [Nontrivial K] (x : α) (L : List (α × Bool))
    (i : Fin L.length) :
    occEps K x L i ≠ 0 ↔ L.get i = (x, true) ∨ L.get i = (x, false) := by
  by_cases h1 : L.get i = (x, true)
  · rw [occEps_pos K x L i h1]
    exact ⟨fun _ => Or.inl h1, fun _ => one_ne_zero⟩
  · by_cases h2 : L.get i = (x, false)
    · rw [occEps_neg K x L i h1 h2]
      exact ⟨fun _ => Or.inr h2, fun _ => neg_ne_zero.mpr one_ne_zero⟩
    · rw [occEps_zero K x L i h1 h2]
      exact ⟨fun h => absurd rfl h,
        fun h => h.elim (fun hp => absurd hp h1) (fun hq => absurd hq h2)⟩

/-- At a position where the sign does not vanish, the sign is `±1`; hence the ring-valued
coefficient is non-zero in every non-trivial ring. -/
theorem occEps_ne_zero_of_occSign_ne_zero {K : Type*} [Ring K] [Nontrivial K] (x : α)
    (L : List (α × Bool)) (i : Fin L.length) (h : occSign x L i ≠ 0) : occEps K x L i ≠ 0 := by
  rw [occEps_eq_intCast]
  rcases (occSign_ne_zero_iff x L i).mp h with h1 | h1
  · rw [occSign_pos x L i h1]; simp
  · have hnt : ¬ L.get i = (x, true) := by rw [h1]; simp
    rw [occSign_neg x L i hnt h1]; simp

/-- Conversely, a non-vanishing ring-valued coefficient gives a non-vanishing integer sign. -/
theorem occSign_ne_zero_of_occEps_ne_zero {K : Type*} [Ring K] [Nontrivial K] (x : α)
    (L : List (α × Bool)) (i : Fin L.length) (h : occEps K x L i ≠ 0) : occSign x L i ≠ 0 := by
  intro h0
  exact h (by rw [occEps_eq_intCast, h0]; simp)

end Work.ORLyndon
