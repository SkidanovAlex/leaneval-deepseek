import Submission.Work.Item3.EnergyStepGeneral
import Submission.Commons.Data.Nat.ofDigits_lt_iff_lex
import Submission.Commons.Data.List.ofDigits_lt_pow_base

open Submission.Nielsen
open FreeGroup
open scoped BigOperators
set_option autoImplicit false

/-!
# EnergyDigits: the positional energy as a digit encoding

`wordEnergy B rank W = Σ_j B^{|W|-j}·rank(W_j)` is the base-`B` encoding of the
*reversed* digit list `(W.map rank).reverse`, i.e. `Nat.ofDigits B`.  This
module records that dictionary and its two consequences, imported from the
shared commons:

* `Nat.ofDigits` comparison is lexicographic on the *reversed* digit lists
  (`Commons.Data.Nat.ofDigits_lt_iff_lex`);
* an encoded list is smaller than the base to its length
  (`Commons.Data.List.ofDigits_lt_pow_base`), whence the **monotonicity of the
  energy in the word length** (`wordEnergy_lt_of_length_lt`): a shorter word
  always has strictly smaller energy.  This is what lets the `(N, eEnergy)`
  lexicographic descent of `EnergyAssembly` be replaced by the energy alone
  (any `N`-decreasing move is `eEnergy`-decreasing), and it is the arithmetic
  content of the "positional" comparisons in `energy_step_general_rho` /
  `_lam`.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- The positional energy of a word is the `Nat.ofDigits` encoding of its
reversed rank list. -/
lemma wordEnergy_eq_ofDigits {α : Type*} (B : ℕ) (rank : α → ℕ) (W : List α) :
    wordEnergy B rank W = Nat.ofDigits B (W.reverse.map rank) := by
  induction W with
  | nil => simp [wordEnergy, Nat.ofDigits]
  | cons a t ih =>
      rw [wordEnergy_cons, ih, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, Nat.ofDigits_append, Nat.ofDigits_cons, Nat.ofDigits_nil,
        List.length_map, List.length_reverse]
      ring

/-- **Energy monotone in length.**  With ranks in `[1, B)` and `B ≥ 2`, a word
strictly shorter than another has strictly smaller energy. -/
theorem wordEnergy_lt_of_length_lt {α : Type*} {B : ℕ} (hB : 1 < B)
    (rank : α → ℕ) (hr1 : ∀ a, 1 ≤ rank a) (hrB : ∀ a, rank a < B)
    {u v : List α} (h : u.length < v.length) :
    wordEnergy B rank u < wordEnergy B rank v := by
  have hu : wordEnergy B rank u < B ^ u.length := by
    rw [wordEnergy_eq_ofDigits]
    have := Commons.Data.List.ofDigits_lt_pow_base hB (d := u.reverse.map rank) (by
      intro x hx
      rcases List.mem_map.mp hx with ⟨a, _, rfl⟩
      exact hrB a)
    rwa [List.length_map, List.length_reverse] at this
  have hv : B ^ (v.length - 1) ≤ wordEnergy B rank v := by
    rcases v with _ | ⟨b, t⟩
    · simp at h
    · have h1 : 1 ≤ rank b := hr1 b
      have hlen : (b :: t).length - 1 = t.length := by simp
      rw [hlen, wordEnergy_cons]
      calc B ^ t.length = 1 * B ^ t.length := (one_mul _).symm
        _ ≤ rank b * B ^ t.length := Nat.mul_le_mul_right _ h1
        _ ≤ rank b * B ^ t.length + wordEnergy B rank t := Nat.le_add_right _ _
        _ = B ^ t.length * rank b + wordEnergy B rank t := by rw [Nat.mul_comm]
  have h2 : u.length ≤ v.length - 1 := by omega
  calc wordEnergy B rank u < B ^ u.length := hu
    _ ≤ B ^ (v.length - 1) := Nat.pow_le_pow_right (by omega) h2
    _ ≤ wordEnergy B rank v := hv

/-- **Energy comparison is the lexicographic order of the rank lists.**  For two
words of equal length with ranks in `[0, B)` and `B > 0`, the smaller energy is
the lexicographically smaller rank list. -/
theorem wordEnergy_lt_iff_lex {α : Type*} {B : ℕ} (hB : 0 < B)
    (rank : α → ℕ) (hrB : ∀ a, rank a < B) {u v : List α}
    (hlen : u.length = v.length) :
    wordEnergy B rank u < wordEnergy B rank v ↔
      List.Lex (· < ·) (u.map rank) (v.map rank) := by
  rw [wordEnergy_eq_ofDigits, wordEnergy_eq_ofDigits]
  have hmap : (u.reverse.map rank).reverse = u.map rank := by
    rw [List.map_reverse, List.reverse_reverse]
  have hmap' : (v.reverse.map rank).reverse = v.map rank := by
    rw [List.map_reverse, List.reverse_reverse]
  rw [← hmap, ← hmap']
  refine Commons.Data.Nat.ofDigits_lt_iff_lex hB ?_ ?_ ?_
  · rw [List.length_map, List.length_reverse, List.length_map, List.length_reverse, hlen]
  · intro x hx
    rcases List.mem_map.mp hx with ⟨a, _, rfl⟩
    exact hrB a
  · intro x hx
    rcases List.mem_map.mp hx with ⟨a, _, rfl⟩
    exact hrB a

end Submission.Nielsen
