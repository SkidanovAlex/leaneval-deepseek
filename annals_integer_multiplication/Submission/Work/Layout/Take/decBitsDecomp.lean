import Mathlib
import Submission.Work.Layout.Take.Defs
import Submission.Work.IntLib.ofBitsAPI

namespace Work.Layout.Take

/-! ## Auxiliary facts about leading zeros and `Nat.bits` -/

/-- The defining equation of `tzB` on a `false ::`-list. -/
@[simp] theorem tzB_false_cons (t : List Bool) : tzB (false :: t) = tzB t + 1 := rfl

/-- A list starting with `true` has no leading zeros. -/
@[simp] theorem tzB_true_cons (t : List Bool) : tzB (true :: t) = 0 := rfl

/-- `n` leading `false`s followed by a `true` have exactly `n` leading zeros. -/
@[simp] theorem tzB_replicate_false_cons_true (n : ℕ) (rest : List Bool) :
    tzB (List.replicate n false ++ true :: rest) = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

/-- A positive natural number has a nonempty bit list. -/
theorem bits_ne_nil {n : ℕ} (hn : n ≠ 0) : n.bits ≠ [] := by
  intro h
  have h1 : n.size = 0 := by rw [← Nat.size_eq_bits_len, h]; rfl
  exact hn (Nat.size_eq_zero.mp h1)

/-- A bit list of a positive number is nonempty. -/
theorem bits_eq_nil_iff {n : ℕ} : n.bits = [] ↔ n = 0 :=
  ⟨fun h => by
      by_contra hn
      exact bits_ne_nil hn h,
    fun h => by subst h; simp⟩

/-- Decomposition of the bit string of `k > 0`: after the leading (i.e. low) `false`s comes
a first `true`; subtracting one turns those `false`s into `true`s and flips that first `true`
into a `false` (unless it was the only bit), leaving the rest of the bits untouched. -/
theorem decBitsDecomp (k : ℕ) (hk : 0 < k) :
    ∃ (tz : ℕ) (rest : List Bool), k.bits = List.replicate tz false ++ true :: rest ∧
      tz = tzB k.bits ∧
      (k - 1).bits = List.replicate tz true ++ (if rest = [] then [] else false :: rest) := by
  suffices h : ∀ k, 0 < k → ∃ rest : List Bool,
      k.bits = List.replicate (tzB k.bits) false ++ true :: rest ∧
      (k - 1).bits = List.replicate (tzB k.bits) true ++
        (if rest = [] then [] else false :: rest) by
    obtain ⟨rest, h1, h2⟩ := h k hk
    exact ⟨tzB k.bits, rest, h1, rfl, h2⟩
  intro k
  refine Nat.strong_induction_on k fun n ih hk => ?_
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- `n = 2 * m` even, so the low bit is `false` and we recurse on `m`
    have hk2 : n = 2 * m := by omega
    rw [hk2] at hk ⊢
    have hm0 : m ≠ 0 := by omega
    obtain ⟨rest, h1, h2⟩ := ih m (by omega) (Nat.pos_of_ne_zero hm0)
    refine ⟨rest, ?_, ?_⟩
    · rw [Nat.bit0_bits m hm0, h1]
      simp [List.replicate_succ]
    · have hsub : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
      rw [hsub, Nat.bit1_bits, Nat.bit0_bits m hm0, h2]
      simp [List.replicate_succ]
  · -- `n = 2 * m + 1` odd, so the low bit is `true` and `tzB = 0`
    have hk2 : n = 2 * m + 1 := by omega
    rw [hk2] at hk ⊢
    refine ⟨m.bits, ?_, ?_⟩
    · rw [Nat.bit1_bits]
      simp
    · have hsub : 2 * m + 1 - 1 = 2 * m := by omega
      rw [hsub, Nat.bit1_bits]
      simp only [tzB_true_cons, List.replicate_zero, List.nil_append]
      by_cases hm0 : m = 0
      · subst m
        simp
      · rw [Nat.bit0_bits m hm0]
        simp [bits_ne_nil hm0]

end Work.Layout.Take
