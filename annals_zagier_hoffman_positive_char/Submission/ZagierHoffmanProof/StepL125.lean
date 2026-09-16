import Submission.ZagierHoffmanProof.StepL124
import Submission.ZagierHoffmanProof.StepL82
set_option autoImplicit false
set_option maxHeartbeats 400000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L125: the initial-tuple (Init) side of the μ3 measure — padCode/
initList infrastructure for maink_mixed_type1_init_bound (SESSION 258r)

The (β)-measure μ₃(s) = (psum s k, initVal q w s, pad0 s (initLen q s)) needs the
Init-based growth facts for the mixed type-1 chain members.  This module builds
the reusable, chain-independent core:

  • padCode_append: padCode splits over list concatenation
    (padCode B W (xs ++ ys) = padCode B W xs + padCode B (W − xs.length) ys
     for xs.length ≤ W) — the digit-alignment fact behind every "the code grows
    when the initial list extends" statement;
  • padCode_lt_append: strict growth when a nonzero digit is inserted
    (padCode B W xs < padCode B W (xs ++ (c :: rest)) for xs.length < W and
     1 ≤ c) — i.e. initVal strictly increases when initList extends with a
    positive entry;
  • initList_eq_take: for a tuple whose entries before `k` are ≤ q and whose
    k-th entry exceeds q, the initial list is exactly the first `k` entries —
    hence for an in-domain-at-a input s: initList s = first (a−1) entries and
    initLen q s = a−1.

These are the tools `maink_mixed_type1_init_bound` (next) applies to the mixed
type-1 members (whose entries 0..a−2 coincide with s's and whose (a−1)-th entry
is the a-head < s⟨a−1⟩).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## padCode: append and growth -/

/-- ★ `padCode` splits over concatenation (the `xs` digits stay in place, the
`ys` digits are coded with the remaining width). -/
lemma padCode_append (B : ℕ) : ∀ (xs : List ℕ) (W : ℕ) (ys : List ℕ),
    xs.length ≤ W →
    padCode B W (xs ++ ys) = padCode B W xs + padCode B (W - xs.length) ys := by
  intro xs
  induction xs with
  | nil => intro W ys _; rw [List.nil_append, List.length_nil, Nat.sub_zero, padCode_nil, zero_add]
  | cons a t ih =>
      intro W ys hlen
      cases W with
      | zero => exact absurd hlen (by simp)
      | succ W =>
          have htlen : t.length ≤ W := by
            simpa using (Nat.succ_le_succ_iff.mp hlen)
          have hstep : padCode B (W + 1) ((a :: t) ++ ys) =
              a * B ^ W + padCode B W (t ++ ys) := rfl
          rw [hstep, ih W ys htlen]
          have hsub : (W + 1) - (a :: t).length = W - t.length := by
            simp [List.length_cons]
          rw [hsub]
          have hhead : padCode B (W + 1) (a :: t) = a * B ^ W + padCode B W t := rfl
          rw [hhead]
          omega

/-- ★ Strict growth of `padCode` when a positive digit follows the coded prefix
(`xs.length < W`): `padCode B W xs < padCode B W (xs ++ c :: rest)`. -/
lemma padCode_lt_append (B : ℕ) (hB : 1 ≤ B) (xs : List ℕ) (W : ℕ) (ys : List ℕ)
    (hlen : xs.length < W) (hne : ys ≠ []) (hys : ∀ v ∈ ys, 1 ≤ v) :
    padCode B W xs < padCode B W (xs ++ ys) := by
  have hle : xs.length ≤ W := le_of_lt hlen
  rw [padCode_append B xs W ys hle]
  have hpos : 0 < padCode B (W - xs.length) ys := by
    cases ys with
    | nil => exact absurd rfl hne
    | cons c rest =>
        have hc : 1 ≤ c := hys c (by simp)
        have hW : W - xs.length = (W - xs.length - 1) + 1 := by omega
        rw [hW]
        have hstep : padCode B ((W - xs.length - 1) + 1) (c :: rest) =
            c * B ^ (W - xs.length - 1) + padCode B (W - xs.length - 1) rest := rfl
        rw [hstep]
        have hpow : 1 ≤ B ^ (W - xs.length - 1) := Nat.one_le_pow _ B hB
        have : 1 ≤ c * B ^ (W - xs.length - 1) := by
          calc 1 = 1 * 1 := by rw [one_mul]
            _ ≤ c * B ^ (W - xs.length - 1) := Nat.mul_le_mul hc hpow
        omega
  omega

/-! ## initList for a tuple with a single "bad" entry -/

/-- `initListAux` of a prefix: if every entry of the (shorter) list is ≤ q, the
initial prefix of the concatenation is the whole shorter list — provided the
next entry exceeds q. -/
lemma initListAux_append_of_le (q : ℕ) : ∀ (l₁ : List ℕ), (∀ v ∈ l₁, v ≤ q) →
    ∀ (l₂ : List ℕ), (∃ c rest, l₂ = c :: rest ∧ q < c) →
    initListAux q (l₁ ++ l₂) = l₁ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro _ l₂ hl₂
      rcases hl₂ with ⟨c, rest, rfl, hgtc⟩
      rw [List.nil_append, initListAux_cons_gt q c rest hgtc]
  | cons a t ih =>
      intro hle l₂ hl₂
      have ha : a ≤ q := hle a (by simp)
      have htle : ∀ v ∈ t, v ≤ q := fun v hv => hle v (by simp [hv])
      rw [List.cons_append, initListAux_cons_le q a (t ++ l₂) ha]
      rw [ih htle l₂ hl₂]

/-- ★ For a tuple with all entries before `k` bounded by `q` and `k`-th entry
exceeding `q`, the initial list is exactly the first `k` entries. -/
lemma initList_eq_take (q : ℕ) {r : ℕ} (s : Fin r → ℕ+) (k : ℕ) (hk : k < r)
    (hle : ∀ x : ℕ, x < k → pad0 s x ≤ q)
    (hgt : q < (s ⟨k, hk⟩ : ℕ)) :
    initList q s = (valueList s).take k := by
  have hsplit : valueList s = (valueList s).take k ++ (valueList s).drop k :=
    (List.take_append_drop k (valueList s)).symm
  rw [initList]
  conv_lhs => rw [hsplit]
  refine initListAux_append_of_le q ((valueList s).take k) ?_ ((valueList s).drop k) ?_
  · intro v hv
    obtain ⟨i, hi, heq⟩ := List.mem_take_iff_getElem.mp hv
    have hik : i < k := lt_of_lt_of_le hi (Nat.min_le_left _ _)
    have hir : i < r := lt_of_lt_of_le hi (by simp [valueList_length])
    rw [← heq]
    have hget : (valueList s)[i] = (s ⟨i, hir⟩ : ℕ) := by
      simp [valueList]
    rw [hget]
    simpa [pad0_of_lt s hir] using hle i hik
  · have hlenv : k < (valueList s).length := by simpa [valueList_length] using hk
    rw [List.drop_eq_getElem_cons hlenv]
    have hget : (valueList s)[k] = (s ⟨k, hk⟩ : ℕ) := by
      simp [valueList]
    exact ⟨(valueList s)[k], (valueList s).drop (k + 1), rfl, by rw [hget]; exact hgt⟩

end ZagierHoffmanPositiveChar
