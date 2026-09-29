import Mathlib
import Submission.Work.Resample.sliceB1defs
import Submission.Work.Resample.egSigTKey

/-!
# The key formula of `P̃_t^{-1}` (`Work.Resample.buLamWord`)

This module fixes the integer formula by which the word `Work.Resample.buLamWord` computes the
destination keys `egLam s t i` of the transposed permutation `P̃_t^{-1}` (paper Prop. 4.7(ii)).

## The mathematics

Let `s < t` be coprime and let `m = σ_t^{-1}(i) ∈ [0,t)` be the pre-image of `i` under the index
map `σ_t k = (-s·k) mod t` of `P̃_t`.  The key of `i` is

* `ℓ = ⌊(2 s m + t)/(2 t)⌋` (the rounding `[s m / t]`) if `m` is a value of `ρ ℓ = [t ℓ / s]`
  for some `ℓ < s` — i.e. if `2 s m - s ≤ 2 t ℓ < 2 s m + s` — and
* `s + i` otherwise (the elements that are *not* selected by the fused `C̃ ∘ P̃_t` step sort
  after the `s` selected ones).

`lamKey s t m i` below is this value; `lamL` is `ℓ`, `lamD` the discrepancy `2(tℓ - sm)` and
`lamF` the `{0,1}`-valued flag which is `1` exactly on the selected indices.  The word computes
`lamKey` from `m`; the pre-image `m = lamMu s t i` of `i` is produced (positionally, by
`LayoutLib.sortByKey`) from the list `lamRecs s t` of pairs `(σ_t k, k)`.

## Contents

* `lamL`, `lamD`, `lamOk`, `lamF`, `lamKey` — the formula;
* `lamMu` — the inverse index map `σ_t^{-1}` on `[0,t)`, with `lamMu_spec`;
* `lamRec`, `lamRecs` — the list of pairs `(σ_t k, k)`, `k < t`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-! ## The formula -/

/-- The candidate source index `ℓ = ⌊(2·s·m + t)/(2·t)⌋`, the integer nearest to `s·m/t`. -/
def lamL (s t m : ℤ) : ℤ := Int.fdiv (2 * (s * m) + t) (2 * t)

/-- The discrepancy `2·(t·ℓ - s·m)` of the candidate `ℓ = lamL s t m`. -/
def lamD (s t m : ℤ) : ℤ := 2 * (t * lamL s t m - s * m)

/-- The candidate `lamL s t m` is a genuine pre-image of `m`: `γ(ℓ) = m` for `γ ℓ = [tℓ/s]`. -/
def lamOk (s t m : ℤ) : Prop :=
  -s ≤ lamD s t m ∧ lamD s t m < s ∧ lamL s t m < s

/-- The selection flag: `1` if `m` lies in the image of `γ ℓ = [tℓ/s]` on `ℓ < s`, else `0`. -/
def lamF (s t m : ℤ) : ℤ :=
  (if -s - 1 < lamD s t m then 1 else 0) * (if lamD s t m < s then 1 else 0) *
    (if lamL s t m < s then 1 else 0)

/-- The destination key of the index `i` whose `σ_t`-pre-image is `m`. -/
def lamKey (s t m i : ℤ) : ℤ :=
  lamF s t m * lamL s t m + (1 - lamF s t m) * (s + i)

/-- A product of three `{0,1}`-flags is `1` only if all three flags hold. -/
theorem mul_flag_eq_one {P Q R : Prop} [Decidable P] [Decidable Q] [Decidable R] :
    (if P then (1 : ℤ) else 0) * (if Q then (1 : ℤ) else 0) * (if R then (1 : ℤ) else 0) = 1 ↔
      P ∧ Q ∧ R := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;>
    simp [hP, hQ, hR]

theorem lamF_eq_one_iff {s t m : ℤ} (hs : 1 ≤ s) : lamF s t m = 1 ↔ lamOk s t m := by
  show lamF s t m = 1 ↔ (-s ≤ lamD s t m ∧ lamD s t m < s ∧ lamL s t m < s)
  rw [lamF, mul_flag_eq_one]
  exact ⟨fun h => ⟨by omega, h.2.1, h.2.2⟩, fun h => ⟨by omega, h.2.1, h.2.2⟩⟩

theorem lamF_nonneg (s t m : ℤ) : 0 ≤ lamF s t m := by
  unfold lamF
  have h1 : 0 ≤ (if -s - 1 < lamD s t m then (1 : ℤ) else 0) := by split <;> norm_num
  have h2 : 0 ≤ (if lamD s t m < s then (1 : ℤ) else 0) := by split <;> norm_num
  have h3 : 0 ≤ (if lamL s t m < s then (1 : ℤ) else 0) := by split <;> norm_num
  exact mul_nonneg (mul_nonneg h1 h2) h3

theorem lamF_le_one (s t m : ℤ) : lamF s t m ≤ 1 := by
  unfold lamF
  have h1 : (if -s - 1 < lamD s t m then (1 : ℤ) else 0) ≤ 1 := by split <;> norm_num
  have h2 : (if lamD s t m < s then (1 : ℤ) else 0) ≤ 1 := by split <;> norm_num
  have h3 : (if lamL s t m < s then (1 : ℤ) else 0) ≤ 1 := by split <;> norm_num
  have g1 : 0 ≤ (if -s - 1 < lamD s t m then (1 : ℤ) else 0) := by split <;> norm_num
  have g2 : 0 ≤ (if lamD s t m < s then (1 : ℤ) else 0) := by split <;> norm_num
  have g3 : 0 ≤ (if lamL s t m < s then (1 : ℤ) else 0) := by split <;> norm_num
  have hab : (if -s - 1 < lamD s t m then (1 : ℤ) else 0) *
      (if lamD s t m < s then (1 : ℤ) else 0) ≤ 1 := by nlinarith
  nlinarith [mul_nonneg g1 g2, mul_le_mul_of_nonneg_right hab g3, g3, h3]

/-- Off the image of `γ` the key is the fallback `s + i`. -/
theorem lamKey_of_not {s t m i : ℤ} (hs : 1 ≤ s) (h : ¬ lamOk s t m) : lamKey s t m i = s + i := by
  have hf : lamF s t m = 0 := by
    rcases eq_or_ne (lamF s t m) 0 with h0 | h0
    · exact h0
    · exact absurd ((lamF_eq_one_iff hs).mp (by
        have h1 := lamF_le_one s t m
        have h2 := lamF_nonneg s t m
        omega)) h
  rw [lamKey, hf]
  ring

/-- On the image of `γ` the key is the candidate index `lamL`. -/
theorem lamKey_of_ok {s t m i : ℤ} (hs : 1 ≤ s) (h : lamOk s t m) : lamKey s t m i = lamL s t m := by
  rw [lamKey, (lamF_eq_one_iff hs).mpr h]
  ring

/-! ## The inverse index map `σ_t^{-1}` on `[0,t)` -/

/-- `σ_t` maps `[0,t)` into `[0,t)`. -/
theorem egSigT_lt (s t k : ℕ) (ht : 0 < t) : egSigT s t k < t := by
  simp only [egSigT]
  exact Nat.mod_lt _ ht

/-- `σ_t` is surjective on `[0,t)` when `gcd s t = 1`. -/
theorem egSigT_surj (s t : ℕ) (hcop : Nat.Coprime s t) (ht : 0 < t) (i : ℕ) (hi : i < t) :
    ∃ k, k < t ∧ egSigT s t k = i := by
  have hinj : Function.Injective
      (fun k : Fin t => (⟨egSigT s t (k : ℕ), egSigT_lt s t k ht⟩ : Fin t)) := by
    intro a b hab
    exact Fin.ext ((egSigTKey s t hcop ht).2 a b a.isLt b.isLt (congrArg Fin.val hab))
  have hsurj : Function.Surjective
      (fun k : Fin t => (⟨egSigT s t (k : ℕ), egSigT_lt s t k ht⟩ : Fin t)) :=
    (Finite.injective_iff_surjective).mp hinj
  obtain ⟨k, hk⟩ := hsurj ⟨i, hi⟩
  exact ⟨k, k.isLt, by simpa using congrArg Fin.val hk⟩

/-- The pre-image `σ_t^{-1}(i)` of `i ∈ [0,t)` (and `0` outside that range). -/
noncomputable def lamMu (s t : ℕ) (i : ℕ) : ℕ :=
  if h : ∃ k, k < t ∧ egSigT s t k = i then Classical.choose h else 0

theorem lamMu_lt (s t : ℕ) (hcop : Nat.Coprime s t) (ht : 0 < t) (i : ℕ) (hi : i < t) :
    lamMu s t i < t := by
  have h : ∃ k, k < t ∧ egSigT s t k = i := egSigT_surj s t hcop ht i hi
  rw [lamMu, dif_pos h]
  exact (Classical.choose_spec h).1

theorem lamMu_spec (s t : ℕ) (hcop : Nat.Coprime s t) (ht : 0 < t) (i : ℕ) (hi : i < t) :
    egSigT s t (lamMu s t i) = i := by
  have h : ∃ k, k < t ∧ egSigT s t k = i := egSigT_surj s t hcop ht i hi
  rw [lamMu, dif_pos h]
  exact (Classical.choose_spec h).2

/-- `lamMu` is a left inverse of `σ_t` on `[0,t)`. -/
theorem lamMu_sigT (s t : ℕ) (hcop : Nat.Coprime s t) (ht : 0 < t) (k : ℕ) (hk : k < t) :
    lamMu s t (egSigT s t k) = k := by
  have h1 : lamMu s t (egSigT s t k) < t := lamMu_lt s t hcop ht _ (egSigT_lt s t k ht)
  have h2 : egSigT s t (lamMu s t (egSigT s t k)) = egSigT s t k :=
    lamMu_spec s t hcop ht _ (egSigT_lt s t k ht)
  exact (egSigTKey s t hcop ht).2 _ _ h1 hk h2

/-! ## The list of pairs `(σ_t k, k)` -/

/-- The record `(σ_t k, k)` read by the sorting stage. -/
def lamRec (s t k : ℕ) : Val := Val.cons (.int ((egSigT s t k : ℕ) : ℤ)) (.int (k : ℤ))

/-- The list of records `(σ_t k, k)` for `k < t`. -/
def lamRecs (s t : ℕ) : List Val := (List.range t).map (lamRec s t)

theorem lamRecs_length (s t : ℕ) : (lamRecs s t).length = t := by
  simp [lamRecs]

theorem pairKey_lamRec (s t k : ℕ) : pairKey (lamRec s t k) = ((egSigT s t k : ℕ) : ℤ) := rfl

theorem lamRecs_key (s t : ℕ) :
    (lamRecs s t).map pairKey = (List.range t).map (fun k => ((egSigT s t k : ℕ) : ℤ)) := by
  simp only [lamRecs, List.map_map]
  exact List.map_congr_left (fun k _ => pairKey_lamRec s t k)

theorem lamRec_key_lt {s t : ℕ} {x : Val} (hx : x ∈ lamRecs s t) :
    ∃ (k : ℕ) (v : Val), x = .cons (.int k) v := by
  rw [lamRecs, List.mem_map] at hx
  obtain ⟨k, hk, hkx⟩ := hx
  exact ⟨egSigT s t k, .int (k : ℤ), hkx ▸ rfl⟩

end Work.Resample
