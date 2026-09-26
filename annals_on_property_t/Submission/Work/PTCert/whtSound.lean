import Mathlib
import Submission.Work.PTCert.GlueDefs

/-! Guidance from the project lead (the requester):

Context: `Submission/Work/PTCert/GlueDefs.lean` (definitions + Props; read it first) glues the
kernel-checked certificate data to the proved generic chain (`Chain.lean`, `Math.lean`,
`Interfaces.lean`; all their Props are already PROVED: avgPrinciple, labelPrinciple, gramSOS,
avgGram, avgMatInvariant, rowFormula, psdOfBlock, psdSignedPerm, ldlScaledPrinciple,
twistedFourierCriterion, residualAbsorption, letterAction, signCodes8, sigmaGroupFacts, modelSound,
permCheckKSound, ...). The design note is `NOTES_LEAD_glue.md` at the workspace root.
Do NOT change GlueDefs.lean. If the statement is false, `declare_false` with a concrete counterexample.
Put helper lemmas in your own file or under `Submission/Work/PTCert/<yourLemma>/`.
Prove the general statement by induction on d: for vs of length 2^d,
wht d vs = (List.range (2^d)).map (fun S => Σ_{ν < 2^d} χ(S, ν) * vs.getD ν 0) with χ(S,ν) the parity
sign of popcount(S &&& ν) (define a helper `chiP S ν := (-1)^(Nat.popcount-like parity)` or use
`chiS5` directly for d ≤ 5 and relate). Step: wht (d+1) vs = zipWith (+) a b ++ zipWith (-) a b with
a = wht d (take 2^d), b = wht d (drop 2^d); for S < 2^d: χ(S, 2^d + ν) = χ(S, ν); for S = 2^d + S':
χ(S, ν) = χ(S', ν) and χ(S, 2^d + ν) = -χ(S', ν) (ν < 2^d). `chiS5 S nu` uses bits 0..4 of S &&& nu.
-/

set_option autoImplicit false

namespace Work.PTCert

open Submission.PTCert

/-!
# `whtSound`: the Walsh–Hadamard transform computes the character sums (GL9)

`WhtSound` says that for `vs : List ℤ` of length `32`, the recursively defined
Walsh–Hadamard transform `wht 5 vs` equals, in row `S`, the signed sum
`∑_{sc < 32} chiS5 S sc * vs.getD sc 0`, where `chiS5 S sc = (-1)^{|S ∧ sc|}` is the parity
character on five bits.

The proof runs a general induction on the depth `d`, with a character `chiR d S ν` defined by the
*same* recursion as `wht` (split off the top bit), so that the four twist identities of the
induction step are immediate arithmetic.  At `d = 5` the two characters agree on the finitely many
relevant indices, which is checked by `decide` (32 × 32 cases).
-/

/-- The Walsh–Hadamard character of depth `d`, indexed by the row `S` and the column `ν`:
the sign of the parity of the number of positions `i < d` at which both `S` and `ν` have a `1`-bit.
The recursion splits off the **top** bit `d - 1`, matching the recursion of `wht`. -/
def chiR : ℕ → ℕ → ℕ → ℤ
  | 0, _, _ => 1
  | d + 1, S, ν =>
      chiR d (S % 2 ^ d) (ν % 2 ^ d) *
        (if (S / 2 ^ d) % 2 = 1 ∧ (ν / 2 ^ d) % 2 = 1 then -1 else 1)

section Arith

lemma add_pow_mod (d y : ℕ) (hy : y < 2 ^ d) : (2 ^ d + y) % 2 ^ d = y := by
  rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hy]

lemma add_pow_div (d y : ℕ) (hy : y < 2 ^ d) : (2 ^ d + y) / 2 ^ d = 1 := by
  exact Nat.div_eq_of_lt_le (k := 1) (n := 2 ^ d) (by omega) (by omega)

end Arith

/-! ## The four twist identities of the induction step -/

/-- Below the top bit, `chiR (d+1)` is `chiR d`. -/
lemma chiR_lt (d S ν : ℕ) (hS : S < 2 ^ d) (hν : ν < 2 ^ d) :
    chiR (d + 1) S ν = chiR d S ν := by
  simp only [chiR]
  rw [Nat.mod_eq_of_lt hS, Nat.mod_eq_of_lt hν, Nat.div_eq_of_lt hS]
  norm_num

/-- Raising the column index by `2 ^ d` (with the row index below `2 ^ d`) changes nothing. -/
lemma chiR_hi_lo (d S ν : ℕ) (hS : S < 2 ^ d) (hν : ν < 2 ^ d) :
    chiR (d + 1) S (2 ^ d + ν) = chiR d S ν := by
  simp only [chiR]
  rw [Nat.mod_eq_of_lt hS, add_pow_mod d ν hν, Nat.div_eq_of_lt hS, add_pow_div d ν hν]
  norm_num

/-- Raising the row index by `2 ^ d` (with the column index below `2 ^ d`) changes nothing. -/
lemma chiR_lo_hi (d S ν : ℕ) (hS : S < 2 ^ d) (hν : ν < 2 ^ d) :
    chiR (d + 1) (2 ^ d + S) ν = chiR d S ν := by
  simp only [chiR]
  rw [add_pow_mod d S hS, Nat.mod_eq_of_lt hν, add_pow_div d S hS, Nat.div_eq_of_lt hν]
  norm_num

/-- Raising **both** indices by `2 ^ d` flips the sign. -/
lemma chiR_hi_hi (d S ν : ℕ) (hS : S < 2 ^ d) (hν : ν < 2 ^ d) :
    chiR (d + 1) (2 ^ d + S) (2 ^ d + ν) = -chiR d S ν := by
  simp only [chiR]
  rw [add_pow_mod d S hS, add_pow_mod d ν hν, add_pow_div d S hS, add_pow_div d ν hν]
  norm_num

/-! ## Elementary list conversions -/

/-- `zipWith` of two mapped copies of one list is the pointwise combination. -/
lemma zipWith_map_map {α β γ δ : Type*} (f : β → γ → δ) (g : α → β) (h : α → γ) (l : List α) :
    List.zipWith f (l.map g) (l.map h) = l.map (fun x => f (g x) (h x)) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- `getD` into a `take` is `getD` into the original list. -/
lemma getD_take_eq {vs : List ℤ} {n ν : ℕ} (hν : ν < n) (hn : n ≤ vs.length) :
    (vs.take n).getD ν 0 = vs.getD ν 0 := by
  have h1 : ν < (vs.take n).length := by rw [List.length_take, Nat.min_eq_left hn]; exact hν
  have h2 : ν < vs.length := lt_of_lt_of_le hν hn
  rw [List.getD_eq_getElem _ _ h1, List.getElem_take, List.getD_eq_getElem _ _ h2]

/-- `getD` into a `drop` is `getD` into the original list at the shifted index. -/
lemma getD_drop_eq {vs : List ℤ} {n ν : ℕ} (h : n + ν < vs.length) :
    (vs.drop n).getD ν 0 = vs.getD (n + ν) 0 := by
  have h1 : ν < (vs.drop n).length := by rw [List.length_drop]; omega
  rw [List.getD_eq_getElem _ _ h1, List.getElem_drop, List.getD_eq_getElem _ _ h]

/-! ## The two halves of the induction step -/

/-- **Low half.** For a row index `S < 2^d`, the character sum of depth `d+1` splits into the two
character sums of depth `d` over the first and the second half of the columns, with a `+`. -/
lemma sum_split_lo (d S : ℕ) (hS : S < 2 ^ d) (vs : List ℤ) (hvs : vs.length = 2 ^ d + 2 ^ d) :
    (∑ ν ∈ Finset.range (2 ^ d + 2 ^ d), chiR (d + 1) S ν * vs.getD ν 0)
      = (∑ ν ∈ Finset.range (2 ^ d), chiR d S ν * (vs.take (2 ^ d)).getD ν 0)
      + (∑ ν ∈ Finset.range (2 ^ d), chiR d S ν * (vs.drop (2 ^ d)).getD ν 0) := by
  rw [Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun ν hν => ?_
    have hν' := Finset.mem_range.mp hν
    rw [chiR_lt d S ν hS hν', getD_take_eq hν' (by omega)]
  · refine Finset.sum_congr rfl fun ν hν => ?_
    have hν' := Finset.mem_range.mp hν
    rw [chiR_hi_lo d S ν hS hν', getD_drop_eq (by omega)]

/-- **High half.** For a row index `2^d + S` with `S < 2^d`, the character sum of depth `d+1`
splits into the two character sums of depth `d` over the first and the second half of the columns,
with a `-`. -/
lemma sum_split_hi (d S : ℕ) (hS : S < 2 ^ d) (vs : List ℤ) (hvs : vs.length = 2 ^ d + 2 ^ d) :
    (∑ ν ∈ Finset.range (2 ^ d + 2 ^ d), chiR (d + 1) (2 ^ d + S) ν * vs.getD ν 0)
      = (∑ ν ∈ Finset.range (2 ^ d), chiR d S ν * (vs.take (2 ^ d)).getD ν 0)
      - (∑ ν ∈ Finset.range (2 ^ d), chiR d S ν * (vs.drop (2 ^ d)).getD ν 0) := by
  rw [Finset.sum_range_add, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun ν hν => ?_
    have hν' := Finset.mem_range.mp hν
    rw [chiR_lo_hi d S ν hS hν', getD_take_eq hν' (by omega)]
  · refine Finset.sum_congr rfl fun ν hν => ?_
    have hν' := Finset.mem_range.mp hν
    rw [chiR_hi_hi d S ν hS hν', getD_drop_eq (by omega), neg_mul]

/-! ## The transform identity -/

/-- **`wht` computes the character sums.**  For a list of length `2^d` (`d ≤ 5`) the
Walsh–Hadamard transform `wht d` has, in row `S`, the signed sum `∑_{ν < 2^d} chiR d S ν · v_ν`. -/
theorem wht_eq_map : ∀ d : ℕ, d ≤ 5 → ∀ vs : List ℤ, vs.length = 2 ^ d →
    wht d vs = (List.range (2 ^ d)).map
      (fun S => ∑ ν ∈ Finset.range (2 ^ d), chiR d S ν * vs.getD ν 0) := by
  intro d
  induction d with
  | zero =>
      intro _ vs hvs
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hvs
      simp [wht, chiR]
  | succ d ih =>
      intro hd vs hvs
      have hp : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [pow_succ', two_mul]
      rw [hp] at hvs
      have htake : (vs.take (2 ^ d)).length = 2 ^ d := by
        rw [List.length_take, Nat.min_eq_left (by omega)]
      have hdrop : (vs.drop (2 ^ d)).length = 2 ^ d := by
        rw [List.length_drop]; omega
      have ha := ih (by omega) (vs.take (2 ^ d)) htake
      have hb := ih (by omega) (vs.drop (2 ^ d)) hdrop
      rw [hp]
      have step : wht (d + 1) vs =
          List.zipWith (· + ·)
            ((List.range (2 ^ d)).map (fun S =>
              ∑ ν ∈ Finset.range (2 ^ d), chiR d S ν * (vs.take (2 ^ d)).getD ν 0))
            ((List.range (2 ^ d)).map (fun S =>
              ∑ ν ∈ Finset.range (2 ^ d), chiR d S ν * (vs.drop (2 ^ d)).getD ν 0))
        ++ List.zipWith (· - ·)
            ((List.range (2 ^ d)).map (fun S =>
              ∑ ν ∈ Finset.range (2 ^ d), chiR d S ν * (vs.take (2 ^ d)).getD ν 0))
            ((List.range (2 ^ d)).map (fun S =>
              ∑ ν ∈ Finset.range (2 ^ d), chiR d S ν * (vs.drop (2 ^ d)).getD ν 0)) := by
        simp only [wht]
        rw [ha, hb]
      rw [step, zipWith_map_map, zipWith_map_map, List.range_add, List.map_append, List.map_map]
      simp only [Function.comp_def]
      congr 1
      · exact List.map_congr_left fun S hS => (sum_split_lo d S (List.mem_range.mp hS) vs hvs).symm
      · exact List.map_congr_left fun S hS => (sum_split_hi d S (List.mem_range.mp hS) vs hvs).symm

/-! ## Agreement of the two characters at depth `5` -/

/-- At depth `5` (i.e. on `32` columns) the recursive character `chiR 5` agrees with the
kernel-checked five-bit character `chiS5`.  A finite check over the `32 × 32` index pairs. -/
lemma chiR5_eq_chiS5 : ∀ S ∈ Finset.range 32, ∀ ν ∈ Finset.range 32, chiR 5 S ν = chiS5 S ν := by
  decide

/-- Agreement of the characters, in the form used below. -/
lemma chiR_eq_chiS5 (S ν : ℕ) (hS : S < 32) (hν : ν < 32) : chiR 5 S ν = chiS5 S ν :=
  chiR5_eq_chiS5 S (Finset.mem_range.mpr hS) ν (Finset.mem_range.mpr hν)

/-- **(GL9) Walsh–Hadamard transform.**  For `vs` of length `32`, the transform `wht 5 vs` has, in
row `S`, the signed sum `∑_{sc < 32} chiS5 S sc · vs.getD sc 0` (`chiS5 S sc = (-1)^{|S ∧ sc|}`). -/
theorem whtSound : WhtSound := by
  intro vs hvs
  have h := wht_eq_map 5 (le_refl 5) vs hvs
  simp only [Nat.reducePow] at h
  rw [h]
  refine List.map_congr_left fun S hS => ?_
  refine Finset.sum_congr rfl fun ν hν => ?_
  rw [chiR_eq_chiS5 S ν (List.mem_range.mp hS) (List.mem_range.mp hν)]

end Work.PTCert
