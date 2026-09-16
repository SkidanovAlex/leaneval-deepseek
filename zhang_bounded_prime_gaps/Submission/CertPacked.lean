import Mathlib
import Submission.CertFactor
import Submission.CertStates

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

open scoped BigOperators
open Finset

/-!
# The packed representation of the certificate's x-side polynomial

The factorisation `Ssum β β' k = mc k (mult β') * xslots (slotList k (mult β')) (mult β)`
(`Submission/CertFactor.lean`) reduces the certificate's arithmetic to evaluating
`xslots (slotList 50 n) m` at the 272 states `m` of weighted degree `≤ 24`, for each of the 272
signatures `n`.

This module sets up the **packed representation** used to compute those 272 coefficients per
signature with O(1) kernel reduction steps per arithmetic operation: the coefficient function
`F : MV → ℕ` is stored as a `List ℕ` of 13 *class words*, one per weighted-degree class, where
class `j`'s word is the base-`2^B` number

  `Σ_{m ∈ classJ j} F m * 2^(B * muVal m)`

(absolute `muVal` indexing, so that `x_v` acts on every class by the SAME shift `B * mu v`).
`mulA`/`mulH` on the coefficient function then correspond to the shift-adds

  `mulA : W_i ↦ W_i + Σ_{v} [v+1 ≤ i] (2(v+1))! · (W_{i-v-1} <<< (B·mu v))`,
  `mulH w : W_i ↦ (2(w+1))! · W_i + Σ_v [v+1 ≤ i] (2(v+1)+2(w+1))! · (W_{i-v-1} <<< (B·mu v))`,

and the correctness (`packedMulA (pack F) = pack (mulA F)`) rests on
* the *no-carry* condition `∀ m, F m < 2^B` (`xslots_le_cap` below gives a provable bound), and
* the state-space lemmas of `Submission/CertStates.lean` (closure + `no_interference`).

This file currently contains the *bound*; the operations and their correctness proof are the
next step (see the roadmap, SESSION 46 §5).
-/

namespace Commons.NumberTheory.MaynardSieve


/-- Block size (bits) of the packed representation.  Large enough that the crude bound
`xslots L m ≤ ∏_{s ∈ L} cap s` is `< 2^B` for every slot list of length `≤ 50` that occurs
(`capA^50` and, sharper, `capA^38 * capH^12` are both `< 2^5664`). -/
def BB : ℕ := 5664

/-- The "capacity" of a slot: the sum of its coefficients (`1 + Σ_v (2(v+1))!` for an `A`-slot,
`(2(w+1))! + Σ_v (2(v+1)+2(w+1))!` for an `H w`-slot). -/
def cap : CertSlot → ℕ
  | CertSlot.A => 1 + ∑ v : Fin 12, Nat.factorial (2 * ((v : ℕ) + 1))
  | CertSlot.H w => Nat.factorial (2 * ((w : ℕ) + 1))
      + ∑ v : Fin 12, Nat.factorial (2 * ((v : ℕ) + 1) + 2 * ((w : ℕ) + 1))

theorem cap_A : cap CertSlot.A = 1 + ∑ v : Fin 12, Nat.factorial (2 * ((v : ℕ) + 1)) := rfl

theorem cap_H (w : Fin 12) : cap (CertSlot.H w)
    = Nat.factorial (2 * ((w : ℕ) + 1))
      + ∑ v : Fin 12, Nat.factorial (2 * ((v : ℕ) + 1) + 2 * ((w : ℕ) + 1)) := rfl

/-- **The coefficient bound.**  `xslots L m` is at most the product of the capacities of the slots
in `L` — the only estimate needed for the packed DP's no-carry condition. -/
theorem xslots_le_cap (L : List CertSlot) (m : MV) : xslots L m ≤ (L.map cap).prod := by
  induction L generalizing m with
  | nil =>
      simp only [xslots_nil, List.map_nil, List.prod_nil]
      split_ifs <;> omega
  | cons s t ih =>
      cases s with
      | A =>
          rw [xslots_cons_A_eq]
          have h1 : mulA (xslots t) m
              ≤ (1 + ∑ v : Fin 12, Nat.factorial (2 * ((v : ℕ) + 1))) * (t.map cap).prod := by
            simp only [mulA]
            have h2 : ∑ v : Fin 12,
                (if 1 ≤ m v then Nat.factorial (2 * ((v : ℕ) + 1)) * xslots t (m - evec v)
                  else 0)
                ≤ (∑ v : Fin 12, Nat.factorial (2 * ((v : ℕ) + 1))) * (t.map cap).prod := by
              rw [Finset.sum_mul]
              refine Finset.sum_le_sum (fun v _ => ?_)
              by_cases h : 1 ≤ m v
              · rw [if_pos h]
                exact Nat.mul_le_mul_left _ (ih (m - evec v))
              · rw [if_neg h]; exact Nat.zero_le _
            calc xslots t m + ∑ v : Fin 12, (if 1 ≤ m v then
                    Nat.factorial (2 * ((v : ℕ) + 1)) * xslots t (m - evec v) else 0)
                ≤ (t.map cap).prod
                  + (∑ v : Fin 12, Nat.factorial (2 * ((v : ℕ) + 1))) * (t.map cap).prod :=
                  Nat.add_le_add (ih m) h2
              _ = (1 + ∑ v : Fin 12, Nat.factorial (2 * ((v : ℕ) + 1))) * (t.map cap).prod := by
                  ring
          rw [List.map_cons, List.prod_cons, cap_A]
          exact h1
      | H w =>
          rw [xslots_cons_H_eq]
          have h1 : mulH w (xslots t) m
              ≤ (Nat.factorial (2 * ((w : ℕ) + 1))
                  + ∑ v : Fin 12, Nat.factorial (2 * ((v : ℕ) + 1) + 2 * ((w : ℕ) + 1)))
                * (t.map cap).prod := by
            simp only [mulH]
            have h2 : ∑ v : Fin 12,
                (if 1 ≤ m v then
                  Nat.factorial (2 * ((v : ℕ) + 1) + 2 * ((w : ℕ) + 1)) * xslots t (m - evec v)
                  else 0)
                ≤ (∑ v : Fin 12, Nat.factorial (2 * ((v : ℕ) + 1) + 2 * ((w : ℕ) + 1)))
                  * (t.map cap).prod := by
              rw [Finset.sum_mul]
              refine Finset.sum_le_sum (fun v _ => ?_)
              by_cases h : 1 ≤ m v
              · rw [if_pos h]
                exact Nat.mul_le_mul_left _ (ih (m - evec v))
              · rw [if_neg h]; exact Nat.zero_le _
            calc Nat.factorial (2 * ((w : ℕ) + 1)) * xslots t m
                  + ∑ v : Fin 12, (if 1 ≤ m v then
                      Nat.factorial (2 * ((v : ℕ) + 1) + 2 * ((w : ℕ) + 1))
                        * xslots t (m - evec v) else 0)
                ≤ Nat.factorial (2 * ((w : ℕ) + 1)) * (t.map cap).prod
                  + (∑ v : Fin 12,
                      Nat.factorial (2 * ((v : ℕ) + 1) + 2 * ((w : ℕ) + 1)))
                    * (t.map cap).prod :=
                  Nat.add_le_add (Nat.mul_le_mul_left _ (ih m)) h2
              _ = (Nat.factorial (2 * ((w : ℕ) + 1))
                    + ∑ v : Fin 12, Nat.factorial (2 * ((v : ℕ) + 1) + 2 * ((w : ℕ) + 1)))
                  * (t.map cap).prod := by
                  ring
          rw [List.map_cons, List.prod_cons, cap_H]
          exact h1

/-- The largest capacity of an `H`-slot (attained at `w = 11`, i.e. the part `24`). -/
def capHmax : ℕ := Nat.factorial 24 + ∑ v : Fin 12, Nat.factorial (2 * ((v : ℕ) + 1) + 24)

theorem capH_le (w : Fin 12) : cap (CertSlot.H w) ≤ capHmax := by
  rw [cap_H, capHmax]
  have hw : 2 * ((w : ℕ) + 1) ≤ 24 := by
    have := w.isLt; omega
  refine Nat.add_le_add (Nat.factorial_le hw) (Finset.sum_le_sum (fun v _ => ?_))
  exact Nat.factorial_le (by omega)

/-- **The block size is large enough.**  For every slot list of length `≤ 50` arising in the
certificate computation (`A^a` followed by `≤ 12` `H`-slots) and every state `m`, the coefficient
`xslots L m` is `< 2^BB`. -/
theorem capA_pow_lt : cap CertSlot.A ^ 50 < 2 ^ BB := by decide

theorem capA_capH_lt : cap CertSlot.A ^ 38 * capHmax ^ 12 < 2 ^ BB := by decide

/-! ## The packed operations -/

/-- The class-`i` word of a coefficient function `F`: the sum `Σ_{m ∈ classJ i} F m · 2^(BB·muVal m)`
(absolute `muVal` positions; positions with no state stay `0`). -/
def classWord (F : MV → ℕ) (i : ℕ) : ℕ :=
  ((classJ i).map (fun m => F m * 2 ^ (BB * muVal m))).sum

/-- The packed word of a coefficient function. -/
def pack (F : MV → ℕ) : List ℕ := List.ofFn (fun i : Fin 13 => classWord F (i : ℕ))

/-- The coefficient read off at a state. -/
def unpack (W : List ℕ) (m : MV) : ℕ :=
  (W.getD (degV m / 2) 0 >>> (BB * muVal m)) % 2 ^ BB

/-- The packed word of the zero polynomial (the constant `1`). -/
def W0 : List ℕ := 1 :: List.replicate 12 0

/-- Packed multiplication by `A = 1 + Σ_v (2(v+1))! x_v`. -/
def packedMulA (W : List ℕ) : List ℕ :=
  List.ofFn (fun i : Fin 13 =>
    W.getD (i : ℕ) 0
      + ∑ v : Fin 12, if (v : ℕ) + 1 ≤ (i : ℕ) then
          Nat.factorial (2 * ((v : ℕ) + 1))
            * (W.getD ((i : ℕ) - (v : ℕ) - 1) 0 <<< (BB * mu v))
        else 0)

/-- Packed multiplication by `h_w = (2(w+1))! + Σ_v (2(v+1)+2(w+1))! x_v`. -/
def packedMulH (w : Fin 12) (W : List ℕ) : List ℕ :=
  List.ofFn (fun i : Fin 13 =>
    Nat.factorial (2 * ((w : ℕ) + 1)) * W.getD (i : ℕ) 0
      + ∑ v : Fin 12, if (v : ℕ) + 1 ≤ (i : ℕ) then
          Nat.factorial (2 * ((v : ℕ) + 1) + 2 * ((w : ℕ) + 1))
            * (W.getD ((i : ℕ) - (v : ℕ) - 1) 0 <<< (BB * mu v))
        else 0)

/-- `packedPowA k` is the packed word of `A^k`. -/
def packedPowA (k : ℕ) : List ℕ := (packedMulA^[k]) W0

/-- The packed word of `xslots (slotList 50 n)`, i.e. of `A^(50-|n|)·∏_w h_w^(n_w)`. -/
def packedRow (n : MV) : List ℕ :=
  (List.finRange 12).foldl (fun W w => (packedMulH w)^[n w] W)
    (packedPowA (50 - ∑ w : Fin 12, n w))

/-- The 272-element class word list of the certificate's computation (indexed by the enumeration
of `certStates`), i.e. the value `xslots (slotList 50 (mult β')) (mult β)` for every pair. -/
def packedAll : List (List ℕ) := certStates.map packedRow

/-- The full table `Ssum β β' 50 = mc 50 (mult β') * xslots (slotList 50 (mult β')) (mult β)`. -/
def ssumTable : List (List ℕ) :=
  certStates.map (fun n => (certStates.map (fun m =>
    mc 50 n * unpack (packedRow n) m)))

end Commons.NumberTheory.MaynardSieve
