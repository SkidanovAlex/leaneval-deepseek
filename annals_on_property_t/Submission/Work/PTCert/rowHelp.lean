import Mathlib
import Submission.Work.PTCert.Checks.SharedAll

/-!
# `PTCert` — shared helper lemmas for the `RowSem` proofs

Generic conversions from the kernel-`Bool` combinators (`allL`, `allR`, `allIdx`, `eqL`, `countL`)
into `∀`/`∧`/`=`, plus a few small data facts about the row codes `x0c r`, the rep information
`rinfo`, the chunk decomposition of `eAll` and the list `pcL`.

Nothing here evaluates a big data structure: the `decide +kernel` proofs only touch the `18` row
codes, the `611` rep-info entries, `pcL` and the chunk concatenation `eC0 ++ … ++ eC7`.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D Submission.PTCert.C

/-! ## The `Bool` combinators as `Prop`s -/

/-- `allL l p` says `p` holds on every element of `l`. -/
theorem allL_eq_true (l : List ℕ) (p : ℕ → Bool) :
    allL l p = true ↔ ∀ a ∈ l, p a = true := by
  induction l with
  | nil => simp [allL]
  | cons a t ih =>
      rw [show allL (a :: t) p = (p a && allL t p) from rfl, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨ha, ht⟩ b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact ht b hb
      · intro h
        exact ⟨h a (List.mem_cons_self ..), fun b hb => h b (List.mem_cons_of_mem a hb)⟩

/-- `allR n p` says `p` holds on every `k < n`. -/
theorem allR_eq_true (n : ℕ) (p : ℕ → Bool) :
    allR n p = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => simp [allR]
  | succ n ih =>
      rw [show allR (n + 1) p = (p n && allR n p) from rfl, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨hn, ht⟩ k hk
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
        · exact ht k hk
        · exact hn
      · intro h
        exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

/-- `allIdx l p i0` says `p (i0 + i) (l[i])` holds for every position `i`. -/
theorem allIdx_eq_true (l : List ℕ) (p : ℕ → ℕ → Bool) (i0 : ℕ) :
    allIdx l p i0 = true ↔ ∀ i < l.length, p (i0 + i) (l.getD i 0) = true := by
  induction l generalizing i0 with
  | nil => simp [allIdx]
  | cons a t ih =>
      rw [show allIdx (a :: t) p i0 = (p i0 a && allIdx t p (i0 + 1)) from rfl, Bool.and_eq_true,
        ih (i0 + 1)]
      constructor
      · rintro ⟨ha, ht⟩ i hi
        cases i with
        | zero => simpa using ha
        | succ j =>
            have hj : j < t.length := by simpa using hi
            have h := ht j hj
            rw [List.getD_cons_succ]
            rw [show i0 + (j + 1) = i0 + 1 + j from by omega]
            exact h
      · intro h
        refine ⟨?_, fun j hj => ?_⟩
        · simpa using h 0 (by simp)
        · have h' := h (j + 1) (by simpa using hj)
          rw [List.getD_cons_succ] at h'
          rw [show i0 + (j + 1) = i0 + 1 + j from by omega] at h'
          exact h'

/-- The kernel equality test on lists is equality. -/
theorem eqL_eq_true (l m : List ℕ) : eqL l m = true ↔ l = m := by
  induction l generalizing m with
  | nil => cases m <;> simp [eqL]
  | cons a t ih =>
      cases m with
      | nil => simp [eqL]
      | cons b u =>
          rw [show eqL (a :: t) (b :: u) = (Nat.beq a b && eqL t u) from rfl, Bool.and_eq_true,
            Nat.beq_eq, ih u]
          constructor
          · rintro ⟨h1, h2⟩; rw [h1, h2]
          · intro h; injection h with h1 h2; exact ⟨h1, h2⟩

/-- The kernel counter is the length of the filtered list. -/
theorem countL_eq_filter_length (l : List ℕ) (p : ℕ → Bool) :
    countL l p = (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [show countL (a :: t) p = (bif p a then 1 else 0) + countL t p from rfl, ih]
      cases hp : p a with
      | false =>
          rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.false_ne_true),
            show (bif (false : Bool) then 1 else 0) = 0 from rfl]
          simp
      | true =>
          rw [List.filter_cons_of_pos (by rw [hp]),
            show (bif (true : Bool) then 1 else 0) = 1 from rfl]
          rw [List.length_cons]; omega

/-- Two `Bool` predicates that agree on a list filter it identically. -/
theorem filter_congr' {l : List ℕ} {p q : ℕ → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.filter p = l.filter q :=
  List.filter_congr h

/-! ## The row codes -/

/-- The row codes `x0c r = cG rowT r` for `r < 18`. -/
def x0cL : List ℕ := [0, 1, 129, 131, 132, 133, 135, 145, 146, 147, 148, 149, 151, 161, 162, 165, 166, 169]

theorem x0c_ok : allR 18 (fun r => Nat.beq (cG rowT r) (x0cL.getD r 0)) = true := by
  decide +kernel

/-- The value of the row code `x0c r`. -/
theorem x0c_val (r : ℕ) (hr : r < 18) : cG rowT r = x0cL.getD r 0 :=
  Nat.beq_eq.mp ((allR_eq_true 18 _).mp x0c_ok r hr)

/-- The listing of the row codes. -/
theorem x0c_list_eq : (List.range 18).map (fun r => cG rowT r) = x0cL := by
  decide +kernel

/-! ## Small data facts -/

theorem validPC_five_zero : validPC 5 0 = false := by decide +kernel

theorem x0c_zero : cG rowT 0 = 0 := by
  have h := x0c_val 0 (by norm_num)
  rw [h]; rfl

/-- The rep-information `rinfo t = cG repInfoT t` is the row number `128 · r + π` with `r < 18`. -/
theorem rinfo_div (t : ℕ) (ht : t < 611) : cG repInfoT t / 128 < 18 := by
  have h : allR 611 (fun t => Nat.blt (cG repInfoT t / 128) 18) = true := by decide +kernel
  exact Nat.blt_eq.mp ((allR_eq_true 611 _).mp h t ht)

theorem rinfo_mod (t : ℕ) (ht : t < 611) : cG repInfoT t % 128 < 120 := by
  have h : allR 611 (fun t => Nat.blt (cG repInfoT t % 128) 120) = true := by decide +kernel
  exact Nat.blt_eq.mp ((allR_eq_true 611 _).mp h t ht)

/-- `eAll` is the concatenation of the eight emitted chunks. -/
theorem eAll_chunks : eAll = eC0 ++ eC1 ++ eC2 ++ eC3 ++ eC4 ++ eC5 ++ eC6 ++ eC7 := by
  decide +kernel

/-- The permutation-code list of the checks is `allPCk`. -/
theorem pcL_allPCk : pcL = allPCk := (eqL_eq_true allPCk pcL).mp C.pc_ok

end Work.PTCert
