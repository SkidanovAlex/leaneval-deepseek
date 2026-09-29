import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Fx.FxCommon
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auConvDefs

/-!
# Shared data for `Work.Resample.auChunkWord` (the `q` word of paper Lemma 4.9)

One chunk `cons (ofList WTS) (ofList WIN)` with the parameter block `auPvals p α s t = [off, cop, p, table]`
below it must be replaced by `cfxVal (tdiv (Σ_i W i * (z i).1) 2^p, tdiv (Σ_i W i * (z i).2) 2^p)`.

The cost bound `K*(L+1)*(Cm (K*p) + p + 1)` must hold for **every** length `L`, while the recursive
primitive `self` (`MulBelow`) may cost as little as `O(1)`.  A single `O(p)`-bit accumulator is
therefore impossible: after `L` rounds the exact sum has `2p + log L` bits, and each `IntLib.add`
charges the *sizes of its arguments*, so a plain accumulator costs `Ω(log L)` per round.  The word
therefore accumulates

* the low parts `lo_r, lo_i ∈ [0, M)` of the two sums, with `M = 2^Q`, `Q = 2p + 1`, and
* **one record per round** — a small value listing the carries `z ∈ {0,1}` of the round —

and only at the very end converts the records into the two carry *counts* (a `foldList` per count
building a unary chain `ofList (replicate c (.int 1))`, whose value `2^c - 1` is turned back into
`c` by `IntLib.evalPoly` (base `1`) followed by `IntLib.clog2`).  The number `L` of rounds is the
length of the record chain, obtained by `Work.Layout.lengthWord`.

## Numerical invariants

Round `j` produces the summands `A_j = W_j * x_j + 2^{2p}`, `B_j = W_j * y_j + 2^{2p}` (the shift
makes them lie in `[0, M)`), the carries `zr_j = (lo_r + A_j) / M ∈ {0,1}` and the new low parts
`lo_r' = (lo_r + A_j) - zr_j * M ∈ [0, M)`.  Then

`lo_r + M * Σ_{j<n} zr_j = Σ_{j<n} A_j`,  so  `Σ_j W_j x_j = lo_r + 2^{2p} * (2 * Σ_j zr_j - L)`.

## The record

`awRec zr zi = ofList ((if zr = 1 then [.int 1] else []) ++ (if zi = 1 then [.int 2] else []))`:
marker `1` iff `zr = 1`, marker `2` iff `zi = 1`.  The chain is `ofList (awRecs zr zi L)` with the
*most recent* record first; its length is `L`, the number of markers `.int 1` is `Σ_j zr_j`, and the
number of markers `.int 2` is `Σ_j zi_j`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## The numerical data -/

/-- The modulus exponent `Q = 2p + 1`. -/
def awQ (p : ℕ) : ℕ := 2 * p + 1

/-- The shift `2^{2p}` applied to the products. -/
def awSh (p : ℕ) : ℤ := (2 : ℤ) ^ (2 * p)

/-- The modulus `M = 2^Q`. -/
def awMod (p : ℕ) : ℤ := (2 : ℤ) ^ awQ p

/-- The carry of one component in one round: `(lo + A) / M`. -/
def awCar (p : ℕ) (lo A : ℤ) : ℤ := Int.tdiv (lo + A) (awMod p)

/-- The new low part of one component in one round: `lo + A - carry * M`. -/
def awLow (p : ℕ) (lo A : ℤ) : ℤ := (lo + A) - awCar p lo A * awMod p

/-! ## Values -/

/-- The pair value of one round's input: the weight `W` and the window entry `(x,y)`. -/
def AwPair (W x y : ℤ) : Val := .cons (.int W) (.cons (.int x) (.int y))

/-- One round's record: the list of the (at most two) nonzero carries. -/
def awRec (zr zi : ℤ) : Val :=
  ofList ((if zr = 1 then [Val.int 1] else []) ++ (if zi = 1 then [Val.int 2] else []))

/-- Number of occurrences of the marker `.int t` in a value. -/
def awCnt (t : ℤ) : Val → ℕ
  | .int a => if a = t then 1 else 0
  | .nil => 0
  | .cons a b => awCnt t a + awCnt t b

/-- Total number of markers `.int t` in a list of values. -/
def awCnts (t : ℤ) (l : List Val) : ℕ := (l.map (awCnt t)).sum

/-- The records of the first `n` rounds, the most recent first. -/
def awRecs (zr zi : ℕ → ℤ) : ℕ → List Val
  | 0 => []
  | (n + 1) => awRec (zr n) (zi n) :: awRecs zr zi n

/-! ## The running low parts -/

/-- The running low part of the real component. -/
def awLor (p : ℕ) (A : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | (n + 1) => awLow p (awLor p A n) (A n)

/-- The running low part of the imaginary component. -/
def awLoi (p : ℕ) (B : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | (n + 1) => awLow p (awLoi p B n) (B n)

/-- The carry of round `n` (real component). -/
def awZr (p : ℕ) (A : ℕ → ℤ) (n : ℕ) : ℤ := awCar p (awLor p A n) (A n)

/-- The carry of round `n` (imaginary component). -/
def awZi (p : ℕ) (B : ℕ → ℤ) (n : ℕ) : ℤ := awCar p (awLoi p B n) (B n)

/-! ## Elementary facts -/

theorem awQ_pos (p : ℕ) : 0 < awQ p := by simp [awQ]

theorem awMod_pos (p : ℕ) : 0 < awMod p := by
  rw [awMod]; positivity

theorem awMod_eq_shift (p : ℕ) : awMod p = 2 * awSh p := by
  rw [awMod, awSh, awQ, pow_succ]; ring

theorem awCar_nonneg {p : ℕ} {lo A : ℤ} (hl : 0 ≤ lo) (hA : 0 ≤ A) : 0 ≤ awCar p lo A :=
  Int.tdiv_nonneg (by linarith) (le_of_lt (awMod_pos p))

theorem awCar_tdiv {p : ℕ} {lo A : ℤ} (h : 0 ≤ lo + A) :
    awCar p lo A = (lo + A) / (awMod p) :=
  Int.tdiv_eq_ediv_of_nonneg h

theorem awLow_nonneg {p : ℕ} {lo A : ℤ} (hl : 0 ≤ lo) (hA : 0 ≤ A) : 0 ≤ awLow p lo A := by
  have h : 0 ≤ lo + A := by linarith
  rw [awLow, awCar_tdiv h, mul_comm, ← Int.emod_def]
  exact Int.emod_nonneg _ (ne_of_gt (awMod_pos p))

theorem awLow_lt {p : ℕ} {lo A : ℤ} (hl : 0 ≤ lo) (hA : 0 ≤ A) : awLow p lo A < awMod p := by
  have h : 0 ≤ lo + A := by linarith
  rw [awLow, awCar_tdiv h, mul_comm, ← Int.emod_def]
  exact Int.emod_lt_of_pos _ (awMod_pos p)

theorem awLow_add_car {p : ℕ} {lo A : ℤ} : awLow p lo A + awCar p lo A * awMod p = lo + A := by
  rw [awLow]; ring

theorem awCar_eq_zero_or_one {p : ℕ} {lo A : ℤ} (hl : 0 ≤ lo) (hA : 0 ≤ A)
    (hlo : lo < awMod p) (hA' : A < awMod p) : awCar p lo A = 0 ∨ awCar p lo A = 1 := by
  have h : 0 ≤ lo + A := by linarith
  rw [awCar_tdiv h]
  have hM := awMod_pos p
  by_cases hlt : lo + A < awMod p
  · exact Or.inl (Int.ediv_eq_zero_of_lt h hlt)
  · refine Or.inr ?_
    have h2 : lo + A - awMod p < awMod p := by linarith
    have h3 : 0 ≤ lo + A - awMod p := by linarith
    have h4 : (lo + A) / awMod p = ((lo + A - awMod p) + awMod p * 1) / awMod p := by ring_nf
    rw [h4, Int.add_mul_ediv_left (a := lo + A - awMod p) (b := awMod p) (c := 1) (by omega)]
    rw [Int.ediv_eq_zero_of_lt h3 h2]
    ring

theorem awLor_nonneg (p : ℕ) (A : ℕ → ℤ) (hA : ∀ j, 0 ≤ A j) : ∀ n, 0 ≤ awLor p A n
  | 0 => le_refl 0
  | (n+1) => awLow_nonneg (awLor_nonneg p A hA n) (hA n)

theorem awLor_lt (p : ℕ) (A : ℕ → ℤ) (hA : ∀ j, 0 ≤ A j) : ∀ n, awLor p A n < awMod p
  | 0 => by rw [awLor]; exact awMod_pos p
  | (n+1) => awLow_lt (awLor_nonneg p A hA n) (hA n)

theorem awLoi_nonneg (p : ℕ) (B : ℕ → ℤ) (hB : ∀ j, 0 ≤ B j) : ∀ n, 0 ≤ awLoi p B n
  | 0 => le_refl 0
  | (n+1) => awLow_nonneg (awLoi_nonneg p B hB n) (hB n)

theorem awLoi_lt (p : ℕ) (B : ℕ → ℤ) (hB : ∀ j, 0 ≤ B j) : ∀ n, awLoi p B n < awMod p
  | 0 => by rw [awLoi]; exact awMod_pos p
  | (n+1) => awLow_lt (awLoi_nonneg p B hB n) (hB n)

/-- The telescoping invariant of the accumulation. -/
theorem awLor_add_sum (p : ℕ) (A : ℕ → ℤ) :
    ∀ n, awLor p A n + awMod p * (∑ j ∈ Finset.range n, awZr p A j) = ∑ j ∈ Finset.range n, A j
  | 0 => by simp [awLor]
  | (n+1) => by
    have ih := awLor_add_sum p A n
    have hstep := awLow_add_car (p := p) (lo := awLor p A n) (A := A n)
    have hz : awZr p A n = awCar p (awLor p A n) (A n) := rfl
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hz, awLor]
    nlinarith [hstep, ih]

theorem awLoi_add_sum (p : ℕ) (B : ℕ → ℤ) :
    ∀ n, awLoi p B n + awMod p * (∑ j ∈ Finset.range n, awZi p B j) = ∑ j ∈ Finset.range n, B j
  | 0 => by simp [awLoi]
  | (n+1) => by
    have ih := awLoi_add_sum p B n
    have hstep := awLow_add_car (p := p) (lo := awLoi p B n) (A := B n)
    have hz : awZi p B n = awCar p (awLoi p B n) (B n) := rfl
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hz, awLoi]
    nlinarith [hstep, ih]

/-! ## The records -/

/-- The number of marker `1`'s in one record (the carries are `0` or `1`). -/
theorem awCnt_awRec_one {zr zi : ℤ} (hzr : zr = 0 ∨ zr = 1) (hzi : zi = 0 ∨ zi = 1) :
    awCnt 1 (awRec zr zi) = if zr = 1 then 1 else 0 := by
  unfold awRec
  rcases hzr with h | h <;> rcases hzi with h2 | h2 <;>
    · subst h; subst h2; decide +kernel

/-- The number of marker `2`'s in one record. -/
theorem awCnt_awRec_two {zr zi : ℤ} (hzr : zr = 0 ∨ zr = 1) (hzi : zi = 0 ∨ zi = 1) :
    awCnt 2 (awRec zr zi) = if zi = 1 then 1 else 0 := by
  unfold awRec
  rcases hzr with h | h <;> rcases hzi with h2 | h2 <;>
    · subst h; subst h2; decide +kernel

theorem awRecs_length (zr zi : ℕ → ℤ) : ∀ n, (awRecs zr zi n).length = n
  | 0 => rfl
  | (n+1) => by rw [awRecs, List.length_cons, awRecs_length zr zi n]

/-! ## The final answer and the carry list -/

/-- The final answer of one component. -/
def awAns (p : ℕ) (lo C n : ℤ) : ℤ := Int.tdiv (lo + (2 * C - n) * awSh p) ((2 : ℤ) ^ p)

/-- The carries of the first rounds, most recent first, as a list of pairs. -/
def awQs (zr zi : ℕ → ℤ) : ℕ → List (ℤ × ℤ)
  | 0 => []
  | (n + 1) => (zr n, zi n) :: awQs zr zi n

theorem awQs_map_awRec (zr zi : ℕ → ℤ) : ∀ L,
    (awQs zr zi L).map (fun q => awRec q.1 q.2) = awRecs zr zi L
  | 0 => rfl
  | (n + 1) => by rw [awQs, awRecs, List.map_cons, awQs_map_awRec zr zi n]

theorem list_sum_range_map (f : ℕ → ℤ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

theorem awQs_first (zr zi : ℕ → ℤ) : ∀ L,
    ((awQs zr zi L).map fun q => if q.1 = 1 then (1 : ℤ) else 0).sum
      = ∑ j ∈ Finset.range L, (if zr j = 1 then (1 : ℤ) else 0)
  | 0 => by simp [awQs]
  | (n + 1) => by
    rw [awQs, List.map_cons, List.sum_cons, awQs_first zr zi n, Finset.sum_range_succ]
    simp only [Prod.fst]; ring

theorem awQs_second (zr zi : ℕ → ℤ) : ∀ L,
    ((awQs zr zi L).map fun q => if q.2 = 1 then (1 : ℤ) else 0).sum
      = ∑ j ∈ Finset.range L, (if zi j = 1 then (1 : ℤ) else 0)
  | 0 => by simp [awQs]
  | (n + 1) => by
    rw [awQs, List.map_cons, List.sum_cons, awQs_second zr zi n, Finset.sum_range_succ]
    simp only [Prod.snd]; ring

/-- The carried count of a `0/1`-valued sequence is its sum. -/
theorem sum_if_eq (f : ℕ → ℤ) (h : ∀ j, f j = 0 ∨ f j = 1) (n : ℕ) :
    (∑ j ∈ Finset.range n, (if f j = 1 then (1 : ℤ) else 0)) = ∑ j ∈ Finset.range n, f j := by
  apply Finset.sum_congr rfl
  intro j _
  rcases h j with h | h <;> simp [h]

theorem awQs_length (zr zi : ℕ → ℤ) : ∀ L, (awQs zr zi L).length = L
  | 0 => rfl
  | (n + 1) => by rw [awQs, List.length_cons, awQs_length zr zi n]

theorem awQs_mem (zr zi : ℕ → ℤ) {L : ℕ} {q : ℤ × ℤ} (h : q ∈ awQs zr zi L) :
    ∃ j < L, q = (zr j, zi j) := by
  induction L with
  | zero => simp [awQs] at h
  | succ n ih =>
    rw [awQs, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨n, Nat.lt_succ_self n, h⟩
    · obtain ⟨j, hj, hq⟩ := ih h
      exact ⟨j, Nat.lt_succ_of_lt hj, hq⟩

/-- The carry is at most one when the low part is `< M` and the summand is `≤ M`. -/
theorem awCar_le_one {p : ℕ} {lo A : ℤ} (hl : 0 ≤ lo) (hA : 0 ≤ A)
    (hlo : lo < awMod p) (hA' : A ≤ awMod p) : awCar p lo A ≤ 1 := by
  have hM : (0 : ℤ) < awMod p := awMod_pos p
  have hsum : 0 ≤ lo + A := by linarith
  rw [awCar_tdiv hsum]
  by_cases hcase : awMod p ≤ lo + A
  · have h1 : lo + A - awMod p < awMod p := by linarith
    have h2 : 0 ≤ lo + A - awMod p := by linarith
    have he : lo + A = (lo + A - awMod p) + awMod p * 1 := by ring
    rw [he, Int.add_mul_ediv_left (a := lo + A - awMod p) (b := awMod p) (c := (1 : ℤ))
      (ne_of_gt hM), Int.ediv_eq_zero_of_lt h2 h1]
    norm_num
  · have h0 : lo + A < awMod p := lt_of_not_ge hcase
    rw [Int.ediv_eq_zero_of_lt hsum h0]
    norm_num

theorem awLor_nonneg_lt (p : ℕ) (A : ℕ → ℤ) : ∀ n, (∀ j < n, 0 ≤ A j) → 0 ≤ awLor p A n
  | 0, _ => le_refl 0
  | (n+1), h => awLow_nonneg (awLor_nonneg_lt p A n (fun j hj => h j (Nat.lt_succ_of_lt hj)))
      (h n (Nat.lt_succ_self n))

theorem awLor_lt_lt (p : ℕ) (A : ℕ → ℤ) : ∀ n, (∀ j < n, 0 ≤ A j) → awLor p A n < awMod p
  | 0, _ => awMod_pos p
  | (n+1), h => awLow_lt (awLor_nonneg_lt p A n (fun j hj => h j (Nat.lt_succ_of_lt hj)))
      (h n (Nat.lt_succ_self n))

theorem awLoi_nonneg_lt (p : ℕ) (B : ℕ → ℤ) : ∀ n, (∀ j < n, 0 ≤ B j) → 0 ≤ awLoi p B n
  | 0, _ => le_refl 0
  | (n+1), h => awLow_nonneg (awLoi_nonneg_lt p B n (fun j hj => h j (Nat.lt_succ_of_lt hj)))
      (h n (Nat.lt_succ_self n))

theorem awLoi_lt_lt (p : ℕ) (B : ℕ → ℤ) : ∀ n, (∀ j < n, 0 ≤ B j) → awLoi p B n < awMod p
  | 0, _ => awMod_pos p
  | (n+1), h => awLow_lt (awLoi_nonneg_lt p B n (fun j hj => h j (Nat.lt_succ_of_lt hj)))
      (h n (Nat.lt_succ_self n))

/-- The counting identity with the bound only below `n`. -/
theorem sum_if_eq_lt (f : ℕ → ℤ) (n : ℕ) (h : ∀ j < n, f j = 0 ∨ f j = 1) :
    (∑ j ∈ Finset.range n, (if f j = 1 then (1 : ℤ) else 0)) = ∑ j ∈ Finset.range n, f j := by
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < n := Finset.mem_range.mp hj
  rcases h j hj' with h | h <;> simp [h]

theorem list_sum_le_length (l : List ℤ) (h : ∀ x ∈ l, 0 ≤ x ∧ x ≤ 1) :
    l.sum ≤ (l.length : ℤ) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a (by simp)
    have ht : ∀ x ∈ t, 0 ≤ x ∧ x ≤ 1 := fun x hx => h x (by simp [hx])
    have := ih ht
    rw [List.sum_cons, List.length_cons]
    push_cast
    linarith [ha.1, ha.2, this]

theorem list_sum_nonneg (l : List ℤ) (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a (by simp)
    have ht : ∀ x ∈ t, 0 ≤ x := fun x hx => h x (by simp [hx])
    have := ih ht
    rw [List.sum_cons]
    linarith

/-- `|a*b| ≤ 2^{2p}` when both factors have `natAbs ≤ 2^p`. -/
theorem abs_mul_le_awSh {p : ℕ} {a b : ℤ} (ha : a.natAbs ≤ 2 ^ p) (hb : b.natAbs ≤ 2 ^ p) :
    |a * b| ≤ awSh p := by
  have ha' : (a.natAbs : ℤ) ≤ (2 : ℤ) ^ p := by exact_mod_cast ha
  have hb' : (b.natAbs : ℤ) ≤ (2 : ℤ) ^ p := by exact_mod_cast hb
  have h1 : |a| = (a.natAbs : ℤ) := by rw [← Int.natCast_natAbs]
  have h2 : |b| = (b.natAbs : ℤ) := by rw [← Int.natCast_natAbs]
  rw [abs_mul, h1, h2, awSh]
  calc (a.natAbs : ℤ) * (b.natAbs : ℤ) ≤ (2 : ℤ) ^ p * (2 : ℤ) ^ p :=
        mul_le_mul ha' hb' (Int.natCast_nonneg _) (by positivity)
    _ = (2 : ℤ) ^ (2 * p) := by rw [← pow_add, two_mul]

/-- Size of one pair value: `2 + isz W + isz x + isz y`. -/
theorem vsz_AwPair (W x y : ℤ) : vsz (AwPair W x y) = 2 + isz W + isz x + isz y := by
  rw [AwPair, Work.Fx.vsz_cons, Work.Fx.vsz_cons, Work.Fx.vsz_int, Work.Fx.vsz_int, Work.Fx.vsz_int]
  ring

/-- The accumulator invariant of the resampling fold. -/
def awInv (p α s t : ℕ) (A B zr zi : ℕ → ℤ) (rest : List Val) : ℕ → List Val → Prop :=
  fun i acc => ∃ (lo_r lo_i : ℤ) (CH : Val),
    acc = Val.int (p : ℤ) :: Val.int lo_r :: Val.int lo_i :: CH :: auPvals p α s t ++ rest ∧
    0 ≤ lo_r ∧ lo_r < awMod p ∧ 0 ≤ lo_i ∧ lo_i < awMod p ∧
    lo_r = awLor p A i ∧ lo_i = awLoi p B i ∧ CH = ofList (awRecs zr zi i)

end Work.Resample




