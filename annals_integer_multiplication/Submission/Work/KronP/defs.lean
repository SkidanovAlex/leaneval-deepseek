import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.ConvR.basic

/-!
# KronP: shared definitions for the Kronecker-substitution word (paper Lemma 2.5)

This file holds the *vocabulary* used by `Submission/Work/KronP/kronecker.lean` and by the
delegated lemmas about it.

## The route

Given `p, r` and two coefficient vectors `u, v ∈ C̃◦^r` (each a list of pairs of integers,
each pair in the disc), write `U₀ = u.map Prod.fst`, `U₁ = u.map Prod.snd`, `V₀, V₁` likewise
(these are the integers `2^p ·` the real/imaginary parts).  Put `X_j := pack U_j (3p)`,
`Y_k := pack V_k (3p)`, `B := 2^{3p}`, `T := 2^{3p-1}`, `N := 2r` and

`C := Σ_{m<N} T·B^m`  (`digitOffset p N`).

The coefficient of `U_j·V_k` at position `m` is at most `r·2^{2p} < T`, so

`X_j·Y_k + C = Σ_{m<N} (c_m + T)·B^m` with `c_m + T ∈ [0, B)`;

hence the base-`B` digits of the nonnegative integer `X_j·Y_k + C` are exactly `c_m + T`
(`kronDigits`).  The Kronecker substitution has therefore produced the coefficients of the four
integer polynomial products in a *linear* number of operations.

The negacyclic combination (coefficient `k` minus coefficient `k+r`) and the truncating division
by `D = 2^{p+κ}` (`r = 2^κ`) are then done coefficientwise (`kronW`, `kronVec`).
-/

set_option autoImplicit false

namespace Work.KronP

open HvdH

/-! ## Basic value encodings -/

/-- Value encoding of a list of integers. -/
def zsVal (l : List ℤ) : Val := ofList (l.map Val.int)

@[simp] theorem zsVal_nil : zsVal ([] : List ℤ) = .nil := rfl

@[simp] theorem zsVal_cons (a : ℤ) (l : List ℤ) :
    zsVal (a :: l) = .cons (.int a) (zsVal l) := rfl

/-- `intList` and `zsVal` agree through the cast `ℕ → ℤ`. -/
theorem intList_eq_zsVal (l : List ℕ) :
    intList l = zsVal (l.map (fun n => (n : ℤ))) := by
  simp [intList, zsVal, List.map_map, Function.comp_def]

theorem vsz_int_eq (z : ℤ) : vsz (Val.int z) = isz z := Work.ConvR.vsz_int z

theorem vsz_zsVal_le {l : List ℤ} {L : ℕ} (h : ∀ x ∈ l, isz x ≤ L) :
    vsz (zsVal l) ≤ l.length * L + l.length + 1 := by
  have hmap : (l.map (fun x => vsz (Val.int x))) = l.map (fun x => isz x) :=
    List.map_congr_left (fun x _ => vsz_int_eq x)
  have hsum : (l.map (fun x => isz x)).sum ≤ l.length * L := by
    calc (l.map (fun x => isz x)).sum ≤ (l.map (fun _ => L)).sum :=
          List.sum_le_sum (fun x hx => h x hx)
      _ = l.length * L := by
          induction l with
          | nil => simp
          | cons a l ih => simp [ih, Nat.succ_mul, Nat.add_comm]
  rw [show zsVal l = ofList (l.map Val.int) from rfl, Work.ConvR.vsz_ofList, List.length_map,
    List.map_map]
  simp only [Function.comp_def] at hmap ⊢
  rw [hmap]
  omega

/-! ## Packing and the convolution coefficients -/

/-- `pack l b = Σ_j l[j]·2^{b·j}` — the Kronecker packing of the coefficient list `l` in base
`2^b` (the coefficients may be negative; the callers split them into positive and negative parts). -/
def pack (l : List ℤ) (b : ℕ) : ℤ :=
  ((List.range l.length).map fun j => l.getD j 0 * (2 : ℤ) ^ (b * j)).sum

/-- The `m`-th coefficient `Σ_{j+k=m} l₁[j]·l₂[k]` of the product of two coefficient lists. -/
def convCoef (l₁ l₂ : List ℤ) (m : ℕ) : ℤ :=
  (((List.range (min l₁.length (m + 1))).filter (fun j => m - j < l₂.length)).map
    (fun j => l₁.getD j 0 * l₂.getD (m - j) 0)).sum

/-- `C = Σ_{m<N} T·B^m` with `T = 2^{3p-1}`, `B = 2^{3p}`: the offset that makes all base-`B`
digits of `W + C` nonnegative when `W` has balanced coefficient digits. -/
def digitOffset (p N : ℕ) : ℤ :=
  ((List.range N).map fun m => (2 : ℤ) ^ (3 * p - 1) * (2 : ℤ) ^ (3 * p * m)).sum

/-- The packing of the real part of `2^p·u`. -/
def kronX0 (u : List (ℤ × ℤ)) (p : ℕ) : ℤ := pack (u.map Prod.fst) (3 * p)

/-- The packing of the imaginary part of `2^p·u`. -/
def kronX1 (u : List (ℤ × ℤ)) (p : ℕ) : ℤ := pack (u.map Prod.snd) (3 * p)

/-- The packing of the real part of `2^p·v`. -/
def kronY0 (v : List (ℤ × ℤ)) (p : ℕ) : ℤ := pack (v.map Prod.fst) (3 * p)

/-- The packing of the imaginary part of `2^p·v`. -/
def kronY1 (v : List (ℤ × ℤ)) (p : ℕ) : ℤ := pack (v.map Prod.snd) (3 * p)

/-- The `N` base-`2^{3p}` digits of the nonnegative integer `X·Y + digitOffset p N`
(the `T`-shifted product coefficients). -/
def kronDigits (p N : ℕ) (X Y : ℤ) : List ℕ :=
  chunks (X * Y + digitOffset p N).toNat (3 * p) N

/-! ## The coefficientwise combination -/

/-- Cast a `ℕ`-list to a `ℤ`-list. -/
def toZl (l : List ℕ) : List ℤ := l.map (fun n => (n : ℤ))

/-- Pointwise difference of two integer lists. -/
def zsubL (l₁ l₂ : List ℤ) : List ℤ := l₁.zipWith (· - ·) l₂

/-- Pointwise sum of two integer lists. -/
def zaddL (l₁ l₂ : List ℤ) : List ℤ := l₁.zipWith (· + ·) l₂

/-- `Δ A = A[0..r) - A[r..2r)`: the negacyclic fold `Σ_m A_m y^m ↦ Σ_{k<r} (A_k - A_{k+r}) y^k`. -/
def deltaL (A : List ℕ) (r : ℕ) : List ℤ := zsubL ((toZl A).take r) ((toZl A).drop r)

/-- Coefficient list of the real part of `4^p·(u·v)` in `ℂ[y]/(y^r+1)`. -/
def D0L (r : ℕ) (A00 A11 : List ℕ) : List ℤ := zsubL (deltaL A00 r) (deltaL A11 r)

/-- Coefficient list of the imaginary part of `4^p·(u·v)` in `ℂ[y]/(y^r+1)`. -/
def D1L (r : ℕ) (A01 A10 : List ℕ) : List ℤ := zaddL (deltaL A01 r) (deltaL A10 r)

/-- The final truncated-quotient vector: divide both parts by `D = 2^{p+κ}` (`r = 2^κ`). -/
noncomputable def kronW (p r : ℕ) (A00 A01 A10 A11 : List ℕ) : List (ℤ × ℤ) :=
  (D0L r A00 A11).zipWith
    (fun a b => (Int.tdiv a (2 ^ (p + Nat.clog 2 r)), Int.tdiv b (2 ^ (p + Nat.clog 2 r))))
    (D1L r A01 A10)

/-- The vector produced by the Kronecker word on the digit lists of the four products. -/
noncomputable def kronVec (p r : ℕ) (u v : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  kronW p r (kronDigits p (2 * r) (kronX0 u p) (kronY0 v p))
            (kronDigits p (2 * r) (kronX0 u p) (kronY1 v p))
            (kronDigits p (2 * r) (kronX1 u p) (kronY0 v p))
            (kronDigits p (2 * r) (kronX1 u p) (kronY1 v p))

/-! ## Sizes used in the cost bounds -/

/-- The size bound for the digit-list value of one product. -/
def digVSz (p r : ℕ) : ℕ := 2 * r * (3 * p + 4) + 2 * r + 1

theorem digVSz_le (p r : ℕ) : digVSz p r ≤ 64 * ((r + 1) * (p + 1) ^ 2) := by
  have hp1 : 1 ≤ p + 1 := by omega
  have hpp : (p + 1) ≤ (p + 1) * (p + 1) := Nat.le_mul_of_pos_left _ hp1
  have hRR : r ≤ r + 1 := by omega
  have hc : 2 * r + 1 ≤ 3 * ((r + 1) * ((p + 1) * (p + 1))) := by
    nlinarith [hRR, hpp, Nat.zero_le p, Nat.zero_le r]
  have hb : 2 * r * (3 * p + 4) ≤ 8 * ((r + 1) * ((p + 1) * (p + 1))) := by
    have ha : 3 * p + 4 ≤ 4 * (p + 1) := by omega
    have h1 : 2 * r * (3 * p + 4) ≤ 2 * r * (4 * (p + 1)) := Nat.mul_le_mul_left _ ha
    have h3 : 2 * r * (4 * (p + 1)) ≤ 8 * ((r + 1) * ((p + 1) * (p + 1))) := by
      nlinarith [hRR, hpp, Nat.zero_le p, Nat.zero_le r]
    linarith
  have hfin : 2 * r * (3 * p + 4) + (2 * r + 1) ≤ 11 * ((r + 1) * ((p + 1) * (p + 1))) := by
    linarith
  have hgoal : 11 * ((r + 1) * ((p + 1) * (p + 1))) ≤ 64 * ((r + 1) * ((p + 1) * (p + 1))) :=
    Nat.mul_le_mul_right _ (by norm_num)
  show 2 * r * (3 * p + 4) + 2 * r + 1 ≤ 64 * ((r + 1) * (p + 1) ^ 2)
  rw [show (p + 1) ^ 2 = (p + 1) * (p + 1) from by ring]
  linarith [hfin, hgoal]

end Work.KronP
