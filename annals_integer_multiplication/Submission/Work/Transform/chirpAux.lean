import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Transform.Defs

/-!
# Auxiliary lemmas for the Bluestein chirp word (`Work.Transform.chirpWord`)

This file is owned by the `chirpWord` development.  It holds the small combinatorial and analytic
lemmas used both by the assembly of `Work.Transform.chirpWord` and by the delegated program words
`chirpTabWord`, `blendWord`, `conjVecWord`, `chirpSetupWord`.

Contents:

* `getD_flatten_replicate`, `getD_map_replicate_flatten` (+ their length forms): the index lemmas
  describing the two ways of stretching a vector (repeat each entry `P` times, tile a vector `t`
  times);
* norms and encoding sizes of fixed-point complex numbers in the disc (`inDisc`);
* `chirp_kron`: the identity `chirp (t :: ts') (a * ts'.prod + b) = zeta t (a*a) * chirp ts' b`
  underlying the Kronecker (blend) step;
* `chirp_err_step`: the one-step error accumulation of a fixed-point complex product.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.Transform

open HvdH

/-! ## Index lemmas for stretched / tiled vectors -/

section Index

variable {α : Type*}

/-- In `List.flatten (List.replicate t u)` (the vector `u` tiled `t` times) the entry of flat index
`a * u.length + b` is `u[b]`, for `a < t` and `b < u.length`. -/
theorem getD_flatten_replicate (u : List α) (d : α) (t a b : ℕ) (hb : b < u.length) (ha : a < t) :
    (List.flatten (List.replicate t u)).getD (a * u.length + b) d = u.getD b d := by
  have hrep : List.replicate t u =
      List.replicate a u ++ (u :: List.replicate (t - a - 1) u) := by
    have hsum : t = a + ((t - a - 1) + 1) := by omega
    conv_lhs => rw [hsum]
    rw [List.replicate_add, List.replicate_succ]
  have hlen : (List.flatten (List.replicate a u)).length = a * u.length := by
    rw [List.length_flatten, List.map_replicate, List.sum_replicate]
    simp
  rw [hrep, List.flatten_append, List.flatten_cons]
  have hle : (List.flatten (List.replicate a u)).length ≤ a * u.length + b := by rw [hlen]; omega
  rw [List.getD_append_right _ _ _ _ hle, hlen, Nat.add_sub_cancel_left]
  exact List.getD_append _ _ _ _ hb

/-- Length of the tiled vector. -/
theorem length_flatten_replicate (u : List α) (t : ℕ) :
    (List.flatten (List.replicate t u)).length = t * u.length := by
  rw [List.length_flatten, List.map_replicate, List.sum_replicate]
  simp

/-- Length of the vector obtained by replacing each entry `x` of `c` by `List.replicate P x` and
flattening. -/
theorem length_map_replicate_flatten (c : List α) (P : ℕ) :
    (List.flatten (c.map (fun x => List.replicate P x))).length = c.length * P := by
  rw [List.length_flatten, List.map_map]
  rw [show (List.length ∘ fun x => List.replicate P x) = fun _ => P from by
    funext x; simp]
  rw [List.map_const', List.sum_replicate]
  simp

/-- In the "stretched" vector `List.flatten (c.map (fun x => List.replicate P x))` (each entry of
`c` repeated `P` times) the entry of flat index `a * P + b` is `c[a]`, for `a < c.length`,
`b < P`. -/
theorem getD_map_replicate_flatten (c : List α) (d : α) (P a b : ℕ) (hb : b < P)
    (ha : a < c.length) :
    (List.flatten (c.map (fun x => List.replicate P x))).getD (a * P + b) d = c.getD a d := by
  have hsplit : c = c.take a ++ (c.getD a d :: c.drop (a + 1)) := by
    conv_lhs => rw [← List.take_append_drop a c]
    rw [List.drop_eq_getElem_cons ha, List.getD_eq_getElem c d ha]
  conv_lhs => rw [hsplit, List.map_append, List.map_cons, List.flatten_append, List.flatten_cons]
  have hlen : (List.flatten ((c.take a).map (fun x => List.replicate P x))).length = a * P := by
    rw [length_map_replicate_flatten, List.length_take, Nat.min_eq_left (le_of_lt ha)]
  have hle : (List.flatten ((c.take a).map (fun x => List.replicate P x))).length ≤ a * P + b := by
    rw [hlen]; omega
  rw [List.getD_append_right _ _ _ _ hle, hlen, Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ (by simpa using hb)]
  exact List.getD_replicate (c.getD a d) (y := d) hb

end Index

/-! ## Norms and sizes of fixed-point complex numbers in the disc -/

/-- Every fixed-point number in the disc has modulus `≤ 1`. -/
theorem chirpAux_norm_fxC_le_one {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) : ‖fxC p z‖ ≤ 1 := by
  have hX : (0 : ℝ) ≤ ‖((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)‖ := norm_nonneg _
  have hp : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have h2 : ‖((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)‖ ^ 2 = (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 := by
    rw [Complex.sq_norm]; simp [Complex.normSq_apply]; ring
  have hle : ((z.1 : ℝ)) ^ 2 + (z.2 : ℝ) ^ 2 ≤ ((2 : ℝ) ^ p) ^ 2 := by
    have h3 : ((z.1 : ℝ)) ^ 2 + (z.2 : ℝ) ^ 2 = ((z.1 ^ 2 + z.2 ^ 2 : ℤ) : ℝ) := by
      push_cast; ring
    rw [h3]
    have h4 : ((4 : ℤ) ^ p) = (2 : ℤ) ^ p * 2 ^ p := by
      rw [show (4 : ℤ) = 2 * 2 by norm_num, mul_pow]
    have h5 : ((z.1 ^ 2 + z.2 ^ 2 : ℤ) : ℝ) ≤ (((2 : ℤ) ^ p * 2 ^ p : ℤ) : ℝ) := by
      exact_mod_cast (h.trans (le_of_eq h4))
    have h6 : ((((2 : ℤ) ^ p * 2 ^ p : ℤ)) : ℝ) = ((2 : ℝ) ^ p) ^ 2 := by
      push_cast; ring
    rwa [h6] at h5
  rw [fxC, norm_div, norm_pow, Complex.norm_ofNat, div_le_one hp]
  nlinarith [h2, hle, hX, hp, sq_nonneg (‖((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)‖ - (2 : ℝ) ^ p),
    sq_nonneg (‖((z.1 : ℂ) + (z.2 : ℂ) * Complex.I)‖ + (2 : ℝ) ^ p)]

/-- `‖ζ^c‖ = 1` for `ζ = e^{πi/r}`. -/
theorem chirpAux_norm_zeta (r c : ℕ) : ‖zeta r c‖ = 1 := by
  rw [zeta, Complex.norm_exp]
  have h : (Real.pi * Complex.I * (c : ℂ) / (r : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.div_re]
  rw [h, Real.exp_zero]

/-- A coordinate of a point of the disc has `natAbs ≤ 2^p`. -/
theorem chirpAux_natAbs_le_of_inDisc {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) :
    z.1.natAbs ≤ 2 ^ p ∧ z.2.natAbs ≤ 2 ^ p := by
  have key : ∀ w : ℤ, w ^ 2 ≤ 4 ^ p → w.natAbs ≤ 2 ^ p := by
    intro w hw
    have h1 : (w.natAbs : ℤ) ^ 2 ≤ (2 : ℤ) ^ p * 2 ^ p := by
      rw [Int.natAbs_sq]
      calc w ^ 2 ≤ 4 ^ p := hw
        _ = (2 : ℤ) ^ p * 2 ^ p := by rw [show (4 : ℤ) = 2 * 2 by norm_num, mul_pow]
    have h2 : w.natAbs ^ 2 ≤ (2 ^ p) ^ 2 := by
      rw [pow_two (2 ^ p)]
      exact_mod_cast h1
    exact (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).1 h2
  have hz1 : z.1 ^ 2 ≤ 4 ^ p := by unfold inDisc at h; nlinarith [sq_nonneg z.2]
  have hz2 : z.2 ^ 2 ≤ 4 ^ p := by unfold inDisc at h; nlinarith [sq_nonneg z.1]
  exact ⟨key z.1 hz1, key z.2 hz2⟩

/-- A coordinate of a point of the disc has encoding size `≤ p + 3`. -/
theorem chirpAux_isz_le_of_inDisc {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) :
    isz z.1 ≤ p + 3 ∧ isz z.2 ≤ p + 3 := by
  obtain ⟨h1, h2⟩ := chirpAux_natAbs_le_of_inDisc h
  have key : ∀ w : ℤ, w.natAbs ≤ 2 ^ p → isz w ≤ p + 3 := by
    intro w hw
    have h3 : w.natAbs.size ≤ p + 1 := by
      rw [Nat.size_le]
      exact lt_of_le_of_lt hw (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self p))
    simp only [isz]; omega
  exact ⟨key z.1 h1, key z.2 h2⟩

/-! ### Encoding sizes (`szl`/`vsz`/`isz` bookkeeping) -/

theorem chirpAux_encodePosNum_length (q : PosNum) :
    (Computability.encodePosNum q).length = q.natSize := by
  induction q with
  | one => rfl
  | bit0 q ih => simp [Computability.encodePosNum, PosNum.natSize, ih]
  | bit1 q ih => simp [Computability.encodePosNum, PosNum.natSize, ih]

theorem chirpAux_encodeNum_length (x : Num) :
    (Computability.encodeNum x).length = x.natSize := by
  cases x with
  | zero => rfl
  | pos q => exact chirpAux_encodePosNum_length q

theorem chirpAux_castNum_ofNat'_nat (n : ℕ) : ((Num.ofNat' n : Num) : ℕ) = n := by simp

theorem chirpAux_encodeNat_length (n : ℕ) : (Computability.encodeNat n).length = n.size := by
  change (Computability.encodeNum (Num.ofNat' n)).length = n.size
  rw [chirpAux_encodeNum_length, Num.natSize_to_nat, chirpAux_castNum_ofNat'_nat]

/-- The encoding size of an integer value is `isz`. -/
theorem chirpAux_vsz_int (z : ℤ) : vsz (.int z) = isz z := by
  simp only [vsz, Val.enc, List.length_cons, List.length_append, List.length_nil,
    List.length_map, chirpAux_encodeNat_length, isz]

/-- Encoding size of a `cons` value. -/
theorem chirpAux_vsz_cons (a b : Val) : vsz (.cons a b) = vsz a + vsz b + 1 := by
  simp only [vsz, Val.enc, List.length_cons, List.length_append]

/-- Encoding size of a `cons`-chain. -/
theorem chirpAux_vsz_ofList (xs : List Val) : vsz (ofList xs) = (xs.map vsz).sum + xs.length + 1 := by
  induction xs with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x xs ih =>
    have e : ofList (x :: xs) = .cons x (ofList xs) := rfl
    rw [e, chirpAux_vsz_cons, ih]
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- Encoding size of a fixed-point complex number in the disc. -/
theorem chirpAux_vsz_cfxVal_le {p : ℕ} {z : ℤ × ℤ} (h : inDisc p z) :
    vsz (cfxVal z) ≤ 2 * p + 8 := by
  obtain ⟨h1, h2⟩ := chirpAux_isz_le_of_inDisc h
  rw [show cfxVal z = Val.cons (.int z.1) (.int z.2) from rfl, chirpAux_vsz_cons,
    chirpAux_vsz_int, chirpAux_vsz_int]
  omega

/-- Total encoding size of a value in the disc vector. -/
theorem chirpAux_vsz_cvecVal_le {p n : ℕ} {a : List (ℤ × ℤ)} (h : InDiscVec p n a) :
    vsz (cvecVal a) ≤ n * (2 * p + 8) + n + 1 := by
  have hlen : a.length = n := h.1
  have hsum : ((a.map cfxVal).map vsz).sum ≤ a.length * (2 * p + 8) := by
    calc ((a.map cfxVal).map vsz).sum
        = (a.map (fun z => vsz (cfxVal z))).sum := by rw [List.map_map]; rfl
      _ ≤ (a.map (fun _ => 2 * p + 8)).sum :=
          List.sum_le_sum (fun z hz => chirpAux_vsz_cfxVal_le (h.2 z hz))
      _ = a.length * (2 * p + 8) := by
          induction a with
          | nil => simp
          | cons x xs ih => simp [ih, Nat.succ_mul]; omega
  rw [hlen] at hsum
  rw [show cvecVal a = ofList (a.map cfxVal) from rfl, chirpAux_vsz_ofList, List.length_map, hlen]
  omega

/-- Total encoding size of `intList ts`. -/
theorem chirpAux_vsz_intList_le (ts : List ℕ) :
    vsz (intList ts) ≤ ts.sum + 4 * ts.length + 2 := by
  induction ts with
  | nil => simp [intList, ofList, vsz, Val.enc]
  | cons t ts ih =>
    have e : intList (t :: ts) = Val.cons (.int (t : ℤ)) (intList ts) := rfl
    have i1 : isz (t : ℤ) ≤ t + 3 := by
      have h2 : t.size ≤ t + 1 := by
        rw [Nat.size_le]
        calc t < 2 ^ t := Nat.lt_two_pow_self
          _ ≤ 2 ^ (t + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ t)
      show (t : ℤ).natAbs.size + 2 ≤ t + 3
      rw [Int.natAbs_natCast]
      omega
    rw [e, chirpAux_vsz_cons, chirpAux_vsz_int]
    simp only [List.sum_cons, List.length_cons]
    omega

/-- `star` of a fixed-point complex number is the fixed-point number with the second coordinate
negated. -/
theorem chirpAux_star_fxC (p : ℕ) (z : ℤ × ℤ) :
    star (fxC p z) = fxC p (z.1, -z.2) := by
  rw [fxC, fxC, Complex.star_def, map_div₀, map_add, map_mul, map_pow]
  have hbase : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  rw [hbase]
  push_cast
  simp only [Complex.conj_I]
  rw [map_intCast, map_intCast]
  ring

/-! ## The chirp at a flattened (Kronecker) index -/

/-- The chirp at the flattened index `a * ts'.prod + b` (i.e. the digit `a` of the first dimension)
factors as the `a`-th entry of the first dimension's table times the chirp of the tail. -/
theorem chirp_kron (t : ℕ) (ts' : List ℕ) (a b : ℕ) (ha : a < t) (hb : b < ts'.prod) :
    chirp (t :: ts') (a * ts'.prod + b) = zeta t (a * a) * chirp ts' b := by
  have hP : 0 < ts'.prod := lt_of_le_of_lt (Nat.zero_le b) hb
  have hdiv : (a * ts'.prod + b) / ts'.prod = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hb, Nat.zero_add]
  have hmod : (a * ts'.prod + b) % ts'.prod = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  simp only [chirp, HvdH.digits, hdiv, hmod, Nat.mod_eq_of_lt ha, HvdH.phase]
  rw [zeta, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## One step of the error analysis -/

/-- Error propagation for one fixed-point complex multiplication: if `w` approximates the product
`A·B` with scaled error `< 2`, `A` approximates `U` with scaled error `< 2` and `B` approximates `V`
with scaled error `< e`, and `|B| ≤ 1`, `|U| ≤ 1`, then the scaled error of `w` against `U·V` is
`< 4 + e`. -/
theorem chirp_err_step {p : ℕ} {w A B U V : ℂ} {e : ℝ}
    (h1 : (2 : ℝ) ^ p * ‖w - A * B‖ < 2) (h2 : (2 : ℝ) ^ p * ‖A - U‖ < 2)
    (h3 : (2 : ℝ) ^ p * ‖B - V‖ < e) (hB : ‖B‖ ≤ 1) (hU : ‖U‖ ≤ 1) :
    (2 : ℝ) ^ p * ‖w - U * V‖ < 4 + e := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hkey : w - U * V = (w - A * B) + ((A - U) * B + U * (B - V)) := by ring
  have hn1 : ‖(A - U) * B‖ = ‖A - U‖ * ‖B‖ := norm_mul _ _
  have hn2 : ‖U * (B - V)‖ = ‖U‖ * ‖B - V‖ := norm_mul _ _
  have htri : ‖w - U * V‖ ≤ ‖w - A * B‖ + (‖A - U‖ * ‖B‖ + ‖U‖ * ‖B - V‖) := by
    rw [hkey]
    calc ‖(w - A * B) + ((A - U) * B + U * (B - V))‖
        ≤ ‖w - A * B‖ + ‖(A - U) * B + U * (B - V)‖ := norm_add_le _ _
      _ ≤ ‖w - A * B‖ + (‖(A - U) * B‖ + ‖U * (B - V)‖) := by
          have := norm_add_le ((A - U) * B) (U * (B - V))
          linarith
      _ = ‖w - A * B‖ + (‖A - U‖ * ‖B‖ + ‖U‖ * ‖B - V‖) := by rw [hn1, hn2]
  have hA : 0 ≤ (2 : ℝ) ^ p * ‖A - U‖ := by positivity
  have hB0 : 0 ≤ ‖B‖ := norm_nonneg _
  have hUU : 0 ≤ ‖U‖ := norm_nonneg _
  have hbb : 0 ≤ ‖B - V‖ := norm_nonneg _
  have h4 : (2 : ℝ) ^ p * (‖A - U‖ * ‖B‖) ≤ (2 : ℝ) ^ p * ‖A - U‖ := by
    have : ‖A - U‖ * ‖B‖ ≤ ‖A - U‖ * 1 := by
      exact mul_le_mul_of_nonneg_left hB (norm_nonneg _)
    calc (2 : ℝ) ^ p * (‖A - U‖ * ‖B‖) ≤ (2 : ℝ) ^ p * (‖A - U‖ * 1) := by
          exact mul_le_mul_of_nonneg_left this (le_of_lt hp)
      _ = (2 : ℝ) ^ p * ‖A - U‖ := by ring
  have h5 : (2 : ℝ) ^ p * (‖U‖ * ‖B - V‖) ≤ (2 : ℝ) ^ p * ‖B - V‖ := by
    have : ‖U‖ * ‖B - V‖ ≤ 1 * ‖B - V‖ := mul_le_mul_of_nonneg_right hU hbb
    calc (2 : ℝ) ^ p * (‖U‖ * ‖B - V‖) ≤ (2 : ℝ) ^ p * (1 * ‖B - V‖) :=
          mul_le_mul_of_nonneg_left this (le_of_lt hp)
      _ = (2 : ℝ) ^ p * ‖B - V‖ := by ring
  have hstep : (2 : ℝ) ^ p * ‖w - U * V‖
      ≤ (2 : ℝ) ^ p * ‖w - A * B‖ + ((2 : ℝ) ^ p * ‖A - U‖ + (2 : ℝ) ^ p * ‖B - V‖) := by
    calc (2 : ℝ) ^ p * ‖w - U * V‖
        ≤ (2 : ℝ) ^ p * (‖w - A * B‖ + (‖A - U‖ * ‖B‖ + ‖U‖ * ‖B - V‖)) :=
          mul_le_mul_of_nonneg_left htri (le_of_lt hp)
      _ = (2 : ℝ) ^ p * ‖w - A * B‖ + ((2 : ℝ) ^ p * (‖A - U‖ * ‖B‖)
            + (2 : ℝ) ^ p * (‖U‖ * ‖B - V‖)) := by ring
      _ ≤ (2 : ℝ) ^ p * ‖w - A * B‖ + ((2 : ℝ) ^ p * ‖A - U‖ + (2 : ℝ) ^ p * ‖B - V‖) := by
          linarith
  linarith

end Work.Transform
