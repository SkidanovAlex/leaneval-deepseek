import Mathlib
import Submission.Work.KronP.kdefs
import Submission.Work.KronP.packMul
import Submission.Work.KronP.convDsum
import Submission.Work.KronP.convCoefBound
import Submission.Work.KronP.chunksDigits
import Submission.Work.KronP.negaIntCoeff
import Submission.Work.KronP.truncApprox
import Submission.Work.ConvR.negaNorm

/-!
# KronP: the mathematical content of paper Lemma 2.5 (`Work.KronP.kronFinal`)

`Work.KronP.kronVec p r u v` is built from the base-`2^{3p}` digits of the four packed products
`kronX_j u p · kronY_k v p`, offset by `digitOffset p (2r)`, then the negacyclic fold and the
truncating division by `2^{p+κ}` (`r = 2^κ`).  This file assembles the proof that the resulting
vector is in the disc `C̃◦^r` and approximates `(1/r)·u·v` with error `< 2` (paper Lemma 2.5),
from the delegated ingredients

* `Work.KronP.packMul`, `Work.KronP.convCoefBound`, `Work.KronP.chunksDigits` (base-`2^{3p}` digits
  of the packed products are the shifted convolution coefficients, `kronDigits_eq` below);
* `Work.KronP.convDsum` (the negacyclic fold in terms of `dsumL`);
* `deltaL_digitList` below (the fold `Δ` of a digit list is the difference of the coefficients);
* `Work.KronP.negaIntCoeff` (`4^p·(u·v) = D0c + i·D1c` exactly);
* `Work.KronP.truncApprox` (truncating division keeps the disc and costs at most `√2 < 2`).
-/

set_option autoImplicit false

namespace Work.KronP
open HvdH

/-! ### placeholders for the delegated lemmas (to be replaced by imports) -/

/-! ### helper lemmas -/

theorem zipWith_map_same {α β γ δ : Type*} (h : α → β → γ) (f : δ → α) (g : δ → β) (l : List δ) :
    List.zipWith h (l.map f) (l.map g) = l.map (fun k => h (f k) (g k)) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem zsubL_map (r : ℕ) (f g : ℕ → ℤ) :
    zsubL ((List.range r).map f) ((List.range r).map g)
      = (List.range r).map (fun k => f k - g k) := by
  unfold zsubL
  exact zipWith_map_same (fun a b => a - b) f g (List.range r)

theorem zaddL_map (r : ℕ) (f g : ℕ → ℤ) :
    zaddL ((List.range r).map f) ((List.range r).map g)
      = (List.range r).map (fun k => f k + g k) := by
  unfold zaddL
  exact zipWith_map_same (fun a b => a + b) f g (List.range r)

theorem getD_range_eq (n j : ℕ) : (List.range n).getD j 0 = if j < n then j else 0 := by
  rcases lt_or_ge j n with h | h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_range]
    simp [h]
  · rw [List.getD_eq_default _ _ (by simpa using h)]
    simp [Nat.not_lt.mpr h]

/-! ### `toZl`, `drop` and the digit lists -/

theorem toZl_cons (n : ℕ) (l : List ℕ) : toZl (n :: l) = ((n : ℤ) :: toZl l) := rfl

/-- `toZl` of a mapped list, computed pointwise. -/
theorem toZl_map {α : Type*} (l : List α) (f : α → ℕ) (g : α → ℤ)
    (h : ∀ x ∈ l, (f x : ℤ) = g x) : toZl (l.map f) = l.map g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.map_cons, toZl_cons, List.map_cons, h a List.mem_cons_self]
      congr 1
      exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

theorem drop_range_two (g : ℕ → ℤ) (r : ℕ) :
    ((List.range (2 * r)).drop r).map g = (List.range r).map (fun k => g (k + r)) := by
  apply List.ext_getElem
  · rw [List.length_map, List.length_drop, List.length_range, List.length_map, List.length_range]
    omega
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_map, List.getElem_drop, List.getElem_range,
        List.getElem_range]
    congr 1
    omega

/-- The negacyclic fold `Δ` of a list of `T`-shifted digits is the difference of the
coefficients: if `A_m = (c m + T).toNat` with `2|c m| < 2^{3p}` (so that the shift makes every
entry positive), then `Δ A k = c k - c (k+r)`. -/
theorem deltaL_digitList {p r : ℕ} (hp : 1 ≤ p) {c : ℕ → ℤ}
    (hbd : ∀ m, m < 2 * r → 2 * |c m| < (2 : ℤ) ^ (3 * p)) :
    deltaL ((List.range (2 * r)).map (fun m => (c m + (2 : ℤ) ^ (3 * p - 1)).toNat)) r
      = (List.range r).map (fun k => c k - c (k + r)) := by
  have h2T : (2 : ℤ) ^ (3 * p) = 2 * (2 : ℤ) ^ (3 * p - 1) := by
    have h4 : (2 : ℤ) ^ (3 * p - 1 + 1) = (2 : ℤ) ^ (3 * p - 1) * 2 := pow_succ _ _
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 3 * p)] at h4
    rw [h4]; ring
  have hpos : ∀ m, m < 2 * r → 0 < c m + (2 : ℤ) ^ (3 * p - 1) := by
    intro m hm
    have h := hbd m hm
    have h1 : |c m| < (2 : ℤ) ^ (3 * p - 1) := by linarith [h2T]
    have h2 := neg_abs_le (c m)
    linarith
  have htoZl : toZl ((List.range (2 * r)).map
        (fun m => (c m + (2 : ℤ) ^ (3 * p - 1)).toNat))
      = (List.range (2 * r)).map (fun m => c m + (2 : ℤ) ^ (3 * p - 1)) :=
    toZl_map _ _ _ (fun x hx => Int.toNat_of_nonneg (le_of_lt (hpos x (List.mem_range.mp hx))))
  unfold deltaL
  rw [htoZl, ← List.map_take, ← List.map_drop, List.take_range,
      Nat.min_eq_left (by omega : r ≤ 2 * r)]
  rw [drop_range_two]
  rw [zsubL_map]
  apply List.map_congr_left
  intro k _
  ring

theorem convCoef_two_mul_abs_lt {p r : ℕ} (hp : 1 ≤ p) (hr : r < 2 ^ (p - 1)) {l₁ l₂ : List ℤ}
    (h₁ : l₁.length = r) (h₂ : l₂.length = r) (hb₁ : ∀ x ∈ l₁, x.natAbs ≤ 2 ^ p)
    (hb₂ : ∀ x ∈ l₂, x.natAbs ≤ 2 ^ p) (m : ℕ) :
    2 * |convCoef l₁ l₂ m| < (2 : ℤ) ^ (3 * p) := by
  have hc := convCoefBound hp hr h₁ h₂ hb₁ hb₂ m
  have hcast : ((2 * (convCoef l₁ l₂ m).natAbs : ℕ) : ℤ) < ((2 ^ (3 * p) : ℕ) : ℤ) := by
    exact_mod_cast hc
  rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat] at hcast
  rwa [show ((convCoef l₁ l₂ m).natAbs : ℤ) = |convCoef l₁ l₂ m| from by simp] at hcast

/-! ### the digits of the packed products -/

theorem kronDigits_eq {p r : ℕ} (hp : 1 ≤ p) {l₁ l₂ : List ℤ} (h₁ : l₁.length = r)
    (h₂ : l₂.length = r) (hb₁ : ∀ x ∈ l₁, x.natAbs ≤ 2 ^ p) (hb₂ : ∀ x ∈ l₂, x.natAbs ≤ 2 ^ p)
    (hr : r < 2 ^ (p - 1)) :
    Work.KronP.kronDigits p (2 * r) (Work.KronP.pack l₁ (3 * p)) (Work.KronP.pack l₂ (3 * p)) =
      (List.range (2 * r)).map (fun m => (Work.KronP.convCoef l₁ l₂ m + (2 : ℤ) ^ (3 * p - 1)).toNat) := by
  have h2T : (2 : ℤ) ^ (3 * p) = 2 * (2 : ℤ) ^ (3 * p - 1) := by
    have h4 : (2 : ℤ) ^ (3 * p - 1 + 1) = (2 : ℤ) ^ (3 * p - 1) * 2 := pow_succ _ _
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 3 * p)] at h4
    rw [h4]; ring
  set d : List ℕ := (List.range (2 * r)).map
    (fun m => (convCoef l₁ l₂ m + (2 : ℤ) ^ (3 * p - 1)).toNat) with hd
  have hdget : ∀ j, j < 2 * r →
      d.getD j 0 = (convCoef l₁ l₂ j + (2 : ℤ) ^ (3 * p - 1)).toNat := by
    intro j hj
    rw [hd, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
  have hdl : d.length = 2 * r := by rw [hd]; simp
  have hpos : ∀ m, m < 2 * r → 0 < convCoef l₁ l₂ m + (2 : ℤ) ^ (3 * p - 1) := by
    intro m hm
    have hlt := convCoef_two_mul_abs_lt hp hr h₁ h₂ hb₁ hb₂ m
    have h1 : |convCoef l₁ l₂ m| < (2 : ℤ) ^ (3 * p - 1) := by linarith [h2T]
    have h2 := neg_abs_le (convCoef l₁ l₂ m)
    linarith
  have hltB : ∀ m, m < 2 * r → convCoef l₁ l₂ m + (2 : ℤ) ^ (3 * p - 1) < (2 : ℤ) ^ (3 * p) := by
    intro m hm
    have hlt := convCoef_two_mul_abs_lt hp hr h₁ h₂ hb₁ hb₂ m
    have h1 : |convCoef l₁ l₂ m| < (2 : ℤ) ^ (3 * p - 1) := by linarith [h2T]
    have h2 := le_abs_self (convCoef l₁ l₂ m)
    linarith [h2T]
  have hbd : ∀ x ∈ d, x < 2 ^ (3 * p) := by
    intro x hx
    rw [hd] at hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_range] at hm
    have hnn := le_of_lt (hpos m hm)
    have hc : (((convCoef l₁ l₂ m + (2 : ℤ) ^ (3 * p - 1)).toNat : ℕ) : ℤ) <
        ((2 ^ (3 * p) : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hnn]; exact_mod_cast hltB m hm
    exact_mod_cast hc
  have hXY : pack l₁ (3 * p) * pack l₂ (3 * p) =
      ((List.range (2 * r)).map (fun m => convCoef l₁ l₂ m * (2 : ℤ) ^ (3 * p * m))).sum := by
    have h := packMul l₁ l₂ (3 * p)
    rw [h₁, h₂, show r + r = 2 * r from by ring] at h
    exact h
  have hC : digitOffset p (2 * r) =
      ((List.range (2 * r)).map (fun m => (2 : ℤ) ^ (3 * p - 1) * (2 : ℤ) ^ (3 * p * m))).sum := rfl
  have hsum : pack l₁ (3 * p) * pack l₂ (3 * p) + digitOffset p (2 * r) =
      ((List.range (2 * r)).map
        (fun m => (convCoef l₁ l₂ m + (2 : ℤ) ^ (3 * p - 1)) * (2 : ℤ) ^ (3 * p * m))).sum := by
    rw [hXY, hC, ← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro m _
    ring
  have hnn : 0 ≤ pack l₁ (3 * p) * pack l₂ (3 * p) + digitOffset p (2 * r) := by
    rw [hsum]
    apply List.sum_nonneg
    intro x hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (le_of_lt (hpos m (List.mem_range.mp hm))) (by positivity)
  have heval : ((HvdH.evalChunks d (3 * p) : ℕ) : ℤ) =
      pack l₁ (3 * p) * pack l₂ (3 * p) + digitOffset p (2 * r) := by
    rw [hsum, HvdH.evalChunks, hdl, Nat.cast_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro m hm
    rw [Function.comp_apply, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      hdget m (List.mem_range.mp hm),
      Int.toNat_of_nonneg (le_of_lt (hpos m (List.mem_range.mp hm)))]
  have heval2 : HvdH.evalChunks d (3 * p) =
      (pack l₁ (3 * p) * pack l₂ (3 * p) + digitOffset p (2 * r)).toNat := by
    have h := heval
    rw [← Int.toNat_of_nonneg hnn] at h
    exact Nat.cast_inj.mp h
  rw [Work.KronP.kronDigits, ← heval2]
  exact chunksDigits (by omega) d hbd hdl

/-! ### the main statement -/

theorem kronFinal {p r : ℕ} (hrpow : r = 2 ^ (Nat.clog 2 r)) (hr2 : 2 ≤ r) (hrlt : r < 2 ^ (p - 1))
    {u v : List (ℤ × ℤ)} (hu : HvdH.InDiscVec p r u) (hv : HvdH.InDiscVec p r v) :
    HvdH.InDiscVec p r (Work.KronP.kronVec p r u v) ∧
      ∀ j : Fin r, (2 : ℝ) ^ p * ‖HvdH.fxC p ((Work.KronP.kronVec p r u v).getD j (0, 0)) -
        ((r : ℂ))⁻¹ * HvdH.negaMul r (HvdH.fxVec p r u) (HvdH.fxVec p r v) j‖ < 2 := by
  have hp1 : 1 ≤ p := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp
      have h : (2 : ℕ) ^ (0 - 1) = 1 := by norm_num
      rw [h] at hrlt
      omega
    · exact hp
  have hul : u.length = r := hu.1
  have hvl : v.length = r := hv.1
  have hU0l : (u.map Prod.fst).length = r := by simpa using hul
  have hU1l : (u.map Prod.snd).length = r := by simpa using hul
  have hV0l : (v.map Prod.fst).length = r := by simpa using hvl
  have hV1l : (v.map Prod.snd).length = r := by simpa using hvl
  have hbU0 : ∀ x ∈ u.map Prod.fst, x.natAbs ≤ 2 ^ p := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact Work.ConvR.natAbs_fst_le_of_inDisc (hu.2 z hz)
  have hbU1 : ∀ x ∈ u.map Prod.snd, x.natAbs ≤ 2 ^ p := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact Work.ConvR.natAbs_snd_le_of_inDisc (hu.2 z hz)
  have hbV0 : ∀ x ∈ v.map Prod.fst, x.natAbs ≤ 2 ^ p := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact Work.ConvR.natAbs_fst_le_of_inDisc (hv.2 z hz)
  have hbV1 : ∀ x ∈ v.map Prod.snd, x.natAbs ≤ 2 ^ p := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact Work.ConvR.natAbs_snd_le_of_inDisc (hv.2 z hz)
  -- the four digit lists
  have hdig00 : kronDigits p (2 * r) (kronX0 u p) (kronY0 v p) =
      (List.range (2 * r)).map (fun m =>
        (convCoef (u.map Prod.fst) (v.map Prod.fst) m + (2 : ℤ) ^ (3 * p - 1)).toNat) := by
    have h := kronDigits_eq (p := p) (r := r) hp1 hU0l hV0l hbU0 hbV0 hrlt
    simpa only [kronX0, kronY0] using h
  have hdig01 : kronDigits p (2 * r) (kronX0 u p) (kronY1 v p) =
      (List.range (2 * r)).map (fun m =>
        (convCoef (u.map Prod.fst) (v.map Prod.snd) m + (2 : ℤ) ^ (3 * p - 1)).toNat) := by
    have h := kronDigits_eq (p := p) (r := r) hp1 hU0l hV1l hbU0 hbV1 hrlt
    simpa only [kronX0, kronY1] using h
  have hdig10 : kronDigits p (2 * r) (kronX1 u p) (kronY0 v p) =
      (List.range (2 * r)).map (fun m =>
        (convCoef (u.map Prod.snd) (v.map Prod.fst) m + (2 : ℤ) ^ (3 * p - 1)).toNat) := by
    have h := kronDigits_eq (p := p) (r := r) hp1 hU1l hV0l hbU1 hbV0 hrlt
    simpa only [kronX1, kronY0] using h
  have hdig11 : kronDigits p (2 * r) (kronX1 u p) (kronY1 v p) =
      (List.range (2 * r)).map (fun m =>
        (convCoef (u.map Prod.snd) (v.map Prod.snd) m + (2 : ℤ) ^ (3 * p - 1)).toNat) := by
    have h := kronDigits_eq (p := p) (r := r) hp1 hU1l hV1l hbU1 hbV1 hrlt
    simpa only [kronX1, kronY1] using h
  -- the negacyclic folds
  have hdel00 : ∀ m, m < 2 * r →
      2 * |convCoef (u.map Prod.fst) (v.map Prod.fst) m| < (2 : ℤ) ^ (3 * p) :=
    fun m _ => convCoef_two_mul_abs_lt hp1 hrlt hU0l hV0l hbU0 hbV0 m
  have hdel01 : ∀ m, m < 2 * r →
      2 * |convCoef (u.map Prod.fst) (v.map Prod.snd) m| < (2 : ℤ) ^ (3 * p) :=
    fun m _ => convCoef_two_mul_abs_lt hp1 hrlt hU0l hV1l hbU0 hbV1 m
  have hdel10 : ∀ m, m < 2 * r →
      2 * |convCoef (u.map Prod.snd) (v.map Prod.fst) m| < (2 : ℤ) ^ (3 * p) :=
    fun m _ => convCoef_two_mul_abs_lt hp1 hrlt hU1l hV0l hbU1 hbV0 m
  have hdel11 : ∀ m, m < 2 * r →
      2 * |convCoef (u.map Prod.snd) (v.map Prod.snd) m| < (2 : ℤ) ^ (3 * p) :=
    fun m _ => convCoef_two_mul_abs_lt hp1 hrlt hU1l hV1l hbU1 hbV1 m
  have hdelta00 : deltaL (kronDigits p (2 * r) (kronX0 u p) (kronY0 v p)) r =
      (List.range r).map (fun k => convCoef (u.map Prod.fst) (v.map Prod.fst) k -
        convCoef (u.map Prod.fst) (v.map Prod.fst) (k + r)) := by
    rw [hdig00]; exact deltaL_digitList hp1 hdel00
  have hdelta01 : deltaL (kronDigits p (2 * r) (kronX0 u p) (kronY1 v p)) r =
      (List.range r).map (fun k => convCoef (u.map Prod.fst) (v.map Prod.snd) k -
        convCoef (u.map Prod.fst) (v.map Prod.snd) (k + r)) := by
    rw [hdig01]; exact deltaL_digitList hp1 hdel01
  have hdelta10 : deltaL (kronDigits p (2 * r) (kronX1 u p) (kronY0 v p)) r =
      (List.range r).map (fun k => convCoef (u.map Prod.snd) (v.map Prod.fst) k -
        convCoef (u.map Prod.snd) (v.map Prod.fst) (k + r)) := by
    rw [hdig10]; exact deltaL_digitList hp1 hdel10
  have hdelta11 : deltaL (kronDigits p (2 * r) (kronX1 u p) (kronY1 v p)) r =
      (List.range r).map (fun k => convCoef (u.map Prod.snd) (v.map Prod.snd) k -
        convCoef (u.map Prod.snd) (v.map Prod.snd) (k + r)) := by
    rw [hdig11]; exact deltaL_digitList hp1 hdel11
  -- the two coordinate lists of the negacyclic product
  have hD0 : D0L r (kronDigits p (2 * r) (kronX0 u p) (kronY0 v p))
      (kronDigits p (2 * r) (kronX1 u p) (kronY1 v p)) =
      (List.range r).map (fun k => D0c u v r k) := by
    simp only [D0L, zsubL]
    rw [hdelta00, hdelta11, zipWith_map_same]
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    have e1 := convDsum (r := r) hU0l hV0l (m := k) (by omega)
    have e2 := convDsum (r := r) hU0l hV0l (m := k + r) (by omega)
    have e3 := convDsum (r := r) hU1l hV1l (m := k) (by omega)
    have e4 := convDsum (r := r) hU1l hV1l (m := k + r) (by omega)
    simp only [D0c, negaCoefL]
    rw [e1, e2, e3, e4]
  have hD1 : D1L r (kronDigits p (2 * r) (kronX0 u p) (kronY1 v p))
      (kronDigits p (2 * r) (kronX1 u p) (kronY0 v p)) =
      (List.range r).map (fun k => D1c u v r k) := by
    simp only [D1L, zaddL]
    rw [hdelta01, hdelta10, zipWith_map_same]
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    have e1 := convDsum (r := r) hU0l hV1l (m := k) (by omega)
    have e2 := convDsum (r := r) hU0l hV1l (m := k + r) (by omega)
    have e3 := convDsum (r := r) hU1l hV0l (m := k) (by omega)
    have e4 := convDsum (r := r) hU1l hV0l (m := k + r) (by omega)
    simp only [D1c, negaCoefL]
    rw [e1, e2, e3, e4]
  have hkron : kronVec p r u v = (List.range r).map
      (fun k => (Int.tdiv (D0c u v r k) ((2 : ℤ) ^ (p + Nat.clog 2 r)),
                 Int.tdiv (D1c u v r k) ((2 : ℤ) ^ (p + Nat.clog 2 r)))) := by
    simp only [kronVec, kronW]
    rw [hD0, hD1, zipWith_map_same]
  have hlen : (kronVec p r u v).length = r := by rw [hkron]; simp
  have hget : ∀ j : Fin r, (kronVec p r u v).getD j (0, 0) =
      (Int.tdiv (D0c u v r j) ((2 : ℤ) ^ (p + Nat.clog 2 r)),
       Int.tdiv (D1c u v r j) ((2 : ℤ) ^ (p + Nat.clog 2 r))) := by
    intro j
    rw [hkron, List.getD_eq_getElem _ _ (by simp)]
    simp
  have hstep : ∀ j : Fin r, inDisc p ((kronVec p r u v).getD j (0, 0)) ∧
      (2 : ℝ) ^ p * ‖fxC p ((kronVec p r u v).getD j (0, 0)) -
        ((r : ℂ))⁻¹ * negaMul r (fxVec p r u) (fxVec p r v) j‖ < 2 := by
    intro j
    have hfxu : ‖fxVec p r u‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
      intro i
      exact Work.ConvR.norm_fxC_le_one (Work.ConvR.InDiscVec.getD hu i)
    have hfxv : ‖fxVec p r v‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
      intro i
      exact Work.ConvR.norm_fxC_le_one (Work.ConvR.InDiscVec.getD hv i)
    have hZ : ‖negaMul r (fxVec p r u) (fxVec p r v) j‖ ≤ (r : ℝ) := by
      calc ‖negaMul r (fxVec p r u) (fxVec p r v) j‖
          ≤ ‖negaMul r (fxVec p r u) (fxVec p r v)‖ := norm_le_pi_norm _ j
        _ ≤ (r : ℝ) * ‖fxVec p r u‖ * ‖fxVec p r v‖ := Work.ConvR.negaNorm r _ _
        _ ≤ (r : ℝ) * 1 * 1 := by
            have h1 : (0 : ℝ) ≤ (r : ℝ) := by positivity
            have h3 : (0 : ℝ) ≤ ‖fxVec p r v‖ := norm_nonneg _
            have h4 : ‖fxVec p r u‖ * ‖fxVec p r v‖ ≤ 1 * 1 :=
              mul_le_mul hfxu hfxv h3 (by norm_num)
            calc (r : ℝ) * ‖fxVec p r u‖ * ‖fxVec p r v‖
                = (r : ℝ) * (‖fxVec p r u‖ * ‖fxVec p r v‖) := by ring
              _ ≤ (r : ℝ) * (1 * 1) := mul_le_mul_of_nonneg_left h4 h1
              _ = (r : ℝ) * 1 * 1 := by ring
        _ = (r : ℝ) := by ring
    have hex := negaIntCoeff (p := p) (r := r) hul hvl (j : ℕ) j.isLt
    have hres := truncApprox (p := p) (r := r) hrpow
      (Z := negaMul r (fxVec p r u) (fxVec p r v) j)
      (D0 := D0c u v r j) (D1 := D1c u v r j) hex hZ
    rw [← hget j] at hres
    exact hres
  constructor
  · refine ⟨hlen, ?_⟩
    intro z hz
    obtain ⟨i, hi, hzi⟩ := List.mem_iff_getElem.mp hz
    rw [← hzi]
    rw [← List.getD_eq_getElem _ _ hi]
    exact (hstep (Fin.cast hlen ⟨i, hi⟩)).1
  · intro j
    exact (hstep j).2

end Work.KronP
