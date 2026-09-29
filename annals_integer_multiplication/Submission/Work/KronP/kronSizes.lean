import Mathlib
import Submission.Work.KronP.defs
import Submission.Work.KronP.math
import Submission.Work.ConvR.basic

/-!
# Sizes for the Kronecker word (paper Lemma 2.5)

`kronSizes` is the uniform size budget used by the Kronecker-substitution word of
`Submission/Work/KronP/`.  With

`B = (r+1)·(p+1)² + vsz (cvecVal u) + vsz (cvecVal v)`

and `u, v ∈ C̃◦^r` (`r ≥ 2`, `p ≥ 1`), every integer/list value that the word reads or writes
is at most a factor `1000` below `B`: the constants `3p, 2r, C = digitOffset p (2r), 2^{p+κ}`
(with `r = 2^κ`), the packed products `X_j, Y_k = pack U_j/V_k (3p)` (each of size `≤ 3rp`), and
the value encodings of all the (pairs and quadruples of) those integers.

The mathematical content is elementary: the packed products have at most `3rp = O(rp)` bits and
`B ≥ (r+1)(p+1)²` dominates every linear-in-`rp` expression produced above.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KronP

open HvdH

/-! ## Elementary size facts -/

/-- The bit size of a natural number is at most the number itself. -/
theorem kp_size_le_self (n : ℕ) : n.size ≤ n := Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))

/-- The empty value has encoding `[nil]`. -/
theorem kp_vsz_val_nil : vsz (Val.nil : Val) = 1 := rfl

/-- Encoding size of a two-element list of integers. -/
theorem kp_vsz_zsVal_pair (a b : ℤ) : vsz (zsVal [a, b]) = isz a + isz b + 3 := by
  simp only [zsVal, List.map_cons, List.map_nil, ofList, List.foldr_cons, List.foldr_nil]
  rw [Work.ConvR.vsz_cons, Work.ConvR.vsz_cons, Work.ConvR.vsz_int, Work.ConvR.vsz_int,
    kp_vsz_val_nil]
  omega

/-- Encoding size of a four-element list of integers. -/
theorem kp_vsz_zsVal_quad (a b c d : ℤ) :
    vsz (zsVal [a, b, c, d]) = isz a + isz b + isz c + isz d + 5 := by
  simp only [zsVal, List.map_cons, List.map_nil, ofList, List.foldr_cons, List.foldr_nil]
  rw [Work.ConvR.vsz_cons, Work.ConvR.vsz_cons, Work.ConvR.vsz_cons, Work.ConvR.vsz_cons,
    Work.ConvR.vsz_int, Work.ConvR.vsz_int, Work.ConvR.vsz_int, Work.ConvR.vsz_int,
    kp_vsz_val_nil]
  omega

/-- A coefficient list of length `r` with all entries of absolute value `≤ 2^p` packs into an
integer of at most `3rp` bits. -/
theorem kp_pack_natAbs_size_le {l : List ℤ} {p r : ℕ} (hp : 1 ≤ p) (hr : 1 ≤ r)
    (hlen : l.length = r) (hb : ∀ x ∈ l, x.natAbs ≤ 2 ^ p) :
    (pack l (3 * p)).natAbs.size ≤ 3 * r * p := by
  have h := pack_natAbs_le l (3 * p) (2 ^ p) (by omega) hb
  rw [hlen] at h
  have h2 : (pack l (3 * p)).natAbs ≤ 2 ^ (3 * p * (r - 1) + p + 1) := by
    calc (pack l (3 * p)).natAbs ≤ 2 ^ p * 2 ^ (3 * p * (r - 1) + 1) := h
      _ = 2 ^ (3 * p * (r - 1) + p + 1) := by rw [← pow_add]; ring_nf
  have hsub : 3 * p * (r - 1) = 3 * p * r - 3 * p := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have h3pr : 3 * p ≤ 3 * p * r := by simpa using Nat.mul_le_mul_left (3 * p) hr
  have hlt : 3 * p * (r - 1) + p + 1 < 3 * r * p := by
    have h1 : 3 * p * (r - 1) + 3 * p = 3 * p * r := by rw [hsub, Nat.sub_add_cancel h3pr]
    have h2 : p + 1 < 3 * p := by omega
    have h3 : 3 * p * r = 3 * r * p := by ring
    omega
  exact Nat.size_le.mpr (lt_of_le_of_lt h2 (Nat.pow_lt_pow_right (by norm_num) hlt))

/-! ## Absorbing the elementary bounds into the budget shape `12rp + 6p + 4r + 13` -/

theorem kp_abs_three_p (p r : ℕ) : (3 * p).size ≤ 12 * r * p + 6 * p + 4 * r + 11 := by
  have h := kp_size_le_self (3 * p)
  nlinarith

theorem kp_abs_two_r (p r : ℕ) : (2 * r).size ≤ 12 * r * p + 6 * p + 4 * r + 11 := by
  have h := kp_size_le_self (2 * r)
  nlinarith

theorem kp_abs_p (p r : ℕ) : p.size ≤ 12 * r * p + 6 * p + 4 * r + 11 := by
  have h := kp_size_le_self p
  nlinarith

theorem kp_abs_r (p r : ℕ) : r.size ≤ 12 * r * p + 6 * p + 4 * r + 11 := by
  have h := kp_size_le_self r
  nlinarith

/-- `C = digitOffset p (2r)` has at most `6rp + 2r + 1` bits. -/
theorem kp_dig_size (p r : ℕ) (hp : 1 ≤ p) :
    (digitOffset p (2 * r)).natAbs.size ≤ 6 * r * p + 2 * r + 1 := by
  rw [Nat.size_le]
  have h0 := digitOffset_natAbs_le p (2 * r) hp
  calc (digitOffset p (2 * r)).natAbs ≤ 2 * r * 2 ^ (3 * p * (2 * r)) := h0
    _ = 2 ^ (3 * p * (2 * r)) * (2 * r) := by ring
    _ ≤ 2 ^ (3 * p * (2 * r)) * 2 ^ (2 * r) :=
        Nat.mul_le_mul_left _ (le_of_lt (Nat.lt_two_pow_self (n := 2 * r)))
    _ = 2 ^ (3 * p * (2 * r) + 2 * r) := by rw [← pow_add]
    _ < 2 ^ (6 * r * p + 2 * r + 1) := by
        apply Nat.pow_lt_pow_right (by norm_num)
        nlinarith

theorem kp_abs_dig (p r : ℕ) (hp : 1 ≤ p) :
    (digitOffset p (2 * r)).natAbs.size ≤ 12 * r * p + 6 * p + 4 * r + 11 := by
  have h := kp_dig_size p r hp
  nlinarith

/-- `2^(p + clog 2 r)` has at most `p + r + 1` bits. -/
theorem kp_abs_pow (p r : ℕ) (hr : 1 ≤ r) :
    (2 ^ (p + Nat.clog 2 r)).size ≤ 12 * r * p + 6 * p + 4 * r + 11 := by
  have hcl : Nat.clog 2 r ≤ r := by
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    exact le_of_lt (Nat.lt_two_pow_self (n := r))
  rw [Nat.size_pow]
  nlinarith

theorem kp_abs_rp {p r t : ℕ} (h : t ≤ r * (p + 3) + r + 1) :
    t ≤ 12 * r * p + 6 * p + 4 * r + 13 := by nlinarith

theorem kp_abs_three {p r t : ℕ} (h : t ≤ 3 * r * p + 2) :
    t ≤ 12 * r * p + 6 * p + 4 * r + 13 := by nlinarith

theorem kp_abs_pair {p r a b : ℕ} (ha : a ≤ 3 * r * p + 2) (hb : b ≤ 3 * r * p + 2) :
    a + b + 3 ≤ 12 * r * p + 6 * p + 4 * r + 13 := by nlinarith

theorem kp_abs_quad {p r a b c d : ℕ} (ha : a ≤ 3 * r * p + 2) (hb : b ≤ 3 * r * p + 2)
    (hc : c ≤ 3 * r * p + 2) (hd : d ≤ 3 * r * p + 2) :
    a + b + c + d + 5 ≤ 12 * r * p + 6 * p + 4 * r + 13 := by nlinarith

/-- The budget shape `12rp + 6p + 4r + 13` is absorbed by `1000·(r+1)(p+1)²`. -/
theorem kp_budget_le {p r t : ℕ} (hp : 1 ≤ p) (hr : 2 ≤ r)
    (h : t ≤ 12 * r * p + 6 * p + 4 * r + 13) : t ≤ 1000 * ((r + 1) * (p + 1) ^ 2) := by
  nlinarith [hp, hr]

/-! ## The size budget -/

theorem kronSizes (p r : ℕ) (u v : List (ℤ × ℤ)) (B : ℕ)
    (hB : B = (r + 1) * (p + 1) ^ 2 + HvdH.vsz (HvdH.cvecVal u) + HvdH.vsz (HvdH.cvecVal v))
    (hp : 1 ≤ p) (hr : 2 ≤ r) (hu : HvdH.InDiscVec p r u) (hv : HvdH.InDiscVec p r v) :
    1 ≤ B ∧
    HvdH.isz (3 * p : ℤ) ≤ 1000 * B ∧ HvdH.isz (2 * r : ℤ) ≤ 1000 * B ∧
    HvdH.isz (Work.KronP.digitOffset p (2 * r)) ≤ 1000 * B ∧
    HvdH.isz ((2 : ℤ) ^ (p + Nat.clog 2 r)) ≤ 1000 * B ∧
    HvdH.isz (p : ℤ) ≤ 1000 * B ∧ HvdH.isz (r : ℤ) ≤ 1000 * B ∧
    HvdH.vsz (Work.KronP.zsVal (u.map Prod.fst)) ≤ 1000 * B ∧
    HvdH.vsz (Work.KronP.zsVal (u.map Prod.snd)) ≤ 1000 * B ∧
    HvdH.vsz (Work.KronP.zsVal (v.map Prod.fst)) ≤ 1000 * B ∧
    HvdH.vsz (Work.KronP.zsVal (v.map Prod.snd)) ≤ 1000 * B ∧
    HvdH.isz (Work.KronP.kronX0 u p) ≤ 1000 * B ∧ HvdH.isz (Work.KronP.kronX1 u p) ≤ 1000 * B ∧
    HvdH.isz (Work.KronP.kronY0 v p) ≤ 1000 * B ∧ HvdH.isz (Work.KronP.kronY1 v p) ≤ 1000 * B ∧
    HvdH.vsz (Work.KronP.zsVal [Work.KronP.kronX0 u p, Work.KronP.kronX1 u p]) ≤ 1000 * B ∧
    HvdH.vsz (Work.KronP.zsVal [Work.KronP.kronY0 v p, Work.KronP.kronY1 v p]) ≤ 1000 * B ∧
    HvdH.vsz (Work.KronP.zsVal [Work.KronP.kronX0 u p, Work.KronP.kronX1 u p,
      Work.KronP.kronX0 u p, Work.KronP.kronX1 u p]) ≤ 1000 * B ∧
    HvdH.vsz (Work.KronP.zsVal [Work.KronP.kronY0 v p, Work.KronP.kronY1 v p,
      Work.KronP.kronY1 v p, Work.KronP.kronY0 v p]) ≤ 1000 * B := by
  obtain ⟨hu_len, hu_disc⟩ := hu
  obtain ⟨hv_len, hv_disc⟩ := hv
  have hr1 : 1 ≤ r := by omega
  have hMB : (r + 1) * (p + 1) ^ 2 ≤ B := by rw [hB]; omega
  have hbig : 12 * r * p + 6 * p + 4 * r + 13 ≤ 1000 * B :=
    le_trans (kp_budget_le hp hr le_rfl) (Nat.mul_le_mul_left _ hMB)
  have key : ∀ t : ℕ, t ≤ 12 * r * p + 6 * p + 4 * r + 13 → t ≤ 1000 * B :=
    fun t ht => le_trans ht hbig
  have keyI : ∀ z : ℤ, z.natAbs.size ≤ 12 * r * p + 6 * p + 4 * r + 11 → isz z ≤ 1000 * B := by
    intro z hz
    apply key
    simp only [isz]
    omega
  have hbU0 : ∀ x ∈ u.map Prod.fst, x.natAbs ≤ 2 ^ p := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact Work.ConvR.natAbs_fst_le_of_inDisc (hu_disc z hz)
  have hbU1 : ∀ x ∈ u.map Prod.snd, x.natAbs ≤ 2 ^ p := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact Work.ConvR.natAbs_snd_le_of_inDisc (hu_disc z hz)
  have hbV0 : ∀ x ∈ v.map Prod.fst, x.natAbs ≤ 2 ^ p := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact Work.ConvR.natAbs_fst_le_of_inDisc (hv_disc z hz)
  have hbV1 : ∀ x ∈ v.map Prod.snd, x.natAbs ≤ 2 ^ p := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact Work.ConvR.natAbs_snd_le_of_inDisc (hv_disc z hz)
  have hlenU0 : (u.map Prod.fst).length = r := by simp [hu_len]
  have hlenU1 : (u.map Prod.snd).length = r := by simp [hu_len]
  have hlenV0 : (v.map Prod.fst).length = r := by simp [hv_len]
  have hlenV1 : (v.map Prod.snd).length = r := by simp [hv_len]
  have hX0 : isz (kronX0 u p) ≤ 3 * r * p + 2 := by
    have h := kp_pack_natAbs_size_le hp hr1 hlenU0 hbU0
    simp only [kronX0, isz]
    omega
  have hX1 : isz (kronX1 u p) ≤ 3 * r * p + 2 := by
    have h := kp_pack_natAbs_size_le hp hr1 hlenU1 hbU1
    simp only [kronX1, isz]
    omega
  have hY0 : isz (kronY0 v p) ≤ 3 * r * p + 2 := by
    have h := kp_pack_natAbs_size_le hp hr1 hlenV0 hbV0
    simp only [kronY0, isz]
    omega
  have hY1 : isz (kronY1 v p) ≤ 3 * r * p + 2 := by
    have h := kp_pack_natAbs_size_le hp hr1 hlenV1 hbV1
    simp only [kronY1, isz]
    omega
  have hVU0 : vsz (zsVal (u.map Prod.fst)) ≤ r * (p + 3) + r + 1 := by
    have h := vsz_zsVal_le (fun x hx => Work.ConvR.isz_le_of_natAbs_le (hbU0 x hx))
    rwa [hlenU0] at h
  have hVU1 : vsz (zsVal (u.map Prod.snd)) ≤ r * (p + 3) + r + 1 := by
    have h := vsz_zsVal_le (fun x hx => Work.ConvR.isz_le_of_natAbs_le (hbU1 x hx))
    rwa [hlenU1] at h
  have hVV0 : vsz (zsVal (v.map Prod.fst)) ≤ r * (p + 3) + r + 1 := by
    have h := vsz_zsVal_le (fun x hx => Work.ConvR.isz_le_of_natAbs_le (hbV0 x hx))
    rwa [hlenV0] at h
  have hVV1 : vsz (zsVal (v.map Prod.snd)) ≤ r * (p + 3) + r + 1 := by
    have h := vsz_zsVal_le (fun x hx => Work.ConvR.isz_le_of_natAbs_le (hbV1 x hx))
    rwa [hlenV1] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans ?_ hMB
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  · apply keyI
    have h : (((3 * p : ℕ)) : ℤ) = 3 * (p : ℤ) := by push_cast; ring
    rw [← h, Int.natAbs_natCast]
    exact kp_abs_three_p p r
  · apply keyI
    have h : (((2 * r : ℕ)) : ℤ) = 2 * (r : ℤ) := by push_cast; ring
    rw [← h, Int.natAbs_natCast]
    exact kp_abs_two_r p r
  · apply keyI
    exact kp_abs_dig p r hp
  · apply keyI
    have h : ((2 : ℤ) ^ (p + Nat.clog 2 r)).natAbs = 2 ^ (p + Nat.clog 2 r) := by simp
    rw [h]
    exact kp_abs_pow p r hr1
  · apply keyI
    rw [Int.natAbs_natCast]
    exact kp_abs_p p r
  · apply keyI
    rw [Int.natAbs_natCast]
    exact kp_abs_r p r
  · apply key
    exact le_trans hVU0 (kp_abs_rp le_rfl)
  · apply key
    exact le_trans hVU1 (kp_abs_rp le_rfl)
  · apply key
    exact le_trans hVV0 (kp_abs_rp le_rfl)
  · apply key
    exact le_trans hVV1 (kp_abs_rp le_rfl)
  · apply key
    exact le_trans hX0 (kp_abs_three le_rfl)
  · apply key
    exact le_trans hX1 (kp_abs_three le_rfl)
  · apply key
    exact le_trans hY0 (kp_abs_three le_rfl)
  · apply key
    exact le_trans hY1 (kp_abs_three le_rfl)
  · apply key
    rw [kp_vsz_zsVal_pair]
    exact kp_abs_pair hX0 hX1
  · apply key
    rw [kp_vsz_zsVal_pair]
    exact kp_abs_pair hY0 hY1
  · apply key
    rw [kp_vsz_zsVal_quad]
    exact kp_abs_quad hX0 hX1 hX0 hX1
  · apply key
    rw [kp_vsz_zsVal_quad]
    exact kp_abs_quad hY0 hY1 hY1 hY0

end Work.KronP
