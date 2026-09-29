import Mathlib
import Submission.Work.Params.defs
import Submission.Work.Params.basic
import Submission.Work.Params.tsfacts
import Submission.Work.Params.uparfacts
import Submission.Work.Params.rparbig
import Submission.Work.Params.vszlemmas

/-!
# Size bounds for the lists `t`, `s` of the parameters (paper §5.1)

For `n` with `65755586 ≤ n.size` (the "big `n`" regime of the `Params` area, where the *constant*
values `6, 12d², F, Q, F·Q, …` all have `Nat.size ≤ n.size + 4`) we bound the encoding lengths of
the three integer lists the program manipulates:

* `intList (List.range d)`  — an absolute constant,
* `intList (tsPar n)` and `intList (ssPar n)` — bounded by `(n.size + 6) * (d + 2)`.

The last two follow from the element bounds `m.size ≤ n.size + 10` (every element is a small
multiple of `r` or of `u₀ ≤ r + F·Q`) together with
`vsz (ofList xs) ≤ (xs.length + 1) * (B + 1)` (`vszlemmas.vsz_ofList_le`).
-/

set_option autoImplicit false

namespace Work.Params

open HvdH

/-- Unfolding of `vsz` at `Val.int`. -/
theorem vsz_int_natCast (m : ℕ) : vsz (Val.int (m : ℤ)) = m.size + 2 := by
  rw [vsz, Work.IntLib.vsz_int, isz]
  simp

/-- **Size of an `intList`.**  `vsz (intList l) = Σ (m.size + 2) + l.length + 1`, so if every
element of `l` has `m.size ≤ B` then `vsz (intList l) ≤ (l.length + 1) * (B + 3)`.

Proved by recursion on the list: this way the unfolding of `HvdH.intList` is used only through its
own definition (`HvdH.intList (a :: t) = Val.cons (Val.int a) (HvdH.intList t)`), never through a
lambda written out by hand (which the elaborator may give a different `ℕ → ℤ` coercion than the one
inside the definition of `HvdH.intList`). -/
theorem vsz_intList_le : ∀ (l : List ℕ) (B : ℕ), (∀ m ∈ l, m.size ≤ B) →
    vsz (HvdH.intList l) ≤ (l.length + 1) * (B + 3)
  | [], B, _ => by
      have h1 : vsz (HvdH.intList ([] : List ℕ)) = 1 := by decide
      rw [h1, List.length_nil]
      simp only [Nat.zero_add, one_mul]
      omega
  | a :: t, B, h => by
      have ih : vsz (HvdH.intList t) ≤ (t.length + 1) * (B + 3) :=
        vsz_intList_le t B (fun m hm => h m (List.mem_cons_of_mem a hm))
      have hrec : vsz (HvdH.intList (a :: t))
          = vsz (Val.int (a : ℤ)) + vsz (HvdH.intList t) + 1 := by
        have h1 : HvdH.intList (a :: t) = Val.cons (Val.int (a : ℤ)) (HvdH.intList t) := rfl
        rw [h1, Work.Params.vsz_cons]
      have ha : vsz (Val.int (a : ℤ)) = a.size + 2 := vsz_int_natCast a
      have hB : a.size ≤ B := h a List.mem_cons_self
      have hlen : (a :: t).length + 1 = t.length + 2 := by simp [List.length_cons]
      rw [hrec, ha, hlen]
      calc a.size + 2 + vsz (HvdH.intList t) + 1
          ≤ B + 2 + ((t.length + 1) * (B + 3)) + 1 := by omega
        _ = (t.length + 2) * (B + 3) := by ring

/-! ## Numeric bounds for the parameters -/

/-- `b = clog 2 n ≤ n.size`. -/
theorem bpar_le_size (n : ℕ) : bpar n ≤ n.size := by
  rw [bpar, Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
  exact le_of_lt ((Nat.size_le).mp le_rfl)

/-- `k_T ≤ n.size + 3`.  Crude estimate: `(4n+b-1)/b ≤ 4n+b ≤ 5·2^{n.size} ≤ 2^{n.size+3}`. -/
theorem kTpar_le_size (n : ℕ) : kTpar n ≤ n.size + 3 := by
  have hn : n < 2 ^ n.size := (Nat.size_le).mp le_rfl
  have h4n : 4 * n < 4 * 2 ^ n.size := Nat.mul_lt_mul_of_pos_left hn (by norm_num)
  have hs : n.size < 2 ^ n.size := Nat.lt_two_pow_self
  have hb : bpar n ≤ n.size := bpar_le_size n
  rw [kTpar, Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
  calc (4 * n + bpar n - 1) / bpar n ≤ 4 * n + bpar n - 1 := Nat.div_le_self _ _
    _ ≤ 4 * n + bpar n := Nat.sub_le _ _
    _ ≤ 4 * n + n.size := by omega
    _ ≤ 4 * 2 ^ n.size + 2 ^ n.size := by omega
    _ = 5 * 2 ^ n.size := by ring
    _ ≤ 8 * 2 ^ n.size := Nat.mul_le_mul_right _ (by norm_num)
    _ = 2 ^ (n.size + 3) := by
        rw [show n.size + 3 = 3 + n.size by omega, pow_add, pow_three']
        ring

/-- `⌈k_T/d⌉ ≤ k_T`. -/
theorem krpar_le_kTpar (n : ℕ) : krpar n ≤ kTpar n := by
  have hDpos : 0 < HvdH.D := by norm_num [HvdH.D]
  unfold krpar
  rw [Nat.div_le_iff_le_mul hDpos]
  have hD1 : 1 ≤ HvdH.D := hDpos
  have h : kTpar n ≤ kTpar n * HvdH.D := by
    simpa using Nat.mul_le_mul_left (kTpar n) hD1
  omega

/-- `r = 2^{⌈k_T/d⌉} ≤ 2^{n.size + 3}`. -/
theorem rpar_le_pow (n : ℕ) : rpar n ≤ 2 ^ (n.size + 3) := by
  calc rpar n = 2 ^ krpar n := rfl
    _ ≤ 2 ^ kTpar n := Nat.pow_le_pow_right (by norm_num) (krpar_le_kTpar n)
    _ = Tpar n := rfl
    _ ≤ 2 ^ (n.size + 3) := Nat.pow_le_pow_right (by norm_num) (kTpar_le_size n)

/-- `(rpar n).size ≤ n.size + 4`. -/
theorem rpar_size_le (n : ℕ) : (rpar n).size ≤ n.size + 4 := by
  rw [Nat.size_le]
  exact lt_of_le_of_lt (rpar_le_pow n)
    (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-- `2^j + 1 ≤ 2^k` when `j + 1 ≤ k`. -/
theorem two_pow_add_one_le {j k : ℕ} (h : j + 1 ≤ k) : 2 ^ j + 1 ≤ 2 ^ k := by
  have h1 : 2 ^ j + 1 ≤ 2 ^ (j + 1) := by
    rw [pow_add, pow_one]
    have : (1:ℕ) ≤ 2 ^ j := Nat.one_le_two_pow
    omega
  exact le_trans h1 (Nat.pow_le_pow_right (by norm_num) h)

/-- `2 * 2^e < 2^k` when `e + 2 ≤ k`. -/
theorem two_mul_two_pow_lt {e k : ℕ} (h : e + 2 ≤ k) : 2 * 2 ^ e < 2 ^ k := by
  have h1 : 2 * 2 ^ e = 2 ^ (1 + e) := by rw [pow_add, pow_one]
  rw [h1]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- `4 * 2^e < 2^k` when `e + 3 ≤ k`. -/
theorem four_mul_two_pow_lt {e k : ℕ} (h : e + 3 ≤ k) : 4 * 2 ^ e < 2 ^ k := by
  have h1 : 4 * 2 ^ e = 2 ^ (2 + e) := by rw [pow_add]; ring
  rw [h1]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- `F·Q ≤ 2^{n.size}` (this is where the threshold `65755586` comes from). -/
theorem Ffac_mul_Qall_le (n : ℕ) (hsz : 65755586 ≤ n.size) : Ffac * Qall ≤ 2 ^ n.size := by
  have h19008 : 19008 ≤ n.size := by omega
  have hE : 19021 * 3456 ≤ n.size - 19008 := by omega
  have hQ : Qall ≤ 2 ^ (n.size - 19008) := Qall_le_pow _ hE
  calc Ffac * Qall ≤ 2 ^ 19008 * 2 ^ (n.size - 19008) := Nat.mul_le_mul Ffac_le_two_pow hQ
    _ = 2 ^ (19008 + (n.size - 19008)) := (pow_add 2 19008 (n.size - 19008)).symm
    _ = 2 ^ n.size := by rw [Nat.add_sub_of_le h19008]

/-- `F·d ≤ 2^{n.size}`. -/
theorem Ffac_mul_D_le (n : ℕ) (hsz : 65755586 ≤ n.size) : Ffac * HvdH.D ≤ 2 ^ n.size :=
  le_trans FfacD_le_pow (Nat.pow_le_pow_right (by norm_num) (by omega : 19019 ≤ n.size))

/-- `L = ⌊(2d-1)r/(4d)⌋ + 1 ≤ r + 1`. -/
theorem Lpar_le_rpar_add_one (n : ℕ) : Lpar n ≤ rpar n + 1 := by
  unfold Lpar
  have hle : rpar n * (2 * HvdH.D - 1) / (4 * HvdH.D) ≤ rpar n := by
    have h1 : rpar n * (2 * HvdH.D - 1) / (4 * HvdH.D)
        ≤ rpar n * (2 * HvdH.D - 1) / (2 * HvdH.D - 1) :=
      Nat.div_le_div_left (by norm_num [HvdH.D]) (by norm_num [HvdH.D])
    rwa [Nat.mul_div_cancel _ (by norm_num [HvdH.D] : 0 < 2 * HvdH.D - 1)] at h1
  omega

/-- `u₀ < 2^{n.size + 5}`: `u₀ < L + F·Q ≤ (r+1) + 2^{n.size} < 2·2^{n.size+3}`. -/
theorem upar_lt_pow (n : ℕ) (hsz : 65755586 ≤ n.size) : upar n < 2 ^ (n.size + 5) := by
  have hu : upar n < Lpar n + Ffac * Qall := (uparfacts n).2.1
  have hLr : Lpar n ≤ rpar n + 1 := Lpar_le_rpar_add_one n
  have h1 : 2 ^ n.size + 1 ≤ 2 ^ (n.size + 3) := two_pow_add_one_le (by omega)
  have h2 : Lpar n ≤ 2 ^ (n.size + 3) + 1 := by have := rpar_le_pow n; omega
  have h3 : Ffac * Qall ≤ 2 ^ n.size := Ffac_mul_Qall_le n hsz
  have hu' : upar n < 2 * 2 ^ (n.size + 3) := by omega
  exact lt_trans hu' (two_mul_two_pow_lt (by omega))

/-! ## Element bounds for `tsPar` and `ssPar` -/

/-- Every element of `tsPar n` is `r/2` or `r`, hence `< 2^{n.size+4} ≤ 2^{n.size+10}`. -/
theorem tsPar_elems_le (n : ℕ) (hsz : 65755586 ≤ n.size) :
    ∀ m ∈ tsPar n, m.size ≤ n.size + 10 := by
  intro m hm
  rw [Nat.size_le]
  unfold tsPar at hm
  rw [List.mem_map] at hm
  obtain ⟨k, _hk, rfl⟩ := hm
  by_cases hkdp : k < dpar n
  · rw [if_pos hkdp]
    have hle : rpar n / 2 ≤ rpar n := Nat.div_le_self _ _
    calc rpar n / 2 ≤ rpar n := hle
      _ ≤ 2 ^ (n.size + 3) := rpar_le_pow n
      _ < 2 ^ (n.size + 10) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  · rw [if_neg hkdp]
    calc rpar n ≤ 2 ^ (n.size + 3) := rpar_le_pow n
      _ < 2 ^ (n.size + 10) := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- Every element of `ssPar n` is `u₀ + F(k+1)` or `2u₀ - 1 + 2F(k-d'+1)`, so `< 2^{n.size+10}`. -/
theorem ssPar_elems_le (n : ℕ) (hsz : 65755586 ≤ n.size) :
    ∀ m ∈ ssPar n, m.size ≤ n.size + 10 := by
  intro m hm
  rw [Nat.size_le]
  unfold ssPar at hm
  rw [List.mem_map] at hm
  obtain ⟨k, hk, rfl⟩ := hm
  rw [List.mem_range] at hk
  have hup : upar n < 2 ^ (n.size + 5) := upar_lt_pow n hsz
  have hFD : Ffac * HvdH.D ≤ 2 ^ n.size := Ffac_mul_D_le n hsz
  have hkD : k + 1 ≤ HvdH.D := by omega
  have h5 : 2 ^ n.size ≤ 2 ^ (n.size + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_cases hkdp : k < dpar n
  · rw [if_pos hkdp]
    have hmul : Ffac * (k + 1) ≤ Ffac * HvdH.D := Nat.mul_le_mul_left _ hkD
    have hmid : upar n + Ffac * (k + 1) < 2 * 2 ^ (n.size + 5) := by omega
    exact lt_trans hmid (two_mul_two_pow_lt (by omega))
  · rw [if_neg hkdp]
    have hk1 : k - dpar n + 1 ≤ HvdH.D := by omega
    have hmul : 2 * Ffac * (k - dpar n + 1) ≤ 2 * Ffac * HvdH.D :=
      Nat.mul_le_mul_left _ hk1
    have hFD2 : 2 * Ffac * HvdH.D ≤ 2 * 2 ^ n.size := by
      have h1 : 2 * Ffac * HvdH.D = 2 * (Ffac * HvdH.D) := by ring
      rw [h1]
      exact Nat.mul_le_mul_left 2 hFD
    have hmid : 2 * upar n - 1 + 2 * Ffac * (k - dpar n + 1) < 4 * 2 ^ (n.size + 5) := by
      have h2u : 2 * upar n < 2 * 2 ^ (n.size + 5) :=
        Nat.mul_lt_mul_of_pos_left hup (by norm_num)
      have h4 : 2 * 2 ^ n.size ≤ 2 * 2 ^ (n.size + 5) := Nat.mul_le_mul_left 2 h5
      omega
    exact lt_trans hmid (four_mul_two_pow_lt (by omega))

/-! ## The main statement -/

theorem listSizesBig (n : ℕ) (hsz : 65755586 ≤ n.size) :
    (HvdH.intList (List.range HvdH.D)).enc.length ≤ n.size + 4 ∧
    (HvdH.intList (Work.Params.tsPar n)).enc.length ≤ (n.size + 6) * (HvdH.D + 2) ∧
    (HvdH.intList (Work.Params.ssPar n)).enc.length ≤ (n.size + 6) * (HvdH.D + 2) := by
  refine ⟨?_, ?_, ?_⟩
  · -- the list `0, 1, …, d-1`
    have hb : ∀ m ∈ List.range HvdH.D, m.size ≤ 11 := by
      intro m hm
      rw [List.mem_range] at hm
      exact (Nat.size_le).mpr (lt_of_lt_of_le hm (by norm_num [HvdH.D]))
    have h := vsz_intList_le (List.range HvdH.D) 11 hb
    have hL : (List.range HvdH.D).length = HvdH.D := by simp
    rw [hL] at h
    have harith : (HvdH.D + 1) * (11 + 3) ≤ n.size + 4 := by simp only [HvdH.D]; omega
    exact le_trans h harith
  · -- the transform sizes `tᵢ`
    have h := vsz_intList_le (tsPar n) (n.size + 10) (tsPar_elems_le n hsz)
    have hL : (tsPar n).length = HvdH.D := by simp [tsPar]
    rw [hL] at h
    have harith : (HvdH.D + 1) * (n.size + 10 + 3) ≤ (n.size + 6) * (HvdH.D + 2) := by
      simp only [HvdH.D]; nlinarith [hsz]
    exact le_trans h harith
  · -- the `sᵢ`
    have h := vsz_intList_le (ssPar n) (n.size + 10) (ssPar_elems_le n hsz)
    have hL : (ssPar n).length = HvdH.D := by simp [ssPar]
    rw [hL] at h
    have harith : (HvdH.D + 1) * (n.size + 10 + 3) ≤ (n.size + 6) * (HvdH.D + 2) := by
      simp only [HvdH.D]; nlinarith [hsz]
    exact le_trans h harith

end Work.Params
