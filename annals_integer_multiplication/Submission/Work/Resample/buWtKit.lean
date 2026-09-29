import Mathlib
import Submission.Work.Resample.buKit

/-!
# `Work.Resample.buWtKit`: shared toolkit for the weight element word `buWtElem`

Elementary facts shared by the construction of the element word of the one-dimensional `B̃`
resampling (paper §4): cost absorption into the `K (p+1)^K` shape, the uniform one-step budget
`buSBW p KS`, uniform size bounds (`isz z ≤ buSZ p`) for values obtained by adding or multiplying
numbers of at most `11p+210` bits, an adapter from the `vs = _ ∧ out = _` shape of a word spec to
`Pipe`, and the two cases of the guard in the definition of `buWt`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.Resample

open HvdH
open Work.Fx

/-! ## Cost absorption -/

/-- A single `K (p+1)^K` budget absorbs any `c (p+1)^d` with `c` a plain constant: the explicit
choice `K = 8 (c + d) + 8` works. -/
theorem le_powK {c d p : ℕ} (hB : 2 ≤ p + 1) (hc : 1 ≤ c) :
    c * (p + 1) ^ d ≤ (8 * (c + d) + 8) * (p + 1) ^ (8 * (c + d) + 8) := by
  have h1 : c ≤ 2 ^ (c + d) :=
    le_trans (le_of_lt (Nat.lt_two_pow_self (n := c))) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 : (2 : ℕ) ^ (c + d) ≤ (p + 1) ^ (c + d) := Nat.pow_le_pow_left hB _
  have h3 : c ≤ (p + 1) ^ (c + d) := le_trans h1 h2
  have h4 : (p + 1) ^ d ≤ (p + 1) ^ (c + d) := Nat.pow_le_pow_right (by omega) (by omega)
  have h5 : c * (p + 1) ^ d ≤ (p + 1) ^ (c + d) * (p + 1) ^ (c + d) := Nat.mul_le_mul h3 h4
  have h6 : (p + 1) ^ (c + d) * (p + 1) ^ (c + d) = (p + 1) ^ (2 * (c + d)) := by
    rw [← pow_add]; ring_nf
  have h7 : (p + 1) ^ (2 * (c + d)) ≤ (p + 1) ^ (8 * (c + d) + 8) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h8 : (p + 1) ^ (8 * (c + d) + 8) ≤ (8 * (c + d) + 8) * (p + 1) ^ (8 * (c + d) + 8) :=
    Nat.le_mul_of_pos_left _ (by omega)
  calc c * (p + 1) ^ d ≤ (p + 1) ^ (c + d) * (p + 1) ^ (c + d) := h5
    _ = (p + 1) ^ (2 * (c + d)) := h6
    _ ≤ (p + 1) ^ (8 * (c + d) + 8) := h7
    _ ≤ (8 * (c + d) + 8) * (p + 1) ^ (8 * (c + d) + 8) := h8

private lemma mul_pow_le' (B a k m N : ℕ) (hB : 1 ≤ B) (ha : a ≤ 2 ^ N) (hk : k ≤ 2 ^ N)
    (hm : 2 ^ N ≤ m) : a * B ^ k ≤ 2 ^ N * B ^ m := by
  have hkm : k ≤ m := le_trans hk hm
  have hpow : B ^ k ≤ B ^ m := pow_le_pow_right₀ hB hkm
  calc a * B ^ k ≤ 2 ^ N * B ^ k := Nat.mul_le_mul_right _ ha
    _ ≤ 2 ^ N * B ^ m := Nat.mul_le_mul_left _ hpow

/-- Four `(coefficient, exponent)` pairs are absorbed into a single `K (p+1)^K`. -/
theorem buCostSum4 (c1 K1 c2 K2 c3 K3 c4 K4 p : ℕ) :
    c1 * (p + 1) ^ K1 + (c2 * (p + 1) ^ K2 + (c3 * (p + 1) ^ K3 + c4 * (p + 1) ^ K4)) ≤
      (2 ^ (c1 + K1 + c2 + K2 + c3 + K3 + c4 + K4 + 20)) *
        (p + 1) ^ (2 ^ (c1 + K1 + c2 + K2 + c3 + K3 + c4 + K4 + 20)) := by
  let N := c1 + K1 + c2 + K2 + c3 + K3 + c4 + K4
  let B := p + 1
  show c1 * B ^ K1 + (c2 * B ^ K2 + (c3 * B ^ K3 + c4 * B ^ K4)) ≤
      2 ^ (N + 20) * B ^ (2 ^ (N + 20))
  have hB1 : 1 ≤ B := by omega
  have hN : N ≤ 2 ^ N := (Nat.lt_two_pow_self (n := N)).le
  have hc1 : c1 ≤ 2 ^ N := le_trans (by omega) hN
  have hc2 : c2 ≤ 2 ^ N := le_trans (by omega) hN
  have hc3 : c3 ≤ 2 ^ N := le_trans (by omega) hN
  have hc4 : c4 ≤ 2 ^ N := le_trans (by omega) hN
  have hK1 : K1 ≤ 2 ^ N := le_trans (by omega) hN
  have hK2 : K2 ≤ 2 ^ N := le_trans (by omega) hN
  have hK3 : K3 ≤ 2 ^ N := le_trans (by omega) hN
  have hK4 : K4 ≤ 2 ^ N := le_trans (by omega) hN
  have hm : 2 ^ N ≤ 2 ^ (N + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX1 : c1 * B ^ K1 ≤ 2 ^ N * B ^ (2 ^ (N + 20)) :=
    mul_pow_le' B c1 K1 (2 ^ (N + 20)) N hB1 hc1 hK1 hm
  have hX2 : c2 * B ^ K2 ≤ 2 ^ N * B ^ (2 ^ (N + 20)) :=
    mul_pow_le' B c2 K2 (2 ^ (N + 20)) N hB1 hc2 hK2 hm
  have hX3 : c3 * B ^ K3 ≤ 2 ^ N * B ^ (2 ^ (N + 20)) :=
    mul_pow_le' B c3 K3 (2 ^ (N + 20)) N hB1 hc3 hK3 hm
  have hX4 : c4 * B ^ K4 ≤ 2 ^ N * B ^ (2 ^ (N + 20)) :=
    mul_pow_le' B c4 K4 (2 ^ (N + 20)) N hB1 hc4 hK4 hm
  have hsum := add_le_add hX1 (add_le_add hX2 (add_le_add hX3 hX4))
  have h4 : 2 ^ N * B ^ (2 ^ (N + 20)) +
      (2 ^ N * B ^ (2 ^ (N + 20)) + (2 ^ N * B ^ (2 ^ (N + 20)) +
        2 ^ N * B ^ (2 ^ (N + 20)))) = 4 * (2 ^ N * B ^ (2 ^ (N + 20))) := by ring
  have h2 : 4 * (2 ^ N * B ^ (2 ^ (N + 20))) ≤ 2 ^ 20 * (2 ^ N * B ^ (2 ^ (N + 20))) :=
    Nat.mul_le_mul_right _ (by norm_num)
  have hkey : 2 ^ 20 * (2 ^ N * B ^ (2 ^ (N + 20))) = 2 ^ (N + 20) * B ^ (2 ^ (N + 20)) := by
    rw [← mul_assoc, ← pow_add, Nat.add_comm]
  calc c1 * B ^ K1 + (c2 * B ^ K2 + (c3 * B ^ K3 + c4 * B ^ K4))
      ≤ 2 ^ N * B ^ (2 ^ (N + 20)) + (2 ^ N * B ^ (2 ^ (N + 20)) +
          (2 ^ N * B ^ (2 ^ (N + 20)) + 2 ^ N * B ^ (2 ^ (N + 20)))) := hsum
    _ = 4 * (2 ^ N * B ^ (2 ^ (N + 20))) := h4
    _ ≤ 2 ^ 20 * (2 ^ N * B ^ (2 ^ (N + 20))) := h2
    _ = 2 ^ (N + 20) * B ^ (2 ^ (N + 20)) := hkey

/-! ## The uniform one-step budget -/

/-- Uniform bound on the cost of one primitive arithmetic step of the element word, for a library
whose constants are all `≤ KS`. -/
def buSBW (p KS : ℕ) : ℕ := KS * (buSZ p + 8) ^ 2

theorem buSZ_ge_big (p : ℕ) : 1000 ≤ buSZ p := by simp only [buSZ]; omega

theorem buSBW_le_pow (p KS : ℕ) : buSBW p KS ≤ (KS * 1000000 ^ 2) * (p + 1) ^ 4 := by
  have hp : 0 ≤ p := Nat.zero_le p
  have hexp : (p + 1) ^ 2 = p * p + 2 * p + 1 := by ring
  have h : buSZ p + 8 ≤ 1000000 * (p + 1) ^ 2 := by
    rw [hexp]
    simp only [buSZ]
    nlinarith [hp]
  calc buSBW p KS = KS * (buSZ p + 8) ^ 2 := rfl
    _ ≤ KS * (1000000 * (p + 1) ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 2)
    _ = (KS * 1000000 ^ 2) * (p + 1) ^ 4 := by ring

theorem le_buSBW_one {K KS p : ℕ} (hK : K ≤ KS) {v : ℕ} (hv : v ≤ buSZ p) :
    K * (v + 1) ≤ buSBW p KS := by
  rw [buSBW]
  calc K * (v + 1) ≤ KS * (buSZ p + 1) := Nat.mul_le_mul hK (by omega)
    _ ≤ KS * (buSZ p + 8) ^ 2 := Nat.mul_le_mul_left _ (by
        have h := buSZ_ge_big p
        have hexp : (buSZ p + 8) ^ 2 = buSZ p * buSZ p + 16 * buSZ p + 64 := by ring
        rw [hexp]; nlinarith)

theorem le_buSBW_two {K KS p : ℕ} (hK : K ≤ KS) {u v : ℕ} (hu : u ≤ buSZ p)
    (hv : v ≤ buSZ p) : K * (u + v) ≤ buSBW p KS := by
  rw [buSBW]
  calc K * (u + v) ≤ KS * (2 * buSZ p) := Nat.mul_le_mul hK (by omega)
    _ ≤ KS * (buSZ p + 8) ^ 2 := Nat.mul_le_mul_left _ (by
        have h := buSZ_ge_big p
        have hexp : (buSZ p + 8) ^ 2 = buSZ p * buSZ p + 16 * buSZ p + 64 := by ring
        rw [hexp]; nlinarith)

theorem le_buSBW_three {K KS p : ℕ} (hK : K ≤ KS) {u v w : ℕ} (hu : u ≤ buSZ p)
    (hv : v ≤ buSZ p) (hw : w ≤ buSZ p) : K * (u + v + w) ≤ buSBW p KS := by
  rw [buSBW]
  calc K * (u + v + w) ≤ KS * (3 * buSZ p) := Nat.mul_le_mul hK (by omega)
    _ ≤ KS * (buSZ p + 8) ^ 2 := Nat.mul_le_mul_left _ (by
        have h := buSZ_ge_big p
        have hexp : (buSZ p + 8) ^ 2 = buSZ p * buSZ p + 16 * buSZ p + 64 := by ring
        rw [hexp]; nlinarith)

theorem le_buSBW_mul {K KS p : ℕ} (hK : K ≤ KS) {u v : ℕ} (hu : u ≤ buSZ p)
    (hv : v ≤ buSZ p) : K * u * v ≤ buSBW p KS := by
  rw [buSBW]
  have hle : buSZ p * buSZ p ≤ (buSZ p + 8) ^ 2 := by
    have hexp : (buSZ p + 8) ^ 2 = buSZ p * buSZ p + 16 * buSZ p + 64 := by ring
    rw [hexp]; nlinarith [Nat.zero_le (buSZ p)]
  calc K * u * v ≤ KS * buSZ p * buSZ p := Nat.mul_le_mul (Nat.mul_le_mul hK hu) hv
    _ = KS * (buSZ p * buSZ p) := by ring
    _ ≤ KS * (buSZ p + 8) ^ 2 := Nat.mul_le_mul_left _ hle

theorem szl_le_buSZ_16 {p : ℕ} {A : List Val} (hAlen : A.length ≤ 16)
    (hA : ∀ v ∈ A, vsz v ≤ buSZ p) : szl A ≤ 16 * buSZ p :=
  le_trans (szl_le_len_mul hA) (Nat.mul_le_mul_right _ hAlen)

theorem le_buSBW_roll {K KS p : ℕ} (hK : K ≤ KS) {A : List Val} {k : ℕ}
    (hk : k ≤ 15) (hAlen : A.length ≤ 16) (hA : ∀ v ∈ A, vsz v ≤ buSZ p) :
    K * (k + 1) * (szl (A.take (k + 1)) + 1) ≤ buSBW p KS := by
  have hlen : (A.take (k + 1)).length ≤ 16 := by
    rw [List.length_take]; omega
  have hsum : szl (A.take (k + 1)) ≤ 16 * buSZ p :=
    szl_le_buSZ_16 hlen (fun v hv => hA v (List.mem_of_mem_take hv))
  have hle : 16 * (16 * buSZ p + 1) ≤ (buSZ p + 8) ^ 2 := by
    have h := buSZ_ge_big p
    have hexp : (buSZ p + 8) ^ 2 = buSZ p * buSZ p + 16 * buSZ p + 64 := by ring
    rw [hexp]; nlinarith
  rw [buSBW]
  calc K * (k + 1) * (szl (A.take (k + 1)) + 1)
      ≤ KS * 16 * (16 * buSZ p + 1) := Nat.mul_le_mul (Nat.mul_le_mul hK (by omega)) (by omega)
    _ = KS * (16 * (16 * buSZ p + 1)) := by ring
    _ ≤ KS * (buSZ p + 8) ^ 2 := Nat.mul_le_mul_left _ hle

/-! ## Uniform size bounds -/

/-- Any `A ≤ 30p+600` satisfies `A + 3 ≤ buSZ p` (the `buSZ` bound is quadratic). -/
theorem le_buSZ_lin {p A : ℕ} (h : A ≤ 30 * p + 600) : A + 3 ≤ buSZ p := by
  have hp : 0 ≤ p := Nat.zero_le p
  simp only [buSZ]
  nlinarith [hp]

/-- An integer of at most `A ≤ 30p+600` bits has `isz ≤ buSZ p`. -/
theorem isz_le_buSZ_of_lin {p A : ℕ} {z : ℤ} (hA : A ≤ 30 * p + 600)
    (h : z.natAbs ≤ 2 ^ A) : isz z ≤ buSZ p :=
  isz_le_buSZ_of (le_buSZ_lin hA) h

/-- Integers of at most `p` bits fit the uniform size bound. -/
theorem isz_le_buSZ_pow_p {p : ℕ} {z : ℤ} (h : z.natAbs ≤ 2 ^ p) : isz z ≤ buSZ p :=
  isz_le_buSZ_of_lin (by omega) h

/-- Integers of at most `2p` bits fit the uniform size bound. -/
theorem isz_le_buSZ_pow_2p {p : ℕ} {z : ℤ} (h : z.natAbs ≤ 2 ^ (2 * p)) : isz z ≤ buSZ p :=
  isz_le_buSZ_of_lin (by omega) h

/-- Integers of at most `11p + 210` bits fit the uniform size bound. -/
theorem isz_le_buSZ_11 {p A : ℕ} {z : ℤ} (hA : A ≤ 11 * p + 210) (h : z.natAbs ≤ 2 ^ A) :
    isz z ≤ buSZ p := isz_le_buSZ_of_lin (by omega) h

/-- The product of two integers of at most `11p+210` bits fits the uniform size bound. -/
theorem isz_mul_le_buSZ_11 {p A B : ℕ} {a b : ℤ} (hA : A ≤ 11 * p + 210)
    (hB : B ≤ 11 * p + 210) (ha : a.natAbs ≤ 2 ^ A) (hb : b.natAbs ≤ 2 ^ B) :
    isz (a * b) ≤ buSZ p := by
  refine isz_le_buSZ_of_lin (A := A + B) (by omega) ?_
  rw [Int.natAbs_mul]
  calc a.natAbs * b.natAbs ≤ 2 ^ A * 2 ^ B := Nat.mul_le_mul ha hb
    _ = 2 ^ (A + B) := by rw [pow_add]

/-- The sum of two integers of at most `11p+210` bits fits the uniform size bound. -/
theorem isz_add_le_buSZ_11 {p A B : ℕ} {a b : ℤ} (hA : A ≤ 11 * p + 210)
    (hB : B ≤ 11 * p + 210) (ha : a.natAbs ≤ 2 ^ A) (hb : b.natAbs ≤ 2 ^ B) :
    isz (a + b) ≤ buSZ p := by
  refine isz_le_buSZ_of_lin (A := max A B + 1) (by omega) ?_
  refine le_trans (Int.natAbs_add_le a b) ?_
  calc a.natAbs + b.natAbs ≤ 2 ^ A + 2 ^ B := Nat.add_le_add ha hb
    _ ≤ 2 ^ (max A B) + 2 ^ (max A B) :=
        Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
          (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
    _ = 2 ^ (max A B + 1) := by rw [pow_succ]; ring

/-- The difference of two integers of at most `11p+210` bits fits the uniform size bound. -/
theorem isz_sub_le_buSZ_11 {p A B : ℕ} {a b : ℤ} (hA : A ≤ 11 * p + 210)
    (hB : B ≤ 11 * p + 210) (ha : a.natAbs ≤ 2 ^ A) (hb : b.natAbs ≤ 2 ^ B) :
    isz (a - b) ≤ buSZ p := by
  have h : a - b = a + (-b) := by ring
  rw [h]
  refine isz_add_le_buSZ_11 hA hB ha ?_
  rwa [Int.natAbs_neg]

theorem isz_neg_le_buSZ_11 {p A : ℕ} {a : ℤ} (hA : A ≤ 11 * p + 210) (ha : a.natAbs ≤ 2 ^ A) :
    isz (-a) ≤ buSZ p := by
  rw [isz_neg]
  exact isz_le_buSZ_11 hA ha

/-! ## `Pipe` adapters -/

/-- A word spec of the shape `vs = A ++ rest ∧ out = B ++ rest` is a `Pipe` step. -/
theorem Pipe.ofHalves {main prog : Cmd} {A B : List Val} {c : ℕ}
    (h : ∀ rest : List Val, WordR main prog (fun vs => vs = A ++ rest)
      (fun vs out => vs = A ++ rest ∧ out = B ++ rest) (fun _ => c)) :
    Pipe main prog A B c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, ⟨_, hout⟩, hev, hn, hstk, hoth⟩ := h rest vs hvs s R hR
  exact ⟨out, s', n, hout, hev, hn, hstk, hoth⟩

/-! ## The guard of `buWt` -/

theorem auBnd_eq (p : ℕ) : auBnd p = ((p + 10 : ℕ) : ℤ) * (2 : ℤ) ^ auPrec p := rfl

theorem auEn_eq (p : ℕ) : auEn p = (2 : ℤ) ^ auPrec p := rfl

theorem auPrec_eq (p : ℕ) : auPrec p = 3 * p + 100 := rfl

theorem auPrec_sub_self (p : ℕ) : auPrec p - p = 2 * p + 100 := by simp only [auPrec]; omega

theorem auEnP_eq (p : ℕ) : auEnP p = (2 : ℤ) ^ (2 * p + 100) := by
  rw [auEnP, auPrec_sub_self]

/-- The guarded branch of `buWt`. -/
theorem buWt_of_le (p α s t : ℕ) (ℓ h : ℤ)
    (hg : buZ p α s t ℓ h ≤ ((p + 10 : ℕ) : ℤ) * (2 : ℤ) ^ auPrec p) :
    buWt p α s t ℓ h =
      Int.tdiv (auH p (-(buZ p α s t ℓ h)) (auNstep p)) ((2 : ℤ) ^ (auPrec p - p)) := by
  simp only [buWt, if_pos hg]

/-- The unguarded branch of `buWt`. -/
theorem buWt_of_not_le (p α s t : ℕ) (ℓ h : ℤ)
    (hg : ¬ (buZ p α s t ℓ h ≤ ((p + 10 : ℕ) : ℤ) * (2 : ℤ) ^ auPrec p)) :
    buWt p α s t ℓ h = 0 := by
  simp only [buWt, if_neg hg]

/-- The guard flag `if Z < auBnd p + 1 then 1 else 0` vanishes exactly above the guard bound. -/
theorem auFlgV_eq_zero_iff {p : ℕ} {Z : ℤ} :
    (if Z < auBnd p + 1 then (1 : ℤ) else 0) = 0 ↔ auBnd p < Z := by
  split
  · rename_i h
    constructor
    · intro hc; exact absurd hc (by norm_num)
    · intro hc; omega
  · rename_i h
    constructor
    · intro _; omega
    · intro _; rfl

/-- The guard flag is nonzero exactly when the guard holds. -/
theorem auFlgV_ne_zero_iff {p : ℕ} {Z : ℤ} :
    (if Z < auBnd p + 1 then (1 : ℤ) else 0) ≠ 0 ↔ Z ≤ auBnd p := by
  rw [ne_eq, auFlgV_eq_zero_iff]
  omega

end Work.Resample
