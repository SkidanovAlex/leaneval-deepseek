import Mathlib
import Submission.Work.Resample.buKit

/-!
# Toolbox for the Horner word `Work.Resample.buHornerWord`

This module fixes the uniform size bound `buSZ p` (from `Work.Resample.buKit`), the uniform
per-step cost bound `buHSB p KS`, the size estimates for the integers that occur in the Horner
recursion, and the elementary identities that turn the fixed-point recursion `auH` into a
program loop.  Nothing here is a program: the words are assembled in `Work.Resample.buHornerWord`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH
open Work.Fx

/-! ## Cost helpers -/

/-- Uniform bound on the cost of one primitive arithmetic step of the Horner word, for a
library whose constants are all `≤ KS`. -/
def buHSB (p KS : ℕ) : ℕ := KS * (buSZ p + 8) ^ 2

theorem buSB_mono {p KS KS' : ℕ} (h : KS ≤ KS') : buHSB p KS ≤ buHSB p KS' :=
  Nat.mul_le_mul_right _ h

theorem buSZ_ge48 (p : ℕ) : 48 ≤ buSZ p := by simp only [buSZ]; omega

theorem le_buSB_one {K KS p : ℕ} (hK : K ≤ KS) {v : ℕ} (hv : v ≤ buSZ p) :
    K * (v + 1) ≤ buHSB p KS := by
  rw [buHSB]
  calc K * (v + 1) ≤ KS * (buSZ p + 1) := Nat.mul_le_mul hK (by omega)
    _ ≤ KS * (buSZ p + 8) ^ 2 := Nat.mul_le_mul_left _ (by
        have h := buSZ_ge48 p; nlinarith)

theorem le_buSB_two {K KS p : ℕ} (hK : K ≤ KS) {u v : ℕ} (hu : u ≤ buSZ p)
    (hv : v ≤ buSZ p) : K * (u + v) ≤ buHSB p KS := by
  rw [buHSB]
  calc K * (u + v) ≤ KS * (2 * buSZ p) := Nat.mul_le_mul hK (by omega)
    _ ≤ KS * (buSZ p + 8) ^ 2 := Nat.mul_le_mul_left _ (by
        have h := buSZ_ge48 p; nlinarith)

theorem le_buSB_three {K KS p : ℕ} (hK : K ≤ KS) {u v w : ℕ} (hu : u ≤ buSZ p)
    (hv : v ≤ buSZ p) (hw : w ≤ buSZ p) : K * (u + v + w) ≤ buHSB p KS := by
  rw [buHSB]
  calc K * (u + v + w) ≤ KS * (3 * buSZ p) := Nat.mul_le_mul hK (by omega)
    _ ≤ KS * (buSZ p + 8) ^ 2 := Nat.mul_le_mul_left _ (by
        have h := buSZ_ge48 p; nlinarith)

theorem le_buSB_mul {K KS p : ℕ} (hK : K ≤ KS) {u v : ℕ} (hu : u ≤ buSZ p)
    (hv : v ≤ buSZ p) : K * u * v ≤ buHSB p KS := by
  rw [buHSB]
  have hle : buSZ p * buSZ p ≤ (buSZ p + 8) ^ 2 := by
    nlinarith [Nat.zero_le (buSZ p)]
  calc K * u * v ≤ KS * buSZ p * buSZ p := Nat.mul_le_mul (Nat.mul_le_mul hK hu) hv
    _ = KS * (buSZ p * buSZ p) := by ring
    _ ≤ KS * (buSZ p + 8) ^ 2 := Nat.mul_le_mul_left _ hle

theorem le_buSB_roll {K KS p : ℕ} (hK : K ≤ KS) {A : List Val} {k : ℕ}
    (hk : k ≤ 7) (hAlen : A.length ≤ 8) (hA : ∀ v ∈ A, vsz v ≤ buSZ p) :
    K * (k + 1) * (szl (A.take (k + 1)) + 1) ≤ buHSB p KS := by
  have hlen : (A.take (k + 1)).length ≤ 8 := by
    rw [List.length_take]; omega
  have hsum : szl (A.take (k + 1)) ≤ 8 * buSZ p :=
    le_trans (szl_le_len_mul (A := A.take (k + 1)) (n := buSZ p)
      (fun v hv => hA v (List.mem_of_mem_take hv))) (Nat.mul_le_mul_right _ hlen)
  have hle : 8 * (8 * buSZ p + 1) ≤ (buSZ p + 8) ^ 2 := by
    have h := buSZ_ge48 p; nlinarith
  rw [buHSB]
  calc K * (k + 1) * (szl (A.take (k + 1)) + 1)
      ≤ KS * 8 * (8 * buSZ p + 1) := Nat.mul_le_mul (Nat.mul_le_mul hK (by omega)) (by omega)
    _ = KS * (8 * (8 * buSZ p + 1)) := by ring
    _ ≤ KS * (buSZ p + 8) ^ 2 := Nat.mul_le_mul_left _ hle

/-! ## Size estimates -/

theorem isz_mono {a b : ℤ} (h : a.natAbs ≤ b.natAbs) : isz a ≤ isz b := by
  simp only [isz]
  exact Nat.add_le_add_right (Nat.size_le_size h) 2

theorem isz_Z_le_buSZ {p : ℕ} {Z : ℤ} (hZ : Z.natAbs ≤ 2 ^ (11 * p + 210)) :
    isz Z ≤ buSZ p :=
  isz_le_buSZ_of (p := p) (A := 11 * p + 210) (by simp only [buSZ]; omega) hZ

theorem isz_p_le_buSZ_HK (p : ℕ) : isz ((p : ℤ)) ≤ buSZ p := by
  apply isz_le_buSZ_of (p := p) (A := p) (by simp only [buSZ]; omega)
  rw [Int.natAbs_natCast]
  exact le_of_lt (Nat.lt_two_pow_self)

theorem isz_auNstep_le_buSZ (p : ℕ) : isz ((auNstep p : ℕ) : ℤ) ≤ buSZ p := by
  apply isz_le_buSZ_of (p := p) (A := 3 * p + 101) (by simp only [buSZ]; omega)
  rw [Int.natAbs_natCast]
  have h1 : auNstep p = 2 * (3 * p + 100) := by simp only [auNstep, auPrec]
  rw [h1]
  have h3 := Nat.lt_two_pow_self (n := 3 * p + 100)
  calc 2 * (3 * p + 100) ≤ 2 * 2 ^ (3 * p + 100) :=
        le_of_lt (Nat.mul_lt_mul_of_pos_left h3 (by norm_num))
    _ = 2 ^ (3 * p + 101) := by rw [pow_succ]; ring

theorem isz_Ns_sub_le_buSZ (p i : ℕ) : isz (((auNstep p - i : ℕ) : ℤ)) ≤ buSZ p := by
  apply isz_le_buSZ_of (p := p) (A := 3 * p + 101) (by simp only [buSZ]; omega)
  rw [Int.natAbs_natCast]
  calc auNstep p - i ≤ auNstep p := Nat.sub_le _ _
    _ = 2 * (3 * p + 100) := by simp only [auNstep, auPrec]
    _ ≤ 2 * 2 ^ (3 * p + 100) :=
        le_of_lt (Nat.mul_lt_mul_of_pos_left (Nat.lt_two_pow_self (n := 3 * p + 100)) (by norm_num))
    _ = 2 ^ (3 * p + 101) := by rw [pow_succ]; ring

theorem isz_zero_le_buSZ (p : ℕ) : isz (0 : ℤ) ≤ buSZ p := isz_const_le_buSZ p 0 (by omega)

theorem isz_one_le_buSZ (p : ℕ) : isz (1 : ℤ) ≤ buSZ p := isz_const_le_buSZ p 1 (by omega)

theorem isz_flag_le_buSZ {p : ℕ} {b : Prop} [Decidable b] :
    isz (if b then (1 : ℤ) else 0) ≤ buSZ p := by
  split
  · exact isz_one_le_buSZ p
  · exact isz_zero_le_buSZ p

theorem isz_sub_one_le_buSZ {p : ℕ} {d : ℤ} (hd1 : 1 ≤ d) (hd : isz d ≤ buSZ p) :
    isz (d - 1) ≤ buSZ p := by
  refine le_trans (isz_mono ?_) hd
  have h2 : 0 ≤ d - 1 := by omega
  have h3 : 0 ≤ d := by omega
  have h5 : ((d - 1).natAbs : ℤ) ≤ (d.natAbs : ℤ) := by
    rw [Int.natAbs_of_nonneg h2, Int.natAbs_of_nonneg h3]
    omega
  exact_mod_cast h5

theorem isz_tdiv_le_buSZ {p : ℕ} {a b : ℤ} (ha : isz a ≤ buSZ p) :
    isz (Int.tdiv a b) ≤ buSZ p :=
  le_trans (isz_mono (Work.Fx.natAbs_tdiv_le a b)) ha

/-- The Horner iterate at `i` has at most `buHQ p - 1` bits. -/
theorem natAbs_auH_le_buHQs (p : ℕ) (Z : ℤ) (i : ℕ) (hp : 100 ≤ p)
    (hZ : Z.natAbs ≤ 2 ^ (11 * p + 210)) (hi : i ≤ auNstep p) :
    (auH p Z i).natAbs ≤ 2 ^ (buHQ p - 1) := natAbs_auH_le_buHQ p Z i hp hZ hi

/-- The product `Z · Q` stays inside the uniform size bound. -/
theorem natAbs_mul_auH_le (p : ℕ) (hp : 100 ≤ p) (Z : ℤ) (hZ : Z.natAbs ≤ 2 ^ (11 * p + 210))
    (i : ℕ) (hi : i ≤ auNstep p) : (Z * auH p Z i).natAbs ≤ 2 ^ (buSZ p - 3) := by
  have hQ := natAbs_auH_le_buHQ p Z i hp hZ hi
  rw [Int.natAbs_mul]
  calc Z.natAbs * (auH p Z i).natAbs ≤ 2 ^ (11 * p + 210) * 2 ^ (buHQ p - 1) :=
        Nat.mul_le_mul hZ hQ
    _ = 2 ^ (11 * p + 210 + (buHQ p - 1)) := by rw [← pow_add]
    _ ≤ 2 ^ (buSZ p - 3) := Nat.pow_le_pow_right (by norm_num) (by simp only [buSZ, buHQ]; omega)

theorem isz_mul_auH_le (p : ℕ) (hp : 100 ≤ p) (Z : ℤ) (hZ : Z.natAbs ≤ 2 ^ (11 * p + 210))
    (i : ℕ) (hi : i ≤ auNstep p) : isz (Z * auH p Z i) ≤ buSZ p := by
  refine isz_le_buSZ (lt_of_le_of_lt (natAbs_mul_auH_le p hp Z hZ i hi) ?_)
  apply Nat.pow_lt_pow_right one_lt_two
  have h := buSZ_ge48 p; omega

/-! ## Cast and recurrence identities -/

theorem Ns_sub_cast (p i : ℕ) (hi : i ≤ auNstep p) :
    (((auNstep p - i : ℕ) : ℤ)) = (auNstep p : ℤ) - (i : ℤ) := Nat.cast_sub hi

theorem Ns_sub_succ_cast (p i : ℕ) (hi : i + 1 ≤ auNstep p) :
    (((auNstep p - (i + 1) : ℕ) : ℤ)) = (((auNstep p - i : ℕ) : ℤ)) - 1 := by
  have h1 : i ≤ auNstep p := by omega
  rw [Nat.cast_sub hi, Nat.cast_sub h1]
  push_cast
  ring

/-- One step of the recursion `auH`, with the divisor written as the natural `auNstep p - i`. -/
theorem auH_succ_eq (p : ℕ) (Z : ℤ) (i : ℕ) (hi : i ≤ auNstep p) :
    auH p Z (i + 1) =
      auEn p + Int.tdiv (Int.tdiv (Z * auH p Z i) (auEn p))
        (((auNstep p - i : ℕ) : ℤ)) := by
  rw [show auH p Z (i + 1) = (2 : ℤ) ^ auPrec p +
      Int.tdiv (Int.tdiv (Z * auH p Z i) ((2 : ℤ) ^ auPrec p))
        ((auNstep p : ℤ) - (i : ℤ)) from rfl]
  rw [Ns_sub_cast p i hi]
  rfl

/-! ## Value-size helpers -/

theorem vsz_int_le_buSZ {p : ℕ} {z : ℤ} (h : isz z ≤ buSZ p) : vsz (HvdH.Val.int z) ≤ buSZ p := by
  simpa [Work.Fx.vsz_int] using h

theorem vsz_int_p_le_buSZ (p : ℕ) : vsz (HvdH.Val.int (p : ℤ)) ≤ buSZ p :=
  vsz_int_le_buSZ (isz_p_le_buSZ_HK p)

theorem vsz_mem_le_cons {p : ℕ} {a : Val} {l : List Val} (ha : vsz a ≤ buSZ p)
    (hl : ∀ v ∈ l, vsz v ≤ buSZ p) : ∀ v ∈ a :: l, vsz v ≤ buSZ p := by
  intro v hv
  rcases List.mem_cons.mp hv with h | h
  · rw [h]; exact ha
  · exact hl v h

theorem vsz_mem_le_nil {p : ℕ} : ∀ v ∈ ([] : List Val), vsz v ≤ buSZ p := by simp

theorem vsz_mem_le_append {p : ℕ} {A B : List Val} (hA : ∀ v ∈ A, vsz v ≤ buSZ p)
    (hB : ∀ v ∈ B, vsz v ≤ buSZ p) : ∀ v ∈ A ++ B, vsz v ≤ buSZ p := by
  intro v hv
  rcases List.mem_append.mp hv with h | h
  · exact hA v h
  · exact hB v h

/-- Absorbing a constant factor into a larger exponent. -/
theorem pow_mul_le (M e p : ℕ) (hM : 1 ≤ M) (hp : 2 ≤ p + 1) :
    M * (p + 1) ^ e ≤ (4 * M + e + 1) * (p + 1) ^ (4 * M + e) := by
  have hpow : M ≤ (p + 1) ^ (4 * M) := by
    have h1 : M ≤ 2 ^ M := le_of_lt (Nat.lt_two_pow_self (n := M))
    have h2 : (2 : ℕ) ^ M ≤ 2 ^ (4 * M) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : (2 : ℕ) ^ (4 * M) ≤ (p + 1) ^ (4 * M) := Nat.pow_le_pow_left hp _
    exact le_trans h1 (le_trans h2 h3)
  have h4 : M * (p + 1) ^ e ≤ (p + 1) ^ (4 * M + e) := by
    calc M * (p + 1) ^ e ≤ (p + 1) ^ (4 * M) * (p + 1) ^ e := Nat.mul_le_mul_right _ hpow
      _ = (p + 1) ^ (4 * M + e) := by rw [← pow_add]
  calc M * (p + 1) ^ e ≤ (p + 1) ^ (4 * M + e) := h4
    _ ≤ (4 * M + e + 1) * (p + 1) ^ (4 * M + e) :=
        Nat.le_mul_of_pos_left _ (by omega)

end Work.Resample
