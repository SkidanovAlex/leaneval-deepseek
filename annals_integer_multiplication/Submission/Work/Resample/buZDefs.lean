import Mathlib
import Submission.Work.Resample.buWtKit
import Submission.Work.Resample.buHornerKit
import Submission.Work.Resample.buKit
import Submission.Work.Resample.buDefs
import Submission.Work.Fx.piWord

/-!
# Intermediate values of the one-dimensional `buZ` word (`Work.Resample.buZW`)

The word `buZW` computes the working-scale exponent
`buZ p α s t ℓ h = ⌊2^P·π α² N/s²⌋` of the one-dimensional `B̃` weight table from the two indices
`ℓ`, `h`.  This module fixes, as named integers, every intermediate value of that word --- the
products `t·ℓ`, `t·h`, the two `β`-values `buBeta s t ℓ`, `buBeta s t (ℓ+h)`, the numerator
`buZN` and the final quotient `buZZ` --- so that the word and its size estimates can refer to them,
and collects the elementary size toolkit and the fact that the canonical block `buCB p α s t`
consists of small values.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH

/-! ## The intermediate values -/

/-- `t·ℓ` -/
def buZU1 (t : ℕ) (ℓ : ℤ) : ℤ := (t : ℤ) * ℓ

/-- `t·h` -/
def buZV (t : ℕ) (h : ℤ) : ℤ := (t : ℤ) * h

/-- `t·ℓ + t·h = t(ℓ+h)` -/
def buZU2 (t : ℕ) (ℓ h : ℤ) : ℤ := buZU1 t ℓ + buZV t h

/-- `2·(t·ℓ)` -/
def buZD1 (t : ℕ) (ℓ : ℤ) : ℤ := buZU1 t ℓ + buZU1 t ℓ

/-- `2s` -/
def buZE (s : ℕ) : ℤ := (s : ℤ) + (s : ℤ)

/-- `2·(t·ℓ) + s` -/
def buZA1 (t : ℕ) (ℓ : ℤ) (s : ℕ) : ℤ := buZD1 t ℓ + (s : ℤ)

/-- `[tℓ/s] = ⌊(2tℓ+s)/(2s)⌋` -/
def buZQ1 (t : ℕ) (ℓ : ℤ) (s : ℕ) : ℤ := Int.fdiv (buZA1 t ℓ s) (buZE s)

/-- `s·[tℓ/s]` -/
def buZR1 (t : ℕ) (ℓ : ℤ) (s : ℕ) : ℤ := (s : ℤ) * buZQ1 t ℓ s

/-- `β_ℓ = t·ℓ - s·[tℓ/s]` -/
def buZB1 (t : ℕ) (ℓ : ℤ) (s : ℕ) : ℤ := buZU1 t ℓ - buZR1 t ℓ s

/-- `2·(t(ℓ+h))` -/
def buZD2 (t : ℕ) (ℓ h : ℤ) : ℤ := buZU2 t ℓ h + buZU2 t ℓ h

/-- `2·(t(ℓ+h)) + s` -/
def buZA2 (t : ℕ) (ℓ h : ℤ) (s : ℕ) : ℤ := buZD2 t ℓ h + (s : ℤ)

/-- `⌊(2t(ℓ+h)+s)/(2s)⌋` -/
def buZQ2 (t : ℕ) (ℓ h : ℤ) (s : ℕ) : ℤ := Int.fdiv (buZA2 t ℓ h s) (buZE s)

/-- `s·⌊(2t(ℓ+h)+s)/(2s)⌋` -/
def buZR2 (t : ℕ) (ℓ h : ℤ) (s : ℕ) : ℤ := (s : ℤ) * buZQ2 t ℓ h s

/-- `β_{ℓ+h}` -/
def buZB2 (t : ℕ) (ℓ h : ℤ) (s : ℕ) : ℤ := buZU2 t ℓ h - buZR2 t ℓ h s

/-- `t·h + β_ℓ` -/
def buZA (t : ℕ) (ℓ h : ℤ) (s : ℕ) : ℤ := buZB1 t ℓ s + buZV t h

/-- `(t·h + β_ℓ)²` -/
def buZSq (t : ℕ) (ℓ h : ℤ) (s : ℕ) : ℤ := buZA t ℓ h s * buZA t ℓ h s

/-- `β_{ℓ+h}²` -/
def buZB2sq (t : ℕ) (ℓ h : ℤ) (s : ℕ) : ℤ := buZB2 t ℓ h s * buZB2 t ℓ h s

/-- `N = (t h + β_ℓ)² - β_{ℓ+h}²` -/
def buZN (t : ℕ) (ℓ h : ℤ) (s : ℕ) : ℤ := buZSq t ℓ h s - buZB2sq t ℓ h s

/-- `α²` -/
def buZA2c (α : ℕ) : ℤ := (α : ℤ) * (α : ℤ)

/-- `α²·N` -/
def buZA2N (t : ℕ) (ℓ h : ℤ) (s : ℕ) (α : ℕ) : ℤ := buZN t ℓ h s * buZA2c α

/-- `π·α²·N` -/
def buZP (p : ℕ) (t : ℕ) (ℓ h : ℤ) (s : ℕ) (α : ℕ) : ℤ := auPi p * buZA2N t ℓ h s α

/-- `s²` -/
def buZS2 (s : ℕ) : ℤ := (s : ℤ) * (s : ℤ)

/-- The value produced by the `buZ` word. -/
def buZZ (p α s t : ℕ) (ℓ h : ℤ) : ℤ := Int.tdiv (buZP p t ℓ h s α) (buZS2 s)

/-- The program of the `buZ` word is a right-nested sequence of commands. -/
def buZProgR : List Cmd → Cmd
  | [] => .skip
  | c :: cs => .seq c (buZProgR cs)

/-! ## Size toolkit -/

/-- `isz ((n : ℤ)) ≤ buSZ p` for `n < 2^p`. -/
theorem isz_natCast_lt_buSZ {p n : ℕ} (h : n < 2 ^ p) : isz ((n : ℤ)) ≤ buSZ p :=
  isz_le_buSZ_of (A := p) (z := (n : ℤ)) (by simp only [buSZ]; omega) (by
    rw [Int.natAbs_natCast]; exact le_of_lt h)

/-- Uniform bit bound for the intermediate values of the `buZ` word. -/
abbrev buZBnd (p : ℕ) : ℕ := 14 * p + 300

theorem buZBnd_add (p : ℕ) : buZBnd p + 3 ≤ buSZ p := by simp only [buZBnd, buSZ]; omega

/-- Every intermediate value of the `buZ` word has at most `buZBnd p` bits. -/
theorem buZ_isz_le {p A : ℕ} {z : ℤ} (hA : A ≤ buZBnd p) (h : z.natAbs ≤ 2 ^ A) :
    isz z ≤ buSZ p :=
  isz_le_buSZ_of (A := A) (by have := buZBnd_add p; omega) h

theorem buZ_na_mul {a b : ℤ} {A B : ℕ} (ha : a.natAbs ≤ 2 ^ A) (hb : b.natAbs ≤ 2 ^ B) :
    (a * b).natAbs ≤ 2 ^ (A + B) := by
  rw [Int.natAbs_mul, pow_add]
  exact Nat.mul_le_mul ha hb

theorem buZ_na_add {a b : ℤ} {A B : ℕ} (ha : a.natAbs ≤ 2 ^ A) (hb : b.natAbs ≤ 2 ^ B) :
    (a + b).natAbs ≤ 2 ^ (max A B + 1) := by
  refine le_trans (Int.natAbs_add_le a b) ?_
  calc a.natAbs + b.natAbs ≤ 2 ^ A + 2 ^ B := Nat.add_le_add ha hb
    _ ≤ 2 ^ (max A B) + 2 ^ (max A B) :=
        Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
          (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
    _ = 2 ^ (max A B + 1) := by rw [pow_succ]; ring

theorem buZ_na_sub {a b : ℤ} {A B : ℕ} (ha : a.natAbs ≤ 2 ^ A) (hb : b.natAbs ≤ 2 ^ B) :
    (a - b).natAbs ≤ 2 ^ (max A B + 1) := by
  refine le_trans (Int.natAbs_sub_le a b) ?_
  calc a.natAbs + b.natAbs ≤ 2 ^ A + 2 ^ B := Nat.add_le_add ha hb
    _ ≤ 2 ^ (max A B) + 2 ^ (max A B) :=
        Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
          (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
    _ = 2 ^ (max A B + 1) := by rw [pow_succ]; ring

/-- Floor division never increases `natAbs` by more than one (the numerator may be negative). -/
theorem buZ_na_fdiv_gen {a b : ℤ} (hb : 0 < b) : (Int.fdiv a b).natAbs ≤ a.natAbs + 1 := by
  rw [Int.fdiv_eq_ediv_of_nonneg a (le_of_lt hb), Int.natAbs_ediv]
  have h := Nat.div_le_self a.natAbs b.natAbs
  split <;> omega

theorem buZ_na_fdiv {a b : ℤ} {A : ℕ} (ha : a.natAbs ≤ 2 ^ A) (hb : 0 < b) :
    (Int.fdiv a b).natAbs ≤ 2 ^ (A + 1) := by
  refine le_trans (buZ_na_fdiv_gen hb) ?_
  have h1 : 1 ≤ 2 ^ A := Nat.one_le_two_pow
  have h2 : 2 ^ (A + 1) = 2 ^ A + 2 ^ A := by rw [pow_succ]; ring
  omega

theorem buZ_na_tdiv {a b : ℤ} {A : ℕ} (ha : a.natAbs ≤ 2 ^ A) :
    (Int.tdiv a b).natAbs ≤ 2 ^ A :=
  le_trans (Work.Fx.natAbs_tdiv_le a b) ha

/-- Powers of two are monotone. -/
theorem buZ_pow_mono {A B : ℕ} (h : A ≤ B) : 2 ^ A ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) h

/-- The canonical parameter block `buCB p α s t` consists of small values. -/
theorem buCB_small (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α)
    (hp : 100 ≤ p) (htp : t < 2 ^ p) (hαp : α ^ 2 < p) :
    ∀ v ∈ buCB p α s t, vsz v ≤ buSZ p := by
  have hsp : s < 2 ^ p := lt_trans hst htp
  have hα2p : α < 2 ^ p := by
    have h1 : α < p := by nlinarith
    exact lt_of_lt_of_le h1 (le_of_lt (Nat.lt_two_pow_self))
  have hm2p : ((egM p α : ℕ) : ℤ).natAbs ≤ 2 ^ p := by
    rw [Int.natAbs_natCast]
    refine le_trans (egM_le p α) ?_
    have := Nat.lt_two_pow_self (n := p); omega
  have hN2p : ((egN p α s t : ℕ) : ℤ).natAbs ≤ 2 ^ (2 * p) := by
    rw [Int.natAbs_natCast]
    have h1 : egN p α s t ≤ p * s := by
      have h := Nat.div_le_self (p * s - 1) (α ^ 2 * (t - s))
      have h3 : 1 ≤ p * s := Nat.mul_pos (by omega) (by omega)
      show (p * s - 1) / (α ^ 2 * (t - s)) + 1 ≤ p * s
      omega
    have hp1 : p ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self (n := p))
    calc egN p α s t ≤ p * s := h1
      _ ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul hp1 (le_of_lt hsp)
      _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf
  intro v hv
  simp only [buCB, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact vsz_int_le_buSZ (isz_le_buSZ_pow_p (z := (p : ℤ)) (by
      rw [Int.natAbs_natCast]; exact le_of_lt (Nat.lt_two_pow_self (n := p))))
  · exact vsz_int_le_buSZ (isz_natCast_lt_buSZ hα2p)
  · exact vsz_int_le_buSZ (isz_natCast_lt_buSZ hsp)
  · exact vsz_int_le_buSZ (isz_natCast_lt_buSZ htp)
  · exact vsz_int_le_buSZ (buZ_isz_le (A := p) (by simp only [buZBnd]; omega) hm2p)
  · exact vsz_int_le_buSZ (buZ_isz_le (A := 2 * p) (by simp only [buZBnd]; omega) hN2p)
  · exact vsz_int_le_buSZ (isz_auPi_le_buSZ p)

end Work.Resample
