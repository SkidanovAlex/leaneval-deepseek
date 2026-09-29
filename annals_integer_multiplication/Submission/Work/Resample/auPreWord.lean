import Mathlib
import Submission.Work.Resample.auKit
import Submission.Work.Resample.auPreKit
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auPrepDefs

/-!
# `Work.Resample.auPreWord`: the setup word of the weight element word

`auPreWord` takes the five values

`[int p, int α, int t, int N, int (auPi p)]`

(only `rest` below them) and pushes the six values

`[int (auFlg p α t N), int (auNstep p), int (auEn p), int (auZ p α t N), int (auEn p),
 int (auEn2 p α)]`

on top of `rest`, at a cost bounded by `300 · auSB p KS` where each single library call costs at
most `auSB p KS = KS · (auSZ p + 8)²`.

The program is a straight-line chain of 74 library calls (each of which is a word of
`KernelLib`/`IntLib`, so each costs at most the uniform one-step budget `auSB p KS`):

* `auEn2 p α = 2^(auPrec p − p)·(2α)`: `prec = 3p + 100`, `prec − p`, `2^(prec−p)`, `α + α`, product;
* `auEn p = 2^auPrec p` and `auNstep p = 2·auPrec p`: `prec = 3p + 100`, `2^prec` and `prec + prec`;
* `auZ p α t N = ⌊(auPi p)·N/(α²t²)⌋`: `α²`, `t²`, their product, `N·π`, and the quotient;
* `auBnd p = (p+10)·2^auPrec p`, compared with `auZ p α t N` to produce `auFlg p α t N`.

The division is guarded against the degenerate case `α = 0` (the statement does *not* assume
`1 ≤ α`): with `e = (if α = 0 then 1 else 0)` the word computes `⌊(Nπ)/(t²α² + e)⌋ · (1 − e)`,
which is `⌊(Nπ)/(t²α²)⌋` for `α ≠ 0` and `0` for `α = 0` (and `auZ p 0 t N = 0` because
`Int.tdiv _ 0 = 0`); the divisor `t²α² + e` is never zero, so the library division applies.

The intermediate values are collected in the auxiliary namespace `AuPreWordAux`: each one is a
`def` whose body is *exactly* the term produced by the corresponding library call, so that every
`Pipe`/`WordR` statement in the proof mentions only short names (this keeps the proof fast).
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace Work.Resample

open HvdH


namespace AuPreWordAux

/-! ## The intermediate values of the word

Each `def` below is the *exact* term computed by the corresponding library step (up to
definitional unfolding), so that every statement in the proof only mentions the short names. -/

def eeX3 (p : ℕ) : ℤ := (3 : ℤ) * (p : ℤ)
def eeW1 (p : ℕ) : ℤ := (100 : ℤ) + 3 * (p : ℤ)
def eeW2 (p : ℕ) : ℤ := (100 : ℤ) + 3 * (p : ℤ) - (p : ℤ)
def eeA2 (α : ℕ) : ℤ := (α : ℤ) * (α : ℤ)
def eeT2 (t : ℕ) : ℤ := (t : ℤ) * (t : ℤ)
def eeAA2 (α : ℕ) : ℤ := (α : ℤ) + (α : ℤ)
def eeE (α : ℕ) : ℤ := if ((α : ℕ) : ℤ) = 0 then (1 : ℤ) else 0
def eeD (α t : ℕ) : ℤ := eeT2 t * eeA2 α
def eeDE (α t : ℕ) : ℤ := eeD α t + eeE α
def eeF (α : ℕ) : ℤ := (1 : ℤ) - eeE α
def eeCN (p : ℕ) (N : ℤ) : ℤ := N * auPi p
def eeZP (p α t : ℕ) (N : ℤ) : ℤ := Int.tdiv (N * auPi p) (eeDE α t)
def eeZ (p α t : ℕ) (N : ℤ) : ℤ := eeZP p α t N * eeF α
def eeENP (p : ℕ) : ℤ := (2 : ℤ) ^ (eeW2 p).toNat
def eeEN (p : ℕ) : ℤ := (2 : ℤ) ^ (eeW1 p).toNat
def eeEN2 (p α : ℕ) : ℤ := eeAA2 α * eeENP p
def eeNST (p : ℕ) : ℤ := eeW1 p + eeW1 p
def eeX10 (p : ℕ) : ℤ := (p : ℤ) + 10
def eeB (p : ℕ) : ℤ := eeEN p * eeX10 p
def eeFLG (p α t : ℕ) (N : ℤ) : ℤ := if eeB p < eeZ p α t N then (1 : ℤ) else 0


/-! ## Helper lemmas -/

/-- A `Pipe` spec gives the `∃ rest` window shape used by the statement of `auPreWord`. -/
theorem Pipe.toWordR {main prog : Cmd} {A B : List Val} {c : ℕ} (h : Pipe main prog A B c) :
    WordR main prog (fun vs => ∃ rest, vs = A ++ rest)
      (fun vs out => ∃ rest, vs = A ++ rest ∧ out = B ++ rest) (fun _ => c) := by
  intro vs hvs s R hR
  obtain ⟨r, rfl⟩ := hvs
  obtain ⟨out, s', n, hout, hev, hn, hstk, hoth⟩ := h r (A ++ r) rfl s R hR
  exact ⟨out, s', n, ⟨r, rfl, hout⟩, hev, hn, hstk, hoth⟩

/-! ## Size bounds for the intermediate values -/

theorem isz_if01_le (p : ℕ) {c : Prop} [Decidable c] :
    isz (if c then (1 : ℤ) else 0) ≤ auSZ p := by
  split <;> exact isz_const_le p (by norm_num)

theorem isz_one_sub_if01_le (p : ℕ) {c : Prop} [Decidable c] :
    isz ((1 : ℤ) - (if c then (1 : ℤ) else 0)) ≤ auSZ p := by
  split
  · rw [sub_self]; exact isz_const_le p (by norm_num)
  · rw [sub_zero]; exact isz_const_le p (by norm_num)

theorem isz_N_le {p : ℕ} {N : ℤ} (h0 : 0 ≤ N) (h : N ≤ (2 : ℤ) ^ (4 * p + 8)) :
    isz N ≤ auSZ p := by
  have h1 : ((N.natAbs : ℕ) : ℤ) ≤ ((2 ^ (4 * p + 8) : ℕ) : ℤ) := by
    rw [Int.natAbs_of_nonneg h0, Int.natCast_pow]
    exact h
  exact isz_le_auSZ_of_natAbs_le (Int.ofNat_le.mp h1) (by omega)

theorem isz_three_p_le (p : ℕ) : isz ((3 : ℤ) * (p : ℤ)) ≤ auSZ p := by
  rw [show (3 : ℤ) * (p : ℤ) = ((3 * p : ℕ) : ℤ) by push_cast; ring]
  refine isz_natCast_bd (N := p + 2) ?_ (by omega)
  calc 3 * p ≤ 3 * 2 ^ p := Nat.mul_le_mul_left 3 (le_of_lt (Nat.lt_two_pow_self (n := p)))
    _ ≤ 4 * 2 ^ p := Nat.mul_le_mul_right _ (by norm_num)
    _ = 2 ^ (p + 2) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        ring_nf

theorem isz_W1_le (p : ℕ) : isz ((100 : ℤ) + 3 * (p : ℤ)) ≤ auSZ p := by
  rw [show (100 : ℤ) + 3 * (p : ℤ) = ((auPrec p : ℕ) : ℤ) by
    simp only [auPrec]; push_cast; ring]
  exact isz_auPrec_le p

theorem isz_W2_le (p : ℕ) : isz ((100 : ℤ) + 3 * (p : ℤ) - (p : ℤ)) ≤ auSZ p := by
  rw [show (100 : ℤ) + 3 * (p : ℤ) - (p : ℤ) = ((2 * p + 100 : ℕ) : ℤ) by
    push_cast; ring]
  refine isz_natCast_bd (N := p + 7) ?_ (by omega)
  calc 2 * p + 100 ≤ 103 * 2 ^ p := by have := three_mul_add_le p; omega
    _ ≤ 128 * 2 ^ p := Nat.mul_le_mul_right _ (by norm_num)
    _ = 2 ^ (p + 7) := by
        rw [show (128 : ℕ) = 2 ^ 7 by norm_num, ← pow_add]
        ring_nf

theorem isz_alpha_sq_le (p α : ℕ) (hα : α ≤ 2 ^ p) : isz ((α : ℤ) * (α : ℤ)) ≤ auSZ p := by
  rw [show (α : ℤ) * (α : ℤ) = ((α * α : ℕ) : ℤ) by push_cast; ring]
  refine isz_natCast_bd (N := 2 * p) ?_ (by omega)
  calc α * α ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul hα hα
    _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf

theorem isz_t_sq_le (p t : ℕ) (ht : t < 2 ^ p) : isz ((t : ℤ) * (t : ℤ)) ≤ auSZ p := by
  rw [show (t : ℤ) * (t : ℤ) = ((t * t : ℕ) : ℤ) by push_cast; ring]
  refine isz_natCast_bd (N := 2 * p) ?_ (by omega)
  calc t * t ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul (le_of_lt ht) (le_of_lt ht)
    _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf

theorem isz_two_alpha_le (p α : ℕ) (hα : α ≤ 2 ^ p) : isz ((α : ℤ) + (α : ℤ)) ≤ auSZ p := by
  rw [show (α : ℤ) + (α : ℤ) = ((2 * α : ℕ) : ℤ) by push_cast; ring]
  refine isz_natCast_bd (N := p + 1) ?_ (by omega)
  calc 2 * α ≤ 2 * 2 ^ p := Nat.mul_le_mul_left 2 hα
    _ = 2 ^ (p + 1) := by rw [pow_succ]; ring

theorem isz_D_le (p α t : ℕ) (hα : α ≤ 2 ^ p) (ht : t < 2 ^ p) :
    isz (((t : ℤ) * (t : ℤ)) * ((α : ℤ) * (α : ℤ))) ≤ auSZ p := by
  rw [show ((t : ℤ) * (t : ℤ)) * ((α : ℤ) * (α : ℤ))
      = (((t * t) * (α * α) : ℕ) : ℤ) by push_cast; ring]
  refine isz_natCast_bd (N := 4 * p) ?_ (by omega)
  calc (t * t) * (α * α) ≤ (2 ^ p * 2 ^ p) * (2 ^ p * 2 ^ p) :=
        Nat.mul_le_mul (Nat.mul_le_mul (le_of_lt ht) (le_of_lt ht)) (Nat.mul_le_mul hα hα)
    _ = 2 ^ (4 * p) := by rw [← pow_add]; ring_nf

theorem isz_DE_le (p α t : ℕ) (hα : α ≤ 2 ^ p) (ht : t < 2 ^ p) :
    isz (((t : ℤ) * (t : ℤ)) * ((α : ℤ) * (α : ℤ)) +
      (if ((α : ℕ) : ℤ) = 0 then (1 : ℤ) else 0)) ≤ auSZ p := by
  have hD : (((t : ℤ) * (t : ℤ)) * ((α : ℤ) * (α : ℤ))).natAbs ≤ 2 ^ (4 * p) := by
    rw [show ((t : ℤ) * (t : ℤ)) * ((α : ℤ) * (α : ℤ))
        = (((t * t) * (α * α) : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]
    calc (t * t) * (α * α) ≤ (2 ^ p * 2 ^ p) * (2 ^ p * 2 ^ p) :=
          Nat.mul_le_mul (Nat.mul_le_mul (le_of_lt ht) (le_of_lt ht)) (Nat.mul_le_mul hα hα)
      _ = 2 ^ (4 * p) := by rw [← pow_add]; ring_nf
  have hE : (if ((α : ℕ) : ℤ) = 0 then (1 : ℤ) else 0).natAbs ≤ 2 ^ 0 := by
    split <;> simp
  exact isz_le_auSZ_of_natAbs_le (N := 4 * p + 1)
    (natAbs_add_bd (N := 4 * p + 1) hD hE (by omega) (by omega)) (by omega)

theorem isz_CN_le (p : ℕ) (N : ℤ) (hN : N.natAbs ≤ 2 ^ (4 * p + 8)) :
    isz (N * auPi p) ≤ auSZ p :=
  isz_le_auSZ_of_natAbs_le (N := 10 * p + 213)
    (natAbs_mul_bd (N := 10 * p + 213) hN (natAbs_auPi_le p) (by omega)) (by omega)

theorem isz_ZP_le (p α t : ℕ) (N : ℤ) (hα : α ≤ 2 ^ p) (ht : t < 2 ^ p)
    (hN : N.natAbs ≤ 2 ^ (4 * p + 8)) :
    isz (Int.tdiv (N * auPi p)
      (((t : ℤ) * (t : ℤ)) * ((α : ℤ) * (α : ℤ)) +
        (if ((α : ℕ) : ℤ) = 0 then (1 : ℤ) else 0))) ≤ auSZ p :=
  isz_le_auSZ_of_natAbs_le (N := 10 * p + 213)
    (natAbs_tdiv_bd (N := 10 * p + 213)
      (natAbs_mul_bd (N := 10 * p + 213) hN (natAbs_auPi_le p) (by omega)) (by omega)) (by omega)

theorem isz_Z_le (p α t : ℕ) (N : ℤ) (hα : α ≤ 2 ^ p) (ht : t < 2 ^ p)
    (hN : N.natAbs ≤ 2 ^ (4 * p + 8)) :
    isz (Int.tdiv (N * auPi p)
        (((t : ℤ) * (t : ℤ)) * ((α : ℤ) * (α : ℤ)) +
          (if ((α : ℕ) : ℤ) = 0 then (1 : ℤ) else 0)) *
      ((1 : ℤ) - (if ((α : ℕ) : ℤ) = 0 then (1 : ℤ) else 0))) ≤ auSZ p := by
  have hZP : (Int.tdiv (N * auPi p)
      (((t : ℤ) * (t : ℤ)) * ((α : ℤ) * (α : ℤ)) +
        (if ((α : ℕ) : ℤ) = 0 then (1 : ℤ) else 0))).natAbs ≤ 2 ^ (10 * p + 213) :=
    natAbs_tdiv_bd (N := 10 * p + 213)
      (natAbs_mul_bd (N := 10 * p + 213) hN (natAbs_auPi_le p) (by omega)) (by omega)
  have hF : ((1 : ℤ) - (if ((α : ℕ) : ℤ) = 0 then (1 : ℤ) else 0)).natAbs ≤ 2 ^ 0 := by
    split <;> simp
  exact isz_le_auSZ_of_natAbs_le (N := 10 * p + 213)
    (natAbs_mul_bd (N := 10 * p + 213) hZP hF (by omega)) (by omega)

theorem isz_X10_le (p : ℕ) : isz ((p : ℤ) + 10) ≤ auSZ p := by
  rw [show (p : ℤ) + 10 = ((p + 10 : ℕ) : ℤ) by push_cast; ring]
  refine isz_natCast_bd (N := p + 4) ?_ (by omega)
  calc p + 10 ≤ 16 * 2 ^ p := by
        have hp : p ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self (n := p))
        have hp1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
        nlinarith
    _ = 2 ^ (p + 4) := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]
        ring_nf

theorem isz_B_le (p : ℕ) :
    isz ((2 : ℤ) ^ ((100 : ℤ) + 3 * (p : ℤ)).toNat * ((p : ℤ) + 10)) ≤ auSZ p := by
  have h1 : ((p : ℤ) + 10) = ((p + 10 : ℕ) : ℤ) := by push_cast; ring
  have h2 : (2 : ℤ) ^ ((100 : ℤ) + 3 * (p : ℤ)).toNat = auEn p := by
    rw [show (100 : ℤ) + 3 * (p : ℤ) = ((auPrec p : ℕ) : ℤ) by
      simp only [auPrec]; push_cast; ring]
    rw [Int.toNat_natCast]
    rfl
  rw [h2, h1, mul_comm (auEn p) ((p + 10 : ℕ) : ℤ), ← auBnd]
  exact isz_auBnd_le p

theorem isz_en_le (p : ℕ) : isz ((2 : ℤ) ^ ((100 : ℤ) + 3 * (p : ℤ)).toNat) ≤ auSZ p := by
  rw [show (100 : ℤ) + 3 * (p : ℤ) = ((auPrec p : ℕ) : ℤ) by
    simp only [auPrec]; push_cast; ring]
  rw [Int.toNat_natCast]
  exact isz_auEn_le p

theorem isz_enP_le (p : ℕ) :
    isz ((2 : ℤ) ^ ((100 : ℤ) + 3 * (p : ℤ) - (p : ℤ)).toNat) ≤ auSZ p := by
  rw [show (100 : ℤ) + 3 * (p : ℤ) - (p : ℤ) = ((2 * p + 100 : ℕ) : ℤ) by push_cast; ring]
  rw [Int.toNat_natCast]
  exact isz_pow2_le (k := 2 * p + 100) (by simp only [auSZ]; omega)

theorem isz_nst_le (p : ℕ) :
    isz (((100 : ℤ) + 3 * (p : ℤ)) + ((100 : ℤ) + 3 * (p : ℤ))) ≤ auSZ p := by
  rw [show (100 : ℤ) + 3 * (p : ℤ) = ((auPrec p : ℕ) : ℤ) by
        simp only [auPrec]; push_cast; ring,
      ← Nat.cast_add,
      show auPrec p + auPrec p = auNstep p by simp only [auNstep]; ring]
  exact isz_auNstep_le p

theorem isz_en2_le (p α : ℕ) (hα : α ≤ 2 ^ p) :
    isz (((α : ℤ) + (α : ℤ)) *
      (2 : ℤ) ^ ((100 : ℤ) + 3 * (p : ℤ) - (p : ℤ)).toNat) ≤ auSZ p := by
  have h : ((α : ℤ) + (α : ℤ)) *
      (2 : ℤ) ^ ((100 : ℤ) + 3 * (p : ℤ) - (p : ℤ)).toNat = auEn2 p α := by
    rw [show (100 : ℤ) + 3 * (p : ℤ) - (p : ℤ) = ((2 * p + 100 : ℕ) : ℤ) by push_cast; ring]
    rw [Int.toNat_natCast]
    rw [show (2 * p + 100 : ℕ) = auPrec p - p by simp only [auPrec]; omega]
    simp only [auEn2, auEnP]
    ring
  rw [h]
  exact isz_auEn2_le p α hα


/-! ## Size bounds for the short names -/

theorem eeW1_nonneg (p : ℕ) : 0 ≤ eeW1 p := by
  have h : eeW1 p = ((auPrec p : ℕ) : ℤ) := by
    rw [eeW1]; simp only [auPrec]; push_cast; ring
  rw [h]; exact Int.natCast_nonneg _

theorem eeW1_toNat_le (p : ℕ) : (eeW1 p).toNat ≤ auSZ p := by
  have h : eeW1 p = ((auPrec p : ℕ) : ℤ) := by
    rw [eeW1]; simp only [auPrec]; push_cast; ring
  rw [h, Int.toNat_natCast]; simp only [auSZ, auPrec]; omega

theorem eeW2_nonneg (p : ℕ) : 0 ≤ eeW2 p := by
  have h : eeW2 p = ((2 * p + 100 : ℕ) : ℤ) := by rw [eeW2]; push_cast; ring
  rw [h]; exact Int.natCast_nonneg _

theorem eeW2_toNat_le (p : ℕ) : (eeW2 p).toNat ≤ auSZ p := by
  have h : eeW2 p = ((2 * p + 100 : ℕ) : ℤ) := by rw [eeW2]; push_cast; ring
  rw [h, Int.toNat_natCast]; simp only [auSZ]; omega

theorem eeisz_X3 (p : ℕ) : isz (eeX3 p) ≤ auSZ p := by rw [eeX3]; exact isz_three_p_le p

theorem eeisz_W1 (p : ℕ) : isz (eeW1 p) ≤ auSZ p := by rw [eeW1]; exact isz_W1_le p

theorem eeisz_W2 (p : ℕ) : isz (eeW2 p) ≤ auSZ p := by rw [eeW2]; exact isz_W2_le p

theorem eeisz_A2 (p α : ℕ) (hα : α ≤ 2 ^ p) : isz (eeA2 α) ≤ auSZ p := by
  rw [eeA2]; exact isz_alpha_sq_le p α hα

theorem eeisz_T2 (p t : ℕ) (ht : t < 2 ^ p) : isz (eeT2 t) ≤ auSZ p := by
  rw [eeT2]; exact isz_t_sq_le p t ht

theorem eeisz_AA2 (p α : ℕ) (hα : α ≤ 2 ^ p) : isz (eeAA2 α) ≤ auSZ p := by
  rw [eeAA2]; exact isz_two_alpha_le p α hα

theorem eeisz_E (p α : ℕ) : isz (eeE α) ≤ auSZ p := by rw [eeE]; exact isz_if01_le p

theorem eeisz_D (p α t : ℕ) (hα : α ≤ 2 ^ p) (ht : t < 2 ^ p) : isz (eeD α t) ≤ auSZ p := by
  rw [eeD, eeT2, eeA2]; exact isz_D_le p α t hα ht

theorem eeisz_DE (p α t : ℕ) (hα : α ≤ 2 ^ p) (ht : t < 2 ^ p) : isz (eeDE α t) ≤ auSZ p := by
  rw [eeDE, eeD, eeT2, eeA2, eeE]; exact isz_DE_le p α t hα ht

theorem eeisz_F (p α : ℕ) : isz (eeF α) ≤ auSZ p := by
  rw [eeF, eeE]; exact isz_one_sub_if01_le p

theorem eeisz_CN (p : ℕ) (N : ℤ) (hN : N.natAbs ≤ 2 ^ (4 * p + 8)) : isz (eeCN p N) ≤ auSZ p := by
  rw [eeCN]; exact isz_CN_le p N hN

theorem eeisz_ZP (p α t : ℕ) (N : ℤ) (hα : α ≤ 2 ^ p) (ht : t < 2 ^ p)
    (hN : N.natAbs ≤ 2 ^ (4 * p + 8)) : isz (eeZP p α t N) ≤ auSZ p := by
  rw [eeZP, eeDE, eeD, eeT2, eeA2, eeE]; exact isz_ZP_le p α t N hα ht hN

theorem eeisz_Z (p α t : ℕ) (N : ℤ) (hα : α ≤ 2 ^ p) (ht : t < 2 ^ p)
    (hN : N.natAbs ≤ 2 ^ (4 * p + 8)) : isz (eeZ p α t N) ≤ auSZ p := by
  rw [eeZ, eeZP, eeDE, eeD, eeT2, eeA2, eeE, eeF]; exact isz_Z_le p α t N hα ht hN

theorem eeisz_ENP (p : ℕ) : isz (eeENP p) ≤ auSZ p := by rw [eeENP, eeW2]; exact isz_enP_le p

theorem eeisz_EN (p : ℕ) : isz (eeEN p) ≤ auSZ p := by rw [eeEN, eeW1]; exact isz_en_le p

theorem eeisz_EN2 (p α : ℕ) (hα : α ≤ 2 ^ p) : isz (eeEN2 p α) ≤ auSZ p := by
  rw [eeEN2, eeAA2, eeENP, eeW2]; exact isz_en2_le p α hα

theorem eeisz_NST (p : ℕ) : isz (eeNST p) ≤ auSZ p := by rw [eeNST, eeW1]; exact isz_nst_le p

theorem eeisz_X10 (p : ℕ) : isz (eeX10 p) ≤ auSZ p := by rw [eeX10]; exact isz_X10_le p

theorem eeisz_B (p : ℕ) : isz (eeB p) ≤ auSZ p := by
  rw [eeB, eeEN, eeX10, eeW1]; exact isz_B_le p

theorem eeisz_FLG (p α t : ℕ) (N : ℤ) : isz (eeFLG p α t N) ≤ auSZ p := by
  rw [eeFLG]; exact isz_if01_le p

end AuPreWordAux

open AuPreWordAux in


theorem auPreWord (hk : HvdH.KernelLib) (hi : HvdH.IntLib) :
    ∃ (pre : HvdH.Cmd) (KS : ℕ),
      ∀ (main : HvdH.Cmd) (p α t : ℕ) (N : ℤ),
        (1 ≤ p) → (0 ≤ N) → (N ≤ (2 : ℤ) ^ (4 * p + 8)) → (1 ≤ t) → (t < 2 ^ p) →
        (α ≤ 2 ^ p) →
        HvdH.WordR main pre
          (fun vs => ∃ rest, vs = [HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ),
            HvdH.Val.int (t : ℤ), HvdH.Val.int N, HvdH.Val.int (auPi p)] ++ rest)
          (fun vs out => ∃ rest, vs = [HvdH.Val.int (p : ℤ), HvdH.Val.int (α : ℤ),
            HvdH.Val.int (t : ℤ), HvdH.Val.int N, HvdH.Val.int (auPi p)] ++ rest ∧
            out = [HvdH.Val.int (auFlg p α t N), HvdH.Val.int ((auNstep p : ℕ) : ℤ),
              HvdH.Val.int (auEn p), HvdH.Val.int (auZ p α t N), HvdH.Val.int (auEn p),
              HvdH.Val.int (auEn2 p α)] ++ rest)
          (fun _ => 300 * auSB p KS) := by
  obtain ⟨pushProg, Kpush, hPush⟩ := hk.pushVal
  obtain ⟨dupProg, Kdup, hDup⟩ := hk.dup
  obtain ⟨dropProg, Kdrop, hDrop⟩ := hk.drop
  obtain ⟨pickProg, Kpick, hPick⟩ := hk.pick
  obtain ⟨rollProg, Kroll, hRoll⟩ := hk.roll
  obtain ⟨swapProg, Kswap, hSwap⟩ := hk.swap
  obtain ⟨addProg, Kadd, hAdd⟩ := hi.add
  obtain ⟨subProg, Ksub, hSub⟩ := hi.sub
  obtain ⟨mulProg, Kmul, hMul⟩ := hi.mulS
  obtain ⟨tdivProg, Ktdiv, hTdiv⟩ := hi.tdiv
  obtain ⟨eqProg, Keq, hEq⟩ := hi.eq
  obtain ⟨ltProg, Klt, hLt⟩ := hi.lt
  obtain ⟨pow2Prog, Kpow2, hPow2⟩ := hi.pow2
  set KS : ℕ := Kpush + Kdup + Kdrop + Kpick + Kroll + Kswap + Kadd + Ksub + Kmul + Ktdiv + Keq + Klt + Kpow2 + 1 with hKS
  have hKpush : Kpush ≤ KS := by rw [hKS]; omega
  have hKdup : Kdup ≤ KS := by rw [hKS]; omega
  have hKdrop : Kdrop ≤ KS := by rw [hKS]; omega
  have hKpick : Kpick ≤ KS := by rw [hKS]; omega
  have hKroll : Kroll ≤ KS := by rw [hKS]; omega
  have hKswap : Kswap ≤ KS := by rw [hKS]; omega
  have hKadd : Kadd ≤ KS := by rw [hKS]; omega
  have hKsub : Ksub ≤ KS := by rw [hKS]; omega
  have hKmul : Kmul ≤ KS := by rw [hKS]; omega
  have hKtdiv : Ktdiv ≤ KS := by rw [hKS]; omega
  have hKeq : Keq ≤ KS := by rw [hKS]; omega
  have hKlt : Klt ≤ KS := by rw [hKS]; omega
  have hKpow2 : Kpow2 ≤ KS := by rw [hKS]; omega
  let P : HvdH.Cmd := (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (.seq (pickProg 0) (pushProg (HvdH.Val.int ((3 : ℤ))))) mulProg) (pushProg (HvdH.Val.int ((100 : ℤ))))) addProg) (pickProg 1)) (pickProg 1)) subProg) pow2Prog) (pickProg 3)) (pickProg 0)) addProg) mulProg) (rollProg 1)) dropProg) (pickProg 1)) (pushProg (HvdH.Val.int ((3 : ℤ))))) mulProg) (pushProg (HvdH.Val.int ((100 : ℤ))))) addProg) pow2Prog) (pickProg 3)) (pickProg 4)) mulProg) (pickProg 5)) (pickProg 6)) mulProg) mulProg) (pushProg (HvdH.Val.int ((0 : ℤ))))) (pickProg 5)) eqProg) dupProg) (rollProg 2)) addProg) (rollProg 1)) (pushProg (HvdH.Val.int ((1 : ℤ))))) subProg) swapProg) (pickProg 8)) (pickProg 8)) mulProg) tdivProg) mulProg) (rollProg 4)) dropProg) (rollProg 4)) dropProg) (rollProg 4)) dropProg) (rollProg 4)) dropProg) (pickProg 3)) (pushProg (HvdH.Val.int ((3 : ℤ))))) mulProg) (pushProg (HvdH.Val.int ((100 : ℤ))))) addProg) pow2Prog) (pickProg 4)) (pushProg (HvdH.Val.int ((3 : ℤ))))) mulProg) (pushProg (HvdH.Val.int ((100 : ℤ))))) addProg) dupProg) addProg) (pushProg (HvdH.Val.int ((10 : ℤ))))) (pickProg 6)) addProg) (pickProg 2)) mulProg) (pickProg 3)) swapProg) ltProg) (rollProg 6)) dropProg)
  refine ⟨P, KS, ?_⟩
  intro main p α t N h1p h0N hNle h1t htp hα
  set CB : ℕ := auSB p KS with hCB
  have hsz_P : isz ((p : ℤ)) ≤ auSZ p := by exact isz_p_le p
  have hsz_A : isz ((α : ℤ)) ≤ auSZ p := by exact isz_le_pow2 hα
  have hsz_T : isz ((t : ℤ)) ≤ auSZ p := by exact isz_le_pow2 (le_of_lt htp)
  have hsz_NN : isz (N) ≤ auSZ p := by exact isz_N_le h0N hNle
  have hsz_PI : isz (auPi p) ≤ auSZ p := by exact isz_auPi_le p
  have hsz_C3 : isz ((3 : ℤ)) ≤ auSZ p := by exact isz_const_le p (by norm_num)
  have hsz_C100 : isz ((100 : ℤ)) ≤ auSZ p := by exact isz_const_le p (by norm_num)
  have hsz_C0 : isz ((0 : ℤ)) ≤ auSZ p := by exact isz_const_le p (by norm_num)
  have hsz_C1 : isz ((1 : ℤ)) ≤ auSZ p := by exact isz_const_le p (by norm_num)
  have hsz_C10 : isz ((10 : ℤ)) ≤ auSZ p := by exact isz_const_le p (by norm_num)
  have hsz_X3 : isz (eeX3 p) ≤ auSZ p := by exact eeisz_X3 p
  have hsz_W1 : isz (eeW1 p) ≤ auSZ p := by exact eeisz_W1 p
  have hsz_W2 : isz (eeW2 p) ≤ auSZ p := by exact eeisz_W2 p
  have hsz_A2 : isz (eeA2 α) ≤ auSZ p := by exact eeisz_A2 p α hα
  have hsz_T2 : isz (eeT2 t) ≤ auSZ p := by exact eeisz_T2 p t htp
  have hsz_AA2 : isz (eeAA2 α) ≤ auSZ p := by exact eeisz_AA2 p α hα
  have hsz_E : isz (eeE α) ≤ auSZ p := by exact eeisz_E p α
  have hsz_D : isz (eeD α t) ≤ auSZ p := by exact eeisz_D p α t hα htp
  have hsz_DE : isz (eeDE α t) ≤ auSZ p := by exact eeisz_DE p α t hα htp
  have hsz_F : isz (eeF α) ≤ auSZ p := by exact eeisz_F p α
  have hsz_ENP : isz (eeENP p) ≤ auSZ p := by exact eeisz_ENP p
  have hsz_EN : isz (eeEN p) ≤ auSZ p := by exact eeisz_EN p
  have hsz_EN2 : isz (eeEN2 p α) ≤ auSZ p := by exact eeisz_EN2 p α hα
  have hsz_NST : isz (eeNST p) ≤ auSZ p := by exact eeisz_NST p
  have hsz_X10 : isz (eeX10 p) ≤ auSZ p := by exact eeisz_X10 p
  have hsz_B : isz (eeB p) ≤ auSZ p := by exact eeisz_B p
  have hsz_FLG : isz (eeFLG p α t N) ≤ auSZ p := by exact eeisz_FLG p α t N
  have hNabs : N.natAbs ≤ 2 ^ (4 * p + 8) := by
    have h1 : ((N.natAbs : ℕ) : ℤ) ≤ ((2 ^ (4 * p + 8) : ℕ) : ℤ) := by
      rw [Int.natAbs_of_nonneg h0N, Int.natCast_pow]
      exact hNle
    exact Int.ofNat_le.mp h1
  have hsz_CN : isz (eeCN p N) ≤ auSZ p := by exact eeisz_CN p N hNabs
  have hsz_ZP : isz (eeZP p α t N) ≤ auSZ p := by exact eeisz_ZP p α t N hα htp hNabs
  have hsz_Z : isz (eeZ p α t N) ≤ auSZ p := by exact eeisz_Z p α t N hα htp hNabs
  have hDEne : eeDE α t ≠ 0 := by
    rw [eeDE, eeD, eeT2, eeA2, eeE]
    rcases eq_or_ne α 0 with hα0 | hα0
    · simp [hα0]
    · have hE0 : (if ((α : ℕ) : ℤ) = 0 then (1 : ℤ) else 0) = 0 := by simp [hα0]
      have hα1 : (1 : ℤ) ≤ (α : ℤ) := by
        have : (1 : ℕ) ≤ α := by omega
        exact_mod_cast this
      have ht1 : (1 : ℤ) ≤ (t : ℤ) := by exact_mod_cast h1t
      have hDpos : (0 : ℤ) < ((t : ℤ) * (t : ℤ)) * ((α : ℤ) * (α : ℤ)) := by
        have h1 : (0 : ℤ) < ((t : ℤ) * (t : ℤ)) := by nlinarith
        have h2 : (0 : ℤ) < ((α : ℤ) * (α : ℤ)) := by nlinarith
        exact mul_pos h1 h2
      rw [hE0, add_zero]
      exact ne_of_gt hDpos
  have hstep : ∀ {n : ℕ} {q₁ q₂ : HvdH.Cmd} {A B D : List HvdH.Val},
      Pipe main q₁ A B (n * CB) → Pipe main q₂ B D CB → Pipe main (.seq q₁ q₂) A D ((n + 1) * CB) := by
    intro n q₁ q₂ A B D h1 h2
    have h := Pipe.comp h1 h2
    rw [show n * CB + CB = (n + 1) * CB by rw [Nat.add_mul, Nat.one_mul]] at h
    exact h
  have s1 : Pipe main (pickProg 0) [HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 0) (by simp))
      (au_le_roll hKpick (A := [HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 0) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_P
        · exact vszVI hsz_A
        · exact vszVI hsz_T
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s2 : Pipe main (pushProg (HvdH.Val.int ((3 : ℤ)))) [HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((3 : ℤ)), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.pushOnAny (T := [HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (hPush main (HvdH.Val.int ((3 : ℤ))))
      |> fun h => Pipe.le h (au_le_one hKpush (vszVI hsz_C3))
  have s3 : Pipe main mulProg [HvdH.Val.int ((3 : ℤ)), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeX3 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.binOp (hMul main)
        (a := (3 : ℤ)) (b := (p : ℤ)) trivial))
      (au_le_mul_auPreKit hKmul hsz_C3 hsz_P)
  have s4 : Pipe main (pushProg (HvdH.Val.int ((100 : ℤ)))) [HvdH.Val.int (eeX3 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((100 : ℤ)), HvdH.Val.int (eeX3 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.pushOnAny (T := [HvdH.Val.int (eeX3 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (hPush main (HvdH.Val.int ((100 : ℤ))))
      |> fun h => Pipe.le h (au_le_one hKpush (vszVI hsz_C100))
  have s5 : Pipe main addProg [HvdH.Val.int ((100 : ℤ)), HvdH.Val.int (eeX3 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.binOp (hAdd main)
        (a := (100 : ℤ)) (b := eeX3 p) trivial))
      (au_le_two hKadd hsz_C100 hsz_X3)
  have s6 : Pipe main (pickProg 1) [HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 1) (by simp))
      (au_le_roll hKpick (A := [HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 1) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_W1
        · exact vszVI hsz_P
        · exact vszVI hsz_A
        · exact vszVI hsz_T
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s7 : Pipe main (pickProg 1) [HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 1) (by simp))
      (au_le_roll hKpick (A := [HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 1) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_P
        · exact vszVI hsz_W1
        · exact vszVI hsz_P
        · exact vszVI hsz_A
        · exact vszVI hsz_T
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s8 : Pipe main subProg [HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeW2 p), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.binOp (hSub main)
        (a := eeW1 p) (b := (p : ℤ)) trivial))
      (au_le_two hKsub hsz_W1 hsz_P)
  have s9 : Pipe main pow2Prog [HvdH.Val.int (eeW2 p), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeENP p), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.unOp (hPow2 main) (eeW2_nonneg p)))
      (au_le_two hKpow2 (eeW2_toNat_le p) hsz_W2)
  have s10 : Pipe main (pickProg 3) [HvdH.Val.int (eeENP p), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((α : ℤ)), HvdH.Val.int (eeENP p), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int (eeENP p), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 3) (by simp))
      (au_le_roll hKpick (A := [HvdH.Val.int (eeENP p), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 3) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_ENP
        · exact vszVI hsz_W1
        · exact vszVI hsz_P
        · exact vszVI hsz_A
        · exact vszVI hsz_T
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s11 : Pipe main (pickProg 0) [HvdH.Val.int ((α : ℤ)), HvdH.Val.int (eeENP p), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int (eeENP p), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int ((α : ℤ)), HvdH.Val.int (eeENP p), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 0) (by simp))
      (au_le_roll hKpick (A := [HvdH.Val.int ((α : ℤ)), HvdH.Val.int (eeENP p), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 0) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_A
        · exact vszVI hsz_ENP
        · exact vszVI hsz_W1
        · exact vszVI hsz_P
        · exact vszVI hsz_A
        · exact vszVI hsz_T
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s12 : Pipe main addProg [HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int (eeENP p), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeAA2 α), HvdH.Val.int (eeENP p), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeENP p), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.binOp (hAdd main)
        (a := (α : ℤ)) (b := (α : ℤ)) trivial))
      (au_le_two hKadd hsz_A hsz_A)
  have s13 : Pipe main mulProg [HvdH.Val.int (eeAA2 α), HvdH.Val.int (eeENP p), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeEN2 p α), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.binOp (hMul main)
        (a := eeAA2 α) (b := eeENP p) trivial))
      (au_le_mul_auPreKit hKmul hsz_AA2 hsz_ENP)
  have s14 : Pipe main (rollProg 1) [HvdH.Val.int (eeEN2 p α), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeW1 p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.roll main hRoll (A := [HvdH.Val.int (eeEN2 p α), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 1) (by simp))
      (au_le_roll hKroll (A := [HvdH.Val.int (eeEN2 p α), HvdH.Val.int (eeW1 p), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 1) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_EN2
        · exact vszVI hsz_W1
        · exact vszVI hsz_P
        · exact vszVI hsz_A
        · exact vszVI hsz_T
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s15 : Pipe main dropProg [HvdH.Val.int (eeW1 p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.appendTail [HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.drop main hDrop (HvdH.Val.int (eeW1 p)))
      |> fun h => Pipe.le h (au_le_one hKdrop (vszVI hsz_W1))
  have s16 : Pipe main (pickProg 1) [HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 1) (by simp))
      (au_le_roll hKpick (A := [HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 1) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P
        · exact vszVI hsz_A
        · exact vszVI hsz_T
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s17 : Pipe main (pushProg (HvdH.Val.int ((3 : ℤ)))) [HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((3 : ℤ)), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.pushOnAny (T := [HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (hPush main (HvdH.Val.int ((3 : ℤ))))
      |> fun h => Pipe.le h (au_le_one hKpush (vszVI hsz_C3))
  have s18 : Pipe main mulProg [HvdH.Val.int ((3 : ℤ)), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeX3 p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.binOp (hMul main)
        (a := (3 : ℤ)) (b := (p : ℤ)) trivial))
      (au_le_mul_auPreKit hKmul hsz_C3 hsz_P)
  have s19 : Pipe main (pushProg (HvdH.Val.int ((100 : ℤ)))) [HvdH.Val.int (eeX3 p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((100 : ℤ)), HvdH.Val.int (eeX3 p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.pushOnAny (T := [HvdH.Val.int (eeX3 p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (hPush main (HvdH.Val.int ((100 : ℤ))))
      |> fun h => Pipe.le h (au_le_one hKpush (vszVI hsz_C100))
  have s20 : Pipe main addProg [HvdH.Val.int ((100 : ℤ)), HvdH.Val.int (eeX3 p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeW1 p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.binOp (hAdd main)
        (a := (100 : ℤ)) (b := eeX3 p) trivial))
      (au_le_two hKadd hsz_C100 hsz_X3)
  have s21 : Pipe main pow2Prog [HvdH.Val.int (eeW1 p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.unOp (hPow2 main) (eeW1_nonneg p)))
      (au_le_two hKpow2 (eeW1_toNat_le p) hsz_W1)
  have s22 : Pipe main (pickProg 3) [HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((α : ℤ)), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 3) (by simp))
      (au_le_roll hKpick (A := [HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 3) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P
        · exact vszVI hsz_A
        · exact vszVI hsz_T
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s23 : Pipe main (pickProg 4) [HvdH.Val.int ((α : ℤ)), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int ((α : ℤ)), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 4) (by simp))
      (au_le_roll hKpick (A := [HvdH.Val.int ((α : ℤ)), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 4) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_A
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P
        · exact vszVI hsz_A
        · exact vszVI hsz_T
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s24 : Pipe main mulProg [HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeA2 α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.binOp (hMul main)
        (a := (α : ℤ)) (b := (α : ℤ)) trivial))
      (au_le_mul_auPreKit hKmul hsz_A hsz_A)
  have s25 : Pipe main (pickProg 5) [HvdH.Val.int (eeA2 α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((t : ℤ)), HvdH.Val.int (eeA2 α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int (eeA2 α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 5) (by simp))
      (au_le_roll hKpick (A := [HvdH.Val.int (eeA2 α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 5) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_A2
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P
        · exact vszVI hsz_A
        · exact vszVI hsz_T
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s26 : Pipe main (pickProg 6) [HvdH.Val.int ((t : ℤ)), HvdH.Val.int (eeA2 α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((t : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (eeA2 α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int ((t : ℤ)), HvdH.Val.int (eeA2 α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 6) (by simp))
      (au_le_roll hKpick (A := [HvdH.Val.int ((t : ℤ)), HvdH.Val.int (eeA2 α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 6) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_T
        · exact vszVI hsz_A2
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P
        · exact vszVI hsz_A
        · exact vszVI hsz_T
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s27 : Pipe main mulProg [HvdH.Val.int ((t : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (eeA2 α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeT2 t), HvdH.Val.int (eeA2 α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeA2 α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.binOp (hMul main)
        (a := (t : ℤ)) (b := (t : ℤ)) trivial))
      (au_le_mul_auPreKit hKmul hsz_T hsz_T)
  have s28 : Pipe main mulProg [HvdH.Val.int (eeT2 t), HvdH.Val.int (eeA2 α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeD α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.binOp (hMul main)
        (a := eeT2 t) (b := eeA2 α) trivial))
      (au_le_mul_auPreKit hKmul hsz_T2 hsz_A2)
  have s29 : Pipe main (pushProg (HvdH.Val.int ((0 : ℤ)))) [HvdH.Val.int (eeD α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((0 : ℤ)), HvdH.Val.int (eeD α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.pushOnAny (T := [HvdH.Val.int (eeD α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (hPush main (HvdH.Val.int ((0 : ℤ))))
      |> fun h => Pipe.le h (au_le_one hKpush (vszVI hsz_C0))
  have s30 : Pipe main (pickProg 5) [HvdH.Val.int ((0 : ℤ)), HvdH.Val.int (eeD α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((0 : ℤ)), HvdH.Val.int (eeD α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int ((0 : ℤ)), HvdH.Val.int (eeD α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 5) (by simp))
      (au_le_roll hKpick (A := [HvdH.Val.int ((0 : ℤ)), HvdH.Val.int (eeD α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 5) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_C0
        · exact vszVI hsz_D
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P
        · exact vszVI hsz_A
        · exact vszVI hsz_T
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s31 : Pipe main eqProg [HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((0 : ℤ)), HvdH.Val.int (eeD α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeE α), HvdH.Val.int (eeD α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeD α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.binOp (hEq main)
        (a := (α : ℤ)) (b := (0 : ℤ)) trivial))
      (au_le_two hKeq hsz_A hsz_C0)
  have s32 : Pipe main dupProg [HvdH.Val.int (eeE α), HvdH.Val.int (eeD α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeE α), HvdH.Val.int (eeE α), HvdH.Val.int (eeD α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.appendTail [HvdH.Val.int (eeD α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.dup main hDup (HvdH.Val.int (eeE α)))
      |> fun h => Pipe.le h (au_le_one hKdup (vszVI hsz_E))
  have s33 : Pipe main (rollProg 2) [HvdH.Val.int (eeE α), HvdH.Val.int (eeE α), HvdH.Val.int (eeD α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeD α t), HvdH.Val.int (eeE α), HvdH.Val.int (eeE α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.roll main hRoll (A := [HvdH.Val.int (eeE α), HvdH.Val.int (eeE α), HvdH.Val.int (eeD α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 2) (by simp))
      (au_le_roll hKroll (A := [HvdH.Val.int (eeE α), HvdH.Val.int (eeE α), HvdH.Val.int (eeD α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 2) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_E
        · exact vszVI hsz_E
        · exact vszVI hsz_D
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P
        · exact vszVI hsz_A
        · exact vszVI hsz_T
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s34 : Pipe main addProg [HvdH.Val.int (eeD α t), HvdH.Val.int (eeE α), HvdH.Val.int (eeE α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeDE α t), HvdH.Val.int (eeE α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeE α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.binOp (hAdd main)
        (a := eeD α t) (b := eeE α) trivial))
      (au_le_two hKadd hsz_D hsz_E)
  have s35 : Pipe main (rollProg 1) [HvdH.Val.int (eeDE α t), HvdH.Val.int (eeE α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeE α), HvdH.Val.int (eeDE α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.roll main hRoll (A := [HvdH.Val.int (eeDE α t), HvdH.Val.int (eeE α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 1) (by simp))
      (au_le_roll hKroll (A := [HvdH.Val.int (eeDE α t), HvdH.Val.int (eeE α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 1) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_DE
        · exact vszVI hsz_E
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P
        · exact vszVI hsz_A
        · exact vszVI hsz_T
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s36 : Pipe main (pushProg (HvdH.Val.int ((1 : ℤ)))) [HvdH.Val.int (eeE α), HvdH.Val.int (eeDE α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((1 : ℤ)), HvdH.Val.int (eeE α), HvdH.Val.int (eeDE α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.pushOnAny (T := [HvdH.Val.int (eeE α), HvdH.Val.int (eeDE α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (hPush main (HvdH.Val.int ((1 : ℤ))))
      |> fun h => Pipe.le h (au_le_one hKpush (vszVI hsz_C1))
  have s37 : Pipe main subProg [HvdH.Val.int ((1 : ℤ)), HvdH.Val.int (eeE α), HvdH.Val.int (eeDE α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeF α), HvdH.Val.int (eeDE α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeDE α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.binOp (hSub main)
        (a := (1 : ℤ)) (b := eeE α) trivial))
      (au_le_two hKsub hsz_C1 hsz_E)
  have s38 : Pipe main swapProg [HvdH.Val.int (eeF α), HvdH.Val.int (eeDE α t), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeDE α t), HvdH.Val.int (eeF α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.swap main hSwap (HvdH.Val.int (eeF α)) (HvdH.Val.int (eeDE α t))))
      (au_le_three hKswap (vszVI hsz_F) (vszVI hsz_DE) (by simp only [auSZ]; omega))
  have s39 : Pipe main (pickProg 8) [HvdH.Val.int (eeDE α t), HvdH.Val.int (eeF α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (auPi p), HvdH.Val.int (eeDE α t), HvdH.Val.int (eeF α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int (eeDE α t), HvdH.Val.int (eeF α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 8) (by simp))
      (au_le_roll hKpick (A := [HvdH.Val.int (eeDE α t), HvdH.Val.int (eeF α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 8) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_DE
        · exact vszVI hsz_F
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P
        · exact vszVI hsz_A
        · exact vszVI hsz_T
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s40 : Pipe main (pickProg 8) [HvdH.Val.int (auPi p), HvdH.Val.int (eeDE α t), HvdH.Val.int (eeF α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (N), HvdH.Val.int (auPi p), HvdH.Val.int (eeDE α t), HvdH.Val.int (eeF α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int (auPi p), HvdH.Val.int (eeDE α t), HvdH.Val.int (eeF α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 8) (by simp))
      (au_le_roll hKpick (A := [HvdH.Val.int (auPi p), HvdH.Val.int (eeDE α t), HvdH.Val.int (eeF α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 8) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_PI
        · exact vszVI hsz_DE
        · exact vszVI hsz_F
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P
        · exact vszVI hsz_A
        · exact vszVI hsz_T
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s41 : Pipe main mulProg [HvdH.Val.int (N), HvdH.Val.int (auPi p), HvdH.Val.int (eeDE α t), HvdH.Val.int (eeF α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeCN p N), HvdH.Val.int (eeDE α t), HvdH.Val.int (eeF α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeDE α t), HvdH.Val.int (eeF α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.binOp (hMul main)
        (a := N) (b := auPi p) trivial))
      (au_le_mul_auPreKit hKmul hsz_NN hsz_PI)
  have s42 : Pipe main tdivProg [HvdH.Val.int (eeCN p N), HvdH.Val.int (eeDE α t), HvdH.Val.int (eeF α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeZP p α t N), HvdH.Val.int (eeF α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeF α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.binOp (hTdiv main)
        (a := eeCN p N) (b := eeDE α t) hDEne))
      (au_le_mul_auPreKit hKtdiv hsz_CN hsz_DE)
  have s43 : Pipe main mulProg [HvdH.Val.int (eeZP p α t N), HvdH.Val.int (eeF α), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.binOp (hMul main)
        (a := eeZP p α t N) (b := eeF α) trivial))
      (au_le_mul_auPreKit hKmul hsz_ZP hsz_F)
  have s44 : Pipe main (rollProg 4) [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((α : ℤ)), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.roll main hRoll (A := [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 4) (by simp))
      (au_le_roll hKroll (A := [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 4) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_Z
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P
        · exact vszVI hsz_A
        · exact vszVI hsz_T
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s45 : Pipe main dropProg [HvdH.Val.int ((α : ℤ)), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.appendTail [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.drop main hDrop (HvdH.Val.int ((α : ℤ))))
      |> fun h => Pipe.le h (au_le_one hKdrop (vszVI hsz_A))
  have s46 : Pipe main (rollProg 4) [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((t : ℤ)), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.roll main hRoll (A := [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 4) (by simp))
      (au_le_roll hKroll (A := [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 4) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_Z
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P
        · exact vszVI hsz_T
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s47 : Pipe main dropProg [HvdH.Val.int ((t : ℤ)), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.appendTail [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (Pipe.drop main hDrop (HvdH.Val.int ((t : ℤ))))
      |> fun h => Pipe.le h (au_le_one hKdrop (vszVI hsz_T))
  have s48 : Pipe main (rollProg 4) [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int (N), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.le (Pipe.roll main hRoll (A := [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 4) (by simp))
      (au_le_roll hKroll (A := [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)]) (k := 4) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_Z
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P
        · exact vszVI hsz_NN
        · exact vszVI hsz_PI))
  have s49 : Pipe main dropProg [HvdH.Val.int (N), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (auPi p)] [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (auPi p)] CB := by
    exact     Pipe.appendTail [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (auPi p)] (Pipe.drop main hDrop (HvdH.Val.int (N)))
      |> fun h => Pipe.le h (au_le_one hKdrop (vszVI hsz_NN))
  have s50 : Pipe main (rollProg 4) [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (auPi p)] [HvdH.Val.int (auPi p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.le (Pipe.roll main hRoll (A := [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (auPi p)]) (k := 4) (by simp))
      (au_le_roll hKroll (A := [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (auPi p)]) (k := 4) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_Z
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P
        · exact vszVI hsz_PI))
  have s51 : Pipe main dropProg [HvdH.Val.int (auPi p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.appendTail [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] (Pipe.drop main hDrop (HvdH.Val.int (auPi p)))
      |> fun h => Pipe.le h (au_le_one hKdrop (vszVI hsz_PI))
  have s52 : Pipe main (pickProg 3) [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))]) (k := 3) (by simp))
      (au_le_roll hKpick (A := [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))]) (k := 3) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl
        · exact vszVI hsz_Z
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P))
  have s53 : Pipe main (pushProg (HvdH.Val.int ((3 : ℤ)))) [HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int ((3 : ℤ)), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.pushOnAny (T := [HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))]) (hPush main (HvdH.Val.int ((3 : ℤ))))
      |> fun h => Pipe.le h (au_le_one hKpush (vszVI hsz_C3))
  have s54 : Pipe main mulProg [HvdH.Val.int ((3 : ℤ)), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int (eeX3 p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] (Pipe.binOp (hMul main)
        (a := (3 : ℤ)) (b := (p : ℤ)) trivial))
      (au_le_mul_auPreKit hKmul hsz_C3 hsz_P)
  have s55 : Pipe main (pushProg (HvdH.Val.int ((100 : ℤ)))) [HvdH.Val.int (eeX3 p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int ((100 : ℤ)), HvdH.Val.int (eeX3 p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.pushOnAny (T := [HvdH.Val.int (eeX3 p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))]) (hPush main (HvdH.Val.int ((100 : ℤ))))
      |> fun h => Pipe.le h (au_le_one hKpush (vszVI hsz_C100))
  have s56 : Pipe main addProg [HvdH.Val.int ((100 : ℤ)), HvdH.Val.int (eeX3 p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int (eeW1 p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] (Pipe.binOp (hAdd main)
        (a := (100 : ℤ)) (b := eeX3 p) trivial))
      (au_le_two hKadd hsz_C100 hsz_X3)
  have s57 : Pipe main pow2Prog [HvdH.Val.int (eeW1 p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] (Pipe.unOp (hPow2 main) (eeW1_nonneg p)))
      (au_le_two hKpow2 (eeW1_toNat_le p) hsz_W1)
  have s58 : Pipe main (pickProg 4) [HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))]) (k := 4) (by simp))
      (au_le_roll hKpick (A := [HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))]) (k := 4) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_EN
        · exact vszVI hsz_Z
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P))
  have s59 : Pipe main (pushProg (HvdH.Val.int ((3 : ℤ)))) [HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int ((3 : ℤ)), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.pushOnAny (T := [HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))]) (hPush main (HvdH.Val.int ((3 : ℤ))))
      |> fun h => Pipe.le h (au_le_one hKpush (vszVI hsz_C3))
  have s60 : Pipe main mulProg [HvdH.Val.int ((3 : ℤ)), HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int (eeX3 p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] (Pipe.binOp (hMul main)
        (a := (3 : ℤ)) (b := (p : ℤ)) trivial))
      (au_le_mul_auPreKit hKmul hsz_C3 hsz_P)
  have s61 : Pipe main (pushProg (HvdH.Val.int ((100 : ℤ)))) [HvdH.Val.int (eeX3 p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int ((100 : ℤ)), HvdH.Val.int (eeX3 p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.pushOnAny (T := [HvdH.Val.int (eeX3 p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))]) (hPush main (HvdH.Val.int ((100 : ℤ))))
      |> fun h => Pipe.le h (au_le_one hKpush (vszVI hsz_C100))
  have s62 : Pipe main addProg [HvdH.Val.int ((100 : ℤ)), HvdH.Val.int (eeX3 p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int (eeW1 p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] (Pipe.binOp (hAdd main)
        (a := (100 : ℤ)) (b := eeX3 p) trivial))
      (au_le_two hKadd hsz_C100 hsz_X3)
  have s63 : Pipe main dupProg [HvdH.Val.int (eeW1 p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int (eeW1 p), HvdH.Val.int (eeW1 p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.appendTail [HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] (Pipe.dup main hDup (HvdH.Val.int (eeW1 p)))
      |> fun h => Pipe.le h (au_le_one hKdup (vszVI hsz_W1))
  have s64 : Pipe main addProg [HvdH.Val.int (eeW1 p), HvdH.Val.int (eeW1 p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] (Pipe.binOp (hAdd main)
        (a := eeW1 p) (b := eeW1 p) trivial))
      (au_le_two hKadd hsz_W1 hsz_W1)
  have s65 : Pipe main (pushProg (HvdH.Val.int ((10 : ℤ)))) [HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int ((10 : ℤ)), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.pushOnAny (T := [HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))]) (hPush main (HvdH.Val.int ((10 : ℤ))))
      |> fun h => Pipe.le h (au_le_one hKpush (vszVI hsz_C10))
  have s66 : Pipe main (pickProg 6) [HvdH.Val.int ((10 : ℤ)), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((10 : ℤ)), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int ((10 : ℤ)), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))]) (k := 6) (by simp))
      (au_le_roll hKpick (A := [HvdH.Val.int ((10 : ℤ)), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))]) (k := 6) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_C10
        · exact vszVI hsz_NST
        · exact vszVI hsz_EN
        · exact vszVI hsz_Z
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P))
  have s67 : Pipe main addProg [HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((10 : ℤ)), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int (eeX10 p), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] (Pipe.binOp (hAdd main)
        (a := (p : ℤ)) (b := (10 : ℤ)) trivial))
      (au_le_two hKadd hsz_P hsz_C10)
  have s68 : Pipe main (pickProg 2) [HvdH.Val.int (eeX10 p), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int (eeEN p), HvdH.Val.int (eeX10 p), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int (eeX10 p), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))]) (k := 2) (by simp))
      (au_le_roll hKpick (A := [HvdH.Val.int (eeX10 p), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))]) (k := 2) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_X10
        · exact vszVI hsz_NST
        · exact vszVI hsz_EN
        · exact vszVI hsz_Z
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P))
  have s69 : Pipe main mulProg [HvdH.Val.int (eeEN p), HvdH.Val.int (eeX10 p), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int (eeB p), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] (Pipe.binOp (hMul main)
        (a := eeEN p) (b := eeX10 p) trivial))
      (au_le_mul_auPreKit hKmul hsz_EN hsz_X10)
  have s70 : Pipe main (pickProg 3) [HvdH.Val.int (eeB p), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeB p), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.le (Pipe.pick main hPick (A := [HvdH.Val.int (eeB p), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))]) (k := 3) (by simp))
      (au_le_roll hKpick (A := [HvdH.Val.int (eeB p), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))]) (k := 3) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_B
        · exact vszVI hsz_NST
        · exact vszVI hsz_EN
        · exact vszVI hsz_Z
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P))
  have s71 : Pipe main swapProg [HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeB p), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int (eeB p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] (Pipe.swap main hSwap (HvdH.Val.int (eeZ p α t N)) (HvdH.Val.int (eeB p))))
      (au_le_three hKswap (vszVI hsz_Z) (vszVI hsz_B) (by simp only [auSZ]; omega))
  have s72 : Pipe main ltProg [HvdH.Val.int (eeB p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int (eeFLG p α t N), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] CB := by
    exact     Pipe.le (Pipe.appendTail [HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] (Pipe.binOp (hLt main)
        (a := eeB p) (b := eeZ p α t N) trivial))
      (au_le_two hKlt hsz_B hsz_Z)
  have s73 : Pipe main (rollProg 6) [HvdH.Val.int (eeFLG p α t N), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))] [HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeFLG p α t N), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α)] CB := by
    exact     Pipe.le (Pipe.roll main hRoll (A := [HvdH.Val.int (eeFLG p α t N), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))]) (k := 6) (by simp))
      (au_le_roll hKroll (A := [HvdH.Val.int (eeFLG p α t N), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α), HvdH.Val.int ((p : ℤ))]) (k := 6) (by norm_num) (by simp) (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact vszVI hsz_FLG
        · exact vszVI hsz_NST
        · exact vszVI hsz_EN
        · exact vszVI hsz_Z
        · exact vszVI hsz_EN
        · exact vszVI hsz_EN2
        · exact vszVI hsz_P))
  have s74 : Pipe main dropProg [HvdH.Val.int ((p : ℤ)), HvdH.Val.int (eeFLG p α t N), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α)] [HvdH.Val.int (eeFLG p α t N), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α)] CB := by
    exact     Pipe.appendTail [HvdH.Val.int (eeFLG p α t N), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α)] (Pipe.drop main hDrop (HvdH.Val.int ((p : ℤ))))
      |> fun h => Pipe.le h (au_le_one hKdrop (vszVI hsz_P))
  have g1 : Pipe main (pickProg 0) [HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] [HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] (1 * CB) := by rw [Nat.one_mul]; exact s1
  have g2 := hstep g1 s2
  have g3 := hstep g2 s3
  have g4 := hstep g3 s4
  have g5 := hstep g4 s5
  have g6 := hstep g5 s6
  have g7 := hstep g6 s7
  have g8 := hstep g7 s8
  have g9 := hstep g8 s9
  have g10 := hstep g9 s10
  have g11 := hstep g10 s11
  have g12 := hstep g11 s12
  have g13 := hstep g12 s13
  have g14 := hstep g13 s14
  have g15 := hstep g14 s15
  have g16 := hstep g15 s16
  have g17 := hstep g16 s17
  have g18 := hstep g17 s18
  have g19 := hstep g18 s19
  have g20 := hstep g19 s20
  have g21 := hstep g20 s21
  have g22 := hstep g21 s22
  have g23 := hstep g22 s23
  have g24 := hstep g23 s24
  have g25 := hstep g24 s25
  have g26 := hstep g25 s26
  have g27 := hstep g26 s27
  have g28 := hstep g27 s28
  have g29 := hstep g28 s29
  have g30 := hstep g29 s30
  have g31 := hstep g30 s31
  have g32 := hstep g31 s32
  have g33 := hstep g32 s33
  have g34 := hstep g33 s34
  have g35 := hstep g34 s35
  have g36 := hstep g35 s36
  have g37 := hstep g36 s37
  have g38 := hstep g37 s38
  have g39 := hstep g38 s39
  have g40 := hstep g39 s40
  have g41 := hstep g40 s41
  have g42 := hstep g41 s42
  have g43 := hstep g42 s43
  have g44 := hstep g43 s44
  have g45 := hstep g44 s45
  have g46 := hstep g45 s46
  have g47 := hstep g46 s47
  have g48 := hstep g47 s48
  have g49 := hstep g48 s49
  have g50 := hstep g49 s50
  have g51 := hstep g50 s51
  have g52 := hstep g51 s52
  have g53 := hstep g52 s53
  have g54 := hstep g53 s54
  have g55 := hstep g54 s55
  have g56 := hstep g55 s56
  have g57 := hstep g56 s57
  have g58 := hstep g57 s58
  have g59 := hstep g58 s59
  have g60 := hstep g59 s60
  have g61 := hstep g60 s61
  have g62 := hstep g61 s62
  have g63 := hstep g62 s63
  have g64 := hstep g63 s64
  have g65 := hstep g64 s65
  have g66 := hstep g65 s66
  have g67 := hstep g66 s67
  have g68 := hstep g67 s68
  have g69 := hstep g68 s69
  have g70 := hstep g69 s70
  have g71 := hstep g70 s71
  have g72 := hstep g71 s72
  have g73 := hstep g72 s73
  have g74 := hstep g73 s74
  have hfinal : Pipe main P [HvdH.Val.int ((p : ℤ)), HvdH.Val.int ((α : ℤ)), HvdH.Val.int ((t : ℤ)), HvdH.Val.int (N), HvdH.Val.int (auPi p)] ([HvdH.Val.int (eeFLG p α t N), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α)]) (300 * CB) :=
    Pipe.le g74 (Nat.mul_le_mul_right CB (by norm_num))
  -- the computed values are the values of the statement
  have hZeq : eeZ p α t N = auZ p α t N := by
    rw [eeZ, eeZP, eeDE, eeD, eeT2, eeA2, eeF, eeE]
    rcases eq_or_ne α 0 with hα0 | hα0
    · have hA0 : ((α : ℤ)) = 0 := by rw [hα0]; simp
      have hE : (if ((α : ℕ) : ℤ) = 0 then (1 : ℤ) else 0) = 1 := by rw [hα0]; simp
      have hF : ((1 : ℤ) - (if ((α : ℕ) : ℤ) = 0 then (1 : ℤ) else 0)) = 0 := by rw [hE]; ring
      have hDE : (((t : ℤ) * (t : ℤ)) * ((α : ℤ) * (α : ℤ)) + (if ((α : ℕ) : ℤ) = 0 then (1 : ℤ) else 0)) = 1 := by rw [hE, hA0]; norm_num
      have hZ0 : auZ p α t N = 0 := by rw [auZ, hA0]; simp
      rw [hDE, hF, mul_zero, hZ0]
    · have hE : (if ((α : ℕ) : ℤ) = 0 then (1 : ℤ) else 0) = 0 := by simp [hα0]
      have hF : ((1 : ℤ) - (if ((α : ℕ) : ℤ) = 0 then (1 : ℤ) else 0)) = 1 := by rw [hE]; ring
      have hDE : (((t : ℤ) * (t : ℤ)) * ((α : ℤ) * (α : ℤ)) + (if ((α : ℕ) : ℤ) = 0 then (1 : ℤ) else 0)) = (((t : ℤ) * (t : ℤ)) * ((α : ℤ) * (α : ℤ))) := by rw [hE, add_zero]
      have hDv : (((t : ℤ) * (t : ℤ)) * ((α : ℤ) * (α : ℤ))) = ((α : ℤ) ^ 2 * (t : ℤ) ^ 2) := by ring
      rw [hDE, hF, mul_one, auZ, hDv, mul_comm N (auPi p)]
  have hNSTeq : eeNST p = ((auNstep p : ℕ) : ℤ) := by
    rw [eeNST, eeW1]
    have h1 : ((100 : ℤ) + 3 * (p : ℤ)) = ((auPrec p : ℕ) : ℤ) := by simp only [auPrec]; push_cast; ring
    rw [h1, ← Nat.cast_add]
    congr 1
    simp only [auNstep]
    ring
  have hENeq : eeEN p = auEn p := by
    rw [eeEN, eeW1]
    have h1 : ((100 : ℤ) + 3 * (p : ℤ)) = ((auPrec p : ℕ) : ℤ) := by simp only [auPrec]; push_cast; ring
    rw [h1, Int.toNat_natCast]
    rfl
  have hEN2eq : eeEN2 p α = auEn2 p α := by
    rw [eeEN2, eeAA2, eeENP, eeW2]
    have h1 : ((100 : ℤ) + 3 * (p : ℤ) - (p : ℤ)) = ((2 * p + 100 : ℕ) : ℤ) := by push_cast; ring
    rw [h1, Int.toNat_natCast]
    rw [show (2 * p + 100 : ℕ) = auPrec p - p by simp only [auPrec]; omega]
    have h2 : ((α : ℤ) + (α : ℤ)) = 2 * (α : ℤ) := by ring
    rw [h2]
    simp only [auEn2, auEnP]
    ring
  have hBeq : eeB p = auBnd p := by
    rw [eeB, eeEN, eeX10, eeW1]
    have h1 : ((p : ℤ) + 10) = ((p + 10 : ℕ) : ℤ) := by push_cast; ring
    have h2 : (2 : ℤ) ^ ((100 : ℤ) + 3 * (p : ℤ)).toNat = auEn p := by
      rw [show (100 : ℤ) + 3 * (p : ℤ) = ((auPrec p : ℕ) : ℤ) by simp only [auPrec]; push_cast; ring]
      rw [Int.toNat_natCast]
      rfl
    rw [h2, h1, mul_comm (auEn p) ((p + 10 : ℕ) : ℤ)]
    rfl
  have hFLGeq : eeFLG p α t N = auFlg p α t N := by
    rw [eeFLG, hBeq, hZeq]
    rfl
  have hW : [HvdH.Val.int (eeFLG p α t N), HvdH.Val.int (eeNST p), HvdH.Val.int (eeEN p), HvdH.Val.int (eeZ p α t N), HvdH.Val.int (eeEN p), HvdH.Val.int (eeEN2 p α)] =
      [HvdH.Val.int (auFlg p α t N), HvdH.Val.int ((auNstep p : ℕ) : ℤ),
        HvdH.Val.int (auEn p), HvdH.Val.int (auZ p α t N),
        HvdH.Val.int (auEn p), HvdH.Val.int (auEn2 p α)] := by
    rw [hFLGeq, hNSTeq, hENeq, hZeq, hEN2eq]
  exact Pipe.toWordR (Pipe.rw hfinal hW)

end Work.Resample
