import Mathlib
import Submission.Work.Resample.auPrepDefs
import Submission.Work.Resample.auKit
import Submission.Work.Fx.piDefs
import Submission.Work.Kernel.Raw
import Submission.Work.IntLib.encodeNatBridge

/-!
# Toolkit for `Work.Resample.auPreChain`: the "pre" word of the 1-D resampling

The lemma `auPreChain` produces a word turning the four parameters `[int p, int α, int s, int t]`
into the window

`[ofList (auKs p t), int p, int α, int s, int t, int (auPi p), int (auCop p α s), int (auOff p α s)]`

at cost `K*(t+1)*(p+1)^K`.  It is the first phase of the table word of `Work.Resample.sliceAu`
(paper §4, Lemma 4.9): the label list `auKs p t` (whose `k`-th element is the record label
`cons (int k) (int (auPi p))`) is handed to the element word of the table, together with the
static parameters `auPi p` (the fixed-point `2^auPrec p·π`), `auCop p α s` and `auOff p α s`
(the extended-array shift data of the resampling).

The program is a straight-line chain of library calls; the file is organised as

* the *values* computed by the program (definitions `sqz`, `mz`, ..., `precz`) and the lemmas
  identifying them with the mathematical objects `auM`, `auOff`, `auCop`, `auPrec`;
* the *size* lemmas giving `isz v ≤ auSZ p` for every intermediate value;
* the *chain* itself, composed linearly with `Pipe.comp`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH
open Work.Fx

/-! ## The values computed by the pre-word -/

/-- `√p` as computed by the `sqrt` word (from the integer value `int p`). -/
def sqz (p : ℕ) : ℤ := (Nat.sqrt (((p : ℤ)).toNat) : ℤ)

/-- `√p + 1`. -/
def s1z (p : ℕ) : ℤ := (1 : ℤ) + sqz p

/-- `m = (⌈√p⌉+1)·α` as computed: `α·(√p+1)`. -/
def mz (p α : ℕ) : ℤ := (α : ℤ) * s1z p

/-- `m + s` as computed. -/
def X1z (p α s : ℕ) : ℤ := mz p α + (s : ℤ)

/-- `m + s - 1` as computed: `(m + s) - 1`. -/
def X2z (p α s : ℕ) : ℤ := (mz p α + (s : ℤ)) - 1


/-- `⌈m/s⌉ = (m+s-1)/s` as computed. -/
def qz (p α s : ℕ) : ℤ := Int.tdiv (X2z p α s) (s : ℤ)

/-- `s·⌈m/s⌉`. -/
def szq (p α s : ℕ) : ℤ := (s : ℤ) * qz p α s

/-- the offset `auOff p α s` as computed. -/
def offz (p α s : ℕ) : ℤ := szq p α s - mz p α

/-- `2s`. -/
def t2sz (s : ℕ) : ℤ := (2 : ℤ) * (s : ℤ)

/-- `2m`. -/
def t2mz (p α : ℕ) : ℤ := (2 : ℤ) * mz p α

/-- `2m + 2s` as computed. -/
def Z1z (p α s : ℕ) : ℤ := t2mz p α + t2sz s

/-- `3p` as computed. -/
def P3z (p : ℕ) : ℤ := (3 : ℤ) * (p : ℤ)

/-- `auOff p α s + 2s + 2m` as computed. -/
def Yz (p α s : ℕ) : ℤ := offz p α s + (t2mz p α + t2sz s)

/-- the copy number `auCop p α s` as computed. -/
def copz (p α s : ℕ) : ℤ := Int.tdiv (Yz p α s) (s : ℤ)

/-- the working precision `auPrec p = 3p+100` as computed. -/
def precz (p : ℕ) : ℤ := (100 : ℤ) + (3 : ℤ) * (p : ℤ)

/-! ## Identifications with the mathematical values -/

theorem sqz_eq (p : ℕ) : sqz p = ((Nat.sqrt p : ℕ) : ℤ) := by
  simp only [sqz, Int.toNat_natCast]

theorem s1z_eq (p : ℕ) : s1z p = ((Nat.sqrt p + 1 : ℕ) : ℤ) := by
  simp only [s1z, sqz_eq]; push_cast; ring

theorem mz_eq (p α : ℕ) : mz p α = ((auM p α : ℕ) : ℤ) := by
  simp only [mz, s1z_eq, auM]; push_cast; ring

theorem X2z_eq (p α s : ℕ) (hα : 1 ≤ α) : X2z p α s = ((auM p α + s - 1 : ℕ) : ℤ) := by
  have h1 : 1 ≤ auM p α + s := by simp only [auM]; nlinarith [Nat.zero_le p, Nat.zero_le s, hα]
  rw [X2z, mz_eq, ← Nat.cast_add, Nat.cast_sub h1, Nat.cast_one]

theorem qz_eq (p α s : ℕ) (hα : 1 ≤ α) (hs : 1 ≤ s) :
    qz p α s = (((auM p α + s - 1) / s : ℕ) : ℤ) := by
  rw [qz, X2z_eq p α s hα, ← natCast_div_eq_tdiv (auM p α + s - 1) hs]

theorem offz_eq (p α s : ℕ) (hα : 1 ≤ α) (hs : 1 ≤ s) :
    offz p α s = ((auOff p α s : ℕ) : ℤ) := by
  rw [offz, szq, qz_eq p α s hα hs, mz_eq, ← auOff_cast p α s hs]

theorem Yz_eq (p α s : ℕ) (hα : 1 ≤ α) (hs : 1 ≤ s) :
    Yz p α s = ((auOff p α s : ℕ) : ℤ) + 2 * (s : ℤ) + 2 * (auM p α : ℤ) := by
  rw [Yz, t2mz, t2sz, offz_eq p α s hα hs, mz_eq]
  ring

theorem copz_eq (p α s : ℕ) (hα : 1 ≤ α) (hs : 1 ≤ s) :
    copz p α s = ((auCop p α s : ℕ) : ℤ) := by
  rw [copz, Yz_eq p α s hα hs, ← auCop_cast p α s hs]

theorem precz_eq (p : ℕ) : precz p = ((auPrec p : ℕ) : ℤ) := by
  rw [precz, auPrec]; push_cast; ring

/-! ## Sizes of the intermediate values -/

theorem vsz_int_eq (z : ℤ) : vsz (Val.int z) = isz z := Work.IntLib.vsz_int z

theorem vszVI {z : ℤ} {p : ℕ} (h : isz z ≤ auSZ p) : vsz (Val.int z) ≤ auSZ p := by
  rw [vsz_int_eq]; exact h

theorem natAbs_add_bd {a b : ℤ} {A B N : ℕ} (ha : a.natAbs ≤ 2 ^ A) (hb : b.natAbs ≤ 2 ^ B)
    (hA : A + 1 ≤ N) (hB : B + 1 ≤ N) : (a + b).natAbs ≤ 2 ^ N := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hA' : A ≤ M := by omega
  have hB' : B ≤ M := by omega
  have h2 : a.natAbs ≤ 2 ^ M := le_trans ha (Nat.pow_le_pow_right (by norm_num) hA')
  have h3 : b.natAbs ≤ 2 ^ M := le_trans hb (Nat.pow_le_pow_right (by norm_num) hB')
  have h5 : a.natAbs + b.natAbs ≤ 2 ^ (M + 1) := by
    have h4 : 2 ^ (M + 1) = 2 ^ M + 2 ^ M := by rw [pow_succ]; ring
    omega
  exact le_trans (Int.natAbs_add_le a b) h5

theorem natAbs_sub_bd {a b : ℤ} {A B N : ℕ} (ha : a.natAbs ≤ 2 ^ A) (hb : b.natAbs ≤ 2 ^ B)
    (hA : A + 1 ≤ N) (hB : B + 1 ≤ N) : (a - b).natAbs ≤ 2 ^ N := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hA' : A ≤ M := by omega
  have hB' : B ≤ M := by omega
  have h2 : a.natAbs ≤ 2 ^ M := le_trans ha (Nat.pow_le_pow_right (by norm_num) hA')
  have h3 : b.natAbs ≤ 2 ^ M := le_trans hb (Nat.pow_le_pow_right (by norm_num) hB')
  have h5 : a.natAbs + b.natAbs ≤ 2 ^ (M + 1) := by
    have h4 : 2 ^ (M + 1) = 2 ^ M + 2 ^ M := by rw [pow_succ]; ring
    omega
  exact le_trans (Int.natAbs_sub_le a b) h5

theorem natAbs_mul_bd {a b : ℤ} {A B N : ℕ} (ha : a.natAbs ≤ 2 ^ A) (hb : b.natAbs ≤ 2 ^ B)
    (hN : A + B ≤ N) : (a * b).natAbs ≤ 2 ^ N := by
  rw [Int.natAbs_mul]
  calc a.natAbs * b.natAbs ≤ 2 ^ A * 2 ^ B := Nat.mul_le_mul ha hb
    _ = 2 ^ (A + B) := by rw [pow_add]
    _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN

theorem natAbs_tdiv_bd {a b : ℤ} {A N : ℕ} (ha : a.natAbs ≤ 2 ^ A) (hN : A ≤ N) :
    (Int.tdiv a b).natAbs ≤ 2 ^ N := by
  rw [Int.natAbs_tdiv]
  exact le_trans (Nat.div_le_self _ _) (le_trans ha (Nat.pow_le_pow_right (by norm_num) hN))

theorem natAbs_natCast_bd {m N : ℕ} (h : m ≤ 2 ^ N) : ((m : ℤ)).natAbs ≤ 2 ^ N := by
  rwa [Int.natAbs_natCast]

theorem isz_le_auSZ_of_natAbs_le {z : ℤ} {p N : ℕ} (h : z.natAbs ≤ 2 ^ N) (hN : N ≤ 10 * p + 397) :
    isz z ≤ auSZ p := by
  refine isz_le_auSZ_of_lt (N := N + 1) ?_ (by omega)
  exact lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.lt_succ_self N))

theorem isz_natCast_bd {m N p : ℕ} (h : m ≤ 2 ^ N) (hN : N ≤ 10 * p + 397) :
    isz ((m : ℤ)) ≤ auSZ p :=
  isz_le_auSZ_of_natAbs_le (natAbs_natCast_bd h) hN

/-- `α ≤ 2^p` from `α² < p`. -/
theorem alpha_le_two_pow (p α : ℕ) (hαp : α ^ 2 < p) : α ≤ 2 ^ p := by
  have h1 : α ≤ α ^ 2 := by
    rcases Nat.eq_zero_or_pos α with h | h
    · simp [h]
    · calc α = α * 1 := by ring
        _ ≤ α * α := Nat.mul_le_mul_left α h
        _ = α ^ 2 := by ring
  exact le_trans (le_trans h1 (le_of_lt hαp)) (le_of_lt (Nat.lt_two_pow_self (n := p)))

theorem isz_p_le (p : ℕ) : isz ((p : ℤ)) ≤ auSZ p :=
  isz_natCast_bd (N := p) (le_of_lt (Nat.lt_two_pow_self (n := p))) (by omega)

theorem isz_alpha_le (p α : ℕ) (hαp : α ^ 2 < p) : isz ((α : ℤ)) ≤ auSZ p :=
  isz_natCast_bd (N := p) (alpha_le_two_pow p α hαp) (by omega)

theorem isz_s_le (p s t : ℕ) (hst : s < t) (htp : t < 2 ^ p) : isz ((s : ℤ)) ≤ auSZ p :=
  isz_natCast_bd (N := p) (le_of_lt (lt_trans hst htp)) (by omega)

theorem isz_t_le (p t : ℕ) (htp : t < 2 ^ p) : isz ((t : ℤ)) ≤ auSZ p :=
  isz_natCast_bd (N := p) (le_of_lt htp) (by omega)

theorem isz_small_le (p m : ℕ) (h : m ≤ 400) : isz ((m : ℤ)) ≤ auSZ p :=
  isz_natCast_bd (N := 9) (le_trans h (by norm_num)) (by omega)

/-! ### The intermediate values -/

theorem isz_sqz_le (p : ℕ) : isz (sqz p) ≤ auSZ p := by
  rw [sqz_eq]
  refine isz_natCast_bd (N := p) ?_ (by omega)
  exact le_trans (Nat.sqrt_le_self p) (le_of_lt (Nat.lt_two_pow_self (n := p)))

theorem isz_s1z_le (p : ℕ) : isz (s1z p) ≤ auSZ p := by
  rw [s1z_eq]
  refine isz_natCast_bd (N := p + 1) ?_ (by omega)
  calc Nat.sqrt p + 1 ≤ p + 1 := Nat.add_le_add_right (Nat.sqrt_le_self p) 1
    _ ≤ 2 ^ (p + 1) := le_of_lt (Nat.lt_two_pow_self (n := p + 1))

/-- `√p + 1 ≤ 2^(p+1)`. -/
theorem sqrt_succ_le (p : ℕ) : Nat.sqrt p + 1 ≤ 2 ^ (p + 1) :=
  calc Nat.sqrt p + 1 ≤ p + 1 := Nat.add_le_add_right (Nat.sqrt_le_self p) 1
    _ ≤ 2 ^ (p + 1) := le_of_lt (Nat.lt_two_pow_self (n := p + 1))

theorem natAbs_mz_le (p α : ℕ) (hαp : α ^ 2 < p) : (mz p α).natAbs ≤ 2 ^ (2 * p + 1) := by
  rw [mz_eq, Int.natAbs_natCast]
  calc auM p α = (Nat.sqrt p + 1) * α := rfl
    _ ≤ 2 ^ (p + 1) * 2 ^ p := Nat.mul_le_mul (sqrt_succ_le p) (alpha_le_two_pow p α hαp)
    _ = 2 ^ (2 * p + 1) := by rw [← pow_add]; ring_nf

theorem isz_mz_le (p α : ℕ) (hαp : α ^ 2 < p) : isz (mz p α) ≤ auSZ p :=
  isz_le_auSZ_of_natAbs_le (natAbs_mz_le p α hαp) (by omega)

theorem natAbs_X2z_le (p α s : ℕ) (hαp : α ^ 2 < p) (hs2 : s ≤ 2 ^ p) :
    (X2z p α s).natAbs ≤ 2 ^ (2 * p + 3) := by
  have h1 : (mz p α).natAbs ≤ 2 ^ (2 * p + 1) := natAbs_mz_le p α hαp
  have h2 : ((s : ℤ)).natAbs ≤ 2 ^ p := by rw [Int.natAbs_natCast]; exact hs2
  have h3 : ((1 : ℤ)).natAbs ≤ 2 ^ 0 := by norm_num
  rw [X2z]
  have h4 : (mz p α + (s : ℤ)).natAbs ≤ 2 ^ (2 * p + 2) :=
    natAbs_add_bd h1 h2 (by omega) (by omega)
  exact natAbs_sub_bd h4 h3 (by omega) (by omega)

theorem isz_X2z_le (p α s : ℕ) (hαp : α ^ 2 < p) (hs2 : s ≤ 2 ^ p) :
    isz (X2z p α s) ≤ auSZ p :=
  isz_le_auSZ_of_natAbs_le (natAbs_X2z_le p α s hαp hs2) (by omega)

theorem natAbs_qz_le (p α s : ℕ) (hαp : α ^ 2 < p) (hs2 : s ≤ 2 ^ p) :
    (qz p α s).natAbs ≤ 2 ^ (2 * p + 3) :=
  natAbs_tdiv_bd (natAbs_X2z_le p α s hαp hs2) (by omega)

theorem isz_qz_le (p α s : ℕ) (hαp : α ^ 2 < p) (hs2 : s ≤ 2 ^ p) :
    isz (qz p α s) ≤ auSZ p :=
  isz_le_auSZ_of_natAbs_le (natAbs_qz_le p α s hαp hs2) (by omega)

theorem natAbs_szq_le (p α s : ℕ) (hαp : α ^ 2 < p) (hs2 : s ≤ 2 ^ p) :
    (szq p α s).natAbs ≤ 2 ^ (3 * p + 3) := by
  rw [szq]
  have h1 : ((s : ℤ)).natAbs ≤ 2 ^ p := by rw [Int.natAbs_natCast]; exact hs2
  have h2 : (qz p α s).natAbs ≤ 2 ^ (2 * p + 3) := natAbs_qz_le p α s hαp hs2
  exact natAbs_mul_bd h1 h2 (by omega)

theorem isz_szq_le (p α s : ℕ) (hαp : α ^ 2 < p) (hs2 : s ≤ 2 ^ p) :
    isz (szq p α s) ≤ auSZ p :=
  isz_le_auSZ_of_natAbs_le (natAbs_szq_le p α s hαp hs2) (by omega)

theorem natAbs_offz_le (p α s : ℕ) (hαp : α ^ 2 < p) (hs2 : s ≤ 2 ^ p) :
    (offz p α s).natAbs ≤ 2 ^ (3 * p + 4) :=
  natAbs_sub_bd (natAbs_szq_le p α s hαp hs2) (natAbs_mz_le p α hαp) (by omega) (by omega)

theorem isz_offz_le (p α s : ℕ) (hαp : α ^ 2 < p) (hs2 : s ≤ 2 ^ p) :
    isz (offz p α s) ≤ auSZ p :=
  isz_le_auSZ_of_natAbs_le (natAbs_offz_le p α s hαp hs2) (by omega)

theorem natAbs_t2sz_le (p s : ℕ) (hs2 : s ≤ 2 ^ p) : (t2sz s).natAbs ≤ 2 ^ (p + 1) := by
  rw [t2sz]
  have h1 : ((2 : ℤ)).natAbs ≤ 2 ^ 1 := by norm_num
  have h2 : ((s : ℤ)).natAbs ≤ 2 ^ p := by rw [Int.natAbs_natCast]; exact hs2
  exact natAbs_mul_bd h1 h2 (by omega)

theorem isz_t2sz_le (p s : ℕ) (hs2 : s ≤ 2 ^ p) : isz (t2sz s) ≤ auSZ p :=
  isz_le_auSZ_of_natAbs_le (natAbs_t2sz_le p s hs2) (by omega)

theorem natAbs_t2mz_le (p α : ℕ) (hαp : α ^ 2 < p) : (t2mz p α).natAbs ≤ 2 ^ (2 * p + 2) := by
  rw [t2mz]
  have h1 : ((2 : ℤ)).natAbs ≤ 2 ^ 1 := by norm_num
  exact natAbs_mul_bd h1 (natAbs_mz_le p α hαp) (by omega)

theorem isz_t2mz_le (p α : ℕ) (hαp : α ^ 2 < p) : isz (t2mz p α) ≤ auSZ p :=
  isz_le_auSZ_of_natAbs_le (natAbs_t2mz_le p α hαp) (by omega)

theorem natAbs_Yz_le (p α s : ℕ) (hαp : α ^ 2 < p) (hs2 : s ≤ 2 ^ p) :
    (Yz p α s).natAbs ≤ 2 ^ (3 * p + 5) := by
  rw [Yz]
  have h1 := natAbs_offz_le p α s hαp hs2
  have h2 : (t2mz p α + t2sz s).natAbs ≤ 2 ^ (2 * p + 3) :=
    natAbs_add_bd (natAbs_t2mz_le p α hαp) (natAbs_t2sz_le p s hs2) (by omega) (by omega)
  exact natAbs_add_bd h1 h2 (by omega) (by omega)

theorem isz_Yz_le (p α s : ℕ) (hαp : α ^ 2 < p) (hs2 : s ≤ 2 ^ p) :
    isz (Yz p α s) ≤ auSZ p :=
  isz_le_auSZ_of_natAbs_le (natAbs_Yz_le p α s hαp hs2) (by omega)

theorem natAbs_copz_le (p α s : ℕ) (hαp : α ^ 2 < p) (hs2 : s ≤ 2 ^ p) :
    (copz p α s).natAbs ≤ 2 ^ (3 * p + 5) :=
  natAbs_tdiv_bd (natAbs_Yz_le p α s hαp hs2) (by omega)

theorem isz_copz_le (p α s : ℕ) (hαp : α ^ 2 < p) (hs2 : s ≤ 2 ^ p) :
    isz (copz p α s) ≤ auSZ p :=
  isz_le_auSZ_of_natAbs_le (natAbs_copz_le p α s hαp hs2) (by omega)

theorem natAbs_precz_le (p : ℕ) : (precz p).natAbs ≤ 2 ^ (p + 8) := by
  rw [precz]
  have h1 : ((100 : ℤ)).natAbs ≤ 2 ^ 7 := by norm_num
  have h2 : ((3 : ℤ) * (p : ℤ)).natAbs ≤ 2 ^ (p + 2) :=
    natAbs_mul_bd (by norm_num : ((3 : ℤ)).natAbs ≤ 2 ^ 2)
      (natAbs_natCast_bd (le_of_lt (Nat.lt_two_pow_self (n := p)))) (by omega)
  exact natAbs_add_bd h1 h2 (by omega) (by omega)

theorem isz_precz_le (p : ℕ) : isz (precz p) ≤ auSZ p :=
  isz_le_auSZ_of_natAbs_le (natAbs_precz_le p) (by omega)

/-! ### Two further intermediate values -/

theorem natAbs_X1z_le (p α s : ℕ) (hαp : α ^ 2 < p) (hs2 : s ≤ 2 ^ p) :
    (X1z p α s).natAbs ≤ 2 ^ (2 * p + 2) := by
  have h1 : (mz p α).natAbs ≤ 2 ^ (2 * p + 1) := natAbs_mz_le p α hαp
  have h2 : ((s : ℤ)).natAbs ≤ 2 ^ p := by rw [Int.natAbs_natCast]; exact hs2
  exact natAbs_add_bd h1 h2 (by omega) (by omega)

theorem isz_X1z_le (p α s : ℕ) (hαp : α ^ 2 < p) (hs2 : s ≤ 2 ^ p) :
    isz (X1z p α s) ≤ auSZ p :=
  isz_le_auSZ_of_natAbs_le (natAbs_X1z_le p α s hαp hs2) (by omega)

theorem natAbs_Z1z_le (p α s : ℕ) (hαp : α ^ 2 < p) (hs2 : s ≤ 2 ^ p) :
    (Z1z p α s).natAbs ≤ 2 ^ (2 * p + 3) :=
  natAbs_add_bd (natAbs_t2mz_le p α hαp) (natAbs_t2sz_le p s hs2) (by omega) (by omega)

theorem isz_Z1z_le (p α s : ℕ) (hαp : α ^ 2 < p) (hs2 : s ≤ 2 ^ p) :
    isz (Z1z p α s) ≤ auSZ p :=
  isz_le_auSZ_of_natAbs_le (natAbs_Z1z_le p α s hαp hs2) (by omega)

theorem natAbs_P3z_le (p : ℕ) : (P3z p).natAbs ≤ 2 ^ (p + 2) := by
  rw [P3z]
  exact natAbs_mul_bd (by norm_num : ((3 : ℤ)).natAbs ≤ 2 ^ 2)
    (natAbs_natCast_bd (le_of_lt (Nat.lt_two_pow_self (n := p)))) (by omega)

theorem isz_P3z_le (p : ℕ) : isz (P3z p) ≤ auSZ p :=
  isz_le_auSZ_of_natAbs_le (natAbs_P3z_le p) (by omega)

/-! ### Helpers for the chain: costs, window bookkeeping, word adapters -/

theorem au_le_mul_auPreKit {K KS p : ℕ} (hK : K ≤ KS) {u v : ℕ} (hu : u ≤ auSZ p) (hv : v ≤ auSZ p) :
    K * u * v ≤ auSB p KS := by
  rw [auSB]
  calc K * u * v ≤ KS * auSZ p * auSZ p := Nat.mul_le_mul (Nat.mul_le_mul hK hu) hv
    _ = KS * (auSZ p) ^ 2 := by ring
    _ ≤ KS * (auSZ p + 8) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

theorem vsz_cons_eq (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  show (a.enc ++ b.enc).length + 1 = vsz a + vsz b + 1
  rw [List.length_append]
  rfl

/-- `vsz (ofList l) ≤ (l.length+1)·(B+1)` when every element has size `≤ B`. -/
theorem vsz_ofList_le {l : List Val} {B : ℕ} (h : ∀ x ∈ l, vsz x ≤ B) :
    vsz (ofList l) ≤ (l.length + 1) * (B + 1) := by
  induction l with
  | nil => simp [ofList, vsz, Val.enc]
  | cons x t ih =>
    have hx : vsz x ≤ B := h x (by simp)
    have ht : ∀ y ∈ t, vsz y ≤ B := fun y hy => h y (by simp [hy])
    have ih' := ih ht
    rw [show ofList (x :: t) = Val.cons x (ofList t) from rfl, vsz_cons_eq, List.length_cons]
    nlinarith [ih']

/-- A `WordR` with an explicit `∃ rest` window is a `Pipe`. -/
theorem Pipe.ofWordR {main prog : Cmd} {A B : List Val} {c : ℕ}
    (h : WordR main prog (fun vs => ∃ rest, vs = A ++ rest)
      (fun vs out => ∃ rest, vs = A ++ rest ∧ out = B ++ rest) (fun _ => c)) :
    Pipe main prog A B c := by
  intro rest vs hvs s R hR
  obtain ⟨out, s', n, ⟨r, hvs', hout⟩, hev, hn, hstk, hoth⟩ := h vs ⟨rest, hvs⟩ s R hR
  have hr : r = rest := List.append_cancel_left (hvs'.symm.trans hvs)
  exact ⟨out, s', n, by rw [hout, hr], hev, hn, hstk, hoth⟩

/-- Membership bounds for windows of integer values of length `1` to `9`. -/
theorem vsz_mem_le1 {p : ℕ} {a : ℤ} (ha : vsz (.int a) ≤ auSZ p) :
    ∀ v ∈ ([.int a] : List Val), vsz v ≤ auSZ p := by
  intro v hv; rcases List.mem_singleton.mp hv with rfl; exact ha

theorem vsz_mem_le2 {p : ℕ} {a b : ℤ} (ha : vsz (.int a) ≤ auSZ p) (hb : vsz (.int b) ≤ auSZ p) :
    ∀ v ∈ ([.int a, .int b] : List Val), vsz v ≤ auSZ p := by
  intro v hv; rcases List.mem_cons.mp hv with rfl | hv
  · exact ha
  rcases List.mem_singleton.mp hv with rfl; exact hb

theorem vsz_mem_le3 {p : ℕ} {a b c : ℤ} (ha : vsz (.int a) ≤ auSZ p)
    (hb : vsz (.int b) ≤ auSZ p) (hc : vsz (.int c) ≤ auSZ p) :
    ∀ v ∈ ([.int a, .int b, .int c] : List Val), vsz v ≤ auSZ p := by
  intro v hv; rcases List.mem_cons.mp hv with rfl | hv
  · exact ha
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hb
  rcases List.mem_singleton.mp hv with rfl; exact hc

theorem vsz_mem_le4 {p : ℕ} {a b c d : ℤ} (ha : vsz (.int a) ≤ auSZ p)
    (hb : vsz (.int b) ≤ auSZ p) (hc : vsz (.int c) ≤ auSZ p) (hd : vsz (.int d) ≤ auSZ p) :
    ∀ v ∈ ([.int a, .int b, .int c, .int d] : List Val), vsz v ≤ auSZ p := by
  intro v hv; rcases List.mem_cons.mp hv with rfl | hv
  · exact ha
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hb
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hc
  rcases List.mem_singleton.mp hv with rfl; exact hd

theorem vsz_mem_le5 {p : ℕ} {a b c d e : ℤ} (ha : vsz (.int a) ≤ auSZ p)
    (hb : vsz (.int b) ≤ auSZ p) (hc : vsz (.int c) ≤ auSZ p) (hd : vsz (.int d) ≤ auSZ p)
    (he : vsz (.int e) ≤ auSZ p) :
    ∀ v ∈ ([.int a, .int b, .int c, .int d, .int e] : List Val), vsz v ≤ auSZ p := by
  intro v hv; rcases List.mem_cons.mp hv with rfl | hv
  · exact ha
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hb
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hc
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hd
  rcases List.mem_singleton.mp hv with rfl; exact he

theorem vsz_mem_le6 {p : ℕ} {a b c d e f : ℤ} (ha : vsz (.int a) ≤ auSZ p)
    (hb : vsz (.int b) ≤ auSZ p) (hc : vsz (.int c) ≤ auSZ p) (hd : vsz (.int d) ≤ auSZ p)
    (he : vsz (.int e) ≤ auSZ p) (hf : vsz (.int f) ≤ auSZ p) :
    ∀ v ∈ ([.int a, .int b, .int c, .int d, .int e, .int f] : List Val), vsz v ≤ auSZ p := by
  intro v hv; rcases List.mem_cons.mp hv with rfl | hv
  · exact ha
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hb
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hc
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hd
  rcases List.mem_cons.mp hv with rfl | hv
  · exact he
  rcases List.mem_singleton.mp hv with rfl; exact hf

theorem vsz_mem_le7 {p : ℕ} {a b c d e f g : ℤ} (ha : vsz (.int a) ≤ auSZ p)
    (hb : vsz (.int b) ≤ auSZ p) (hc : vsz (.int c) ≤ auSZ p) (hd : vsz (.int d) ≤ auSZ p)
    (he : vsz (.int e) ≤ auSZ p) (hf : vsz (.int f) ≤ auSZ p) (hg : vsz (.int g) ≤ auSZ p) :
    ∀ v ∈ ([.int a, .int b, .int c, .int d, .int e, .int f, .int g] : List Val),
      vsz v ≤ auSZ p := by
  intro v hv; rcases List.mem_cons.mp hv with rfl | hv
  · exact ha
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hb
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hc
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hd
  rcases List.mem_cons.mp hv with rfl | hv
  · exact he
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hf
  rcases List.mem_singleton.mp hv with rfl; exact hg

theorem vsz_mem_le8 {p : ℕ} {a b c d e f g h : ℤ} (ha : vsz (.int a) ≤ auSZ p)
    (hb : vsz (.int b) ≤ auSZ p) (hc : vsz (.int c) ≤ auSZ p) (hd : vsz (.int d) ≤ auSZ p)
    (he : vsz (.int e) ≤ auSZ p) (hf : vsz (.int f) ≤ auSZ p) (hg : vsz (.int g) ≤ auSZ p)
    (hh : vsz (.int h) ≤ auSZ p) :
    ∀ v ∈ ([.int a, .int b, .int c, .int d, .int e, .int f, .int g, .int h] : List Val),
      vsz v ≤ auSZ p := by
  intro v hv; rcases List.mem_cons.mp hv with rfl | hv
  · exact ha
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hb
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hc
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hd
  rcases List.mem_cons.mp hv with rfl | hv
  · exact he
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hf
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hg
  rcases List.mem_singleton.mp hv with rfl; exact hh

theorem vsz_mem_le9 {p : ℕ} {a b c d e f g h i : ℤ} (ha : vsz (.int a) ≤ auSZ p)
    (hb : vsz (.int b) ≤ auSZ p) (hc : vsz (.int c) ≤ auSZ p) (hd : vsz (.int d) ≤ auSZ p)
    (he : vsz (.int e) ≤ auSZ p) (hf : vsz (.int f) ≤ auSZ p) (hg : vsz (.int g) ≤ auSZ p)
    (hh : vsz (.int h) ≤ auSZ p) (hi : vsz (.int i) ≤ auSZ p) :
    ∀ v ∈ ([.int a, .int b, .int c, .int d, .int e, .int f, .int g, .int h, .int i] : List Val),
      vsz v ≤ auSZ p := by
  intro v hv; rcases List.mem_cons.mp hv with rfl | hv
  · exact ha
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hb
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hc
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hd
  rcases List.mem_cons.mp hv with rfl | hv
  · exact he
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hf
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hg
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hh
  rcases List.mem_singleton.mp hv with rfl; exact hi

/-- Absorb a constant into a large power: `C·b^m ≤ b^e` when `C ≤ 2^c` and `c+m ≤ e`. -/
theorem const_mul_pow_le {C b c m e : ℕ} (hb : 2 ≤ b) (hC : C ≤ 2 ^ c) (h : c + m ≤ e) :
    C * b ^ m ≤ b ^ e := by
  calc C * b ^ m ≤ 2 ^ c * b ^ m := Nat.mul_le_mul_right _ hC
    _ ≤ b ^ c * b ^ m := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hb c)
    _ = b ^ (c + m) := by rw [← pow_add]
    _ ≤ b ^ e := Nat.pow_le_pow_right (by omega) h

end Work.Resample
