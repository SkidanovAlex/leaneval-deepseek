import Mathlib
import Submission.Work.Resample.buKit

/-!
# Kit for the `buZb` word

`Work.Resample.buZb` (the diagonal weight exponent of the one-dimensional `B̃` resampling) is
computed by a chain of `KernelLib`/`IntLib` primitives from the five numbers `ℓ, p, α, s, t`.  This
module fixes the *values* met on the way (as definitions, so that the window of every step of the
word can be named), the two conversion lemmas relating them to `buBeta`/`buZb`, a uniform size bound
`isz · ≤ buSZ p` for each of them, and cost helpers bounding one primitive step of the chain by
`KS * (buSZ p + 8) ^ 2`.

The chain (see `Work.Resample.buZbWord`) is

`A = t·ℓ`, `A+A`, `2tℓ+s`, `q = ⌊(2tℓ+s)/(2s)⌋`, `s·q`, `β = tℓ - s·q` (`= buBeta s t ℓ`),
`β²`, `α²`, `α²β²`, `π·α²β²`, `s²`, `buZb = ⌊π·α²β²/s²⌋`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Resample

open HvdH
open Work.Fx

/-! ## The values -/

/-- `t·ℓ`. -/
def buA (t : ℕ) (ℓ : ℤ) : ℤ := (t : ℤ) * ℓ

/-- `t·ℓ + t·ℓ` (the word computes `A + A`). -/
def buAA (t : ℕ) (ℓ : ℤ) : ℤ := buA t ℓ + buA t ℓ

/-- `2tℓ + s` (the word computes `s + (A + A)`, i.e. `s` on top of `A + A`). -/
def buAAs (s t : ℕ) (ℓ : ℤ) : ℤ := (s : ℤ) + buAA t ℓ

/-- `2s` (the word computes `s + s`). -/
def buS2 (s : ℕ) : ℤ := (s : ℤ) + (s : ℤ)

/-- `q = ⌊(2tℓ+s)/(2s)⌋ = [tℓ/s]`. -/
def buQ (s t : ℕ) (ℓ : ℤ) : ℤ := Int.fdiv (buAAs s t ℓ) (buS2 s)

/-- `s·q` as produced by the word (`s` on top of `q`). -/
def buQS (s t : ℕ) (ℓ : ℤ) : ℤ := (s : ℤ) * buQ s t ℓ

/-- `β²`. -/
noncomputable def buBB (s t : ℕ) (ℓ : ℤ) : ℤ := buBeta s t ℓ * buBeta s t ℓ

/-- `α·α`. -/
def buAl2 (α : ℕ) : ℤ := (α : ℤ) * (α : ℤ)

/-- `α²·β²`. -/
noncomputable def buAlBB (α s t : ℕ) (ℓ : ℤ) : ℤ := buAl2 α * buBB s t ℓ

/-- `π·α²·β²` with `π = auPi p`. -/
noncomputable def buPAlBB (p α s t : ℕ) (ℓ : ℤ) : ℤ := auPi p * buAlBB α s t ℓ

/-- `s·s`. -/
def buSS (s : ℕ) : ℤ := (s : ℤ) * (s : ℤ)

/-! ## The two conversion lemmas -/

/-- The word computes `buBeta s t ℓ`: `β = t·ℓ − q·s`. -/
theorem buBeta_eq_buQS (s t : ℕ) (hs : 0 < s) (ℓ : ℤ) :
    buBeta s t ℓ = buA t ℓ - buQS s t ℓ := by
  have h1 : (2 * ((t : ℤ) * ℓ) + (s : ℤ)) = buAAs s t ℓ := by
    simp only [buAAs, buAA, buA]; ring
  have h2 : 2 * (s : ℤ) = buS2 s := by simp only [buS2]; ring
  rw [buBeta_eq s t hs ℓ, h1, h2]
  simp only [buA, buQS, buQ]
  ring

/-- The word computes `buZb p α s t ℓ`: `⌊π·α²·β² / s²⌋`. -/
theorem buZb_eq_tdiv (p α s t : ℕ) (ℓ : ℤ) :
    buZb p α s t ℓ = Int.tdiv (buPAlBB p α s t ℓ) (buSS s) := by
  simp only [buZb, buPAlBB, buAlBB, buAl2, buBB, buSS, pow_two]

/-! ## Sizes -/

/-- `t·ℓ` has at most `2p` bits. -/
theorem natAbs_buA_le (p s t : ℕ) (ℓ : ℤ) (hℓ : 0 ≤ ℓ) (hℓs : ℓ < (s : ℤ)) (hsp : s < 2 ^ p)
    (htp : t < 2 ^ p) : (buA t ℓ).natAbs ≤ 2 ^ (2 * p) := by
  have h1 : ℓ.natAbs ≤ s := natAbs_le_of ℓ (s : ℤ) (by positivity) (by omega) (by omega)
  rw [buA, Int.natAbs_mul, Int.natAbs_natCast]
  calc t * ℓ.natAbs ≤ t * s := Nat.mul_le_mul_left _ h1
    _ ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul (le_of_lt htp) (le_of_lt hsp)
    _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf

theorem isz_buA_le (p s t : ℕ) (ℓ : ℤ) (hℓ : 0 ≤ ℓ) (hℓs : ℓ < (s : ℤ)) (hsp : s < 2 ^ p)
    (htp : t < 2 ^ p) (hp : 100 ≤ p) : isz (buA t ℓ) ≤ buSZ p :=
  isz_le_buSZ_of (p := p) (A := 2 * p + 1) (by simp only [buSZ]; omega)
    (le_trans (natAbs_buA_le p s t ℓ hℓ hℓs hsp htp)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem isz_buAA_le (p s t : ℕ) (ℓ : ℤ) (hℓ : 0 ≤ ℓ) (hℓs : ℓ < (s : ℤ)) (hsp : s < 2 ^ p)
    (htp : t < 2 ^ p) (hp : 100 ≤ p) : isz (buAA t ℓ) ≤ buSZ p := by
  have h := natAbs_buA_le p s t ℓ hℓ hℓs hsp htp
  refine isz_le_buSZ_of (p := p) (A := 2 * p + 2) (by simp only [buSZ]; omega) ?_
  rw [buAA]
  calc (buA t ℓ + buA t ℓ).natAbs ≤ (buA t ℓ).natAbs + (buA t ℓ).natAbs := Int.natAbs_add_le _ _
    _ ≤ 2 ^ (2 * p) + 2 ^ (2 * p) := Nat.add_le_add h h
    _ = 2 ^ (2 * p + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ (2 * p + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem isz_buAAs_le (p s t : ℕ) (ℓ : ℤ) (hℓ : 0 ≤ ℓ) (hℓs : ℓ < (s : ℤ)) (hsp : s < 2 ^ p)
    (htp : t < 2 ^ p) (hp : 100 ≤ p) : isz (buAAs s t ℓ) ≤ buSZ p := by
  have h := natAbs_buA_le p s t ℓ hℓ hℓs hsp htp
  refine isz_le_buSZ_of (p := p) (A := 2 * p + 2) (by simp only [buSZ]; omega) ?_
  rw [buAAs]
  refine le_trans (Int.natAbs_add_le (s : ℤ) (buAA t ℓ)) ?_
  have h2 : (buAA t ℓ).natAbs ≤ 2 ^ (2 * p + 1) := by
    rw [buAA]
    calc (buA t ℓ + buA t ℓ).natAbs ≤ (buA t ℓ).natAbs + (buA t ℓ).natAbs := Int.natAbs_add_le _ _
      _ ≤ 2 ^ (2 * p) + 2 ^ (2 * p) := Nat.add_le_add h h
      _ = 2 ^ (2 * p + 1) := by rw [pow_succ]; ring
  calc ((s : ℤ)).natAbs + (buAA t ℓ).natAbs ≤ 2 ^ p + 2 ^ (2 * p + 1) :=
        Nat.add_le_add (by simpa using le_of_lt hsp) h2
    _ ≤ 2 ^ (2 * p + 1) + 2 ^ (2 * p + 1) := by
        apply Nat.add_le_add_right
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 ^ (2 * p + 2) := by rw [pow_succ]; ring

theorem isz_buS2_le (p s : ℕ) (hsp : s < 2 ^ p) (hp : 100 ≤ p) : isz (buS2 s) ≤ buSZ p := by
  refine isz_le_buSZ_of (p := p) (A := p + 1) (by simp only [buSZ]; omega) ?_
  rw [buS2]
  calc ((s : ℤ) + (s : ℤ)).natAbs ≤ ((s : ℤ)).natAbs + ((s : ℤ)).natAbs := Int.natAbs_add_le _ _
    _ = s + s := by rw [Int.natAbs_natCast]
    _ = 2 * s := by ring
    _ ≤ 2 * 2 ^ p := Nat.mul_le_mul_left _ (le_of_lt hsp)
    _ = 2 ^ (p + 1) := by rw [pow_succ]; ring

/-- `|[u/v]| · v ≤ |u| + v`. -/
theorem natAbs_rnd_mul_le (u : ℤ) (v : ℕ) (hv : 0 < v) :
    (HvdH.rnd ((u : ℝ) / (v : ℝ))).natAbs * v ≤ u.natAbs + v := by
  set r : ℤ := HvdH.rnd ((u : ℝ) / (v : ℝ)) with hr
  have hrf : (r : ℝ) = ⌊(u : ℝ) / (v : ℝ) + 1 / 2⌋ := rfl
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hfl : (r : ℝ) ≤ (u : ℝ) / (v : ℝ) + 1 / 2 := by rw [hrf]; exact Int.floor_le _
  have hfr : (u : ℝ) / (v : ℝ) + 1 / 2 < (r : ℝ) + 1 := by
    rw [hrf]; exact Int.lt_floor_add_one _
  have h2 : |(u : ℝ) / (v : ℝ) - (r : ℝ)| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  have hg : |(u : ℝ) - (r : ℝ) * (v : ℝ)| ≤ (v : ℝ) := by
    have h1 : (u : ℝ) - (r : ℝ) * (v : ℝ) = (v : ℝ) * ((u : ℝ) / (v : ℝ) - (r : ℝ)) := by
      field_simp
    rw [h1, abs_mul, abs_of_pos hvR]
    nlinarith
  have hcast : (((u - r * (v : ℤ) : ℤ)) : ℝ) = (u : ℝ) - (r : ℝ) * (v : ℝ) := by push_cast; ring
  have hg' : (u - r * (v : ℤ)).natAbs ≤ v := by
    apply natAbs_le_of _ (v : ℤ) (by positivity)
    · have : (-(v : ℤ) : ℝ) ≤ ((u - r * (v : ℤ) : ℤ) : ℝ) := by
        rw [hcast]; exact (abs_le.mp hg).1
      exact_mod_cast this
    · have : (((u - r * (v : ℤ) : ℤ)) : ℝ) ≤ (v : ℤ) := by
        rw [hcast]; exact (abs_le.mp hg).2
      exact_mod_cast this
  calc (HvdH.rnd ((u : ℝ) / (v : ℝ))).natAbs * v
      = r.natAbs * ((v : ℤ)).natAbs := by rw [Int.natAbs_natCast]
    _ = (r * (v : ℤ)).natAbs := (Int.natAbs_mul _ _).symm
    _ = (u - (u - r * (v : ℤ))).natAbs := by ring_nf
    _ ≤ u.natAbs + (u - r * (v : ℤ)).natAbs := Int.natAbs_sub_le _ _
    _ ≤ u.natAbs + v := Nat.add_le_add_left hg' _

/-- `q = [tℓ/s]` as a rounded real quotient. -/
theorem buQ_eq_rnd (s t : ℕ) (ℓ : ℤ) (hs : 0 < s) :
    buQ s t ℓ = HvdH.rnd ((buA t ℓ : ℝ) / (s : ℝ)) := by
  have h1 : buAAs s t ℓ = 2 * buA t ℓ + (s : ℤ) := by simp only [buAAs, buAA]; ring
  have h2 : buS2 s = 2 * (s : ℤ) := by simp only [buS2]; ring
  rw [buQ, h1, h2, ← rnd_eq_fdiv (buA t ℓ) s hs]

theorem natAbs_buQ_le (p s t : ℕ) (ℓ : ℤ) (hs : 0 < s) (hsp : s < 2 ^ p) (hp : 1 ≤ p)
    (hA : (buA t ℓ).natAbs ≤ 2 ^ (2 * p)) : (buQ s t ℓ).natAbs ≤ 2 ^ (2 * p + 1) := by
  rw [buQ_eq_rnd s t ℓ hs]
  have h1 : (HvdH.rnd ((buA t ℓ : ℝ) / (s : ℝ))).natAbs ≤ (buA t ℓ).natAbs + s :=
    le_trans (Nat.le_mul_of_pos_right _ hs) (natAbs_rnd_mul_le (buA t ℓ) s hs)
  calc (HvdH.rnd ((buA t ℓ : ℝ) / (s : ℝ))).natAbs ≤ (buA t ℓ).natAbs + s := h1
    _ ≤ 2 ^ (2 * p) + 2 ^ (2 * p) :=
        Nat.add_le_add hA (le_trans (le_of_lt hsp) (Nat.pow_le_pow_right (by norm_num) (by omega)))
    _ = 2 ^ (2 * p + 1) := by rw [pow_succ]; ring

theorem isz_buQ_le (p s t : ℕ) (ℓ : ℤ) (hℓ : 0 ≤ ℓ) (hℓs : ℓ < (s : ℤ)) (hs : 0 < s)
    (hsp : s < 2 ^ p) (htp : t < 2 ^ p) (hp : 100 ≤ p) : isz (buQ s t ℓ) ≤ buSZ p :=
  isz_le_buSZ_of (p := p) (A := 2 * p + 2) (by simp only [buSZ]; omega)
    (le_trans (natAbs_buQ_le p s t ℓ hs hsp (by omega) (natAbs_buA_le p s t ℓ hℓ hℓs hsp htp))
      (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem isz_buQS_le (p s t : ℕ) (ℓ : ℤ) (hℓ : 0 ≤ ℓ) (hℓs : ℓ < (s : ℤ)) (hs : 0 < s)
    (hsp : s < 2 ^ p) (htp : t < 2 ^ p) (hp : 100 ≤ p) : isz (buQS s t ℓ) ≤ buSZ p := by
  have hq := natAbs_buQ_le p s t ℓ hs hsp (by omega) (natAbs_buA_le p s t ℓ hℓ hℓs hsp htp)
  refine isz_le_buSZ_of (p := p) (A := 3 * p + 1) (by simp only [buSZ]; omega) ?_
  rw [buQS, Int.natAbs_mul, Int.natAbs_natCast]
  calc s * (buQ s t ℓ).natAbs ≤ 2 ^ p * 2 ^ (2 * p + 1) :=
        Nat.mul_le_mul (le_of_lt hsp) hq
    _ = 2 ^ (3 * p + 1) := by rw [← pow_add]; ring_nf

theorem isz_buBB_le (p s t : ℕ) (ℓ : ℤ) (hs : 0 < s) (hsp : s < 2 ^ p) (hp : 100 ≤ p) :
    isz (buBB s t ℓ) ≤ buSZ p := by
  refine isz_le_buSZ_of (p := p) (A := 2 * p + 1) (by simp only [buSZ]; omega) ?_
  rw [buBB, Int.natAbs_mul]
  have h := natAbs_buBeta_le s t hs ℓ
  calc (buBeta s t ℓ).natAbs * (buBeta s t ℓ).natAbs ≤ s * s := Nat.mul_le_mul h h
    _ ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul (le_of_lt hsp) (le_of_lt hsp)
    _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf
    _ ≤ 2 ^ (2 * p + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem isz_buAl2_le (p α : ℕ) (hαp : α ^ 2 < p) (hp : 100 ≤ p) : isz (buAl2 α) ≤ buSZ p := by
  refine isz_le_buSZ_of (p := p) (A := p + 1) (by simp only [buSZ]; omega) ?_
  rw [buAl2, Int.natAbs_mul, Int.natAbs_natCast]
  calc α * α = α ^ 2 := by ring
    _ ≤ p := le_of_lt hαp
    _ ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self)
    _ ≤ 2 ^ (p + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem isz_buAlBB_le (p α s t : ℕ) (ℓ : ℤ) (hαp : α ^ 2 < p) (hs : 0 < s) (hsp : s < 2 ^ p)
    (hp : 100 ≤ p) : isz (buAlBB α s t ℓ) ≤ buSZ p := by
  refine isz_le_buSZ_of (p := p) (A := 3 * p + 1) (by simp only [buSZ]; omega) ?_
  rw [buAlBB, Int.natAbs_mul]
  have h1 : (buAl2 α).natAbs ≤ 2 ^ p := by
    rw [buAl2, Int.natAbs_mul, Int.natAbs_natCast]
    calc α * α = α ^ 2 := by ring
      _ ≤ p := le_of_lt hαp
      _ ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self)
  have h2 : (buBB s t ℓ).natAbs ≤ 2 ^ (2 * p) := by
    rw [buBB, Int.natAbs_mul]
    have h := natAbs_buBeta_le s t hs ℓ
    calc (buBeta s t ℓ).natAbs * (buBeta s t ℓ).natAbs ≤ s * s := Nat.mul_le_mul h h
      _ ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul (le_of_lt hsp) (le_of_lt hsp)
      _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf
  calc (buAl2 α).natAbs * (buBB s t ℓ).natAbs ≤ 2 ^ p * 2 ^ (2 * p) := Nat.mul_le_mul h1 h2
    _ = 2 ^ (3 * p) := by rw [← pow_add]; ring_nf
    _ ≤ 2 ^ (3 * p + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem isz_buPAlBB_le (p α s t : ℕ) (ℓ : ℤ) (hαp : α ^ 2 < p) (hs : 0 < s) (hsp : s < 2 ^ p)
    (hp : 100 ≤ p) : isz (buPAlBB p α s t ℓ) ≤ buSZ p := by
  refine isz_le_buSZ_of (p := p) (A := 9 * p + 205) (by simp only [buSZ]; omega) ?_
  rw [buPAlBB, Int.natAbs_mul]
  have h1 : (auPi p).natAbs ≤ 2 ^ (6 * p + 205) := natAbs_auPi_le p
  have h2 : (buAlBB α s t ℓ).natAbs ≤ 2 ^ (3 * p) := by
    rw [buAlBB, Int.natAbs_mul]
    have h3 : (buAl2 α).natAbs ≤ 2 ^ p := by
      rw [buAl2, Int.natAbs_mul, Int.natAbs_natCast]
      calc α * α = α ^ 2 := by ring
        _ ≤ p := le_of_lt hαp
        _ ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self)
    have h4 : (buBB s t ℓ).natAbs ≤ 2 ^ (2 * p) := by
      rw [buBB, Int.natAbs_mul]
      have h := natAbs_buBeta_le s t hs ℓ
      calc (buBeta s t ℓ).natAbs * (buBeta s t ℓ).natAbs ≤ s * s := Nat.mul_le_mul h h
        _ ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul (le_of_lt hsp) (le_of_lt hsp)
        _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf
    calc (buAl2 α).natAbs * (buBB s t ℓ).natAbs ≤ 2 ^ p * 2 ^ (2 * p) := Nat.mul_le_mul h3 h4
      _ = 2 ^ (3 * p) := by rw [← pow_add]; ring_nf
  calc (auPi p).natAbs * (buAlBB α s t ℓ).natAbs ≤ 2 ^ (6 * p + 205) * 2 ^ (3 * p) :=
        Nat.mul_le_mul h1 h2
    _ = 2 ^ (9 * p + 205) := by rw [← pow_add]; ring_nf

theorem isz_buSS_le (p s : ℕ) (hsp : s < 2 ^ p) (hp : 100 ≤ p) : isz (buSS s) ≤ buSZ p := by
  refine isz_le_buSZ_of (p := p) (A := 2 * p + 1) (by simp only [buSZ]; omega) ?_
  rw [buSS, Int.natAbs_mul, Int.natAbs_natCast]
  calc s * s ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul (le_of_lt hsp) (le_of_lt hsp)
    _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf
    _ ≤ 2 ^ (2 * p + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The value computed by the whole word fits the uniform bound. -/
theorem isz_buZb_le' (p α s t : ℕ) (ℓ : ℤ) (hαp : α ^ 2 < p) (hs : 0 < s) (hsp : s < 2 ^ p)
    (hp : 100 ≤ p) : isz (Int.tdiv (buPAlBB p α s t ℓ) (buSS s)) ≤ buSZ p := by
  rw [← buZb_eq_tdiv]
  exact isz_buZb_le p α s t ℓ (le_of_lt hαp) hs hsp hp

/-! ## Cost helpers

Each primitive step of the chain is bounded by `KS * (BT) ^ 2` with `BT = buSZ p + 8`.
-/

theorem le_sq_self {BT : ℕ} (h : 1 ≤ BT) : BT ≤ BT ^ 2 := by nlinarith

/-- A `pick` step: `K·(k+1)·(sz+1) ≤ C·BT²` when `k+1 ≤ 13`, `sz+1 ≤ 13·BT`. -/
theorem pickCost {K k sz C BT : ℕ} (hBT : 1 ≤ BT) (hk : k + 1 ≤ 13) (hsz : sz + 1 ≤ 13 * BT)
    (hC : K * 13 * 13 ≤ C) : K * (k + 1) * (sz + 1) ≤ C * BT ^ 2 := by
  have h1 : K * (k + 1) ≤ K * 13 := Nat.mul_le_mul_left K (by omega)
  calc K * (k + 1) * (sz + 1) ≤ (K * 13) * (13 * BT) := Nat.mul_le_mul h1 hsz
    _ = (K * 13 * 13) * BT := by ring
    _ ≤ C * BT := Nat.mul_le_mul_right _ hC
    _ ≤ C * BT ^ 2 := Nat.mul_le_mul_left _ (le_sq_self hBT)

/-- A `mulS`/`fdiv` step: `K·a·b ≤ C·BT²`. -/
theorem binMulCost {K a b C BT : ℕ} (hBT : 1 ≤ BT) (ha : a ≤ BT) (hb : b ≤ BT) (hC : K ≤ C) :
    K * a * b ≤ C * BT ^ 2 := by
  calc K * a * b ≤ K * BT * BT := Nat.mul_le_mul (Nat.mul_le_mul_left K ha) hb
    _ = K * BT ^ 2 := by ring
    _ ≤ C * BT ^ 2 := Nat.mul_le_mul_right _ hC

/-- An `add`/`sub` step: `K·(a+b) ≤ C·BT²`. -/
theorem binAddCost {K a b C BT : ℕ} (hBT : 1 ≤ BT) (ha : a ≤ BT) (hb : b ≤ BT) (hC : 2 * K ≤ C) :
    K * (a + b) ≤ C * BT ^ 2 := by
  calc K * (a + b) ≤ K * (BT + BT) := Nat.mul_le_mul_left K (by omega)
    _ = (2 * K) * BT := by ring
    _ ≤ C * BT := Nat.mul_le_mul_right _ hC
    _ ≤ C * BT ^ 2 := Nat.mul_le_mul_left _ (le_sq_self hBT)

/-- A `swap` step: `K·(a+b+1) ≤ C·BT²`. -/
theorem swapCost {K a b C BT : ℕ} (hBT : 1 ≤ BT) (ha : a ≤ BT) (hb : b ≤ BT) (hC : 3 * K ≤ C) :
    K * (a + b + 1) ≤ C * BT ^ 2 := by
  calc K * (a + b + 1) ≤ K * (BT + BT + BT) := Nat.mul_le_mul_left K (by omega)
    _ = (3 * K) * BT := by ring
    _ ≤ C * BT := Nat.mul_le_mul_right _ hC
    _ ≤ C * BT ^ 2 := Nat.mul_le_mul_left _ (le_sq_self hBT)

/-- A `dup`/`drop` step: `K·(a+1) ≤ C·BT²`. -/
theorem dupCost {K a C BT : ℕ} (hBT : 1 ≤ BT) (ha : a ≤ BT) (hC : 2 * K ≤ C) :
    K * (a + 1) ≤ C * BT ^ 2 := by
  calc K * (a + 1) ≤ K * (BT + BT) := Nat.mul_le_mul_left K (by omega)
    _ = (2 * K) * BT := by ring
    _ ≤ C * BT := Nat.mul_le_mul_right _ hC
    _ ≤ C * BT ^ 2 := Nat.mul_le_mul_left _ (le_sq_self hBT)

/-- Cost absorption: two words of cost `K₁(p+1)^K₁`, `K₂(p+1)^K₂` fit into one of the same form. -/
theorem costAdd {K₁ K₂ p : ℕ} (hp : 2 ≤ p + 1) :
    K₁ * (p + 1) ^ K₁ + K₂ * (p + 1) ^ K₂ ≤
      2 ^ (K₁ + K₂ + 2) * (p + 1) ^ (2 ^ (K₁ + K₂ + 2)) := by
  set B : ℕ := p + 1 with hB
  have hB1 : 1 ≤ B := by rw [hB]; omega
  set K : ℕ := 2 ^ (K₁ + K₂ + 2) with hK
  set X : ℕ := 2 ^ (K₁ + K₂ + 1) with hX
  have hXK : X ≤ K := by
    rw [hX, hK]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK1 : K₁ ≤ X := by
    rw [hX]
    exact le_trans (by omega : K₁ ≤ K₁ + K₂ + 1) (le_of_lt (Nat.lt_two_pow_self))
  have hK2 : K₂ ≤ X := by
    rw [hX]
    exact le_trans (by omega : K₂ ≤ K₁ + K₂ + 1) (le_of_lt (Nat.lt_two_pow_self))
  have h3 : K₁ * B ^ K₁ ≤ X * B ^ K :=
    Nat.mul_le_mul hK1 (Nat.pow_le_pow_right hB1 (le_trans hK1 hXK))
  have h4 : K₂ * B ^ K₂ ≤ X * B ^ K :=
    Nat.mul_le_mul hK2 (Nat.pow_le_pow_right hB1 (le_trans hK2 hXK))
  calc K₁ * B ^ K₁ + K₂ * B ^ K₂ ≤ X * B ^ K + X * B ^ K := Nat.add_le_add h3 h4
    _ = 2 * (X * B ^ K) := by ring
    _ = K * B ^ K := by
        rw [hK, hX]
        rw [show K₁ + K₂ + 2 = K₁ + K₂ + 1 + 1 from by omega, pow_succ]
        ring

end Work.Resample
