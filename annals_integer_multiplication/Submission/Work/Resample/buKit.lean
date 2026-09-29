import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.buDefs
import Submission.Work.Resample.sliceB1defs
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auKit
import Submission.Work.Resample.auPrepDefs
import Submission.Work.Resample.auPiWord

/-!
# Shared data and estimates for the uniform `B̃` preparation word (`Work.Resample.buPrep`)

This module fixes the *values* produced by the table word `prep` of the one-dimensional `B̃`
resampling (paper §4, Lemmas 4.8–4.12) and the size estimates its construction needs.  Nothing
here is a program; the individual words are proved in sibling modules and assembled in
`Work.Resample.buPrep`.

## The canonical block

Every sub-word of `prep` receives the same seven-value block

`buCB p α s t = [p, α, s, t, m, n, π]`

(with `m = egM p α`, `n = egN p α s t` and `π = auPi p` the fixed-point value of `π` at precision
`auPrec p = 3p+100`) on top of the value stack and pushes its result on top of it.  The five
results

`buL11` (the alternating signs), `buL10` (the `2m` weight columns), `buL9` (the `s` diagonal
weights), `buL8` (the `s` destination keys `(t i) % s`) and `buL7` (the `t` destination keys of
`P̃_t`) are then rotated below the block by a fixed rotation; the stack is then exactly
`buTabList p α s t`, the static table of `Work.Resample.sliceBu` (`buTabList_eq`).

## Sizes

`buSZ p` is a uniform bound on `isz` of *every* integer value occurring anywhere in `prep`
(the intermediate values of the Horner recursion `auH` have `O(p²)` bits), and `buHQ p` bounds
the Horner iterates.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Work.Resample

open HvdH

/-! ## The canonical block and the five entries -/

/-- The seven-value canonical block `[p, α, s, t, m, n, π]` on which every sub-word of `prep`
works. -/
def buCB (p α s t : ℕ) : List Val :=
  [.int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int ((egM p α : ℕ) : ℤ),
   .int ((egN p α s t : ℕ) : ℤ), .int (auPi p)]

/-- The `t` destination keys of `P̃_t⁻¹` (`egLam s t i` for `i < t`). -/
noncomputable def buL7 (p α s t : ℕ) : Val :=
  zl (List.ofFn (fun i : Fin t => (egLam s t (i : ℕ) : ℤ)))

/-- The `s` destination keys `(t i) % s` of the final `P̃_sᵀ` step. -/
def buL8 (p α s t : ℕ) : Val := zl (List.ofFn (fun i : Fin s => (egKeyS s t (i : ℕ) : ℤ)))

/-- The `s` diagonal weights `buWd`. -/
noncomputable def buL9 (p α s t : ℕ) : Val :=
  zl (List.ofFn (fun i : Fin s => buWd p α s t (i : ℤ)))

/-- The `2m` columns of tabulated Gaussian weights, each labelled by its shift `h`. -/
noncomputable def buL10 (p α s t : ℕ) : Val :=
  ofList ((egHs (egM p α)).map (fun h => Val.cons (.int h) (buCol p α s t h)))

/-- The alternating signs `(-1)^{j+1}` of the Neumann sum (there are `n-1` of them). -/
noncomputable def buL11 (p α s t : ℕ) : Val :=
  zl ((List.range (egN p α s t - 1)).map (fun j => (-1 : ℤ) ^ (j + 1)))

/-- The table of `sliceBu` in terms of the entries above. -/
private theorem buTabList_eq (p α s t : ℕ) (hs : 0 < s) (hcop : Nat.Coprime t s) :
    buTabList p α s t hs hcop =
      [.int (p : ℤ), .int (α : ℤ), .int (s : ℤ), .int (t : ℤ), .int ((egM p α : ℕ) : ℤ),
       .int ((egN p α s t : ℕ) : ℤ), buL7 p α s t, buL8 p α s t, buL9 p α s t, buL10 p α s t,
       buL11 p α s t] := by
  rfl

/-! ## Sizes -/

/-- Uniform bound on `isz` of every integer value occurring in `prep`. -/
def buSZ (p : ℕ) : ℕ := 80 * (p * p) + 6000 * p + 100000

/-- Bound on `isz` of the iterates `auH p Z j` of the Horner recursion. -/
def buHQ (p : ℕ) : ℕ := 50 * (p * p) + 3000 * p + 50000

theorem buSZ_ge (p : ℕ) : 2 ≤ buSZ p := by simp only [buSZ]; omega

theorem buSZ_three (p : ℕ) : 3 ≤ buSZ p := by simp only [buSZ]; omega

theorem buSZ_lt_self (p : ℕ) : buSZ p - 3 < buSZ p - 2 := by have h := buSZ_three p; omega

theorem isz_le_buSZ {p : ℕ} {z : ℤ} (h : z.natAbs < 2 ^ (buSZ p - 2)) : isz z ≤ buSZ p := by
  have h1 : z.natAbs.size ≤ buSZ p - 2 := Nat.size_le.mpr h
  have h2 := buSZ_ge p
  simp only [isz]
  omega

/-- A value of at most `A` bits has `isz ≤ buSZ p`, as long as `A + 3 ≤ buSZ p`. -/
theorem isz_le_buSZ_of {p A : ℕ} {z : ℤ} (hA : A + 3 ≤ buSZ p) (h : z.natAbs ≤ 2 ^ A) :
    isz z ≤ buSZ p := by
  apply isz_le_buSZ
  calc z.natAbs ≤ 2 ^ A := h
    _ ≤ 2 ^ (buSZ p - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ < 2 ^ (buSZ p - 2) := Nat.pow_lt_pow_right one_lt_two (by
        have := buSZ_three p; omega)

theorem isz_natCast_le_buSZ {p n : ℕ} (h : n < 2 ^ (buSZ p - 2)) : isz ((n : ℕ) : ℤ) ≤ buSZ p := by
  apply isz_le_buSZ
  rwa [Int.natAbs_natCast]

/-- A natural of at most `A` bits has `isz ≤ buSZ p`. -/
theorem isz_natCast_le_buSZ_of {p A n : ℕ} (hA : A + 3 ≤ buSZ p) (h : n ≤ 2 ^ A) :
    isz ((n : ℕ) : ℤ) ≤ buSZ p := by
  apply isz_le_buSZ_of hA
  rwa [Int.natAbs_natCast]

/-- Small constants. -/
theorem isz_const_le_buSZ (p m : ℕ) (h : m ≤ 100) : isz ((m : ℤ)) ≤ buSZ p := by
  refine isz_natCast_le_buSZ_of (p := p) (A := 7) ?_ ?_
  · simp only [buSZ]; omega
  · calc m ≤ 100 := h
      _ ≤ 2 ^ 7 := by norm_num

theorem isz_auPi_le_buSZ (p : ℕ) : isz (auPi p) ≤ buSZ p :=
  isz_le_buSZ_of (p := p) (A := 6 * p + 205) (by simp only [buSZ]; omega) (natAbs_auPi_le p)

theorem egM_le (p α : ℕ) : egM p α ≤ p + 1 := by
  have h := Nat.sqrt_le_self p
  have h2 := Nat.div_le_self (Nat.sqrt p) (2 * α)
  simp only [egM]
  omega

theorem isz_egM_le (p α : ℕ) : isz ((egM p α : ℕ) : ℤ) ≤ buSZ p := by
  refine isz_natCast_le_buSZ_of (p := p) (A := p) ?_ ?_
  · simp only [buSZ]; omega
  · have h1 := egM_le p α
    have h2 : p + 1 ≤ 2 ^ p := by
      have := Nat.lt_two_pow_self (n := p)
      omega
    omega

theorem isz_egN_le (p α s t : ℕ) (hs : 0 < s) (hsp : s < 2 ^ p) (hp : 1 ≤ p) :
    isz ((egN p α s t : ℕ) : ℤ) ≤ buSZ p := by
  refine isz_natCast_le_buSZ_of (p := p) (A := 2 * p) ?_ ?_
  · simp only [buSZ]; omega
  · have h1 : egN p α s t ≤ p * s := by
      have h := Nat.div_le_self (p * s - 1) (α ^ 2 * (t - s))
      have h3 : 1 ≤ p * s := Nat.mul_pos hp hs
      show (p * s - 1) / (α ^ 2 * (t - s)) + 1 ≤ p * s
      omega
    have hp1 : p ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self)
    have h3 : p * s ≤ p * 2 ^ p := Nat.mul_le_mul_left _ (le_of_lt hsp)
    have h4 : p * 2 ^ p ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul_right _ hp1
    have h5 : 2 ^ p * 2 ^ p = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf
    exact le_trans h1 (le_trans h3 (le_trans h4 (le_of_eq h5)))

/-! ## The rounded quotient `[u/v]` -/

/-- `[u/v] = ⌊u/v + 1/2⌋ = ⌊(2u+v)/(2v)⌋` for `v > 0`. -/
theorem rnd_eq_fdiv (u : ℤ) (v : ℕ) (hv : 0 < v) :
    HvdH.rnd ((u : ℝ) / (v : ℝ)) = Int.fdiv (2 * u + (v : ℤ)) (2 * (v : ℤ)) := by
  have h2 : (u : ℝ) / (v : ℝ) + 1 / 2 = ((2 * u + (v : ℤ) : ℤ) : ℝ) / ((2 * v : ℕ) : ℝ) := by
    push_cast; field_simp
  have h3 : HvdH.rnd ((u:ℝ)/(v:ℝ)) = ⌊((2 * u + (v : ℤ) : ℤ) : ℝ) / ((2 * v : ℕ) : ℝ)⌋ := by
    unfold HvdH.rnd; rw [h2]
  rw [h3, Int.floor_div_natCast, Int.floor_intCast]
  rw [Int.fdiv_eq_ediv_of_nonneg (2 * u + (v : ℤ)) (show (0:ℤ) ≤ 2 * (v:ℤ) by positivity)]
  push_cast
  rfl

/-- The computable form of `buBeta`. -/
theorem buBeta_eq (s t : ℕ) (hs : 0 < s) (n : ℤ) :
    buBeta s t n = (t : ℤ) * n - Int.fdiv (2 * ((t : ℤ) * n) + (s : ℤ)) (2 * (s : ℤ)) * (s : ℤ) := by
  unfold buBeta
  have h : (t : ℝ) * (n : ℝ) / (s : ℝ) = (((t : ℤ) * n : ℤ) : ℝ) / ((s : ℕ) : ℝ) := by
    push_cast; ring
  rw [h, rnd_eq_fdiv _ _ hs]

/-- `|x| ≤ s` (with `0 ≤ s`) transfers to `x.natAbs ≤ s.natAbs`. -/
theorem natAbs_le_of (x s : ℤ) (hs : 0 ≤ s) (h1 : -s ≤ x) (h2 : x ≤ s) : x.natAbs ≤ s.natAbs := by
  have h3 : |x| ≤ |s| := by
    rw [abs_of_nonneg hs]
    exact abs_le.mpr ⟨h1, h2⟩
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at h3
  exact_mod_cast h3

/-- `|β_n| ≤ s`. -/
theorem natAbs_buBeta_le (s t : ℕ) (hs : 0 < s) (n : ℤ) : (buBeta s t n).natAbs ≤ s := by
  have hb := buBeta_eq s t hs n
  rw [hb]
  set u : ℤ := (t : ℤ) * n with hu
  set r : ℤ := Int.fdiv (2 * u + (s : ℤ)) (2 * (s : ℤ)) with hr
  have hrf : r = HvdH.rnd ((u:ℝ)/(s:ℝ)) := by
    rw [hr, ← rnd_eq_fdiv u s hs]
  have hfl : (r : ℝ) ≤ (u : ℝ) / (s : ℝ) + 1 / 2 := by
    rw [hrf]; exact Int.floor_le _
  have hfr : (u : ℝ) / (s : ℝ) + 1 / 2 < (r : ℝ) + 1 := by
    rw [hrf]; exact Int.lt_floor_add_one _
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have h2 : |(u : ℝ) / (s : ℝ) - (r : ℝ)| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  have hg : |(u : ℝ) - (r : ℝ) * (s : ℝ)| ≤ (s : ℝ) := by
    have h1 : (u : ℝ) - (r : ℝ) * (s : ℝ) = (s : ℝ) * ((u : ℝ) / (s : ℝ) - (r : ℝ)) := by
      field_simp
    rw [h1, abs_mul, abs_of_pos hsR]
    nlinarith
  have hcast : ((u - r * (s : ℤ) : ℤ) : ℝ) = (u : ℝ) - (r : ℝ) * (s : ℝ) := by push_cast; ring
  apply natAbs_le_of _ (s : ℤ) (by positivity)
  · have : (-(s : ℤ) : ℝ) ≤ ((u - r * (s : ℤ) : ℤ) : ℝ) := by
      rw [hcast]; exact (abs_le.mp hg).1
    exact_mod_cast this
  · have : (((u - r * (s : ℤ) : ℤ)) : ℝ) ≤ (s : ℤ) := by
      rw [hcast]; exact (abs_le.mp hg).2
    exact_mod_cast this

/-- `β` fits the uniform size bound. -/
theorem isz_buBeta_le (p s t : ℕ) (hs : 0 < s) (hsp : s < 2 ^ p) (hp : 100 ≤ p) (n : ℤ) :
    isz (buBeta s t n) ≤ buSZ p := by
  refine isz_le_buSZ_of (p := p) (A := p) ?_ ?_
  · simp only [buSZ]; omega
  · exact le_trans (natAbs_buBeta_le s t hs n) (le_of_lt hsp)

/-! ## The Horner iterates `auH p Z j` -/

/-- The Horner recursion grows at most by the factor `2^(8p+111)` per step, when the initial
argument has at most `11p+210` bits. -/
theorem natAbs_auH_le (p : ℕ) (Z : ℤ) (j : ℕ) (hZ : Z.natAbs ≤ 2 ^ (11 * p + 210)) :
    (auH p Z j).natAbs ≤ 2 ^ (auPrec p + j * (8 * p + 111)) := by
  have h2P : (((2 : ℤ) ^ auPrec p).natAbs) = 2 ^ auPrec p := by
    rw [Int.natAbs_pow]; norm_num
  induction j with
  | zero =>
    show ((2 : ℤ) ^ auPrec p).natAbs ≤ _
    rw [h2P]
    exact Nat.pow_le_pow_right (by norm_num) (by simp)
  | succ j ih =>
    have hstep : (auH p Z (j + 1)).natAbs
        ≤ 2 ^ auPrec p + (Z.natAbs * (auH p Z j).natAbs) / 2 ^ auPrec p := by
      show ((2:ℤ)^auPrec p + Int.tdiv (Int.tdiv (Z * auH p Z j) ((2:ℤ)^auPrec p))
        ((auNstep p : ℤ) - (j:ℤ))).natAbs ≤ _
      refine le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_left ?_ _)
      rw [Int.natAbs_tdiv]
      refine le_trans (Nat.div_le_self _ _) ?_
      rw [Int.natAbs_tdiv, h2P, Int.natAbs_mul]
      exact le_rfl
    have h3 : (Z.natAbs * (auH p Z j).natAbs) / 2 ^ auPrec p
        ≤ 2 ^ (11 * p + 210 + j * (8 * p + 111)) := by
      have hmul : Z.natAbs * (auH p Z j).natAbs
          ≤ 2 ^ (11 * p + 210) * 2 ^ (auPrec p + j * (8 * p + 111)) :=
        Nat.mul_le_mul hZ ih
      refine le_trans (Nat.div_le_div_right hmul) ?_
      rw [← pow_add]
      rw [Nat.pow_div (by
        have h1 : auPrec p ≤ auPrec p + j * (8 * p + 111) := Nat.le_add_right _ _
        exact le_trans h1 (Nat.le_add_left _ _)) (by norm_num)]
      apply Nat.pow_le_pow_right (by norm_num)
      simp only [auPrec]; omega
    have h4 : 2 ^ auPrec p + 2 ^ (11 * p + 210 + j * (8 * p + 111))
        ≤ 2 ^ (auPrec p + (j + 1) * (8 * p + 111)) := by
      have hle : auPrec p ≤ 11 * p + 210 + j * (8 * p + 111) := by
        simp only [auPrec]; omega
      have h5 : 2 ^ auPrec p ≤ 2 ^ (11 * p + 210 + j * (8 * p + 111)) :=
        Nat.pow_le_pow_right (by norm_num) hle
      have hexp : 11 * p + 210 + j * (8 * p + 111) + 1
          = auPrec p + (j + 1) * (8 * p + 111) := by
        simp only [auPrec]; ring
      calc 2 ^ auPrec p + 2 ^ (11 * p + 210 + j * (8 * p + 111))
          ≤ 2 ^ (11 * p + 210 + j * (8 * p + 111))
              + 2 ^ (11 * p + 210 + j * (8 * p + 111)) := Nat.add_le_add_right h5 _
        _ = 2 ^ (11 * p + 210 + j * (8 * p + 111)) * 2 := by ring
        _ = 2 ^ (11 * p + 210 + j * (8 * p + 111) + 1) := (pow_succ _ _).symm
        _ = 2 ^ (auPrec p + (j + 1) * (8 * p + 111)) := by rw [hexp]
    exact le_trans (le_trans hstep (Nat.add_le_add_left h3 _)) h4

/-- The Horner iterates fit the uniform size bound. -/
theorem natAbs_auH_le_buHQ (p : ℕ) (Z : ℤ) (j : ℕ) (hp : 100 ≤ p)
    (hZ : Z.natAbs ≤ 2 ^ (11 * p + 210)) (hj : j ≤ auNstep p) :
    (auH p Z j).natAbs ≤ 2 ^ (buHQ p - 1) := by
  have hexp : auPrec p + j * (8 * p + 111) ≤ buHQ p - 1 := by
    have h1 : j * (8 * p + 111) ≤ auNstep p * (8 * p + 111) := Nat.mul_le_mul_right _ hj
    have h2 : auNstep p = 6 * p + 200 := by simp only [auNstep, auPrec]; ring
    rw [h2] at h1
    have h3 : (6 * p + 200) * (8 * p + 111) = 48 * (p * p) + 2266 * p + 22200 := by ring
    rw [h3] at h1
    simp only [auPrec, buHQ]
    omega
  calc (auH p Z j).natAbs ≤ 2 ^ (auPrec p + j * (8 * p + 111)) := natAbs_auH_le p Z j hZ
    _ ≤ 2 ^ (buHQ p - 1) := Nat.pow_le_pow_right (by norm_num) hexp

theorem isz_auH_le_buSZ (p : ℕ) (Z : ℤ) (j : ℕ) (hp : 100 ≤ p)
    (hZ : Z.natAbs ≤ 2 ^ (11 * p + 210)) (hj : j ≤ auNstep p) :
    isz (auH p Z j) ≤ buSZ p := by
  refine isz_le_buSZ_of (p := p) (A := buHQ p - 1) ?_ ?_
  · simp only [buSZ, buHQ]; omega
  · exact natAbs_auH_le_buHQ p Z j hp hZ hj

/-! ## Sizes of the remaining parameters and weights -/

/-- `|t·h + β_ℓ| ≤ 2^(2p+1)`, hence `|buN| ≤ 2^(4p+3)`. -/
theorem natAbs_buN_le (p α s t : ℕ) (ℓ h : ℤ) (hs : 0 < s) (hM : egM p α ≤ p + 1)
    (hh : h.natAbs ≤ egM p α) (hsp : s < 2 ^ p) (htp : t < 2 ^ p) (hp : 1 ≤ p) :
    (buN s t ℓ h).natAbs ≤ 2 ^ (4 * p + 3) := by
  have hs2 : (0:ℤ) ≤ (s:ℤ) := by positivity
  have hβ1 : (buBeta s t ℓ).natAbs ≤ s := natAbs_buBeta_le s t hs ℓ
  have hβ2 : (buBeta s t (ℓ + h)).natAbs ≤ s := natAbs_buBeta_le s t hs (ℓ + h)
  have hth : ((t:ℤ) * h).natAbs ≤ 2 ^ (2 * p) := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    have h1 : t * h.natAbs ≤ t * egM p α := Nat.mul_le_mul_left _ hh
    have h2 : t * egM p α ≤ t * (p + 1) := Nat.mul_le_mul_left _ hM
    have h3 : t * (p + 1) ≤ 2 ^ p * 2 ^ p := by
      have hp1 : p + 1 ≤ 2 ^ p := by
        have := Nat.lt_two_pow_self (n := p)
        omega
      calc t * (p + 1) ≤ (2 ^ p - 1) * 2 ^ p := by
            apply Nat.mul_le_mul (by omega : t ≤ 2 ^ p - 1) hp1
        _ ≤ 2 ^ p * 2 ^ p := by
            apply Nat.mul_le_mul_right
            omega
    calc t * h.natAbs ≤ t * egM p α := h1
      _ ≤ t * (p + 1) := h2
      _ ≤ 2 ^ p * 2 ^ p := h3
      _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf
  have h1 : ((t:ℤ) * h + buBeta s t ℓ).natAbs ≤ 2 ^ (2 * p) + s := by
    refine le_trans (Int.natAbs_add_le _ _) ?_
    exact Nat.add_le_add hth hβ1
  have h2 : ((t:ℤ) * h + buBeta s t ℓ).natAbs ≤ 2 ^ (2 * p + 1) := by
    refine le_trans h1 ?_
    have h3 : s ≤ 2 ^ p := le_of_lt hsp
    calc 2 ^ (2 * p) + s ≤ 2 ^ (2 * p) + 2 ^ p := Nat.add_le_add_left h3 _
      _ ≤ 2 ^ (2 * p) + 2 ^ (2 * p) := Nat.add_le_add_left (Nat.pow_le_pow_right (by norm_num) (by omega)) _
      _ = 2 ^ (2 * p + 1) := by rw [pow_succ]; ring
  have h3 : (((t:ℤ) * h + buBeta s t ℓ) ^ 2).natAbs ≤ 2 ^ (4 * p + 2) := by
    rw [Int.natAbs_pow]
    calc ((t:ℤ) * h + buBeta s t ℓ).natAbs ^ 2 ≤ (2 ^ (2 * p + 1)) ^ 2 :=
          Nat.pow_le_pow_left h2 2
      _ = 2 ^ (4 * p + 2) := by rw [← pow_mul]; ring_nf
  have h4 : ((buBeta s t (ℓ + h)) ^ 2).natAbs ≤ 2 ^ (2 * p) := by
    rw [Int.natAbs_pow]
    refine le_trans (Nat.pow_le_pow_left hβ2 2) ?_
    calc s ^ 2 ≤ (2 ^ p) ^ 2 := Nat.pow_le_pow_left (le_of_lt hsp) 2
      _ = 2 ^ (2 * p) := by rw [← pow_mul]; ring_nf
  refine le_trans (Int.natAbs_sub_le _ _) ?_
  calc (((t:ℤ) * h + buBeta s t ℓ) ^ 2).natAbs + ((buBeta s t (ℓ + h)) ^ 2).natAbs
      ≤ 2 ^ (4 * p + 2) + 2 ^ (2 * p) := Nat.add_le_add h3 h4
    _ ≤ 2 ^ (4 * p + 2) + 2 ^ (4 * p + 2) := Nat.add_le_add_left (Nat.pow_le_pow_right (by norm_num) (by omega)) _
    _ = 2 ^ (4 * p + 3) := by rw [pow_succ]; ring

theorem isz_buN_le (p α s t : ℕ) (ℓ h : ℤ) (hs : 0 < s) (hh : h.natAbs ≤ egM p α)
    (hsp : s < 2 ^ p) (htp : t < 2 ^ p) (hp : 100 ≤ p) :
    isz (buN s t ℓ h) ≤ buSZ p :=
  isz_le_buSZ_of (p := p) (A := 4 * p + 3) (by simp only [buSZ]; omega)
    (natAbs_buN_le p α s t ℓ h hs (egM_le p α) hh hsp htp (by omega))

/-- `|buZ| ≤ 2^(11p+210)`. -/
theorem natAbs_buZ_le (p α s t : ℕ) (ℓ h : ℤ) (hαp : α ^ 2 ≤ p) (hα : α ≤ 2 ^ p)
    (hs : 0 < s) (hh : h.natAbs ≤ egM p α) (hsp : s < 2 ^ p) (htp : t < 2 ^ p) (hp : 100 ≤ p) :
    (buZ p α s t ℓ h).natAbs ≤ 2 ^ (11 * p + 210) := by
  have hN := natAbs_buN_le p α s t ℓ h hs (egM_le p α) hh hsp htp (by omega)
  have hpi : (auPi p).natAbs ≤ 2 ^ (6 * p + 205) := natAbs_auPi_le p
  have hα2 : ((α : ℤ) ^ 2).natAbs ≤ 2 ^ p := by
    rw [Int.natAbs_pow]
    calc ((α : ℤ)).natAbs ^ 2 = α ^ 2 := by rw [Int.natAbs_natCast]
      _ ≤ p := hαp
      _ ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self)
  have hprod : (auPi p * ((α : ℤ) ^ 2 * buN s t ℓ h)).natAbs ≤ 2 ^ (11 * p + 208) := by
    rw [Int.natAbs_mul, Int.natAbs_mul]
    calc (auPi p).natAbs * (((α : ℤ) ^ 2).natAbs * (buN s t ℓ h).natAbs)
        ≤ 2 ^ (6 * p + 205) * (2 ^ p * 2 ^ (4 * p + 3)) := by
          refine Nat.mul_le_mul hpi (Nat.mul_le_mul hα2 hN)
      _ = 2 ^ (11 * p + 208) := by rw [← pow_add, ← pow_add]; ring_nf
  rw [buZ, Int.natAbs_tdiv]
  exact le_trans (Nat.div_le_self _ _) (le_trans hprod (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem isz_buZ_le (p α s t : ℕ) (ℓ h : ℤ) (hαp : α ^ 2 ≤ p) (hα : α ≤ 2 ^ p)
    (hs : 0 < s) (hh : h.natAbs ≤ egM p α) (hsp : s < 2 ^ p) (htp : t < 2 ^ p) (hp : 100 ≤ p) :
    isz (buZ p α s t ℓ h) ≤ buSZ p :=
  isz_le_buSZ_of (p := p) (A := 11 * p + 210) (by simp only [buSZ]; omega)
    (natAbs_buZ_le p α s t ℓ h hαp hα hs hh hsp htp hp)

/-- `|buZb| ≤ 2^(7p+205)`. -/
theorem natAbs_buZb_le (p α s t : ℕ) (ℓ : ℤ) (hαp : α ^ 2 ≤ p) (hs : 0 < s) (hsp : s < 2 ^ p)
    (hp : 100 ≤ p) : (buZb p α s t ℓ).natAbs ≤ 2 ^ (7 * p + 205) := by
  have hβ := natAbs_buBeta_le s t hs ℓ
  have hpi : (auPi p).natAbs ≤ 2 ^ (6 * p + 205) := natAbs_auPi_le p
  have hα2 : ((α : ℤ) ^ 2).natAbs ≤ 2 ^ p := by
    rw [Int.natAbs_pow]
    calc ((α : ℤ)).natAbs ^ 2 = α ^ 2 := by rw [Int.natAbs_natCast]
      _ ≤ p := hαp
      _ ≤ 2 ^ p := le_of_lt (Nat.lt_two_pow_self)
  have hβ2 : ((buBeta s t ℓ) ^ 2).natAbs ≤ s ^ 2 := by
    rw [Int.natAbs_pow]
    exact Nat.pow_le_pow_left hβ 2
  have hprod : (auPi p * ((α : ℤ) ^ 2 * (buBeta s t ℓ) ^ 2)).natAbs ≤ 2 ^ (7 * p + 205) * s ^ 2 := by
    rw [Int.natAbs_mul, Int.natAbs_mul]
    calc (auPi p).natAbs * (((α : ℤ) ^ 2).natAbs * ((buBeta s t ℓ) ^ 2).natAbs)
        ≤ 2 ^ (6 * p + 205) * (2 ^ p * s ^ 2) :=
          Nat.mul_le_mul hpi (Nat.mul_le_mul hα2 hβ2)
      _ = 2 ^ (7 * p + 205) * s ^ 2 := by
          have he : 6 * p + 205 + p = 7 * p + 205 := by ring
          rw [← mul_assoc, ← pow_add, he]
  rw [buZb, Int.natAbs_tdiv, Int.natAbs_pow, Int.natAbs_natCast]
  refine Nat.div_le_of_le_mul ?_
  rw [Nat.mul_comm]
  exact hprod

theorem isz_buZb_le (p α s t : ℕ) (ℓ : ℤ) (hαp : α ^ 2 ≤ p) (hs : 0 < s) (hsp : s < 2 ^ p)
    (hp : 100 ≤ p) : isz (buZb p α s t ℓ) ≤ buSZ p :=
  isz_le_buSZ_of (p := p) (A := 7 * p + 205) (by simp only [buSZ]; omega)
    (natAbs_buZb_le p α s t ℓ hαp hs hsp hp)

/-- `buWt` fits the uniform size bound. -/
theorem natAbs_buWt_le (p α s t : ℕ) (ℓ h : ℤ) (hαp : α ^ 2 ≤ p) (hα : α ≤ 2 ^ p)
    (hs : 0 < s) (hh : h.natAbs ≤ egM p α) (hsp : s < 2 ^ p) (htp : t < 2 ^ p) (hp : 100 ≤ p) :
    (buWt p α s t ℓ h).natAbs ≤ 2 ^ (buHQ p - 1) := by
  have hZ := natAbs_buZ_le p α s t ℓ h hαp hα hs hh hsp htp hp
  unfold buWt
  split
  · rw [Int.natAbs_tdiv]
    refine le_trans (Nat.div_le_self _ _) ?_
    exact natAbs_auH_le_buHQ p (-(buZ p α s t ℓ h)) (auNstep p) hp (by simpa using hZ) le_rfl
  · simp

theorem isz_buWt_le (p α s t : ℕ) (ℓ h : ℤ) (hαp : α ^ 2 ≤ p) (hα : α ≤ 2 ^ p)
    (hs : 0 < s) (hh : h.natAbs ≤ egM p α) (hsp : s < 2 ^ p) (htp : t < 2 ^ p) (hp : 100 ≤ p) :
    isz (buWt p α s t ℓ h) ≤ buSZ p := by
  refine isz_le_buSZ_of (p := p) (A := buHQ p - 1) ?_ ?_
  · simp only [buSZ, buHQ]; omega
  · exact natAbs_buWt_le p α s t ℓ h hαp hα hs hh hsp htp hp

/-- `2^auPrec p` fits the uniform size bound. -/
theorem isz_auEn_le_buSZ (p : ℕ) : isz (auEn p) ≤ buSZ p := by
  refine isz_le_buSZ_of (p := p) (A := auPrec p) ?_ ?_
  · simp only [buSZ, auPrec]; omega
  · rw [auEn, Int.natAbs_pow]
    have h2 : ((2:ℤ)).natAbs = 2 := by norm_num
    rw [h2]

/-- The guard bound `(p+10)·2^auPrec p` fits the uniform size bound. -/
theorem isz_auBnd_le_buSZ (p : ℕ) : isz (auBnd p) ≤ buSZ p := by
  exact isz_le_buSZ_of (p := p) (A := 4 * p + 104) (by simp only [buSZ]; omega)
    (natAbs_auBnd_le p)

end Work.Resample
