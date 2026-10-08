import Mathlib
import Submission.Work.L2F.Props.OddSubDefs
import Submission.Work.L2F.Props.oddsub.smul_one_add_smul_eq_zero

namespace Work.L2F.Props.oddsub

open Matrix

/-!
# A finite subgroup of `SL(2,F)` of odd order containing a unipotent element forces `char F` odd

Let `F` be a field and `g ∈ SL(2,F)` a *unipotent* matrix, i.e. `g - a • 1` is a nonzero
nilpotent (`UnipotentMatrix`).  If `g` has **odd** order `m`, then the characteristic of `F`
is an odd prime.

Indeed write `N = g - a • 1`, so `N * N = 0` and `N ≠ 0`, and `g = a • 1 + N`.  Expanding the
`m`-th power inside the algebra `F·1 + F·N` (a truncated polynomial ring, `N² = 0`) gives

  `g ^ m = a ^ m • 1 + (m · a ^ (m-1)) • N`.

Since `g ^ m = 1` and `1`, `N` are linearly independent (`N` is a nonzero nilpotent, hence not
a scalar), this forces `a ^ m = 1` and `m · a ^ (m-1) = 0`.  From `a ^ m = 1` we get `a ≠ 0`
and `a ^ (m-1) ≠ 0`, whence `(m : F) = 0`.  Therefore the characteristic `p = ringChar F`
divides `m`; as `m` is odd, `p ≠ 0` and `p ≠ 2`, and `p` is prime.
-/

/-- The product rule in the algebra `F·1 + F·N` when `N * N = 0`:
`(x•1 + y•N) * (u•1 + v•N) = (x·u)•1 + (x·v + y·u)•N`. -/
theorem mul_smul_one_add_sq_zero (F : Type*) [Field F]
    (N : Matrix (Fin 2) (Fin 2) F) (hN2 : N * N = 0) (x y u v : F) :
    (x • (1 : Matrix (Fin 2) (Fin 2) F) + y • N) *
        (u • (1 : Matrix (Fin 2) (Fin 2) F) + v • N)
      = (x * u) • (1 : Matrix (Fin 2) (Fin 2) F) + (x * v + y * u) • N := by
  have h11 : (x • (1 : Matrix (Fin 2) (Fin 2) F)) * (u • (1 : Matrix (Fin 2) (Fin 2) F))
      = (x * u) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.smul_mul, one_mul, smul_smul]
  have h12 : (x • (1 : Matrix (Fin 2) (Fin 2) F)) * (v • N) = (x * v) • N := by
    rw [Matrix.smul_mul, one_mul, smul_smul]
  have h21 : (y • N) * (u • (1 : Matrix (Fin 2) (Fin 2) F)) = (y * u) • N := by
    rw [Matrix.smul_mul, Matrix.mul_smul, mul_one, smul_smul]
  have h22 : (y • N) * (v • N) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hN2, smul_zero, smul_zero]
  rw [add_mul, mul_add, mul_add, h11, h12, h21, h22, add_zero, add_assoc, ← add_smul]

/-- Powers of `a • 1 + N` when `N * N = 0`:
`(a • 1 + N) ^ (m + 1) = a ^ (m + 1) • 1 + ((m + 1) · a ^ m) • N`. -/
theorem pow_succ_smul_one_add_sq_zero (F : Type*) [Field F]
    (a : F) (N : Matrix (Fin 2) (Fin 2) F) (hN2 : N * N = 0) (m : ℕ) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + N) ^ (m + 1)
      = a ^ (m + 1) • (1 : Matrix (Fin 2) (Fin 2) F) + (((m + 1 : ℕ) : F) * a ^ m) • N := by
  induction m with
  | zero => simp
  | succ k ih =>
    conv_lhs => rw [pow_succ]
    rw [ih]
    have hfac : a • (1 : Matrix (Fin 2) (Fin 2) F) + N
        = a • (1 : Matrix (Fin 2) (Fin 2) F) + (1 : F) • N := by
      rw [one_smul]
    rw [hfac]
    rw [mul_smul_one_add_sq_zero F N hN2 (a ^ (k + 1)) (((k + 1 : ℕ) : F) * a ^ k) a 1]
    have h1 : a ^ (k + 1) * a = a ^ (k + 1 + 1) := by rw [← pow_succ]
    have h2 : a ^ (k + 1) * 1 + (((k + 1 : ℕ) : F) * a ^ k) * a
        = (((k + 1 + 1 : ℕ)) : F) * a ^ (k + 1) := by
      rw [mul_one, mul_assoc, ← pow_succ]
      push_cast
      ring
    rw [h1, h2]

theorem charP_odd_of_unipotent (F : Type*) [Field F]
    (L : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) (hodd : Odd (Nat.card L))
    (hu : ∃ g ∈ L, Work.L2F.Props.UnipotentMatrix ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) :
    ∃ p : ℕ, Nat.Prime p ∧ CharP F p ∧ p ≠ 2 := by
  classical
  obtain ⟨g, hgL, hg⟩ := hu
  simp only [Work.L2F.Props.UnipotentMatrix] at hg
  obtain ⟨a, hAne, hA2⟩ := hg
  set A : Matrix (Fin 2) (Fin 2) F :=
    ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hA
  have hAne' : A - a • (1 : Matrix (Fin 2) (Fin 2) F) ≠ 0 := by rw [hA]; exact hAne
  have hA2' : (A - a • (1 : Matrix (Fin 2) (Fin 2) F)) *
      (A - a • (1 : Matrix (Fin 2) (Fin 2) F)) = 0 := by
    rw [hA]; exact hA2
  set N : Matrix (Fin 2) (Fin 2) F := A - a • (1 : Matrix (Fin 2) (Fin 2) F) with hN
  have hNne : N ≠ 0 := by rw [hN]; exact hAne'
  have hN2 : N * N = 0 := by rw [hN]; exact hA2'
  have hAeq : A = a • (1 : Matrix (Fin 2) (Fin 2) F) + N := by rw [hN]; abel
  -- `Nat.card L` is odd, hence nonzero; write it as `j + 1`.
  have hmne : Nat.card L ≠ 0 := by
    rintro h0
    rw [h0] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hmne
  rw [Nat.succ_eq_add_one] at hj
  have hoddj : Odd (j + 1) := by rw [← hj]; exact hodd
  -- `g ^ (j+1) = 1` in `SL(2,F)`, hence `A ^ (j+1) = 1`.
  have hpowLS : (g : Matrix.SpecialLinearGroup (Fin 2) F) ^ Nat.card L = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard L hgL)
  have hpow : A ^ Nat.card L = 1 := by
    have h := congrArg
      (fun x : Matrix.SpecialLinearGroup (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) hpowLS
    simpa [hA] using h
  have hpowj : A ^ (j + 1) = 1 := by rw [← hj]; exact hpow
  -- the power formula
  have hbin : A ^ (j + 1) = a ^ (j + 1) • (1 : Matrix (Fin 2) (Fin 2) F)
      + (((j + 1 : ℕ) : F) * a ^ j) • N := by
    rw [hAeq, pow_succ_smul_one_add_sq_zero F a N hN2 j]
  have hrel : a ^ (j + 1) • (1 : Matrix (Fin 2) (Fin 2) F)
      + (((j + 1 : ℕ) : F) * a ^ j) • N = 1 := by
    rw [← hbin, hpowj]
  -- `N` is not a scalar matrix
  have hNscalar : ∀ c : F, N ≠ c • (1 : Matrix (Fin 2) (Fin 2) F) := by
    intro c hc
    have h0 : (c • (1 : Matrix (Fin 2) (Fin 2) F)) * (c • (1 : Matrix (Fin 2) (Fin 2) F)) = 0 := by
      rw [← hc]; exact hN2
    have h0' : (c * c) • (1 : Matrix (Fin 2) (Fin 2) F) = 0 := by
      simpa [Matrix.smul_mul, one_mul, smul_smul] using h0
    have hcc : c * c = 0 := by
      have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) h0'
      simpa [Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply, smul_eq_mul] using h
    have hc0 : c = 0 := by
      by_contra hc'
      exact mul_ne_zero hc' hc' hcc
    rw [hc0, zero_smul] at hc
    exact hNne hc
  -- linear independence gives `a ^ (j+1) = 1` and `((j+1 : ℕ) : F) * a ^ j = 0`
  have hrel0 : (a ^ (j + 1) - 1) • (1 : Matrix (Fin 2) (Fin 2) F)
      + (((j + 1 : ℕ) : F) * a ^ j) • N = 0 := by
    rw [sub_smul, one_smul]
    rw [show a ^ (j + 1) • (1 : Matrix (Fin 2) (Fin 2) F) - 1
          + (((j + 1 : ℕ) : F) * a ^ j) • N
        = (a ^ (j + 1) • (1 : Matrix (Fin 2) (Fin 2) F)
          + (((j + 1 : ℕ) : F) * a ^ j) • N) - 1 from by abel]
    rw [hrel, sub_self]
  obtain ⟨haeval, hcoeff⟩ :=
    smul_one_add_smul_eq_zero F N hNscalar (a ^ (j + 1) - 1) (((j + 1 : ℕ) : F) * a ^ j) hrel0
  have ham : a ^ (j + 1) = 1 := sub_eq_zero.mp haeval
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : j + 1 ≠ 0)] at ham
    exact zero_ne_one ham
  have haj : a ^ j ≠ 0 := by
    intro h0
    rw [pow_succ, h0, zero_mul] at ham
    exact zero_ne_one ham
  have hcast : (((j + 1 : ℕ)) : F) = 0 := (mul_eq_zero.mp hcoeff).resolve_right haj
  -- characteristic theory
  have hp_dvd : ringChar F ∣ (j + 1) := (ringChar.spec F (j + 1)).mp hcast
  have hoddp : Odd (ringChar F) := Odd.of_dvd_nat hoddj hp_dvd
  have hpne : ringChar F ≠ 0 := by
    rintro h0
    rw [h0] at hoddp
    obtain ⟨k, hk⟩ := hoddp
    omega
  haveI : CharP F (ringChar F) := ringChar.charP F
  refine ⟨ringChar F, CharP.char_prime_of_ne_zero F hpne, ringChar.charP F, ?_⟩
  rintro h0
  rw [h0] at hoddp
  obtain ⟨k, hk⟩ := hoddp
  omega

end Work.L2F.Props.oddsub
