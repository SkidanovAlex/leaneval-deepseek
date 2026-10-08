import Mathlib
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.Models.Port.PSU3.Centralizer
import Submission.Work.PSU3.BenderST
import Submission.Work.PSU3.BenderST.psu3_std_defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.BST.psu3_stdSol` — the standard solution in `PSU(3,2ⁿ)`

The distinguished involution of the unipotent radical of `PSU(3,2ⁿ)` relative to the Weyl
element `w̄` is the image `s₀ = u(0,1) = psu3Std n` of the matrix `!![1,0,1;0,1,0;0,0,1]`.
The two elementary matrix identities behind this are, with `t = J3 = !![0,0,1;0,1,0;1,0,0]`
(`suSg`) and `s = u(0,1)`:

* `t s t = s t s` — so `(s₀, s₀)` solves the structure identity `w s w = r⁻¹ w r`
  (as `s₀² = 1`), and
* `(s t)³ = 1`, `s t ≠ 1` — so `orderOf (s₀ w̄) = 3`.

All entries are `0` and `1`, so the computations are characteristic independent and are done
entrywise with `Matrix.ext`, `fin_cases` and `Matrix.mul_fin_three`.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000

open Matrix LeanEval.GroupTheory.Defs

namespace Work.PSU3.BST

/-- `u(0,1)` as a matrix. -/
private lemma suUg_zero_one_coe (n : ℕ) :
    ((Submission.PSU3.suUg n 0 1 : GL (Fin 3) (Submission.PSU3.F n)) :
      Matrix (Fin 3) (Fin 3) (Submission.PSU3.F n)) = !![1, 0, 1; 0, 1, 0; 0, 0, 1] := by
  rw [Submission.PSU3.suUg_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Submission.PSU3.suUmat, zero_pow (show 2 ^ n ≠ 0 by positivity)]

/-- `J3` as an explicit matrix. -/
private lemma suSg_coe' (n : ℕ) :
    ((Submission.PSU3.suSg n : GL (Fin 3) (Submission.PSU3.F n)) :
      Matrix (Fin 3) (Fin 3) (Submission.PSU3.F n)) = !![0, 0, 1; 0, 1, 0; 1, 0, 0] :=
  Submission.PSU3.suSg_coe n

/-- **The structure identity at the matrix level**: `t s t = s t s`, `t = suSg`, `s = u(0,1)`. -/
private lemma suSg_conj_suUg_zero_one_mat (n : ℕ) :
    ((Submission.PSU3.suSg n : GL (Fin 3) (Submission.PSU3.F n)) :
        Matrix (Fin 3) (Fin 3) (Submission.PSU3.F n)) *
      (((Submission.PSU3.suUg n 0 1 : GL (Fin 3) (Submission.PSU3.F n))) :
        Matrix (Fin 3) (Fin 3) (Submission.PSU3.F n)) *
      ((Submission.PSU3.suSg n : GL (Fin 3) (Submission.PSU3.F n)) :
        Matrix (Fin 3) (Fin 3) (Submission.PSU3.F n)) =
    (((Submission.PSU3.suUg n 0 1 : GL (Fin 3) (Submission.PSU3.F n))) :
        Matrix (Fin 3) (Fin 3) (Submission.PSU3.F n)) *
      ((Submission.PSU3.suSg n : GL (Fin 3) (Submission.PSU3.F n)) :
        Matrix (Fin 3) (Fin 3) (Submission.PSU3.F n)) *
      (((Submission.PSU3.suUg n 0 1 : GL (Fin 3) (Submission.PSU3.F n))) :
        Matrix (Fin 3) (Fin 3) (Submission.PSU3.F n)) := by
  rw [suSg_coe', suUg_zero_one_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_three, CharTwo.add_self_eq_zero]

/-- `(s t)³ = 1` at the level of `GL(3,F)`. -/
private lemma suUg_zero_one_mul_suSg_cube (n : ℕ) :
    (Submission.PSU3.suUg n 0 1 * Submission.PSU3.suSg n) *
        (Submission.PSU3.suUg n 0 1 * Submission.PSU3.suSg n) *
        (Submission.PSU3.suUg n 0 1 * Submission.PSU3.suSg n) = 1 := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one,
    suSg_coe', suUg_zero_one_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_three, CharTwo.add_self_eq_zero]

/-- `(s t)³ = 1` in the form of a triple product of `s t`. -/
private lemma suUg_zero_one_mul_suSg_pow (n : ℕ) :
    (Submission.PSU3.suUg n 0 1 * Submission.PSU3.suSg n) *
        (Submission.PSU3.suUg n 0 1 * Submission.PSU3.suSg n) *
        (Submission.PSU3.suUg n 0 1 * Submission.PSU3.suSg n) = 1 :=
  suUg_zero_one_mul_suSg_cube n

/-- The structure identity in `↥(SU(3,2ⁿ))`. -/
private lemma suSU_conj (n : ℕ) :
    Submission.PSU3.suSgM n * Work.PSU3.BenderST.psu3StdSU n * Submission.PSU3.suSgM n =
      Work.PSU3.BenderST.psu3StdSU n * Submission.PSU3.suSgM n *
        Work.PSU3.BenderST.psu3StdSU n := by
  apply Subtype.ext
  apply Units.ext
  show ((Submission.PSU3.suSg n : GL (Fin 3) (Submission.PSU3.F n)) : Matrix (Fin 3) (Fin 3) (Submission.PSU3.F n)) * (((Submission.PSU3.suUg n 0 1 : GL (Fin 3) (Submission.PSU3.F n))) : Matrix (Fin 3) (Fin 3) (Submission.PSU3.F n)) * ((Submission.PSU3.suSg n : GL (Fin 3) (Submission.PSU3.F n)) : Matrix (Fin 3) (Fin 3) (Submission.PSU3.F n)) = (((Submission.PSU3.suUg n 0 1 : GL (Fin 3) (Submission.PSU3.F n))) : Matrix (Fin 3) (Fin 3) (Submission.PSU3.F n)) * ((Submission.PSU3.suSg n : GL (Fin 3) (Submission.PSU3.F n)) : Matrix (Fin 3) (Fin 3) (Submission.PSU3.F n)) * (((Submission.PSU3.suUg n 0 1 : GL (Fin 3) (Submission.PSU3.F n))) : Matrix (Fin 3) (Fin 3) (Submission.PSU3.F n))
  exact suSg_conj_suUg_zero_one_mat n

/-- `(u(0,1) · t)³ = 1` in `↥(SU(3,2ⁿ))`. -/
private lemma suSU_cube (n : ℕ) :
    ((Work.PSU3.BenderST.psu3StdSU n * Submission.PSU3.suSgM n) *
        (Work.PSU3.BenderST.psu3StdSU n * Submission.PSU3.suSgM n)) *
      (Work.PSU3.BenderST.psu3StdSU n * Submission.PSU3.suSgM n) = 1 := by
  apply Subtype.ext
  show ((Submission.PSU3.suUg n 0 1 * Submission.PSU3.suSg n) *
      (Submission.PSU3.suUg n 0 1 * Submission.PSU3.suSg n)) *
      (Submission.PSU3.suUg n 0 1 * Submission.PSU3.suSg n) = 1
  exact suUg_zero_one_mul_suSg_cube n

/-- `s t ≠ 1` at the level of `GL(3,F)` (the `(0,2)` entry is `1`, while that of `1` is `0`). -/
private lemma suUg_zero_one_mul_suSg_ne_one (n : ℕ) :
    Submission.PSU3.suUg n 0 1 * Submission.PSU3.suSg n ≠ 1 := by
  intro h
  have h02 := congrArg (fun g : GL (Fin 3) (Submission.PSU3.F n) =>
    (((g : GL (Fin 3) (Submission.PSU3.F n)) :
      Matrix (Fin 3) (Fin 3) (Submission.PSU3.F n)) 0 2)) h
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one,
    suSg_coe', suUg_zero_one_coe] at h02
  simp [Matrix.mul_fin_three, CharTwo.add_self_eq_zero] at h02

/-- `u(0,1)² = 1` at the level of `GL(3,F)`. -/
private lemma suUg_zero_one_sq (n : ℕ) :
    Submission.PSU3.suUg n 0 1 * Submission.PSU3.suUg n 0 1 = 1 := by
  have h := Submission.PSU3.suUg_mul_self n 0 1
  rw [show (0 : Submission.PSU3.F n) ^ (2 ^ n + 1) = 0 from
    zero_pow (show 2 ^ n + 1 ≠ 0 by positivity), Submission.PSU3.suUg_zero] at h
  exact h

/-- `gen ^ (q+1) ≠ 1`, `q = 2^n`: the generator of `Fˣ` has order `q² - 1 > q + 1`. -/
private lemma gen_pow_add_one_ne_one (n : ℕ) (hn : 2 ≤ n) :
    ((Submission.PSU3.gen n : (Submission.PSU3.F n)ˣ) : Submission.PSU3.F n) ^ (2 ^ n + 1) ≠ 1 := by
  intro h1
  have hord := Submission.PSU3.orderOf_gen n (by omega)
  have h1' : Submission.PSU3.gen n ^ (2 ^ n + 1) = 1 := by
    apply Units.ext
    simpa using h1
  have hdvd : 2 ^ (2 * n) - 1 ∣ 2 ^ n + 1 := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one h1'
  have hpos : 0 < 2 ^ n + 1 := by positivity
  have hle : 2 ^ (2 * n) - 1 ≤ 2 ^ n + 1 := Nat.le_of_dvd hpos hdvd
  have hle' : 2 ^ (2 * n) ≤ 2 ^ n + 2 := by omega
  have hsq : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [← pow_add]; ring_nf
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  nlinarith [hle', hsq, h4]

/-- `psu3Std n ≠ 1`: the class of `u(0,1)` is not a scalar, because it does not commute with
the image of the torus element `t(gen)` (`suTg_mul_suUg_zero_iff`). -/
private lemma psu3Std_ne_one (n : ℕ) (hn : 2 ≤ n) : Work.PSU3.BenderST.psu3Std n ≠ 1 := by
  intro h
  have hker : Work.PSU3.BenderST.psu3StdSU n ∈ (Submission.PSU3.psu3Hom n).ker := by
    rw [MonoidHom.mem_ker, ← Work.PSU3.BenderST.psu3Std_val]
    exact h
  have hcent : Work.PSU3.BenderST.psu3StdSU n ∈ Subgroup.center ↥(Submission.PSU3.SU3 n) :=
    Submission.PSU3.psu3Hom_ker_le_center n hker
  have hcomm := (Subgroup.mem_center_iff.mp hcent)
    (Submission.PSU3.suTgSU n (Submission.PSU3.gen n) : ↥(Submission.PSU3.SU3 n))
  have hsum : Submission.PSU3.suTg n (Submission.PSU3.gen n) *
      Submission.PSU3.suUg n 0 1 =
      Submission.PSU3.suUg n 0 1 * Submission.PSU3.suTg n (Submission.PSU3.gen n) := by
    have h2 : ((Work.PSU3.BenderST.psu3StdSU n : ↥(Submission.PSU3.SU3 n)) :
        GL (Fin 3) (Submission.PSU3.F n)) = Submission.PSU3.suUg n 0 1 := rfl
    have h3 : ((Submission.PSU3.suTgSU n (Submission.PSU3.gen n) :
        ↥(Submission.PSU3.SU3 n)) : GL (Fin 3) (Submission.PSU3.F n)) =
        Submission.PSU3.suTg n (Submission.PSU3.gen n) := rfl
    rw [← h2, ← h3]
    exact congrArg (fun z : ↥(Submission.PSU3.SU3 n) =>
      (z : GL (Fin 3) (Submission.PSU3.F n))) hcomm
  exact gen_pow_add_one_ne_one n hn
    ((Submission.PSU3.suTg_mul_suUg_zero_iff n (c := 1) (by norm_num)
      (Submission.PSU3.gen n)).mp hsum)

/-- **The standard solution in `PSU(3,2ⁿ)`**: the distinguished involution of `Ū` relative to
the Weyl element `w̄` is `s₀ = r₀ = u(0,1)`, and `orderOf (s₀ * w̄) = 3`. -/
theorem psu3_stdSol (n : ℕ) (hn : 2 ≤ n) :
    ∃ s₀ r₀ : LeanEval.GroupTheory.Defs.PSU3Model n,
      s₀ ∈ (Submission.PSU3.psu3BenderPair n hn).U ∧ orderOf s₀ = 2 ∧
      r₀ ∈ (Submission.PSU3.psu3BenderPair n hn).U ∧
      (Submission.PSU3.psu3BenderPair n hn).w * s₀ * (Submission.PSU3.psu3BenderPair n hn).w
        = r₀⁻¹ * (Submission.PSU3.psu3BenderPair n hn).w * r₀ ∧
      orderOf (s₀ * (Submission.PSU3.psu3BenderPair n hn).w) = 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set P := Submission.PSU3.psu3BenderPair n hn with hP
  have hw : (P.w : PSU3Model n) = Submission.PSU3.psu3Hom n (Submission.PSU3.suSgM n) := rfl
  have hstd : Work.PSU3.BenderST.psu3Std n =
      Submission.PSU3.psu3Hom n (Work.PSU3.BenderST.psu3StdSU n) :=
    Work.PSU3.BenderST.psu3Std_val n
  -- the structure identity `w * s * w = s * w * s`
  have hconj : P.w * Work.PSU3.BenderST.psu3Std n * P.w =
      Work.PSU3.BenderST.psu3Std n * P.w * Work.PSU3.BenderST.psu3Std n := by
    rw [hw, hstd, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    exact congrArg (Submission.PSU3.psu3Hom n) (suSU_conj n)
  -- `(s * w)³ = 1`
  have hcube : (Work.PSU3.BenderST.psu3Std n * P.w) *
      (Work.PSU3.BenderST.psu3Std n * P.w) *
      (Work.PSU3.BenderST.psu3Std n * P.w) = 1 := by
    have hA : Work.PSU3.BenderST.psu3Std n * P.w =
        Submission.PSU3.psu3Hom n
          (Work.PSU3.BenderST.psu3StdSU n * Submission.PSU3.suSgM n) := by
      rw [hstd, hw, map_mul]
    rw [hA, ← map_mul, ← map_mul, ← map_one (Submission.PSU3.psu3Hom n)]
    exact congrArg (Submission.PSU3.psu3Hom n) (suSU_cube n)
  -- `s² = 1`
  have hsq : Work.PSU3.BenderST.psu3Std n ^ 2 = 1 := by
    have h : Work.PSU3.BenderST.psu3StdSU n * Work.PSU3.BenderST.psu3StdSU n = 1 := by
      simpa [pow_two] using Work.PSU3.BenderST.psu3StdSU_sq n
    rw [pow_two, hstd, ← map_mul, h, map_one]
  have hprod_ne : Work.PSU3.BenderST.psu3Std n * P.w ≠ 1 := by
    intro h1
    refine P.hwB ?_
    have h2 : P.w = (Work.PSU3.BenderST.psu3Std n)⁻¹ := by
      calc P.w = 1 * P.w := (one_mul _).symm
        _ = ((Work.PSU3.BenderST.psu3Std n)⁻¹ * Work.PSU3.BenderST.psu3Std n) * P.w := by
              rw [inv_mul_cancel]
        _ = (Work.PSU3.BenderST.psu3Std n)⁻¹ *
              (Work.PSU3.BenderST.psu3Std n * P.w) := by rw [mul_assoc]
        _ = (Work.PSU3.BenderST.psu3Std n)⁻¹ * 1 := by rw [h1]
        _ = (Work.PSU3.BenderST.psu3Std n)⁻¹ := mul_one _
    rw [h2]
    exact P.B.inv_mem (P.U_le_B (Work.PSU3.BenderST.psu3Std_mem n))
  have hordprod : orderOf (Work.PSU3.BenderST.psu3Std n * P.w) = 3 := by
    have h3 : (Work.PSU3.BenderST.psu3Std n * P.w) ^ 3 = 1 := by
      simpa [pow_succ, pow_two, mul_assoc] using hcube
    exact orderOf_eq_prime h3 hprod_ne
  have hord₂ : orderOf (Work.PSU3.BenderST.psu3Std n) = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hsq) (psu3Std_ne_one n hn)
  refine ⟨Work.PSU3.BenderST.psu3Std n, Work.PSU3.BenderST.psu3Std n,
    Work.PSU3.BenderST.psu3Std_mem n, hord₂, Work.PSU3.BenderST.psu3Std_mem n, ?_, hordprod⟩
  have hinv : (Work.PSU3.BenderST.psu3Std n)⁻¹ = Work.PSU3.BenderST.psu3Std n :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsq)
  rw [hconj, hinv]

end Work.PSU3.BST
