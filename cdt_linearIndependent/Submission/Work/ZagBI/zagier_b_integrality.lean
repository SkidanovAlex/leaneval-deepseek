import Mathlib
import Submission.CDTPlan.InterfacesA

/-! Guidance from the project lead (the requester):

# Area ZagB-I — `[1..n]²·b_n ∈ ℤ` (up to a fixed K) via the Beukers integral (ROUTE a)
A parallel agent attacks the same statement by q-series (route b). Yours: elementary, Beukers-style.
`HB_coeff` = b_n (ZagierHBC; recurrence (n+1)²u_{n+1} = (10n²+10n+3)u_n − 9n²u_{n−1}, b₀=0, b₁=1).
DO NOT depend on lemmas proved by `native_decide` (ZagierHBC's small values are; re-prove what you
need by `decide`/`norm_num`/`rfl`) — check `#print axioms`.  ...

## Actual route found (elementary, no Beukers integral needed)

Write `U := H_B / H_A ∈ ℚ⟦x⟧` (well defined since `H_A(0) = 1`).  Since `H_A ∈ ℤ⟦x⟧`
(`HA_coeff_eq_cast`), the coefficientwise Cauchy product `H_B = H_A · U` gives, *provided*
`U` has denominator type `[1..n]²`, the bound `[1..n]²·b_n ∈ ℤ` for `H_B` as well
(`lcm(1..l) ∣ lcm(1..n)` for `l ≤ n`).

The denominator type of `U` is *elementary*: the two ODEs
`L(H_A) = 0`, `L(H_B) = 1` for `L(y) = x(1−x)(1−9x)y'' + (1−20x+27x²)y' + 3(−1+3x)y`
(the paper's `(zagr)`/`(zagrt)` in ODE form) imply, by pure power-series algebra,
`(H_A · A₃ · U')' = H_A` with `A₃ = x(1−x)(1−9x)H_A`, i.e.
`(1 − 10x + 9x²)·H_A²·U' = Σ_m (a_m/(m+1)) x^m` (`a_m = HA_coeff m = HA_coeffZ m ∈ ℤ`).
Since `(1−10x+9x²)H_A² ∈ ℤ⟦x⟧` has constant term `1`, its inverse has integer coefficients,
so `[1..m+1]·[x^m]U' ∈ ℤ` and hence `[1..n]·n·[x^n]U ∈ ℤ`; with `l | lcmUpto n` and
`lcmUpto l | lcmUpto n` for `l ≤ n` the transfer to `HB_coeff` gives `[1..n]²·b_n ∈ ℤ`.

So `ZagierBIntegrality` holds with `K = 1` — linearity, no Beukers integral, no modular forms.
-/

set_option maxHeartbeats 1000000

namespace Work.ZagBI

open Submission.CDTPlan
open PowerSeries
open scoped BigOperators

noncomputable section

/-! ## 1. The `H_A` ODE, re-proved without the `native_decide`-tainted initial values

`Submission.CDT.HA_ode` is *tainted*: its proof uses `HA_coeff_zero/one/two`, which are
proved by `native_decide` (`#print axioms` shows the `Lean.ofReduceBool` axioms).  Every
lemma of this file must be axiom-clean, so the homogeneous ODE `L(H_A) = 0` is re-proved
here from the (clean) recurrence `HA_coeff_recurrence_zero` and the clean values
`a₀ = 1, a₁ = 3, a₂ = 15`. -/

lemma HA_coeff_zero_clean : Submission.CDT.HA_coeff 0 = 1 := by
  norm_num [Submission.CDT.HA_coeff]

lemma HA_coeff_one_clean : Submission.CDT.HA_coeff 1 = 3 := by
  norm_num [Submission.CDT.HA_coeff, Finset.sum_range_succ]

lemma HA_coeff_two_clean : Submission.CDT.HA_coeff 2 = 15 := by
  norm_num [Submission.CDT.HA_coeff, Finset.sum_range_succ, Nat.choose]

lemma HA_odeLHS_coeff_clean (n : ℕ) : PowerSeries.coeff n (Submission.CDT.HA_odeLHS Submission.CDT.HA) = 0 := by
  classical
  let F : PowerSeries ℚ := Submission.CDT.HA
  let dF : PowerSeries ℚ := PowerSeries.derivative (R := ℚ) F
  let d2F : PowerSeries ℚ := PowerSeries.derivative (R := ℚ) dF
  have hU : ∀ m, PowerSeries.coeff m F = Submission.CDT.HA_coeff m := by
    intro m
    rw [show F = Submission.CDT.HA from rfl, Submission.CDT.coeff_HA]
  have hU0 : Submission.CDT.HA_coeff 0 = 1 := HA_coeff_zero_clean
  have hU1 : Submission.CDT.HA_coeff 1 = 3 := HA_coeff_one_clean
  have hU2 : Submission.CDT.HA_coeff 2 = 15 := HA_coeff_two_clean
  have hderiv : ∀ m, PowerSeries.coeff m dF = Submission.CDT.HA_coeff (m + 1) * ((m : ℚ) + 1) := by
    intro m
    rw [show dF = PowerSeries.derivative (R := ℚ) Submission.CDT.HA from rfl, PowerSeries.coeff_derivative, hU]
  have hderiv2 : ∀ m, PowerSeries.coeff m d2F = Submission.CDT.HA_coeff (m + 2) * ((m : ℚ) + 1) * ((m : ℚ) + 2) := by
    intro m
    rw [show d2F = PowerSeries.derivative (R := ℚ) dF from rfl, PowerSeries.coeff_derivative]
    rw [hderiv (m + 1)]
    ring_nf
    simp [Nat.cast_add, Nat.cast_one]
    ring
  have hsplit :
      Submission.CDT.HA_odeLHS F
      = X * d2F - C 10 * (X ^ 2 * d2F) + C 9 * (X ^ 3 * d2F)
        + dF - C 20 * (X * dF) + C 27 * (X ^ 2 * dF)
        - C 3 * F + C 9 * (X * F) := by
    rw [show F = Submission.CDT.HA from rfl]
    unfold Submission.CDT.HA_odeLHS
    ring
  rw [show Submission.CDT.HA = F from rfl]
  rw [hsplit]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul]
  have hXm : ∀ (g : PowerSeries ℚ) (m : ℕ), PowerSeries.coeff (m + 1) (X * g) = PowerSeries.coeff m g := by
    intro g m
    simpa [Nat.add_comm] using (PowerSeries.coeff_X_pow_mul g 1 m)
  have hX2m : ∀ (g : PowerSeries ℚ) (m : ℕ), PowerSeries.coeff (m + 2) (X ^ 2 * g) = PowerSeries.coeff m g := by
    intro g m
    exact PowerSeries.coeff_X_pow_mul g 2 m
  have hX3m : ∀ (g : PowerSeries ℚ) (m : ℕ), PowerSeries.coeff (m + 3) (X ^ 3 * g) = PowerSeries.coeff m g := by
    intro g m
    exact PowerSeries.coeff_X_pow_mul g 3 m
  have hzpow : ∀ (g : PowerSeries ℚ) (m : ℕ) (j : ℕ), j < m →
      PowerSeries.coeff j (X ^ m * g) = 0 := by
    intro g m j hj
    rw [PowerSeries.coeff_X_pow_mul']
    have : ¬ m ≤ j := by omega
    simp [this]
  cases n with
  | zero =>
      have hz1 : PowerSeries.coeff 0 (X * d2F) = 0 := by simp
      have hz2 := hzpow d2F 2 0 (by norm_num)
      have hz3 := hzpow d2F 3 0 (by norm_num)
      have hz4 : PowerSeries.coeff 0 (X * dF) = 0 := by simp
      have hz5 := hzpow dF 2 0 (by norm_num)
      have hz6 : PowerSeries.coeff 0 (X * F) = 0 := by simp
      rw [hz1, hz2, hz3, hz4, hz5, hz6, hderiv 0, hU 0]
      norm_num [hU0, hU1]
  | succ m =>
      cases m with
      | zero =>
          have hx1 : PowerSeries.coeff 1 (X * d2F) = PowerSeries.coeff 0 d2F := by
            simpa using (hXm d2F 0)
          have hx2 := hzpow d2F 2 1 (by norm_num)
          have hx3 := hzpow d2F 3 1 (by norm_num)
          have hx4 : PowerSeries.coeff 1 (X * dF) = PowerSeries.coeff 0 dF := by
            simpa using (hXm dF 0)
          have hx5 := hzpow dF 2 1 (by norm_num)
          have hx6 : PowerSeries.coeff 1 (X * F) = PowerSeries.coeff 0 F := by
            simpa using (hXm F 0)
          rw [hx1, hx2, hx3, hx4, hx5, hx6]
          rw [hderiv 1, hderiv 0, hderiv2 0, hU 1, hU 0]
          norm_num
          ring_nf
          have hz := Submission.CDT.HA_coeff_recurrence_zero 1 (by norm_num)
          ring_nf at hz
          linear_combination hz
      | succ k =>
          cases k with
          | zero =>
              have hx1 : PowerSeries.coeff 2 (X * d2F) = PowerSeries.coeff 1 d2F := by
                simpa using (hXm d2F 1)
              have hx2 : PowerSeries.coeff 2 (X ^ 2 * d2F) = PowerSeries.coeff 0 d2F := by
                simpa using (hX2m d2F 0)
              have hx3 := hzpow d2F 3 2 (by norm_num)
              have hx4 : PowerSeries.coeff 2 (X * dF) = PowerSeries.coeff 1 dF := by
                simpa using (hXm dF 1)
              have hx5 : PowerSeries.coeff 2 (X ^ 2 * dF) = PowerSeries.coeff 0 dF := by
                simpa using (hX2m dF 0)
              have hx6 : PowerSeries.coeff 2 (X * F) = PowerSeries.coeff 1 F := by
                simpa using (hXm F 1)
              rw [hx1, hx2, hx3, hx4, hx5, hx6]
              rw [hderiv 2, hderiv 1, hderiv 0, hderiv2 1, hderiv2 0, hU 2, hU 1]
              ring_nf
              have hz := Submission.CDT.HA_coeff_recurrence_zero 2 (by norm_num)
              ring_nf at hz
              linear_combination hz
          | succ k =>
              have hx1 : PowerSeries.coeff (k + 3) (X * d2F) = PowerSeries.coeff (k + 2) d2F := by
                simpa [Nat.add_assoc] using (hXm d2F (k + 2))
              have hx2 : PowerSeries.coeff (k + 3) (X ^ 2 * d2F) = PowerSeries.coeff (k + 1) d2F := by
                simpa [Nat.add_assoc] using (hX2m d2F (k + 1))
              have hx3 : PowerSeries.coeff (k + 3) (X ^ 3 * d2F) = PowerSeries.coeff k d2F := by
                exact hX3m d2F k
              have hx4 : PowerSeries.coeff (k + 3) (X * dF) = PowerSeries.coeff (k + 2) dF := by
                simpa [Nat.add_assoc] using (hXm dF (k + 2))
              have hx5 : PowerSeries.coeff (k + 3) (X ^ 2 * dF) = PowerSeries.coeff (k + 1) dF := by
                simpa [Nat.add_assoc] using (hX2m dF (k + 1))
              have hx6 : PowerSeries.coeff (k + 3) (X * F) = PowerSeries.coeff (k + 2) F := by
                simpa [Nat.add_assoc] using (hXm F (k + 2))
              rw [hx1, hx2, hx3, hx4, hx5, hx6]
              rw [hderiv (k + 3), hderiv (k + 2), hderiv (k + 1), hderiv2 (k + 2), hderiv2 (k + 1),
                hderiv2 k, hU (k + 3), hU (k + 2)]
              ring_nf
              have hz := Submission.CDT.HA_coeff_recurrence_zero (k + 3) (by omega)
              ring_nf at hz
              simp only [Nat.cast_add, Nat.cast_ofNat] at hz ⊢
              ring_nf at hz ⊢
              rw [show (3 + k) - 1 = 2 + k by omega] at hz
              linear_combination hz

/-- the homogeneous ODE of `H_A`, axiom-clean -/
lemma HA_ode_clean : Submission.CDT.HA_odeLHS Submission.CDT.HA = 0 := by
  apply PowerSeries.ext
  intro n
  exact HA_odeLHS_coeff_clean n


/-! ## 2. The quotient `U = H_B/H_A` and the ODE algebra -/

/-- `x(1−x)(1−9x) = x − 10x² + 9x³`, as a power series. -/
def Pode : PowerSeries ℚ := X - C 10 * X ^ 2 + C 9 * X ^ 3

/-- its derivative `1 − 20x + 27x²`. -/
def dPode : PowerSeries ℚ := (1 : PowerSeries ℚ) - C 20 * X + C 27 * X ^ 2

/-- the quotient `U = H_B/H_A` (well-defined: `H_A(0) = 1`). -/
def U : PowerSeries ℚ := Submission.CDT.HB * Submission.CDT.HA⁻¹

/-- the `y'`-coefficient of the expanded `L(y) = x(1−x)(1−9x)y'' + (1−20x+27x²)y'
+ 3(−1+3x)y` at `f = H_A`. -/
def A2s : PowerSeries ℚ := 2 * Pode * PowerSeries.derivative (R := ℚ) Submission.CDT.HA
  + dPode * Submission.CDT.HA

/-- the `y''`-coefficient of `L` at `f = H_A`, i.e. `x(1−x)(1−9x)H_A`. -/
def A3s : PowerSeries ℚ := Pode * Submission.CDT.HA

lemma deriv_C_mul (a : ℚ) (f : PowerSeries ℚ) :
    PowerSeries.derivative (R := ℚ) (C a * f) = C a * PowerSeries.derivative (R := ℚ) f := by
  rw [← PowerSeries.smul_eq_C_mul, Derivation.map_smul, PowerSeries.smul_eq_C_mul]

lemma deriv_mul (f g : PowerSeries ℚ) :
    PowerSeries.derivative (R := ℚ) (f * g) = PowerSeries.derivative (R := ℚ) f * g + f * PowerSeries.derivative (R := ℚ) g := by
  rw [Derivation.leibniz, smul_eq_mul]
  ring

lemma deriv_Pode : PowerSeries.derivative (R := ℚ) Pode = dPode := by
  rw [Pode, dPode, map_add, map_sub, deriv_C_mul, deriv_C_mul]
  rw [PowerSeries.derivative_pow, PowerSeries.derivative_pow, PowerSeries.derivative_X]
  simp only [map_ofNat]
  ring_nf

lemma HA_odeLHS_eq (y : PowerSeries ℚ) :
    Submission.CDT.HA_odeLHS y
      = Pode * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) y)
        + dPode * PowerSeries.derivative (R := ℚ) y + (-C 3 + C 9 * X) * y := rfl

/-- the Leibniz expansion of `L(f·g)` at `f`: `L(fg) = g·L(f) + g'·(2Pf' + P'f) + g''·Pf`. -/
lemma HA_odeLHS_mul (f g : PowerSeries ℚ) :
    Submission.CDT.HA_odeLHS (f * g) = g * Submission.CDT.HA_odeLHS f
      + PowerSeries.derivative (R := ℚ) g
          * (2 * Pode * PowerSeries.derivative (R := ℚ) f + dPode * f)
      + PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) g) * (Pode * f) := by
  rw [HA_odeLHS_eq, HA_odeLHS_eq, deriv_mul f g, map_add, deriv_mul, deriv_mul]
  ring

lemma HA_mul_inv : Submission.CDT.HA * Submission.CDT.HA⁻¹ = 1 := by
  refine PowerSeries.mul_inv_cancel _ ?_
  rw [show PowerSeries.constantCoeff Submission.CDT.HA = 1 from ?_]
  · norm_num
  · rw [show Submission.CDT.HA = PowerSeries.mk Submission.CDT.HA_coeff from rfl,
      PowerSeries.constantCoeff_mk]
    norm_num [Submission.CDT.HA_coeff]

lemma HA_mul_U : Submission.CDT.HA * U = Submission.CDT.HB := by
  rw [U]
  calc Submission.CDT.HA * (Submission.CDT.HB * Submission.CDT.HA⁻¹)
      = Submission.CDT.HB * (Submission.CDT.HA * Submission.CDT.HA⁻¹) := by ring
    _ = Submission.CDT.HB := by rw [HA_mul_inv, mul_one]

/-- the first-order equation for `U`: `A₃·U'' + A₂·U' = 1`. -/
lemma U_ode : A3s * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) U)
    + A2s * PowerSeries.derivative (R := ℚ) U = 1 := by
  have h1 : Submission.CDT.HA_odeLHS (Submission.CDT.HA * U) = 1 := by
    rw [HA_mul_U]; exact Submission.CDT.HB_ode
  rw [HA_odeLHS_mul, HA_ode_clean, mul_zero, zero_add] at h1
  have hthis : A3s * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) U)
      + A2s * PowerSeries.derivative (R := ℚ) U
      = PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) U) * (Pode * Submission.CDT.HA)
        + PowerSeries.derivative (R := ℚ) U
            * (2 * Pode * PowerSeries.derivative (R := ℚ) Submission.CDT.HA
              + dPode * Submission.CDT.HA) := by
    rw [A3s, A2s]; ring
  rw [hthis, add_comm]; exact h1

/-- **the key identity**: `(H_A·A₃·U')' = H_A`.  Consequence of `L(H_A) = 0`, `L(H_B) = 1`. -/
lemma key_identity :
    PowerSeries.derivative (R := ℚ) (Submission.CDT.HA * A3s * PowerSeries.derivative (R := ℚ) U)
      = Submission.CDT.HA := by
  have hU := U_ode
  have hA3U : A3s * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) U)
      = 1 - A2s * PowerSeries.derivative (R := ℚ) U := by
    rw [← hU]; ring
  have hbr : PowerSeries.derivative (R := ℚ) (Submission.CDT.HA * A3s)
      - Submission.CDT.HA * A2s = 0 := by
    have e1 : Submission.CDT.HA * A3s = Pode * Submission.CDT.HA ^ 2 := by rw [A3s]; ring
    have e2 : Submission.CDT.HA * A2s
        = PowerSeries.derivative (R := ℚ) (Pode * Submission.CDT.HA ^ 2) := by
      rw [A2s, deriv_mul Pode (Submission.CDT.HA ^ 2), PowerSeries.derivative_pow, deriv_Pode]
      simp
      ring
    rw [e1, e2]; ring
  calc PowerSeries.derivative (R := ℚ) (Submission.CDT.HA * A3s * PowerSeries.derivative (R := ℚ) U)
      = PowerSeries.derivative (R := ℚ) (Submission.CDT.HA * A3s) * PowerSeries.derivative (R := ℚ) U
          + (Submission.CDT.HA * A3s) * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) U) := by
        rw [deriv_mul]
    _ = PowerSeries.derivative (R := ℚ) (Submission.CDT.HA * A3s) * PowerSeries.derivative (R := ℚ) U
          + Submission.CDT.HA
              * (A3s * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) U)) := by ring
    _ = PowerSeries.derivative (R := ℚ) (Submission.CDT.HA * A3s) * PowerSeries.derivative (R := ℚ) U
          + Submission.CDT.HA * (1 - A2s * PowerSeries.derivative (R := ℚ) U) := by rw [hA3U]
    _ = Submission.CDT.HA
          + PowerSeries.derivative (R := ℚ) U
              * (PowerSeries.derivative (R := ℚ) (Submission.CDT.HA * A3s)
                - Submission.CDT.HA * A2s) := by ring
    _ = Submission.CDT.HA := by rw [hbr]; ring

/-- `H_A·A₃·U' = x·D̂·U'` with `D̂ = (1−10x+9x²)H_A²`. -/
def Dhat : PowerSeries ℚ := (1 - C 10 * X + C 9 * X ^ 2) * Submission.CDT.HA ^ 2

lemma key_identity' :
    Submission.CDT.HA * A3s * PowerSeries.derivative (R := ℚ) U = X * (Dhat * PowerSeries.derivative (R := ℚ) U) := by
  rw [A3s, Dhat, Pode]; ring

/-- the coefficient form of the key identity: `(m+1)·[x^m](D̂·U') = a_m`. -/
lemma coeff_key (m : ℕ) :
    PowerSeries.coeff m (Dhat * PowerSeries.derivative (R := ℚ) U) * ((m : ℚ) + 1)
      = Submission.CDT.HA_coeff m := by
  have hXm : ∀ (g : PowerSeries ℚ) (m : ℕ),
      PowerSeries.coeff (m + 1) (X * g) = PowerSeries.coeff m g := by
    intro g m
    simpa [Nat.add_comm] using (PowerSeries.coeff_X_pow_mul g 1 m)
  have h := congrArg (fun f : PowerSeries ℚ => PowerSeries.coeff m f) key_identity
  rw [key_identity', PowerSeries.coeff_derivative, hXm] at h
  rw [Submission.CDT.coeff_HA] at h
  exact h

/-- the series with coefficients `a_m/(m+1)`. -/
def Bhat : PowerSeries ℚ := PowerSeries.mk (fun m => Submission.CDT.HA_coeff m / ((m : ℚ) + 1))

lemma coeff_Bhat (m : ℕ) : PowerSeries.coeff m Bhat
    = Submission.CDT.HA_coeff m / ((m : ℚ) + 1) := PowerSeries.coeff_mk m _

/-- `D̂·U' = B̂`. -/
lemma Dhat_mul_derivU : Dhat * PowerSeries.derivative (R := ℚ) U = Bhat := by
  apply PowerSeries.ext
  intro m
  rw [coeff_Bhat]
  have h := coeff_key m
  have hne : ((m : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  linarith [h]

/-! ## 3. Integer coefficients `D̂ ∈ ℤ⟦x⟧`, `D̂⁻¹ ∈ ℤ⟦x⟧` -/

/-- a power series over `ℚ` has integer coefficients -/
def IntCoeffs (f : PowerSeries ℚ) : Prop := ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n f = z

lemma intCoeffs_one : IntCoeffs (1 : PowerSeries ℚ) := by
  intro n
  refine ⟨if n = 0 then 1 else 0, ?_⟩
  rw [PowerSeries.coeff_one]
  split <;> simp

lemma intCoeffs_C_nat (k : ℕ) : IntCoeffs (C (k : ℚ)) := by
  intro n
  refine ⟨if n = 0 then (k : ℤ) else 0, ?_⟩
  rw [PowerSeries.coeff_C]
  split <;> simp

lemma intCoeffs_X : IntCoeffs (X : PowerSeries ℚ) := by
  intro n
  refine ⟨if n = 1 then 1 else 0, ?_⟩
  rw [PowerSeries.coeff_X]
  split <;> simp

lemma intCoeffs_HA : IntCoeffs Submission.CDT.HA := by
  intro n
  exact ⟨Submission.CDT.HA_coeffZ n, by
    rw [Submission.CDT.coeff_HA, Submission.CDT.HA_coeff_eq_cast]⟩

/-- a finite sum of "integers" is an integer -/
lemma intFinset_sum {ι : Type*} (s : Finset ι) (g : ι → ℚ)
    (hg : ∀ i ∈ s, ∃ z : ℤ, g i = z) : ∃ z : ℤ, ∑ i ∈ s, g i = z := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨z, hz⟩ := hg a (Finset.mem_insert_self a s)
    obtain ⟨w, hw⟩ := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    refine ⟨z + w, ?_⟩
    rw [Finset.sum_insert ha, hz, hw]
    norm_num

lemma int_mul' {a b : ℚ} (ha : ∃ z : ℤ, a = z) (hb : ∃ z : ℤ, b = z) :
    ∃ z : ℤ, a * b = z := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨w, rfl⟩ := hb
  exact ⟨z * w, by norm_num⟩

lemma IntCoeffs.add {f g : PowerSeries ℚ} (hf : IntCoeffs f) (hg : IntCoeffs g) :
    IntCoeffs (f + g) := by
  intro n
  obtain ⟨z, hz⟩ := hf n
  obtain ⟨w, hw⟩ := hg n
  exact ⟨z + w, by rw [map_add, hz, hw]; norm_num⟩

lemma IntCoeffs.neg {f : PowerSeries ℚ} (hf : IntCoeffs f) : IntCoeffs (-f) := by
  intro n
  obtain ⟨z, hz⟩ := hf n
  exact ⟨-z, by rw [map_neg, hz]; norm_num⟩

lemma IntCoeffs.sub {f g : PowerSeries ℚ} (hf : IntCoeffs f) (hg : IntCoeffs g) :
    IntCoeffs (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

lemma IntCoeffs.mul {f g : PowerSeries ℚ} (hf : IntCoeffs f) (hg : IntCoeffs g) :
    IntCoeffs (f * g) := by
  intro n
  have h : PowerSeries.coeff n (f * g)
      = ∑ i ∈ Finset.range (n + 1),
          PowerSeries.coeff i f * PowerSeries.coeff (n - i) g := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j g) n]
  rw [h]
  exact intFinset_sum _ _ (fun i _ => int_mul' (hf i) (hg (n - i)))

lemma IntCoeffs.pow {f : PowerSeries ℚ} (hf : IntCoeffs f) (k : ℕ) : IntCoeffs (f ^ k) := by
  induction k with
  | zero => simpa using intCoeffs_one
  | succ k ih => rw [pow_succ]; exact ih.mul hf

lemma intCoeffs_Dhat : IntCoeffs Dhat := by
  rw [Dhat]
  exact ((IntCoeffs.add (IntCoeffs.sub intCoeffs_one
    ((intCoeffs_C_nat 10).mul intCoeffs_X)) ((intCoeffs_C_nat 9).mul (intCoeffs_X.pow 2)))).mul
    (intCoeffs_HA.pow 2)

lemma coeff_zero_Dhat : PowerSeries.coeff 0 Dhat = 1 := by
  have h1 : PowerSeries.coeff 0 (1 - C 10 * X + C 9 * X ^ 2 : PowerSeries ℚ) = 1 := by
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_one, PowerSeries.coeff_X]
    norm_num
  have h2 : PowerSeries.coeff 0 (Submission.CDT.HA ^ 2) = 1 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i Submission.CDT.HA * PowerSeries.coeff j Submission.CDT.HA) 0]
    simp only [Finset.sum_range_one, Nat.sub_zero]
    rw [Submission.CDT.coeff_HA, HA_coeff_zero_clean]
    norm_num
  rw [Dhat, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i (1 - C 10 * X + C 9 * X ^ 2 : PowerSeries ℚ)
        * PowerSeries.coeff j (Submission.CDT.HA ^ 2)) 0]
  simp only [Finset.sum_range_one, Nat.sub_zero]
  rw [h1, h2]
  norm_num

lemma constantCoeff_Dhat : PowerSeries.constantCoeff Dhat = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_Dhat]

/-- the coefficients of `D̂⁻¹` are integers (strong induction on the degree). -/
lemma intCoeffs_Dhat_inv : IntCoeffs Dhat⁻¹ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_inv]
    split
    · exact ⟨1, by rw [constantCoeff_Dhat]; norm_num⟩
    · rename_i hn
      have hsum : ∃ z : ℤ, (∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
          (if x.2 < n then PowerSeries.coeff x.1 Dhat * PowerSeries.coeff x.2 Dhat⁻¹ else 0)) = z := by
        refine intFinset_sum _ _ (fun x hx => ?_)
        by_cases hx2 : x.2 < n
        · rw [if_pos hx2]
          exact int_mul' (intCoeffs_Dhat x.1) (ih x.2 hx2)
        · rw [if_neg hx2]
          exact ⟨0, by norm_num⟩
      obtain ⟨z, hz⟩ := hsum
      refine ⟨-z, ?_⟩
      rw [constantCoeff_Dhat, inv_one, hz]
      norm_num

/-! ## 4. `lcm(1..n)` arithmetic -/

lemma lcmUpto_pos (n : ℕ) : 0 < Submission.CDTPlan.lcmUpto n := by
  rw [Submission.CDTPlan.lcmUpto]
  by_contra h
  have h0 : (Finset.Icc 1 n).lcm id = 0 := by omega
  obtain ⟨x, hx, hx0⟩ := (Finset.lcm_eq_zero_iff (f := id)).mp h0
  simp only [id_eq] at hx0
  have h1 : 1 ≤ x := (Finset.mem_Icc.mp hx).1
  omega

lemma dvd_lcmUpto {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) : m ∣ Submission.CDTPlan.lcmUpto n := by
  rw [Submission.CDTPlan.lcmUpto]
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hm, hmn⟩)

lemma lcmUpto_dvd {m n : ℕ} (hmn : m ≤ n) :
    Submission.CDTPlan.lcmUpto m ∣ Submission.CDTPlan.lcmUpto n := by
  rw [Submission.CDTPlan.lcmUpto, Submission.CDTPlan.lcmUpto]
  exact Finset.lcm_mono (Finset.Icc_subset_Icc_right hmn) (f := id)

lemma lcm_sq_dvd (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (k * Submission.CDTPlan.lcmUpto k) ∣ (Submission.CDTPlan.lcmUpto n) ^ 2 := by
  rw [pow_two]
  exact mul_dvd_mul (dvd_lcmUpto hk hkn) (lcmUpto_dvd hkn)

/-- If `c ∣ C` and `c·x` is an integer then so is `C·x`. -/
lemma int_of_dvd_mul {c C : ℕ} {x : ℚ} (h : c ∣ C) (hx : ∃ z : ℤ, (c : ℚ) * x = z) :
    ∃ z : ℤ, (C : ℚ) * x = z := by
  obtain ⟨q, rfl⟩ := h
  obtain ⟨z, hz⟩ := hx
  refine ⟨(q : ℤ) * z, ?_⟩
  push_cast
  rw [← hz]
  ring

/-! ## 5. The denominators of `U'` and `U` -/

lemma derivU_eq : PowerSeries.derivative (R := ℚ) U = Dhat⁻¹ * Bhat := by
  have h : Dhat⁻¹ * Dhat = 1 := by
    refine PowerSeries.inv_mul_cancel _ ?_
    rw [constantCoeff_Dhat]; norm_num
  calc PowerSeries.derivative (R := ℚ) U = (Dhat⁻¹ * Dhat) * PowerSeries.derivative (R := ℚ) U := by
        rw [h]; ring
    _ = Dhat⁻¹ * (Dhat * PowerSeries.derivative (R := ℚ) U) := by ring
    _ = Dhat⁻¹ * Bhat := by rw [Dhat_mul_derivU]

/-- `lcm(1..m+1) · [x^m]U' ∈ ℤ`. -/
lemma derivU_lcm (m : ℕ) : ∃ z : ℤ,
    (Submission.CDTPlan.lcmUpto (m+1) : ℚ) * PowerSeries.coeff m (PowerSeries.derivative (R := ℚ) U) = z := by
  have hcoeff : PowerSeries.coeff m (PowerSeries.derivative (R := ℚ) U)
      = ∑ i ∈ Finset.range (m + 1),
          PowerSeries.coeff i Dhat⁻¹ * PowerSeries.coeff (m - i) Bhat := by
    rw [derivU_eq, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i Dhat⁻¹ * PowerSeries.coeff j Bhat) m]
  rw [hcoeff, Finset.mul_sum]
  refine intFinset_sum _ _ (fun i hi => ?_)
  have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hdvd : (m - i + 1) ∣ Submission.CDTPlan.lcmUpto (m+1) :=
    dvd_lcmUpto (by omega) (by omega)
  have hx : ∃ z : ℤ, ((m - i + 1 : ℕ) : ℚ) * PowerSeries.coeff (m - i) Bhat = z := by
    rw [coeff_Bhat]
    refine ⟨Submission.CDT.HA_coeffZ (m - i), ?_⟩
    rw [Submission.CDT.HA_coeff_eq_cast]
    have hc : (((m - i + 1 : ℕ)) : ℚ) = ((m - i : ℚ) + 1) := by
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub him]
    rw [hc]
    field_simp
    rw [Nat.cast_sub him]
    ring
  obtain ⟨zb, hzb⟩ := int_of_dvd_mul hdvd hx
  obtain ⟨ze, hze⟩ := intCoeffs_Dhat_inv i
  refine ⟨ze * zb, ?_⟩
  rw [show (Submission.CDTPlan.lcmUpto (m + 1) : ℚ)
        * (PowerSeries.coeff i Dhat⁻¹ * PowerSeries.coeff (m - i) Bhat)
      = PowerSeries.coeff i Dhat⁻¹
        * ((Submission.CDTPlan.lcmUpto (m + 1) : ℚ)
          * PowerSeries.coeff (m - i) Bhat) from by ring,
    hze, hzb]
  push_cast
  ring

lemma coeff_zero_U : PowerSeries.coeff 0 U = 0 := by
  have h := congrArg (fun f : PowerSeries ℚ => PowerSeries.coeff 0 f) HA_mul_U
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i Submission.CDT.HA * PowerSeries.coeff j U) 0] at h
  simp only [Finset.sum_range_one, Nat.sub_zero] at h
  rw [Submission.CDT.coeff_HA, HA_coeff_zero_clean, one_mul, Submission.CDT.coeff_HB,
    Submission.CDT.HB_coeff_zero] at h
  exact h

/-- `k·lcm(1..k)·[x^k]U ∈ ℤ` for `k ≥ 1`. -/
lemma U_lcm (k : ℕ) (hk : 1 ≤ k) : ∃ z : ℤ,
    ((k * Submission.CDTPlan.lcmUpto k : ℕ) : ℚ) * PowerSeries.coeff k U = z := by
  have hcast : (((k - 1 : ℕ)) : ℚ) + 1 = (k : ℚ) := by
    rw [Nat.cast_sub hk]; norm_num
  have hcd : PowerSeries.coeff (k - 1) (PowerSeries.derivative (R := ℚ) U)
      = PowerSeries.coeff k U * (k : ℚ) := by
    rw [PowerSeries.coeff_derivative, show k - 1 + 1 = k by omega, hcast]
  obtain ⟨z, hz⟩ := derivU_lcm (k - 1)
  rw [show k - 1 + 1 = k by omega, hcd] at hz
  refine ⟨z, ?_⟩
  rw [← hz]
  push_cast
  ring

/-! ## 6. Transfer to `HB_coeff` and the target -/

/-- `[1..n]²·b_n ∈ ℤ` — the paper's `defabc` item 2 for `b_n` (with `K = 1`). -/
lemma HB_coeff_lcm_sq (n : ℕ) (hn : 1 ≤ n) : ∃ z : ℤ,
    ((lcmUpto n : ℚ) ^ 2) * Submission.CDT.HB_coeff n = z := by
  have hcoeff : Submission.CDT.HB_coeff n
      = ∑ i ∈ Finset.range (n + 1), Submission.CDT.HA_coeff i * PowerSeries.coeff (n - i) U := by
    rw [← Submission.CDT.coeff_HB, ← HA_mul_U, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i Submission.CDT.HA * PowerSeries.coeff j U) n]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Submission.CDT.coeff_HA]
  rw [hcoeff, Finset.mul_sum]
  refine intFinset_sum _ _ (fun i hi => ?_)
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rcases Nat.eq_zero_or_pos (n - i) with hzero | hpos
  · rw [hzero, coeff_zero_U, mul_zero]
    exact ⟨0, by norm_num⟩
  · have hdvd := lcm_sq_dvd n (n - i) hpos (by omega)
    obtain ⟨z, hz⟩ := int_of_dvd_mul hdvd (U_lcm (n - i) hpos)
    have hza : ∃ w : ℤ, Submission.CDT.HA_coeff i = w :=
      ⟨Submission.CDT.HA_coeffZ i, Submission.CDT.HA_coeff_eq_cast i⟩
    obtain ⟨za, hza⟩ := hza
    refine ⟨za * z, ?_⟩
    rw [show (lcmUpto n : ℚ) ^ 2 * (Submission.CDT.HA_coeff i * PowerSeries.coeff (n - i) U)
          = Submission.CDT.HA_coeff i
            * ((lcmUpto n : ℚ) ^ 2 * PowerSeries.coeff (n - i) U) from by ring,
      hza]
    push_cast at hz ⊢
    rw [hz]

/-- **`ZagierBIntegrality`** (`Submission.CDTPlan.InterfacesA`): `[1..n]²·b_n ∈ ℤ` up to a fixed
factor `K`, i.e. here with `K = 1`. -/
theorem zagier_b_integrality : ZagierBIntegrality := by
  refine ⟨1, by norm_num, fun n hn => ?_⟩
  obtain ⟨z, hz⟩ := HB_coeff_lcm_sq n hn
  exact ⟨z, by simpa using hz⟩

end
end Work.ZagBI
