import Mathlib
import Submission.Commons.Data.Nat.Choose.zagierC_recurrence

/-!
# `H_A` of the paper's Theorem-A proof: the Hauptmodul series on `Y₀(6)`

Foundation of the CDT proof of Theorem `mainA` (arXiv:2408.15403,
§"Zagier's sequences A and C"): with the coefficient sequence
`aₙ = Σ_{k=0}^{n} C(n,k)²·C(2k,k)` (Zagier's sequence `C`, values
`1, 3, 15, 93, 639, 4653, …`), the power series
`H_A(x) = Σₙ aₙxⁿ = 1 + 3x + 15x² + 93x³ + …`.

**Proved here**: the coefficients `HA_coeff` (rational), their integer
bridge `HA_coeff_eq_cast`, the initial values `a₀ = 1, a₁ = 3, a₂ = 15`, and
the **three-term P-recurrence in `ℚ`** `HA_coeff_recurrence` (cast of the
commons integer recurrence `Commons.Data.Nat.Choose.zagierC_recurrence`,
which was proved by creative telescoping).

**Proved here**: the homogeneous second-order ODE.  The operator
`HA_odeLHS` below is the expanded form of
`x(1−x)(1−9x)·y'' + (1−20x+27x²)·y' + 3(−1+3x)·y`
(`X(1−X)(1−9X) = X − 10X² + 9X³`, `3(−1+3X) = −3 + 9X`), and
`HA_ode : HA_odeLHS HA = 0`.  Proof: coefficient-wise
(`HA_odeLHS_coeff`); for `n ≥ 1` the `xⁿ`-coefficient of the ODE-LHS is
`((n+1:ℕ):ℚ)²·a_{n+1} − (10(n:ℚ)²+10(n:ℚ)+3)·aₙ + 9(n:ℚ)²·a_{n−1}`,
which vanishes by the `HA_coeff_recurrence_zero` form of the three-term
P-recurrence; the `x⁰`-coefficient is `a₁ − 3a₀ = 0`.  Mechanics: split the
ODE-LHS into monomial pieces with `ring`, extract coefficients with
`PowerSeries.coeff_X_pow_mul` / `coeff_X_pow_mul'`
(`coeff (d+m) (X^m·p) = coeff d p`, and `0` below the `m`-th degree) and
`PowerSeries.coeff_derivative` (`coeff k (derivative f) = coeff (k+1) f·(↑k+1)`),
then case-split on `n = 0 | 1 | 2 | k+3`.

**Next brick**: the companion sequences `bₙ, cₙ` (Zagier's sequences `A`
and `B` at the same parameter value — the coefficients of the `H_B`, `H_C`
series of the paper's Proposition `functionsH`, eqs. (zagr)/(zagrt)), their
P-recurrences and the inhomogeneous ODE data needed for the function
`H(x) = a·H_A(x) + b·H_B(x) + c·H_C(x)` of denominator type `[1..n]²`
under the assumed `ℚ`-dependence of `1, ζ(2), L(2,χ₋₃)`.

All coefficients live in `ℚ` (the recurrence and values are integers,
pushed into `ℚ` by `exact_mod_cast`).
-/
open scoped BigOperators

noncomputable section

namespace Submission.CDT

/-- the coefficients `aₙ = Σₖ C(n,k)²·C(2k,k)` (Zagier's sequence `C`),
as rationals -/
def HA_coeff (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℚ) ^ 2 * (Nat.choose (2 * k) k : ℚ)

/-- the integer version of the same sequence -/
def HA_coeffZ (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) ^ 2 * (Nat.choose (2 * k) k : ℤ)

/-- the rational coefficients are the casts of the integers -/
lemma HA_coeff_eq_cast (n : ℕ) : HA_coeff n = (HA_coeffZ n : ℚ) := by
  unfold HA_coeff HA_coeffZ
  exact_mod_cast rfl

/-- the Hauptmodul series `H_A(x) = Σₙ aₙ xⁿ` -/
def HA : PowerSeries ℚ := PowerSeries.mk HA_coeff

lemma coeff_HA (n : ℕ) : PowerSeries.coeff n HA = HA_coeff n := by
  rw [HA, PowerSeries.coeff_mk]

/-- initial values `a₀ = 1`, `a₁ = 3`, `a₂ = 15`.

(Axiom-purge: these were `native_decide`, which injects
`…_native.native_decide.ax_*` axioms into every downstream proof.  The
statements are unchanged; the proofs now evaluate the defining finite sum
with `norm_num`, so `#print axioms` stays inside
`propext`/`Classical.choice`/`Quot.sound`.) -/
lemma HA_coeff_zero : HA_coeff 0 = 1 := by
  norm_num [HA_coeff, Finset.sum_range_succ, Nat.choose]

lemma HA_coeff_one : HA_coeff 1 = 3 := by
  norm_num [HA_coeff, Finset.sum_range_succ, Nat.choose]

lemma HA_coeff_two : HA_coeff 2 = 15 := by
  norm_num [HA_coeff, Finset.sum_range_succ, Nat.choose]

/-- the three-term P-recurrence in `ℚ` (from the integer recurrence of the
commons, cast) -/
lemma HA_coeff_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℕ) : ℚ) ^ 2 * HA_coeff (n + 1) =
      ((10 : ℚ) * (n : ℚ) ^ 2 + 10 * (n : ℚ) + 3) * HA_coeff n
        - (9 : ℚ) * (n : ℚ) ^ 2 * HA_coeff (n - 1) := by
  -- integer recurrence, with the inline sums identified with HA_coeffZ
  have hZ' : ((n + 1 : ℕ) : ℤ) ^ 2 * HA_coeffZ (n + 1) =
      ((10 : ℤ) * (n : ℤ) ^ 2 + 10 * (n : ℤ) + 3) * HA_coeffZ n
        - (9 : ℤ) * (n : ℤ) ^ 2 * HA_coeffZ (n - 1) := by
    simpa [HA_coeffZ, show (n - 1) + 1 = n by omega] using
      (Commons.Data.Nat.Choose.zagierC_recurrence n hn)
  have hQ := congrArg (fun z : ℤ => (z : ℚ)) hZ'
  -- push the casts through the ℤ-algebra structure
  push_cast at hQ
  -- rewrite the cast coefficients to the rational sequence
  rw [← HA_coeff_eq_cast (n + 1), ← HA_coeff_eq_cast n, ← HA_coeff_eq_cast (n - 1)] at hQ
  -- align the coefficient factor of the LHS (push_cast writes it as n + 1)
  rw [show ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 by
    rw [Nat.cast_add, Nat.cast_one]]
  exact hQ


open PowerSeries

/-- the ODE LHS operator in expanded form, equal to the paper's
`X(1−X)(1−9X)·y'' + (1−20X+27X²)·y' + 3(−1+3X)·y` (expand the factors:
`X(1−X)(1−9X) = X − 10X² + 9X³`, `3(−1+3X) = −3 + 9X`). -/
def HA_odeLHS (y : PowerSeries ℚ) : PowerSeries ℚ :=
  (X - C 10 * X ^ 2 + C 9 * X ^ 3) * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) y)
    + ((1 : PowerSeries ℚ) - C 20 * X + C 27 * X ^ 2) * PowerSeries.derivative (R := ℚ) y
    + (-C 3 + C 9 * X) * y

/-- the three-term P-recurrence in zero form:
`(n+1)²·a_{n+1} − (10n²+10n+3)·aₙ + 9n²·a_{n−1} = 0` (for `n ≥ 1`). -/
lemma HA_coeff_recurrence_zero (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℕ) : ℚ) ^ 2 * HA_coeff (n + 1)
      - (((10 : ℚ) * (n : ℚ) ^ 2 + 10 * (n : ℚ) + 3) * HA_coeff n)
      + (9 : ℚ) * (n : ℚ) ^ 2 * HA_coeff (n - 1) = 0 := by
  have hrec := HA_coeff_recurrence n hn
  linear_combination hrec

/-- coefficient form of the homogeneous ODE for `H_A`: every coefficient of
`HA_odeLHS HA` vanishes (n = 0 uses `a₁ − 3a₀ = 0`, `n ≥ 1` uses the
recurrence in zero form). -/
lemma HA_odeLHS_coeff (n : ℕ) : PowerSeries.coeff n (HA_odeLHS HA) = 0 := by
  classical
  let F : PowerSeries ℚ := HA
  let dF : PowerSeries ℚ := PowerSeries.derivative (R := ℚ) F
  let d2F : PowerSeries ℚ := PowerSeries.derivative (R := ℚ) dF
  have hU : ∀ m, PowerSeries.coeff m F = HA_coeff m := by
    intro m
    rw [show F = HA from rfl, coeff_HA]
  have hU0 : HA_coeff 0 = 1 := HA_coeff_zero
  have hU1 : HA_coeff 1 = 3 := HA_coeff_one
  have hU2 : HA_coeff 2 = 15 := HA_coeff_two
  have hderiv : ∀ m, PowerSeries.coeff m dF = HA_coeff (m + 1) * ((m : ℚ) + 1) := by
    intro m
    rw [show dF = PowerSeries.derivative (R := ℚ) HA from rfl, PowerSeries.coeff_derivative, hU]
  have hderiv2 : ∀ m, PowerSeries.coeff m d2F = HA_coeff (m + 2) * ((m : ℚ) + 1) * ((m : ℚ) + 2) := by
    intro m
    rw [show d2F = PowerSeries.derivative (R := ℚ) dF from rfl, PowerSeries.coeff_derivative]
    rw [hderiv (m + 1)]
    ring_nf
    simp [Nat.cast_add, Nat.cast_one]
    ring
  have hsplit :
      HA_odeLHS F
      = X * d2F - C 10 * (X ^ 2 * d2F) + C 9 * (X ^ 3 * d2F)
        + dF - C 20 * (X * dF) + C 27 * (X ^ 2 * dF)
        - C 3 * F + C 9 * (X * F) := by
    rw [show F = HA from rfl]
    unfold HA_odeLHS
    ring
  rw [show HA = F from rfl]
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
          have hz := HA_coeff_recurrence_zero 1 (by norm_num)
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
              have hz := HA_coeff_recurrence_zero 2 (by norm_num)
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
              have hz := HA_coeff_recurrence_zero (k + 3) (by omega)
              ring_nf at hz
              simp only [Nat.cast_add, Nat.cast_ofNat] at hz ⊢
              ring_nf at hz ⊢
              rw [show (3 + k) - 1 = 2 + k by omega] at hz
              linear_combination hz

/-- the homogeneous second-order ODE of the paper satisfied by the
Hauptmodul series `H_A(x) = Σ aₙxⁿ`, eq. (zagr) of arXiv:2408.15403:
`x(1−x)(1−9x)·y'' + (1−20x+27x²)·y' + 3(−1+3x)·y = 0`. -/
lemma HA_ode : HA_odeLHS HA = 0 := by
  apply PowerSeries.ext
  intro n
  exact HA_odeLHS_coeff n

end Submission.CDT
