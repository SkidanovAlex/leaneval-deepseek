import Mathlib
import Submission.CDT.ZagierH
import Submission.CDT.SympDescent
import Submission.Commons.RingTheory.PowerSeries.coeff_inv_one_sub_C_mul

/-!
# The companion series `H_B`, `H_C` and Proposition `functionsH` (CDT)

This module continues the formalization of the Zagier-sequence spine behind
Theorem `mainA` of Calegari–Dimitrov–Tang, arXiv:2408.15403
(§"Zagier's sequences A and C").  `Submission.CDT.ZagierH` introduced the
Hauptmodul series `H_A(x) = Σ aₙxⁿ` (`aₙ = Σₖ C(n,k)²C(2k,k)`, Zagier's
sequence C, values `1,3,15,93,…`) and proved its homogeneous ODE
`HA_ode`:
`x(1−x)(1−9x)y'' + (1−20x+27x²)y' + 3(−1+3x)y = 0`.

Here we introduce the two companion series `H_B(x) = Σ bₙxⁿ =
x + 23x²/4 + 145x³/4 + …` and `H_C(x) = Σ cₙxⁿ = x + 6x² + 343x³/9 + …`
of Lemma `defabc` of the paper.  The coefficients are defined by the paper's
recurrences: `b₀ = c₀ = 0`, `b₁ = c₁ = 1`, and for `n ≥ 1`
`(n+1)²b_{n+1} = (10n²+10n+3)bₙ − 9n²b_{n−1}` (homogeneous, paper eq. (zagr))
and `(n+1)²c_{n+1} = (10n²+10n+3)cₙ − 9n²c_{n−1} + 1` (inhomogeneous, eq. (zagrt)).

**Main results** (the algebraic half of Proposition `functionsH`):
* `HB_ode` : `HA_odeLHS HB = 1` — `H_B` satisfies the ODE with RHS `1`;
* `HC_ode` : `HA_odeLHS HC = (1−X)⁻¹` — `H_C` satisfies the ODE with RHS
  `1/(1−x)` (equivalently `Σ xⁿ`);
* `functionsH_ode` : for any `a b c : ℚ`, the combination
  `H(x) = a·H_A(x) + b·H_B(x) + c·H_C(x)` (def `ZagierH`) satisfies the
  inhomogeneous ODE
  `x(1−x)(1−9x)H'' + (1−20x+27x²)H' + 3(−1+3x)H = b + c/(1−x)`.

The engine is the generic coefficient lemma `HA_odeLHS_coeff_eq`: for any
coefficient sequence `f` satisfying the boundary equation
`f₁ − 3f₀ = e0` and the recurrence with RHS `e1` (all `n ≥ 1`), the
`xⁿ`-coefficient of `HA_odeLHS (mk f)` is `e0` at `n = 0` and `e1` at
`n ≥ 1`.  It is proved by the same four-case coefficient analysis as
`HA_odeLHS_coeff` in `ZagierH` (`n = 0 | 1 | 2 | k+3`).

(Consistency with the paper's displayed initial values is verified:
`b₂ = 23/4`, `c₂ = 6`, `c₃ = 343/9` — see the `example`s below.)

**Still ahead**: the paper's *rationality/denominator-type* claims
(`[1,2,…,n]²·bₙ, [1,2,…,n]²·cₙ ∈ ℤ` — these come from the Eichler-integral
construction, deep), the overconvergence claims of Lemma `defabc` (iii), the
symmetrization `G(y) = Sym⁺H` (§"The symmetrization of H(x)") and the
14-functions/arithmetic-holonomy machinery.  The recurrence-defined `b`, `c`
here are the paper's sequences once the modular/Eichler-integral identity is
established; Proposition `functionsH` itself is purely a consequence of the
recurrences, as in the paper's proof ("either from equation (zagr) and
(zagrt) … one verifies that y = H(x) satisfies the given differential
equation").
-/

open scoped BigOperators

noncomputable section

namespace Submission.CDT

open PowerSeries

/-- coefficients `bₙ` of the companion `H_B`: `b₀ = 0, b₁ = 1`, and the
homogeneous recurrence `(n+1)²b_{n+1} = (10n²+10n+3)bₙ − 9n²b_{n−1}` for
`n ≥ 1` (same recurrence as Zagier's sequence C / `aₙ`, paper eq. (zagr)). -/
def HB_coeff : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      (((10 : ℚ) * ((n + 1 : ℕ) : ℚ) ^ 2 + 10 * ((n + 1 : ℕ) : ℚ) + 3) * HB_coeff (n + 1)
        - (9 : ℚ) * ((n + 1 : ℕ) : ℚ) ^ 2 * HB_coeff n) / (((n + 2 : ℕ) : ℚ) ^ 2)

/-- coefficients `cₙ` of the companion `H_C`: `c₀ = 0, c₁ = 1`, and the
inhomogeneous recurrence `(n+1)²c_{n+1} = (10n²+10n+3)cₙ − 9n²c_{n−1} + 1`
for `n ≥ 1` (paper eq. (zagrt)). -/
def HC_coeff : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      (((10 : ℚ) * ((n + 1 : ℕ) : ℚ) ^ 2 + 10 * ((n + 1 : ℕ) : ℚ) + 3) * HC_coeff (n + 1)
        - (9 : ℚ) * ((n + 1 : ℕ) : ℚ) ^ 2 * HC_coeff n + 1) / (((n + 2 : ℕ) : ℚ) ^ 2)

lemma HB_coeff_zero : HB_coeff 0 = 0 := by rfl
lemma HB_coeff_one : HB_coeff 1 = 1 := by rfl
lemma HC_coeff_zero : HC_coeff 0 = 0 := by rfl
lemma HC_coeff_one : HC_coeff 1 = 1 := by rfl

-- sanity: the recurrence-defined head of `H_B`/`H_C` matches the paper's
-- `defabc` display `b₂ = 23/4, b₃ = 145/4, b₄ = 3993/16`, `c₂ = 6,
-- c₃ = 343/9, c₄ = 788/3` (so `[1..n]²·bₙ, [1..n]²·cₙ ∈ ℤ` holds at the
-- displayed orders: `4·(23/4)=23`, `36·(145/4)=1305`, `36·(343/9)=1372`, …).
lemma HB_coeff_two : HB_coeff 2 = 23 / 4 := by native_decide
lemma HB_coeff_three : HB_coeff 3 = 145 / 4 := by native_decide
lemma HB_coeff_four : HB_coeff 4 = 3993 / 16 := by native_decide
lemma HB_coeff_five : HB_coeff 5 = 727059 / 400 := by native_decide
lemma HC_coeff_two : HC_coeff 2 = 6 := by native_decide
lemma HC_coeff_three : HC_coeff 3 = 343 / 9 := by native_decide
lemma HC_coeff_four : HC_coeff 4 = 788 / 3 := by native_decide
lemma HB_coeff_six : HB_coeff 6 = 5495507 / 400 := by native_decide
lemma HB_coeff_seven : HB_coeff 7 = 417806469 / 3920 := by native_decide
lemma HB_coeff_eight : HB_coeff 8 = 66085799967 / 78400 := by native_decide
lemma HC_coeff_six : HC_coeff 6 = 1084694 / 75 := by native_decide
lemma HC_coeff_seven : HC_coeff 7 = 27488711 / 245 := by native_decide
lemma HC_coeff_eight : HC_coeff 8 = 1086994872 / 1225 := by native_decide

/-- the companion series `H_B(x) = Σ bₙxⁿ = x + 23x²/4 + 145x³/4 + …` -/
def HB : PowerSeries ℚ := PowerSeries.mk HB_coeff

/-- the companion series `H_C(x) = Σ cₙxⁿ = x + 6x² + 343x³/9 + …` -/
def HC : PowerSeries ℚ := PowerSeries.mk HC_coeff

lemma coeff_HB (n : ℕ) : PowerSeries.coeff n HB = HB_coeff n := by
  rw [HB, PowerSeries.coeff_mk]

lemma coeff_HC (n : ℕ) : PowerSeries.coeff n HC = HC_coeff n := by
  rw [HC, PowerSeries.coeff_mk]

/-- k-form of the homogeneous recurrence for `b` (all `k`): -/
lemma HB_coeff_recurrence_k (k : ℕ) :
    ((k + 2 : ℕ) : ℚ) ^ 2 * HB_coeff (k + 2) =
      (((10 : ℚ) * ((k + 1 : ℕ) : ℚ) ^ 2 + 10 * ((k + 1 : ℕ) : ℚ) + 3) * HB_coeff (k + 1)
        - (9 : ℚ) * ((k + 1 : ℕ) : ℚ) ^ 2 * HB_coeff k) := by
  rw [HB_coeff]
  have hnz : ((k + 2 : ℕ) : ℚ) ^ 2 ≠ 0 := by positivity
  field_simp [hnz]

/-- the homogeneous recurrence for `b` in the paper's zero form, `n ≥ 1` -/
lemma HB_coeff_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℕ) : ℚ) ^ 2 * HB_coeff (n + 1)
      - (((10 : ℚ) * (n : ℚ) ^ 2 + 10 * (n : ℚ) + 3) * HB_coeff n)
      + (9 : ℚ) * (n : ℚ) ^ 2 * HB_coeff (n - 1) = 0 := by
  have hk := HB_coeff_recurrence_k (n - 1)
  rw [show (n - 1) + 2 = n + 1 by omega, show (n - 1) + 1 = n by omega] at hk
  linear_combination hk

/-- the inhomogeneous recurrence for `c` (`n ≥ 1`, RHS `1`) -/
lemma HC_coeff_recurrence (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℕ) : ℚ) ^ 2 * HC_coeff (n + 1)
      - (((10 : ℚ) * (n : ℚ) ^ 2 + 10 * (n : ℚ) + 3) * HC_coeff n)
      + (9 : ℚ) * (n : ℚ) ^ 2 * HC_coeff (n - 1) = 1 := by
  have hk : ((n - 1 + 2 : ℕ) : ℚ) ^ 2 * HC_coeff (n - 1 + 2) =
      (((10 : ℚ) * ((n - 1 + 1 : ℕ) : ℚ) ^ 2 + 10 * ((n - 1 + 1 : ℕ) : ℚ) + 3) * HC_coeff (n - 1 + 1)
        - (9 : ℚ) * ((n - 1 + 1 : ℕ) : ℚ) ^ 2 * HC_coeff (n - 1) + 1) := by
    conv_lhs => rw [HC_coeff]
    field_simp
  rw [show n - 1 + 2 = n + 1 by omega, show n - 1 + 1 = n by omega] at hk
  linear_combination hk

lemma HA_odeLHS_coeff_eq (f : ℕ → ℚ) (e0 e1 : ℚ)
    (hc0 : f 1 - 3 * f 0 = e0)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      ((n + 1 : ℕ) : ℚ) ^ 2 * f (n + 1)
        - (((10 : ℚ) * (n : ℚ) ^ 2 + 10 * (n : ℚ) + 3) * f n)
        + (9 : ℚ) * (n : ℚ) ^ 2 * f (n - 1) = e1) :
    ∀ n : ℕ, PowerSeries.coeff n (HA_odeLHS (PowerSeries.mk f)) = if n = 0 then e0 else e1 := by
  intro n
  classical
  let F : PowerSeries ℚ := PowerSeries.mk f
  let dF : PowerSeries ℚ := PowerSeries.derivative (R := ℚ) F
  let d2F : PowerSeries ℚ := PowerSeries.derivative (R := ℚ) dF
  have hU : ∀ m, PowerSeries.coeff m F = f m := by
    intro m
    rw [show F = PowerSeries.mk f from rfl, PowerSeries.coeff_mk]
  have hderiv : ∀ m, PowerSeries.coeff m dF = f (m + 1) * ((m : ℚ) + 1) := by
    intro m
    rw [show dF = PowerSeries.derivative (R := ℚ) F from rfl, PowerSeries.coeff_derivative, hU]
  have hderiv2 : ∀ m, PowerSeries.coeff m d2F = f (m + 2) * ((m : ℚ) + 1) * ((m : ℚ) + 2) := by
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
    unfold HA_odeLHS
    ring
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
      rw [if_pos rfl]
      have hz1 : PowerSeries.coeff 0 (X * d2F) = 0 := by simp
      have hz2 := hzpow d2F 2 0 (by norm_num)
      have hz3 := hzpow d2F 3 0 (by norm_num)
      have hz4 : PowerSeries.coeff 0 (X * dF) = 0 := by simp
      have hz5 := hzpow dF 2 0 (by norm_num)
      have hz6 : PowerSeries.coeff 0 (X * F) = 0 := by simp
      rw [hz1, hz2, hz3, hz4, hz5, hz6, hderiv 0, hU 0]
      norm_num
      exact hc0
  | succ m =>
      rw [if_neg (by omega : ¬ m + 1 = 0)]
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
          have hz := hrec 1 (by norm_num)
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
              have hz := hrec 2 (by norm_num)
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
              have hz := hrec (k + 3) (by omega)
              ring_nf at hz
              simp only [Nat.cast_add, Nat.cast_ofNat] at hz ⊢
              ring_nf at hz ⊢
              rw [show (3 + k) - 1 = 2 + k by omega] at hz
              linear_combination hz

/-- the coefficients of `H_B` give the inhomogeneous ODE `L(H_B) = 1`
coefficient-wise: `coeff 0 = b₁ − 3b₀ = 1`, `coeff n = 0` for `n ≥ 1`. -/
lemma HB_odeLHS_coeff (n : ℕ) :
    PowerSeries.coeff n (HA_odeLHS HB) = if n = 0 then 1 else 0 := by
  have hc0 : HB_coeff 1 - 3 * HB_coeff 0 = 1 := by norm_num [HB_coeff]
  have hg := HA_odeLHS_coeff_eq HB_coeff 1 0 hc0 HB_coeff_recurrence n
  simpa [HB] using hg

/-- the coefficients of `H_C` give the inhomogeneous ODE `L(H_C) = 1/(1−x)`
coefficient-wise: every coefficient is `1`. -/
lemma HC_odeLHS_coeff (n : ℕ) :
    PowerSeries.coeff n (HA_odeLHS HC) = 1 := by
  have hc0 : HC_coeff 1 - 3 * HC_coeff 0 = 1 := by norm_num [HC_coeff]
  have hg := HA_odeLHS_coeff_eq HC_coeff 1 1 hc0 HC_coeff_recurrence n
  have hg' : PowerSeries.coeff n (HA_odeLHS (PowerSeries.mk HC_coeff)) = if n = 0 then 1 else 1 := hg
  simpa [HC] using hg

/-- the companion series `H_B` satisfies the *inhomogeneous* ODE with RHS `1` -/
lemma HB_ode : HA_odeLHS HB = 1 := by
  apply PowerSeries.ext
  intro n
  rw [HB_odeLHS_coeff]
  simp

/-- `1/(1−x)` as a power series has every coefficient `1` -/
lemma coeff_inv_one_sub_eq_one (n : ℕ) : PowerSeries.coeff n ((1 : PowerSeries ℚ) - X)⁻¹ = 1 := by
  have h := Commons.RingTheory.PowerSeries.coeff_inv_one_sub_C_mul ℚ (1 : ℚ) n
  simpa using h

/-- the companion series `H_C` satisfies the *inhomogeneous* ODE with RHS `1/(1−x)` -/
lemma HC_ode : HA_odeLHS HC = ((1 : PowerSeries ℚ) - X)⁻¹ := by
  apply PowerSeries.ext
  intro n
  rw [HC_odeLHS_coeff, coeff_inv_one_sub_eq_one]

/-- the paper's function `H(x) = a·H_A(x) + b·H_B(x) + c·H_C(x)` (eq. (defH)) -/
def ZagierH (a b c : ℚ) : PowerSeries ℚ := C a * HA + C b * HB + C c * HC

/-- coefficients of `ZagierH` -/
lemma ZagierH_coeff (a b c : ℚ) (n : ℕ) :
    PowerSeries.coeff n (ZagierH a b c) = a * HA_coeff n + b * HB_coeff n + c * HC_coeff n := by
  rw [ZagierH]
  simp [coeff_HA, coeff_HB, coeff_HC]

/-- the coefficient function of `ZagierH a b c` -/
def ZagierH_coeff_seq (a b c : ℚ) (n : ℕ) : ℚ := a * HA_coeff n + b * HB_coeff n + c * HC_coeff n

lemma ZagierH_eq_mk (a b c : ℚ) : ZagierH a b c = PowerSeries.mk (ZagierH_coeff_seq a b c) := by
  apply PowerSeries.ext
  intro n
  rw [ZagierH_coeff, PowerSeries.coeff_mk]
  rfl

/-- the generic ODE lemma instantiated for the coefficient sequence of
`ZagierH a b c`: `L(ZagierH)` has coefficient `b + c` at `x⁰` and `c` at
`xⁿ` for `n ≥ 1`, i.e. `L(H) = b + c/(1−x)` coefficient-wise. -/
lemma ZagierH_odeLHS_coeff (a b c : ℚ) (n : ℕ) :
    PowerSeries.coeff n (HA_odeLHS (ZagierH a b c)) = if n = 0 then b + c else c := by
  rw [ZagierH_eq_mk]
  have hc0 : ZagierH_coeff_seq a b c 1 - 3 * ZagierH_coeff_seq a b c 0 = b + c := by
    unfold ZagierH_coeff_seq
    rw [HA_coeff_zero, HA_coeff_one, HB_coeff_zero, HB_coeff_one, HC_coeff_zero, HC_coeff_one]
    ring
  have hrec : ∀ n : ℕ, 1 ≤ n →
      ((n + 1 : ℕ) : ℚ) ^ 2 * ZagierH_coeff_seq a b c (n + 1)
        - (((10 : ℚ) * (n : ℚ) ^ 2 + 10 * (n : ℚ) + 3) * ZagierH_coeff_seq a b c n)
        + (9 : ℚ) * (n : ℚ) ^ 2 * ZagierH_coeff_seq a b c (n - 1) = c := by
    intro n hn
    unfold ZagierH_coeff_seq
    have hA := HA_coeff_recurrence_zero n hn
    have hB := HB_coeff_recurrence n hn
    have hC := HC_coeff_recurrence n hn
    calc
      ((n + 1 : ℕ) : ℚ) ^ 2 * (a * HA_coeff (n + 1) + b * HB_coeff (n + 1) + c * HC_coeff (n + 1))
        - (((10 : ℚ) * (n : ℚ) ^ 2 + 10 * (n : ℚ) + 3) *
            (a * HA_coeff n + b * HB_coeff n + c * HC_coeff n))
        + (9 : ℚ) * (n : ℚ) ^ 2 * (a * HA_coeff (n - 1) + b * HB_coeff (n - 1) + c * HC_coeff (n - 1))
          = a * (((n + 1 : ℕ) : ℚ) ^ 2 * HA_coeff (n + 1)
              - (((10 : ℚ) * (n : ℚ) ^ 2 + 10 * (n : ℚ) + 3) * HA_coeff n)
              + (9 : ℚ) * (n : ℚ) ^ 2 * HA_coeff (n - 1))
            + b * (((n + 1 : ℕ) : ℚ) ^ 2 * HB_coeff (n + 1)
              - (((10 : ℚ) * (n : ℚ) ^ 2 + 10 * (n : ℚ) + 3) * HB_coeff n)
              + (9 : ℚ) * (n : ℚ) ^ 2 * HB_coeff (n - 1))
            + c * (((n + 1 : ℕ) : ℚ) ^ 2 * HC_coeff (n + 1)
              - (((10 : ℚ) * (n : ℚ) ^ 2 + 10 * (n : ℚ) + 3) * HC_coeff n)
              + (9 : ℚ) * (n : ℚ) ^ 2 * HC_coeff (n - 1)) := by ring
      _ = c := by rw [hA, hB, hC]; ring
  have hg := HA_odeLHS_coeff_eq (ZagierH_coeff_seq a b c) (b + c) c hc0 hrec n
  exact hg

/-- coefficients of the RHS `b + c/(1−x)` of the `functionsH` ODE -/
lemma coeff_functionsH_rhs (b c : ℚ) (n : ℕ) :
    PowerSeries.coeff n (C b + C c * (((1 : PowerSeries ℚ) - X)⁻¹)) = if n = 0 then b + c else c := by
  by_cases hn : n = 0
  · subst n
    simp only [map_add, coeff_C_mul]
    rw [coeff_inv_one_sub_eq_one]
    simp
  · rw [if_neg hn]
    have hb0 : PowerSeries.coeff n (C b) = 0 := by
      cases n with
      | zero => exact False.elim (hn rfl)
      | succ m => simp
    simp only [map_add, coeff_C_mul]
    rw [hb0, coeff_inv_one_sub_eq_one]
    ring

/-- Proposition `functionsH` of arXiv:2408.15403 (algebraic half): the
function `H(x) = a·H_A(x) + b·H_B(x) + c·H_C(x)` satisfies
`x(1−x)(1−9x)H'' + (1−20x+27x²)H' + 3(−1+3x)H = b + c/(1−x)`. -/
theorem functionsH_ode (a b c : ℚ) :
    HA_odeLHS (ZagierH a b c) = C b + C c * ((1 : PowerSeries ℚ) - X)⁻¹ := by
  apply PowerSeries.ext
  intro n
  rw [ZagierH_odeLHS_coeff, coeff_functionsH_rhs]


/-! ## `G(y) = Sym⁺(a·H_A + b·H_B + c·H_C) = a·G_A + b·Sym⁺H_B + c·Sym⁺H_C`

The `G(y)` of the paper's proof of Theorem `mainA` is the symmetrization
of the `H(x)` of Proposition `functionsH` (`defH`): under the absurd
`ℚ`-dependence `a + b·L(2,χ)/2 + c·ζ(2)/4 = 0` one forms
`H = aH_A + bH_B + cH_C ∈ ℚ⟦x⟧` (with rational coefficients `a,b,c`, so
`H ∈ ℚ⟦x⟧` by `ZagierH_coeff`) and `G(y) = Sym⁺H`.  `Sym⁺` is `ℚ`-linear
(`sympSym_add`, `sympSym_C_mul`, module `SympDescent`), so `G` decomposes
into the symmetrizations of the three building blocks — in particular, with
`a,b,c` rational, `Sym⁺(ZagierH a b c) ∈ ℚ⟦y⟧` is an explicit `ℚ`-linear
combination of `G_A = Sym⁺H_A`, `Sym⁺H_B`, `Sym⁺H_C`.  (The paper's
denominator-type and holonomy analysis applies to this specific `G`; the
`G_A` part is integrally pinned in `SympZagier` (`sympSym_HA_IntSeries`,
descent coefficients `g₀..g₁₁`).)
-/

/-- `Sym⁺(a·H_A + b·H_B + c·H_C) = a·G_A + b·Sym⁺H_B + c·Sym⁺H_C` — the
symmetrization of the `functionsH`-combination is the `ℚ`-linear
combination of the symmetrizations (paper `defH`/`defG`) -/
lemma sympSym_ZagierH (a b c : ℚ) :
    sympSym (ZagierH a b c) =
      PowerSeries.C a * sympSym HA + PowerSeries.C b * sympSym HB
        + PowerSeries.C c * sympSym HC := by
  unfold ZagierH
  rw [sympSym_add, sympSym_C_mul]
  rw [sympSym_add, sympSym_C_mul, sympSym_C_mul]

end Submission.CDT
