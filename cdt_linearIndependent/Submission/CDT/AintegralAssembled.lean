import Mathlib
import Submission.CDT.Aintegral
import Submission.CDT.ZagierH
import Submission.CDT.ZagierHBC
import Submission.Commons.Analysis.Differential.ode_pullback_mobius
import Submission.Commons.RingTheory.PowerSeries.ode_78_coeff
import Submission.Commons.Analysis.Integral.doubleIntegral_zetaJ_one

/-!
# Assembled `(Aintegral)`: the ζ-side Beukers identity `ζ(2)·G_A − 4·G_C = Σ (−1)ⁿIₙxⁿ`

This module closes the paper's display `(Aintegral)`
(arXiv:2408.15403, Remark `euler rep`)

```lean
ζ(2)·G_A(x) − 4·G_C(x) = Σₙ xⁿ·(−1)ⁿ·∫₀¹∫₀¹ (1−s²)ⁿ(1−t²)ⁿ/(1−st)^{n+1} ds dt
```

where `G_A = mobTrans H_A`, `G_C = mobTrans H_C` are the Möbius transforms
of the paper's `(Gs)` display (`Submission.CDT.Aintegral`).

## The route

The paper proves the identity by "evaluating the geometric series"; here it
is assembled from four independent bricks:

1. **the Möbius pullback of the ODE** (commons
   `Commons.Analysis.Differential.ode_pullback_mobius`, fleet L137): if `f`
   satisfies `x(1−x)(1−9x)f'' + (1−20x+27x²)f' + 3(3x−1)f = 0`, then its
   gauge-Möbius transform `G(x) = f(x/(1+x))/(1+x)` satisfies the
   `(7,−8,2)`-operator
   `x(1−8x)(1+x)G'' + (1−14x−24x²)G' − 2(1+4x)G = 0`.
   Applied to `H_A` (`HA_ode`) this gives `ODE78 G_A = 0`; applied through
   the *mode* form `ode_subst_mobPsi_L_mode` to `H_C` (`HC_ode`, whose RHS
   is `1/(1−x)`) it gives `ODE78 G_C = 1`;
2. **coefficient extraction** (commons
   `Commons.RingTheory.PowerSeries.ode_78_coeff`, fleet L144): the `xⁿ`
   coefficient of the `(7,−8,2)`-operator applied to `G` is
   `(n+1)²g_{n+1} − (7n²+7n+2)gₙ − 8n²g_{n−1}`.  Hence both coefficient
   streams satisfy the paper's recurrence
   `(n+1)²g_{n+1} = (7n²+7n+2)gₙ + 8n²g_{n−1}` (`G_A` for all `n`, `G_C`
   for `n ≥ 1`; `G_C`'s `n = 0` instance is `c₁ − 2c₀ = 1`), with
   `g₀ = 1, g₁ = 2` for `G_A` (Zagier's sequence **A** = Franel numbers
   `1,2,10,56,…`) and `c₀ = 0, c₁ = 1` for `G_C` (`0,1,4,208/9,…`);
3. **the ζ-side recurrence for the integrals**: `Iₙ` satisfies the same
   `(7,−8,2)` recurrence (`zetaJ_recurrence`, PROVED from the commons
   `zetaintegral_recurrence_parametric`), so `Kₙ = (−1)ⁿIₙ` satisfies the
   recurrence with the *plus* signs (`zetaJK_recurrence`);
4. **the two initial values**: `n = 0` is `I₀ = ζ(2)` (`zetaJ_zero_eq`) and
   `n = 1` is the elementary integral evaluation
   `I₁ = ∫₀¹∫₀¹ (1−s²)(1−t²)/(1−st)² = 4 − 2ζ(2)` (commons
   `doubleIntegral_zetaJ_one`, fleet L141), whose proof expands
   `1/(1−st)² = Σ(k+1)(st)^k`, integrates termwise, and evaluates
   `Σ_k 4/((k+1)(k+3)²) = 4 − 2ζ(2)`.

Since a second-order recurrence together with `n = 0, 1` determines a
sequence, two-step induction gives **`AintegralIdentity`** for all `n`:

```lean
zeta2Real·[xⁿ]G_A − 4·[xⁿ]G_C = (−1)ⁿ·Iₙ .
```

Consequently, with the kernel bound `|Iₙ| ≤ ζ(2)` (`zetaJ_bound`), the
Möbius-transformed difference `G_C − (ζ(2)/4)G_A` overconverges to radius
`≥ 1` (`overconvergesCtr_proved`) — the ζ-side mirror of
`overconvergesB_proved` of `Submission.CDT.CintegralAssembled`.
-/

open PowerSeries
open scoped BigOperators

noncomputable section

namespace Submission.CDT

open Commons.Analysis.Differential (ode_pb_M ode_pb_L ode_mobPsi ode_pullback_mobius
  ode_subst_mobPsi_L_mode ode_mobPsi_subst_injective ode_subst_one)

/-! ## The `(7,−8,2)` operator kills the Möbius pullbacks -/

/-- `C 9 = C 3 · C 3` in `ℚ⟦X⟧` -/
lemma C_three_sq : (PowerSeries.C 3 : PowerSeries ℚ) ^ 2 = PowerSeries.C 9 := by
  have h : (3 : ℚ) ^ 2 = 9 := by norm_num
  rw [← h, map_pow]

/-- `C 10 = C 9 + 1` in `ℚ⟦X⟧` -/
lemma C_ten_eq : (PowerSeries.C (10 : ℚ) : PowerSeries ℚ) = PowerSeries.C 9 + 1 := by
  have h : (10 : ℚ) = 9 + 1 := by norm_num
  rw [h, map_add, map_one]

/-- `HA_odeLHS` in the factored form used by
`Commons.Analysis.Differential.ode_pullback_mobius` -/
lemma HA_odeLHS_eq (y : PowerSeries ℚ) :
    HA_odeLHS y
      = PowerSeries.X * (1 - PowerSeries.X) * (1 - PowerSeries.C 9 * PowerSeries.X)
            * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) y)
          + (1 - PowerSeries.C 20 * PowerSeries.X + PowerSeries.C 27 * PowerSeries.X ^ 2)
            * (PowerSeries.derivative (R := ℚ)) y
          + PowerSeries.C 3 * (PowerSeries.C 3 * PowerSeries.X - 1) * y := by
  unfold HA_odeLHS
  rw [C_ten_eq]
  ring_nf
  rw [C_three_sq]
  ring

/-- the commons operator `ode_pb_L` is `HA_odeLHS` -/
lemma ode_pb_L_eq (y : PowerSeries ℚ) : ode_pb_L y = HA_odeLHS y := by
  rw [HA_odeLHS_eq]
  unfold ode_pb_L
  simp only [Commons.Analysis.Differential.ode_a2, Commons.Analysis.Differential.ode_a1,
    Commons.Analysis.Differential.ode_a0, map_ofNat]

/-- **the transformed Hauptmodul series is a solution of the `(7,−8,2)`
operator**: the Möbius pullback of `HA_ode` -/
lemma GAtr_ode78 : ode_pb_M GAtr = 0 := by
  have hL : PowerSeries.X * (1 - PowerSeries.X) * (1 - PowerSeries.C 9 * PowerSeries.X)
        * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) HA)
      + (1 - PowerSeries.C 20 * PowerSeries.X + PowerSeries.C 27 * PowerSeries.X ^ 2)
        * (PowerSeries.derivative (R := ℚ)) HA
      + PowerSeries.C 3 * (PowerSeries.C 3 * PowerSeries.X - 1) * HA = 0 := by
    rw [← HA_odeLHS_eq]; exact HA_ode
  have h := ode_pullback_mobius HA hL
  unfold GAtr mobTrans mobPhi ode_pb_M
  exact h

/-- the Möbius pullback of `HC_ode`, transported back through the (injective)
substitution `ψ = x/(1−x)`: the operator sends `G_C` to `1` -/
lemma subst_mobPsi_ode_pb_M_GCtr :
    PowerSeries.subst ode_mobPsi (ode_pb_M GCtr) = 1 := by
  have h := ode_subst_mobPsi_L_mode HC
  have h1 : PowerSeries.subst ode_mobPsi (ode_pb_M GCtr)
      = (1 - PowerSeries.X) * ode_pb_L HC := h
  rw [ode_pb_L_eq HC, HC_ode] at h1
  rw [PowerSeries.mul_inv_cancel ((1 : PowerSeries ℚ) - PowerSeries.X) (by simp)] at h1
  exact h1

/-- **`G_C` is a solution of the inhomogeneous `(7,−8,2)` operator** with
constant right-hand side `1` (equivalently: `G_C` satisfies the paper's
`(7,−8,2)` recurrence for `n ≥ 1`, with `c₁ − 2c₀ = 1` at `n = 0`) -/
lemma GCtr_ode78 : ode_pb_M GCtr = 1 :=
  ode_mobPsi_subst_injective (by rw [subst_mobPsi_ode_pb_M_GCtr, ode_subst_one])

/-! ## The `(7,−8,2)` coefficient recurrences -/

/-- **the `(7,−8,2)` coefficient recurrence for the transformed Hauptmodul
series** `G_A` (Zagier's sequence **A** = Franel numbers `1,2,10,56,…`),
for all `n` (with the convention `g_{−1} = 0`) -/
lemma GAtr_coeff_recurrence (n : ℕ) :
    (((n + 1 : ℕ)) : ℚ) ^ 2 * GAtr.coeff (n + 1)
      = (7 * (n : ℚ) ^ 2 + 7 * (n : ℚ) + 2) * GAtr.coeff n
        + 8 * (n : ℚ) ^ 2 * GAtr.coeff (n - 1) := by
  have h := Commons.RingTheory.PowerSeries.ode_78_coeff GAtr n
  have hz : PowerSeries.coeff n
      (PowerSeries.X * (1 - 8 * PowerSeries.X) * (1 + PowerSeries.X)
          * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) GAtr)
        + (1 - 14 * PowerSeries.X - 24 * PowerSeries.X ^ 2)
          * PowerSeries.derivative (R := ℚ) GAtr
        + (-2 - 8 * PowerSeries.X) * GAtr) = 0 := by
    have h0 : PowerSeries.coeff n (ode_pb_M GAtr) = 0 := by rw [GAtr_ode78]; rfl
    exact h0
  have hzero : ((n + 1 : ℕ) : ℚ) ^ 2 * GAtr.coeff (n + 1)
      - (7 * (n : ℚ) ^ 2 + 7 * (n : ℚ) + 2) * GAtr.coeff n
      - 8 * (n : ℚ) ^ 2 * GAtr.coeff (n - 1) = 0 := h.symm.trans hz
  linarith

/-- **the `(7,−8,2)` coefficient recurrence for the transformed companion
series** `G_C = 0 + x + 4x² + (208/9)x³ + …`, for `n ≥ 1` -/
lemma GCtr_coeff_recurrence (n : ℕ) (hn : 1 ≤ n) :
    (((n + 1 : ℕ)) : ℚ) ^ 2 * GCtr.coeff (n + 1)
      = (7 * (n : ℚ) ^ 2 + 7 * (n : ℚ) + 2) * GCtr.coeff n
        + 8 * (n : ℚ) ^ 2 * GCtr.coeff (n - 1) := by
  have h := Commons.RingTheory.PowerSeries.ode_78_coeff GCtr n
  have hz : PowerSeries.coeff n
      (PowerSeries.X * (1 - 8 * PowerSeries.X) * (1 + PowerSeries.X)
          * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) GCtr)
        + (1 - 14 * PowerSeries.X - 24 * PowerSeries.X ^ 2)
          * PowerSeries.derivative (R := ℚ) GCtr
        + (-2 - 8 * PowerSeries.X) * GCtr) = 0 := by
    have h0 : PowerSeries.coeff n (ode_pb_M GCtr) = PowerSeries.coeff n (1 : PowerSeries ℚ) := by
      rw [GCtr_ode78]
    have h1 : PowerSeries.coeff n (1 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_one, if_neg (by omega : ¬ (n = 0))]
    exact h0.trans h1
  have hzero : ((n + 1 : ℕ) : ℚ) ^ 2 * GCtr.coeff (n + 1)
      - (7 * (n : ℚ) ^ 2 + 7 * (n : ℚ) + 2) * GCtr.coeff n
      - 8 * (n : ℚ) ^ 2 * GCtr.coeff (n - 1) = 0 := h.symm.trans hz
  linarith

/-- first coefficient of `G_A`: `g₁ = 2` (the `n = 0` instance of the
recurrence, `g₁ = 2g₀`) -/
lemma GAtr_coeff_one : GAtr.coeff 1 = 2 := by
  have h := GAtr_coeff_recurrence 0
  rw [GAtr_coeff_zero] at h
  norm_num at h
  linarith

/-- first coefficient of `G_C`: `c₁ = 2c₀ + 1 = 1` (the `n = 0` instance of
`GCtr_ode78`) -/
lemma GCtr_coeff_one : GCtr.coeff 1 = 1 := by
  have h := Commons.RingTheory.PowerSeries.ode_78_coeff GCtr 0
  have hz : PowerSeries.coeff 0
      (PowerSeries.X * (1 - 8 * PowerSeries.X) * (1 + PowerSeries.X)
          * PowerSeries.derivative (R := ℚ) (PowerSeries.derivative (R := ℚ) GCtr)
        + (1 - 14 * PowerSeries.X - 24 * PowerSeries.X ^ 2)
          * PowerSeries.derivative (R := ℚ) GCtr
        + (-2 - 8 * PowerSeries.X) * GCtr) = 1 := by
    have h0 : PowerSeries.coeff 0 (ode_pb_M GCtr) = PowerSeries.coeff 0 (1 : PowerSeries ℚ) := by
      rw [GCtr_ode78]
    have h1 : PowerSeries.coeff 0 (1 : PowerSeries ℚ) = 1 := by simp
    exact h0.trans h1
  rw [hz] at h
  rw [GCtr_coeff_zero] at h
  norm_num at h
  linarith

/-! ## The two initial values of the integral sequence -/

/-- the shifted ζ-series is `zeta2Real` -/
lemma tsum_succ_eq : (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2) = zeta2Real := by
  have hsum : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
  have hsh := hsum.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), div_zero, zero_add] at hsh
  have h' : (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)
      = ∑' n : ℕ, (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 2) (n + 1) := by
    apply tsum_congr
    intro n
    push_cast
    ring
  rw [h', zeta2Real]
  exact hsh

/-- **the `n = 1` value of the `(Aintegral)` integral**:
`I₁ = ∫₀¹∫₀¹ (1−s²)(1−t²)/(1−st)² = 4 − 2ζ(2)` (commons
`doubleIntegral_zetaJ_one`) -/
lemma zetaJ_one_eq : zetaJ 1 = 4 - 2 * zeta2Real := by
  have hfun : (fun s : ℝ => ∫ t in (0 : ℝ)..1, zetaKernel 1 s t)
      = (fun s : ℝ => ∫ t in (0 : ℝ)..1,
          (1 - s ^ 2) * (1 - t ^ 2) / (1 - s * t) ^ 2) := by
    funext s
    apply intervalIntegral.integral_congr
    intro t ht
    simp [zetaKernel]
  rw [zetaJ, hfun, Commons.Analysis.Integral.doubleIntegral_zetaJ_one, tsum_succ_eq]

/-! ## The recurrence for the signed integrals and the induction -/

/-- **the signed integrals `Kₙ = (−1)ⁿIₙ` satisfy the `(7,−8,2)` recurrence**
with the same (plus) signs as `G_A`/`G_C` -/
lemma zetaJK_recurrence (n : ℕ) (hn : 1 ≤ n) :
    (((n + 1 : ℕ)) : ℝ) ^ 2 * ((-1 : ℝ) ^ (n + 1) * zetaJ (n + 1))
      = (7 * (n : ℝ) ^ 2 + 7 * (n : ℝ) + 2) * ((-1 : ℝ) ^ n * zetaJ n)
        + 8 * (n : ℝ) ^ 2 * ((-1 : ℝ) ^ (n - 1) * zetaJ (n - 1)) := by
  have h := zetaJ_recurrence n hn
  have hs : (-1 : ℝ) ^ (n + 1) = -((-1 : ℝ) ^ n) := by rw [pow_succ]; ring
  have hs2 : (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ (n - 1) := by
    rw [show n + 1 = n - 1 + 2 by omega, pow_add]; norm_num
  have h1 : (-1 : ℝ) ^ (n + 1)
        * (-(7 * (n : ℝ) ^ 2 + 7 * (n : ℝ) + 2) * zetaJ n)
      = (7 * (n : ℝ) ^ 2 + 7 * (n : ℝ) + 2) * ((-1 : ℝ) ^ n * zetaJ n) := by
    rw [hs]; ring
  have h2 : (-1 : ℝ) ^ (n + 1) * (8 * (n : ℝ) ^ 2 * zetaJ (n - 1))
      = 8 * (n : ℝ) ^ 2 * ((-1 : ℝ) ^ (n - 1) * zetaJ (n - 1)) := by
    rw [hs2]; ring
  have h4 : (-1 : ℝ) ^ (n + 1) * ((((n + 1 : ℕ)) : ℝ) ^ 2 * zetaJ (n + 1))
      = (((n + 1 : ℕ)) : ℝ) ^ 2 * ((-1 : ℝ) ^ (n + 1) * zetaJ (n + 1)) := by ring
  have h3 := congrArg (fun x : ℝ => (-1 : ℝ) ^ (n + 1) * x) h
  rw [h4, mul_add, h1, h2] at h3
  exact h3

/-- the `(7,−8,2)` recurrence for the (real) coefficients of `G_A` -/
lemma GAtr_coeff_recurrence_real (n : ℕ) :
    (((n + 1 : ℕ)) : ℝ) ^ 2 * ((GAtr.coeff (n + 1) : ℚ) : ℝ)
      = (7 * (n : ℝ) ^ 2 + 7 * (n : ℝ) + 2) * ((GAtr.coeff n : ℚ) : ℝ)
        + 8 * (n : ℝ) ^ 2 * ((GAtr.coeff (n - 1) : ℚ) : ℝ) := by
  have h := congrArg (fun z : ℚ => (z : ℝ)) (GAtr_coeff_recurrence n)
  push_cast at h
  rw [show (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 by push_cast; ring]
  exact h

/-- the `(7,−8,2)` recurrence for the (real) coefficients of `G_C` -/
lemma GCtr_coeff_recurrence_real (n : ℕ) (hn : 1 ≤ n) :
    (((n + 1 : ℕ)) : ℝ) ^ 2 * ((GCtr.coeff (n + 1) : ℚ) : ℝ)
      = (7 * (n : ℝ) ^ 2 + 7 * (n : ℝ) + 2) * ((GCtr.coeff n : ℚ) : ℝ)
        + 8 * (n : ℝ) ^ 2 * ((GCtr.coeff (n - 1) : ℚ) : ℝ) := by
  have h := congrArg (fun z : ℚ => (z : ℝ)) (GCtr_coeff_recurrence n hn)
  push_cast at h
  rw [show (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 by push_cast; ring]
  exact h

/-- **the paper's `(Aintegral)` identity is PROVED, for every `n`**:
`ζ(2)·[xⁿ]G_A − 4·[xⁿ]G_C = (−1)ⁿ·Iₙ` -/
theorem AintegralIdentity_proved : AintegralIdentity := by
  have key : ∀ n : ℕ, zeta2Real * ((GAtr.coeff n : ℚ) : ℝ)
      - 4 * ((GCtr.coeff n : ℚ) : ℝ) = (-1 : ℝ) ^ n * zetaJ n := by
    apply Nat.twoStepInduction
    · rw [GAtr_coeff_zero, GCtr_coeff_zero, zetaJ_zero_eq]
      norm_num
    · rw [GAtr_coeff_one, GCtr_coeff_one, zetaJ_one_eq]
      norm_num
      ring
    · intro n ih0 ih1
      have hm : 1 ≤ n + 1 := by omega
      have hA := GAtr_coeff_recurrence_real (n + 1)
      have hC := GCtr_coeff_recurrence_real (n + 1) hm
      have hK := zetaJK_recurrence (n + 1) hm
      simp only [show n + 1 + 1 = n + 2 by omega, show n + 1 - 1 = n by omega] at hA hC hK
      have hc : (((n + 2 : ℕ)) : ℝ) ^ 2 ≠ 0 := by positivity
      have hmain : (((n + 2 : ℕ)) : ℝ) ^ 2
            * (zeta2Real * ((GAtr.coeff (n + 2) : ℚ) : ℝ)
                - 4 * ((GCtr.coeff (n + 2) : ℚ) : ℝ))
          = (((n + 2 : ℕ)) : ℝ) ^ 2 * ((-1 : ℝ) ^ (n + 2) * zetaJ (n + 2)) := by
        linear_combination (zeta2Real) * hA - 4 * hC - hK
          + (7 * (((n + 1 : ℕ)) : ℝ) ^ 2 + 7 * (((n + 1 : ℕ)) : ℝ) + 2) * ih1
          + (8 * (((n + 1 : ℕ)) : ℝ) ^ 2) * ih0
      exact mul_left_cancel₀ hc hmain
  intro n
  unfold AintegralIdentityAt
  exact key n

/-- **the ζ-side overconvergence is PROVED** (unconditionally): the
Möbius-transformed difference `G_C − (ζ(2)/4)·G_A` has radius of convergence
`≥ 1` — the ζ-side mirror of `overconvergesB_proved` -/
theorem overconvergesCtr_proved :
    OverconvergesUnit (fun n : ℕ =>
      ((GCtr.coeff n : ℚ) : ℝ) - (zeta2Real / 4) * ((GAtr.coeff n : ℚ) : ℝ)) :=
  overconvergesCtr_of_aintegral AintegralIdentity_proved zetaJ_bound

end Submission.CDT
