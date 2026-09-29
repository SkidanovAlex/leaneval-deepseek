import Mathlib
import Submission.CDT.Aintegral
import Submission.CDT.AintegralAssembled
import Submission.CDT.EichlerInput
import Submission.CDT.CintegralAssembled
import Submission.Commons.RingTheory.PowerSeries.coeff_mobiusTransformInv
import Submission.Commons.Analysis.Integral.doubleIntegral_Bkernel_binom
import Submission.Commons.Analysis.Integral.doubleIntegral_Bkernel_bound

/-!
# The *untransformed* ζ-side overconvergence: `H_C − (ζ(2)/4)H_A` has radius `≥ 1`

The paper's Lemma `defabc`(iii) (arXiv:2408.15403) claims that — although
`H_A, H_B, H_C` each have radius of convergence `1/9` — the two combinations

```lean
H_B(x) − (L(2,χ₋₃)/2)·H_A(x),      H_C(x) − (ζ(2)/4)·H_A(x)
```

both have radius of convergence `1`.  For `H_B` this is the analytic half of
`EichlerInputB`, supplied by the `(Cintegral)` display
(`Submission.CDT.CintegralAssembled.overconvergesB_proved`).  This module
proves the **`H_C` half** — `OverconvergesUnit eichlerDiffC` — hence reduces
`EichlerInputC` to its modular `[1..n]²`-integrality conjunct alone
(`eichlerInputC_of_modular` below).

## The route

The `(Aintegral)` display (cf. `Submission.CDT.Aintegral`) is stated in the
*Möbius-transformed* variables `G_A, G_C`; its
radius-`≥1` consequence for the transformed difference does **not** give the
untransformed claim (the inverse transform of a radius-`≥1` series only has
radius `≥ 1/2`).  The correct route is the *inverse* (binomial) transform of
the integral representation, which produces a *new* double integral with a
pointwise bounded kernel:

* the inverse Möbius transform `F ↦ (1−y)⁻¹F(y/(1−y))` inverts
  `mobTrans` (`mobTrans_inv`), so with the commons
  `Commons.RingTheory.PowerSeries.coeff_mobiusTransformInv`, the coefficients
  of `H_A`, `H_C` are the binomial transforms of those of `G_A`, `G_C`
  (`HA_coeff_eq_btSum`, `HC_coeff_eq_btSum`):
  `aₙ = Σₖ C(n,k)·[xᵏ]G_A`, `cₙ = Σₖ C(n,k)·[xᵏ]G_C`;
* feeding in the **proved** `(Aintegral)` identity
  (`AintegralIdentity_proved`, `Submission.CDT.AintegralAssembled`)
  `ζ(2)·[xᵏ]G_A − 4·[xᵏ]G_C = (−1)ᵏ·Iₖ` gives
  `eichlerDiffC n = −(1/4)·Σₖ C(n,k)(−1)ᵏIₖ`;
* the binomial theorem expands the *new* kernel
  `B(s,t) := (1−st) − (1−s²)(1−t²) = s² + t² − st − s²t²`:
  `Bⁿ = Σₖ C(n,k)(1−st)^{n−k}(−1)ᵏ(1−s²)ᵏ(1−t²)ᵏ`, so that termwise
  integration (a *finite* sum — no interchange needed) gives

  ```lean
  Jₙ := ∫₀¹∫₀¹ B(s,t)ⁿ/(1−st)^{n+1} ds dt = Σₖ C(n,k)(−1)ᵏ Iₖ
  ```
  (`zetaBJ_eq_binom`, from the commons `doubleIntegral_Bkernel_binom`, fleet
  L152), hence `eichlerDiffC n = −(1/4)·Jₙ`;
* finally `0 ≤ B(s,t) ≤ 1 − st` on the unit square gives the **uniform**
  pointwise bound `|Bⁿ/(1−st)^{n+1}| ≤ 1/(1−st)`, so

  ```lean
  |Jₙ| ≤ ∫₀¹∫₀¹ ds dt/(1−st) = ζ(2)
  ```
  (`zetaBJ_bound`), i.e. the untransformed difference has *bounded*
  coefficients: `|eichlerDiffC n| ≤ ζ(2)/4`, which is more than the
  subexponential growth `OverconvergesUnit` asks for.
-/

open PowerSeries
open scoped BigOperators

noncomputable section

namespace Submission.CDT

open Commons.Analysis.Differential (ode_mobPsi ode_mobPsi_hasSubst ode_subst_mobPsi_mobPhi
  ode_subst_mobPsi_X_add_one_inv ode_mobPhi ode_mobPhi_hasSubst)

/-! ## The inverse Möbius transform and the binomial transform of the coefficients -/

/-- **the inverse Möbius transform**: the map `F ↦ (1−y)⁻¹·F(y/(1−y))` inverts
`mobTrans f = (1/(1+x))·f(x/(1+x))` -/
lemma mobTrans_inv (f : PowerSeries ℚ) :
    ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹
      * (mobTrans f).subst (PowerSeries.X * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹) = f := by
  have h1 : PowerSeries.X * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ = ode_mobPsi := rfl
  have h2 : mobPhi = ode_mobPhi := rfl
  rw [h1]
  unfold mobTrans
  rw [h2, PowerSeries.subst_mul ode_mobPsi_hasSubst, ode_subst_mobPsi_X_add_one_inv]
  rw [PowerSeries.subst_comp_subst_apply ode_mobPhi_hasSubst ode_mobPsi_hasSubst,
    ode_subst_mobPsi_mobPhi, PowerSeries.X_subst]
  rw [← mul_assoc,
    PowerSeries.inv_mul_cancel ((1 : PowerSeries ℚ) - PowerSeries.X) (by simp), one_mul]

/-- the inverse transform of `G_A` is `H_A` -/
lemma inv_mobTrans_GAtr :
    ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹
      * GAtr.subst (PowerSeries.X * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹) = HA := by
  have := mobTrans_inv HA
  simpa only [GAtr] using this

/-- the inverse transform of `G_C` is `H_C` -/
lemma inv_mobTrans_GCtr :
    ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹
      * GCtr.subst (PowerSeries.X * ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹) = HC := by
  have := mobTrans_inv HC
  simpa only [GCtr] using this

/-- **binomial transform of `G_A`'s coefficients**: `aₙ = Σₖ C(n,k)·[xᵏ]G_A` -/
lemma HA_coeff_eq_btSum (n : ℕ) :
    (HA_coeff n : ℝ)
      = ∑ k ∈ Finset.range (n + 1),
          ((GAtr.coeff k : ℚ) : ℝ) * ((Nat.choose n k : ℕ) : ℝ) := by
  have h := Commons.RingTheory.PowerSeries.coeff_mobiusTransformInv GAtr n
  rw [inv_mobTrans_GAtr, coeff_HA] at h
  have h' := congrArg (fun z : ℚ => (z : ℝ)) h
  push_cast at h'
  exact h'

/-- **binomial transform of `G_C`'s coefficients**: `cₙ = Σₖ C(n,k)·[xᵏ]G_C` -/
lemma HC_coeff_eq_btSum (n : ℕ) :
    (HC_coeff n : ℝ)
      = ∑ k ∈ Finset.range (n + 1),
          ((GCtr.coeff k : ℚ) : ℝ) * ((Nat.choose n k : ℕ) : ℝ) := by
  have h := Commons.RingTheory.PowerSeries.coeff_mobiusTransformInv GCtr n
  rw [inv_mobTrans_GCtr, coeff_HC] at h
  have h' := congrArg (fun z : ℚ => (z : ℝ)) h
  push_cast at h'
  exact h'

/-! ## The auxiliary kernel `B(s,t) = (1−st) − (1−s²)(1−t²)` and its integrals -/

/-- the auxiliary kernel `B(s,t) = (1−st) − (1−s²)(1−t²) = s²+t²−st−s²t²` -/
def bKernel (s t : ℝ) : ℝ := (1 - s * t) - (1 - s ^ 2) * (1 - t ^ 2)

/-- `s² + t² − st − s²t² = (1−st) − (1−s²)(1−t²)` -/
lemma bKernel_eq (s t : ℝ) : bKernel s t = s ^ 2 + t ^ 2 - s * t - s ^ 2 * t ^ 2 := by
  unfold bKernel; ring

/-- `0 ≤ B` on the unit square (it is `(1−st) − (1−s²)(1−t²)`) -/
lemma bKernel_nonneg {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ bKernel s t := by
  have hst0 : 0 ≤ s * t := mul_nonneg hs0 ht0
  have hst1 : s * t ≤ 1 := by nlinarith
  have h1 : (1 - s * t) ^ 2 ≤ 1 - s * t := by nlinarith
  have h2 : (1 - s ^ 2) * (1 - t ^ 2) ≤ (1 - s * t) ^ 2 := one_sub_sq_mul_le s t
  unfold bKernel
  linarith

/-- `B ≤ 1 − st` on the unit square -/
lemma bKernel_le_one_sub_mul {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    bKernel s t ≤ 1 - s * t := by
  have h1 : 0 ≤ 1 - s ^ 2 := by nlinarith
  have h2 : 0 ≤ 1 - t ^ 2 := by nlinarith
  have h : 0 ≤ (1 - s ^ 2) * (1 - t ^ 2) := mul_nonneg h1 h2
  unfold bKernel
  linarith

/-- the `B`-double integrals `Jₙ = ∫₀¹∫₀¹ B(s,t)ⁿ/(1−st)^{n+1}` -/
def zetaBJ (n : ℕ) : ℝ :=
  ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
    bKernel s t ^ n / (1 - s * t) ^ (n + 1)

/-- **the binomial identity for the `B`-integrals**: termwise integration of
`Bⁿ = Σₖ C(n,k)(1−st)^{n−k}(−1)ᵏ(1−s²)ᵏ(1−t²)ᵏ` gives
`Jₙ = Σₖ C(n,k)(−1)ᵏ·Iₖ` -/
lemma zetaBJ_eq_binom (n : ℕ) :
    zetaBJ n = ∑ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℝ) * (-1) ^ k * zetaJ k := by
  have h := Commons.Analysis.Integral.doubleIntegral_Bkernel_binom n
  have hL : zetaBJ n
      = ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
          (((1 - s * t) - (1 - s ^ 2) * (1 - t ^ 2)) ^ n / (1 - s * t) ^ (n + 1)) := rfl
  rw [hL, h]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [zetaJ, zetaKernel]

/-! ## The untransformed difference is `−Jₙ/4` -/

/-- **the untransformed ζ-side difference is `−Jₙ/4`**:
`cₙ − (ζ(2)/4)aₙ = −(1/4)·Jₙ`, where `Jₙ = ∫₀¹∫₀¹ Bⁿ/(1−st)^{n+1}` -/
lemma eichlerDiffC_eq (n : ℕ) : eichlerDiffC n = -(1 / 4) * zetaBJ n := by
  rw [eichlerDiffC, HA_coeff_eq_btSum, HC_coeff_eq_btSum, zetaBJ_eq_binom]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : zeta2Real * ((GAtr.coeff k : ℚ) : ℝ) - 4 * ((GCtr.coeff k : ℚ) : ℝ)
      = (-1 : ℝ) ^ k * zetaJ k := AintegralIdentity_proved k
  linear_combination (-(((Nat.choose n k : ℕ) : ℝ) / 4)) * hk

/-! ## The overconvergence of the untransformed ζ-side difference -/

/-- **`Jₙ` is uniformly bounded**: `|Jₙ| ≤ ζ(2)`, from the pointwise bound
`|Bⁿ/(1−st)^{n+1}| ≤ 1/(1−st)` and `∫₀¹∫₀¹ds dt/(1−st) = ζ(2)` -/
lemma zetaBJ_bound (n : ℕ) : |zetaBJ n| ≤ zeta2Real := by
  have h := Commons.Analysis.Integral.doubleIntegral_Bkernel_bound n
  have hL : zetaBJ n
      = ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
          (((1 - s * t) - (1 - s ^ 2) * (1 - t ^ 2)) ^ n / (1 - s * t) ^ (n + 1)) := rfl
  rw [hL, ← tsum_succ_eq]
  exact h

/-- the untransformed ζ-side difference has *bounded* coefficients:
`|cₙ − (ζ(2)/4)aₙ| ≤ ζ(2)/4` -/
lemma abs_eichlerDiffC_le (n : ℕ) : |eichlerDiffC n| ≤ zeta2Real / 4 := by
  have h4 : |-(1 / 4) * zetaBJ n| = (1 / 4) * |zetaBJ n| := by
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  rw [eichlerDiffC_eq, h4]
  linarith [zetaBJ_bound n]

/-- **the untransformed ζ-side overconvergence is PROVED**: the coefficients
of `H_C − (ζ(2)/4)H_A` grow subexponentially, i.e. the series has radius of
convergence `≥ 1` (indeed the coefficients are bounded by `ζ(2)/4`) — the
`H_C` half of the paper's Lemma `defabc`(iii), and the analytic half of
`EichlerInputC` -/
theorem overconvergesC_proved : OverconvergesUnit eichlerDiffC := by
  intro r hr0 hr1
  refine ⟨zeta2Real / 4 + 1, by linarith [one_le_zeta2Real], fun n => ?_⟩
  have hrp : 0 < r ^ n := pow_pos hr0 n
  have h1 : r ^ n ≤ 1 := pow_le_one₀ hr0.le hr1.le
  have h2 : zeta2Real / 4 + 1 ≤ (zeta2Real / 4 + 1) / r ^ n := by
    rw [le_div_iff₀ hrp]
    nlinarith [one_le_zeta2Real]
  have h3 : |eichlerDiffC n| ≤ zeta2Real / 4 + 1 := by
    have := abs_eichlerDiffC_le n
    linarith [one_le_zeta2Real]
  exact le_trans h3 h2

/-- **`EichlerInputC` from its modular conjunct alone**: the analytic
(overconvergence) half is proved here (`overconvergesC_proved`); only the
modular `[1..n]²`-integrality `ModularIntegralityC` remains — the `H_C` mirror
of `eichlerInputB_of_modular` -/
theorem eichlerInputC_of_modular (hMod : ModularIntegralityC) : EichlerInputC :=
  ⟨hMod, overconvergesC_proved⟩

/-- **the overconvergence half of Proposition `functionsH`** now follows from
the modular `[1..n]²`-integrality alone: with `overconvergesB_proved`
(`Submission.CDT.CintegralAssembled`) and `overconvergesC_proved` both
unconditional, `functionsH_overconverges` needs no analytic input. -/
theorem functionsH_overconverges_of_modular (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (L2chi3Real / 2) + (c : ℝ) * (zeta2Real / 4) = 0)
    (hB : ModularIntegralityB) (hC : ModularIntegralityC) :
    OverconvergesUnit (fun n => (ZagierH_coeff_seq a b c n : ℝ)) :=
  functionsH_overconverges a b c hrel (eichlerInputB_of_modular hB).2
    (eichlerInputC_of_modular hC).2

end Submission.CDT
