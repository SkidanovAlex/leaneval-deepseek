import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.pairKernel_flatIntegralCone
import Submission.Work.BoseFixB1.perBoxF_flat
import Submission.Work.BoseFixB1S.BoxPIndFlat
import Submission.Work.BoseFixB1S.sectorPassageB1Pair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.densePairValue` — the **flat pair-condensate value** of the dense
# band (the unconditional half of the session-5 estimate (E2))

The chapter's dense residual `Work.BoseB1Cube.CubeBandArmDenseAt` needs the pair-term payout

    `Ps = flatPairSum ≥ (1 − η)·M₂·S²/(2V²N)`      (`S = boxFlatCount`, `N = ‖Φ‖²`)

from the *state alone*.  This module proves the first, unconditional half of it: the
**rank-one (mean-field) Cauchy–Schwarz pair value**

    `flatPairSum ≥ (√(c²Λ) − √B)²`,

where

* `c = pairCSMean` is the mean of `Φ` over `Aⁿ` (the coefficient of the box-indicator product
  `pairCSInd = ∏ᵢ1_A(xᵢ)`),
* `Λ = pairCSValue` is the *exact* value `½Σ_{p}∫_{Aⁿ}w(x_p) = (n(n−1)/2)V^{n−2}∫_{A×A}w` of the
  pair kernel against the indicator product — the PROVED
  `Work.BoseB1Cube.pairKernel_flatIntegralCone`,
* `B = ∫(Φ − c·1_{Aⁿ})²·W₂` is the pair energy of the *fluctuation*.

The proof is *only* Cauchy–Schwarz, in its discriminant form: for every `t : ℝ`

    `0 ≤ ∫(t·1_{Aⁿ} − (Φ − c·1_{Aⁿ}))²·W₂ = t²Λ − 2t·Y + B` ,   `Y = ∫1_{Aⁿ}(Φ−c·1_{Aⁿ})·W₂`,

so `Y² ≤ ΛB`; expanding `flatPairSum = ∫Φ²W₂ = ∫(c·1_{Aⁿ} + (Φ−c·1_{Aⁿ}))²W₂ = c²Λ + 2cY + B`
gives the claim.  (`W₂ = ½Σ_pw(x_p) ≥ 0` is essential — it is the standing hypothesis `0 ≤ v`.)

**This is the *easy* half of (E2)**: it is unconditional, but its *quality* depends on the state
(it is lossy exactly when `B ≍ Λ`, i.e. when the fluctuation carries as much pair energy as the
condensate).  The remaining quantitative input of the dense arm is the comparison of `√(c²Λ)` with
`√(M₂·S²/(2V²N))`, i.e. the sharp interaction estimate (FS `lm:appinteractionestimate`); see
`Submission/Work/BoseB1Cube/FINDING_denseArm_route.md` and the session-6 note.

## Cone note

All inputs are in the `boxPairValue` cone of the chapter and carry `constCalib=False
pairValue=False`: the pair-kernel identity `pairKernel_flatIntegralCone`, the kernel nonnegativity
`Work.BoseFixB1S.wSmallPair_nonneg_B1S` (`sectorPassageB1Pair`), `flatPairSum`
(`BoseFixB1.perBoxF_flat`) and the integrability engine of `BoxPIndFlat`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 0. The vocabulary -/

/-- The **box-indicator product** `∏ᵢ 1_A(xᵢ)`, i.e. the indicator of the configuration set `Aⁿ`
inside `X n`.  It is the rank-one (mean-field) test function of the flat pair value. -/
def pairCSInd {n : ℕ} (A : Set E3) : X n → ℝ :=
  fun x => ∏ i : Fin n, A.indicator (fun _ => (1 : ℝ)) (x i)

/-- The **mean of `Φ` over `Aⁿ`**, as the coefficient of `pairCSInd`: the `L²`-projection of `Φ`
onto the constants on `Aⁿ` is `pairCSMean A ℓ Φ · 1_{Aⁿ}`. -/
def pairCSMean {n : ℕ} (A : Set E3) (ℓ : ℝ) (Φ : X n → ℝ) : ℝ :=
  (∫ x in abox n ℓ, (pairCSInd A x) ^ 2)⁻¹ * ∫ x in abox n ℓ, pairCSInd A x * Φ x

/-- The **pair-kernel sum** `½Σ_{p∈pairSet n}w(x_{p.1},x_{p.2})` as a function of the
configuration.  Its integral against `Φ²` is `flatPairSum`. -/
def pairCSKernel {n : ℕ} (w : E3 → E3 → ℝ) : X n → ℝ :=
  fun x => (1 / 2) * ∑ p ∈ pairSet n, w (x p.1) (x p.2)

/-- The **fluctuation** `R = Φ − c·1_{Aⁿ}` of the state against its `Aⁿ`-mean. -/
def pairCSFluct {n : ℕ} (A : Set E3) (ℓ : ℝ) (Φ : X n → ℝ) : X n → ℝ :=
  fun x => Φ x - pairCSMean A ℓ Φ * pairCSInd A x

/-- The **exact pair-kernel value** `Λ = (n(n−1)/2)·V^{n−2}·∫_{A×A}w`, the value of `W₂` against
`1_{Aⁿ}` (`pairKernel_flatIntegralCone`). -/
def pairCSValue {n : ℕ} (A : Set E3) (V : ℝ) (w : E3 → E3 → ℝ) : ℝ :=
  ((n : ℝ) * ((n : ℝ) - 1) / 2) * V ^ (n - 2) * (∫ p in A ×ˢ A, w p.1 p.2)

/-! ## 1. Elementary properties of the vocabulary -/

/-- `pairSet n` is the ordered off-diagonal, of cardinality `n(n−1)`. -/
lemma pairSet_card_cast (n : ℕ) : (((pairSet n).card : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
  have h : pairSet n = (Finset.univ : Finset (Fin n)).offDiag := by
    ext p
    simp [pairSet, Finset.mem_offDiag]
  rw [h, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  rcases Nat.eq_zero_or_pos n with h0 | h1
  · subst h0; simp
  · have hle : n ≤ n * n := Nat.le_mul_of_pos_left n h1
    rw [Nat.cast_sub hle, Nat.cast_mul]
    ring

lemma pairCSKernel_nonneg {n : ℕ} {w : E3 → E3 → ℝ} (hw : ∀ a b, 0 ≤ w a b)
    (x : X n) : 0 ≤ pairCSKernel w x := by
  unfold pairCSKernel
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun p _ => hw _ _)

lemma pairCSKernel_abs_le {n : ℕ} {w : E3 → E3 → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hw : ∀ a b, |w a b| ≤ D) (x : X n) :
    |pairCSKernel w x| ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 * D := by
  unfold pairCSKernel
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have h1 : |∑ p ∈ pairSet n, w (x p.1) (x p.2)| ≤ (pairSet n).card * D := by
    calc |∑ p ∈ pairSet n, w (x p.1) (x p.2)|
        ≤ ∑ p ∈ pairSet n, |w (x p.1) (x p.2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ pairSet n, D := Finset.sum_le_sum fun p _ => hw _ _
      _ = (pairSet n).card * D := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard := pairSet_card_cast n
  have hcast : (((pairSet n).card : ℕ) : ℝ) = ((pairSet n).card : ℝ) := rfl
  rw [hcast, hcard] at h1
  calc (1 / 2) * |∑ p ∈ pairSet n, w (x p.1) (x p.2)|
      ≤ (1 / 2) * ((n : ℝ) * ((n : ℝ) - 1) * D) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = (n : ℝ) * ((n : ℝ) - 1) / 2 * D := by ring

lemma pairCSInd_nonneg {n : ℕ} {A : Set E3} (x : X n) : 0 ≤ pairCSInd A x := by
  unfold pairCSInd
  exact Finset.prod_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _

lemma pairCSInd_le_one {n : ℕ} {A : Set E3} (x : X n) : pairCSInd A x ≤ 1 := by
  unfold pairCSInd
  refine Finset.prod_le_one₀ (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    (fun i _ => ?_)
  by_cases h : x i ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]

lemma pairCSInd_sq {n : ℕ} {A : Set E3} (x : X n) : (pairCSInd A x) ^ 2 = pairCSInd A x := by
  have hper : ∀ i : Fin n, (A.indicator (fun _ => (1 : ℝ)) (x i)) ^ 2
      = A.indicator (fun _ => (1 : ℝ)) (x i) := by
    intro i
    by_cases h : x i ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  unfold pairCSInd
  rw [sq, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [← sq, hper i]

lemma pairCSInd_abs_le_one {n : ℕ} {A : Set E3} (x : X n) : |pairCSInd A x| ≤ 1 := by
  rw [abs_of_nonneg (pairCSInd_nonneg x)]
  exact pairCSInd_le_one x

lemma measurable_pairCSInd {n : ℕ} {A : Set E3} (hA : MeasurableSet A) :
    Measurable (pairCSInd (n := n) A) := by
  change Measurable (fun x : X n => ∏ i : Fin n, A.indicator (fun _ => (1 : ℝ)) (x i))
  exact Finset.measurable_prod Finset.univ fun i _ =>
    (measurable_const.indicator hA).comp (measurable_pi_apply i)

lemma measurable_pairCSKernel {n : ℕ} {w : E3 → E3 → ℝ}
    (hw : Measurable (Function.uncurry w)) : Measurable (pairCSKernel (n := n) w) := by
  change Measurable (fun x : X n => (1 / 2) * ∑ p ∈ pairSet n, w (x p.1) (x p.2))
  refine Measurable.const_mul (Finset.measurable_sum _ fun p _ => ?_) _
  have h1 : Measurable (fun x : X n => (x p.1, x p.2)) :=
    (measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2)
  have hw' : Measurable (fun q : E3 × E3 => w q.1 q.2) := hw
  exact hw'.comp h1

lemma pairCSFluct_abs_le {n : ℕ} {A : Set E3} {ℓ C : ℝ} {Φ : X n → ℝ}
    (hC : ∀ x ∈ abox n ℓ, |Φ x| ≤ C) {x : X n} (hx : x ∈ abox n ℓ) :
    |pairCSFluct A ℓ Φ x| ≤ C + |pairCSMean A ℓ Φ| := by
  unfold pairCSFluct
  have h1 : |Φ x - pairCSMean A ℓ Φ * pairCSInd A x|
      ≤ |Φ x| + |pairCSMean A ℓ Φ * pairCSInd A x| := abs_sub _ _
  have h2 : |pairCSMean A ℓ Φ * pairCSInd A x| ≤ |pairCSMean A ℓ Φ| * 1 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (pairCSInd_abs_le_one x) (abs_nonneg _)
  have h3 := hC x hx
  simp only [mul_one] at h2
  linarith

/-! ## 2. Integrability on the compact box -/

lemma integrableOn_pairCSIndSq_kernel {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) {w : E3 → E3 → ℝ} (hw : Measurable (Function.uncurry w))
    {D : ℝ} (hD : 0 ≤ D) (hwD : ∀ a b, |w a b| ≤ D) :
    IntegrableOn (fun x : X n => (pairCSInd A x) ^ 2 * pairCSKernel w x) (abox n ℓ) := by
  refine Work.BoseFixB1S.integrableOn_mul_of_bound (N := n) (ℓ := ℓ)
    (f := fun x : X n => (pairCSInd A x) ^ 2) (g := fun x : X n => pairCSKernel w x)
    hℓ ((measurable_pairCSInd hA).pow_const 2) (measurable_pairCSKernel hw)
    (Cf := 1) (Cg := (n : ℝ) * ((n : ℝ) - 1) / 2 * D) ?_ ?_
  · intro x _
    rw [abs_of_nonneg (sq_nonneg _)]
    calc (pairCSInd A x) ^ 2 = |pairCSInd A x| ^ 2 := (sq_abs _).symm
      _ ≤ 1 := by
          have h := pairCSInd_abs_le_one (A := A) x
          nlinarith [abs_nonneg (pairCSInd A x)]
  · intro x _
    exact pairCSKernel_abs_le hD hwD x

lemma integrableOn_pairCSInd_mul_kernel {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) {w : E3 → E3 → ℝ} (hw : Measurable (Function.uncurry w))
    {D : ℝ} (hD : 0 ≤ D) (hwD : ∀ a b, |w a b| ≤ D) {Φ : X n → ℝ} (hΦm : Measurable Φ)
    {C : ℝ} (hC : ∀ x ∈ abox n ℓ, |Φ x| ≤ C) :
    IntegrableOn (fun x : X n => pairCSInd A x * Φ x * pairCSKernel w x) (abox n ℓ) := by
  refine Work.BoseFixB1S.integrableOn_mul_of_bound (N := n) (ℓ := ℓ)
    (f := fun x : X n => pairCSInd A x * Φ x) (g := fun x : X n => pairCSKernel w x)
    hℓ ((measurable_pairCSInd hA).mul hΦm) (measurable_pairCSKernel hw)
    (Cf := C) (Cg := (n : ℝ) * ((n : ℝ) - 1) / 2 * D) ?_ ?_
  · intro x hx
    rw [abs_mul]
    calc |pairCSInd A x| * |Φ x| ≤ 1 * C :=
          mul_le_mul (pairCSInd_abs_le_one x) (hC x hx) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  · intro x _
    exact pairCSKernel_abs_le hD hwD x

lemma integrableOn_pairCSFluctSq_kernel {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) {w : E3 → E3 → ℝ} (hw : Measurable (Function.uncurry w))
    {D : ℝ} (hD : 0 ≤ D) (hwD : ∀ a b, |w a b| ≤ D) {Φ : X n → ℝ} (hΦm : Measurable Φ)
    {C : ℝ} (hC : ∀ x ∈ abox n ℓ, |Φ x| ≤ C) :
    IntegrableOn (fun x : X n => (pairCSFluct A ℓ Φ x) ^ 2 * pairCSKernel w x) (abox n ℓ) := by
  have hm : Measurable (pairCSFluct A ℓ Φ) :=
    hΦm.sub (measurable_const.mul (measurable_pairCSInd hA))
  refine Work.BoseFixB1S.integrableOn_mul_of_bound (N := n) (ℓ := ℓ)
    (f := fun x : X n => (pairCSFluct A ℓ Φ x) ^ 2) (g := fun x : X n => pairCSKernel w x)
    hℓ (hm.pow_const 2) (measurable_pairCSKernel hw) (Cf := (C + |pairCSMean A ℓ Φ|) ^ 2)
    (Cg := (n : ℝ) * ((n : ℝ) - 1) / 2 * D) ?_ ?_
  · intro x hx
    have h1 := pairCSFluct_abs_le (A := A) (ℓ := ℓ) hC hx
    have h2 : (pairCSFluct A ℓ Φ x) ^ 2 ≤ (C + |pairCSMean A ℓ Φ|) ^ 2 := by
      rw [← sq_abs (pairCSFluct A ℓ Φ x)]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [abs_of_nonneg (sq_nonneg _)]
    exact h2
  · intro x _
    exact pairCSKernel_abs_le hD hwD x

lemma integrableOn_pairCSInd_fluct_kernel {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {A : Set E3}
    (hA : MeasurableSet A) {w : E3 → E3 → ℝ} (hw : Measurable (Function.uncurry w))
    {D : ℝ} (hD : 0 ≤ D) (hwD : ∀ a b, |w a b| ≤ D) {Φ : X n → ℝ} (hΦm : Measurable Φ)
    {C : ℝ} (hC : ∀ x ∈ abox n ℓ, |Φ x| ≤ C) :
    IntegrableOn (fun x : X n => pairCSInd A x * pairCSFluct A ℓ Φ x * pairCSKernel w x)
      (abox n ℓ) := by
  have hm : Measurable (pairCSFluct A ℓ Φ) :=
    hΦm.sub (measurable_const.mul (measurable_pairCSInd hA))
  refine Work.BoseFixB1S.integrableOn_mul_of_bound (N := n) (ℓ := ℓ)
    (f := fun x : X n => pairCSInd A x * pairCSFluct A ℓ Φ x)
    (g := fun x : X n => pairCSKernel w x)
    hℓ ((measurable_pairCSInd hA).mul hm) (measurable_pairCSKernel hw)
    (Cf := C + |pairCSMean A ℓ Φ|) (Cg := (n : ℝ) * ((n : ℝ) - 1) / 2 * D) ?_ ?_
  · intro x hx
    rw [abs_mul]
    have h1 := pairCSFluct_abs_le (A := A) (ℓ := ℓ) hC hx
    calc |pairCSInd A x| * |pairCSFluct A ℓ Φ x| ≤ 1 * (C + |pairCSMean A ℓ Φ|) :=
          mul_le_mul (pairCSInd_abs_le_one x) h1 (abs_nonneg _) zero_le_one
      _ = C + |pairCSMean A ℓ Φ| := one_mul _
  · intro x _
    exact pairCSKernel_abs_le hD hwD x

/-! ## 3. The pair-kernel value against the indicator product -/

/-- **The exact kernel value** `∫_{abox}(∏ᵢ1_A(xᵢ))·W₂ = Λ` — the PROVED
`Work.BoseB1Cube.pairKernel_flatIntegralCone` read in this module's vocabulary. -/
theorem integral_pairCSInd_kernel_eq {n : ℕ} {ℓ V D : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {w : E3 → E3 → ℝ}
    (hwm : AEStronglyMeasurable (Function.uncurry w) (volume.restrict (A ×ˢ A)))
    (hwD : ∀ a b, |w a b| ≤ D) :
    (∫ x in abox n ℓ, pairCSInd A x * pairCSKernel w x) = pairCSValue (n := n) A V w :=
  pairKernel_flatIntegralCone hℓ hV hA hVeq hAc hwm hwD

/-- The same against the *square* of the indicator product (`1_{Aⁿ}² = 1_{Aⁿ}`). -/
theorem integral_pairCSIndSq_kernel_eq {n : ℕ} {ℓ V D : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {w : E3 → E3 → ℝ}
    (hwm : AEStronglyMeasurable (Function.uncurry w) (volume.restrict (A ×ˢ A)))
    (hwD : ∀ a b, |w a b| ≤ D) :
    (∫ x in abox n ℓ, (pairCSInd A x) ^ 2 * pairCSKernel w x) = pairCSValue (n := n) A V w := by
  rw [← integral_pairCSInd_kernel_eq (n := n) (ℓ := ℓ) (V := V) (D := D) hℓ hV hA hVeq hAc hwm hwD]
  refine MeasureTheory.setIntegral_congr_fun (abox_measurable n ℓ) fun x _ => ?_
  rw [pairCSInd_sq]

/-! ## 4. The discriminant arithmetic of Cauchy–Schwarz -/

/-- **The discriminant form of Cauchy–Schwarz.**  If `t²A − 2tY + B ≥ 0` for every `t : ℝ` and
`A, B ≥ 0`, then `Y² ≤ AB`. -/
theorem sq_le_mul_of_quadratic_nonneg {A B Y : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 ≤ t ^ 2 * A - 2 * t * Y + B) : Y ^ 2 ≤ A * B := by
  rcases lt_or_eq_of_le hA with hApos | hA0
  · have h1 := h (Y / A)
    have h2 : (Y / A) ^ 2 * A - 2 * (Y / A) * Y + B = B - Y ^ 2 / A := by
      field_simp; ring
    have h3 : Y ^ 2 / A ≤ B := by linarith [h2.le, h2.ge, h1]
    rw [div_le_iff₀ hApos] at h3
    linarith
  · have hA0' : A = 0 := hA0.symm
    rcases eq_or_ne Y 0 with hY | hY
    · rw [hY, hA0']; simp
    · have h1 := h ((B + 1) / (2 * Y))
      have h2 : ((B + 1) / (2 * Y)) ^ 2 * A - 2 * ((B + 1) / (2 * Y)) * Y + B = -1 := by
        rw [hA0']; field_simp; ring
      linarith [h2.le, h2.ge, h1]

/-- **The weighted Cauchy–Schwarz inequality** for an integral against a nonnegative weight:
if `f²w`, `g²w` and `fgw` are all integrable then `(∫fgw)² ≤ (∫f²w)(∫g²w)`.

The proof is the discriminant form: `0 ≤ ∫(tf − g)²w = t²∫f²w − 2t∫fgw + ∫g²w` for every `t`,
and the quadratic has nonnegative discriminant. -/
theorem integral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {F G Wt : α → ℝ}
    (hW : ∀ x, 0 ≤ Wt x)
    (hF : Integrable (fun x => (F x) ^ 2 * Wt x) μ)
    (hG : Integrable (fun x => (G x) ^ 2 * Wt x) μ)
    (hFG : Integrable (fun x => F x * G x * Wt x) μ) :
    (∫ x, F x * G x * Wt x ∂μ) ^ 2
      ≤ (∫ x, (F x) ^ 2 * Wt x ∂μ) * (∫ x, (G x) ^ 2 * Wt x ∂μ) := by
  have hquad : ∀ t : ℝ, (∫ x, (t * F x - G x) ^ 2 * Wt x ∂μ)
      = t ^ 2 * (∫ x, (F x) ^ 2 * Wt x ∂μ) - 2 * t * (∫ x, F x * G x * Wt x ∂μ)
        + (∫ x, (G x) ^ 2 * Wt x ∂μ) := by
    intro t
    have hpt : ∀ x, (t * F x - G x) ^ 2 * Wt x
        = t ^ 2 * ((F x) ^ 2 * Wt x) - (2 * t) * (F x * G x * Wt x) + (G x) ^ 2 * Wt x := by
      intro x; ring
    rw [show (fun x => (t * F x - G x) ^ 2 * Wt x)
        = fun x => t ^ 2 * ((F x) ^ 2 * Wt x) - (2 * t) * (F x * G x * Wt x)
            + (G x) ^ 2 * Wt x from funext hpt]
    rw [MeasureTheory.integral_add
        (f := fun x => t ^ 2 * ((F x) ^ 2 * Wt x) - (2 * t) * (F x * G x * Wt x))
        (g := fun x => (G x) ^ 2 * Wt x)
        ((hF.const_mul (t ^ 2)).sub (hFG.const_mul (2 * t))) hG,
      MeasureTheory.integral_sub (f := fun x => t ^ 2 * ((F x) ^ 2 * Wt x))
        (g := fun x => (2 * t) * (F x * G x * Wt x)) (hF.const_mul (t ^ 2))
        (hFG.const_mul (2 * t)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hF0 : 0 ≤ ∫ x, (F x) ^ 2 * Wt x ∂μ :=
    MeasureTheory.integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hW x)
  have hG0 : 0 ≤ ∫ x, (G x) ^ 2 * Wt x ∂μ :=
    MeasureTheory.integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hW x)
  exact sq_le_mul_of_quadratic_nonneg hF0 hG0 fun t => by
    rw [← hquad t]
    exact MeasureTheory.integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hW x)

/-- The integral of a function that is pointwise a sum of three integrable functions. -/
theorem integral_congr_add3 {α : Type*} [MeasurableSpace α] {μ : Measure α} {f1 f2 f3 F : α → ℝ}
    (h1 : Integrable f1 μ) (h2 : Integrable f2 μ) (h3 : Integrable f3 μ)
    (hF : ∀ x, F x = f1 x + f2 x + f3 x) :
    ∫ x, F x ∂μ = (∫ x, f1 x ∂μ) + (∫ x, f2 x ∂μ) + (∫ x, f3 x ∂μ) := by
  rw [show F = fun x => f1 x + f2 x + f3 x from funext hF,
    MeasureTheory.integral_add (f := fun x => f1 x + f2 x) (g := f3) (h1.add h2) h3,
    MeasureTheory.integral_add h1 h2]

/-! ## 5. The flat pair-condensate value -/

/-- **The unconditional Cauchy–Schwarz pair value.**  For a continuous state `Φ`, a box `A` with
`0 < V = |A|` and a pair kernel `w ≥ 0` bounded by `D`,

    `flatPairSum ≥ (√(c²·Λ) − √B)²` ,   `c = pairCSMean A ℓ Φ` ,

with the exact kernel value `Λ = pairCSValue A V w` and the fluctuation pair energy
`B = ∫(Φ − c·1_{Aⁿ})²·W₂`. -/
theorem flatPairSum_ge_pairCS {v : E3 → ℝ} {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : E3) (hV : 0 < Work.SmallBoxSliding.boxMass ℓ d u) {n : ℕ} {Φ : X n → ℝ}
    (hΦc : Continuous Φ) {D : ℝ} (hD : 0 ≤ D) (hv : 0 ≤ v)
    (hvm : Measurable (Function.uncurry (Submission.BoseGases.wSmallPair M ℓ d u v)))
    (hwD : ∀ a b, |Submission.BoseGases.wSmallPair M ℓ d u v a b| ≤ D) :
    (Real.sqrt ((pairCSMean (dlBox ℓ d u) ℓ Φ) ^ 2
          * pairCSValue (n := n) (dlBox ℓ d u) (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.wSmallPair M ℓ d u v))
        - Real.sqrt (∫ x in abox n ℓ,
            (pairCSFluct (dlBox ℓ d u) ℓ Φ x) ^ 2
              * pairCSKernel (Submission.BoseGases.wSmallPair M ℓ d u v) x)) ^ 2
      ≤ Work.BoseFixB1.flatPairSum v M ℓ d u Φ := by
  classical
  set A : Set E3 := dlBox ℓ d u with hAdef
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set w : E3 → E3 → ℝ := Submission.BoseGases.wSmallPair M ℓ d u v with hwdef
  set c : ℝ := pairCSMean A ℓ Φ with hcdef
  set R : X n → ℝ := pairCSFluct A ℓ Φ with hRdef
  set Wt : X n → ℝ := pairCSKernel w with hWtdef
  set Lam : ℝ := pairCSValue (n := n) A V w with hLamdef
  set Y : ℝ := ∫ x in abox n ℓ, pairCSInd A x * R x * Wt x with hYdef
  set Bq : ℝ := ∫ x in abox n ℓ, (R x) ^ 2 * Wt x with hBqdef
  -- the hypotheses about `A`, `V`, `w`
  have hAmeas : MeasurableSet A := hAdef ▸ Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hVeq : V = (volume A).toReal := by
    rw [hVdef, hAdef]; exact Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  have hAc : A ⊆ acube ℓ := hAdef ▸ Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hVpos : 0 < V := hVdef ▸ hV
  have hΦm : Measurable Φ := hΦc.measurable
  have hvm' : Measurable (Function.uncurry w) := hwdef ▸ hvm
  have hwD' : ∀ a b, |w a b| ≤ D := fun a b => hwdef ▸ hwD a b
  -- the kernel is pointwise nonnegative
  have hwnn : ∀ a b, 0 ≤ w a b := fun a b => hwdef ▸
    Work.BoseFixB1S.wSmallPair_nonneg_B1S u a b (hv (a - b))
  have hWnn : ∀ x : X n, 0 ≤ Wt x := fun x => pairCSKernel_nonneg hwnn x
  -- a bound for `Φ` on the compact box
  obtain ⟨C, hC⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn
    (s := abox n ℓ) hΦc.continuousOn
  have hC' : ∀ x ∈ abox n ℓ, |Φ x| ≤ C := fun x hx => by
    simpa [Real.norm_eq_abs] using hC x hx
  -- integrability of the pieces, in the `Integrable` form
  have hI1 : Integrable (fun x : X n => (pairCSInd A x) ^ 2 * Wt x)
      (volume.restrict (abox n ℓ)) :=
    hWtdef ▸ integrableOn_pairCSIndSq_kernel hℓ hAmeas hvm' hD hwD'
  have hI2 : Integrable (fun x : X n => pairCSInd A x * R x * Wt x)
      (volume.restrict (abox n ℓ)) :=
    hRdef ▸ hWtdef ▸ integrableOn_pairCSInd_fluct_kernel hℓ hAmeas hvm' hD hwD' hΦm hC'
  have hI3 : Integrable (fun x : X n => (R x) ^ 2 * Wt x) (volume.restrict (abox n ℓ)) :=
    hRdef ▸ hWtdef ▸ integrableOn_pairCSFluctSq_kernel hℓ hAmeas hvm' hD hwD' hΦm hC'
  -- the exact value of the kernel against the indicator
  have hVal : (∫ x in abox n ℓ, (pairCSInd A x) ^ 2 * Wt x) = Lam := by
    rw [hLamdef, hWtdef, hAdef, hVdef, hwdef]
    exact integral_pairCSIndSq_kernel_eq hℓ hV hAmeas hVeq hAc hvm.aestronglyMeasurable hwD
  -- nonnegativity of `Lam` and `Bq`
  have hLam0 : 0 ≤ Lam := by
    rw [hLamdef]
    simp only [pairCSValue]
    have h1 : 0 ≤ ∫ p in A ×ˢ A, w p.1 p.2 :=
      MeasureTheory.integral_nonneg fun p => hwnn p.1 p.2
    have h2 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; norm_num
      · have hn : (1 : ℝ) ≤ n := by exact_mod_cast h
        have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
    have h3 : (0 : ℝ) ≤ V ^ (n - 2) := pow_nonneg hVpos.le (n - 2)
    exact mul_nonneg (mul_nonneg h2 h3) h1
  have hBq0 : 0 ≤ Bq := by
    rw [hBqdef]
    exact MeasureTheory.integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hWnn x)
  -- Cauchy–Schwarz
  have hCS : Y ^ 2 ≤ Lam * Bq := by
    rw [hYdef, hBqdef]
    have h1 : Integrable (fun x : X n => (pairCSInd A x) ^ 2 * Wt x)
        (volume.restrict (abox n ℓ)) := hI1
    have h2 : Integrable (fun x : X n => (R x) ^ 2 * Wt x) (volume.restrict (abox n ℓ)) := hI3
    have h3 : Integrable (fun x : X n => pairCSInd A x * R x * Wt x)
        (volume.restrict (abox n ℓ)) := hI2
    have h4 := integral_mul_sq_le (μ := volume.restrict (abox n ℓ))
      (F := pairCSInd A) (G := R) (Wt := Wt) hWnn h1 h2 h3
    rw [hVal] at h4
    exact h4
  -- the expansion of `flatPairSum`
  have hflat : Work.BoseFixB1.flatPairSum v M ℓ d u Φ
      = ∫ x in abox n ℓ, (Φ x) ^ 2 * Wt x := by
    simp only [Work.BoseFixB1.flatPairSum, hWtdef, pairCSKernel, hwdef]
  have hexp : (∫ x in abox n ℓ, (Φ x) ^ 2 * Wt x) = c ^ 2 * Lam + 2 * c * Y + Bq := by
    have h1 : Integrable (fun x : X n => c ^ 2 * ((pairCSInd A x) ^ 2 * Wt x))
        (volume.restrict (abox n ℓ)) := hI1.const_mul _
    have h2 : Integrable (fun x : X n => (2 * c) * (pairCSInd A x * R x * Wt x))
        (volume.restrict (abox n ℓ)) := hI2.const_mul _
    have hpt : ∀ x : X n, (Φ x) ^ 2 * Wt x
        = c ^ 2 * ((pairCSInd A x) ^ 2 * Wt x) + (2 * c) * (pairCSInd A x * R x * Wt x)
          + (R x) ^ 2 * Wt x := by
      intro x
      have hx : Φ x = c * pairCSInd A x + R x := by
        rw [hRdef, pairCSFluct, hcdef]; ring
      rw [hx]; ring
    have hstep := integral_congr_add3 (μ := volume.restrict (abox n ℓ)) h1 h2 hI3 hpt
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hVal] at hstep
    rw [← hYdef, ← hBqdef] at hstep
    exact hstep
  rw [hflat, hexp]
  -- the final arithmetic
  have hcsq : Real.sqrt (c ^ 2 * Lam) = |c| * Real.sqrt Lam := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  have hYabs : |Y| ≤ Real.sqrt Lam * Real.sqrt Bq := by
    have h1 : |Y| ≤ Real.sqrt (Lam * Bq) := by
      rw [← Real.sqrt_sq_eq_abs,
        Real.sqrt_le_sqrt_iff (x := Y ^ 2) (y := Lam * Bq) (mul_nonneg hLam0 hBq0)]
      exact hCS
    rwa [Real.sqrt_mul hLam0] at h1
  have hcross : 2 * c * Y ≥ -2 * (|c| * (Real.sqrt Lam * Real.sqrt Bq)) := by
    have h1 : c * Y ≥ -(|c| * |Y|) := by
      have h2 := neg_abs_le (c * Y)
      rw [abs_mul] at h2
      linarith
    have h2 : |c| * |Y| ≤ |c| * (Real.sqrt Lam * Real.sqrt Bq) :=
      mul_le_mul_of_nonneg_left hYabs (abs_nonneg c)
    linarith
  have hexpand : (|c| * Real.sqrt Lam - Real.sqrt Bq) ^ 2
      = c ^ 2 * Lam - 2 * (|c| * (Real.sqrt Lam * Real.sqrt Bq)) + Bq := by
    have hs : (|c| * Real.sqrt Lam) ^ 2 = c ^ 2 * Lam := by
      rw [mul_pow, sq_abs, Real.sq_sqrt hLam0]
    have hb : (Real.sqrt Bq) ^ 2 = Bq := Real.sq_sqrt hBq0
    rw [sub_sq, hs, hb]
    ring
  rw [hcsq, hexpand]
  linarith

end Work.BoseB1Cube
