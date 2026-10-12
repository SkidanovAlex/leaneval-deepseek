import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.perBoxF_localised
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The pointwise local-sup fibre bound (no measurability needed) -/

/-- **Pointwise domination of the localised kernel `wSmallPair` by the exact cutoffs.**

For any numerator `f` vanishing outside `ball 0 R` (with `R ≤ (ℓd)/16` and `R ≤ ℓ·chiR0`),
with `κ := 2·(smallConvLower M)⁻¹`,

    |w_{B(u)}(x,y)| ≤ κ·χ_{B(u)}(x)·|f(x−y)|·χ_{B(u)}(y) .

(This is the χ_B-keeping form of `Work.BoseFixB1.corner_wSmallPair_fibre_le.abs_wSmallPair_chiB_le`,
restated here so that the file depends only on the sorry-free scattering modules.) -/
lemma abs_wSmallPair_chiB_le_local {M : ℕ} (hM : 1 ≤ M) {ℓ d R : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hfsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → f z = 0)
    (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u x y : EuclideanSpace ℝ (Fin 3)) :
    |Submission.BoseGases.wSmallPair M ℓ d u f x y| ≤
      (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹)
        * Submission.BoseGases.chiSmallB M ℓ d u x * |f (x - y)|
        * Submission.BoseGases.chiSmallB M ℓ d u y := by
  have hcd : 0 < ℓ * d := mul_pos hℓ hd
  have hxnn : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  have hynn : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u y :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u y
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hW : |Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y)| ≤
      |f (x - y)| / Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.abs_wSmallScaled_le (M := M) (c := ℓ * d) (R := R)
      hM hcd hfsupp hR (x - y)
  have hmid : |Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y)
        / Submission.BoseGases.convScale ℓ (x - y)| ≤
      2 * (|f (x - y)| / Work.SmallBoxSliding.smallConvLower M) := by
    by_cases hnorm : ‖x - y‖ ≤ R
    · have hinv : |(Submission.BoseGases.convScale ℓ (x - y))⁻¹| ≤ 2 :=
        Submission.BoseGases.abs_inv_convScale_le_two (ℓ := ℓ) (R := R) hℓ hRχ hnorm
      rw [div_eq_mul_inv, abs_mul]
      calc |Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y)|
              * |(Submission.BoseGases.convScale ℓ (x - y))⁻¹|
          ≤ (|f (x - y)| / Work.SmallBoxSliding.smallConvLower M) * 2 :=
            mul_le_mul hW hinv (abs_nonneg _) (div_nonneg (abs_nonneg _) (le_of_lt hSpos))
        _ = 2 * (|f (x - y)| / Work.SmallBoxSliding.smallConvLower M) := by ring
    · have hz0 : f (x - y) = 0 := hfsupp (x - y) (le_of_lt (lt_of_not_ge hnorm))
      have hw0 : Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y) = 0 := by
        dsimp [Submission.BoseGases.wSmallScaled]
        rw [hz0]
        ring
      rw [hw0, hz0, zero_div, abs_zero]
      simp
  have hm0 : 0 ≤ 2 * (|f (x - y)| / Work.SmallBoxSliding.smallConvLower M) :=
    mul_nonneg (by norm_num) (div_nonneg (abs_nonneg _) (le_of_lt hSpos))
  calc |Submission.BoseGases.wSmallPair M ℓ d u f x y|
      = Submission.BoseGases.chiSmallB M ℓ d u x
          * |Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y)
              / Submission.BoseGases.convScale ℓ (x - y)|
          * Submission.BoseGases.chiSmallB M ℓ d u y := by
        unfold Submission.BoseGases.wSmallPair
        rw [abs_mul, abs_mul, abs_of_nonneg hxnn, abs_of_nonneg hynn]
    _ ≤ Submission.BoseGases.chiSmallB M ℓ d u x
          * (2 * (|f (x - y)| / Work.SmallBoxSliding.smallConvLower M))
          * Submission.BoseGases.chiSmallB M ℓ d u y :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmid hxnn) (le_refl _) hynn
          (mul_nonneg hxnn hm0)
    _ = (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹)
          * Submission.BoseGases.chiSmallB M ℓ d u x * |f (x - y)|
          * Submission.BoseGases.chiSmallB M ℓ d u y := by
        rw [div_eq_mul_inv]; ring

/-- **The local-sup fibre bound.**

If `χ_{B(u)}(y) ≤ g x` for all `y` with `‖y − x‖ ≤ R` (i.e. `g x` bounds the cutoff on the
`R`-ball around `x`, which is exactly the support of the kernel `g₀(x − ·)`), then

    |∫_y w_{1,B(u)}(x,y) dy| ≤ 2·(smallConvLower M)⁻¹·(∫|g₀|)·χ_{B(u)}(x)·g x .

The second cutoff factor is kept (and dominated with `hg`) instead of being bounded by its sup
`chiSupAbs·chiSmallDecay M`; this is the "local-sup" form of `FINDING_flatArmSliding.md` §4.2,
whose point is the extra factor `χ_{B(u)}(x)` on the right. -/
theorem fibre_abs_le_chiB_mul_localSup {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (h : Work.UBB.ScatSol v) (hR0 : 0 < R0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u x : EuclideanSpace ℝ (Fin 3)) {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg : ∀ y : EuclideanSpace ℝ (Fin 3), ‖y - x‖ ≤ R0 →
      Submission.BoseGases.chiSmallB M ℓ d u y ≤ g x) :
    |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y| ≤
      (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹
        * (∫ w : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h w|))
        * Submission.BoseGases.chiSmallB M ℓ d u x * g x := by
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hg0int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR0 hv_supp h
  have hsupp0 : ∀ z : EuclideanSpace ℝ (Fin 3), R0 ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  set A : ℝ := Submission.BoseGases.chiSmallB M ℓ d u x with hAdef
  set G : ℝ := ∫ w : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h w| with hGdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]; exact Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  have hgx0 : 0 ≤ g x := le_trans hA0 (hg x (by simpa using hR0.le))
  have hG0 : 0 ≤ G := by
    rw [hGdef]; exact integral_nonneg (fun w => abs_nonneg _)
  have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.wSmall1Pair h M ℓ d u x y| ≤
        2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * A * g x
          * |Submission.BoseGases.g0 v h (x - y)| := by
    intro y
    have hbase := abs_wSmallPair_chiB_le_local (M := M) hM hℓ hd hsupp0 hR hRχ u x y
    have hrew : Submission.BoseGases.wSmall1Pair h M ℓ d u x y
        = Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) x y := rfl
    have hfacnn : 0 ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * A
        * |Submission.BoseGases.g0 v h (x - y)| := by
      refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (le_of_lt (inv_pos.mpr hSpos))) hA0) (abs_nonneg _)
    rw [hrew]
    by_cases hxy : ‖x - y‖ ≤ R0
    · have hy : Submission.BoseGases.chiSmallB M ℓ d u y ≤ g x :=
        hg y (by simpa [norm_sub_rev] using hxy)
      calc |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) x y|
          ≤ (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹)
              * Submission.BoseGases.chiSmallB M ℓ d u x
              * |Submission.BoseGases.g0 v h (x - y)|
              * Submission.BoseGases.chiSmallB M ℓ d u y := hbase
        _ ≤ (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹)
              * Submission.BoseGases.chiSmallB M ℓ d u x
              * |Submission.BoseGases.g0 v h (x - y)| * g x :=
            mul_le_mul_of_nonneg_left hy hfacnn
        _ = 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * A * g x
              * |Submission.BoseGases.g0 v h (x - y)| := by rw [hAdef]; ring
    · have hz0 : Submission.BoseGases.g0 v h (x - y) = 0 :=
        hsupp0 (x - y) (le_of_lt (lt_of_not_ge hxy))
      have hw0 : Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) x y = 0 := by
        unfold Submission.BoseGases.wSmallPair Submission.BoseGases.wSmallScaled
        rw [hz0]
        ring
      rw [hw0, hz0]
      simp
  have hfi : MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      |Submission.BoseGases.g0 v h (x - y)|) := hg0int.abs.comp_sub_left x
  have hmaj : MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * A * g x
        * |Submission.BoseGases.g0 v h (x - y)|) := hfi.const_mul _
  have hmajOn : MeasureTheory.IntegrableOn (fun y : EuclideanSpace ℝ (Fin 3) =>
      2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * A * g x
        * |Submission.BoseGases.g0 v h (x - y)|) (Submission.BoseGases.acube ℓ) :=
    hmaj.integrableOn
  have hstep1 : |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
      ≤ ∫ y in Submission.BoseGases.acube ℓ,
        |Submission.BoseGases.wSmall1Pair h M ℓ d u x y| := by
    have hh := norm_integral_le_integral_norm
      (μ := (volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ))
      (f := fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
    simpa only [Real.norm_eq_abs] using hh
  have hstep2 : (∫ y in Submission.BoseGases.acube ℓ,
        |Submission.BoseGases.wSmall1Pair h M ℓ d u x y|)
      ≤ ∫ y in Submission.BoseGases.acube ℓ,
        2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * A * g x
          * |Submission.BoseGases.g0 v h (x - y)| :=
    integral_mono_of_nonneg (ae_of_all _ (fun y => abs_nonneg _)) hmajOn (ae_of_all _ hpt)
  have hstep3 : (∫ y in Submission.BoseGases.acube ℓ,
        2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * A * g x
          * |Submission.BoseGases.g0 v h (x - y)|)
      = (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * A * g x)
        * (∫ y in Submission.BoseGases.acube ℓ, |Submission.BoseGases.g0 v h (x - y)|) :=
    integral_const_mul _ _
  have hstep4 : (∫ y in Submission.BoseGases.acube ℓ, |Submission.BoseGases.g0 v h (x - y)|)
      ≤ ∫ y : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h (x - y)| :=
    setIntegral_le_integral hfi (ae_of_all _ (fun y => abs_nonneg _))
  have hstep5 : (∫ y : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h (x - y)|) = G := by
    rw [hGdef]
    exact Submission.BoseGases.integral_comp_sub_left
      (fun w : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h w|) x
  have hfac0 : 0 ≤ 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * A * g x :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (le_of_lt (inv_pos.mpr hSpos))) hA0) hgx0
  calc |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
      ≤ ∫ y in Submission.BoseGases.acube ℓ,
          |Submission.BoseGases.wSmall1Pair h M ℓ d u x y| := hstep1
    _ ≤ ∫ y in Submission.BoseGases.acube ℓ,
          2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * A * g x
            * |Submission.BoseGases.g0 v h (x - y)| := hstep2
    _ = (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * A * g x)
          * (∫ y in Submission.BoseGases.acube ℓ,
              |Submission.BoseGases.g0 v h (x - y)|) := hstep3
    _ ≤ (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * A * g x) * G :=
        mul_le_mul_of_nonneg_left (le_trans hstep4 hstep5.le) hfac0
    _ = (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * G)
          * Submission.BoseGases.chiSmallB M ℓ d u x * g x := by rw [hAdef, hGdef]; ring

/-! ## 2. The requested statement, with the missing measurability hypothesis added -/

/-- **Corrected form of `flatArmFibreLocalSup`**: the requested statement with the hypothesis
`(hgm : Measurable g)` added (equivalently `AEMeasurable g volume` would do).

`fibSum` is the integral over `abox n ℓ` of `Φ²` against the fibre sum; §1 bounds each fibre
pointwise by `2·(smallConvLower M)⁻¹·(∫|g₀|)·χ_B(xᵢ)·g xᵢ = 16π·(smallConvLower M)⁻¹·a v·χ_B(xᵢ)g xᵢ`,
and monotone integration finishes, the dominating integrand being measurable (this is exactly the
step that needs the measurability of `g`) and bounded on the compact box. -/
theorem flatArmFibreLocalSup_measurable {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR16 : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (hΦc : Continuous Φ) (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hgm : Measurable g)
    (hg : ∀ x y : EuclideanSpace ℝ (Fin 3),
      ‖y - x‖ ≤ R → Submission.BoseGases.chiSmallB M ℓ d u y ≤ g x)
    (hgb : ∀ x : EuclideanSpace ℝ (Fin 3),
      g x ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) :
    ∃ C : ℝ, 0 ≤ C ∧
      Work.BoseFixB1.fibSum h M ℓ d u Φ
        ≤ C * (_root_.BoseGases.a v)
          * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
              ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)) := by
  set Cs : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M with hCsdef
  have hCs0 : 0 ≤ Cs := by
    rw [hCsdef]
    exact mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg M)
  -- the value of `∫|g₀|`
  set G : ℝ := ∫ w : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h w| with hGdef
  have hGval : G = 8 * π * (_root_.BoseGases.a v) := by
    rw [hGdef]
    have habs : (∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h z|)
        = ∫ z : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.g0 v h z := by
      refine integral_congr_ae ?_
      filter_upwards [Submission.BoseGases.g0_nonneg_ae (v := v) (R := R) hR hv hvrad hv_supp h]
        with z hz
      exact abs_of_nonneg hz
    rw [habs, Submission.BoseGases.g0_integral hR hv_supp h]
  set c : ℝ := 2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * G with hcdef
  have hceq : c = 16 * π * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * (_root_.BoseGases.a v) := by
    rw [hcdef, hGval]; ring
  -- the pointwise fibre bound at every particle
  have hfib : ∀ x : Submission.BoseGases.X n, ∀ i : Fin n,
      (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
        ≤ c * (Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)) := by
    intro x i
    have h1 := fibre_abs_le_chiB_mul_localSup (v := v) (R0 := R) h hR hv_supp hM hℓ hd hR16 hRχ
      u (x i) (fun y hy => hg (x i) y hy)
    rw [← hGdef] at h1
    calc (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
        ≤ |∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y| := le_abs_self _
      _ ≤ (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * G)
            * Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i) := h1
      _ = c * (Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)) := by
          rw [hcdef]; ring
  -- the pointwise comparison of the integrands
  have hpoint : ∀ x : Submission.BoseGases.X n,
      (Φ x) ^ 2 * ∑ i : Fin n, (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
        ≤ c * ((Φ x) ^ 2 *
            ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)) := by
    intro x
    have hsum : (∑ i : Fin n, (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y))
        ≤ ∑ i : Fin n, c * (Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)) :=
      Finset.sum_le_sum fun i _ => hfib x i
    calc (Φ x) ^ 2 * ∑ i : Fin n, (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y)
        ≤ (Φ x) ^ 2 * ∑ i : Fin n, c * (Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)) :=
          mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = c * ((Φ x) ^ 2
            * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)) := by
          have h1 : (∑ i : Fin n,
                c * (Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)))
              = c * ∑ i : Fin n,
                  Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i) :=
            (Finset.mul_sum Finset.univ (fun i : Fin n =>
              Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)) c).symm
          rw [h1]
          ring
  -- the dominating integrand is integrable on the compact box
  have hAbox : IsCompact (Submission.BoseGases.abox n ℓ) :=
    Work.UBBInputs9.B.abox_isCompact n ℓ
  have hcB : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M ℓ d u z) := by
    unfold Submission.BoseGases.chiSmallB
    exact (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))
  have hHmeas : Measurable (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)) :=
    ((hΦc.measurable).pow_const 2).mul
      (Finset.measurable_sum _ fun i _ =>
        (hcB.measurable.comp (measurable_pi_apply i)).mul
          (hgm.comp (measurable_pi_apply i)))
  obtain ⟨BΦ, hBΦ⟩ := hAbox.exists_bound_of_continuousOn hΦc.continuousOn
  set B : ℝ := max BΦ 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hBΦ' : ∀ x ∈ Submission.BoseGases.abox n ℓ, |Φ x| ≤ B := by
    intro x hx
    rw [← Real.norm_eq_abs]
    exact le_trans (hBΦ x hx) (le_max_left _ _)
  have hHbound : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      ‖(Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)‖
        ≤ B ^ 2 * ((n : ℝ) * Cs ^ 2) := by
    intro x hx
    have hterm : ∀ i : Fin n,
        |Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)| ≤ Cs ^ 2 := by
      intro i
      have hχ : |Submission.BoseGases.chiSmallB M ℓ d u (x i)| ≤ Cs := by
        rw [abs_of_nonneg (Submission.BoseGases.chiSmallB_nonneg M ℓ d u (x i)), hCsdef]
        exact Work.BoseFixB1.chiSmallB_le_sup hM u (x i)
      have hgnn : 0 ≤ g (x i) :=
        le_trans (Submission.BoseGases.chiSmallB_nonneg M ℓ d u (x i))
          (hg (x i) (x i) (by simpa using hR.le))
      have hgabs : |g (x i)| ≤ Cs := by
        rw [abs_of_nonneg hgnn, hCsdef]
        exact hgb (x i)
      rw [abs_mul, sq]
      exact mul_le_mul hχ hgabs (abs_nonneg _) hCs0
    have hsum : |∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)|
        ≤ (n : ℝ) * Cs ^ 2 := by
      calc |∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)|
          ≤ ∑ i : Fin n, |Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, Cs ^ 2 := Finset.sum_le_sum fun i _ => hterm i
        _ = (n : ℝ) * Cs ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (Φ x))]
    have hsq : (Φ x) ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg (Φ x)) (hBΦ' x hx) 2
    exact mul_le_mul hsq hsum (abs_nonneg _) (by positivity)
  have hH_int : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      (Φ x) ^ 2 * ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i))
      (Submission.BoseGases.abox n ℓ) := by
    refine MeasureTheory.IntegrableOn.of_bound hAbox.measure_lt_top
      hHmeas.aestronglyMeasurable (B ^ 2 * ((n : ℝ) * Cs ^ 2)) ?_
    rw [MeasureTheory.ae_restrict_iff' hAbox.measurableSet]
    exact Filter.Eventually.of_forall fun x hx => hHbound x hx
  -- the monotone integration
  have hmono : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
        ∑ i : Fin n, (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y))
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, c * ((Φ x) ^ 2 *
          ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)) :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x =>
        mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ =>
          Work.BoseFixB1.wSmall1Pair_fibre_nonneg (v := v) (R0 := R) hR hv hvrad hv_supp h
            u (x i)))
      (hH_int.const_mul c) (Filter.Eventually.of_forall fun x => hpoint x)
  refine ⟨16 * π * (Work.SmallBoxSliding.smallConvLower M)⁻¹, ?_, ?_⟩
  · have hS := Work.SmallBoxSliding.smallConvLower_pos M
    positivity
  calc Work.BoseFixB1.fibSum h M ℓ d u Φ
      = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
          ∑ i : Fin n, (∫ y in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.wSmall1Pair h M ℓ d u (x i) y) := by
        rw [Work.BoseFixB1.fibSum]
    _ ≤ ∫ x in Submission.BoseGases.abox n ℓ, c * ((Φ x) ^ 2 *
          ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)) := hmono
    _ = c * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
          ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)) :=
        integral_const_mul _ _
    _ = (16 * π * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * (_root_.BoseGases.a v)
          * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
              ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)) := by
        rw [hceq]

/-! ## 3. The requested statement (FALSE as written — kept verbatim for the requester)

The statement below has **no measurability hypothesis on `g`**; see the header of this file for
the counterexample showing that the right-hand side can be `0` (Mathlib's Bochner integral is `0`
on non-`AEStronglyMeasurable` functions) while `fibSum` is positive.  The corrected form is
`flatArmFibreLocalSup_measurable` above (§2). -/

theorem flatArmFibreLocalSup {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR16 : R ≤ ℓ * d / 16)
    (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (hΦc : Continuous Φ) (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hg : ∀ x y : EuclideanSpace ℝ (Fin 3),
      ‖y - x‖ ≤ R → Submission.BoseGases.chiSmallB M ℓ d u y ≤ g x)
    (hgb : ∀ x : EuclideanSpace ℝ (Fin 3),
      g x ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) :
    ∃ C : ℝ, 0 ≤ C ∧
      Work.BoseFixB1.fibSum h M ℓ d u Φ
        ≤ C * (_root_.BoseGases.a v)
          * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
              ∑ i : Fin n, Submission.BoseGases.chiSmallB M ℓ d u (x i) * g (x i)) := by sorry

end Work.BoseFixB1S
