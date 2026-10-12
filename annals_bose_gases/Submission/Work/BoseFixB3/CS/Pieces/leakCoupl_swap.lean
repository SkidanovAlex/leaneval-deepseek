import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB3.CS.Reduce
import Submission.Work.BoseFixB3.Conv.stronglyMeasurable_lowMult
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.leakCoupl_swap`

The **leakage coupling swap** used by `CS.Pieces.leakCoupl_core`: the double integral of the
leakage coupling, written as an `x`-integral inside a `y`-integral, is the *same* double
integral as the `y`-integral inside a `z`-integral on the right-hand side.

With `Λ = acube ℓ`, `χ_Λ := chiU ℓ 0` and `L := leakFn fc κ ℓ`, the identity is

    ∫_{Λ} L(y) χ_Λ(y) (∫_{Λ} χ_Λ(x) F(x−y) dx) dy
      = ∫_z F(z) (∫_{Λ} L(y) χ_Λ(y) χ_Λ(y+z) dy),

i.e. `z = x − y` in the inner integral (a translation of `L¹`, together with the fact that
`supp χ_Λ ⊆ ball 0 (ℓ/2) ⊆ Λ`, which makes the `x ∈ Λ` restriction and the `x ∈ ℝ³`
integration interchangeable, and makes the constraint `y + z ∈ Λ` automatic in the final
`y`-integral) followed by Fubini.

Fubini applies because the joint integrand is dominated by
`1_Λ(y) · |B| · ‖χ_Λ‖_∞² · |F z|`, which is integrable on `volume × volume` (Λ has finite
volume and `F` is integrable); the `B`-hypothesis of the statement provides the uniform
bound on `L`, and `L = 1 − lowMult fc κ ℓ (fun _ => 1)` is strongly measurable.
-/

noncomputable section

open MeasureTheory Filter Classical
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB3.CS.Pieces

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-! ## Elementary facts about the window `chiU ℓ 0` -/

/-- `chiU ℓ 0` vanishes outside the centred cube `acube ℓ` (its support is the ball of
radius `ℓ/2`, which is contained in `acube ℓ`). -/
lemma leakSwap_chiU_zero_off (ℓ : ℝ) (hℓ : 0 < ℓ) (x : E3)
    (hx : x ∉ Submission.BoseGases.acube ℓ) :
    Submission.BoseGases.chiU ℓ 0 x = 0 := by
  have hnorm : ℓ / 2 < ‖x‖ := by
    by_contra h
    exact hx (Submission.BoseGases.mem_acube_of_norm_le hℓ.le (le_of_not_gt h))
  have hgt : (1 : ℝ) / 2 < ‖(ℓ⁻¹ : ℝ) • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)]
    have h2 : ℓ⁻¹ * (ℓ / 2) = 1 / 2 := by field_simp
    rw [← h2]
    exact mul_lt_mul_of_pos_left hnorm (inv_pos.mpr hℓ)
  rw [show Submission.BoseGases.chiU ℓ 0 x = Submission.BoseGases.chi ((ℓ⁻¹ : ℝ) • x) from by
    simp [Submission.BoseGases.chiU]]
  exact Submission.BoseGases.chi_eq_zero_of_norm_gt _ hgt

/-- `chiU ℓ u` is bounded, uniformly in the point. -/
lemma leakSwap_chiU_abs_le (ℓ : ℝ) (u : E3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E3, |Submission.BoseGases.chiU ℓ u x| ≤ C := by
  refine ⟨(Real.sqrt Submission.BoseGases.chiNormSq)⁻¹,
    inv_nonneg.mpr (Real.sqrt_nonneg _), fun x => ?_⟩
  have hnn : 0 ≤ Submission.BoseGases.chiU ℓ u x := Submission.BoseGases.chi_nonneg _
  rw [abs_of_nonneg hnn]
  simpa only [Submission.BoseGases.chiU] using
    Submission.BoseGases.chi_le_sqrt_inv ((ℓ⁻¹ : ℝ) • x - u)

/-- The leakage function `leakFn fc κ ℓ = 1 − lowMult fc κ ℓ (fun _ => 1)` is strongly
measurable (a constant minus a momentum multiplier acting on the constant function `1`). -/
lemma leakSwap_leakFn_sm (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) :
    StronglyMeasurable (Work.BoseFixB3.CS.leakFn fc κ ℓ) := by
  have h1m : Measurable (Work.BoseFixB3.CS.oneFn : E3 → ℝ) := measurable_const
  have h := Work.BoseFixB3.Conv.stronglyMeasurable_lowMult (fc := fc) (κ := κ) (ℓ := ℓ)
    (Ψ := Work.BoseFixB3.CS.oneFn) h1m
  show StronglyMeasurable
    (fun y : E3 => 1 - Work.BoseBoxFix.lowMult fc κ ℓ Work.BoseFixB3.CS.oneFn y)
  exact stronglyMeasurable_const.sub h

/-- **The inner `x`-integral, rewritten.** For `ℓ > 0` the `x`-integral over the box of
`χ_Λ(x) F(x−y)` is the full-space integral of the translate `z ↦ χ_Λ(z+y) F(z)`. -/
lemma leakSwap_inner {ℓ : ℝ} (hℓ : 0 < ℓ) (y : E3) (F : E3 → ℝ) :
    (∫ x in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.chiU ℓ 0 x * F (x - y) * Submission.BoseGases.chiU ℓ 0 y)
      = Submission.BoseGases.chiU ℓ 0 y *
          ∫ z, Submission.BoseGases.chiU ℓ 0 (z + y) * F z := by
  have hmain : (∫ x in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.chiU ℓ 0 x * F (x - y))
      = ∫ x, Submission.BoseGases.chiU ℓ 0 x * F (x - y) :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [leakSwap_chiU_zero_off ℓ hℓ x hx, zero_mul])
  have htrans : (∫ x, Submission.BoseGases.chiU ℓ 0 x * F (x - y))
      = ∫ z, Submission.BoseGases.chiU ℓ 0 (z + y) * F z := by
    rw [← MeasureTheory.integral_sub_right_eq_self
      (fun z : E3 => Submission.BoseGases.chiU ℓ 0 (z + y) * F z) y]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp [sub_add_cancel])
  rw [MeasureTheory.integral_mul_const, hmain, htrans]
  exact mul_comm _ _

/-! ## Joint integrability of the double integrand -/

/-- The joint integrand `(y,z) ↦ 1_Λ(y) (L y χ_Λ(y)) χ_Λ(y+z) F z` is integrable on the
product measure: it is dominated by `1_Λ(y) |B| ‖χ_Λ‖_∞² |F z|`. -/
lemma leakSwap_integrable {fc : Work.BoseBoxFix.LowCut} {κ ℓ B : ℝ} (hℓ : 0 < ℓ)
    (hB : ∀ y : E3, |Work.BoseFixB3.CS.leakFn fc κ ℓ y| ≤ B) {F : E3 → ℝ}
    (hF : Integrable F) :
    Integrable (Function.uncurry (fun y z : E3 =>
        if y ∈ Submission.BoseGases.acube ℓ then
          ((Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y) *
            Submission.BoseGases.chiU ℓ 0 (z + y)) * F z
        else 0))
      (volume.prod volume) := by
  obtain ⟨C, hCnn, hC⟩ := leakSwap_chiU_abs_le ℓ 0
  have hscM : MeasurableSet (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_measurable ℓ
  have hsctop : volume (Submission.BoseGases.acube ℓ) ≠ ⊤ :=
    ne_of_lt (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
  have hOne : Integrable
      ((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ))) volume := by
    rw [MeasureTheory.integrable_indicator_iff hscM]
    exact MeasureTheory.integrableOn_const (hs := hsctop)
  have hKind : Integrable
      ((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => |B| * C * C)) volume := by
    have hcongr : (fun x : E3 => (|B| * C * C) *
          ((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) x))
        = ((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => |B| * C * C)) := by
      funext x
      by_cases hx : x ∈ Submission.BoseGases.acube ℓ
      · simp only [Set.indicator_of_mem hx, mul_one]
      · simp only [Set.indicator_of_notMem hx, mul_zero]
    simpa only [hcongr] using hOne.const_mul (|B| * C * C)
  have hD : Integrable (fun p : E3 × E3 =>
      (Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => |B| * C * C) p.1 *
        |F p.2|) (volume.prod volume) := hKind.mul_prod hF.abs
  have hAESM : AEStronglyMeasurable (Function.uncurry (fun y z : E3 =>
        if y ∈ Submission.BoseGases.acube ℓ then
          ((Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y) *
            Submission.BoseGases.chiU ℓ 0 (z + y)) * F z
        else 0)) (volume.prod volume) := by
    have hchi_eq : (fun x : E3 => Submission.BoseGases.chiU ℓ 0 x)
        = fun x : E3 => Submission.BoseGases.chi ((ℓ⁻¹ : ℝ) • x) := by
      funext x; simp [Submission.BoseGases.chiU]
    have hchi_cont : Continuous (fun x : E3 => Submission.BoseGases.chiU ℓ 0 x) := by
      rw [hchi_eq]
      exact Submission.BoseGases.chi_continuous.comp
        ((continuous_id : Continuous fun x : E3 => x).const_smul (ℓ⁻¹))
    have hL : AEStronglyMeasurable
        (fun p : E3 × E3 => Work.BoseFixB3.CS.leakFn fc κ ℓ p.1) (volume.prod volume) :=
      (leakSwap_leakFn_sm fc κ ℓ).aestronglyMeasurable.comp_fst
    have hc1 : AEStronglyMeasurable
        (fun p : E3 × E3 => Submission.BoseGases.chiU ℓ 0 p.1) (volume.prod volume) :=
      hchi_cont.aestronglyMeasurable.comp_fst
    have hc2 : AEStronglyMeasurable
        (fun p : E3 × E3 => Submission.BoseGases.chiU ℓ 0 (p.2 + p.1))
        (volume.prod volume) :=
      (hchi_cont.comp (continuous_snd.add continuous_fst)).aestronglyMeasurable
    have hF2 : AEStronglyMeasurable (fun p : E3 × E3 => F p.2) (volume.prod volume) :=
      hF.aestronglyMeasurable.comp_snd
    have hprod : AEStronglyMeasurable (fun p : E3 × E3 =>
        ((Work.BoseFixB3.CS.leakFn fc κ ℓ p.1 * Submission.BoseGases.chiU ℓ 0 p.1) *
          Submission.BoseGases.chiU ℓ 0 (p.2 + p.1)) * F p.2) (volume.prod volume) :=
      ((hL.mul hc1).mul hc2).mul hF2
    have hind := hprod.indicator (hscM.prod MeasurableSet.univ)
    have heq : Function.uncurry (fun y z : E3 =>
          if y ∈ Submission.BoseGases.acube ℓ then
            ((Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y) *
              Submission.BoseGases.chiU ℓ 0 (z + y)) * F z
          else 0)
        = (Submission.BoseGases.acube ℓ ×ˢ (Set.univ : Set E3)).indicator
            (fun p : E3 × E3 =>
              ((Work.BoseFixB3.CS.leakFn fc κ ℓ p.1 * Submission.BoseGases.chiU ℓ 0 p.1) *
                Submission.BoseGases.chiU ℓ 0 (p.2 + p.1)) * F p.2) := by
      funext p
      by_cases hp : p.1 ∈ Submission.BoseGases.acube ℓ
      · simp only [Function.uncurry, if_pos hp,
          Set.indicator_of_mem (show p ∈ Submission.BoseGases.acube ℓ ×ˢ (Set.univ : Set E3)
            from ⟨hp, Set.mem_univ _⟩)]
      · have hp' : p ∉ Submission.BoseGases.acube ℓ ×ˢ (Set.univ : Set E3) := fun h => hp h.1
        simp only [Function.uncurry, if_neg hp, Set.indicator_of_notMem hp']
    rw [heq]
    exact hind
  refine MeasureTheory.Integrable.mono' hD hAESM (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs]
  by_cases hp : p.1 ∈ Submission.BoseGases.acube ℓ
  · simp only [Function.uncurry, if_pos hp, Set.indicator_of_mem hp]
    have h1 : |Work.BoseFixB3.CS.leakFn fc κ ℓ p.1| ≤ |B| :=
      le_trans (hB p.1) (le_abs_self B)
    have h2 : |Submission.BoseGases.chiU ℓ 0 p.1| ≤ C := hC p.1
    have h3 : |Submission.BoseGases.chiU ℓ 0 (p.2 + p.1)| ≤ C := hC _
    have habs : |((Work.BoseFixB3.CS.leakFn fc κ ℓ p.1 * Submission.BoseGases.chiU ℓ 0 p.1) *
        Submission.BoseGases.chiU ℓ 0 (p.2 + p.1)) * F p.2|
        = (|Work.BoseFixB3.CS.leakFn fc κ ℓ p.1| * |Submission.BoseGases.chiU ℓ 0 p.1| *
            |Submission.BoseGases.chiU ℓ 0 (p.2 + p.1)|) * |F p.2| := by
      simp only [abs_mul]
    rw [habs]
    calc (|Work.BoseFixB3.CS.leakFn fc κ ℓ p.1| * |Submission.BoseGases.chiU ℓ 0 p.1| *
            |Submission.BoseGases.chiU ℓ 0 (p.2 + p.1)|) * |F p.2|
        ≤ ((|B| * C) * C) * |F p.2| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg B)) h3 (abs_nonneg _)
              (mul_nonneg (abs_nonneg B) hCnn)) (abs_nonneg _)
      _ = (|B| * C * C) * |F p.2| := by ring
  · simp only [Function.uncurry, if_neg hp, Set.indicator_of_notMem hp]
    simp

theorem leakCoupl_swap :
    ∀ (fc : Work.BoseBoxFix.LowCut) (κ ℓ B : ℝ), 0 < κ → 0 < ℓ →
      (∀ y : EuclideanSpace ℝ (Fin 3), |Work.BoseFixB3.CS.leakFn fc κ ℓ y| ≤ B) →
      ∀ (F : EuclideanSpace ℝ (Fin 3) → ℝ), MeasureTheory.Integrable F →
        (∫ y in Submission.BoseGases.acube ℓ,
            Work.BoseFixB3.CS.leakFn fc κ ℓ y *
              (∫ x in Submission.BoseGases.acube ℓ,
                Submission.BoseGases.chiU ℓ 0 x * F (x - y) * Submission.BoseGases.chiU ℓ 0 y))
          = ∫ z : EuclideanSpace ℝ (Fin 3), F z *
              (∫ y in Submission.BoseGases.acube ℓ,
                Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y *
                  Submission.BoseGases.chiU ℓ 0 (y + z)) := by
  intro fc κ ℓ B hκ hℓ hB F hF
  classical
  set f : E3 → E3 → ℝ := fun y z => if y ∈ Submission.BoseGases.acube ℓ then
      ((Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y) *
        Submission.BoseGases.chiU ℓ 0 (z + y)) * F z else 0 with hf
  -- ### Step 1: the inner `x`-integral, rewritten
  have step1 : ∀ y : E3, Work.BoseFixB3.CS.leakFn fc κ ℓ y *
      (∫ x in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.chiU ℓ 0 x * F (x - y) * Submission.BoseGases.chiU ℓ 0 y)
      = ∫ z, f y z := by
    intro y
    rw [leakSwap_inner hℓ y F]
    rw [← MeasureTheory.integral_const_mul (Submission.BoseGases.chiU ℓ 0 y)
      (fun z : E3 => Submission.BoseGases.chiU ℓ 0 (z + y) * F z)]
    rw [← MeasureTheory.integral_const_mul (Work.BoseFixB3.CS.leakFn fc κ ℓ y)
      (fun z : E3 => Submission.BoseGases.chiU ℓ 0 y *
        (Submission.BoseGases.chiU ℓ 0 (z + y) * F z))]
    by_cases hy : y ∈ Submission.BoseGases.acube ℓ
    · have hcongr : (fun z : E3 => Work.BoseFixB3.CS.leakFn fc κ ℓ y *
          (Submission.BoseGases.chiU ℓ 0 y *
            (Submission.BoseGases.chiU ℓ 0 (z + y) * F z))) = fun z : E3 => f y z := by
        funext z
        simp only [hf, if_pos hy]
        ring
      rw [hcongr]
    · have hz0 : (fun z : E3 => Work.BoseFixB3.CS.leakFn fc κ ℓ y *
          (Submission.BoseGases.chiU ℓ 0 y *
            (Submission.BoseGases.chiU ℓ 0 (z + y) * F z))) = fun _ => (0 : ℝ) := by
        funext z
        rw [leakSwap_chiU_zero_off ℓ hℓ y hy, zero_mul, mul_zero]
      have hfz : (fun z : E3 => f y z) = fun _ => (0 : ℝ) := by
        funext z
        simp only [hf, if_neg hy]
      rw [hz0, hfz, MeasureTheory.integral_zero]
  -- ### Step 2: the left-hand side is the double integral of `f`
  have hLHS : (∫ y in Submission.BoseGases.acube ℓ,
        Work.BoseFixB3.CS.leakFn fc κ ℓ y *
          (∫ x in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.chiU ℓ 0 x * F (x - y) * Submission.BoseGases.chiU ℓ 0 y))
      = ∫ y, ∫ z, f y z := by
    have hpoint : ∀ y : E3, (Submission.BoseGases.acube ℓ).indicator
          (fun y : E3 => Work.BoseFixB3.CS.leakFn fc κ ℓ y *
            (∫ x in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.chiU ℓ 0 x * F (x - y) *
                Submission.BoseGases.chiU ℓ 0 y)) y
        = ∫ z, f y z := by
      intro y
      by_cases hy : y ∈ Submission.BoseGases.acube ℓ
      · rw [Set.indicator_of_mem hy, step1 y]
      · rw [Set.indicator_of_notMem hy]
        have hfz : (fun z : E3 => f y z) = fun _ => (0 : ℝ) := by
          funext z
          simp only [hf, if_neg hy]
        rw [hfz, MeasureTheory.integral_zero]
    rw [← MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
    simp only [hpoint]
  -- ### Step 3: Fubini
  have hInt : Integrable (Function.uncurry f) (volume.prod volume) := by
    have h := leakSwap_integrable (fc := fc) (κ := κ) (ℓ := ℓ) (B := B) hℓ hB hF
    simpa only [hf] using h
  have hswap : (∫ y, ∫ z, f y z) = ∫ z, ∫ y, f y z :=
    MeasureTheory.integral_integral_swap (f := f) hInt
  -- ### Step 4: the right-hand side is the double integral of `f`
  have hRHS : (∫ z, ∫ y, f y z) = ∫ z : E3, F z *
        (∫ y in Submission.BoseGases.acube ℓ,
          Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y *
            Submission.BoseGases.chiU ℓ 0 (y + z)) := by
    have hpoint : ∀ z : E3, (∫ y, f y z) = F z *
        (∫ y in Submission.BoseGases.acube ℓ,
          Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y *
            Submission.BoseGases.chiU ℓ 0 (y + z)) := by
      intro z
      have h1 : (∫ y, f y z) = ∫ y in Submission.BoseGases.acube ℓ,
          ((Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y) *
            Submission.BoseGases.chiU ℓ 0 (z + y)) * F z := by
        rw [← MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        by_cases hy : y ∈ Submission.BoseGases.acube ℓ
        · simp only [hf, if_pos hy, Set.indicator_of_mem hy]
        · simp only [hf, if_neg hy, Set.indicator_of_notMem hy]
      rw [h1, MeasureTheory.integral_mul_const]
      have h2 : (∫ y in Submission.BoseGases.acube ℓ,
            (Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y) *
              Submission.BoseGases.chiU ℓ 0 (z + y))
          = ∫ y in Submission.BoseGases.acube ℓ,
              Work.BoseFixB3.CS.leakFn fc κ ℓ y * Submission.BoseGases.chiU ℓ 0 y *
                Submission.BoseGases.chiU ℓ 0 (y + z) := by
        refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
          (fun y _ => ?_)
        rw [add_comm z y]
      rw [h2]
      exact mul_comm _ _
    simp only [hpoint]
  rw [hLHS, hswap, hRHS]

end Work.BoseFixB3.CS.Pieces
