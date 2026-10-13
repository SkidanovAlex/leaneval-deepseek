/-
Copyright: work module for the Elgindi finite-time singularity project.

# `pPureShiftAux/MajEst` — the `u`-average majorant of the radial difference quotient

The pointwise domination of `PPureShiftRad.Basic`

  `HkIntegrand α 0 (dq c g) z θ ≤ (c-1)⁻¹ ∫_1^c u² HkIntegrand α 0 (D_z g) (z u) θ du`

says that the `ℋ⁰`-integrand of the difference quotient is dominated by the `u`-average `Maj` of
the `ℋ⁰`-integrand of the radial derivative `D_z g`.  This module integrates that domination: the
`ℋ⁰`-lintegral of `Maj` is at most `c³` times the `ℋ⁰`-lintegral of `D_z g`.

The two structural facts are

* the multiplicative substitution `z ↦ z u` in the radial variable
  (`AngSecond.lintegral_Ioi_comp_mul_pos`), which is what turns the difference quotient into a
  radial derivative (the Jacobian `u⁻¹` cancels the `u²` of the majorant, leaving `u`);
* Tonelli's theorem on the product of the quadrant measure with `du` on `(1,c)`, whose
  `AEMeasurable` hypotheses come from *continuity on the open sets*.

Everything is stated for an abstract `Φ : ℝ → ℝ → ℝ` (with `Φ = HkIntegrand α 0 (D_z g)` in the
intended instantiation), so that the elaborator never has to unfold the (large) definition of
`HkIntegrand` inside a `ContinuousOn` statement.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cores.Dil.DilBasic
import Submission.Work.FTS.EllipticEst.Cores.Dil.HkSqLimit
import Submission.Work.FTS.EllipticEst.AngSecond.lintegral_w_sq_shift_two_le
import Submission.Work.FTS.EllipticEst.AngSecond.ofReal_intervalIntegral_eq_lintegral
import Submission.Work.FTS.EllipticEst.Cores.PPureShiftRad.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.pPureShiftAux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The quadrant measure, in this file's namespace. -/
abbrev qM : MeasureTheory.Measure (ℝ × ℝ) := Work.FTS.EllipticEst.Cores.Dil.quadMeasure

/-- The quadrant measure with the radial variable restricted to the *open* half-line; the two
differ only by the null set `{z = 0}`. -/
theorem qM_eq_ioi :
    qM = (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  show (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) = _
  rw [MeasureTheory.restrict_Ioi_eq_restrict_Ici (a := (0 : ℝ))]

/-- The reverse orientation of `qM_eq_ioi`. -/
theorem ioi_prod_eq_qM :
    (MeasureTheory.volume.restrict (Set.Ioi 0)).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) = qM := qM_eq_ioi.symm

/-- `qM` as the restriction of the two-dimensional Lebesgue measure to the closed quadrant. -/
theorem qM_eq_restrict :
    qM = ((MeasureTheory.volume : Measure ℝ).prod MeasureTheory.volume).restrict
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  show ((MeasureTheory.volume : Measure ℝ).restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) = _
  rw [MeasureTheory.Measure.prod_restrict]

/-- **The `u`-average majorant** of `Φ` over the segment `[z, cz]`: with `Φ` the `ℋ⁰`-integrand
of `D_z g` it dominates the `ℋ⁰`-integrand of the difference quotient `dq c g`. -/
def Maj (c : ℝ) (Φ : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c, u ^ 2 * Φ (z * u) θ

theorem Maj_nonneg {c : ℝ} {Φ : ℝ → ℝ → ℝ} (hc : 1 < c) (hnn : ∀ z θ, 0 ≤ Φ z θ)
    (z θ : ℝ) : 0 ≤ Maj c Φ z θ := by
  refine mul_nonneg (inv_nonneg.mpr (by linarith)) ?_
  refine intervalIntegral.integral_nonneg (le_of_lt hc) ?_
  intro u _
  exact mul_nonneg (sq_nonneg u) (hnn _ _)

/-! ## Change of variables in the lower Lebesgue integral on an interval -/

/-- **Change of variables** `u ↦ z * u` (`z > 0`) for the lower Lebesgue integral over an open
interval.  No measurability of `F` is required. -/
theorem lintegral_Ioo_comp_mul_pos {a b z : ℝ} (hz : 0 < z) (F : ℝ → ENNReal) :
    (∫⁻ u in Set.Ioo a b, F (z * u))
      = ENNReal.ofReal z⁻¹ * ∫⁻ s in Set.Ioo (z * a) (z * b), F s := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hmem : ∀ u : ℝ, u ∈ Set.Ioo a b ↔ z * u ∈ Set.Ioo (z * a) (z * b) := by
    intro u
    simp only [Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith [hz], by nlinarith [hz]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith [hz], by nlinarith [hz]⟩
  have hmain : ∀ H : ℝ → ENNReal,
      (∫⁻ u, H (z * u)) = ENNReal.ofReal z⁻¹ * ∫⁻ s, H s := by
    intro H
    let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ z hz0).toMeasurableEquiv
    have he : ⇑e = (fun u : ℝ => z * u) := rfl
    have hmap : Measure.map (⇑e) MeasureTheory.volume =
        ENNReal.ofReal z⁻¹ • MeasureTheory.volume := by
      rw [he, Real.map_volume_mul_left hz0, abs_of_pos (inv_pos.mpr hz)]
    calc ∫⁻ u, H (z * u)
        = ∫⁻ u, H (e u) := by rw [he]
      _ = ∫⁻ u, H u ∂(Measure.map (⇑e) MeasureTheory.volume) :=
            (lintegral_map_equiv H e).symm
      _ = ∫⁻ u, H u ∂(ENNReal.ofReal z⁻¹ • MeasureTheory.volume) := by rw [hmap]
      _ = ENNReal.ofReal z⁻¹ * ∫⁻ u, H u := by
            rw [lintegral_smul_measure, smul_eq_mul]
  calc (∫⁻ u in Set.Ioo a b, F (z * u))
      = ∫⁻ u, (Set.Ioo a b).indicator (fun u => F (z * u)) u :=
        (MeasureTheory.lintegral_indicator measurableSet_Ioo (fun u => F (z * u))).symm
    _ = ∫⁻ u, (Set.Ioo (z * a) (z * b)).indicator F (z * u) := by
        refine lintegral_congr fun u => ?_
        by_cases h : u ∈ Set.Ioo a b
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmem u).mp h)]
        · rw [Set.indicator_of_notMem h,
            Set.indicator_of_notMem (fun hc => h ((hmem u).mpr hc))]
    _ = ENNReal.ofReal z⁻¹ * ∫⁻ s, (Set.Ioo (z * a) (z * b)).indicator F s := hmain _
    _ = ENNReal.ofReal z⁻¹ * ∫⁻ s in Set.Ioo (z * a) (z * b), F s := by
        rw [MeasureTheory.lintegral_indicator measurableSet_Ioo F]

/-! ## Continuity and a.e. measurability of the shifted integrands -/

/-- The uncurried shifted composite `(q.1.1 * q.2, q.1.2) ↦ Φ (q.1.1 * q.2) q.1.2` is
continuous on the product of the open quadrant with the open half-line. -/
theorem continuousOn_comp_mul_quad {Φ : ℝ → ℝ → ℝ}
    (hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun q : (ℝ × ℝ) × ℝ => Φ (q.1.1 * q.2) q.1.2)
      ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ Set.Ioi (0 : ℝ)) := by
  have hmap : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => (q.1.1 * q.2, q.1.2))
      ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ Set.Ioi (0 : ℝ)) :=
    (((continuous_fst.comp continuous_fst).mul continuous_snd).prodMk
      (continuous_snd.comp continuous_fst)).continuousOn
  have hms : Set.MapsTo (fun q : (ℝ × ℝ) × ℝ => (q.1.1 * q.2, q.1.2))
      ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ Set.Ioi (0 : ℝ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    intro q hq
    show 0 < q.1.1 * q.2 ∧ q.1.2 ∈ Set.Ioo 0 (Real.pi / 2)
    exact ⟨mul_pos hq.1.1 hq.2, hq.1.2⟩
  exact hΦ.comp hmap hms

/-- **A.e. measurability of the pair integrand** `(θ, u) ↦ u² Φ (z u) θ`, on
`Iθ × (1, c)`, from continuity of `Φ` on the open quadrant. -/
theorem aemeasurable_shift_pair {Φ : ℝ → ℝ → ℝ}
    (hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z c : ℝ} (hz : 0 < z) (hc : 1 < c) :
    AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (q.2 ^ 2 * Φ (z * q.2) q.1))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) c))) := by
  have hcont : ContinuousOn (fun q : ℝ × ℝ => q.2 ^ 2 * Φ (z * q.2) q.1)
      (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo (1 : ℝ) c) := by
    refine ContinuousOn.mul ((continuous_snd.pow 2).continuousOn) ?_
    have hmap : ContinuousOn (fun q : ℝ × ℝ => (z * q.2, q.1))
        (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo (1 : ℝ) c) :=
      ((continuous_const.mul continuous_snd).prodMk continuous_fst).continuousOn
    have hms : Set.MapsTo (fun q : ℝ × ℝ => (z * q.2, q.1))
        (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo (1 : ℝ) c)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      intro q hq
      show 0 < z * q.2 ∧ q.1 ∈ Set.Ioo 0 (Real.pi / 2)
      exact ⟨mul_pos hz (lt_trans zero_lt_one hq.2.1), hq.1⟩
    exact hΦ.comp hmap hms
  have hce : ContinuousOn (fun q : ℝ × ℝ => ENNReal.ofReal (q.2 ^ 2 * Φ (z * q.2) q.1))
      (Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Ioo (1 : ℝ) c) :=
    ENNReal.continuous_ofReal.comp_continuousOn hcont
  have hIθ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  rw [hIθ, MeasureTheory.Measure.prod_restrict]
  exact hce.aemeasurable ((isOpen_Ioo.prod isOpen_Ioo).measurableSet)

/-- **A.e. measurability of the triple integrand** `(p, u) ↦ u² Φ (p.1 u) p.2`, on
`qM ⊗ du|_{(1,c)}`, from continuity of `Φ` on the open quadrant. -/
theorem aemeasurable_shift_triple {Φ : ℝ → ℝ → ℝ}
    (hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {c : ℝ} (hc : 1 < c) :
    AEMeasurable (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal (q.2 ^ 2 * Φ (q.1.1 * q.2) q.1.2))
      (qM.prod (MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) c))) := by
  have hcont : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => q.2 ^ 2 * Φ (q.1.1 * q.2) q.1.2)
      ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ Set.Ioo (1 : ℝ) c) := by
    refine ContinuousOn.mul ((continuous_snd.pow 2).continuousOn) ?_
    have hmap : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => (q.1.1 * q.2, q.1.2))
        ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ Set.Ioo (1 : ℝ) c) :=
      (((continuous_fst.comp continuous_fst).mul continuous_snd).prodMk
        (continuous_snd.comp continuous_fst)).continuousOn
    have hms : Set.MapsTo (fun q : (ℝ × ℝ) × ℝ => (q.1.1 * q.2, q.1.2))
        ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ Set.Ioo (1 : ℝ) c)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      intro q hq
      exact ⟨mul_pos hq.1.1 (lt_trans zero_lt_one hq.2.1), hq.1.2⟩
    exact hΦ.comp hmap hms
  have hce : ContinuousOn
      (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal (q.2 ^ 2 * Φ (q.1.1 * q.2) q.1.2))
      ((Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ×ˢ Set.Ioo (1 : ℝ) c) :=
    ENNReal.continuous_ofReal.comp_continuousOn hcont
  have hIθ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  rw [qM_eq_ioi, hIθ, MeasureTheory.Measure.prod_restrict,
    MeasureTheory.Measure.prod_restrict]
  exact hce.aemeasurable ((isOpen_Ioi.prod isOpen_Ioo).prod isOpen_Ioo).measurableSet

/-! ## The pointwise expansion of the majorant -/

/-- `ofReal` of the majorant is the `u`-lintegral of the shifted integrand: for `z > 0` and
`θ ∈ Iθ`,

  `ofReal (Maj c Φ z θ) = ofReal ((c-1)⁻¹) ∫⁻ u ∈ (1,c), ofReal (u² Φ (z u) θ)`. -/
theorem ofReal_Maj_eq {Φ : ℝ → ℝ → ℝ} {c : ℝ} (hc : 1 < c) (hnn : ∀ z θ, 0 ≤ Φ z θ)
    (hcontu : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousOn (fun u : ℝ => u ^ 2 * Φ (z * u) θ) (Set.Icc (1 : ℝ) c)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      ENNReal.ofReal (Maj c Φ z θ)
        = ENNReal.ofReal ((c - 1)⁻¹) * ∫⁻ u in Set.Ioo (1 : ℝ) c,
            ENNReal.ofReal (u ^ 2 * Φ (z * u) θ) := by
  intro z hz θ hθ
  have hc1 : (1 : ℝ) ≤ c := le_of_lt hc
  have hcnn : (0 : ℝ) ≤ c - 1 := by linarith
  show ENNReal.ofReal ((c - 1)⁻¹ * ∫ u in (1 : ℝ)..c, u ^ 2 * Φ (z * u) θ) = _
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hcnn)]
  congr 1
  exact Work.FTS.EllipticEst.AngSecond.ofReal_intervalIntegral_eq_lintegral hc1
    (hcontu z (Set.mem_Ici.mpr (le_of_lt hz)) θ hθ)
    (fun u _ => mul_nonneg (sq_nonneg u) (hnn (z * u) θ))

/-! ## A.e. measurability on the quadrant from continuity on the open quadrant -/

/-- If `Φ` is continuous on the open quadrant then `ofReal ∘ Φ` is a.e.-measurable for the
quadrant measure: the open quadrant differs from `Iz × Iθ` by the null set
`{z = 0} ∪ {θ = 0} ∪ {θ = π/2}`. -/
theorem aemeasurable_ofReal_Q0 {Φ : ℝ → ℝ → ℝ}
    (hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Φ p.1 p.2)) qM := by
  have hce : ContinuousOn (fun p : ℝ × ℝ => ENNReal.ofReal (Φ p.1 p.2))
      Work.FTS.EllipticEst.Q0 :=
    ENNReal.continuous_ofReal.comp_continuousOn hΦ
  have hIθ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm
  rw [qM_eq_ioi, hIθ, MeasureTheory.Measure.prod_restrict]
  exact hce.aemeasurable ((isOpen_Ioi.prod isOpen_Ioo).measurableSet)

/-- The shift `p ↦ (p.1 * u, p.2)` of a function continuous on the open quadrant is again
continuous on the open quadrant, for `u > 0`. -/
theorem continuousOn_shift_fst {Φ : ℝ → ℝ → ℝ}
    (hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0)
    {u : ℝ} (hu : 0 < u) :
    ContinuousOn (fun p : ℝ × ℝ => Φ (p.1 * u) p.2) Work.FTS.EllipticEst.Q0 := by
  have hmap : ContinuousOn (fun p : ℝ × ℝ => (p.1 * u, p.2)) Work.FTS.EllipticEst.Q0 :=
    ((continuous_fst.mul continuous_const).prodMk continuous_snd).continuousOn
  have hms : Set.MapsTo (fun p : ℝ × ℝ => (p.1 * u, p.2))
      Work.FTS.EllipticEst.Q0 Work.FTS.EllipticEst.Q0 := by
    intro p hp
    show 0 < p.1 * u ∧ p.2 ∈ Set.Ioo 0 (Real.pi / 2)
    exact ⟨mul_pos hp.1 hu, hp.2⟩
  exact hΦ.comp hmap hms

/-- **The multiplicative substitution in the radial variable** for the quadrant measure:
`∫⁻ p, ofReal (Φ (p.1 u) p.2) = u⁻¹ ∫⁻ p, ofReal (Φ p.1 p.2)` for `u > 0`. -/
theorem lintegral_shift_Phi {Φ : ℝ → ℝ → ℝ}
    (hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0)
    {u : ℝ} (hu : 0 < u) :
    (∫⁻ p, ENNReal.ofReal (Φ (p.1 * u) p.2) ∂qM)
      = ENNReal.ofReal u⁻¹ * ∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM := by
  have hmeas1 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Φ (p.1 * u) p.2))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [← qM_eq_ioi]
    exact aemeasurable_ofReal_Q0 (Φ := fun a b => Φ (a * u) b) (continuousOn_shift_fst hΦ hu)
  have hmeas2 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Φ p.1 p.2))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [← qM_eq_ioi]
    exact aemeasurable_ofReal_Q0 hΦ
  rw [qM_eq_ioi, MeasureTheory.lintegral_prod _ hmeas1,
    MeasureTheory.lintegral_prod _ hmeas2]
  have hswap : (∫⁻ z in Set.Ioi 0,
      ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Φ (z * u) θ))
      = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Φ (u * z) θ) := by
    refine lintegral_congr fun z => lintegral_congr fun θ => ?_
    rw [mul_comm]
  rw [hswap]
  exact Work.FTS.EllipticEst.AngSecond.lintegral_Ioi_comp_mul_pos u hu
    (fun s : ℝ => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Φ s θ))

/-! ## The `ℋ⁰`-lintegral of the majorant -/

/-- **The majorant estimate**: the `ℋ⁰`-lintegral of `Maj c Φ` is at most `c³` times the
`ℋ⁰`-lintegral of `Φ`. -/
theorem lintegral_Maj_le {Φ : ℝ → ℝ → ℝ} {c : ℝ} (hc : 1 < c) (hnn : ∀ z θ, 0 ≤ Φ z θ)
    (hΦc : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hcontu : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousOn (fun u : ℝ => u ^ 2 * Φ (z * u) θ) (Set.Icc (1 : ℝ) c)) :
    (∫⁻ p, ENNReal.ofReal (Maj c Φ p.1 p.2) ∂qM)
      ≤ ENNReal.ofReal (c ^ 3) * ∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM := by
  have hc1 : (1 : ℝ) ≤ c := le_of_lt hc
  have hcnn : (0 : ℝ) ≤ c - 1 := by linarith
  set K : ENNReal := ∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM with hK
  have hF : AEMeasurable
      (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal (q.2 ^ 2 * Φ (q.1.1 * q.2) q.1.2))
      (qM.prod (MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) c))) :=
    aemeasurable_shift_triple hΦc hc
  -- step 1: expand `ofReal (Maj ·)` a.e.
  have hae1 : ∀ᵐ p ∂qM, ENNReal.ofReal (Maj c Φ p.1 p.2)
      = ENNReal.ofReal ((c - 1)⁻¹) * ∫⁻ u in Set.Ioo (1 : ℝ) c,
          ENNReal.ofReal (u ^ 2 * Φ (p.1 * u) p.2) := by
    have hset : Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ
        =ᵐ[((MeasureTheory.volume : Measure ℝ).prod MeasureTheory.volume)]
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      MeasureTheory.Measure.set_prod_ae_eq
        (MeasureTheory.Ioi_ae_eq_Ici' (μ := MeasureTheory.volume) (a := (0 : ℝ)) (by simp))
        (Filter.EventuallyEq.rfl)
    rw [qM_eq_restrict, ← MeasureTheory.Measure.restrict_congr_set hset]
    refine MeasureTheory.ae_restrict_of_forall_mem
      (isOpen_Ioi.measurableSet.prod measurableSet_Icc) ?_
    intro p hp
    exact ofReal_Maj_eq hc hnn hcontu p.1 hp.1 p.2 hp.2
  rw [lintegral_congr_ae hae1,
    MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- step 2: Tonelli, swapping `p` and `u`
  have hswap :
      MeasureTheory.lintegral qM (fun p : ℝ × ℝ =>
          MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) c))
            (fun u : ℝ => ENNReal.ofReal (u ^ 2 * Φ (p.1 * u) p.2)))
        = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) c))
            (fun u : ℝ => MeasureTheory.lintegral qM
              (fun p : ℝ × ℝ => ENNReal.ofReal (u ^ 2 * Φ (p.1 * u) p.2))) :=
    MeasureTheory.lintegral_lintegral_swap
      (f := fun (p : ℝ × ℝ) (u : ℝ) => ENNReal.ofReal (u ^ 2 * Φ (p.1 * u) p.2)) hF
  rw [hswap]
  -- step 3: the value of the inner integral
  have hpoint : ∀ u ∈ Set.Ioo (1 : ℝ) c,
      (∫⁻ p, ENNReal.ofReal (u ^ 2 * Φ (p.1 * u) p.2) ∂qM) = ENNReal.ofReal u * K := by
    intro u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu.1
    calc (∫⁻ p, ENNReal.ofReal (u ^ 2 * Φ (p.1 * u) p.2) ∂qM)
        = ∫⁻ p, ENNReal.ofReal (u ^ 2) * ENNReal.ofReal (Φ (p.1 * u) p.2) ∂qM :=
          lintegral_congr fun p => by rw [ENNReal.ofReal_mul (sq_nonneg u)]
      _ = ENNReal.ofReal (u ^ 2) * (∫⁻ p, ENNReal.ofReal (Φ (p.1 * u) p.2) ∂qM) :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (u ^ 2) * (ENNReal.ofReal u⁻¹ * K) := by
          rw [lintegral_shift_Phi hΦc hu0]
      _ = ENNReal.ofReal u * K := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg u),
            show u ^ 2 * u⁻¹ = u by field_simp]
  rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo hpoint]
  rw [MeasureTheory.lintegral_mul_const K (f := fun u : ℝ => ENNReal.ofReal u)
    (ENNReal.measurable_ofReal.comp measurable_id)]
  -- step 4: the `u`-integral and the arithmetic
  have hvalue : (∫⁻ u in Set.Ioo (1 : ℝ) c, ENNReal.ofReal u)
      = ENNReal.ofReal ((c ^ 2 - 1) / 2) := by
    have h1 : (∫ x in (1 : ℝ)..c, x) = (c ^ 2 - 1) / 2 := by
      rw [integral_id]; ring
    rw [← h1]
    exact (Work.FTS.EllipticEst.AngSecond.ofReal_intervalIntegral_eq_lintegral
      (a := (1 : ℝ)) (b := c) (f := fun u : ℝ => u) hc1 continuousOn_id
      (fun u hu => by linarith [hu.1])).symm
  have hcc : (c - 1)⁻¹ * ((c ^ 2 - 1) / 2) = (c + 1) / 2 := by
    have hcne : c - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hvalue, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hcnn), hcc]
  gcongr
  have h2 : c ≤ c ^ 3 := by nlinarith [hc]
  linarith

/-! ## The `θ`-slice and `z`-integral integrability of the majorant -/

/-- **The `u`-average bound.**  For `z > 0`,
`∫⁻_{u ∈ (1,c)} ofReal u² · ofReal (∫_θ Φ (z u) θ) ≤ c² · z⁻¹ · ∫⁻ Φ`. -/
theorem lintegral_shift_mul_bound {Φ : ℝ → ℝ → ℝ} {c : ℝ} (hc : 1 < c)
    (hnn : ∀ z θ, 0 ≤ Φ z θ)
    (hΦc : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hΦint : ∀ s ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Φ s θ) Work.Spaces.Iθ)
    {z : ℝ} (hz : 0 < z) :
    (∫⁻ u in Set.Ioo (1 : ℝ) c, ENNReal.ofReal (u ^ 2) *
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Φ (z * u) θ))
      ≤ ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal z⁻¹ *
          ∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM) := by
  have hbound2 : ∀ u ∈ Set.Ioo (1 : ℝ) c,
      ENNReal.ofReal (u ^ 2) ≤ ENNReal.ofReal (c ^ 2) := by
    intro u hu
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [hu.1, hu.2]
  calc (∫⁻ u in Set.Ioo (1 : ℝ) c, ENNReal.ofReal (u ^ 2) *
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Φ (z * u) θ))
      ≤ (∫⁻ u in Set.Ioo (1 : ℝ) c, ENNReal.ofReal (c ^ 2) *
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Φ (z * u) θ)) := by
        refine lintegral_mono_ae ?_
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
        exact Filter.Eventually.of_forall fun u hu =>
          mul_le_mul_of_nonneg_right (hbound2 u hu) (by positivity)
    _ = ENNReal.ofReal (c ^ 2) * (∫⁻ u in Set.Ioo (1 : ℝ) c,
          ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Φ (z * u) θ)) := by
        rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal z⁻¹ *
          (∫⁻ s in Set.Ioo z (z * c),
            ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Φ s θ))) := by
        rw [lintegral_Ioo_comp_mul_pos hz
          (fun s => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Φ s θ))]
        simp only [mul_one]
    _ ≤ ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal z⁻¹ *
          (∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (by positivity)
        calc (∫⁻ s in Set.Ioo z (z * c),
              ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Φ s θ))
            = ∫⁻ s in Set.Ioo z (z * c), ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (Φ s θ) := by
              refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo ?_
              intro s hs
              have hsIz : s ∈ Work.Spaces.Iz := le_of_lt (lt_trans hz hs.1)
              exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hΦint s hsIz)
                (Filter.Eventually.of_forall fun θ => hnn s θ)
          _ ≤ ∫⁻ s in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (Φ s θ) :=
              MeasureTheory.lintegral_mono_set (fun s hs => lt_trans hz hs.1)
          _ = ∫⁻ s in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (Φ s θ) :=
              MeasureTheory.setLIntegral_congr
                (MeasureTheory.Ioi_ae_eq_Ici' (μ := MeasureTheory.volume) (a := (0 : ℝ))
                  (by simp))
          _ = ∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM :=
              (MeasureTheory.lintegral_prod _ (aemeasurable_ofReal_Q0 hΦc)).symm

/-- **The `θ`-slice bound for the majorant.**  For `z > 0` the `ℋ⁰`-lintegral of `Maj c Φ z ·`
is finite, with an explicit bound in terms of the total `ℋ⁰`-lintegral of `Φ`. -/
theorem lintegral_Maj_theta_le {Φ : ℝ → ℝ → ℝ} {c : ℝ} (hc : 1 < c)
    (hnn : ∀ z θ, 0 ≤ Φ z θ)
    (hΦc : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hcontu : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousOn (fun u : ℝ => u ^ 2 * Φ (z * u) θ) (Set.Icc (1 : ℝ) c))
    (hΦint : ∀ s ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Φ s θ) Work.Spaces.Iθ)
    {z : ℝ} (hz : 0 < z) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Maj c Φ z θ))
      ≤ ENNReal.ofReal ((c - 1)⁻¹) * (ENNReal.ofReal (c ^ 2) *
          (ENNReal.ofReal z⁻¹ * ∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM)) := by
  have hc1 : (1 : ℝ) ≤ c := le_of_lt hc
  -- step 1: expand every `θ`-slice
  have hstep : ∀ θ ∈ Work.Spaces.Iθ, ENNReal.ofReal (Maj c Φ z θ)
      = ENNReal.ofReal ((c - 1)⁻¹) * ∫⁻ u in Set.Ioo (1 : ℝ) c,
          ENNReal.ofReal (u ^ 2 * Φ (z * u) θ) :=
    fun θ hθ => ofReal_Maj_eq hc hnn hcontu z (Set.mem_Ioi.mpr hz) θ hθ
  rw [MeasureTheory.setLIntegral_congr_fun (μ := MeasureTheory.volume)
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) hstep,
    MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- step 2: Tonelli in `(θ, u)`
  have hF : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal (q.2 ^ 2 * Φ (z * q.2) q.1))
      ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
        (MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) c))) :=
    aemeasurable_shift_pair hΦc hz hc
  have hswap :
      MeasureTheory.lintegral (MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (fun θ : ℝ => MeasureTheory.lintegral
            (MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) c))
            (fun u : ℝ => ENNReal.ofReal (u ^ 2 * Φ (z * u) θ)))
        = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) c))
            (fun u : ℝ => MeasureTheory.lintegral
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)
              (fun θ : ℝ => ENNReal.ofReal (u ^ 2 * Φ (z * u) θ))) :=
    MeasureTheory.lintegral_lintegral_swap
      (f := fun (θ : ℝ) (u : ℝ) => ENNReal.ofReal (u ^ 2 * Φ (z * u) θ)) hF
  rw [hswap]
  -- step 3: the value of the inner integral
  have hpoint : ∀ u ∈ Set.Ioo (1 : ℝ) c,
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (u ^ 2 * Φ (z * u) θ))
        = ENNReal.ofReal (u ^ 2) *
            ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Φ (z * u) θ) := by
    intro u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu.1
    have hzu : z * u ∈ Work.Spaces.Iz := le_of_lt (mul_pos hz hu0)
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (u ^ 2 * Φ (z * u) θ))
        = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (u ^ 2) *
            ENNReal.ofReal (Φ (z * u) θ) :=
          lintegral_congr fun θ => by rw [ENNReal.ofReal_mul (sq_nonneg u)]
      _ = ENNReal.ofReal (u ^ 2) *
            (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Φ (z * u) θ)) :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (u ^ 2) *
            ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Φ (z * u) θ) := by
          rw [(MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hΦint (z * u) hzu)
            (Filter.Eventually.of_forall (fun θ => hnn (z * u) θ))).symm]
  rw [MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo hpoint]
  exact mul_le_mul_of_nonneg_left
    (lintegral_shift_mul_bound hc hnn hΦc hΦint hz) (by positivity)

/-- **The `θ`-slices of the majorant are integrable.** -/
theorem integrableOn_Maj_slice {Φ : ℝ → ℝ → ℝ} {c : ℝ} (hc : 1 < c)
    (hnn : ∀ z θ, 0 ≤ Φ z θ)
    (hΦc : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hcontu : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousOn (fun u : ℝ => u ^ 2 * Φ (z * u) θ) (Set.Icc (1 : ℝ) c))
    (hΦint : ∀ s ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Φ s θ) Work.Spaces.Iθ)
    (hΦ0 : ∀ θ, Φ 0 θ = 0)
    (hKfin : (∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM) ≠ ⊤) :
    ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Maj c Φ z θ) Work.Spaces.Iθ := by
  intro z hz
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
  · subst hz0
    have h0 : ∀ θ, Maj c Φ 0 θ = 0 := by
      intro θ
      show (c - 1)⁻¹ * ∫ u in (1 : ℝ)..c, u ^ 2 * Φ (0 * u) θ = 0
      simp only [zero_mul, hΦ0, mul_zero, intervalIntegral.integral_zero, mul_zero]
    refine MeasureTheory.IntegrableOn.congr_fun integrableOn_zero
      (fun θ _ => (h0 θ).symm) measurableSet_Icc
  · have hA : AEMeasurable (fun θ => ENNReal.ofReal (Maj c Φ z θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have h1 : AEMeasurable (fun θ : ℝ => ENNReal.ofReal ((c - 1)⁻¹) *
          ∫⁻ u in Set.Ioo (1 : ℝ) c, ENNReal.ofReal (u ^ 2 * Φ (z * u) θ))
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        ((aemeasurable_shift_pair hΦc hzpos hc).lintegral_prod_right).const_mul _
      refine h1.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact (ofReal_Maj_eq hc hnn hcontu z (Set.mem_Ioi.mpr hzpos) θ hθ).symm
    have ham : MeasureTheory.AEStronglyMeasurable (fun θ => Maj c Φ z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have h2 : AEMeasurable (fun θ : ℝ => (ENNReal.ofReal (Maj c Φ z θ)).toReal)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        ENNReal.measurable_toReal.comp_aemeasurable hA
      refine h2.aestronglyMeasurable.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ _
      exact ENNReal.toReal_ofReal (Maj_nonneg hc hnn z θ)
    have hfin : (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Maj c Φ z θ)) < ⊤ := by
      refine lt_of_le_of_lt (lintegral_Maj_theta_le hc hnn hΦc hcontu hΦint hzpos) ?_
      exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKfin)))
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable ham
      (Filter.Eventually.of_forall fun θ => Maj_nonneg hc hnn z θ)).mp hfin.ne

/-- **The `z`-integral of the majorant's `θ`-slices is integrable.** -/
theorem integrableOn_Maj_z {Φ : ℝ → ℝ → ℝ} {c : ℝ} (hc : 1 < c)
    (hnn : ∀ z θ, 0 ≤ Φ z θ)
    (hΦc : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) Work.FTS.EllipticEst.Q0)
    (hcontu : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousOn (fun u : ℝ => u ^ 2 * Φ (z * u) θ) (Set.Icc (1 : ℝ) c))
    (hΦint : ∀ s ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Φ s θ) Work.Spaces.Iθ)
    (hΦ0 : ∀ θ, Φ 0 θ = 0)
    (hKfin : (∫⁻ p, ENNReal.ofReal (Φ p.1 p.2) ∂qM) ≠ ⊤) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Maj c Φ z θ) Work.Spaces.Iz := by
  have hslice := integrableOn_Maj_slice hc hnn hΦc hcontu hΦint hΦ0 hKfin
  have hA : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Maj c Φ p.1 p.2)) qM := by
    have hset : Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ
        =ᵐ[((MeasureTheory.volume : Measure ℝ).prod MeasureTheory.volume)]
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      MeasureTheory.Measure.set_prod_ae_eq
        (MeasureTheory.Ioi_ae_eq_Ici' (μ := MeasureTheory.volume) (a := (0 : ℝ)) (by simp))
        (Filter.EventuallyEq.rfl)
    have h1 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((c - 1)⁻¹) *
        ∫⁻ u in Set.Ioo (1 : ℝ) c, ENNReal.ofReal (u ^ 2 * Φ (p.1 * u) p.2)) qM :=
      ((aemeasurable_shift_triple hΦc hc).lintegral_prod_right).const_mul _
    refine h1.congr ?_
    rw [qM_eq_restrict, ← MeasureTheory.Measure.restrict_congr_set hset]
    filter_upwards [MeasureTheory.ae_restrict_mem
      (isOpen_Ioi.measurableSet.prod measurableSet_Icc)] with p hp
    exact (ofReal_Maj_eq hc hnn hcontu p.1 hp.1 p.2 hp.2).symm
  have hbridge : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Maj c Φ z θ))
      = ∫⁻ p, ENNReal.ofReal (Maj c Φ p.1 p.2) ∂qM := by
    have hcongr : ∀ z ∈ Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Maj c Φ z θ)
          = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Maj c Φ z θ) :=
      fun z hz => MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hslice z hz)
        (Filter.Eventually.of_forall fun θ => Maj_nonneg hc hnn z θ)
    rw [MeasureTheory.setLIntegral_congr_fun (μ := MeasureTheory.volume)
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) hcongr]
    exact (MeasureTheory.lintegral_prod _ hA).symm
  have hfin : (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, Maj c Φ z θ)) < ⊤ := by
    rw [hbridge]
    exact lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKfin)
      (lintegral_Maj_le hc hnn hΦc hcontu))
  have hmes : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, Maj c Φ z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h2 : AEMeasurable (fun z : ℝ =>
        (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (Maj c Φ z θ)).toReal)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      ENNReal.measurable_toReal.comp_aemeasurable hA.lintegral_prod_right
    refine h2.aestronglyMeasurable.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hslice z hz)
      (Filter.Eventually.of_forall fun θ => Maj_nonneg hc hnn z θ)]
    exact ENNReal.toReal_ofReal
      (MeasureTheory.integral_nonneg fun θ => Maj_nonneg hc hnn z θ)
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmes
    (Filter.Eventually.of_forall fun z =>
      MeasureTheory.integral_nonneg fun θ => Maj_nonneg hc hnn z θ)).mp hfin.ne

/-- The `ℋ⁰`-lintegral of a smooth honest function is `ofReal` of its `HkSq`. -/
theorem lintegral_ofReal_HkIntegrand_eq' {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 0 f) :
    (∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 f p.1 p.2) ∂qM)
      = ENNReal.ofReal (Work.Spaces.HkSq α 0 f) :=
  (Work.FTS.EllipticEst.Cores.Dil.ofReal_HkSq_zero hmem
    (aemeasurable_ofReal_Q0 (hf.continuousOn_HkIntegrand α 0))).symm

/-- **The level-`0` estimate for the radial difference quotient**: the `ℋ⁰`-lintegral of `dq c g`
is at most `c³` times the `ℋ⁰`-squared norm of the radial derivative `D_z g`. -/
theorem lintegral_HkIntegrand_dq_le {α c : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hgmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dz g)) (hc : 1 < c) :
    (∫⁻ p, ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c g) p.1 p.2)
        ∂qM)
      ≤ ENNReal.ofReal (c ^ 3 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz g)) := by
  have hΦc : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    hg.Dz.continuousOn_HkIntegrand α 0
  have hnn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α 0 (Work.Spaces.Dz g) z θ
  have hcontu : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ContinuousOn (fun u : ℝ => u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ)
        (Set.Icc (1 : ℝ) c) :=
    Work.FTS.EllipticEst.Cores.PPureShiftRad.continuousOn_u_majorant (α := α) hg hc
  have hae : ∀ᵐ p ∂qM, ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c g) p.1 p.2)
      ≤ ENNReal.ofReal (Maj c (fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) z θ)
          p.1 p.2) := by
    rw [qM_eq_restrict]
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) ?_
    intro p hp
    exact ENNReal.ofReal_le_ofReal
      (Work.FTS.EllipticEst.Cores.PPureShiftRad.HkIntegrand_dq_le hg hc p.1 hp.1 p.2 hp.2)
  calc (∫⁻ p, ENNReal.ofReal
        (Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.Cores.Dil.dq c g) p.1 p.2) ∂qM)
      ≤ ∫⁻ p, ENNReal.ofReal (Maj c
          (fun z θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) z θ) p.1 p.2) ∂qM :=
        lintegral_mono_ae hae
    _ ≤ ENNReal.ofReal (c ^ 3) * (∫⁻ p, ENNReal.ofReal
          (Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) p.1 p.2) ∂qM) :=
        lintegral_Maj_le hc hnn hΦc hcontu
    _ = ENNReal.ofReal (c ^ 3) *
          ENNReal.ofReal (Work.Spaces.HkSq α 0 (Work.Spaces.Dz g)) := by
        rw [lintegral_ofReal_HkIntegrand_eq' hg.Dz hgmem]
    _ = ENNReal.ofReal (c ^ 3 * Work.Spaces.HkSq α 0 (Work.Spaces.Dz g)) := by
        rw [ENNReal.ofReal_mul (by positivity)]

end Work.FTS.EllipticEst.Cores.pPureShiftAux
