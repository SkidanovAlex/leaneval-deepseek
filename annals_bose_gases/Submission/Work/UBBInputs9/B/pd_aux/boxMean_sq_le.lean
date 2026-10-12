import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxA0.kwPhi_props
import Submission.Work.UBBInputs9.B.pd_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs9.B.pd_aux

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Pointwise bound for the box mean of the witness state.**

Let `ℓ, d > 0`, `γ > 0`, `2/ℓ < cc`, and assume `hvol`: every sliding box `dlBox ℓ d u` that
meets the inner cube `{z : ℝ³ | ∀ i, |z i| ≤ ℓ/4}` has volume `≥ γ³`.  Then for every `u : ℝ³`,

    (boxMean ℓ d u (kwPhi ℓ cc))² ≤ (γ³)⁻¹ ,

where `boxMean ℓ d u Φ = (boxMass ℓ d u)⁻¹ * ∫ z in dlBox ℓ d u, Φ (fun _ => z)`.

(The relevant corpus lemmas: `Work.SmallBoxSliding.boxMass_eq_measureReal`
(`boxMass ℓ d u = (volume : Measure ℝ³).real (dlBox ℓ d u)`),
`Work.SmallBoxSliding.volume_dlBox_lt_top`, `Work.SmallBoxSliding.measurableSet_dlBox`,
`Submission.BoseGases.cs_finite_measure` (Cauchy–Schwarz `(∫ f)² ≤ μ.real univ * ∫ f²` on a
*finite* measure, in `Submission/Work/SmallBoxSliding`-reachable `Submission.SectorProj`),
`Work.SmallBoxA0.kwPhi_props`, `Work.SmallBoxA0.kwBoxExtend`,
`Submission.BoseGases.abs_coord_le_norm`.)

HINT.  Write `F : ℝ³ → ℝ := fun z => kwPhi ℓ cc (fun _ => z)` (the avatar of `kwPhi ℓ cc` on
`ℝ³`; `X 1 = Fin 1 → ℝ³`, so `(fun _ => z) 0 = z`) and `J := ∫ z in dlBox ℓ d u, F z`, so that
`boxMean ℓ d u (kwPhi ℓ cc) = (boxMass ℓ d u)⁻¹ * J`.

1. If `F` vanishes on `dlBox ℓ d u` then `J = 0`
   (`MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero`), hence `boxMean = 0` and we are done.
2. Otherwise pick `z ∈ dlBox ℓ d u` with `F z ≠ 0`.  Item (3) of `Work.SmallBoxA0.kwPhi_props`
   says `1/(2*cc) < ‖x 0‖ → kwPhi ℓ cc x = 0`, so `‖z‖ ≤ 1/(2*cc)`, and `2/ℓ < cc` gives
   `1/(2*cc) < ℓ/4`; with `Submission.BoseGases.abs_coord_le_norm` (`|z i| ≤ ‖z‖`) we get
   `|z i| < ℓ/4`, so `hvol` gives `ENNReal.ofReal (γ^3) ≤ volume (dlBox ℓ d u)`, whence
   `γ^3 ≤ boxMass ℓ d u` (`ENNReal.toReal_mono` with `volume_dlBox_lt_top`, then
   `ENNReal.toReal_ofReal`).
3. Cauchy–Schwarz: on the finite measure `μ := (volume : Measure ℝ³).restrict (dlBox ℓ d u)`
   (finiteness from `volume_dlBox_lt_top`), with `f := F` (a.e. strongly measurable and
   a.e. bounded, e.g. from continuity of `F` and compact support of `kwPhi ℓ cc`),
   `Submission.BoseGases.cs_finite_measure` gives
   `J² ≤ boxMass ℓ d u * ∫ z in dlBox ℓ d u, (F z)²`, since `μ.real univ = boxMass ℓ d u`
   and `∫ z, F z ∂μ = ∫ z in dlBox ℓ d u, F z`.
4. `∫ z in dlBox ℓ d u, (F z)² ≤ ∫ z, (F z)² = 1`:
   `MeasureTheory.setIntegral_le_integral` (integrability of `F²` from continuity plus compact
   support) for the inequality, and `Work.SmallBoxA0.kwBoxExtend` together with
   `∫ x in abox 1 ℓ, (kwPhi ℓ cc x)² = 1` (item (5) of `Work.SmallBoxA0.kwPhi_props`) for the
   equality (`kwBoxExtend` needs the integrand to vanish off `acube ℓ`, which follows from the
   vanishing of `kwPhi ℓ cc` off `ball 0 (1/(2*cc)) ⊆ acube ℓ`; `X 1 ≃ ℝ³` by evaluation at `0`,
   `Fin.forall_fin_one`).
5. Combine: `boxMean² = (boxMass)⁻² * J² ≤ (boxMass)⁻¹ * 1 ≤ (γ³)⁻¹`
   (`inv_le_inv₀`, using `0 < γ³ ≤ boxMass`, and `(boxMass)⁻² ≥ 0`). -/
theorem boxMean_sq_le {ℓ d cc γ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hcc : 2 / ℓ < cc) (hγ : 0 < γ)
    (hvol : ∀ (u z : EuclideanSpace ℝ (Fin 3)), z ∈ Submission.BoseGases.dlBox ℓ d u →
      (∀ i : Fin 3, |z i| ≤ ℓ / 4) →
        ENNReal.ofReal (γ ^ 3) ≤
          (volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
            (Submission.BoseGases.dlBox ℓ d u)) :
    ∀ u : EuclideanSpace ℝ (Fin 3),
      (Work.UBBInputs9.B.boxMean ℓ d u (Work.SmallBoxA0.kwPhi ℓ cc)) ^ 2 ≤ (γ ^ 3)⁻¹ := by
  intro u
  obtain ⟨hcont, hsupp, hvan, hlam, hnorm, hkin⟩ :=
    Work.SmallBoxA0.kwPhi_props (s := ℓ) (c := cc) hℓ hcc
  have hccpos : 0 < cc := lt_trans (div_pos two_pos hℓ) hcc
  have hγ3pos : 0 < γ ^ 3 := pow_pos hγ 3
  -- `2/ℓ < cc` with `ℓ > 0` gives the vanishing margin `1/(2cc) < ℓ/4`.
  have h12 : 1 / (2 * cc) < ℓ / 4 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have h2 : 2 < cc * ℓ := by rw [div_lt_iff₀ hℓ] at hcc; linarith
    nlinarith
  rw [show Work.UBBInputs9.B.boxMean ℓ d u (Work.SmallBoxA0.kwPhi ℓ cc)
      = (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ *
        ∫ z in Submission.BoseGases.dlBox ℓ d u,
          Work.SmallBoxA0.kwPhi ℓ cc (fun _ => z) from rfl]
  -- The avatar `F` of the witness on `ℝ³` and its box integral `J`.
  set F : ℝ³ → ℝ := fun z => Work.SmallBoxA0.kwPhi ℓ cc (fun _ => z) with hF
  set J : ℝ := ∫ z in Submission.BoseGases.dlBox ℓ d u, F z with hJ
  -- `F` is continuous, compactly supported, and has total `L²`-mass `1`.
  have hFcont : Continuous F := by rw [hF]; fun_prop
  have hFc : HasCompactSupport F := by
    rw [hF]
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ³) (1 / (2 * cc)))
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    push Not at h
    exact hz (hvan (fun _ => z) (by simpa using h))
  have hFint : (∫ z : ℝ³, (F z) ^ 2) = 1 := by
    rw [hF]
    rw [← Work.SmallBoxA0.kwBoxExtend (s := ℓ)
        (F := fun z : ℝ³ => (Work.SmallBoxA0.kwPhi ℓ cc (fun _ => z)) ^ 2) ?_]
    · rw [← hnorm]
      apply integral_congr_ae
      filter_upwards with x
      have hx : (fun _ : Fin 1 => x 0) = x := by funext i; rw [Fin.eq_zero i]
      rw [hx]
    · intro z hz
      have hz0 : Work.SmallBoxA0.kwPhi ℓ cc (fun _ => z) = 0 := by
        apply hvan
        have hnorm_gt : ℓ / 2 < ‖z‖ := by
          have hz' : ¬ ∀ m : Fin 3, |z m| ≤ ℓ / 2 := by
            intro h
            apply hz
            rw [Submission.BoseGases.mem_acube_iff]
            intro m
            rw [Set.mem_Icc]
            obtain ⟨h1, h2⟩ := abs_le.mp (h m)
            exact ⟨by linarith, h2⟩
          push Not at hz'
          obtain ⟨m, hm⟩ := hz'
          exact lt_of_lt_of_le hm (Submission.BoseGases.abs_coord_le_norm z m)
        have : (1 : ℝ) / (2 * cc) < ‖z‖ := lt_trans h12 (by linarith)
        simpa using this
      rw [hz0, zero_pow (by norm_num)]
  have hF2c : HasCompactSupport (fun z : ℝ³ => (F z) ^ 2) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ³) (1 / (2 * cc)))
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    push Not at h
    rw [Function.mem_support] at hz
    have hz0 : F z = 0 := by rw [hF]; exact hvan (fun _ => z) (by simpa using h)
    exact hz (by rw [hz0, zero_pow (by norm_num)])
  have hF2int : Integrable (fun z : ℝ³ => (F z) ^ 2) volume :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) hF2c
  by_cases hzero : ∀ z ∈ Submission.BoseGases.dlBox ℓ d u, F z = 0
  · -- `F` vanishes on the box: `J = 0` and the bound is trivial.
    have hJ0 : J = 0 := by
      rw [hJ]
      exact MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero hzero
    rw [hJ0, mul_zero, zero_pow (by norm_num)]
    exact inv_nonneg.mpr (pow_nonneg hγ.le 3)
  · -- A witness point: `F z ≠ 0` forces `‖z‖ ≤ 1/(2cc)`, whence `hvol` controls `boxMass`.
    push Not at hzero
    obtain ⟨z, hzmem, hzF⟩ := hzero
    have hnorm_le : ‖z‖ ≤ 1 / (2 * cc) := by
      by_contra h
      push Not at h
      exact hzF (by rw [hF]; exact hvan (fun _ => z) (by simpa using h))
    have hcoord : ∀ i : Fin 3, |z i| ≤ ℓ / 4 := by
      intro i
      calc |z i| ≤ ‖z‖ := Submission.BoseGases.abs_coord_le_norm z i
        _ ≤ 1 / (2 * cc) := hnorm_le
        _ ≤ ℓ / 4 := le_of_lt h12
    have hvolz := hvol u z hzmem hcoord
    have hγbox : γ ^ 3 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
      have hfin := Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u
      have h1 := ENNReal.toReal_mono (ne_of_lt hfin) hvolz
      rw [ENNReal.toReal_ofReal (pow_nonneg hγ.le 3)] at h1
      rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
      exact h1
    have hbox : 0 < Work.SmallBoxSliding.boxMass ℓ d u := lt_of_lt_of_le hγ3pos hγbox
    -- Cauchy–Schwarz on the (finite-measure) restricted box.
    have hCS : J ^ 2 ≤ Work.SmallBoxSliding.boxMass ℓ d u *
        (∫ z in Submission.BoseGases.dlBox ℓ d u, (F z) ^ 2) := by
      rw [hJ]
      let μ : Measure ℝ³ := (volume : Measure ℝ³).restrict (Submission.BoseGases.dlBox ℓ d u)
      have hfin : IsFiniteMeasure μ := ⟨by
        rw [Measure.restrict_apply_univ]
        exact Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u⟩
      haveI : IsFiniteMeasure μ := hfin
      obtain ⟨C, hC⟩ := hFc.exists_bound_of_continuous hFcont
      have hb : ∀ᵐ x ∂μ, |F x| ≤ C := ae_of_all _ (fun x => by simpa [Real.norm_eq_abs] using hC x)
      have hcs := Submission.BoseGases.cs_finite_measure (μ := μ) (f := F)
        hFcont.aestronglyMeasurable hb
      have hvolμ : μ.real Set.univ = Work.SmallBoxSliding.boxMass ℓ d u := by
        rw [MeasureTheory.measureReal_restrict_apply_univ]
        exact (Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u).symm
      rw [hvolμ] at hcs
      exact hcs
    have hint2 : (∫ z in Submission.BoseGases.dlBox ℓ d u, (F z) ^ 2) ≤ 1 := by
      have hle := MeasureTheory.setIntegral_le_integral (μ := (volume : Measure ℝ³))
        (s := Submission.BoseGases.dlBox ℓ d u) hF2int (ae_of_all _ (fun z => sq_nonneg (F z)))
      rwa [hFint] at hle
    have hJ2 : J ^ 2 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
      calc J ^ 2 ≤ Work.SmallBoxSliding.boxMass ℓ d u *
            (∫ z in Submission.BoseGases.dlBox ℓ d u, (F z) ^ 2) := hCS
        _ ≤ Work.SmallBoxSliding.boxMass ℓ d u * 1 :=
            mul_le_mul_of_nonneg_left hint2 (le_of_lt hbox)
        _ = Work.SmallBoxSliding.boxMass ℓ d u := mul_one _
    calc ((Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ * J) ^ 2
        = ((Work.SmallBoxSliding.boxMass ℓ d u)⁻¹) ^ 2 * J ^ 2 := by rw [mul_pow]
      _ ≤ ((Work.SmallBoxSliding.boxMass ℓ d u)⁻¹) ^ 2 * Work.SmallBoxSliding.boxMass ℓ d u :=
            mul_le_mul_of_nonneg_left hJ2 (by positivity)
      _ = (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ := by
            rw [pow_two, mul_assoc, inv_mul_cancel₀ (ne_of_gt hbox), mul_one]
      _ ≤ (γ ^ 3)⁻¹ := by
            rw [inv_le_inv₀ hbox hγ3pos]
            exact hγbox

end Work.UBBInputs9.B.pd_aux
