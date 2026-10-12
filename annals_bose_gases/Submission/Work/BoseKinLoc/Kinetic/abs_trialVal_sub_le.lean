import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Kinetic.box_cauchy_schwarz
import Submission.Work.BoseKinLoc.Kinetic.neuFracTrialDefs
import Submission.Work.BoseKinLoc.Kinetic.sqrt_integralOn_add_sq_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Kinetic

open MeasureTheory Filter

set_option linter.unusedVariables false

theorem abs_trialVal_sub_le {ℓ a2 R : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) (hR : 0 < R)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ ψ' g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψm : MeasureTheory.AEStronglyMeasurable ψ MeasureTheory.volume)
    (hψ'm : MeasureTheory.AEStronglyMeasurable ψ' MeasureTheory.volume)
    (hψ : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z) ^ 2))
    (hψ' : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (ψ' z) ^ 2))
    (hψd : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z - ψ' z) ^ 2))
    (hRψ : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2 ≤ R ^ 2)
    (hRψ' : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ' z) ^ 2 ≤ R ^ 2)
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgs : HasCompactSupport g)
    (hg2 : ∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2 ≤ (2 * R / a2) ^ 2) :
    |Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u ψ g - Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u ψ' g|
      ≤ 6 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) := by
  classical
  -- `g` is smooth with compact support: a.e. measurable and square integrable.
  have hg_am : AEStronglyMeasurable g volume := hg.continuous.aestronglyMeasurable
  have hgc : HasCompactSupport (fun z : EuclideanSpace ℝ (Fin 3) => (g z) ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hgs ⊢
    filter_upwards [hgs] with x hx
    simp [hx]
  have hg2glob : Integrable (fun z : EuclideanSpace ℝ (Fin 3) => (g z) ^ 2) volume :=
    (hg.continuous.pow 2).integrable_of_hasCompactSupport hgc
  -- integrability on the box `Λ = lamBox ℓ u`
  have hψ2B : Integrable (fun z => (ψ z) ^ 2) (volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    hψ.integrableOn
  have hψ'2B : Integrable (fun z => (ψ' z) ^ 2) (volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    hψ'.integrableOn
  have hg2B : Integrable (fun z => (g z) ^ 2) (volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    hg2glob.integrableOn
  -- the states are `L²` on the box
  have hψL2 : MemLp ψ 2 (volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    (memLp_two_iff_integrable_sq hψm.restrict).mpr hψ2B
  have hψ'L2 : MemLp ψ' 2 (volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    (memLp_two_iff_integrable_sq hψ'm.restrict).mpr hψ'2B
  have hdL2 : MemLp (fun z => ψ z - ψ' z) 2 (volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    hψL2.sub hψ'L2
  have hpL2 : MemLp (fun z => ψ z + ψ' z) 2 (volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    hψL2.add hψ'L2
  have hgL2 : MemLp g 2 (volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    (memLp_two_iff_integrable_sq hg_am.restrict).mpr hg2B
  -- the cross terms are integrable (Hölder with `p = q = 2`)
  have hψgB : Integrable (fun z => ψ z * g z) (volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    (box_cauchy_schwarz hψL2 hgL2).1
  have hψ'gB : Integrable (fun z => ψ' z * g z) (volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    (box_cauchy_schwarz hψ'L2 hgL2).1
  -- the two "quadratic" pieces of `trialVal` as differences of integrals
  have hI : (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2)
        - (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ' z) ^ 2)
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z + ψ' z) * (ψ z - ψ' z) := by
    rw [← integral_sub hψ2B hψ'2B]
    exact integral_congr_ae (Eventually.of_forall (fun z => by ring))
  have hJ : (∫ z in Work.BoseKinLoc.lamBox ℓ u, ψ z * g z)
        - (∫ z in Work.BoseKinLoc.lamBox ℓ u, ψ' z * g z)
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) * g z := by
    rw [← integral_sub hψgB hψ'gB]
    exact integral_congr_ae (Eventually.of_forall (fun z => by ring))
  -- **the difference identity**: the `g`-dependent kinetic/quadratic terms cancel
  have hdiff : Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u ψ g
        - Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u ψ' g
      = (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z + ψ' z) * (ψ z - ψ' z))
        - 2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) * g z) := by
    unfold Work.BoseKinLoc.Kinetic.trialVal
    rw [← hI, ← hJ]
    ring
  -- bound on the `(ψ+ψ')(ψ−ψ')` term
  have hA : |∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z + ψ' z) * (ψ z - ψ' z)|
      ≤ 2 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) := by
    have hcs := (box_cauchy_schwarz hpL2 hdL2).2
    have hs : Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z + ψ' z) ^ 2) ≤ 2 * R :=
      sqrt_integralOn_add_sq_le (le_of_lt hR) hψL2 hψ'L2 hRψ hRψ'
    have hnn : 0 ≤ Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) :=
      Real.sqrt_nonneg _
    calc |∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z + ψ' z) * (ψ z - ψ' z)|
        ≤ Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z + ψ' z) ^ 2)
            * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) := hcs
      _ ≤ 2 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) :=
          mul_le_mul_of_nonneg_right hs hnn
  -- bound on the `2a²(ψ−ψ')g` term
  have hB : |2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) * g z)|
      ≤ 2 * a2 * (2 * R / a2)
        * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) := by
    rw [abs_mul, abs_of_pos (show 0 < 2 * a2 by positivity)]
    have hcs := (box_cauchy_schwarz hdL2 hgL2).2
    have hgb : Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2) ≤ 2 * R / a2 := by
      calc Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2)
          ≤ Real.sqrt ((2 * R / a2) ^ 2) := Real.sqrt_le_sqrt hg2
        _ = 2 * R / a2 := Real.sqrt_sq (by positivity)
    have hDnn : 0 ≤ Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) :=
      Real.sqrt_nonneg _
    calc 2 * a2 * |∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) * g z|
        ≤ 2 * a2 * (Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2)
            * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2)) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ ≤ 2 * a2
            * (Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2)
                * (2 * R / a2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hgb hDnn
      _ = 2 * a2 * (2 * R / a2)
            * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) := by ring
  rw [hdiff]
  have hc : 2 * a2 * (2 * R / a2) = 4 * R := by field_simp; ring
  calc |(∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z + ψ' z) * (ψ z - ψ' z))
          - 2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) * g z)|
      ≤ |∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z + ψ' z) * (ψ z - ψ' z)|
        + |2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) * g z)| := by
        rw [sub_eq_add_neg]
        calc |(∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z + ψ' z) * (ψ z - ψ' z))
              + -(2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) * g z))|
            ≤ |∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z + ψ' z) * (ψ z - ψ' z)|
              + |-(2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) * g z))| :=
                abs_add_le _ _
          _ = |∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z + ψ' z) * (ψ z - ψ' z)|
              + |2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) * g z)| := by
                rw [abs_neg]
    _ ≤ 2 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2)
        + 2 * a2 * (2 * R / a2)
          * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) :=
          add_le_add hA hB
    _ = 6 * R * Real.sqrt (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z - ψ' z) ^ 2) := by
          rw [hc]; ring

end Work.BoseKinLoc.Kinetic
