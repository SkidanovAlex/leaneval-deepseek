import Mathlib
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLC7.HeisMul
import Submission.Work.EKLC7.HeisShift
import Submission.Work.EKLC7.CoordTest
import Submission.Work.EKLC7.CoordTripDefs
import Submission.Work.EKLC7.CoordTripAux
import Submission.Work.EKLC7.TripFubini
import Submission.Work.EKLC7.CcIntegralExtend
import Submission.Work.EKLC7.CcExhaustion

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

open scoped ENNReal

namespace Work.EKLC7

open MeasureTheory Filter Topology
open Work.EKLContract
open Work.EKLContract.Lemmas

instance instLocallyCompactMatrix3 : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
  inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → ℝ))

instance instLocallyCompactSpaceSL3 : LocallyCompactSpace SL3 := isClosed_sl3.locallyCompactSpace

theorem CoordTrip :
    ∀ {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
      (νij νjk νik νN : MeasureTheory.Measure Work.EKLContract.SL3) (cA cB : ℝ),
      MeasureTheory.IsFiniteMeasureOnCompacts νij → MeasureTheory.IsFiniteMeasureOnCompacts νjk →
      MeasureTheory.IsFiniteMeasureOnCompacts νik →
      Work.EKLC7.TripleA νN νij νjk νik cA → Work.EKLC7.TripleB νN νij νjk νik cB →
      νij (Work.EKLContract.Uij hij)ᶜ = 0 → νjk (Work.EKLContract.Uij hjk)ᶜ = 0 →
      νik (Work.EKLContract.Uij hik)ᶜ = 0 →
      (∀ (F : ℝ × ℝ × ℝ → ℝ), Continuous F → HasCompactSupport F →
        ∫ z, F z ∂(νN.map (fun g => (Work.EKLC7.pcoord i j g, Work.EKLC7.qcoord i k g,
            Work.EKLC7.rcoord j k g)))
          = cA * ∫ p, ∫ r, ∫ q, F (p, p * r + q, r)
              ∂(νik.map (Work.EKLC7.qcoord i k)) ∂(νjk.map (Work.EKLC7.rcoord j k))
              ∂(νij.map (Work.EKLC7.pcoord i j)))
      ∧ (∀ (F : ℝ × ℝ × ℝ → ℝ), Continuous F → HasCompactSupport F →
        ∫ z, F z ∂(νN.map (fun g => (Work.EKLC7.pcoord i j g, Work.EKLC7.qcoord i k g,
            Work.EKLC7.rcoord j k g)))
          = cB * ∫ p, ∫ r, ∫ q, F (p, q, r)
              ∂(νik.map (Work.EKLC7.qcoord i k)) ∂(νjk.map (Work.EKLC7.rcoord j k))
              ∂(νij.map (Work.EKLC7.pcoord i j))) := by
  intro i j k hij hjk hik νij νjk νik νN cA cB hνij hνjk hνik hTripA hTripB hnij hnjk hnik
  haveI : IsFiniteMeasureOnCompacts νij := hνij
  haveI : IsFiniteMeasureOnCompacts νjk := hνjk
  haveI : IsFiniteMeasureOnCompacts νik := hνik
  haveI : IsFiniteMeasureOnCompacts (νij.map (fun g => pcoord i j g)) :=
    isFiniteMeasureOnCompacts_map_entry hij hnij
  haveI : IsFiniteMeasureOnCompacts (νjk.map (fun g => rcoord j k g)) :=
    isFiniteMeasureOnCompacts_map_entry hjk hnjk
  haveI : IsFiniteMeasureOnCompacts (νik.map (fun g => qcoord i k g)) :=
    isFiniteMeasureOnCompacts_map_entry hik hnik
  haveI : IsFiniteMeasureOnCompacts (νij.map (fun g => toMat g i j)) :=
    isFiniteMeasureOnCompacts_map_entry hij hnij
  haveI : IsFiniteMeasureOnCompacts (νjk.map (fun g => toMat g j k)) :=
    isFiniteMeasureOnCompacts_map_entry hjk hnjk
  haveI : IsFiniteMeasureOnCompacts (νik.map (fun g => toMat g i k)) :=
    isFiniteMeasureOnCompacts_map_entry hik hnik
  have hAp : νij = (νij.map (fun g => pcoord i j g)).map (fun s => uij hij s) :=
    measure_eq_map_uij_entry hij hnij
  have hBp : νjk = (νjk.map (fun g => rcoord j k g)).map (fun s => uij hjk s) :=
    measure_eq_map_uij_entry hjk hnjk
  have hCp : νik = (νik.map (fun g => qcoord i k g)).map (fun s => uij hik s) :=
    measure_eq_map_uij_entry hik hnik
  set rhoA : Measure SL3 := (νij.prod (νjk.prod νik)).map mult3 with hrhoA
  set rhoB : Measure SL3 := (νjk.prod (νij.prod νik)).map mult3 with hrhoB
  haveI : IsFiniteMeasureOnCompacts rhoA := by
    rw [hrhoA]
    exact isFiniteMeasureOnCompacts_rhoA hij hjk hik hAp hBp hCp
  haveI : IsFiniteMeasureOnCompacts rhoB := by
    rw [hrhoB]
    exact isFiniteMeasureOnCompacts_rhoB hij hjk hik hAp hBp hCp
  have hfunA : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      ∫ g, f g ∂νN = cA * ∫ g, f g ∂rhoA := by
    intro f
    rw [hTripA f]
    congr 1
    exact TripFubini (horoUij_cont hij) (horoUij_cont hjk) (horoUij_cont hik)
      (continuous_heisA hij hjk hik) (prod_heisA hij hjk hik) (heisA_lex hij hjk hik)
      hAp hBp hCp f
  have hfunB : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      ∫ g, f g ∂νN = cB * ∫ g, f g ∂rhoB := by
    intro f
    rw [hTripB f]
    congr 1
    exact TripFubini (horoUij_cont hjk) (horoUij_cont hij) (horoUij_cont hik)
      (continuous_heisB hij hjk hik) (prod_heisB hij hjk hik) (heisB_lex hij hjk hik)
      hBp hAp hCp f
  have hstarA : ∀ g : SL3 → ℝ, Continuous g → (∃ C : ℝ, ∀ x, |g x| ≤ C) →
      (∫⁻ x, ENNReal.ofReal (g x) ∂νN).toReal
        = cA * (∫⁻ x, ENNReal.ofReal (g x) ∂rhoA).toReal := by
    intro g hgc hgb
    by_cases hcA : 0 ≤ cA
    · obtain ⟨φ, hφ0, hφ1, hφmono, hφtop⟩ := CcExhaustion (X := SL3)
      have hfun2 : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
          ∫ x, (f : SL3 → ℝ) x ∂νN
            = ∫ x, (f : SL3 → ℝ) x ∂(ENNReal.ofReal cA • rhoA) := by
        intro f
        rw [hfunA f, integral_smul_measure, ENNReal.toReal_ofReal hcA, smul_eq_mul]
      haveI : IsFiniteMeasureOnCompacts (ENNReal.ofReal cA • rhoA) :=
        IsFiniteMeasureOnCompacts.smul rhoA ENNReal.ofReal_ne_top
      have hkey := CcIntegralExtend νN (ENNReal.ofReal cA • rhoA) φ hφ0 hφ1 hφmono hφtop
        hfun2 g hgc hgb
      rw [hkey, lintegral_smul_measure, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcA]
    · have hcAneg : cA < 0 := not_le.mp hcA
      obtain ⟨φ, hφ0, hφ1, hφmono, hφtop⟩ := CcExhaustion (X := SL3)
      have hposA : ∀ f : CompactlySupportedContinuousMap SL3 ℝ, 0 ≤ (f : SL3 → ℝ) →
          ∫ x, (f : SL3 → ℝ) x ∂rhoA = 0 := by
        intro f hf
        have h1 := hfunA f
        have h2 : 0 ≤ ∫ x, (f : SL3 → ℝ) x ∂νN := integral_nonneg hf
        have h3 : 0 ≤ ∫ x, (f : SL3 → ℝ) x ∂rhoA := integral_nonneg hf
        nlinarith [h1, h2, h3, hcAneg]
      have hzeroA : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
          ∫ x, (f : SL3 → ℝ) x ∂rhoA = 0 :=
        integral_eq_zero_of_nonneg_eq_zero rhoA hposA
      have hzeroN : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
          ∫ x, (f : SL3 → ℝ) x ∂νN = 0 := by
        intro f
        rw [hfunA f, hzeroA f, mul_zero]
      haveI : IsFiniteMeasureOnCompacts (0 : Measure SL3) := ⟨fun K hK => by simp⟩
      have hνN0 : (∫⁻ x, ENNReal.ofReal (g x) ∂νN).toReal = 0 := by
        have hkey := CcIntegralExtend νN (0 : Measure SL3) φ hφ0 hφ1 hφmono hφtop
          (fun f => by rw [hzeroN f]; simp) g hgc hgb
        rw [hkey]; simp
      have hrho0 : (∫⁻ x, ENNReal.ofReal (g x) ∂rhoA).toReal = 0 := by
        have hkey := CcIntegralExtend rhoA (0 : Measure SL3) φ hφ0 hφ1 hφmono hφtop
          (fun f => by rw [hzeroA f]; simp) g hgc hgb
        rw [hkey]; simp
      rw [hνN0, hrho0, mul_zero]
  have hstarB : ∀ g : SL3 → ℝ, Continuous g → (∃ C : ℝ, ∀ x, |g x| ≤ C) →
      (∫⁻ x, ENNReal.ofReal (g x) ∂νN).toReal
        = cB * (∫⁻ x, ENNReal.ofReal (g x) ∂rhoB).toReal := by
    intro g hgc hgb
    by_cases hcB : 0 ≤ cB
    · obtain ⟨φ, hφ0, hφ1, hφmono, hφtop⟩ := CcExhaustion (X := SL3)
      have hfun2 : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
          ∫ x, (f : SL3 → ℝ) x ∂νN
            = ∫ x, (f : SL3 → ℝ) x ∂(ENNReal.ofReal cB • rhoB) := by
        intro f
        rw [hfunB f, integral_smul_measure, ENNReal.toReal_ofReal hcB, smul_eq_mul]
      haveI : IsFiniteMeasureOnCompacts (ENNReal.ofReal cB • rhoB) :=
        IsFiniteMeasureOnCompacts.smul rhoB ENNReal.ofReal_ne_top
      have hkey := CcIntegralExtend νN (ENNReal.ofReal cB • rhoB) φ hφ0 hφ1 hφmono hφtop
        hfun2 g hgc hgb
      rw [hkey, lintegral_smul_measure, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hcB]
    · have hcBneg : cB < 0 := not_le.mp hcB
      obtain ⟨φ, hφ0, hφ1, hφmono, hφtop⟩ := CcExhaustion (X := SL3)
      have hposB : ∀ f : CompactlySupportedContinuousMap SL3 ℝ, 0 ≤ (f : SL3 → ℝ) →
          ∫ x, (f : SL3 → ℝ) x ∂rhoB = 0 := by
        intro f hf
        have h1 := hfunB f
        have h2 : 0 ≤ ∫ x, (f : SL3 → ℝ) x ∂νN := integral_nonneg hf
        have h3 : 0 ≤ ∫ x, (f : SL3 → ℝ) x ∂rhoB := integral_nonneg hf
        nlinarith [h1, h2, h3, hcBneg]
      have hzeroB : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
          ∫ x, (f : SL3 → ℝ) x ∂rhoB = 0 :=
        integral_eq_zero_of_nonneg_eq_zero rhoB hposB
      have hzeroN : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
          ∫ x, (f : SL3 → ℝ) x ∂νN = 0 := by
        intro f
        rw [hfunB f, hzeroB f, mul_zero]
      haveI : IsFiniteMeasureOnCompacts (0 : Measure SL3) := ⟨fun K hK => by simp⟩
      have hνN0 : (∫⁻ x, ENNReal.ofReal (g x) ∂νN).toReal = 0 := by
        have hkey := CcIntegralExtend νN (0 : Measure SL3) φ hφ0 hφ1 hφmono hφtop
          (fun f => by rw [hzeroN f]; simp) g hgc hgb
        rw [hkey]; simp
      have hrho0 : (∫⁻ x, ENNReal.ofReal (g x) ∂rhoB).toReal = 0 := by
        have hkey := CcIntegralExtend rhoB (0 : Measure SL3) φ hφ0 hφ1 hφmono hφtop
          (fun f => by rw [hzeroB f]; simp) g hgc hgb
        rw [hkey]; simp
      rw [hνN0, hrho0, mul_zero]
  have hmapA : rhoA.map (coordMap i j k)
      = ((νij.map (fun g => pcoord i j g)).prod
          ((νjk.map (fun g => rcoord j k g)).prod (νik.map (fun g => qcoord i k g)))).map
          shearA := by
    rw [hrhoA]
    exact rhoA_map_coordMap hij hjk hik hAp hBp hCp
  have hmapB : rhoB.map (coordMap i j k)
      = ((νij.map (fun g => pcoord i j g)).prod
          ((νjk.map (fun g => rcoord j k g)).prod (νik.map (fun g => qcoord i k g)))).map
          shearB2 := by
    rw [hrhoB]
    exact rhoB_map_coordMap2 hij hjk hik hAp hBp hCp
  refine ⟨?_, ?_⟩
  · intro F hFc hFs
    obtain ⟨MF, hMF⟩ := exists_abs_bound_of_continuous hFc hFs
    have hGc : Continuous fun g : SL3 => F (coordMap i j k g) :=
      hFc.comp (continuous_coordMap i j k)
    have hGb : ∃ C : ℝ, ∀ x, |F (coordMap i j k x)| ≤ C :=
      ⟨MF, fun x => hMF (coordMap i j k x)⟩
    have key := integral_eq_of_ofReal_lintegral_eq νN rhoA cA hstarA
      (fun g : SL3 => F (coordMap i j k g)) hGc hGb
    calc ∫ z, F z ∂(νN.map (coordMap i j k))
        = ∫ g, F (coordMap i j k g) ∂νN := by
          rw [integral_map (continuous_coordMap i j k).aemeasurable hFc.aestronglyMeasurable]
      _ = cA * ∫ g, F (coordMap i j k g) ∂rhoA := key
      _ = cA * ∫ z, F z ∂(rhoA.map (coordMap i j k)) := by
          rw [integral_map (continuous_coordMap i j k).aemeasurable hFc.aestronglyMeasurable]
      _ = cA * ∫ z, F z ∂(((νij.map (fun g => pcoord i j g)).prod
            ((νjk.map (fun g => rcoord j k g)).prod (νik.map (fun g => qcoord i k g)))).map
            shearA) := by rw [hmapA]
      _ = cA * ∫ x, F (shearA x) ∂((νij.map (fun g => pcoord i j g)).prod
            ((νjk.map (fun g => rcoord j k g)).prod (νik.map (fun g => qcoord i k g)))) := by
          rw [integral_map continuous_shearA.aemeasurable hFc.aestronglyMeasurable]
      _ = cA * ∫ p, ∫ r, ∫ q, F (p, p * r + q, r) ∂(νik.map (fun g => qcoord i k g))
            ∂(νjk.map (fun g => rcoord j k g)) ∂(νij.map (fun g => pcoord i j g)) := by
          rw [fubini_shearA_of (Ap := νij.map (fun g => pcoord i j g))
            (Bp := νjk.map (fun g => rcoord j k g)) (Cp := νik.map (fun g => qcoord i k g)) hFc hFs]
  · intro F hFc hFs
    obtain ⟨MF, hMF⟩ := exists_abs_bound_of_continuous hFc hFs
    have hGc : Continuous fun g : SL3 => F (coordMap i j k g) :=
      hFc.comp (continuous_coordMap i j k)
    have hGb : ∃ C : ℝ, ∀ x, |F (coordMap i j k x)| ≤ C :=
      ⟨MF, fun x => hMF (coordMap i j k x)⟩
    have key := integral_eq_of_ofReal_lintegral_eq νN rhoB cB hstarB
      (fun g : SL3 => F (coordMap i j k g)) hGc hGb
    calc ∫ z, F z ∂(νN.map (coordMap i j k))
        = ∫ g, F (coordMap i j k g) ∂νN := by
          rw [integral_map (continuous_coordMap i j k).aemeasurable hFc.aestronglyMeasurable]
      _ = cB * ∫ g, F (coordMap i j k g) ∂rhoB := key
      _ = cB * ∫ z, F z ∂(rhoB.map (coordMap i j k)) := by
          rw [integral_map (continuous_coordMap i j k).aemeasurable hFc.aestronglyMeasurable]
      _ = cB * ∫ z, F z ∂(((νij.map (fun g => pcoord i j g)).prod
            ((νjk.map (fun g => rcoord j k g)).prod (νik.map (fun g => qcoord i k g)))).map
            shearB2) := by rw [hmapB]
      _ = cB * ∫ x, F (shearB2 x) ∂((νij.map (fun g => pcoord i j g)).prod
            ((νjk.map (fun g => rcoord j k g)).prod (νik.map (fun g => qcoord i k g)))) := by
          rw [integral_map continuous_shearB2.aemeasurable hFc.aestronglyMeasurable]
      _ = cB * ∫ p, ∫ r, ∫ q, F (p, q, r) ∂(νik.map (fun g => qcoord i k g))
            ∂(νjk.map (fun g => rcoord j k g)) ∂(νij.map (fun g => pcoord i j g)) := by
          rw [fubini_shearB2_of (Ap := νij.map (fun g => pcoord i j g))
            (Bp := νjk.map (fun g => rcoord j k g)) (Cp := νik.map (fun g => qcoord i k g)) hFc hFs]

end Work.EKLC7
