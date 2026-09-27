import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLComp.LeafAux

/-!
# The pushforward relation of two measures with equal conditional expectations

Let `ρ, ρ'` be two measures on the group `SL₃(ℝ)`, `S` a measurable set of finite (nonzero)
`ρ`-, `ρ'`-mass, and `x ∈ X₃ = SL₃(ℝ)/SL₃(ℤ)`.  If there is a function `e` on subsets of `X₃`
such that for every `C` in a countable π-system `piBasis` generating the Borel σ-algebra of `X₃`
the averages of `1_C` over `S` along the orbit of `x` agree for `ρ` and `ρ'` in the sense

`∫_{u ∈ S} 1_C(u·x) dρ = (ρ S).toReal * e C`,   `∫_{u ∈ S} 1_C(u·x) dρ' = (ρ' S).toReal * e C`,

then the two pushforwards of the restrictions of `ρ`, `ρ'` to `S` under `u ↦ u·x` are
proportional with the reciprocal constants:

`(ρ' S) • (ρ|_S).map (· · x) = (ρ S) • (ρ'|_S).map (· · x)`.

This is the elementary "two measures whose conditional expectations agree are proportional"
step used to compare the transversal measures coming from the two leafwise systems.

The proof: for `C ∈ piBasis`, the pushforward at `C` is `ρ (S ∩ f⁻¹C)` where `f u = u·x`, and the
Bochner integral of the indicator is the `.toReal` of exactly this number; so
`((ρ|_S).map f) C = ofReal ((ρ S).toReal * e C)`.  Both measures therefore agree on the
π-system `piBasis` after scaling by the reciprocal masses, and they have the same total mass;
`ext_of_piBasis` finishes.
-/

open MeasureTheory Set
open scoped ENNReal
open Work.EKLContract Work.EKLComp

namespace Work.EKLRelCross

/-- The Bochner integral over `S` of the indicator of `C` composed with `u ↦ u • x` is the
(real) measure of `S ∩ {u | u • x ∈ C}`. -/
lemma setIntegral_indicator_smul (ρ : Measure SL3) (S : Set SL3) (C : Set X3) (x : X3)
    (hS : MeasurableSet S) (hC : MeasurableSet C) :
    (∫ u in S, (Set.indicator C (1 : X3 → ℝ)) (u • x) ∂ρ)
      = (ρ (S ∩ (fun u : SL3 => u • x) ⁻¹' C)).toReal := by
  have hfm : Measurable (fun u : SL3 => u • x) := by measurability
  have hpre : MeasurableSet ((fun u : SL3 => u • x) ⁻¹' C) := hC.preimage hfm
  have hcongr : (fun u : SL3 => (Set.indicator C (1 : X3 → ℝ)) (u • x))
      = ((fun u : SL3 => u • x) ⁻¹' C).indicator (1 : SL3 → ℝ) := by
    funext u
    by_cases h : u • x ∈ C
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (by simpa using h)]
      rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (by simpa using h)]
  rw [hcongr]
  rw [← MeasureTheory.integral_indicator (μ := ρ)
      (f := ((fun u : SL3 => u • x) ⁻¹' C).indicator (1 : SL3 → ℝ)) hS]
  rw [Set.indicator_indicator]
  rw [MeasureTheory.integral_indicator_one (hS.inter hpre), MeasureTheory.Measure.real_def]

theorem pushforward_relation_of_condExp (x : Work.EKLContract.X3) (S : Set Work.EKLContract.SL3)
    (ρ ρ' : MeasureTheory.Measure Work.EKLContract.SL3) [MeasureTheory.IsFiniteMeasureOnCompacts ρ] [MeasureTheory.IsFiniteMeasureOnCompacts ρ']
    (hSmeas : MeasurableSet S) (hSfin : ρ S ≠ ⊤) (hSfin' : ρ' S ≠ ⊤)
    (hSpos : ρ S ≠ 0) (hSpos' : ρ' S ≠ 0) (e : Set Work.EKLContract.X3 → ℝ)
    (heq : ∀ C ∈ Work.EKLComp.piBasis,
        (∫ u in S, (Set.indicator C (1 : Work.EKLContract.X3 → ℝ)) (u • x) ∂ρ) = (ρ S).toReal * e C ∧
        (∫ u in S, (Set.indicator C (1 : Work.EKLContract.X3 → ℝ)) (u • x) ∂ρ') = (ρ' S).toReal * e C) :
    (ρ' S) • ((ρ.restrict S).map (fun g : Work.EKLContract.SL3 => g • x))
      = (ρ S) • ((ρ'.restrict S).map (fun g : Work.EKLContract.SL3 => g • x)) := by
  classical
  have hfm : Measurable (fun u : SL3 => u • x) := by measurability
  set μ : Measure X3 := Measure.map (fun u : SL3 => u • x) (ρ.restrict S) with hμ
  set ν : Measure X3 := Measure.map (fun u : SL3 => u • x) (ρ'.restrict S) with hν
  have hμuniv : μ univ = ρ S := by
    rw [hμ, Measure.map_apply hfm MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ]
  have hνuniv : ν univ = ρ' S := by
    rw [hν, Measure.map_apply hfm MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ]
  have key : ∀ C ∈ piBasis, (ρ' S) * μ C = (ρ S) * ν C := by
    intro C hC
    have hCmeas : MeasurableSet C := measurableSet_of_mem_piBasis hC
    have hpre : MeasurableSet ((fun u : SL3 => u • x) ⁻¹' C) := hCmeas.preimage hfm
    obtain ⟨heqρ, heqρ'⟩ := heq C hC
    have hμCeq : μ C = ρ ((fun u : SL3 => u • x) ⁻¹' C ∩ S) := by
      rw [hμ, Measure.map_apply hfm hCmeas, Measure.restrict_apply hpre]
    have hνCeq : ν C = ρ' ((fun u : SL3 => u • x) ⁻¹' C ∩ S) := by
      rw [hν, Measure.map_apply hfm hCmeas, Measure.restrict_apply hpre]
    have hμfin : μ C ≠ ⊤ := by
      rw [hμCeq]
      exact ne_top_of_le_ne_top hSfin (MeasureTheory.measure_mono Set.inter_subset_right)
    have hνfin : ν C ≠ ⊤ := by
      rw [hνCeq]
      exact ne_top_of_le_ne_top hSfin' (MeasureTheory.measure_mono Set.inter_subset_right)
    have hμreal : (μ C).toReal = (ρ S).toReal * e C := by
      rw [hμCeq, Set.inter_comm, ← heqρ, setIntegral_indicator_smul ρ S C x hSmeas hCmeas]
    have hνreal : (ν C).toReal = (ρ' S).toReal * e C := by
      rw [hνCeq, Set.inter_comm, ← heqρ', setIntegral_indicator_smul ρ' S C x hSmeas hCmeas]
    have hρSpos : 0 < (ρ S).toReal := ENNReal.toReal_pos hSpos hSfin
    have hρ'Spos : 0 < (ρ' S).toReal := ENNReal.toReal_pos hSpos' hSfin'
    have hμC : μ C = ENNReal.ofReal ((ρ S).toReal * e C) := by
      rw [← ENNReal.ofReal_toReal hμfin, hμreal]
    have hνC : ν C = ENNReal.ofReal ((ρ' S).toReal * e C) := by
      rw [← ENNReal.ofReal_toReal hνfin, hνreal]
    calc (ρ' S) * μ C
        = (ρ' S) * (ENNReal.ofReal ((ρ S).toReal) * ENNReal.ofReal (e C)) := by
            rw [hμC, ENNReal.ofReal_mul (le_of_lt hρSpos)]
      _ = (ρ S) * ν C := by
            rw [hνC, ENNReal.ofReal_mul (le_of_lt hρ'Spos),
              ENNReal.ofReal_toReal hSfin, ENNReal.ofReal_toReal hSfin']
            ac_rfl
  have htot : ((ρ' S) • μ) univ = ((ρ S) • ν) univ := by
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul, hμuniv, hνuniv,
      mul_comm]
  have hinst : IsFiniteMeasure ((ρ' S) • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul, hμuniv]
    exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hSfin' hSfin)⟩
  exact Work.EKLComp.ext_of_piBasis key htot

end Work.EKLRelCross
