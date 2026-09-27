import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.VolDefs
import Submission.Work.Mostow.HaarBase
import Submission.Work.Mostow.volHImageNull
import Submission.Work.Mostow.measureFundLeOrbit
import Submission.Work.Mostow.hjacEquivariant
import Submission.Work.Mostow.hjacAeEqOneOfIntegralEq
import Submission.Work.Mostow.areaFormula
import Submission.Work.Mostow.continuousEqOneOfAeEqOne

/-! Guidance from the project lead (the requester):

# Area V — volumeSqueeze : VolumeProp n   (lead's design)

Data: lattices Γ, Λ (HypLattice), a hom f, F C¹ surjective, F(γ•u) = f(γ)•F(u), hjac F ≤ 1, fundamental domains
DΓ, DΛ for volH. Prove (1) volH DΛ ≤ volH DΓ, (2) if moreover volH DΓ ≤ volH DΛ then hjac F ≡ 1.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal

noncomputable section

variable {n : ℕ}

/-! ## The main theorem -/

theorem volumeSqueeze (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) :
    VolumeProp n := by
  intro Γ Λ hΓ hΛ f F hFC hFsurj hFE hFJ DΓ DΛ hDΓ hDΛ
  have hAone : ∀ u : E n, (1 : PO n 1) • u = u := hA.2.2.2.1
  have hAmul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := hA.2.2.2.2.1
  have hIcont : ∀ g : PO n 1, ContDiff ℝ 1 (fun u : E n => g • u) := hI.2.2.2.2.2.2.2.2.1
  have hImp : ∀ g : PO n 1, MeasurePreserving (fun u : E n => g • u) (volH n) (volH n) :=
    hI.2.2.2.2.2.2.2.2.2.2.2.1
  -- the action of `PO n 1` on `E n` as a `MulAction`, and the induced actions of the lattices
  letI : MulAction (PO n 1) (E n) := { one_smul := hAone, mul_smul := hAmul }
  letI : MulAction Γ (E n) := inferInstance
  letI : MulAction Λ (E n) := inferInstance
  haveI hmcΓ : MeasurableConstSMul Γ (E n) :=
    ⟨fun c => (hIcont (c : PO n 1)).continuous.measurable⟩
  haveI hmcΛ : MeasurableConstSMul Λ (E n) :=
    ⟨fun c => (hIcont (c : PO n 1)).continuous.measurable⟩
  haveI hsmΓ : SMulInvariantMeasure Γ (E n) (volH n) :=
    ⟨fun c s hs => (hImp (c : PO n 1)).measure_preimage hs.nullMeasurableSet⟩
  haveI hsmΛ : SMulInvariantMeasure Λ (E n) (volH n) :=
    ⟨fun c s hs => (hImp (c : PO n 1)).measure_preimage hs.nullMeasurableSet⟩
  haveI hcΓ : Countable Γ := countable_of_isDiscrete (PO n 1) hΓ.1
  haveI hcΛ : Countable Λ := countable_of_isDiscrete (PO n 1) hΛ.1
  -- finiteness of the volume of `DΓ`
  have hfinDΓ : volH n DΓ < ⊤ := by
    obtain ⟨D, hD, hDtop⟩ := hΓ.2
    rw [IsFundamentalDomain.measure_eq hDΓ hD]
    exact lt_top_iff_ne_top.mpr hDtop
  -- a measurable version of `DΓ`
  obtain ⟨S, hSsub, hSmeas, hSae⟩ := hDΓ.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hIntEq : ∫⁻ u in S, ENNReal.ofReal (hjac F u) ∂(volH n)
      = ∫⁻ u in DΓ, ENNReal.ofReal (hjac F u) ∂(volH n) := setLIntegral_congr hSae
  have hNullDS : volH n (DΓ \ S) = 0 := by
    have h : ∀ᵐ x ∂(volH n), x ∉ DΓ \ S := by
      filter_upwards [hSae] with x hx hx'
      exact hx'.2 (hx.mpr hx'.1)
    have := ae_iff.mp h
    simpa only [Set.mem_setOf_eq, not_not, Set.ofPred_mem_eq] using this
  -- the weighted area formula on `S`
  obtain ⟨B, hBmeas, hBsub, hBle⟩ := areaFormula n hFC hSmeas
  obtain ⟨M, hMsub, hMmeas, hM0⟩ :=
    exists_measurable_superset_of_null (volHImageNull n hFC hNullDS)
  have hE'meas : MeasurableSet (B ∪ M) := hBmeas.union hMmeas
  have hE'sub : F '' DΓ ⊆ B ∪ M := by
    rintro w ⟨u, hu, rfl⟩
    by_cases huS : u ∈ S
    · exact Or.inl (hBsub ⟨u, huS, rfl⟩)
    · exact Or.inr (hMsub ⟨u, ⟨hu, huS⟩, rfl⟩)
  have hE'le : volH n (B ∪ M) ≤ ∫⁻ u in DΓ, ENNReal.ofReal (hjac F u) ∂(volH n) := by
    have h2 : volH n B + volH n M
        ≤ (∫⁻ u in S, ENNReal.ofReal (hjac F u) ∂(volH n)) + 0 :=
      add_le_add hBle (le_of_eq hM0)
    calc volH n (B ∪ M) ≤ volH n B + volH n M := measure_union_le B M
      _ ≤ (∫⁻ u in S, ENNReal.ofReal (hjac F u) ∂(volH n)) + 0 := h2
      _ = ∫⁻ u in DΓ, ENNReal.ofReal (hjac F u) ∂(volH n) := by rw [add_zero, hIntEq]
  -- `F '' DΓ` meets every `Λ`-orbit almost everywhere
  have hNnull : volH n {u : E n | ¬ ∃ γ : Γ, γ • u ∈ DΓ} = 0 := ae_iff.mp hDΓ.ae_covers
  have hImNnull : volH n (F '' {u : E n | ¬ ∃ γ : Γ, γ • u ∈ DΓ}) = 0 :=
    volHImageNull n hFC hNnull
  have hcov : ∀ᵐ w ∂(volH n), ∃ l : Λ, l • w ∈ B ∪ M := by
    rw [ae_iff]
    refine measure_mono_null ?_ hImNnull
    rintro w hw
    obtain ⟨u, rfl⟩ := hFsurj w
    by_contra hcon
    have hu : ∃ γ : Γ, γ • u ∈ DΓ := by
      by_contra h'
      exact hcon ⟨u, h', rfl⟩
    obtain ⟨γ, hγ⟩ := hu
    refine hw ⟨f γ, ?_⟩
    show (f γ : PO n 1) • F u ∈ B ∪ M
    rw [← hFE γ u]
    exact hE'sub ⟨γ • u, hγ, rfl⟩
  -- the fundamental domain inequality
  have hle1 : volH n DΛ ≤ volH n (B ∪ M) := measureFundLeOrbit (volH n) hDΛ hE'meas hcov
  have hle3 : ∫⁻ u in DΓ, ENNReal.ofReal (hjac F u) ∂(volH n) ≤ volH n DΓ := by
    calc ∫⁻ u in DΓ, ENNReal.ofReal (hjac F u) ∂(volH n)
        ≤ ∫⁻ _u in DΓ, (1 : ℝ≥0∞) ∂(volH n) :=
          setLIntegral_mono measurable_const (fun u _ => by
            simpa using ENNReal.ofReal_le_ofReal (hFJ u))
      _ = volH n DΓ := setLIntegral_one _
  have hle3' : ∫⁻ u in DΓ, ENNReal.ofReal (hjac F u) ∂(volH n) ≤ volH n DΓ := hle3
  refine ⟨hle1.trans (hE'le.trans hle3'), fun hvol => ?_⟩
  -- the equality case
  have hEq : ∫⁻ u in DΓ, ENNReal.ofReal (hjac F u) ∂(volH n) = volH n DΓ :=
    le_antisymm hle3' (hvol.trans (hle1.trans hE'le))
  have hfinS : volH n S < ⊤ := by
    rw [measure_congr hSae]
    exact hfinDΓ
  have hEqS : ∫⁻ u in S, ENNReal.ofReal (hjac F u) ∂(volH n) = volH n S := by
    rw [hIntEq, hEq, (measure_congr hSae).symm]
  have haeS : ∀ᵐ u ∂(volH n), u ∈ S → hjac F u = 1 :=
    hjacAeEqOneOfIntegralEq n hFC hFJ hSmeas hfinS hEqS
  have hnot : ∀ᵐ u ∂(volH n), u ∉ DΓ \ S := by
    rw [ae_iff]
    simpa only [Set.ofPred_mem_eq, not_not] using hNullDS
  have haeD : ∀ᵐ u ∂(volH n), u ∈ DΓ → hjac F u = 1 := by
    filter_upwards [haeS, hnot] with u hu huNot
    intro huD
    exact hu (by by_contra h; exact huNot ⟨huD, h⟩)
  exact continuousEqOneOfAeEqOne n hI hDΓ (hjacContinuous n hFC)
    (hjacEquivariant n hI f hFC hFE) haeD

end

end Work.Mostow
