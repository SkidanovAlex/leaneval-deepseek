import Mathlib
import Submission.Work.EKLProd.BoxFlowerDefs

/-!
# Measurable section of the product-box parametrising map

`boxParam T U R C = ((V R ∩ T) × (V R ∩ U)) × C` parametrises the product-box collar of a
transversal `C`, and `boxParamMap (t, u, c) = (t * u) • c` maps it onto the collar.  This module
proves that, under the hypotheses of the box-flower construction, `boxParamMap` is injective on
`boxParam T U R C` and has a **measurable** left inverse:

* `measurableSet_boxParam` — the parametrising set is Borel;
* `continuous_boxParamMap` — the parametrising map is continuous;
* `boxParamMap_injOn` — injectivity, from the *uniqueness* of the decomposition `T · U`
  (`hdisj`, i.e. `T ⊓ U = 1`) and the cross-section property of `C` inside the displacement ball
  `Ucl H ρ` (which dominates `(prodBox T U R)⁻¹ · prodBox T U R` by `hbound`);
* `box_measSection` — the measurable section, obtained from the Lusin–Suslin theorem
  (`ContinuousOn.measurableEmbedding`, the image of a Borel set under a continuous injective map
  in a Polish space is Borel, and the inverse is measurable) applied to the *restriction* of
  `boxParamMap` to `boxParam T U R C`, extended measurably to all of `X₃` by
  `MeasurableEmbedding.exists_measurable_extend`.

The statement of `box_measSection` is the one requested by the product-box flower component of the
Einsiedler–Katok–Lindenstrauss formalisation; the hypotheses `hfreeH` (freeness of the `H`-orbit
on `C`) is not needed for the section itself, but belongs to the same geometric datum.
-/

open MeasureTheory Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLProd

open Work.EKLContract

/-- The parametrising set `boxParam T U R C` is Borel: `V R` is open, `T` and `U` are closed. -/
theorem measurableSet_boxParam (T U : Subgroup SL3) (hTc : IsClosed (T : Set SL3))
    (hUc : IsClosed (U : Set SL3)) (R : ℝ) {C : Set X3} (hC : MeasurableSet C) :
    MeasurableSet (boxParam T U R C) := by
  have hV : MeasurableSet (V R) := by
    rw [Work.EKLContract.Lemmas.V_eq_iInter]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
      (isOpen_lt (by fun_prop : Continuous (fun g : SL3 =>
        |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|))
        continuous_const).measurableSet))
  unfold boxParam
  exact (hV.inter hTc.measurableSet).prod ((hV.inter hUc.measurableSet).prod hC)

/-- The parametrising map of the product-box flower is continuous. -/
theorem continuous_boxParamMap : Continuous (boxParamMap : SL3 × SL3 × X3 → X3) := by
  unfold boxParamMap
  fun_prop

/-- **Injectivity of the product-box parametrisation.**  If `(prodBox T U R)⁻¹ · prodBox T U R`
lies in the displacement ball `Ucl H ρ` and `C` meets every `Ucl H ρ`-translate of itself only at
the origin (the cross-section property), then `boxParamMap` is injective on the parametrising set.

The decomposition `t * u` of an element of the product box is unique because `T ⊓ U = 1`. -/
theorem boxParamMap_injOn {H T U : Subgroup SL3} (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {R ρ : ℝ} {C : Set X3}
    (hbound : ∀ g ∈ prodBox T U R, ∀ g' ∈ prodBox T U R, g'⁻¹ * g ∈ Work.EKLComp.Ucl H ρ)
    (hcross : ∀ c ∈ C, ∀ v ∈ Work.EKLComp.Ucl H ρ, v • c ∈ C → v = 1) :
    Set.InjOn boxParamMap (boxParam T U R C) := by
  rintro p ⟨hp1, hp2, hpc⟩ q ⟨hq1, hq2, hqc⟩ hpq
  have hg : p.1 * p.2.1 ∈ prodBox T U R := Set.mul_mem_mul hp1 hp2
  have hg' : q.1 * q.2.1 ∈ prodBox T U R := Set.mul_mem_mul hq1 hq2
  have hpq' : (p.1 * p.2.1) • p.2.2 = (q.1 * q.2.1) • q.2.2 := hpq
  have hv : (q.1 * q.2.1)⁻¹ * (p.1 * p.2.1) ∈ Work.EKLComp.Ucl H ρ := hbound _ hg _ hg'
  have hvc : ((q.1 * q.2.1)⁻¹ * (p.1 * p.2.1)) • p.2.2 = q.2.2 := by
    rw [mul_smul, hpq', inv_smul_smul]
  have hv1 : (q.1 * q.2.1)⁻¹ * (p.1 * p.2.1) = 1 :=
    hcross p.2.2 hpc _ hv (by rw [hvc]; exact hqc)
  have hcc : p.2.2 = q.2.2 := by rw [← hvc, hv1, one_smul]
  have hgg : p.1 * p.2.1 = q.1 * q.2.1 := by
    have h : q.1 * q.2.1 = p.1 * p.2.1 := inv_mul_eq_one.mp hv1
    exact h.symm
  have htet : p.1 = q.1 := hT_hU_unique hdisj hp1.2 hp2.2 hq1.2 hq2.2 hgg
  have huhu : p.2.1 = q.2.1 := by
    have h : p.1 * p.2.1 = p.1 * q.2.1 := by rw [← htet] at hgg; exact hgg
    exact mul_left_cancel h
  exact Prod.ext htet (Prod.ext huhu hcc)

/-- **Measurable section of the product-box parametrisation.**  Under the hypotheses of the
product-box flower construction, `boxParamMap` restricted to `boxParam T U R C` is a Borel
isomorphism onto its (Borel) image, and its inverse extends to a measurable map on all of `X₃`. -/
theorem box_measSection {H T U : Subgroup Work.EKLContract.SL3}
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hTc : IsClosed (T : Set Work.EKLContract.SL3))
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    {R ρ : ℝ} {C : Set Work.EKLContract.X3} (hC : MeasurableSet C)
    (hbound : ∀ g ∈ Work.EKLProd.prodBox T U R, ∀ g' ∈ Work.EKLProd.prodBox T U R,
      g'⁻¹ * g ∈ Work.EKLComp.Ucl H ρ)
    (hfreeH : ∀ c ∈ C, ∀ h₁ ∈ H, ∀ h₂ ∈ H, h₁ • c = h₂ • c → h₁ = h₂)
    (hcross : ∀ c ∈ C, ∀ v ∈ Work.EKLComp.Ucl H ρ, v • c ∈ C → v = 1)
    (hne : (Work.EKLProd.boxParam T U R C).Nonempty) :
    ∃ ψ : Work.EKLContract.X3 →
        Work.EKLContract.SL3 × Work.EKLContract.SL3 × Work.EKLContract.X3,
      Measurable ψ ∧ ∀ p ∈ Work.EKLProd.boxParam T U R C, ψ (Work.EKLProd.boxParamMap p) = p := by
  haveI hpolSL : PolishSpace SL3 := Work.EKLContract.Lemmas.polishSpace_specialLinearGroup
  haveI hpolX : PolishSpace X3 := Work.EKLComp.X3Background.2.2.2.1
  have hA : MeasurableSet (boxParam T U R C) := measurableSet_boxParam T U hTc hUc R hC
  have hinj : Set.InjOn boxParamMap (boxParam T U R C) := boxParamMap_injOn hdisj hbound hcross
  have hcont : ContinuousOn boxParamMap (boxParam T U R C) :=continuous_boxParamMap.continuousOn
  have hemb : MeasurableEmbedding ((boxParam T U R C).domRestrict boxParamMap) :=
    ContinuousOn.measurableEmbedding hA hcont hinj
  obtain ⟨p0, _hp0⟩ := hne
  obtain ⟨ψ, hψmeas, hψcomp⟩ := hemb.exists_measurable_extend
      (g := fun x : (boxParam T U R C) => (x : SL3 × SL3 × X3))
      measurable_subtype_coe (fun _ => ⟨p0⟩)
  refine ⟨ψ, hψmeas, ?_⟩
  intro p hp
  have h1 : ψ (boxParamMap p) = ((⟨p, hp⟩ : (boxParam T U R C)) : SL3 × SL3 × X3) := by
    have := congrFun hψcomp ⟨p, hp⟩
    simpa [Set.domRestrict_apply] using this
  simpa using h1

end Work.EKLProd
