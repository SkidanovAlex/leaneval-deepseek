import Mathlib
import Submission.Work.EKLRelCross.entropy_cs_interface
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLComp.PlaqueToolkit

/-!
# `Work.EKLRelCross.plaque_identity_base`

The local product structure of the leafwise measures at the base point of an orbit plaque.
-/

namespace Work.EKLRelCross

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract
open Work.EKLComp

noncomputable section
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {μ : Measure X3} [IsProbabilityMeasure μ]
variable {U : Subgroup SL3} {ν : X3 → Measure SL3} {X' : Set X3}

/-- `1 ∈ V ε` for `ε > 0`. -/
lemma one_mem_V {ε : ℝ} (hε : 0 < ε) : (1 : SL3) ∈ V ε := by
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_one, sub_self, abs_zero]
  exact hε

/-- **Shape at the base point.** -/
lemma shape_plaqueSigma_base {x₀ : X3} {ε : ℝ} (hε : 0 < ε)
    (hinj : ∀ a ∈ U, ∀ b ∈ U, a • x₀ = b • x₀ → a = b) :
    shape (plaqueSigma U x₀ ε) U x₀ = V ε ∩ (U : Set SL3) := by
  have h := Work.EKLProd.shape_orbitImage U x₀ (V ε ∩ (U : Set SL3)) Set.inter_subset_right hinj
      (1 : SL3) ⟨one_mem_V hε, U.one_mem⟩
  rw [one_smul] at h
  change shape (MeasurableSpace.generateFrom {(fun u : SL3 => u • x₀) '' (V ε ∩ (U : Set SL3))}) U x₀
      = V ε ∩ (U : Set SL3)
  rw [h]
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe, mul_one]
  exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2⟩⟩

/-- **Shape at a translate.** -/
lemma shape_plaqueSigma_translate {x₀ : X3} {ε : ℝ} {u₁ : SL3}
    (hu₁ : u₁ ∈ V ε ∩ (U : Set SL3))
    (hinj : ∀ a ∈ U, ∀ b ∈ U, a • x₀ = b • x₀ → a = b) :
    shape (plaqueSigma U x₀ ε) U (u₁ • x₀) = {u : SL3 | u ∈ U ∧ u * u₁ ∈ V ε} := by
  have h := Work.EKLProd.shape_orbitImage U x₀ (V ε ∩ (U : Set SL3)) Set.inter_subset_right hinj
      u₁ hu₁
  change shape (MeasurableSpace.generateFrom {(fun u : SL3 => u • x₀) '' (V ε ∩ (U : Set SL3))}) U (u₁ • x₀)
      = {u : SL3 | u ∈ U ∧ u * u₁ ∈ V ε}
  rw [h]
  ext u
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, U.mul_mem h.1 hu₁.2⟩⟩

/-- The leafwise average of `1_A (· • x)` over a set `s` is the `ν x`-mass of the preimage box. -/
lemma integral_indicator_smul {ν : X3 → Measure SL3} {x : X3} {s : Set SL3} {A : Set X3}
    (hA : MeasurableSet A) :
    ∫ u in s, (A.indicator (fun _ : X3 => (1:ℝ))) (u • x) ∂(ν x)
      = ((ν x) (s ∩ {u : SL3 | u • x ∈ A})).toReal := by
  classical
  have hcont : Continuous (fun u : SL3 => u • x) := continuous_id.smul continuous_const
  have hmeas : MeasurableSet {u : SL3 | u • x ∈ A} := hA.preimage hcont.measurable
  have hfun : (fun u : SL3 => (A.indicator (fun _ : X3 => (1:ℝ))) (u • x))
      = ({u : SL3 | u • x ∈ A}.indicator (fun _ : SL3 => (1:ℝ))) := by
    funext u
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : u • x ∈ A <;> simp [h]
  rw [hfun, MeasureTheory.setIntegral_indicator hmeas, MeasureTheory.setIntegral_const,
    smul_eq_mul, mul_one, MeasureTheory.measureReal_def]

/-- **Rescaling of the `ν`-mass of the shape.** -/
lemma mass_shape_prop {x₀ : X3} {ε : ℝ} (hε : 0 < ε) {u₁ : SL3}
    (hu₁ : u₁ ∈ V ε ∩ (U : Set SL3)) (hUc : IsClosed (U : Set SL3))
    (hinj : ∀ a ∈ U, ∀ b ∈ U, a • x₀ = b • x₀ → a = b)
    {c : ℝ≥0∞} (hmap : ν (u₁ • x₀) = c⁻¹ • (ν x₀).map (fun g : SL3 => g * u₁⁻¹)) :
    ν (u₁ • x₀) (shape (plaqueSigma U x₀ ε) U (u₁ • x₀))
      = c⁻¹ * ν x₀ (shape (plaqueSigma U x₀ ε) U x₀) := by
  have hsh1 := shape_plaqueSigma_translate (U:=U) (x₀:=x₀) (ε:=ε) hu₁ hinj
  have hsh0 := shape_plaqueSigma_base (U:=U) (x₀:=x₀) (ε:=ε) hε hinj
  have hpre : (fun g : SL3 => g * u₁⁻¹) ⁻¹' {u : SL3 | u ∈ U ∧ u * u₁ ∈ V ε}
      = V ε ∩ (U : Set SL3) := by
    ext h; simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hcU, hcV⟩
      have hhU : h ∈ U := by
        have h' : (h * u₁⁻¹) * u₁ ∈ U := U.mul_mem hcU hu₁.2
        rwa [mul_assoc, inv_mul_cancel, mul_one] at h'
      have hhV : h ∈ V ε := by rwa [mul_assoc, inv_mul_cancel, mul_one] at hcV
      exact ⟨hhV, hhU⟩
    · rintro ⟨hhV, hhU⟩
      exact ⟨U.mul_mem hhU (U.inv_mem hu₁.2), by rwa [mul_assoc, inv_mul_cancel, mul_one]⟩
  have hmeas : MeasurableSet ({u : SL3 | u ∈ U ∧ u * u₁ ∈ V ε}) := by
    have h1 : {u : SL3 | u ∈ U ∧ u * u₁ ∈ V ε} = (U : Set SL3) ∩ ((fun g : SL3 => g * u₁) ⁻¹' V ε) := by
      ext u; rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]; rfl
    rw [h1]
    exact hUc.measurableSet.inter
      (((isOpen_V ε).preimage (continuous_id.mul continuous_const))).measurableSet
  have hm2 : Measurable (fun g : SL3 => g * u₁⁻¹) := (continuous_id.mul continuous_const).measurable
  rw [hsh1, hsh0, hmap, Measure.smul_apply]
  rw [show (Measure.map (fun g : SL3 => g * u₁⁻¹) (ν x₀)) {u : SL3 | u ∈ U ∧ u * u₁ ∈ V ε}
      = ν x₀ ((fun g : SL3 => g * u₁⁻¹) ⁻¹' {u : SL3 | u ∈ U ∧ u * u₁ ∈ V ε})
      from Measure.map_apply hm2 hmeas]
  rw [hpre, smul_eq_mul]

/-- **Rescaling of the `ν`-mass of the shape intersected with the `A`-preimage.** -/
lemma mass_shapeA_prop {x₀ : X3} {ε : ℝ} (hε : 0 < ε) {u₁ : SL3}
    (hu₁ : u₁ ∈ V ε ∩ (U : Set SL3)) (hUc : IsClosed (U : Set SL3))
    (hinj : ∀ a ∈ U, ∀ b ∈ U, a • x₀ = b • x₀ → a = b)
    {A : Set X3} (hA : MeasurableSet A)
    {c : ℝ≥0∞} (hmap : ν (u₁ • x₀) = c⁻¹ • (ν x₀).map (fun g : SL3 => g * u₁⁻¹)) :
    ν (u₁ • x₀) (shape (plaqueSigma U x₀ ε) U (u₁ • x₀) ∩ {u : SL3 | u • (u₁ • x₀) ∈ A})
      = c⁻¹ * ν x₀ (shape (plaqueSigma U x₀ ε) U x₀ ∩ {u : SL3 | u • x₀ ∈ A}) := by
  have hsh1 := shape_plaqueSigma_translate (U:=U) (x₀:=x₀) (ε:=ε) hu₁ hinj
  have hsh0 := shape_plaqueSigma_base (U:=U) (x₀:=x₀) (ε:=ε) hε hinj
  have hpre : (fun g : SL3 => g * u₁⁻¹) ⁻¹'
        ({u : SL3 | u ∈ U ∧ u * u₁ ∈ V ε} ∩ {u : SL3 | u • (u₁ • x₀) ∈ A})
      = (V ε ∩ (U : Set SL3)) ∩ {u : SL3 | u • x₀ ∈ A} := by
    ext h; simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hcU, hcV⟩, hcA⟩
      have hhU : h ∈ U := by
        have h' : (h * u₁⁻¹) * u₁ ∈ U := U.mul_mem hcU hu₁.2
        rwa [mul_assoc, inv_mul_cancel, mul_one] at h'
      have hhV : h ∈ V ε := by rwa [mul_assoc, inv_mul_cancel, mul_one] at hcV
      refine ⟨⟨hhV, hhU⟩, ?_⟩
      rwa [mul_smul, inv_smul_smul] at hcA
    · rintro ⟨⟨hhV, hhU⟩, hhA⟩
      refine ⟨⟨U.mul_mem hhU (U.inv_mem hu₁.2), by rwa [mul_assoc, inv_mul_cancel, mul_one]⟩, ?_⟩
      rwa [mul_smul, inv_smul_smul]
  have hmeas : MeasurableSet ({u : SL3 | u ∈ U ∧ u * u₁ ∈ V ε} ∩ {u : SL3 | u • (u₁ • x₀) ∈ A}) := by
    have h1 : {u : SL3 | u ∈ U ∧ u * u₁ ∈ V ε} = (U : Set SL3) ∩ ((fun g : SL3 => g * u₁) ⁻¹' V ε) := by
      ext u; rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]; rfl
    have h2 : MeasurableSet ((U : Set SL3) ∩ ((fun g : SL3 => g * u₁) ⁻¹' V ε)) :=
      hUc.measurableSet.inter (((isOpen_V ε).preimage (continuous_id.mul continuous_const))).measurableSet
    have h3 : MeasurableSet ({u : SL3 | u • (u₁ • x₀) ∈ A}) :=
      hA.preimage ((continuous_id.smul continuous_const).measurable)
    rw [h1]; exact h2.inter h3
  have hm2 : Measurable (fun g : SL3 => g * u₁⁻¹) := (continuous_id.mul continuous_const).measurable
  rw [hsh1, hsh0, hmap, Measure.smul_apply]
  rw [show (Measure.map (fun g : SL3 => g * u₁⁻¹) (ν x₀))
        ({u : SL3 | u ∈ U ∧ u * u₁ ∈ V ε} ∩ {u : SL3 | u • (u₁ • x₀) ∈ A})
      = ν x₀ ((fun g : SL3 => g * u₁⁻¹) ⁻¹'
          ({u : SL3 | u ∈ U ∧ u * u₁ ∈ V ε} ∩ {u : SL3 | u • (u₁ • x₀) ∈ A}))
      from Measure.map_apply hm2 hmeas]
  rw [hpre, smul_eq_mul]

/-- **The leafwise average ratio is the same at `x₀` and at `u₁ • x₀`.** -/
lemma ratio_translate (hL : IsLeafwise μ U ν X') {x₀ : X3} (hX0 : x₀ ∈ X')
    {ε : ℝ} (hε : 0 < ε) {u₁ : SL3} (hu₁ : u₁ ∈ V ε ∩ (U : Set SL3))
    (hxX : u₁ • x₀ ∈ X') (hUc : IsClosed (U : Set SL3))
    (hinj : ∀ a ∈ U, ∀ b ∈ U, a • x₀ = b • x₀ → a = b)
    {A : Set X3} (hA : MeasurableSet A) :
    (∫ u in shape (plaqueSigma U x₀ ε) U (u₁ • x₀),
        (A.indicator (fun _ : X3 => (1:ℝ))) (u • (u₁ • x₀)) ∂(ν (u₁ • x₀)))
        / ((ν (u₁ • x₀)) (shape (plaqueSigma U x₀ ε) U (u₁ • x₀))).toReal
      = (∫ u in shape (plaqueSigma U x₀ ε) U x₀,
        (A.indicator (fun _ : X3 => (1:ℝ))) (u • x₀) ∂(ν x₀))
        / ((ν x₀) (shape (plaqueSigma U x₀ ε) U x₀)).toReal := by
  obtain ⟨c, hc0, hcT, hc⟩ := hL.equivariant x₀ hX0 u₁ hu₁.2 hxX
  have hm1 : Measurable (fun g : SL3 => g * u₁) := (continuous_id.mul continuous_const).measurable
  have hm2 : Measurable (fun g : SL3 => g * u₁⁻¹) := (continuous_id.mul continuous_const).measurable
  have hcomp : (fun g : SL3 => g * u₁⁻¹) ∘ (fun g : SL3 => g * u₁) = id := by
    funext g; simp
  have hmap : ν (u₁ • x₀) = c⁻¹ • (ν x₀).map (fun g : SL3 => g * u₁⁻¹) := by
    have key : (ν x₀).map (fun g : SL3 => g * u₁⁻¹) = c • (ν (u₁ • x₀)) := by
      rw [hc, Measure.map_smul, Measure.map_map hm2 hm1, hcomp, Measure.map_id] <;> try fun_prop
    rw [key, smul_smul, ENNReal.inv_mul_cancel hc0 hcT, one_smul]
  have hM := mass_shape_prop (U:=U) (ν:=ν) (x₀:=x₀) (ε:=ε) hε hu₁ hUc hinj hmap
  have hS := mass_shapeA_prop (U:=U) (ν:=ν) (x₀:=x₀) (ε:=ε) hε hu₁ hUc hinj hA hmap
  have hcne : (c⁻¹).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨ENNReal.inv_ne_zero.mpr hcT, ENNReal.inv_ne_top.mpr hc0⟩
  rw [integral_indicator_smul (ν := ν) (x := u₁ • x₀) hA,
      integral_indicator_smul (ν := ν) (x := x₀) hA, hS, hM,
      ENNReal.toReal_mul, ENNReal.toReal_mul]
  rw [mul_div_mul_left _ _ hcne]

theorem plaque_identity_base (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3)
    (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    Work.EKLRelCross.PlaqueId μ U ν := by
  rw [PlaqueId]
  have haefree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1 :=
    ae_free_orbit h2 μ U hU t0 ht0 hcontr
  have hXae : ∀ᵐ x ∂μ, x ∈ X' := by
    rw [MeasureTheory.ae_iff, show {a : X3 | ¬ a ∈ X'} = X'ᶜ from rfl]
    exact hL.conull
  filter_upwards [haefree, hXae] with x₀ hfree hx'
  intro ε hε A hA
  have hinj : ∀ a ∈ U, ∀ b ∈ U, a • x₀ = b • x₀ → a = b := by
    intro a ha b hb hab
    have h : (b⁻¹ * a) • x₀ = x₀ := by rw [mul_smul, hab, inv_smul_smul]
    have hh := hfree (b⁻¹ * a) (U.mul_mem (U.inv_mem hb) ha) h
    rw [inv_mul_eq_one] at hh
    exact hh.symm
  by_cases hμP : μ (orbitPlaque U x₀ ε) = 0
  · have hAP : μ (A ∩ orbitPlaque U x₀ ε) = 0 :=
      measure_mono_null Set.inter_subset_right hμP
    rw [hAP, hμP, mul_zero, zero_mul]
  · have hPmeas : MeasurableSet (orbitPlaque U x₀ ε) := Work.EKLProd.borelOrbitImage U hU.1 x₀ ε
    have hfmeas : Measurable (A.indicator (fun _ : X3 => (1:ℝ))) := measurable_const.indicator hA
    have hfb : ∃ C, ∀ y, |(A.indicator (fun _ : X3 => (1:ℝ))) y| ≤ C := ⟨1, fun y => by
      by_cases hy : y ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]⟩
    have hav := Work.EKLComp.plaque_average_eq (U:=U) (ν:=ν) (X':=X') hL (x₀:=x₀) (ε:=ε)
      hε hU.1 hinj hμP (A.indicator (fun _ : X3 => (1:ℝ))) hfmeas hfb
    have hPint : ∫ y in (orbitPlaque U x₀ ε), (A.indicator (fun _ : X3 => (1:ℝ))) y ∂μ
        = (μ (A ∩ orbitPlaque U x₀ ε)).toReal := by
      rw [MeasureTheory.setIntegral_indicator hA, MeasureTheory.setIntegral_const, smul_eq_mul,
        mul_one, MeasureTheory.measureReal_def, Set.inter_comm]
    have hPX : ∀ᵐ x ∂(μ.restrict (orbitPlaque U x₀ ε)), x ∈ X' := MeasureTheory.ae_restrict_of_ae hXae
    have hPmem : ∀ᵐ x ∂(μ.restrict (orbitPlaque U x₀ ε)), x ∈ orbitPlaque U x₀ ε := by
      rw [MeasureTheory.ae_restrict_iff' hPmeas]
      exact Filter.Eventually.of_forall (fun _ h => h)
    have hconst : ∀ᵐ x ∂(μ.restrict (orbitPlaque U x₀ ε)),
        (∫ u in shape (plaqueSigma U x₀ ε) U x, (A.indicator (fun _ : X3 => (1:ℝ))) (u • x) ∂(ν x))
          / ((ν x) (shape (plaqueSigma U x₀ ε) U x)).toReal
        = (∫ u in shape (plaqueSigma U x₀ ε) U x₀,
            (A.indicator (fun _ : X3 => (1:ℝ))) (u • x₀) ∂(ν x₀))
          / ((ν x₀) (shape (plaqueSigma U x₀ ε) U x₀)).toReal := by
      filter_upwards [hPX, hPmem] with x hxX hxP
      obtain ⟨u₁, hu₁, rfl⟩ := hxP
      exact ratio_translate (U:=U) (ν:=ν) (X':=X') (μ:=μ) (A:=A) hL hx' hε hu₁ hxX hU.1 hinj hA
    have hav2 : ∀ᵐ x ∂(μ.restrict (orbitPlaque U x₀ ε)),
        (μ (orbitPlaque U x₀ ε)).toReal⁻¹ * (μ (A ∩ orbitPlaque U x₀ ε)).toReal
          = (∫ u in shape (plaqueSigma U x₀ ε) U x,
              (A.indicator (fun _ : X3 => (1:ℝ))) (u • x) ∂(ν x))
            / ((ν x) (shape (plaqueSigma U x₀ ε) U x)).toReal := by
      filter_upwards [hav] with x hx
      rw [← hx, hPint]
    have hav3 : ∀ᵐ x ∂(μ.restrict (orbitPlaque U x₀ ε)),
        (μ (orbitPlaque U x₀ ε)).toReal⁻¹ * (μ (A ∩ orbitPlaque U x₀ ε)).toReal
          = (∫ u in shape (plaqueSigma U x₀ ε) U x₀,
              (A.indicator (fun _ : X3 => (1:ℝ))) (u • x₀) ∂(ν x₀))
            / ((ν x₀) (shape (plaqueSigma U x₀ ε) U x₀)).toReal := by
      filter_upwards [hav2, hconst] with x h1 h2
      rw [h1, h2]
    have hkey : (μ (orbitPlaque U x₀ ε)).toReal⁻¹ * (μ (A ∩ orbitPlaque U x₀ ε)).toReal
        = (∫ u in shape (plaqueSigma U x₀ ε) U x₀,
            (A.indicator (fun _ : X3 => (1:ℝ))) (u • x₀) ∂(ν x₀))
          / ((ν x₀) (shape (plaqueSigma U x₀ ε) U x₀)).toReal := by
      by_cases hp : (μ (orbitPlaque U x₀ ε)).toReal⁻¹ * (μ (A ∩ orbitPlaque U x₀ ε)).toReal
          = (∫ u in shape (plaqueSigma U x₀ ε) U x₀,
              (A.indicator (fun _ : X3 => (1:ℝ))) (u • x₀) ∂(ν x₀))
            / ((ν x₀) (shape (plaqueSigma U x₀ ε) U x₀)).toReal
      · exact hp
      · exfalso
        have hz : (μ.restrict (orbitPlaque U x₀ ε))
            {x : X3 | ¬ ((μ (orbitPlaque U x₀ ε)).toReal⁻¹ * (μ (A ∩ orbitPlaque U x₀ ε)).toReal
              = (∫ u in shape (plaqueSigma U x₀ ε) U x₀,
                  (A.indicator (fun _ : X3 => (1:ℝ))) (u • x₀) ∂(ν x₀))
                / ((ν x₀) (shape (plaqueSigma U x₀ ε) U x₀)).toReal)} = 0 :=
          (MeasureTheory.ae_iff).mp hav3
        rw [show {x : X3 | ¬ ((μ (orbitPlaque U x₀ ε)).toReal⁻¹ * (μ (A ∩ orbitPlaque U x₀ ε)).toReal
              = (∫ u in shape (plaqueSigma U x₀ ε) U x₀,
                  (A.indicator (fun _ : X3 => (1:ℝ))) (u • x₀) ∂(ν x₀))
                / ((ν x₀) (shape (plaqueSigma U x₀ ε) U x₀)).toReal)} = Set.univ
            from Set.eq_univ_of_forall (fun _ => hp)] at hz
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at hz
        exact hμP hz
    have hsh0base := shape_plaqueSigma_base (U:=U) (x₀:=x₀) (ε:=ε) hε hinj
    rw [hsh0base] at hkey
    rw [integral_indicator_smul (ν := ν) (x := x₀) (s := V ε ∩ (U : Set SL3)) hA] at hkey
    have hbase := Work.EKLProd.plaque_shape_mass (U:=U) (ν:=ν) (X':=X') hL (x₀:=x₀) (ε:=ε)
      hε (1:SL3) ⟨one_mem_V hε, U.one_mem⟩ (by simpa using hx') hinj
    simp only [one_smul] at hbase
    rw [show shape (MeasurableSpace.generateFrom {(fun u : SL3 => u • x₀) '' (V ε ∩ (U : Set SL3))}) U x₀
        = V ε ∩ (U : Set SL3) from hsh0base] at hbase
    have hMpos : ((ν x₀) (V ε ∩ (U : Set SL3))).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hbase.1.ne', hbase.2.ne⟩
    have hμPpos : 0 < (μ (orbitPlaque U x₀ ε)).toReal := ENNReal.toReal_pos hμP (measure_ne_top μ _)
    have hcross : (μ (A ∩ orbitPlaque U x₀ ε)).toReal * ((ν x₀) (V ε ∩ (U : Set SL3))).toReal
        = (μ (orbitPlaque U x₀ ε)).toReal
          * ((ν x₀) ((V ε ∩ (U : Set SL3)) ∩ {u : SL3 | u • x₀ ∈ A})).toReal := by
      have hμ : (μ (orbitPlaque U x₀ ε)).toReal ≠ 0 := hμPpos.ne'
      rw [eq_div_iff hMpos] at hkey
      rw [mul_assoc] at hkey
      rw [inv_mul_eq_iff_eq_mul₀ hμ] at hkey
      exact hkey
    have hfin1 : (μ (A ∩ orbitPlaque U x₀ ε)) * ((ν x₀) (V ε ∩ (U : Set SL3))) ≠ ⊤ :=
      ENNReal.mul_ne_top (measure_ne_top μ _) hbase.2.ne
    have hfin2 : (μ (orbitPlaque U x₀ ε))
        * ((ν x₀) ((V ε ∩ (U : Set SL3)) ∩ {u : SL3 | u • x₀ ∈ A})) ≠ ⊤ :=
      ENNReal.mul_ne_top (measure_ne_top μ _)
        (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hbase.2).ne
    have hENN : (μ (A ∩ orbitPlaque U x₀ ε)) * ((ν x₀) (V ε ∩ (U : Set SL3)))
        = (μ (orbitPlaque U x₀ ε))
          * ((ν x₀) ((V ε ∩ (U : Set SL3)) ∩ {u : SL3 | u • x₀ ∈ A})) := by
      rw [← ENNReal.toReal_eq_toReal_iff' hfin1 hfin2, ENNReal.toReal_mul, ENNReal.toReal_mul]
      exact hcross
    have hset : (V ε ∩ (U : Set SL3)) ∩ {u : SL3 | u • x₀ ∈ A}
        = {u : SL3 | u ∈ V ε ∩ (U : Set SL3) ∧ u • x₀ ∈ A} := by
      ext u; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [mul_comm ((ν x₀) (V ε ∩ (U : Set SL3))) (μ (A ∩ orbitPlaque U x₀ ε)), hENN, hset]

end

end Work.EKLRelCross
