import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.conjBox_measurable
import Submission.Work.EKLC6Core.measurable_growthFun
import Submission.Work.EKLC6Core.log_of_inv_mass

/-!
# `EKLC6Core.growth_glue` — glue for the additivity of the growth functions

The product box `B₀ = B₁^T · B₁^U ⊆ H` and the pointwise coboundary identity for the three growth
functions of a product decomposition `H = T · U` (see `EKLC6Core.growth_integral_sup`).

This module is imported by `EKLC6Core.rectangle_mass` (via its sub-lemma
`rect_mass_factor`, which uses `mem_image2_mul_iff`), hence it must not depend on
`rectangle_mass`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Pointwise
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## The product box `B₀ = B₁^T · B₁^U` -/

/-- The product box `B₁^T · B₁^U`: the set whose `νH`-mass is the proportionality constant of the
product structure in the normalisation of the frozen contract. -/
def prodBox (T U : Subgroup SL3) : Set SL3 :=
  Set.image2 (fun a b : SL3 => a * b) (Box1 T) (Box1 U)

theorem isCompact_prodBox {T U : Subgroup SL3} (hT : IsHoro T) (hU : IsHoro U) :
    IsCompact (prodBox T U) :=
  (isCompact_box1 hT).mul (isCompact_box1 hU)

theorem measurableSet_prodBox {T U : Subgroup SL3} (hT : IsHoro T) (hU : IsHoro U) :
    MeasurableSet (prodBox T U) :=
  (isCompact_prodBox hT hU).isClosed.measurableSet

/-! ## Elementary glue -/

/-- The product map is injective on `T × U` when `T ∩ U = {1}`. -/
theorem mul_inj_on {T U : Subgroup SL3} (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {g u a b : SL3} (hg : g ∈ T) (hu : u ∈ U) (ha : a ∈ T) (hb : b ∈ U)
    (h : g * u = a * b) : g = a ∧ u = b := by
  have h1 : a⁻¹ * g = b * u⁻¹ := by
    calc a⁻¹ * g = a⁻¹ * g * (u * u⁻¹) := by group
      _ = a⁻¹ * (g * u) * u⁻¹ := by group
      _ = a⁻¹ * (a * b) * u⁻¹ := by rw [h]
      _ = b * u⁻¹ := by group
  have hmT : a⁻¹ * g ∈ T := T.mul_mem (T.inv_mem ha) hg
  have hmU : b * u⁻¹ ∈ U := U.mul_mem hb (U.inv_mem hu)
  have h2 : a⁻¹ * g = 1 := hdisj _ hmT (by rw [h1]; exact hmU)
  have h3 : b * u⁻¹ = 1 := by rw [← h1]; exact h2
  exact ⟨(inv_mul_eq_one.mp h2).symm, (mul_inv_eq_one.mp h3).symm⟩

/-- The indicator of a product rectangle factorizes on `T × U`. -/
theorem mem_image2_mul_iff {T U : Subgroup SL3} (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {AT AU : Set SL3} (hAT : AT ⊆ (T : Set SL3)) (hAU : AU ⊆ (U : Set SL3))
    {g u : SL3} (hg : g ∈ T) (hu : u ∈ U) :
    g * u ∈ Set.image2 (fun a b : SL3 => a * b) AT AU ↔ g ∈ AT ∧ u ∈ AU := by
  constructor
  · intro h
    rw [Set.mem_image2] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    obtain ⟨hga, hub⟩ := mul_inj_on hdisj hg hu (hAT ha) (hAU hb) hab.symm
    exact ⟨hga.symm ▸ ha, hub.symm ▸ hb⟩
  · rintro ⟨hg', hu'⟩
    exact Set.mem_image2.mpr ⟨g, hg', u, hu', rfl⟩

/-- Conjugation by `aDiag t` distributes over products of sets. -/
theorem conjBy_image2_mul (t : Fin 3 → ℝ) (AT AU : Set SL3) :
    conjBy t (Set.image2 (fun a b : SL3 => a * b) AT AU)
      = Set.image2 (fun a b : SL3 => a * b) (conjBy t AT) (conjBy t AU) := by
  ext g
  simp only [conjBy, Set.mem_image, Set.mem_image2]
  constructor
  · rintro ⟨h, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨aDiag t * a * (aDiag t)⁻¹, ⟨a, ha, rfl⟩, aDiag t * b * (aDiag t)⁻¹,
      ⟨b, hb, rfl⟩, by group⟩
  · rintro ⟨x, ⟨a, ha, rfl⟩, y, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a * b, ⟨a, ha, b, hb, rfl⟩, by group⟩

theorem conjBox_eq_conjBy (U : Subgroup SL3) (t : Fin 3 → ℝ) :
    conjBox U t = conjBy t (Box1 U) := rfl

/-! ## The pointwise coboundary identity -/

/-- **The pointwise coboundary identity.**  At a point `x` where the product structure holds with
constants `cx` (at `x`) and `cy` (at `aDiag (-t) • x`), where the `A`-covariance of the three
leaf-wise systems is given by the constants `cH`, `cT`, `cU`, and where the rectangle-mass
identities of `Work.EKLC6Core.rectangle_mass` hold for the product box `prodBox T U` (at both
points) and for its conjugate `conjBy t (prodBox T U)`, the difference of the three growth
functions is the coboundary of the `νH`-mass of the product box. -/
theorem growthFun_sub_eq {H T U : Subgroup SL3}
    {νH νT νU : X3 → Measure SL3} {t : Fin 3 → ℝ} {x : X3}
    {cx cy : ℝ} (hcx : 0 < cx) (hcy : 0 < cy)
    {cH cT cU : ℝ≥0∞} (hcH0 : cH ≠ 0) (hcHT : cH ≠ ⊤) (hcT0 : cT ≠ 0) (hcTT : cT ≠ ⊤)
    (hcU0 : cU ≠ 0) (hcUT : cU ≠ ⊤)
    (hHrel : νH (aDiag (-t) • x) = cH • (νH x).map (fun g => aDiag (-t) * g * (aDiag (-t))⁻¹))
    (hTrel : νT (aDiag (-t) • x) = cT • (νT x).map (fun g => aDiag (-t) * g * (aDiag (-t))⁻¹))
    (hUrel : νU (aDiag (-t) • x) = cU • (νU x).map (fun g => aDiag (-t) * g * (aDiag (-t))⁻¹))
    (hHnorm : νH (aDiag (-t) • x) (Box1 H) = 1) (hTnorm : νT (aDiag (-t) • x) (Box1 T) = 1)
    (hUnorm : νU (aDiag (-t) • x) (Box1 U) = 1)
    (hHbox : MeasurableSet (Box1 H)) (hTbox : MeasurableSet (Box1 T))
    (hUbox : MeasurableSet (Box1 U)) (hB0m : MeasurableSet (prodBox T U))
    (hrectT : νH x (Set.image2 (fun a b : SL3 => a * b) (conjBox T t) (conjBox U t))
      = ENNReal.ofReal cx * (νT x (conjBox T t) * νU x (conjBox U t)))
    (hrect0 : νH x (prodBox T U) = ENNReal.ofReal cx)
    (hrectφ : νH (aDiag (-t) • x) (prodBox T U) = ENNReal.ofReal cy) :
    growthFun H νH t x - growthFun T νT t x - growthFun U νU t x
      = Real.log cy - Real.log cx := by
  classical
  have hposH : 0 < cH.toReal := ENNReal.toReal_pos hcH0 hcHT
  have hposT : 0 < cT.toReal := ENNReal.toReal_pos hcT0 hcTT
  have hposU : 0 < cU.toReal := ENNReal.toReal_pos hcU0 hcUT
  have hconj : conjBy t (prodBox T U)
      = Set.image2 (fun a b : SL3 => a * b) (conjBox T t) (conjBox U t) := by
    rw [prodBox, conjBox_eq_conjBy, conjBox_eq_conjBy]
    exact conjBy_image2_mul t (Box1 T) (Box1 U)
  have hmassH : νH x (conjBox H t) = cH⁻¹ := by
    have hm : (νH x).map (fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹)
        = cH⁻¹ • νH (aDiag (-t) • x) := by
      rw [hHrel, smul_smul, ENNReal.inv_mul_cancel hcH0 hcHT, one_smul]
    calc νH x (conjBox H t)
        = νH x (conjBy t (Box1 H)) := rfl
      _ = νH x ((fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹) ⁻¹' (Box1 H)) := by
            rw [preimage_conj_neg]
      _ = ((νH x).map (fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹)) (Box1 H) := by
            rw [Measure.map_apply (measurable_conj (-t)) hHbox]
      _ = (cH⁻¹ • νH (aDiag (-t) • x)) (Box1 H) := by rw [hm]
      _ = cH⁻¹ * νH (aDiag (-t) • x) (Box1 H) := by rw [Measure.smul_apply, smul_eq_mul]
      _ = cH⁻¹ * 1 := by rw [hHnorm]
      _ = cH⁻¹ := mul_one _
  have hmassT : νT x (conjBox T t) = cT⁻¹ := by
    have hm : (νT x).map (fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹)
        = cT⁻¹ • νT (aDiag (-t) • x) := by
      rw [hTrel, smul_smul, ENNReal.inv_mul_cancel hcT0 hcTT, one_smul]
    calc νT x (conjBox T t)
        = νT x (conjBy t (Box1 T)) := rfl
      _ = νT x ((fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹) ⁻¹' (Box1 T)) := by
            rw [preimage_conj_neg]
      _ = ((νT x).map (fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹)) (Box1 T) := by
            rw [Measure.map_apply (measurable_conj (-t)) hTbox]
      _ = (cT⁻¹ • νT (aDiag (-t) • x)) (Box1 T) := by rw [hm]
      _ = cT⁻¹ * νT (aDiag (-t) • x) (Box1 T) := by rw [Measure.smul_apply, smul_eq_mul]
      _ = cT⁻¹ * 1 := by rw [hTnorm]
      _ = cT⁻¹ := mul_one _
  have hmassU : νU x (conjBox U t) = cU⁻¹ := by
    have hm : (νU x).map (fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹)
        = cU⁻¹ • νU (aDiag (-t) • x) := by
      rw [hUrel, smul_smul, ENNReal.inv_mul_cancel hcU0 hcUT, one_smul]
    calc νU x (conjBox U t)
        = νU x (conjBy t (Box1 U)) := rfl
      _ = νU x ((fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹) ⁻¹' (Box1 U)) := by
            rw [preimage_conj_neg]
      _ = ((νU x).map (fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹)) (Box1 U) := by
            rw [Measure.map_apply (measurable_conj (-t)) hUbox]
      _ = (cU⁻¹ • νU (aDiag (-t) • x)) (Box1 U) := by rw [hm]
      _ = cU⁻¹ * νU (aDiag (-t) • x) (Box1 U) := by rw [Measure.smul_apply, smul_eq_mul]
      _ = cU⁻¹ * 1 := by rw [hUnorm]
      _ = cU⁻¹ := mul_one _
  have hlink : νH x (conjBy t (prodBox T U))
      = cH⁻¹ * νH (aDiag (-t) • x) (prodBox T U) := by
    have hm : (νH x).map (fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹)
        = cH⁻¹ • νH (aDiag (-t) • x) := by
      rw [hHrel, smul_smul, ENNReal.inv_mul_cancel hcH0 hcHT, one_smul]
    calc νH x (conjBy t (prodBox T U))
        = νH x ((fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹) ⁻¹' (prodBox T U)) := by
            rw [preimage_conj_neg]
      _ = ((νH x).map (fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹)) (prodBox T U) := by
            rw [Measure.map_apply (measurable_conj (-t)) hB0m]
      _ = (cH⁻¹ • νH (aDiag (-t) • x)) (prodBox T U) := by rw [hm]
      _ = cH⁻¹ * νH (aDiag (-t) • x) (prodBox T U) := by rw [Measure.smul_apply, smul_eq_mul]
  have hkey : cH⁻¹ * ENNReal.ofReal cy = ENNReal.ofReal cx * (cT⁻¹ * cU⁻¹) := by
    rw [← hrectφ, ← hlink, hconj, hrectT, hmassT, hmassU]
  have hreal : cH.toReal⁻¹ * cy = cx * (cT.toReal⁻¹ * cU.toReal⁻¹) := by
    have h := congrArg ENNReal.toReal hkey
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (le_of_lt hcy),
      ENNReal.toReal_ofReal (le_of_lt hcx)] at h
    exact h
  have hmul : cy * cT.toReal * cU.toReal = cH.toReal * cx := by
    have h1 := hreal
    field_simp at h1
    linarith [h1]
  have hlog : Real.log cH.toReal
      = Real.log cT.toReal + Real.log cU.toReal + Real.log cy - Real.log cx := by
    have hA : Real.log (cy * (cT.toReal * cU.toReal)) = Real.log (cH.toReal * cx) := by
      rw [show cy * (cT.toReal * cU.toReal) = cy * cT.toReal * cU.toReal by ring, hmul]
    rw [Real.log_mul (ne_of_gt hcy) (ne_of_gt (mul_pos hposT hposU)),
      Real.log_mul (ne_of_gt hposT) (ne_of_gt hposU),
      Real.log_mul (ne_of_gt hposH) (ne_of_gt hcx)] at hA
    linarith [hA]
  have hgH : growthFun H νH t x = Real.log cH.toReal := by
    refine log_of_inv_mass (U := H) (ν := νH) t x hposH ?_
    rw [hmassH, ENNReal.toReal_inv]
  have hgT : growthFun T νT t x = Real.log cT.toReal := by
    refine log_of_inv_mass (U := T) (ν := νT) t x hposT ?_
    rw [hmassT, ENNReal.toReal_inv]
  have hgU : growthFun U νU t x = Real.log cU.toReal := by
    refine log_of_inv_mass (U := U) (ν := νU) t x hposU ?_
    rw [hmassU, ENNReal.toReal_inv]
  rw [hgH, hgT, hgU, hlog]
  ring

