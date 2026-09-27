import Mathlib
import Submission.Work.EKLC6Core.growth_integral_sup
import Submission.Work.EKLC6Core.growth_glue
import Submission.Work.EKLC6Core.rectangle_mass
import Submission.Work.EKLC6Core.measurable_growthFun
import Submission.Work.EKLContract.Interfaces

open MeasureTheory Filter Topology
open scoped ENNReal Pointwise
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **The pointwise coboundary identity, almost everywhere.**

Combining the product structure of the leaf-wise measures (`P_Product`) with the `A`-covariance
of `νH`, `νT`, `νU` and the rectangle-mass formula, the difference of the three growth functions
is the coboundary, under the flow map `aDiag (-t)`, of the `νH`-mass of the product box
`prodBox T U = B₁^T · B₁^U`.  This is the a.e. identity on which the additivity of the entropy
contributions (`EKLC6Core.growth_integral_sup`) rests. -/
theorem growthFun_sub_eq_ae {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hprod : Work.EKLContract.P_Product)
    {H T U : Subgroup Work.EKLContract.SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hHT : Work.EKLContract.IsHoro T) (hHU : Work.EKLContract.IsHoro U)
    (hHH : Work.EKLContract.IsHoro H)
    (hcent : ∃ t' : Fin 3 → ℝ,
      (∀ g ∈ T, Work.EKLContract.aDiag t' * g = g * Work.EKLContract.aDiag t') ∧
      (∀ u ∈ U, Filter.Tendsto
        (fun n : ℕ => Work.EKLContract.aDiag t' ^ n * u * (Work.EKLContract.aDiag t' ^ n)⁻¹)
        Filter.atTop (nhds 1)))
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hdec : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hAinv : Work.EKLContract.IsAInvariant μ)
    {νH νT νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {XH XT XU XH' XT' XU' : Set Work.EKLContract.X3}
    (hLH : Work.EKLContract.IsLeafwise μ H νH XH)
    (hLT : Work.EKLContract.IsLeafwise μ T νT XT)
    (hLU : Work.EKLContract.IsLeafwise μ U νU XU)
    (hcovH : Work.EKLC6Core.ACovariant νH XH') (hXH' : μ (XH'ᶜ) = 0)
    (hcovT : Work.EKLC6Core.ACovariant νT XT') (hXT' : μ (XT'ᶜ) = 0)
    (hcovU : Work.EKLC6Core.ACovariant νU XU') (hXU' : μ (XU'ᶜ) = 0) :
    ∀ᵐ x ∂μ, Work.EKLC6Core.growthFun H νH t x - Work.EKLC6Core.growthFun T νT t x
      - Work.EKLC6Core.growthFun U νU t x
      = (fun z : Work.EKLContract.X3 => Real.log ((νH z (Work.EKLC6Core.prodBox T U)).toReal))
          (Work.EKLContract.aDiag (-t) • x)
        - (fun z : Work.EKLContract.X3 => Real.log ((νH z (Work.EKLC6Core.prodBox T U)).toReal)) x := by
  classical
  -- the product structure at every point, almost everywhere
  let P : X3 → Prop := fun y => ∃ c : ℝ, 0 < c ∧ ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      ∫ g, f g ∂(νH y) = c * ∫ g, (∫ u, f (g * u) ∂(νU y)) ∂(νT y)
  have hpp : ∀ᵐ x ∂μ, P x :=
    hprod μ hAinv H T U hHH hHT hHU hTH hUH hcent hnorm hdec hdisj
      νH νT νU XH XT XU hLH hLT hLU
  -- the six conull sets
  have hmemH : ∀ᵐ x ∂μ, x ∈ XH := by
    rw [MeasureTheory.ae_iff]; exact hLH.conull
  have hmemT : ∀ᵐ x ∂μ, x ∈ XT := by
    rw [MeasureTheory.ae_iff]; exact hLT.conull
  have hmemU : ∀ᵐ x ∂μ, x ∈ XU := by
    rw [MeasureTheory.ae_iff]; exact hLU.conull
  have hmemH' : ∀ᵐ x ∂μ, x ∈ XH' := by
    rw [MeasureTheory.ae_iff]; exact hXH'
  have hmemT' : ∀ᵐ x ∂μ, x ∈ XT' := by
    rw [MeasureTheory.ae_iff]; exact hXT'
  have hmemU' : ∀ᵐ x ∂μ, x ∈ XU' := by
    rw [MeasureTheory.ae_iff]; exact hXU'
  have hgood : ∀ᵐ x ∂μ, x ∈ XH ∧ x ∈ XT ∧ x ∈ XU ∧ x ∈ XH' ∧ x ∈ XT' ∧ x ∈ XU' := by
    filter_upwards [hmemH, hmemT, hmemU, hmemH', hmemT', hmemU'] with x h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  -- the same for the shifted point `aDiag (-t) • x`
  have hφmp : MeasureTheory.MeasurePreserving
      (fun z : Work.EKLContract.X3 => Work.EKLContract.aDiag (-t) • z) μ μ := hAinv (-t)
  have hshift_notmem (N : Set Work.EKLContract.X3) (hN : μ N = 0) :
      ∀ᵐ x ∂μ, Work.EKLContract.aDiag (-t) • x ∉ N := by
    apply MeasureTheory.ae_iff.mpr
    have h : μ ((fun z : Work.EKLContract.X3 => Work.EKLContract.aDiag (-t) • z) ⁻¹' N) = 0 :=
      hφmp.preimage_null hN
    rwa [show {a : Work.EKLContract.X3 |
        ¬ (Work.EKLContract.aDiag (-t) • a ∉ N)} =
      (fun z : Work.EKLContract.X3 => Work.EKLContract.aDiag (-t) • z) ⁻¹' N from by
      ext x; simp]
  have hshift_mem (S : Set Work.EKLContract.X3) (hS : μ Sᶜ = 0) :
      ∀ᵐ x ∂μ, Work.EKLContract.aDiag (-t) • x ∈ S := by
    have h := hshift_notmem Sᶜ hS
    filter_upwards [h] with x hx
    simpa using hx
  have hgoodshift : ∀ᵐ x ∂μ,
      Work.EKLContract.aDiag (-t) • x ∈ XH ∧ Work.EKLContract.aDiag (-t) • x ∈ XT ∧
        Work.EKLContract.aDiag (-t) • x ∈ XU ∧
        Work.EKLContract.aDiag (-t) • x ∈ XH' ∧ Work.EKLContract.aDiag (-t) • x ∈ XT' ∧
        Work.EKLContract.aDiag (-t) • x ∈ XU' := by
    filter_upwards [hshift_mem XH hLH.conull, hshift_mem XT hLT.conull, hshift_mem XU hLU.conull,
      hshift_mem XH' hXH', hshift_mem XT' hXT', hshift_mem XU' hXU'] with x h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  have hppshift : ∀ᵐ x ∂μ, P (Work.EKLContract.aDiag (-t) • x) := by
    have hbad : μ {y : Work.EKLContract.X3 | ¬ P y} = 0 := by
      rw [← MeasureTheory.ae_iff]; exact hpp
    have h := hshift_notmem {y : Work.EKLContract.X3 | ¬ P y} hbad
    filter_upwards [h] with x hx
    simpa using hx
  -- the pointwise coboundary identity
  filter_upwards [hpp, hppshift, hgood, hgoodshift] with x hpx hpxs hx hxs
  obtain ⟨cx, hcx, hPx⟩ := hpx
  obtain ⟨cy, hcy, hPy⟩ := hpxs
  obtain ⟨cH, hcH0, hcHT, hcHrel⟩ := hcovH (-t) x hx.2.2.2.1 hxs.2.2.2.1
  obtain ⟨cT, hcT0, hcTT, hcTrel⟩ := hcovT (-t) x hx.2.2.2.2.1 hxs.2.2.2.2.1
  obtain ⟨cU, hcU0, hcUT, hcUrel⟩ := hcovU (-t) x hx.2.2.2.2.2 hxs.2.2.2.2.2
  -- the rectangle-mass identities (from `Work.EKLC6Core.rectangle_mass`)
  have hsubT : conjBox T t ⊆ (T : Set SL3) := by
    rintro g ⟨b, hb, rfl⟩
    exact hHT.2.1 t b hb.1
  have hsubU : conjBox U t ⊆ (U : Set SL3) := by
    rintro g ⟨b, hb, rfl⟩
    exact hHU.2.1 t b hb.1
  have hrectT : νH x (Set.image2 (fun a b : SL3 => a * b) (conjBox T t) (conjBox U t))
      = ENNReal.ofReal cx * (νT x (conjBox T t) * νU x (conjBox U t)) :=
    rectangle_mass hTH hUH hdisj hLH hLT hLU x hx.1 hx.2.1 hx.2.2.1 hcx hPx
      (AT := conjBox T t) (AU := conjBox U t)
      (isCompact_conjBox hHT t) (isCompact_conjBox hHU t) hsubT hsubU
  have hrect0 : νH x (prodBox T U) = ENNReal.ofReal cx := by
    have h := rectangle_mass hTH hUH hdisj hLH hLT hLU x hx.1 hx.2.1 hx.2.2.1 hcx hPx
      (AT := Box1 T) (AU := Box1 U)
      (isCompact_box1 hHT) (isCompact_box1 hHU) (fun g hg => hg.1) (fun g hg => hg.1)
    rw [prodBox]
    rw [h, hLT.normalised x hx.2.1, hLU.normalised x hx.2.2.1, mul_one, mul_one]
  have hrectφ : νH (aDiag (-t) • x) (prodBox T U) = ENNReal.ofReal cy := by
    have h := rectangle_mass hTH hUH hdisj hLH hLT hLU (aDiag (-t) • x) hxs.1 hxs.2.1 hxs.2.2.1
      hcy hPy (AT := Box1 T) (AU := Box1 U)
      (isCompact_box1 hHT) (isCompact_box1 hHU) (fun g hg => hg.1) (fun g hg => hg.1)
    rw [prodBox]
    rw [h, hLT.normalised _ hxs.2.1, hLU.normalised _ hxs.2.2.1, mul_one, mul_one]
  have hkey := growthFun_sub_eq (νH := νH) (νT := νT) (νU := νU) (t := t) (x := x)
    hcx hcy hcH0 hcHT hcT0 hcTT hcU0 hcUT hcHrel hcTrel hcUrel
    (hLH.normalised _ hxs.1) (hLT.normalised _ hxs.2.1) (hLU.normalised _ hxs.2.2.1)
    (measurableSet_box1 hHH) (measurableSet_box1 hHT) (measurableSet_box1 hHU)
    (measurableSet_prodBox hHT hHU) hrectT hrect0 hrectφ
  rw [hkey, hrect0, hrectφ, ENNReal.toReal_ofReal (le_of_lt hcx),
    ENNReal.toReal_ofReal (le_of_lt hcy)]

end Work.EKLC6Core

end
