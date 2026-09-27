import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLCompLeaf.measurable_nu
import Submission.Work.EKLC6Core.coboundary_integral
import Submission.Work.EKLC6Core.rectangle_mass
import Submission.Work.EKLC6Core.growth_glue

/-!
# `EKLC6Core.growth_integral_sup` — additivity of the entropy contributions

The product structure of leaf-wise measures (Pisa Cor. 8.8, the frozen contract `P_Product`)
says that for `H = T · U` (`T` normalising `U`, `T ∩ U = {1}`) the leaf-wise measures satisfy
`νH x = c(x) · (νT x ⊗ νU x).map (· * ·)` for `μ`-a.e. `x`.  In the *specific* normalisation of
the frozen contract (`ν x (B₁^U) = 1`) the proportionality constant `c(x)` is non-trivial, but it
is a coboundary along the `aDiag`-orbit: the rectangle formula
`Work.EKLC6Core.rectangle_mass` applied to the product box `B₀ = B₁^T · B₁^U` and to its
conjugate identifies `c(x) = νH x (B₀)`, and the `A`-covariance of `νH` (with the normalization
at the shifted point) gives

`growthFun H νH t x - growthFun T νT t x - growthFun U νU t x
   = log (νH (aDiag (-t) • x) (B₀)) - log (νH x (B₀))`

(`Work.EKLC6Core.growthFun_sub_eq`, in `EKLC6Core.growth_glue`), a coboundary of the
*measurable* function `z ↦ log (νH z (B₀))`
(`Work.EKLCompLeaf.measurable_apply_isCompact`).  Since `aDiag (-t)` preserves `μ` and the mean
of a coboundary of a measurable function vanishes (`Work.EKLC6Core.coboundary_integral`), the
integral of the coboundary vanishes, and the claimed additivity of the growth-function integrals
follows from the integrability hypotheses.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Pointwise
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## The main theorem -/

/-- **Additivity of the entropy contributions over the product decomposition `H = T · U`.**
For `H = T · U` (`T` normalising `U`, `T ∩ U = {1}`, `H` horospherical) and an `A`-invariant
probability measure `μ` with leaf-wise systems for `H`, `T`, `U` (with `A`-covariance on conull
sets), the integrals of the three growth functions are additive. -/
theorem growth_integral_sup {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hprod : Work.EKLContract.P_Product)
    {H T U : Subgroup Work.EKLContract.SL3} (hTH : T ≤ H) (hUH : U ≤ H)
    (hHT : Work.EKLContract.IsHoro T) (hHU : Work.EKLContract.IsHoro U)
    (hHH : Work.EKLContract.IsHoro H)
    (hcent : ∃ t' : Fin 3 → ℝ, (∀ g ∈ T, Work.EKLContract.aDiag t' * g = g * Work.EKLContract.aDiag t') ∧
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
    (hcovU : Work.EKLC6Core.ACovariant νU XU') (hXU' : μ (XU'ᶜ) = 0)
    (hNH : MeasureTheory.Integrable (Work.EKLC6Core.growthFun H νH t) μ)
    (hNT : MeasureTheory.Integrable (Work.EKLC6Core.growthFun T νT t) μ)
    (hNU : MeasureTheory.Integrable (Work.EKLC6Core.growthFun U νU t) μ) :
    ∫ x, Work.EKLC6Core.growthFun H νH t x ∂μ =
      ∫ x, Work.EKLC6Core.growthFun T νT t x ∂μ +
        ∫ x, Work.EKLC6Core.growthFun U νU t x ∂μ := by
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
  have hφmp : MeasurePreserving (fun z : X3 => aDiag (-t) • z) μ μ := hAinv (-t)
  have hshift_notmem (N : Set X3) (hN : μ N = 0) : ∀ᵐ x ∂μ, aDiag (-t) • x ∉ N := by
    apply MeasureTheory.ae_iff.mpr
    have h : μ ((fun z : X3 => aDiag (-t) • z) ⁻¹' N) = 0 := hφmp.preimage_null hN
    rwa [show {a : X3 | ¬ (aDiag (-t) • a ∉ N)} = (fun z : X3 => aDiag (-t) • z) ⁻¹' N from by
      ext x; simp]
  have hshift_mem (S : Set X3) (hS : μ Sᶜ = 0) : ∀ᵐ x ∂μ, aDiag (-t) • x ∈ S := by
    have h := hshift_notmem Sᶜ hS
    filter_upwards [h] with x hx
    simpa using hx
  have hgoodshift : ∀ᵐ x ∂μ,
      aDiag (-t) • x ∈ XH ∧ aDiag (-t) • x ∈ XT ∧ aDiag (-t) • x ∈ XU ∧
        aDiag (-t) • x ∈ XH' ∧ aDiag (-t) • x ∈ XT' ∧ aDiag (-t) • x ∈ XU' := by
    filter_upwards [hshift_mem XH hLH.conull, hshift_mem XT hLT.conull, hshift_mem XU hLU.conull,
      hshift_mem XH' hXH', hshift_mem XT' hXT', hshift_mem XU' hXU'] with x h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  have hppshift : ∀ᵐ x ∂μ, P (aDiag (-t) • x) := by
    have hbad : μ {y : X3 | ¬ P y} = 0 := by
      rw [← MeasureTheory.ae_iff]; exact hpp
    have h := hshift_notmem {y : X3 | ¬ P y} hbad
    filter_upwards [h] with x hx
    simpa using hx
  -- the pointwise coboundary identity
  have hpt : ∀ᵐ x ∂μ,
      growthFun H νH t x - growthFun T νT t x - growthFun U νU t x
        = (fun z : X3 => Real.log ((νH z (prodBox T U)).toReal)) (aDiag (-t) • x)
          - (fun z : X3 => Real.log ((νH z (prodBox T U)).toReal)) x := by
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
  -- the `νH`-mass of the product box is almost everywhere measurable
  have hΨm : AEStronglyMeasurable
      (fun z : X3 => Real.log ((νH z (prodBox T U)).toReal)) μ := by
    let ν' : X3 → Measure SL3 := fun z => if z ∈ XH then νH z else 0
    have hν'fin : ∀ z : X3, IsFiniteMeasureOnCompacts (ν' z) := by
      intro z
      by_cases hz : z ∈ XH
      · simp only [ν', hz, if_true]; exact hLH.radon z hz
      · simp only [ν', hz, if_false]; exact ⟨fun K _ => by simp⟩
    have hν'meas : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
        Measurable (fun z : X3 => ∫ g, f g ∂(ν' z)) := by
      intro f
      have h1 : Measurable (fun z : X3 => ∫ g, f g ∂(νH z)) := hLH.measurable f
      have h2 : (fun z : X3 => ∫ g, f g ∂(ν' z))
          = XH.indicator (fun z : X3 => ∫ g, f g ∂(νH z)) := by
        funext z
        by_cases hz : z ∈ XH <;> simp [ν', Set.indicator, hz]
      rw [h2]
      exact h1.indicator hLH.meas_dom
    have hmass : Measurable (fun z : X3 => ν' z (prodBox T U)) :=
      Work.EKLCompLeaf.measurable_apply_isCompact hν'meas hν'fin
        (isCompact_prodBox hHT hHU)
    have hlog : Measurable (fun z : X3 => Real.log ((ν' z (prodBox T U)).toReal)) :=
      Real.measurable_log.comp hmass.ennreal_toReal
    have hae : (fun z : X3 => Real.log ((ν' z (prodBox T U)).toReal))
        =ᵐ[μ] (fun z : X3 => Real.log ((νH z (prodBox T U)).toReal)) := by
      filter_upwards [hmemH] with z hz
      simp only [ν', hz, if_true]
    exact hlog.aestronglyMeasurable.congr hae
  -- the difference is an integrable coboundary
  have hDint : MeasureTheory.Integrable
      (fun x : X3 => growthFun H νH t x - growthFun T νT t x - growthFun U νU t x) μ :=
    (hNH.sub hNT).sub hNU
  have hzero := coboundary_integral (φ := fun z : X3 => aDiag (-t) • z) hφmp hΨm hDint hpt
  have h1 : ∫ x, growthFun H νH t x - growthFun T νT t x ∂μ
      = ∫ x, growthFun H νH t x ∂μ - ∫ x, growthFun T νT t x ∂μ :=
    integral_sub hNH hNT
  have h2 : ∫ x, growthFun H νH t x - growthFun T νT t x - growthFun U νU t x ∂μ
      = ∫ x, growthFun H νH t x - growthFun T νT t x ∂μ - ∫ x, growthFun U νU t x ∂μ :=
    integral_sub (hNH.sub hNT) hNU
  linarith [hzero, h1, h2]

end Work.EKLC6Core

end
