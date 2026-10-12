import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.WB.Lead
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.wbW_lower` — the lower bound `π(a v)ℓ³ ≤ W` for the localised mass

FS's constant `𝒞 = W = ∫_{I₋}∬w_{1,B(u)}` is `≍ 8π(a v)ℓ³`: the total (`u ∈ ℝ³`)
localised mass is `8π(a v)ℓ³` up to the quadratic deviation (`mass_total`), and the
discarded parameter set `I₋ᶜ` carries at most `O((a v)ℓ³)` of cutoff mass
(`hcomp`, the regime input `window_regime`).  Subtracting the two gives the crude
lower bound `π(a v)ℓ³ ≤ W` used by the Cauchy–Schwarz window.

The proof is the measure-theoretic bookkeeping of that subtraction:

* `htotal` is *strictly* positive (`a v > 0`, `ℓ > 0`), so the Bochner integral
  `∫_u wbMass v h μ u` is that of an **integrable** function
  (`MeasureTheory.integral_undef`: a non-integrable function has integral `0`);
* hence the domain splits, `∫_ℝ³ = ∫_{I₋} + ∫_{I₋ᶜ}`
  (`MeasureTheory.integral_add_compl`, with `I₋` measurable);
* on `I₋ᶜ` the pointwise interface bound `hmassU` and monotonicity of the set
  integral (`MeasureTheory.setIntegral_mono_on`, against the integrable cutoff
  mass `SmallBoxSliding.integrable_chiSmallB_mass`) give
  `∫_{I₋ᶜ} wbMass ≤ C₁(a v)∫_{I₋ᶜ}chiMass ≤ C₁(a v)·(2π/C₁)ℓ³ = 2π(a v)ℓ³`;
* `8π(3/4) − 2π = 4π ≥ π` finishes.

The hypotheses `hv`, `hvrad`, `hv_supp`, `hR0`, `hμ` are the paper's standing ones
(they are what makes `w1MassB ≥ 0` and the regime satisfiable); the argument below
uses only positivity of `a v` and `ℓ`.
-/

namespace Work.BoseFixB1.WB

open MeasureTheory

theorem wbW_lower {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v)
    (hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hmassU : ∀ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.wbMass v h μ u
      ≤ C₁ * _root_.BoseGases.a v
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (htotal : 8 * Real.pi * _root_.BoseGases.a v * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 * (3 / 4)
      ≤ ∫ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.wbMass v h μ u)
    (hcomp : (∫ u in (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ,
        Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      ≤ (2 * Real.pi / C₁) * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) :
    Real.pi * _root_.BoseGases.a v * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
      ≤ Work.BoseFixB1.wbW v h μ := by
  -- The total mass is a *strictly positive* number, so the Bochner integral is that of an
  -- integrable function (`integral_undef` otherwise).
  have hint : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixB1.wbMass v h μ u) := by
    by_contra hni
    rw [MeasureTheory.integral_undef hni] at htotal
    have hpos : 0 < 8 * Real.pi * _root_.BoseGases.a v
        * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 * (3 / 4) := by positivity
    linarith
  have hs : MeasurableSet (Work.SmallBoxSliding.interiorSet
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ) :=
    Work.SmallBoxSliding.measurableSet_interiorSet _ _ _
  have hsplit := MeasureTheory.integral_add_compl hs hint
  -- The cutoff mass is integrable in the parameter `u`.
  have hχint : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) := by
    simpa only [Work.SmallBoxSliding.chiMass_def] using
      (Work.SmallBoxSliding.integrable_chiSmallB_mass hM hℓ hd)
  -- The discarded mass, dominated by the cutoff mass times `C₁(a v)` and then bounded by `hcomp`.
  have hY : (∫ u in (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ, Work.BoseFixB1.wbMass v h μ u)
      ≤ 2 * Real.pi * _root_.BoseGases.a v * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by
    have hmono : (∫ u in (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ, Work.BoseFixB1.wbMass v h μ u)
        ≤ ∫ u in (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ,
            (C₁ * _root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
      MeasureTheory.setIntegral_mono_on hint.integrableOn
        (hχint.const_mul (C₁ * _root_.BoseGases.a v)).integrableOn
        hs.compl (fun u _ => hmassU u)
    calc (∫ u in (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ, Work.BoseFixB1.wbMass v h μ u)
        ≤ ∫ u in (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ,
            (C₁ * _root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u := hmono
      _ = (C₁ * _root_.BoseGases.a v) * (∫ u in (Work.SmallBoxSliding.interiorSet
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)ᶜ,
              Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) := by
            rw [MeasureTheory.integral_const_mul]
      _ ≤ (C₁ * _root_.BoseGases.a v) * ((2 * Real.pi / C₁)
            * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) :=
            mul_le_mul_of_nonneg_left hcomp (le_of_lt (mul_pos hC₁ hav))
      _ = 2 * Real.pi * _root_.BoseGases.a v * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by
            field_simp
  -- Split the total and subtract the discarded part.
  have hkey : 8 * Real.pi * _root_.BoseGases.a v * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 * (3 / 4)
      - 2 * Real.pi * _root_.BoseGases.a v * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
      ≤ ∫ u in Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ, Work.BoseFixB1.wbMass v h μ u := by
    linarith [hsplit, htotal, hY]
  -- `8π(3/4) − 2π = 4π ≥ π`.
  have harith : Real.pi * _root_.BoseGases.a v * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
      ≤ 8 * Real.pi * _root_.BoseGases.a v * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 * (3 / 4)
        - 2 * Real.pi * _root_.BoseGases.a v * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by
    have hprod : 0 < Real.pi * _root_.BoseGases.a v * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by
      positivity
    nlinarith [hprod]
  rw [Work.BoseFixB1.wbW]
  exact le_trans harith hkey

end Work.BoseFixB1.WB
