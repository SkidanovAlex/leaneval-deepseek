/-
# `Work.R1G.gTest_meas` — the test perturbation profile is a.e. strongly measurable

The scalar field

  `x ↦ profile p (gTest ε) (ρ(x)^p) (θ(x))`

is a composition of the measurable map `x ↦ (ρ(x)^p, θ(x))` on `ℝ³` with the measurable
function `(z,θ) ↦ profile p (gTest ε) z θ` on `ℝ²`.  Each ingredient is measurable:

* `ρ = √(r² + x₃²)` and `θ = arctan(x₃/r)` are continuous (`Real.sqrt`, `Real.arctan`, and
  division on `ℝ` are continuous), so `Rc p x = ρ(x)^p` is measurable (`Real.rpow` is
  continuous for nonnegative exponent, `hp`);
* `profile` is the two-branch function with the measurable branch condition `0 ≤ θ`; both
  branches are built from `F_* = α·(Γ(θ)/c)·2z/(1+z)²` (`Γ(θ) = (sinθcos²θ)^{α/3}` is an
  `rpow` with fixed exponent, hence measurable) and from `gTest ε = ε·z²e^{-z}·sin(2θ)`,
  which is continuous.

The result then follows from `Measurable.aestronglyMeasurable`.
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.R1G.GTest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory

namespace Work.R1G

theorem gTest_meas {p : ℝ} (hp : 0 ≤ p) (ε : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun x : Work.ConstructionInstance.R3 =>
        Work.ConstructionInstance.profile p (gTest ε) (Work.Cyl.Rc p x) (Work.Cyl.theta x))
      MeasureTheory.volume := by
  -- the radial coordinate `ρ` is continuous, so `Rc p = ρ^p` is measurable (`hp`)
  have hRc : Measurable (fun x : Work.ConstructionInstance.R3 => Work.Cyl.Rc p x) := by
    have hrho : Continuous fun x : Work.ConstructionInstance.R3 => Work.Cyl.rho x := by
      unfold Work.Cyl.rho Work.Cyl.axial Work.Cyl.radSq
      fun_prop
    unfold Work.Cyl.Rc
    exact ((Real.continuous_rpow_const hp).comp hrho).measurable
  have hth : Measurable (fun x : Work.ConstructionInstance.R3 => Work.Cyl.theta x) := by
    unfold Work.Cyl.theta Work.Cyl.axial Work.Cyl.radial Work.Cyl.radSq
    measurability
  -- the profile as a function of `(z,θ)`
  have hmF : Measurable (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 q.2) := by
    unfold Work.Construction.Fstar Work.Spaces.Gam
    simp only [Work.FM.Fstar]
    measurability
  have hmF' : Measurable (fun q : ℝ × ℝ => Work.Construction.Fstar p q.1 (-q.2)) := by
    unfold Work.Construction.Fstar Work.Spaces.Gam
    simp only [Work.FM.Fstar]
    measurability
  have hmg : Measurable (fun q : ℝ × ℝ => gTest ε q.1 q.2) := by
    unfold gTest gPhi gPsi
    measurability
  have hmg' : Measurable (fun q : ℝ × ℝ => gTest ε q.1 (-q.2)) := by
    unfold gTest gPhi gPsi
    measurability
  have hprof : Measurable
      (fun q : ℝ × ℝ => Work.ConstructionInstance.profile p (gTest ε) q.1 q.2) := by
    unfold Work.ConstructionInstance.profile
    exact Measurable.ite (p := fun q : ℝ × ℝ => 0 ≤ q.2)
      (measurableSet_le measurable_const measurable_snd) (hmF.add hmg) ((hmF'.add hmg').neg)
  exact (hprof.comp (hRc.prodMk hth)).aestronglyMeasurable

end Work.R1G
