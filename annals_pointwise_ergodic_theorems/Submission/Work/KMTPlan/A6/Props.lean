/-
# The sub-contract inputs of the high–high case, from their proved modules

This module discharges the named inputs of the high–high sub-contract
(`Work.KMTPlan.Sub.VanishingF`, `VanishingG`, `BesselF`, `BesselG`, `NonAliasingSize`,
`LogGain`, `GoodScaleArith` of `Submission/Work/KMTPlan/Model.lean`) from the theorems proved in
`Submission/Work/KMTPlan/A6/`, so that the high–high case `Work.KMTPlan.A6.highHighCase` can be
applied by `Work.KMTPlan.A6.areaA6_final`.
-/
import Mathlib
import Submission.Work.KMTPlan.Model
import Submission.Work.KMTPlan.A6.projVanishingF
import Submission.Work.KMTPlan.A6.projVanishingG
import Submission.Work.KMTPlan.A6.besselF
import Submission.Work.KMTPlan.A6.besselG
import Submission.Work.KMTPlan.A6.nonAliasing_of_size
import Submission.Work.KMTPlan.A6.logTerm_le_gain
import Submission.Work.KMTPlan.A6.goodScaleArith

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

/-- `Sub.VanishingF`, from `A6.projVanishingF`. -/
theorem Sub_VanishingF : Work.KMTPlan.Sub.VanishingF :=
  fun ρ hρ hρ1 l₁ k₁ L N f hk hc hw hNA hf =>
    projVanishingF ρ hρ hρ1 l₁ k₁ L N f hk hc hw hNA hf

/-- `Sub.VanishingG`, from `A6.projVanishingG`. -/
theorem Sub_VanishingG : Work.KMTPlan.Sub.VanishingG :=
  fun ρ hρ hρ1 P l₂ k₂ L N g hk hc hw hNA hg =>
    projVanishingG ρ hρ hρ1 P l₂ k₂ L N g hk hc hw hNA hg

/-- `Sub.BesselF`, from `A6.besselF`. -/
theorem Sub_BesselF (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) : Work.KMTPlan.Sub.BesselF ρ :=
  besselF ρ hρ hρ1

/-- `Sub.BesselG`, from `A6.besselG`. -/
theorem Sub_BesselG (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : ℤ[X]) :
    Work.KMTPlan.Sub.BesselG ρ P :=
  besselG ρ hρ hρ1 P

/-- `Sub.NonAliasingSize`, from `A6.nonAliasing_of_size`. -/
theorem Sub_NonAliasingSize (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    Work.KMTPlan.Sub.NonAliasingSize ρ :=
  nonAliasing_of_size ρ hρ hρ1

/-- `Sub.LogGain`, from `A6.logTerm_le_gain`. -/
theorem Sub_LogGain (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (c : ℝ) (hc : 0 < c)
    (R : ℝ) (hR : 1 ≤ R) : Work.KMTPlan.Sub.LogGain ρ c R :=
  logTerm_le_gain ρ hρ c hc R hR

/-- `Sub.GoodScaleArith`, from `A6.goodScaleArith`. -/
theorem Sub_GoodScaleArith (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1 / (4 * (C₀ : ℝ))) (R : ℝ) (hR : 1 ≤ R) :
    Work.KMTPlan.Sub.GoodScaleArith C₀ ρ R :=
  goodScaleArith C₀ hC₀ ρ hρ hρ1 R hR

end Work.KMTPlan.A6
