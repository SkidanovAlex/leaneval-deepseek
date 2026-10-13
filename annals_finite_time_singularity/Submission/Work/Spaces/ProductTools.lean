/-
Copyright: work module for the Elgindi finite-time singularity project.

# Tools for the product rules

`L2Mem g` says that the (iterated) integral `L2Sq g = ∫_z ∫_θ g²` of `g` is honest.
The main estimate here is the standard "pull out an `L^∞` factor" step used in every
term of the product rules in `H^4`:

`L2Sq (A · B) ≤ |B|_∞² · L2Sq A`

(one factor is bounded pointwise by its `L^∞`-norm on the domain, the other keeps its
weighted `L²`-norm).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.WlInf_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- `g` is square integrable over the domain in the iterated sense: every angular
slice is integrable and the resulting function of `z` is integrable on `[0,∞)`. -/
def L2Mem (g : ℝ → ℝ → ℝ) : Prop :=
  (∀ z ∈ Iz, IntegrableOn (fun θ => (g z θ) ^ 2) Iθ) ∧
    IntegrableOn (fun z => ∫ θ in Iθ, (g z θ) ^ 2) Iz

/-- Pulling an `L^∞`-factor out of the squared `L²`-norm. -/
theorem L2Sq_mul_le_supAbs (A B : ℝ → ℝ → ℝ) (hB : SupFinite B) (hA : L2Mem A) :
    L2Sq (fun z θ => A z θ * B z θ) ≤ (supAbs B) ^ 2 * L2Sq A := by
  have hsB : 0 ≤ supAbs B := supAbs_nonneg hB
  have hpt : ∀ z ∈ Iz, ∀ θ ∈ Iθ, (A z θ * B z θ) ^ 2 ≤ (A z θ) ^ 2 * (supAbs B) ^ 2 := by
    intro z hz θ hθ
    have h1 : |B z θ| ≤ supAbs B := abs_le_supAbs hz hθ hB
    have h2 : (B z θ) ^ 2 ≤ (supAbs B) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hsB]
      exact h1
    calc (A z θ * B z θ) ^ 2 = (A z θ) ^ 2 * (B z θ) ^ 2 := by ring
      _ ≤ (A z θ) ^ 2 * (supAbs B) ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  rw [L2Sq]
  have hinner : ∀ᵐ z ∂(volume.restrict Iz),
      (∫ θ in Iθ, (A z θ * B z θ) ^ 2)
        ≤ ∫ θ in Iθ, (A z θ) ^ 2 * (supAbs B) ^ 2 :=
    MeasureTheory.ae_restrict_of_forall_mem (show MeasurableSet Iz from measurableSet_Ici)
      fun z hz => MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall fun θ => sq_nonneg _)
        ((hA.1 z hz).mul_const _)
        (MeasureTheory.ae_restrict_of_forall_mem
          (show MeasurableSet Iθ from measurableSet_Icc) fun θ hθ => hpt z hz θ hθ)
  have hfun : (fun z : ℝ => ∫ θ in Iθ, (A z θ) ^ 2 * (supAbs B) ^ 2)
      = fun z : ℝ => (∫ θ in Iθ, (A z θ) ^ 2) * (supAbs B) ^ 2 := by
    funext z
    rw [MeasureTheory.integral_mul_const]
  have hint2 : Integrable (fun z => ∫ θ in Iθ, (A z θ) ^ 2 * (supAbs B) ^ 2) (volume.restrict Iz) := by
    rw [hfun]
    exact hA.2.mul_const _
  calc ∫ z in Iz, (∫ θ in Iθ, (A z θ * B z θ) ^ 2)
      ≤ ∫ z in Iz, (∫ θ in Iθ, (A z θ) ^ 2 * (supAbs B) ^ 2) :=
        MeasureTheory.integral_mono_of_nonneg
          (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _)
          hint2 hinner
    _ = (supAbs B) ^ 2 * ∫ z in Iz, (∫ θ in Iθ, (A z θ) ^ 2) := by
        simp only [MeasureTheory.integral_mul_const]
        ring

end Work.Spaces
