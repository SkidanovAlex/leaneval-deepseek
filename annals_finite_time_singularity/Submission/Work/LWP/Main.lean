import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.LWP.BiotSavart.farField_decay_fderiv_const
import Submission.Work.LWP.VorticityAPI
import Submission.Work.Spaces.mixed_sq_integrableOn
import Submission.Work.Spaces.sup_mixed_le_H4
-- ===== merged: Submission.Work.LWP.FarField =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.LWP






end Work.LWP
end
-- ===== merged: Submission.Work.LWP.Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.LWP

/-- **The analytic inputs of the LWP chapter, bundled.**  Every theorem of
`Submission/Work/LWP/` is conditional on (a subset of) these; `NOTES.md` states what a proof of
each requires. -/
structure LWPInputs (α : NNReal) : Prop where
  /-- the Calderón–Zygmund/Schauder estimate: the `C^{1,α}` closure of Biot–Savart (item 1) -/
  schauder : BiotSavartSchauder α
  /-- the Biot–Savart law `∇×(BS ω) = ω`, `div (BS ω) = 0` -/
  law : BiotSavartLaw
  /-- reflection equivariance of Biot–Savart (the odd clause).  **No longer a true input**: it is
  proved as `Work.LWP.biotSavartReflection_holds`
  (`Submission/Work/LWP/BiotSavart/biotSavart_reflZ.lean`); the field is kept so that the bundle
  stays stable. -/
  reflection : BiotSavartReflection
  /-- the Picard iteration for the vorticity equation (item 2) -/
  transport : VorticityTransportExistence α
  /-- the elliptic reconstruction of the pressure -/
  pressure : PressureReconstruction α
  /-- propagation of the odd symmetry -/
  oddProp : IsOddPropagates
  /-- the Poincaré lemma on `ℝ³` (used in the classical pressure argument).  **No longer a true
  input**: it is proved as `Work.LWP.curlFreeIsGradient_holds`
  (`Submission/Work/LWP/CurlFree/curlFree_isGradient.lean`). -/
  poincare : CurlFreeIsGradient
  /-- uniqueness in the Lichtenstein–Gunther class -/
  uniqueness : EulerUniqueness α
  /-- the Beale–Kato–Majda continuation criterion (item 3) -/
  bkm : BKMExtension α
  /-- existence of a maximal solution -/
  maxExists : MaximalSolutionExists α

variable {α : NNReal}








/-- **The assembly's complete data package.**  A compactly supported vorticity `ω₀` that is `L¹`,
bounded, `α`-Hölder and divergence-free, with odd velocity and the `α`-power decay clause,
produces simultaneously the analytic datum class `EulerData`, the Biot–Savart-compatible class
`EulerDataBS` (with the decay field automatic) and the self-consistency clause `hself` needed by
`local_existence`. -/
theorem assembly_data (H : LWPInputs α) {ω₀ : R3 → R3} {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hint : Integrable ω₀) (hω : ∀ y, ‖ω₀ y‖ ≤ M) (hh : Holder α ω₀)
    (hdiv : ∀ x, div ω₀ x = 0) (hsupp : ∀ y, ω₀ y ≠ 0 → y ∈ Metric.closedBall 0 R)
    (hodd : IsOdd (biotSavart ω₀)) (hdec : VorticityDecay α ω₀) :
    EulerData α (biotSavart ω₀) ∧ EulerDataBS α (biotSavart ω₀) ∧
      (∀ x, biotSavart ω₀ x = biotSavart (vorticity (biotSavart ω₀)) x) :=
  ⟨eulerData_of_biotSavart H.schauder H.law hint (isBoundedFun_of_norm_le hω) hh hdiv hodd hdec,
   eulerDataBS_of_compactSupport H.law hR hM hint hω hh hdiv hsupp,
   self_eq_biotSavart_of_biotSavart H.law hint (isBoundedFun_of_norm_le hω) hdiv⟩



/-- **`BiotSavartReflection` is not an input any more**: the reflection equivariance of the
Biot–Savart operator is proved in
`Submission/Work/LWP/BiotSavart/biotSavart_reflZ.lean`. -/
theorem biotSavartReflection_holds : BiotSavartReflection :=
  fun _ hω x => BiotSavart.biotSavart_reflZ hω x



end Work.LWP
end
