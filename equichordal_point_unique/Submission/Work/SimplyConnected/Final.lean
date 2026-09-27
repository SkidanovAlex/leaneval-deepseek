import Submission.UnifDeps
import Submission.Work.SimplyConnected.Wiring
import Submission.Work.SimplyConnected.Modulus.isCoveringMap_branchProj
import Submission.Work.Potential.logCoefficient_of_pos_harmonic
import Submission.Work.Potential.removable_singularity_of_bounded_near

/-!
# The simply connected case of uniformization: final assembly

This module discharges every input of
`Work.SC.uniformization_of_simplyConnected_of_inputs'` except the parabolic branch:

* the two potential-theoretic inputs (`Submission.LogCoefficientInput`, i.e. Bôcher's theorem, and
  `Submission.RemovableInput`, i.e. removable singularities for bounded harmonic functions) are
  `Work.Potential.logCoefficient_of_pos_harmonic` and
  `Work.Potential.removable_singularity_of_bounded_near`;
* the covering property of the modulus bundle is `Work.SC.isCoveringMap_branchProj` (proved in
  `Submission/Work/SimplyConnected/Modulus/`), which with
  `Work.SC.exists_holomorphic_modulus_of_hasGreenFunctionE` produces the holomorphic modulus of a
  strong Green function — the monodromy being trivial because `X` is simply connected.

Consequently **the hyperbolic case is complete**:
`Work.SC.uniformization_of_hyperbolic` says that a simply connected non-compact surface carrying a
weak Green function is `ℂ` or `𝔻`.  The single remaining input of
`Work.SC.uniformization_of_simplyConnected_of_parabolic` is the parabolic branch `hC` — a simply
connected, non-compact surface with no weak Green function is `ℂ` (`Work.Parabolic`).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Work.SC

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Bôcher's theorem** in the form of the input `Submission.LogCoefficientInput`. -/
theorem logCoefficientInput (z₀ : X) : Submission.LogCoefficientInput (X := X) z₀ :=
  fun hu hpos => Work.Potential.logCoefficient_of_pos_harmonic hu hpos

/-- **Removable singularities** in the form of the input `Submission.RemovableInput`. -/
theorem removableInput (z₀ : X) : Submission.RemovableInput (X := X) z₀ :=
  fun hu hb => Work.Potential.removable_singularity_of_bounded_near hu hb

/-- **Normalisation of the logarithmic pole of a weak Green function**, with no further input. -/
theorem exists_hasGreenFunctionE (hX : ¬ CompactSpace X) {z₀ : X} {E : X → ℝ}
    (hE : Submission.HasGreenFunctionWeak z₀ E) :
    ∃ E' : X → ℝ, Submission.HasGreenFunctionE z₀ E' :=
  exists_hasGreenFunctionE_of_hasGreenFunctionWeak hX (fun z => logCoefficientInput z)
    (fun z => removableInput z) hE

/-- **The covering property of the modulus bundle.** -/
theorem isCoveringMap_branchProj' {z₀ : X} {E : X → ℝ} (hE : Submission.HasGreenFunctionE z₀ E) :
    @IsCoveringMap (ModulusBundle z₀ E) X (modulusBundleTopology z₀ E) _ (branchProj z₀ E) :=
  Work.SimplyConnected.Modulus.isCoveringMap_branchProj hE

/-- **The holomorphic modulus of a strong Green function**, with no further input. -/
theorem exists_holomorphic_modulus [SimplyConnectedSpace X] {z₀ : X} {E : X → ℝ}
    (hE : Submission.HasGreenFunctionE z₀ E) :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧ Submission.HasLogPoleAt z₀ Φ ∧
      ∀ x : X, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)) :=
  exists_holomorphic_modulus_of_hasGreenFunctionE hE (isCoveringMap_branchProj' hE)

section HyperbolicInputs

variable {z₀ : X} {E : X → ℝ}

/-- **The hyperbolic case of uniformization on a simply connected surface**, from the two
potential-theoretic inputs (Bôcher's theorem and removable singularities) and the covering
property of the modulus bundle.  This is the fully verified form of the hyperbolic branch: its
proof term uses only `propext`, `Classical.choice` and `Quot.sound` (in particular no `sorryAx`),
while the next theorem substitutes the potential-theoretic inputs from the parallel subproject. -/
theorem uniformization_of_hyperbolic_of_inputs [SimplyConnectedSpace X] (hX : ¬ CompactSpace X)
    (hlog : ∀ z : X, Submission.LogCoefficientInput (X := X) z)
    (hrem : ∀ z : X, Submission.RemovableInput (X := X) z)
    (hcov : ∀ {z : X} {E' : X → ℝ}, Submission.HasGreenFunctionE z E' →
      @IsCoveringMap (ModulusBundle z E') X (modulusBundleTopology z E') _ (branchProj z E'))
    (hE : Submission.HasGreenFunctionWeak z₀ E) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) :=
  uniformization_of_hasGreenFunctionWeak hX hE
    (fun hE' => exists_hasGreenFunctionE_of_hasGreenFunctionWeak hX hlog hrem hE')
    (fun hE' => exists_holomorphic_modulus_of_hasGreenFunctionE hE' (hcov hE'))

end HyperbolicInputs

/-- **The hyperbolic case of uniformization on a simply connected surface**, with no further
input: a simply connected, non-compact Riemann surface carrying a weak Green function is
biholomorphic to `ℂ` or to the upper half plane. -/
theorem uniformization_of_hyperbolic [SimplyConnectedSpace X] (hX : ¬ CompactSpace X)
    {z₀ : X} {E : X → ℝ} (hE : Submission.HasGreenFunctionWeak z₀ E) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) :=
  uniformization_of_hasGreenFunctionWeak hX hE (fun hE' => exists_hasGreenFunctionE hX hE')
    (fun hE' => exists_holomorphic_modulus hE')

section Ball

variable {z₀ : X} {E : X → ℝ}

/-- **The hyperbolic case, as a bijection onto the open unit disc.**  On a simply connected
non-compact surface with a weak Green function there is an injective holomorphic map onto the unit
disc — the stronger form of `Work.SC.uniformization_of_hyperbolic` needed by the normal-family
(exhaustion) arguments, which consume an *injective* map on each piece. -/
theorem exists_injective_map_ball_of_hasGreenFunctionWeak [SimplyConnectedSpace X]
    (hX : ¬ CompactSpace X) (hE : Submission.HasGreenFunctionWeak z₀ E) :
    ∃ Φ : X → ℂ, Submission.HolomorphicOnX Φ Set.univ ∧ Function.Injective Φ ∧
      (∀ x : X, Φ x ∈ Metric.ball (0 : ℂ) 1) ∧
      (∀ w : ℂ, ‖w‖ < 1 → ∃ x : X, Φ x = w) := by
  obtain ⟨E', hE'⟩ := exists_hasGreenFunctionE hX hE
  obtain ⟨Φ, hΦ, hpole, hmod⟩ := exists_holomorphic_modulus hE'
  have hpos : ∀ x : X, x ≠ z₀ → 0 < E' x := hE'.1.1
  have hzero : Φ z₀ = 0 := Submission.phi_zero_of_logPole hΦ hpole
  have hmaps : ∀ x : X, Φ x ∈ Metric.ball (0 : ℂ) 1 :=
    Submission.phi_mem_ball hpos hmod hzero
  have hbij : Function.Bijective (fun x : X => (⟨Φ x, hmaps x⟩ : Metric.ball (0 : ℂ) 1)) :=
    Commons.Analysis.Complex.ProperIntoBall.bijective_of_isProperMap_into_ball_single_zero
      hmaps (fun K hK hKsub => Submission.isCompact_preimage_of_green hpos hmod hzero
        hE'.1.2.2 hΦ.continuous hK hKsub) (fun x => hΦ x (mem_univ x))
      (Submission.phi_preimage_zero hpos hmod hzero)
      (Submission.phi_deriv_ne_zero_of_logPole hpole)
  refine ⟨Φ, hΦ, fun x y hxy => hbij.1 (Subtype.ext hxy), hmaps, fun w hw => ?_⟩
  obtain ⟨x, hx⟩ := hbij.2 ⟨w, by rwa [Metric.mem_ball, dist_eq_norm, sub_zero]⟩
  exact ⟨x, congrArg Subtype.val hx⟩

end Ball

/-- **The simply connected, non-compact case of uniformization**, with the parabolic branch as its
only remaining input. -/
theorem uniformization_of_simplyConnected_of_parabolic [SimplyConnectedSpace X]
    (hX : ¬ CompactSpace X)
    (hC : (∀ (z₀ : X) (E : X → ℝ), ¬ Submission.HasGreenFunctionWeak z₀ E) →
      Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ)) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) :=
  Work.SC.uniformization_of_simplyConnected_of_inputs' hX
    (fun z₀ => logCoefficientInput z₀) (fun z₀ => removableInput z₀)
    (fun hE => isCoveringMap_branchProj' hE) hC

end Work.SC
