import Submission.Lib.Unif2.UnifDeps
import Submission.Lib.Unif2.GreenData
import Submission.Lib.Unif2.Endgame2
import Submission.Lib.Unif2.PackagingOpen
import Submission.Lib.Unif2.Commons.Analysis.Complex.ProperIntoBall.bijective_of_isProperMap_into_ball_single_zero

/-!
# The hyperbolic endgame, repaired, and the Green-function modulus interface

The endgame interface `Submission.uniformization_of_proper_single_zero_disc` (Session 13) uses the
properness hypothesis

`∀ K : Set ℂ, IsCompact K → IsCompact (Φ ⁻¹' (K ∩ Metric.ball (0 : ℂ) 1))`,

which is **unsatisfiable** when `X` is non-compact and `Φ` maps into the disc: taking
`K = Metric.closedBall 0 1` gives `Φ ⁻¹' (K ∩ ball) = univ`, so `IsCompact univ` would force
`CompactSpace X`.  The interface is therefore vacuous and cannot be applied to the problem.

The correct (satisfiable) properness condition is that preimages of compact subsets *of the disc*
are compact; that is the hypothesis of the commons lemma
`Commons.Analysis.Complex.ProperIntoBall.bijective_of_isProperMap_into_ball_single_zero`
(fleet child, this session, which repaired the same flaw in
`Commons.Analysis.Complex.bijective_of_properInto_ball_holomorphic_single_zero`).

This module provides

* `Submission.uniformization_of_properInto_disc` — the **repaired** hyperbolic endgame: a holomorphic
  `Φ : X → 𝔻`, proper into the disc, with `Φ ⁻¹' {0} = {z₀}` and a non-vanishing chart derivative at
  `z₀`, gives the conclusion (indeed `X ≅ 𝔻`);

* `Submission.uniformization_of_green_modulus` — the same, starting from the *Green-function data*:
  a positive harmonic function `E` on `X ∖ {z₀}` with a logarithmic pole at `z₀` and vanishing at
  infinity, together with a holomorphic `Φ` whose modulus is `exp (-E)`.  This isolates exactly the
  remaining analytic input of the hyperbolic case of uniformization.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The repaired hyperbolic endgame.**  A holomorphic map `Φ : X → 𝔻` which is proper into `𝔻`
(preimages of compact subsets of `𝔻` are compact), has `Φ ⁻¹' {0} = {z₀}` and a non-vanishing chart
derivative at `z₀`, is a biholomorphism onto `𝔻`; hence the uniformization conclusion holds.

Here `hX : ¬ CompactSpace X` is needed only to produce a point different from `z₀`. -/
theorem uniformization_of_properInto_disc (hX : ¬ CompactSpace X) {Φ : X → ℂ} {z₀ : X}
    (hmaps : ∀ x : X, Φ x ∈ Metric.ball (0 : ℂ) 1)
    (hprop : ∀ K : Set ℂ, IsCompact K → K ⊆ Metric.ball (0 : ℂ) 1 → IsCompact (Φ ⁻¹' K))
    (hΦ : HolomorphicOnX Φ univ) (hfib : Φ ⁻¹' {0} = {z₀})
    (hloc : deriv (Φ ∘ (chartAt ℂ z₀).symm) ((chartAt ℂ z₀) z₀) ≠ 0) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) := by
  have hbij : Function.Bijective (fun x : X => (⟨Φ x, hmaps x⟩ : Metric.ball (0 : ℂ) 1)) :=
    Commons.Analysis.Complex.ProperIntoBall.bijective_of_isProperMap_into_ball_single_zero
      hmaps hprop (fun x => hΦ x (mem_univ x)) hfib hloc
  have hderiv : ∀ z : X, deriv (Φ ∘ (chartAt ℂ z).symm) ((chartAt ℂ z) z) ≠ 0 := fun z =>
    Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic
      (fun a b hab => hbij.1 (Subtype.ext hab))
      (fun x => hΦ x (mem_univ x)) (exists_ne_of_not_compactSpace (X := X) hX z)
  exact uniformization_of_bijective_to_disc hmaps hbij hΦ hderiv

/-- **The Green-function modulus interface.**  If `E` is positive and harmonic off `z₀` with a
logarithmic pole at `z₀` (`Submission.HasLogPoleAt`), `E → 0` at infinity (the superlevel sets are
compact) and `exp (-E)` is the modulus of a holomorphic function `Φ`, then the uniformization
conclusion holds for `X`.

The hypothesis `hmod` is exactly the statement that *the Green function has a holomorphic
modulus*, i.e. that its conjugate differential has periods in `2πℤ`; the classical construction
realises `Φ = exp (-(G + iG*))`. -/
theorem uniformization_of_green_modulus (hX : ¬ CompactSpace X) {z₀ : X} {E : X → ℝ} {Φ : X → ℂ}
    (hΦ : HolomorphicOnX Φ univ)
    (hpos : ∀ x, x ≠ z₀ → 0 < E x)
    (hmod : ∀ x, x ≠ z₀ → ‖Φ x‖ = Real.exp (-(E x)))
    (hinf : ∀ ε : ℝ, 0 < ε → IsCompact {x : X | ε ≤ E x})
    (hpole : HasLogPoleAt z₀ Φ) :
    Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane) := by
  have hzero : Φ z₀ = 0 := phi_zero_of_logPole hΦ hpole
  exact uniformization_of_properInto_disc hX (phi_mem_ball hpos hmod hzero)
    (fun K hK hKsub => isCompact_preimage_of_green hpos hmod hzero hinf hΦ.continuous hK hKsub)
    hΦ (phi_preimage_zero hpos hmod hzero) (phi_deriv_ne_zero_of_logPole hpole)

end Submission
