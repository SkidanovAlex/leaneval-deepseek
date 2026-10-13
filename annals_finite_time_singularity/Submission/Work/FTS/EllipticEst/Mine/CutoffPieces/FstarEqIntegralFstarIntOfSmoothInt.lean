/-
T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. 194 (3) 2021.

The angular moment `F_*(z) = ∫_θ F(z,θ) sinθcos²θ dθ` can be computed from the *smooth*
form `FstarInt α Ψ` of the integrand: on the open quadrant `F = bslOp α Ψ` (`IsBslSol`) and
the angular weight turns `bslOp α Ψ z θ · sinθcos²θ` into `FstarInt α Ψ z θ`
(`bslOp_mul_sinCos2_eq`); the two exceptional angles `θ = 0` (where `IsBslSol` says nothing)
and `θ = π/2` (where the `tan`-term of `bslOp` is singular) form a null set, so they do not
change the integral.

This is the same statement as `Work.FTS.EllipticEst.Cert.FstarSmooth.Fstar_eq_integral_FstarInt`,
but with the *weak* regularity hypothesis `SmoothInt Ψ` instead of `SmoothNbhd Ψ`.  The only
place where `SmoothNbhd` was used in that proof is the differentiability of the `θ`-slice of
`Ψ` at an interior angle; `SmoothInt` suffices for that, because smoothness on the open strip
`(-1,∞) × (0,π/2)` gives the derivative at every interior point
(`SmoothIntSliceDifferentiableAt`, which is already available in this directory).

The a.e. form of `MeasureTheory.setIntegral_congr_ae` means that no integrability of the two
integrands is needed.
-/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Cert.FstarSmooth.Defs
import Submission.Work.FTS.EllipticEst.Cert.FstarSmooth.Fstar_eq_integral_FstarInt
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Mine.CutoffPieces.SmoothIntSliceDifferentiableAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine.CutoffPieces

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- On the open quadrant the two integrands agree: there `F = bslOp α Ψ` (`IsBslSol`) and the
angular weight turns `bslOp α Ψ z θ · sinθcos²θ` into `FstarInt α Ψ z θ`.  The differentiability
of the `θ`-slice of `Ψ` at the interior angle `θ` comes from `SmoothInt Ψ`. -/
private lemma integrand_eq_of_pos {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.Spaces.SmoothInt Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ2 : θ < π / 2) :
    F z θ * Work.Elliptic.sinCos2 θ
      = Work.FTS.EllipticEst.Cert.FstarInt α Ψ z θ := by
  have hcos : Real.cos θ ≠ 0 := by
    have h := Real.cos_pos_of_mem_Ioo (show θ ∈ Set.Ioo (-(π / 2)) (π / 2) from
      ⟨by linarith [Real.pi_pos], hθ2⟩)
    linarith
  have hd : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ :=
    SmoothIntSliceDifferentiableAt Ψ hΨ hz ⟨hθ0, hθ2⟩
  rw [← hsol.1 z hz θ hθ0 hθ2]
  exact Work.FTS.EllipticEst.Cert.bslOp_mul_sinCos2_eq α Ψ hcos hd

theorem FstarEqIntegralFstarIntOfSmoothInt (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.Spaces.SmoothInt Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Cert.FstarInt α Ψ z θ := by
  intro z hz
  rw [Work.Elliptic.Fstar]
  refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (t := ({0, π / 2} : Set ℝ)) (fun θ hθ => ?_) ?_
  · push Not at hθ
    have hθI : θ ∈ Work.Spaces.Iθ := hθ.1
    rcases eq_or_lt_of_le hθI.1 with h0 | h0
    · simp [h0.symm]
    · rcases eq_or_lt_of_le hθI.2 with h2 | h2
      · simp [h2]
      · exact absurd (integrand_eq_of_pos h hsol hz h0 h2) hθ.2
  · exact Set.Finite.measure_zero (Set.Finite.insert 0 (Set.finite_singleton (π / 2))) volume

end Work.FTS.EllipticEst.Mine.CutoffPieces
