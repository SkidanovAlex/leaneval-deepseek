/-
T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. 194 (3) 2021.

The angular moment `F_*(z) = ∫_θ F(z,θ) sinθcos²θ dθ` can be computed from the *smooth* form
`FstarInt α Ψ` of the integrand: on the open quadrant `F = bslOp α Ψ` (`IsBslSol`) and the
angular weight turns `bslOp α Ψ z θ · sinθcos²θ` into `FstarInt α Ψ z θ`
(`bslOp_mul_sinCos2_eq`); the two exceptional angles `θ = 0` (where `IsBslSol` says nothing)
and `θ = π/2` (where the `tan`-term of `bslOp` is singular) form a null set, so they do not
change the integral.  `SmoothNbhd Ψ` is only used to differentiate the `θ`-slice of `Ψ` at
the interior angles.

The a.e. form of `MeasureTheory.setIntegral_congr_ae` means that no integrability of the two
integrands is needed.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Cert.FstarSmooth.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.PsiStar_ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert.FstarSmooth

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- The `θ`-slice of a function which is smooth on a neighbourhood of the closed quadrant is
differentiable at every point of the open quadrant. -/
private lemma differentiableAt_slice_snd_open {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) {z θ : ℝ} (hz : -1 < z) (hθ : -1 < θ)
    (hθ' : θ < π / 2 + 1) : DifferentiableAt ℝ (fun θ' => f z θ') θ := by
  have hy : (z, θ) ∈ Work.Spaces.nbhU := by
    simp only [Work.Spaces.nbhU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
    exact ⟨hz, hθ, hθ'⟩
  have hd : DifferentiableAt ℝ (Function.uncurry f) (z, θ) :=
    (hf.contDiffAt (Work.Spaces.isOpen_nbhU.mem_nhds hy)).differentiableAt (by norm_num)
  change DifferentiableAt ℝ (Function.uncurry f ∘ fun θ' : ℝ => (z, θ')) θ
  exact hd.comp θ (hasFDerivAt_prodMk_right z θ).differentiableAt

/-- On the open quadrant the two integrands agree: there `F = bslOp α Ψ` (`IsBslSol`) and the
angular weight turns `bslOp α Ψ z θ · sinθcos²θ` into `FstarInt α Ψ z θ`. -/
private lemma integrand_eq_of_pos {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ2 : θ < π / 2) :
    F z θ * Work.Elliptic.sinCos2 θ
      = Work.FTS.EllipticEst.Cert.FstarInt α Ψ z θ := by
  have hcos : Real.cos θ ≠ 0 := by
    have h := Real.cos_pos_of_mem_Ioo (show θ ∈ Set.Ioo (-(π / 2)) (π / 2) from
      ⟨by linarith [Real.pi_pos], hθ2⟩)
    linarith
  have hd : DifferentiableAt ℝ (fun θ' => Ψ z θ') θ :=
    differentiableAt_slice_snd_open hΨ (by linarith) (by linarith)
      (by linarith [Real.pi_pos])
  rw [← hsol.1 z hz θ hθ0 hθ2]
  exact Work.FTS.EllipticEst.Cert.bslOp_mul_sinCos2_eq α Ψ hcos hd

theorem Fstar_eq_integral_FstarInt (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hΨ : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    ∀ z, 0 < z →
      Work.Elliptic.Fstar F z
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
      · exact absurd (integrand_eq_of_pos hΨ hsol hz h0 h2) hθ.2
  · exact Set.Finite.measure_zero (Set.Finite.insert 0 (Set.finite_singleton (π / 2))) volume

end Work.FTS.EllipticEst.Cert.FstarSmooth
