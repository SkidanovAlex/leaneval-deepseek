import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.FieldDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open Work.Cyl

theorem first_derivs_mul_pow_rpow (Ψ : ℝ → ℝ → ℝ) (α ρ θ : ℝ) (hρ : 0 < ρ)
    (hΨ : ContDiffAt ℝ 2 (Function.uncurry Ψ) (ρ ^ α, θ)) :
    Work.Cyl.pdR (fun p q => p ^ 2 * Ψ (p ^ α) q) ρ θ
        = 2 * ρ * Ψ (ρ ^ α) θ + α * ρ ^ (α + 1) * Work.Cyl.pdR Ψ (ρ ^ α) θ
      ∧ Work.Cyl.pdZ (fun p q => p ^ 2 * Ψ (p ^ α) q) ρ θ = ρ ^ 2 * Work.Cyl.pdZ Ψ (ρ ^ α) θ
      ∧ Work.Cyl.pdZZ (fun p q => p ^ 2 * Ψ (p ^ α) q) ρ θ = ρ ^ 2 * Work.Cyl.pdZZ Ψ (ρ ^ α) θ := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  refine ⟨?_, ?_, ?_⟩
  · -- radial derivative
    have hΨd : Work.Cyl.DiffAt2 Ψ (ρ ^ α) θ := hΨ.differentiableAt (by decide)
    have hslice : DifferentiableAt ℝ (fun u : ℝ => Ψ u θ) (ρ ^ α) :=
      differentiableAt_slice_fst Ψ (ρ ^ α) θ hΨd
    have hslice' : HasDerivAt (fun u : ℝ => Ψ u θ) (Work.Cyl.pdR Ψ (ρ ^ α) θ) (ρ ^ α) :=
      hslice.hasDerivAt
    have hpow : HasDerivAt (fun p : ℝ => p ^ α) (α * ρ ^ (α - 1)) ρ :=
      Real.hasDerivAt_rpow_const (Or.inl hρne)
    have hcomp₀ : HasDerivAt ((fun u : ℝ => Ψ u θ) ∘ (fun p : ℝ => p ^ α))
        (Work.Cyl.pdR Ψ (ρ ^ α) θ * (α * ρ ^ (α - 1))) ρ :=
      hslice'.comp ρ hpow
    have hcomp : HasDerivAt (fun p : ℝ => Ψ (p ^ α) θ)
        (Work.Cyl.pdR Ψ (ρ ^ α) θ * (α * ρ ^ (α - 1))) ρ := hcomp₀
    have h2 : HasDerivAt (fun p : ℝ => p ^ 2) (2 * ρ) ρ := by
      simpa using (hasDerivAt_pow 2 ρ)
    have hprod : HasDerivAt (fun r' : ℝ => r' ^ 2 * Ψ (r' ^ α) θ)
        (2 * ρ * Ψ (ρ ^ α) θ + ρ ^ 2 * (Work.Cyl.pdR Ψ (ρ ^ α) θ * (α * ρ ^ (α - 1)))) ρ :=
      h2.mul hcomp
    rw [Work.Cyl.pdR, hprod.deriv]
    have hpow2 : ρ ^ (2:ℝ) = ρ ^ 2 := Real.rpow_natCast ρ 2
    have hkey : ρ ^ (2:ℝ) * ρ ^ (α - 1) = ρ ^ (α + 1) := by
      rw [← Real.rpow_add hρ]
      congr 1
      ring
    rw [← hpow2, ← hkey]
    ring
  · -- axial derivative
    rw [Work.Cyl.pdZ, Work.Cyl.pdZ, deriv_const_mul_field]
  · -- second axial derivative
    have hfun : (fun z' => Work.Cyl.pdZ (fun p q => p ^ 2 * Ψ (p ^ α) q) ρ z')
        = fun z' => ρ ^ 2 * Work.Cyl.pdZ Ψ (ρ ^ α) z' := by
      funext z'
      rw [Work.Cyl.pdZ, Work.Cyl.pdZ, deriv_const_mul_field]
    rw [Work.Cyl.pdZZ, Work.Cyl.pdZZ, hfun, deriv_const_mul_field]

end Work.Elliptic
