import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Gdot
import Submission.Work.FTS.StrongEps.hasDerivWithinAt_of_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

theorem epsSol_eq_integral {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} (hsol : Work.FTS.StrongEps.IsEpsSol α ρ ε T Φs E g₀ g)
    (hcont : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s => Work.FTS.StrongEps.epsRHS α ρ ε Φs E g s z θ) (Set.Icc 0 T)) :
    ∀ z θ τ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → τ ∈ Set.Icc 0 T →
      g z θ τ = g₀ z θ + ∫ s in (0 : ℝ)..τ, Work.FTS.StrongEps.epsRHS α ρ ε Φs E g s z θ := by
  -- `Q0` is the *open* quadrant, so the pointwise scheme `IsEpsSol` applies at `(z,θ)`,
  -- and the prescribed derivative is exactly `epsRHS`.
  intro z θ τ hQ hτ
  obtain ⟨hz, hθ₁, hθ₂⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ₁, hθ₂⟩
  -- the fake-time derivative of the slice `s ↦ g z θ s`, within `[0,T]`.
  have hderiv : ∀ x ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => g z θ s)
        (Work.FTS.StrongEps.epsRHS α ρ ε Φs E g x z θ) (Set.Icc 0 T) x :=
    fun x hx => hsol.2 z θ x hz hθ hx
  -- the fundamental theorem of calculus on `[0,τ]`, with a continuous integrand
  -- (`hcont`), so that the (one-sided) derivative on the whole interval bounds the integral.
  have hsub : Set.Icc (0 : ℝ) τ ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl hτ.2
  have hftc : ∫ s in (0 : ℝ)..τ, Work.FTS.StrongEps.epsRHS α ρ ε Φs E g s z θ
      = g z θ τ - g z θ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ.1
      ((HasDerivWithinAt.continuousOn hderiv).mono hsub)
      (fun x hx => (hderiv x ⟨hx.1.le, le_trans hx.2.le hτ.2⟩).hasDerivAt
        (Icc_mem_nhds hx.1 (lt_of_lt_of_le hx.2 hτ.2)))
      (ContinuousOn.intervalIntegrable_of_Icc hτ.1 ((hcont z θ hQ).mono hsub))
  rw [← hsol.1 z θ]
  linarith

end Work.FTS.StrongEps
