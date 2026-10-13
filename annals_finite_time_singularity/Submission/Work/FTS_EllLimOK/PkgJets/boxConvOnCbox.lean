import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_EllLimOK.BoxReg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS_EllLimOK.PkgJets

theorem boxConvOnCbox {α : ℝ} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {fn : ℕ → Work.FTS.Galerkin.Fn} {f : Work.FTS.Galerkin.Fn} {σ : ℕ → ℕ} {Ψ : ℝ → ℝ → ℝ}
    (hsol : ∀ n : ℕ,
      Work.FTS.StrongGlobal.IsBslSolPos α (fn (σ n)) (E (fn (σ n))))
    (hΨ : Work.FTS.StrongGlobal.IsBslSolPos α f Ψ)
    (hJ : Work.FTS_EllLimOK.JConv (fun n => E (fn (σ n))) Ψ) :
    ∀ a b : ℝ, 0 < a → a ≤ b → ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      Filter.Tendsto (fun n => E (fn (σ n)) p.1 p.2) Filter.atTop (nhds (Ψ p.1 p.2)) := by
  -- On the open quadrant the convergence is exactly the `j = i = 0` slot of `JConv`
  -- (`mixed 0 0 = id` definitionally), and on the two Dirichlet lines `θ = 0`, `θ = π/2`
  -- the sequence is *constantly* `0` because both `IsBslSolPos`'s carry the values there.
  intro a b ha _hab p hp
  rw [Work.FTS_EllLimOK.mem_cbox] at hp
  obtain ⟨hz, hθ⟩ := hp
  have hz0 : 0 < p.1 := lt_of_lt_of_le ha hz.1
  rcases eq_or_lt_of_le hθ.1 with h2 | h2
  · -- `θ = 0`
    rw [← h2]
    have hv : ∀ n : ℕ, E (fn (σ n)) p.1 0 = 0 := fun n => (hsol n).2.1 p.1 hz0.le
    rw [hΨ.2.1 p.1 hz0.le,
      show (fun n : ℕ => E (fn (σ n)) p.1 0) = fun _ => (0 : ℝ) from funext hv]
    exact tendsto_const_nhds
  · rcases eq_or_lt_of_le hθ.2 with h3 | h3
    · -- `θ = π/2`
      rw [h3]
      have hv : ∀ n : ℕ, E (fn (σ n)) p.1 (π / 2) = 0 := fun n => (hsol n).2.2.1 p.1 hz0.le
      rw [hΨ.2.2.1 p.1 hz0.le,
        show (fun n : ℕ => E (fn (σ n)) p.1 (π / 2)) = fun _ => (0 : ℝ) from funext hv]
      exact tendsto_const_nhds
    · -- interior point: the `JConv` slot `(j,i) = (0,0)`
      simpa using hJ 0 0 (by norm_num) p.1 p.2 ⟨hz0, h2, h3⟩

end Work.FTS_EllLimOK.PkgJets
