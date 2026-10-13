import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.AeColl.pairFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.EllipticEst.Deleg

/-- `psiD δ` agrees with the constant `1` on the *open* interval `(δ/2, π/2 - δ/2)`
(where it is already known to equal `1`), hence — that interval being open — its germ at any
interior point `θ` is the germ of the constant `1`.  Consequently both `deriv` and
`deriv ∘ deriv` of `psiD δ` vanish at `θ`. -/
theorem psiD_deriv2_zero_mid : ∀ (δ : ℝ), 0 < δ → ∀ θ : ℝ, δ / 2 < θ → θ < Real.pi / 2 - δ / 2 →
    deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ = 0 := by
  intro δ hδ θ h1 h2
  -- `psiD δ` is the germ of the constant `1` at `θ`.
  have hmem : Set.Ioo (δ / 2) (Real.pi / 2 - δ / 2) ∈ 𝓝 θ :=
    isOpen_Ioo.mem_nhds ⟨h1, h2⟩
  have heq : Work.FTS.EllipticEst.AeColl.psiD δ =ᶠ[𝓝 θ] fun _ => (1 : ℝ) :=
    Filter.eventually_of_mem hmem fun θ' hθ' =>
      Work.FTS.EllipticEst.AeColl.psiD_eq_one_of_mem hδ (le_of_lt hθ'.1) (le_of_lt hθ'.2)
  -- Differentiating preserves the germ relation.
  have h1eq : deriv (Work.FTS.EllipticEst.AeColl.psiD δ) =ᶠ[𝓝 θ] deriv (fun _ => (1 : ℝ)) :=
    heq.deriv
  calc deriv (deriv (Work.FTS.EllipticEst.AeColl.psiD δ)) θ
      = deriv (deriv (fun _ => (1 : ℝ))) θ := h1eq.deriv_eq
    _ = 0 := by simp

end Work.FTS.EllipticEst.Deleg
