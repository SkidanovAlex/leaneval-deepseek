import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

theorem invCos_jet_bound :
    ∃ B : ℕ → ℝ, ∀ k : ℕ, ∀ θ ∈ Set.Ioo (0 : ℝ) (3 * Real.pi / 8),
      |iteratedDeriv k (fun t : ℝ => (Real.cos t)⁻¹) θ| ≤ B k := by
  -- `sec θ = (cos θ)⁻¹` is `C^∞` on the open interval `(-π/2, π/2)`, hence every
  -- iterated derivative is continuous on the closed interval `[0, 3π/8]`, where it
  -- attains a finite maximum. That maximum supplies `B k`.
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hU : IsOpen (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := isOpen_Ioo
  have hsub : Set.Icc (0 : ℝ) (3 * Real.pi / 8) ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- `sec` is `C^n` on the open interval, for every `n`, since `cos` is and is nonzero there.
  have hcd : ∀ n : ℕ, ContDiffOn ℝ n (fun t : ℝ => (Real.cos t)⁻¹)
      (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
    intro n
    have h1 : ContDiffOn ℝ n (fun t : ℝ => Real.cos t)
        (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := Real.contDiff_cos.contDiffOn
    exact h1.inv (fun t ht => ne_of_gt (Real.cos_pos_of_mem_Ioo ht))
  -- Therefore each iterated derivative is continuous on the closed interval.
  have hcont : ∀ k : ℕ, ContinuousOn (iteratedDeriv k (fun t : ℝ => (Real.cos t)⁻¹))
      (Set.Icc (0 : ℝ) (3 * Real.pi / 8)) := by
    intro k
    have h1 : ContinuousOn (iteratedDerivWithin k (fun t : ℝ => (Real.cos t)⁻¹)
          (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)))
        (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
      (hcd k).continuousOn_iteratedDerivWithin le_rfl hU.uniqueDiffOn
    have h2 : ContinuousOn (iteratedDerivWithin k (fun t : ℝ => (Real.cos t)⁻¹)
          (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)))
        (Set.Icc (0 : ℝ) (3 * Real.pi / 8)) := h1.mono hsub
    refine h2.congr ?_
    -- on the open interval the `Within` and the honest iterated derivative agree
    exact ((iteratedDerivWithin_of_isOpen hU).mono hsub).symm
  -- weierstrass on the compact interval
  choose B hB using fun k => isCompact_Icc.exists_bound_of_continuousOn (hcont k)
  refine ⟨B, fun k θ hθ => ?_⟩
  have hmem : θ ∈ Set.Icc (0 : ℝ) (3 * Real.pi / 8) := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  simpa using hB k θ hmem

end Work.FTS.EllipticEst.remov
