import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.PkgJets.CosWeightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS_EllLimOK.PkgJets

/-- Auxiliary: the elementary derivative computation behind `cw_hasDerivAt`, isolated so
that the `rpow` bookkeeping and the algebraic rearrangement are visible separately.

It says that the derivative of `50 * sin(2θ)^(1-η) / cos(θ)^4` (as produced by the product
and `rpow` rules) equals `cwPhiD θ`.  Concretely, `(sin(2θ)^(1-η))' · cos(θ)^{-4} -
sin(2θ)^(1-η) · (cos(θ)^{-4})'` rearranges to `sin(2θ)^(-η) · (2(1-η)cos(2θ) + 8sin²θ) /
cos(θ)^4`, the two `rpow` exponents being normalised with `Real.rpow_add` and the identity
`sin(2θ) = 2 sin θ cos θ`. -/
private theorem cw_deriv_value (θ : ℝ) (hs : 0 < Real.sin (2 * θ)) :
    (50 * (2 * Real.cos (2 * θ) * (1 - Work.Spaces.eta)
            * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta - 1)) * (Real.cos θ) ^ (4 : ℕ)
        - 50 * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)
            * (4 * (Real.cos θ) ^ (3 : ℕ) * (-Real.sin θ))) / ((Real.cos θ) ^ (4 : ℕ)) ^ 2
      = cwPhiD θ := by
  rw [cwPhiD]
  -- normalise the two `rpow` exponents against the `sin(2θ)^(-η)` appearing in `cwPhiD`
  have hsexp : (1 : ℝ) - Work.Spaces.eta - 1 = -(Work.Spaces.eta) := by ring
  have hs1 : (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta)
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) * Real.sin (2 * θ) := by
    rw [show (1 : ℝ) - Work.Spaces.eta = -(Work.Spaces.eta) + 1 by ring,
      Real.rpow_add hs, Real.rpow_one]
  rw [hsexp, hs1, Real.sin_two_mul]
  field_simp
  ring

theorem cw_hasDerivAt : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
    HasDerivAt cwPhi (cwPhiD θ) θ := by
  intro θ hθ
  -- `θ ∈ (0, π/2)`, so both bases are non-zero on a neighbourhood of `θ`
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  -- `θ ↦ sin (2θ)` and hence its `(1-η)`-th power
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h2 := (Real.hasDerivAt_sin (2 * θ)).comp θ h1
    simpa [Function.comp_def, mul_comm] using h2
  have hA : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (1 - Work.Spaces.eta))
      (2 * Real.cos (2 * θ) * (1 - Work.Spaces.eta)
        * (Real.sin (2 * θ)) ^ (1 - Work.Spaces.eta - 1)) θ :=
    hsin.rpow_const (p := 1 - Work.Spaces.eta) (Or.inl (ne_of_gt hs))
  have hB : HasDerivAt (fun t : ℝ => (Real.cos t) ^ (4 : ℕ))
      (4 * (Real.cos θ) ^ (3 : ℕ) * (-Real.sin θ)) θ :=
    (Real.hasDerivAt_cos θ).pow 4
  -- product rule: quotient rule applied to `(50 · sin(2θ)^(1-η)) / cos(θ)^4`
  have hmain := (hA.const_mul (50 : ℝ)).div hB
    (pow_ne_zero 4 (ne_of_gt hc))
  -- the function of `hmain` is `cwPhi` up to definitional unfolding
  refine hmain.congr_deriv ?_
  exact cw_deriv_value θ hs

end Work.FTS_EllLimOK.PkgJets
