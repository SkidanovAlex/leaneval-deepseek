/-
Copyright: work module for the Elgindi finite-time singularity project.

# Derivative of the angular integration-by-parts primitive

For `g` of class `C²` on the open interval `(0, π/2)` (so in particular at every interior
point `θ`), the primitive

  `θ ↦ g θ · g' θ · sin(2θ)^p - p · cos(2θ) · sin(2θ)^{p-1} · g θ²`

has derivative

  `(g')² sin(2θ)^p + g g'' sin(2θ)^p + 2p g² sin(2θ)^p + 2p(1-p) g² cot(2θ)² sin(2θ)^p`

at `θ`.  Equivalently, in the notation `σ = sin(2θ)^{-p}`,

  `(σ · g · g' - p cot(2θ) σ g²)' = σ (g')² + σ g g'' + 2p σ g² + 2p(1-p) cot(2θ)² σ g²`,

the sharp slice integration by parts (cf. `Prop.bPrimG_hasDerivAt`, which is the same
computation with the square completion `μ σ (g' - (1+p) cot(2θ) g)²` in place of the
expanded cross terms).

The two mixed terms `± 2p cos(2θ) sin(2θ)^{p-1} g g'` cancel, and the remaining
`sin(2θ)^{p-2} cos(2θ)²` is converted into `cot(2θ)² sin(2θ)^p` with the two `rpow`
identities `sin^{p-1} = sin^p / sin`, `sin^{p-2} = sin^p / sin²` (valid since `sin 2θ > 0`
on `(0, π/2)`).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS.EllipticEst.Prop

/-- **Derivative of the angular IBP primitive.**  For `p : ℝ` and `g` of class `C²` on a
neighbourhood of `θ ∈ (0, π/2)`,

  `(θ ↦ g g' sin(2θ)^p - p cos(2θ) sin(2θ)^{p-1} g²)'
      = (g')² sin(2θ)^p + g g'' sin(2θ)^p + 2p g² sin(2θ)^p
        + 2p(1-p) g² cot(2θ)² sin(2θ)^p`

at `θ`. -/
theorem angIbpPrimDeriv (p : ℝ) (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun t : ℝ => g t * deriv g t * (Real.sin (2 * t)) ^ p
        - p * Real.cos (2 * t) * (Real.sin (2 * t)) ^ (p - 1) * (g t) ^ 2)
      ((deriv g θ) ^ 2 * (Real.sin (2 * θ)) ^ p
        + g θ * deriv (deriv g) θ * (Real.sin (2 * θ)) ^ p
        + 2 * p * ((g θ) ^ 2 * (Real.sin (2 * θ)) ^ p)
        + 2 * p * (1 - p) * ((g θ) ^ 2 * (Real.cot (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ p)) θ := by
  -- `g` is `C²` at the interior point `θ`, hence both `g` and `deriv g` are differentiable there.
  have hgAt : ContDiffAt ℝ 2 g θ := hg.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have hg1 : HasDerivAt g (deriv g θ) θ := (hgAt.differentiableAt (by norm_num)).hasDerivAt
  have hg2 : HasDerivAt (deriv g) (deriv (deriv g) θ) θ :=
    ((hgAt.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  -- `sin (2 θ) > 0` on the interval, so the `rpow` derivative rules and the `rpow` algebra apply.
  have hs : (0:ℝ) < Real.sin (2*θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h2 : HasDerivAt (fun t : ℝ => 2*t) 2 θ := by simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2*t)) (2*Real.cos (2*θ)) θ := by
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_sin (2*θ)).comp θ h2
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (2*t)) (-2*Real.sin (2*θ)) θ := by
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_cos (2*θ)).comp θ h2
  -- the two `rpow` factors
  have hSp : HasDerivAt (fun t : ℝ => (Real.sin (2*t))^p)
      ((2*Real.cos (2*θ)) * p * (Real.sin (2*θ))^(p-1)) θ :=
    hsin.rpow_const (Or.inl hs.ne')
  have hSp1 : HasDerivAt (fun t : ℝ => (Real.sin (2*t))^(p-1))
      ((2*Real.cos (2*θ)) * (p-1) * (Real.sin (2*θ))^(p-2)) θ := by
    have h := hsin.rpow_const (Or.inl hs.ne') (p := p-1)
    rw [show p - 1 - 1 = p - 2 by ring] at h
    exact h
  -- assemble: `(g g' · sin^p) - (p cos · sin^{p-1} · g²)`
  have hA := (hg1.mul hg2).mul hSp
  have hC1 := hcos.mul hSp1
  have hB := (hC1.const_mul p).mul (hg1.pow 2)
  have hF := hA.sub hB
  refine (hF.congr_of_eventuallyEq ?_).congr_deriv ?_
  · -- the function built above is the target function
    filter_upwards with t
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
    ring
  · -- the derivative value equals the stated expression
    have e1 : Real.sin (2*θ) ^ (p-1) = Real.sin (2*θ)^p / Real.sin (2*θ) := by
      rw [Real.rpow_sub hs, Real.rpow_one]
    have e2 : Real.sin (2*θ) ^ (p-2) = Real.sin (2*θ)^p / (Real.sin (2*θ))^2 := by
      rw [Real.rpow_sub hs, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [Real.cot_eq_cos_div_sin]
    rw [e1, e2]
    field_simp
    ring

end Work.FTS.EllipticEst.Prop
