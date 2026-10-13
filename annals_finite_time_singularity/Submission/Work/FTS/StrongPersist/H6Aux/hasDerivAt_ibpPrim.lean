import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux

theorem hasDerivAt_ibpPrim {q : ℝ} {H : ℝ → ℝ}
    (hH : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), HasDerivAt H (deriv H θ) θ) :
    ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      HasDerivAt (fun θ' => Real.sin (2*θ') * ((Real.sin (2*θ'))^(-q) * (H θ')^2))
        (2 * (Real.sin (2*θ) * deriv H θ * H θ * (Real.sin (2*θ))^(-q))
          - 2*(q-1) * (Real.cos (2*θ) * (Real.sin (2*θ))^(-q) * (H θ)^2)) θ := by
  intro θ hθ
  -- on the open interval `sin (2θ) > 0`
  have hs0 : 0 < Real.sin (2*θ) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [hθ.1]
    · linarith [hθ.2]
  -- the inner chain rule for `θ' ↦ sin (2θ')`
  have h2 : HasDerivAt (fun θ' : ℝ => 2*θ') (2:ℝ) θ := by
    simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin (2*θ')) (Real.cos (2*θ) * 2) θ := h2.sin
  -- and the real power of it
  have hpow : HasDerivAt (fun θ' : ℝ => Real.sin (2*θ') ^ (-q))
      ((Real.cos (2*θ) * 2) * (-q) * Real.sin (2*θ) ^ (-q - 1)) θ := by
    have h := hsin.rpow_const (p := -q) (Or.inl (ne_of_gt hs0))
    simpa using h
  have hsq : HasDerivAt (H ^ 2) (2 * H θ * deriv H θ) θ := by
    have h := (hH θ hθ).pow 2
    simpa using h
  have hprod := hsin.mul (hpow.mul hsq)
  -- rewrite the pointwise product of functions into the product-rule shape
  have hfun : (fun θ' : ℝ => Real.sin (2*θ') *
      (Real.sin (2*θ') ^ (-q) * (H θ')^2))
      = (fun θ' : ℝ => Real.sin (2*θ')) * ((fun θ' : ℝ => Real.sin (2*θ') ^ (-q)) * (H ^ 2)) := by
    funext θ'; simp [Pi.mul_apply, Pi.pow_apply]
  rw [hfun]
  refine hprod.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply]
  -- abbreviate `s = sin (2θ) > 0`; the only `rpow` fact needed is `s * s^{-q-1} = s^{-q}`
  set s := Real.sin (2*θ) with hsdef
  have hs : 0 < s := hs0
  have hrpow : s * s ^ (-1 - q) = s ^ (-q) := by
    rw [show (-1 - q : ℝ) = -q - 1 by ring, Real.rpow_sub hs (-q) 1, Real.rpow_one,
      ← mul_div_assoc]
    exact mul_div_cancel_left₀ _ (ne_of_gt hs)
  have hrpow_gen : ∀ a : ℝ, a * s * s ^ (-1 - q) = a * s ^ (-q) := by
    intro a; rw [mul_assoc, hrpow]
  ring_nf
  rw [hrpow_gen]
  ring

end Work.FTS.StrongPersist.H6Aux
