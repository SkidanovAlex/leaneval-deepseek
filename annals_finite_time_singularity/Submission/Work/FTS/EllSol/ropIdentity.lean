/-
# `Work.FTS.EllSol.ropIdentity` — the pointwise identity of the `ℛ`-transfer

The identity

  `ℛ(Ξ) = 4 sin²θ · (Ξ/sin 2θ) + 2 sin²θ · (α D_z(Ξ/sin 2θ)) + ∂_θΞ`

on the open quadrant, `Ξ = EllResid α F Ψ`.  It is the structural core of the `ℛ`-transfer: it
replaces the two unbounded coefficients `tan θ` of `ℛ` by the *bounded* profiles `sin²θ`, at the
price of dividing `Ξ` by `sin 2θ` (which is harmless because `Ξ` vanishes on the two angular
boundary lines).  It is the same identity as `Work.FTS.EllipticEst.Rop_EllResid_eq_sin_sq`,
re-proved here so that the assembly of `ropTransfer.lean` does not have to import the (oversize)
module carrying it.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllSol.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- **`ℛ(Ξ) = 4 sin²θ · Φ + 2 sin²θ · (α D_zΦ) + ∂_θΞ`** on the open quadrant, where
`Φ = Ξ/sin 2θ`.  The two `tan θ` factors of `ℛ` cancel into the bounded profiles `sin²θ`. -/
theorem Rop_EllResid_eq_sin_sq_local (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hd : DifferentiableAt ℝ
      (fun θ' => Work.Elliptic.EllResid α F Ψ z θ' / Real.sin (2 * θ')) θ) :
    Work.FTS.EllipticEst.Rop α (Work.Elliptic.EllResid α F Ψ) z θ
      = 4 * Real.sin θ ^ 2 * (Work.Elliptic.EllResid α F Ψ z θ / Real.sin (2 * θ))
        + 2 * Real.sin θ ^ 2 * (α * Work.Spaces.Dz
            (fun z θ => Work.Elliptic.EllResid α F Ψ z θ / Real.sin (2 * θ)) z θ)
        + Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) z θ := by
  have hsinθ : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos]))
  have hsin : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  have hcos : Real.cos θ ≠ 0 := by
    intro h
    rw [Real.sin_two_mul, h] at hsin
    simp at hsin
  set q : ℝ := Work.Elliptic.EllResid α F Ψ z θ / Real.sin (2 * θ) with hq
  have hΞ : Work.Elliptic.EllResid α F Ψ z θ = Real.sin (2 * θ) * q := by
    rw [hq, mul_div_cancel₀ _ hsin]
  have hsin2' : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
    have h2' : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    exact (Real.hasDerivAt_sin (2 * θ)).comp θ h2'
  have heq : (fun θ' => Work.Elliptic.EllResid α F Ψ z θ')
      =ᶠ[𝓝 θ] (fun θ' => Real.sin (2 * θ') *
        (Work.Elliptic.EllResid α F Ψ z θ' / Real.sin (2 * θ'))) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (Real.pi / 2) from ⟨hθ0, hθ1⟩)]
      with θ' hθ'
    have hs : Real.sin (2 * θ') ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ'.1])
        (by linarith [hθ'.2, Real.pi_pos]))
    field_simp
  have hpth : Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) z θ
      = 2 * Real.cos (2 * θ) * q
        + Real.sin (2 * θ) * Work.Spaces.pth
            (fun z θ => Work.Elliptic.EllResid α F Ψ z θ / Real.sin (2 * θ)) z θ := by
    have h1 : Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) z θ
        = deriv (fun θ' => Real.sin (2 * θ') *
            (Work.Elliptic.EllResid α F Ψ z θ' / Real.sin (2 * θ'))) θ := by
      simp only [Work.Spaces.pth]
      exact Filter.EventuallyEq.deriv_eq heq
    have h2 : deriv (fun θ' => Real.sin (2 * θ') *
            (Work.Elliptic.EllResid α F Ψ z θ' / Real.sin (2 * θ'))) θ
        = (Real.cos (2 * θ) * 2)
            * (Work.Elliptic.EllResid α F Ψ z θ / Real.sin (2 * θ))
          + Real.sin (2 * θ) * deriv (fun θ' =>
              Work.Elliptic.EllResid α F Ψ z θ' / Real.sin (2 * θ')) θ :=
      (hsin2'.mul hd.hasDerivAt).deriv
    rw [h1, h2]
    simp only [Work.Spaces.pth]
    rw [hq]
    ring
  have hpz : Work.Spaces.pz (Work.Elliptic.EllResid α F Ψ) z θ
      = Real.sin (2 * θ) * Work.Spaces.pz
          (fun z θ => Work.Elliptic.EllResid α F Ψ z θ / Real.sin (2 * θ)) z θ := by
    simp only [Work.Spaces.pz]
    rw [show (fun z' => Work.Elliptic.EllResid α F Ψ z' θ)
        = fun z' => Real.sin (2 * θ)
            * (Work.Elliptic.EllResid α F Ψ z' θ / Real.sin (2 * θ)) from by
      funext z'; field_simp]
    exact deriv_const_mul_field (Real.sin (2 * θ))
  rw [Work.FTS.EllipticEst.Rop, hpz, hpth, hΞ, Real.sin_two_mul, Real.cos_two_mul]
  field_simp
  simp only [Work.Spaces.Dz]
  ring

end Work.FTS.EllSol
