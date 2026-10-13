/-
Copyright: work module for the Elgindi finite-time singularity project.

# The derivative of the Wronskian flux `Bflux`

`Bflux u θ = cos θ * (u'(θ) * sin 2θ - u(θ) * 2 cos 2θ)` is the flux of `u` against the
kernel element `sin 2θ` of the one-dimensional operator

  `Lzero1 u = -u'' + (tan θ · u)' - 6u`.

The pointwise identity

  `deriv (Bflux u) θ = -(cos θ * sin 2θ) * Lzero1 u θ`

makes `Bflux` a primitive of an explicit multiple of `Lzero1 u`; it is the first step of the
endpoint analysis of `sliceRightSmall` (`Wn u = u / sin 2θ` has derivative
`Bflux u / (cos θ * sin 2θ ^ 2)`).

The proof is a direct product-rule computation.  Since `Bflux` involves `deriv u`, we need
`u` to be twice differentiable at `θ`; `hsm : ContDiffOn ℝ 2 u (Ioo 0 (π/2))` supplies this
(`ContDiffAt.derivWithin` for `m = 1` gives `C¹`-ness of `deriv u`).  The final real
identity is `ring`-provable after expanding `sin 2θ`, `cos 2θ` and `tan θ` (no use of
`sin² + cos² = 1` is needed; only `cos θ ≠ 0`).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.AngAWeak.SRSAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.EllipticEst.AngAWeak.SRSAux

theorem BfluxDeriv {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (Work.FTS.EllipticEst.AngAWeak.Bflux u)
      (-(Real.cos θ * Real.sin (2 * θ) * Work.FTS.EllipticEst.Lzero1 u θ)) θ := by
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have h2 : ContDiffAt ℝ 2 u θ := hsm.contDiffAt hmem
  have hdif : DifferentiableAt ℝ u θ := h2.differentiableAt (by norm_num)
  have hu : HasDerivAt u (deriv u θ) θ := hdif.hasDerivAt
  have hdu : HasDerivAt (deriv u) (deriv (deriv u) θ) θ :=
    ((h2.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hcpos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hcne : Real.cos θ ≠ 0 := ne_of_gt hcpos
  -- the derivative of `θ ↦ tan θ * u θ`, which is the second term of `Lzero1`
  have hderiv_mul : deriv (fun t => Real.tan t * u t) θ
      = (1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ := by
    change deriv (Real.tan * u) θ = _
    rw [deriv_mul (Real.differentiableAt_tan.mpr hcne) hdif, Real.deriv_tan]
  -- `Lzero1` evaluated at `θ`, with the derivative of the product expanded
  have hL : Work.FTS.EllipticEst.Lzero1 u θ
      = -deriv (deriv u) θ + ((1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ) - 6 * u θ := by
    rw [Work.FTS.EllipticEst.Lzero1, hderiv_mul]
  have hsin2 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    simpa [Function.comp_def] using (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  have hcos2 : HasDerivAt (fun t : ℝ => 2 * Real.cos (2 * t)) (2 * (-(Real.sin (2 * θ)) * 2)) θ := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h2' := (Real.hasDerivAt_cos (2 * θ)).comp θ h1
    have h3 := h2'.const_mul (2 : ℝ)
    simpa [Function.comp_def] using h3
  -- the derivative of the bracket `u' · sin 2θ - u · 2 cos 2θ`
  have hinner : HasDerivAt (fun t : ℝ => deriv u t * Real.sin (2 * t) - u t * (2 * Real.cos (2 * t)))
      ((deriv (deriv u) θ * Real.sin (2 * θ) + deriv u θ * (Real.cos (2 * θ) * 2))
        - (deriv u θ * (2 * Real.cos (2 * θ)) + u θ * (2 * (-(Real.sin (2 * θ)) * 2)))) θ :=
    (hdu.mul hsin2).sub (hu.mul hcos2)
  have hB : HasDerivAt (Work.FTS.EllipticEst.AngAWeak.Bflux u)
      ((-Real.sin θ) * (deriv u θ * Real.sin (2 * θ) - u θ * (2 * Real.cos (2 * θ)))
        + Real.cos θ * ((deriv (deriv u) θ * Real.sin (2 * θ) + deriv u θ * (Real.cos (2 * θ) * 2))
        - (deriv u θ * (2 * Real.cos (2 * θ)) + u θ * (2 * (-(Real.sin (2 * θ)) * 2))))) θ := by
    have hc : HasDerivAt Real.cos (-Real.sin θ) θ := Real.hasDerivAt_cos θ
    have hh := hc.mul hinner
    convert hh using 1
    funext t
    simp only [Work.FTS.EllipticEst.AngAWeak.Bflux, Pi.mul_apply]
  -- the resulting value is the announced multiple of `Lzero1 u θ`
  have hkey : ((-Real.sin θ) * (deriv u θ * Real.sin (2 * θ) - u θ * (2 * Real.cos (2 * θ)))
        + Real.cos θ * ((deriv (deriv u) θ * Real.sin (2 * θ) + deriv u θ * (Real.cos (2 * θ) * 2))
        - (deriv u θ * (2 * Real.cos (2 * θ)) + u θ * (2 * (-(Real.sin (2 * θ)) * 2)))))
      = -(Real.cos θ * Real.sin (2 * θ) * Work.FTS.EllipticEst.Lzero1 u θ) := by
    rw [hL, Real.sin_two_mul, Real.cos_two_mul, Real.tan_eq_sin_div_cos]
    field_simp
    ring
  rw [hkey] at hB
  exact hB

end Work.FTS.EllipticEst.AngAWeak.SRSAux
