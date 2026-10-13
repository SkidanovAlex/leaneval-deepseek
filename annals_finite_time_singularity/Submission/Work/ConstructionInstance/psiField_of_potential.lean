import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.Cyl.Coords
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Cyl.hasDerivAt_div_id

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

namespace Work.ConstructionInstance

/-- Reconstruction of the stream function.  If the profile `(r,z) ↦ φ (r,z)` has gradient
`(-(r u_z), r u_r)` on the half-plane `r > 0`, then the no-swirl velocity field with components
`u_r, u_z` is a stream-function field, namely for `ψ = φ/r`:

`∂_z ψ = u_r` and `∂_r ψ + ψ/r = -u_z`, which is exactly the stream-function representation
`u_r = ∂_z ψ`, `u_z = -(ψ/r) - ∂_r ψ` of `Work.Cyl.psiField`. -/
theorem psiField_of_potential (ur uz : ℝ → ℝ → ℝ) (φ : ℝ × ℝ → ℝ)
    (hφ : ∀ p : ℝ × ℝ, 0 < p.1 →
      HasFDerivAt φ
        ((-(p.1 * uz p.1 p.2)) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
          + (p.1 * ur p.1 p.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p) :
    ∃ ψ : ℝ → ℝ → ℝ, ∀ x : Work.Cyl.R3, 0 < Work.Cyl.radial x →
      Work.Cyl.cylField ur uz x = Work.Cyl.psiField ψ x := by
  -- The stream function is the potential divided by the radius.
  let ψ : ℝ → ℝ → ℝ := fun r z => φ (r, z) / r
  -- Off the axis the two defining relations of the stream function hold.
  have key : ∀ (R Z : ℝ), 0 < R →
      Work.Cyl.pdZ ψ R Z = ur R Z ∧
      -(ψ R Z / R) - Work.Cyl.pdR ψ R Z = uz R Z := by
    intro R Z hRpos
    have hRne : R ≠ 0 := ne_of_gt hRpos
    have hFd : HasFDerivAt φ
        ((-(R * uz R Z)) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
          + (R * ur R Z) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) (R, Z) := hφ (R, Z) hRpos
    -- the two one-variable derivatives of the potential
    have hrt : HasDerivAt (fun t => φ (t, Z)) (-(R * uz R Z)) R := by
      have h := Work.Spaces.hasDerivAt_slice_fst hFd
      have he : ((-(R * uz R Z)) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
            + (R * ur R Z) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) (1, 0) = -(R * uz R Z) := by
        simp
      rw [he] at h
      exact h
    have hzt : HasDerivAt (fun t => φ (R, t)) (R * ur R Z) Z := by
      have h := Work.Spaces.hasDerivAt_slice_snd hFd
      have he : ((-(R * uz R Z)) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
          + (R * ur R Z) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) (0, 1) = R * ur R Z := by
        simp
      rw [he] at h
      exact h
    have hpdZ_ha : HasDerivAt (fun z' => φ (R, z') / R) (ur R Z) Z := by
      have h := hzt.div_const R
      rw [mul_div_cancel_left₀ (ur R Z) hRne] at h
      exact h
    have hpdZ : Work.Cyl.pdZ ψ R Z = ur R Z := hpdZ_ha.deriv
    have hpdR_ha : HasDerivAt (fun r' => φ (r', Z) / r')
        (-(φ (R, Z) / R ^ 2) - uz R Z) R := by
      have h := Work.Cyl.hasDerivAt_div_id hrt hRne
      convert h using 1
      field_simp
      ring
    have hpdR : Work.Cyl.pdR ψ R Z = -(φ (R, Z) / R ^ 2) - uz R Z := hpdR_ha.deriv
    have hpsi : ψ R Z = φ (R, Z) / R := rfl
    refine ⟨hpdZ, ?_⟩
    rw [hpdR, hpsi]
    field_simp
    ring
  refine ⟨ψ, ?_⟩
  intro x hx
  set R := Work.Cyl.radial x with hR
  set Z := Work.Cyl.axial x with hZ
  obtain ⟨h1, h2⟩ := key R Z hx
  simp only [Work.Cyl.cylField, Work.Cyl.psiField]
  rw [← hR, ← hZ, h1, h2]

end Work.ConstructionInstance
