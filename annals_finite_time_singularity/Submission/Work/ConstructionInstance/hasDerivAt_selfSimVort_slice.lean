import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.ConstructionInstance.SelfSim
import Submission.Work.ConstructionInstance.hasDerivAt_inv_mul_comp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **The time slice of the constructed (cut) self-similar vorticity is differentiable in `t`.**

The cut field is `selfSimVort p g L lam x t = χ(ρ(x)/L) • U x t`, where
`U x t = λ̄(t)⁻¹ • omegaSz p g (ρ(x)^p/λ̄(t)) x` is the *uncut* self-similar field.  Since the
cut-off factor and the frame `e_θ(x)` do not depend on `t`, the derivative in `t` is obtained from
the scalar chain rule `hasDerivAt_inv_mul_comp` for `s ↦ λ̄(s)⁻¹ · F(c/λ̄(s))`; equivalently, the
field is `s ↦ (a * ((lam s)⁻¹ * profile p g (c / lam s) θ)) • e` for the constants
`a = χ(ρ(y)/L)`, `c = ρ(y)^p`, `θ = θ(y)` and the constant vector `e = e_θ(y)`.

On the symmetry axis (`radial y = 0`) the frame vector `e_θ(y)` vanishes, so the field is
identically `0`. -/
theorem hasDerivAt_selfSimVort_slice {p : ℝ} {g : ℝ → ℝ → ℝ} {L : ℝ} {lam : ℝ → ℝ} {T : ℝ}
    (hgdiff : ∀ z θ : ℝ, 0 < z →
      HasDerivAt (fun z' => Work.ConstructionInstance.profile p g z' θ)
        (Work.Spaces.pz (Work.ConstructionInstance.profile p g) z θ) z)
    (hlam : ∀ t ∈ Work.ConstructionInstance.preWindow T, 0 < lam t)
    (hlamdif : ∀ t ∈ Work.ConstructionInstance.preWindow T, HasDerivAt lam (deriv lam t) t)
    {t : ℝ} (ht : t ∈ Work.ConstructionInstance.preWindow T) (y : Work.ConstructionInstance.R3) :
    HasDerivAt (fun s : ℝ => Work.ConstructionInstance.selfSimVort p g L lam y s)
      (FiniteTimeSingularity.timeDeriv
        (Work.ConstructionInstance.selfSimVort p g L lam) y t) t := by
  have hlt : 0 < lam t := hlam t ht
  by_cases hrad : Work.Cyl.radial y = 0
  · -- on the symmetry axis the field vanishes identically
    have he0 : Work.Cyl.eTheta y = 0 := by
      rw [Work.Cyl.eTheta, hrad, div_zero, zero_smul]
    have hω0 : selfSimVort p g L lam y = fun _ => 0 := by
      funext s
      rw [selfSimVort_apply, omegaSz_apply, he0, smul_zero, smul_zero, smul_zero]
    rw [FiniteTimeSingularity.timeDeriv, hω0, deriv_const]
    exact hasDerivAt_const t 0
  · have hy : y ≠ 0 := by
      intro h0
      exact hrad (by rw [h0, Work.Cyl.radial_eq_zero_iff]; exact ⟨rfl, rfl⟩)
    have hρpos : 0 < Work.Cyl.rho y := by rw [Work.Cyl.rho_pos_iff]; exact hy
    set c : ℝ := Work.Cyl.rho y ^ p with hc
    set θ : ℝ := Work.Cyl.theta y with hθdef
    set e : R3 := Work.Cyl.eTheta y with he
    set a : ℝ := Work.Stability.chi (Work.Cyl.rho y / L) with ha
    have hcpos : 0 < c := by rw [hc]; exact Real.rpow_pos_of_pos hρpos p
    have hzpos : 0 < c / lam t := div_pos hcpos hlt
    -- the scalar chain rule for `s ↦ λ̄(s)⁻¹ · F(c/λ̄(s))`
    have hφ : HasDerivAt (fun s => (lam s)⁻¹ * profile p g (c / lam s) θ)
        (-(deriv lam t * (profile p g (c / lam t) θ
          + (c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ) / (lam t) ^ 2)) t :=
      hasDerivAt_inv_mul_comp (F := fun z' => profile p g z' θ) (hlamdif t ht) (ne_of_gt hlt)
        (hgdiff (c / lam t) θ hzpos)
    -- the cut field is `χ(ρ(y)/L) = a` times the uncut scalar part, along the constant vector `e`
    have hcut : selfSimVort p g L lam y
        = fun s => (a * ((lam s)⁻¹ * profile p g (c / lam s) θ)) • e := by
      funext s
      rw [selfSimVort_apply, ← ha, omegaSz_apply, ← hc, ← hθdef, ← he]
      rw [smul_smul, smul_smul]
      congr 1
      ring
    have hderivG : HasDerivAt (selfSimVort p g L lam y)
        ((a * (-(deriv lam t * (profile p g (c / lam t) θ
          + (c / lam t) * Work.Spaces.pz (profile p g) (c / lam t) θ)
            / (lam t) ^ 2))) • e) t := by
      rw [hcut]
      exact (hφ.const_mul a).smul_const e
    rw [FiniteTimeSingularity.timeDeriv, hderivG.deriv]
    exact hderivG

end Work.ConstructionInstance
