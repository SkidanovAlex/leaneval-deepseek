/-
# `solVort_holder` — the spatial slices of the constructed vorticity are `α`-Hölder

For a `ProfileData α` the vorticity of the construction is the *cut* self-similar field

  `solVort P x t = λ̄(t)⁻¹ · χ(ρ(x)/L) · F(ρ(x)^p/λ̄(t), θ(x)) · e_θ(x)`,   `p = profExp α = 3α`

(`Reduced.lean`).  This file proves that for every `t` before the maximal time the slice
`x ↦ solVort P x t` is `α`-Hölder — the `ωS_holder` field of the (repaired) input package.

## The argument

The only nontrivial regularity input is `holder_omegaS_of_data`, which proves that the *datum*
`omegaS (3α) g = F(ρ(x)^{3α}, θ(x))·e_θ(x)` is `α`-Hölder from the explicit data on the
perturbation `g` (its angular vanishing, its radial/angular `α`-moduli, the vanishing at `z = 0`
and the smoothness near the closed quadrant).

The time-dependent slice is obtained from the datum by the **self-similar dilation** in the
physical variable.  With `b = λ̄(t)^{-1/p} > 0` one has, pointwise in `x`,

  `omegaS p g (b • x) = omegaSz p g (ρ(x)^p/λ̄(t)) x`,

because `ρ(b•x) = b·ρ(x)`, `θ(b•x) = θ(x)` and `e_θ(b•x) = e_θ(x)`
(`solVort_holder_rho_smul`/`_theta_smul`/`_eTheta_smul`): a positive dilation preserves the
azimuthal direction while rescaling the self-similar variable `z = ρ^p` by `b^p = λ̄(t)^{-1}`.
Dilation by `b` is `b`-Lipschitz, so composing the `α`-Hölder datum with it multiplies the Hölder
constant by `b^α`.

It remains to multiply by the scalar `λ̄(t)^{-1}` and by the radial cut-off factor
`χ(ρ(x)/L)`, which is bounded and Lipschitz; the product of a bounded Lipschitz function with a
bounded `α`-Hölder function (`0 < α ≤ 1`) is `α`-Hölder, which is
`Work.Stability.holder_smul_of_bounded_lipschitz` (`OmegaCutHolder.lean`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.ConstructionInstance.Reduced
import Submission.Work.ConstructionInstance.holder_omegaS_of_data
import Submission.Work.Stability.OmegaCutHolder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

/-! ## The cylindrical coordinates under a positive dilation -/

/-- `ρ` is positively homogeneous: `ρ(c • x) = c·ρ(x)` for `c ≥ 0`. -/
lemma solVort_holder_radial_smul {c : ℝ} (hc : 0 ≤ c) (x : R3) :
    Work.Cyl.radial (c • x) = c * Work.Cyl.radial x := by
  rw [Work.Cyl.radial, Work.Cyl.radial,
    show Work.Cyl.radSq (c • x) = c ^ 2 * Work.Cyl.radSq x by simp [Work.Cyl.radSq]; ring,
    Real.sqrt_mul (by positivity) (Work.Cyl.radSq x), Real.sqrt_sq_eq_abs, abs_of_nonneg hc]

/-- `ρ(c • x) = c·ρ(x)` for `c ≥ 0` (`ρ(x) = ‖x‖`). -/
lemma solVort_holder_rho_smul {c : ℝ} (hc : 0 ≤ c) (x : R3) :
    Work.Cyl.rho (c • x) = c * Work.Cyl.rho x := by
  rw [Work.Cyl.rho_eq_norm, Work.Cyl.rho_eq_norm, norm_smul, Real.norm_of_nonneg hc]

/-- The angular vector field is homogeneous: `angularVec (c • x) = c • angularVec x`. -/
lemma solVort_holder_angularVec_smul (c : ℝ) (x : R3) :
    Work.Cyl.angularVec (c • x) = c • Work.Cyl.angularVec x := by
  ext i; fin_cases i <;> simp [Work.Cyl.angularVec]

/-- The azimuthal angle is invariant under a positive dilation: `θ(c • x) = θ(x)`. -/
lemma solVort_holder_theta_smul {c : ℝ} (hc : 0 < c) (x : R3) :
    Work.Cyl.theta (c • x) = Work.Cyl.theta x := by
  rw [Work.Cyl.theta, Work.Cyl.theta]
  congr 1
  rw [show Work.Cyl.axial (c • x) = c * Work.Cyl.axial x by simp [Work.Cyl.axial],
    solVort_holder_radial_smul hc.le]
  field_simp

/-- The azimuthal frame vector is invariant under a positive dilation: `e_θ(c • x) = e_θ(x)`. -/
lemma solVort_holder_eTheta_smul {c : ℝ} (hc : 0 < c) (x : R3) :
    Work.Cyl.eTheta (c • x) = Work.Cyl.eTheta x := by
  rw [Work.Cyl.eTheta, Work.Cyl.eTheta, solVort_holder_radial_smul hc.le,
    solVort_holder_angularVec_smul, smul_smul]
  congr 1
  field_simp

/-! ## The spatial Hölder regularity of the slices -/

theorem solVort_holder {α : NNReal} (P : Work.ConstructionInstance.ProfileData α) :
    ∀ t ∈ Work.ConstructionInstance.preWindow P.T,
      Holder α (fun x => Work.ConstructionInstance.solVort P x t) := by
  intro t ht
  have hp : 0 < profExp α := profExp_pos P.hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith [P.hα13]
  have hα1 : α ≤ 1 := by
    rw [← NNReal.coe_le_coe]; push_cast; linarith [P.hα13]
  have hlt : 0 < P.lam t := P.hlam t ht
  -- the dilation factor `b = λ̄(t)^{-1/p}`
  obtain ⟨b, hb, hbp⟩ : ∃ b : ℝ, 0 < b ∧ b ^ (profExp α) = (P.lam t)⁻¹ := by
    refine ⟨(P.lam t)⁻¹ ^ (1 / profExp α),
      Real.rpow_pos_of_pos (inv_pos.mpr hlt) _, ?_⟩
    rw [← Real.rpow_mul (inv_nonneg.mpr hlt.le) (1 / profExp α) (profExp α),
      div_mul_cancel₀ 1 (ne_of_gt hp), Real.rpow_one]
  -- the dilations of the cylindrical coordinates
  have hz : ∀ x : R3, Work.Cyl.rho (b • x) ^ (profExp α)
      = Work.Cyl.rho x ^ (profExp α) / P.lam t := by
    intro x
    rw [solVort_holder_rho_smul hb.le, Real.mul_rpow hb.le (Work.Cyl.rho_nonneg x), hbp,
      div_eq_mul_inv, mul_comm ((P.lam t)⁻¹)]
  have hω : ∀ x : R3, omegaS (profExp α) P.g (b • x)
      = omegaSz (profExp α) P.g (Work.Cyl.rho x ^ profExp α / P.lam t) x := by
    intro x
    rw [omegaS_apply', omegaSz_apply, solVort_holder_theta_smul hb x,
      solVort_holder_eTheta_smul hb x, hz x]
  have hid : ∀ x : R3, solVort P x t
      = (P.lam t)⁻¹ •
          (Work.Stability.cutFactor P.L x • omegaS (profExp α) P.g (b • x)) := by
    intro x
    rw [solVort_apply, Work.Stability.cutFactor_apply, hω x]
  -- the datum is `α`-Hölder (`holder_omegaS_of_data`)
  have hS : Holder α (omegaS (profExp α) P.g) :=
    holder_omegaS_of_data P.hα P.hα13 P.hCv P.hLg P.hLθ
      P.hvt P.hquad0 P.hquad P.hvan P.hzk P.hzth (ContDiffOn.of_le P.hsmooth (by simp))
  -- composing with the `b`-Lipschitz dilation keeps `α`-Hölder (constant `C·b^α`)
  have hA : Holder α (fun x : R3 => omegaS (profExp α) P.g (b • x)) := by
    obtain ⟨C, hC⟩ := hS
    refine ⟨C * Real.toNNReal (b ^ (α : ℝ)), ?_⟩
    apply Work.Stability.holderWith_of_dist_le
    intro x y
    have h1 := hC.dist_le (b • x) (b • y)
    rw [dist_smul₀, Real.norm_of_nonneg hb.le, Real.mul_rpow hb.le dist_nonneg] at h1
    calc dist (omegaS (profExp α) P.g (b • x)) (omegaS (profExp α) P.g (b • y))
        ≤ (C : ℝ) * (b ^ (α : ℝ) * dist x y ^ (α : ℝ)) := h1
      _ = ((C * Real.toNNReal (b ^ (α : ℝ)) : NNReal) : ℝ) * dist x y ^ (α : ℝ) := by
          rw [NNReal.coe_mul, Real.coe_toNNReal (b ^ (α : ℝ)) (Real.rpow_nonneg hb.le _)]
          ring
  -- the dilated datum is bounded (the box of `Basic.omegaS_norm_le`)
  have hAb : IsBoundedFun
      (fun x : R3 => omegaS (profExp α) P.g (b • x)) := by
    refine Work.Stability.isBoundedFun_of_forall_norm_le
      (C := 20 * profExp α + P.Cg) (fun x => ?_)
    exact omegaS_norm_le hp hp1 (bdd_g P) P.hCg
      (fun θ hθ => by
        have hG : Gamma (profExp α / 3) θ ≤ 1 := Gamma_le_one (by positivity) hθ
        nlinarith [hG, hp.le, P.hCg]) (b • x)
  rw [funext hid]
  -- multiply by the bounded Lipschitz cut-off factor ...
  have hcut : Holder α (fun x : R3 =>
      Work.Stability.cutFactor P.L x • omegaS (profExp α) P.g (b • x)) := by
    obtain ⟨Kφ, hKφ⟩ := Work.Stability.cutFactor_lipschitz P.hL
    exact Work.Stability.holder_smul_of_bounded_lipschitz hα1
      (Work.Stability.cutFactor_bounded P.L) hKφ hAb hA
  -- ... and by the scalar `λ̄(t)^{-1}`
  obtain ⟨C2, hC2⟩ := hcut
  exact ⟨C2 * ‖(P.lam t)⁻¹‖₊, HolderWith.smul _ hC2⟩

end Work.ConstructionInstance
