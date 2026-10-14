import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.SolutionDelivery.DatumEuler
-- ===== merged: Submission.Work.FTS.RegPkgGal.ConsumerRegPkg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Metric
open scoped Topology NNReal Real

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false

variable {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}

/-- `|θ(x)| ∈ Iθ`. -/
lemma abs_theta_mem_Iθ (x : R3) : |Work.Cyl.theta x| ∈ Work.Spaces.Iθ := by
  refine ⟨abs_nonneg _, ?_⟩
  rw [Work.Cyl.theta]
  exact abs_le.mpr ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
    le_of_lt (Real.arctan_lt_pi_div_two _)⟩



/-! ## The conjunction shape of the composite transfer -/


/-! ## The vanishing-rate transfer -/

/-- `(r/ρ)^{2α} ≤ r^α` for `0 ≤ r ≤ ρ²` (copy of the `private` helper of
`Work.ConstructionInstance.gComp_abs_le`). -/
private lemma rpow_two_mul_le_of_le_sq {α r ρ : ℝ} (hα : 0 < α) (hr : 0 ≤ r) (hρ : 0 < ρ)
    (h : r ≤ ρ ^ 2) : (r / ρ) ^ (2 * α) ≤ r ^ α := by
  have hs0 : 0 ≤ r / ρ := div_nonneg hr hρ.le
  have hsρ : r / ρ ≤ ρ := by
    rw [div_le_iff₀ hρ]; nlinarith
  have h1 : (r / ρ) ^ α ≤ ρ ^ α := Real.rpow_le_rpow hs0 hsρ hα.le
  have h2 : (r / ρ) ^ (2 * α) = (r / ρ) ^ α * (r / ρ) ^ α := by
    rw [show 2 * α = α + α from by ring, Real.rpow_add' hs0 (by positivity)]
  rw [h2]
  calc (r / ρ) ^ α * (r / ρ) ^ α ≤ (r / ρ) ^ α * ρ ^ α :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hs0 α)
    _ = (r / ρ * ρ) ^ α := (Real.mul_rpow hs0 hρ.le).symm
    _ = r ^ α := by rw [div_mul_cancel₀ r hρ.ne']

/-- `ρ^{3α} ≤ r^α` for `0 < ρ ≤ 1` and `ρ² < r` (copy of the `private` helper of
`Work.ConstructionInstance.gComp_abs_le`). -/
private lemma rpow_three_mul_le_of_sq_lt {α r ρ : ℝ} (hα : 0 < α) (hr : 0 ≤ r) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (h : ρ ^ 2 < r) : ρ ^ (3 * α) ≤ r ^ α := by
  have h1 : ρ ^ (3 * α) ≤ ρ ^ (2 * α) :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by linarith)
  have h2 : ρ ^ (2 * α) = (ρ ^ 2) ^ α := by
    rw [Real.rpow_mul hρ.le (2:ℝ) α, Real.rpow_two]
  calc ρ ^ (3 * α) ≤ ρ ^ (2 * α) := h1
    _ = (ρ ^ 2) ^ α := h2
    _ ≤ r ^ α := Real.rpow_le_rpow (sq_nonneg ρ) h.le hα.le



/-! ## The uniform-in-`τ` consumers of `RegPkg'` -/



end Work.FTS.RegPkgGal
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R7d.chain_rule_along_curve =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R7d

open scoped Topology

/-- **The chain rule along the characteristic curve.**

Let `α s = (z s, θ s)` be a curve whose velocity is the (negated) transport velocity at the
*current* point and *current* fake time,

  `ż = -z · Vz(z,θ,τ)`,   `θ̇ = -Vθ(z,θ,τ)`   (with `τ = τ₀ - s`),

and suppose that `F` satisfies the transport equation along fake time at `(α t, τ₀ - t)`,

  `∂_τ F(α t, τ₀ - t) = -( Vz·D_z F + Vθ·∂_θ F + cs·F )`   (in `HasDerivAt` form),

with `F` differentiable at the point.  Then the composite `s ↦ F(α s, τ₀ - s)` —— the value of
`F` at the *point of the characteristic* at *fake time* `τ₀ - s` —— obeys the linear ODE

  `d/ds F(α s, τ₀ - s) = cs(α t, τ₀ - t) · F(α t, τ₀ - t)`   at `s = t`.

This is the chain-rule step of the support propagation (R7): the two transport terms cancel
against the equation, leaving the linear term `cs`.

The derivative of the composite is the Fréchet derivative of the uncurried `F` at
`(α t, τ₀ - t)` applied to the velocity `(-(α t).1·Vz, -Vθ, -1)`; its three coordinates are
computed by `Work.FTS.StrongGlobal.fderiv_uncurry3_apply`, the third one is then replaced by
the value supplied by the transport equation (`hEq.deriv`), and the remaining identity is
elementary arithmetic. -/
theorem chain_rule_along_curve {F : ℝ → ℝ → ℝ → ℝ} {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ}
    {α : ℝ → ℝ × ℝ} {τ₀ t : ℝ}
    (hFd : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2)
      ((α t).1, (α t).2, τ₀ - t))
    (hα : HasDerivAt α
      (-((α t).1 * Vz (α t).1 (α t).2 (τ₀ - t)), -(Vθ (α t).1 (α t).2 (τ₀ - t))) t)
    (hEq : HasDerivAt (fun s => F (α t).1 (α t).2 s)
      (-(Vz (α t).1 (α t).2 (τ₀ - t)
          * Work.Spaces.Dz (fun z θ => F z θ (τ₀ - t)) (α t).1 (α t).2
        + Vθ (α t).1 (α t).2 (τ₀ - t)
          * Work.Spaces.pth (fun z θ => F z θ (τ₀ - t)) (α t).1 (α t).2
        + cs (α t).1 (α t).2 (τ₀ - t) * F (α t).1 (α t).2 (τ₀ - t))) (τ₀ - t)) :
    HasDerivAt (fun s => F (α s).1 (α s).2 (τ₀ - s))
      (cs (α t).1 (α t).2 (τ₀ - t) * F (α t).1 (α t).2 (τ₀ - t)) t := by
  -- the fake time is traversed backwards, `s ↦ τ₀ - s`
  have hτ : HasDerivAt (fun s : ℝ => τ₀ - s) (0 - 1) t :=
    (hasDerivAt_const (c := τ₀) (x := t)).sub (hasDerivAt_id t)
  -- the velocity of the parameter curve `s ↦ (z(s), θ(s), τ₀ - s)`
  have hφ : HasDerivAt (fun s : ℝ => ((α s).1, ((α s).2, τ₀ - s)))
      (-((α t).1 * Vz (α t).1 (α t).2 (τ₀ - t)),
        (-(Vθ (α t).1 (α t).2 (τ₀ - t)), 0 - 1)) t :=
    hα.fst.prodMk (hα.snd.prodMk hτ)
  -- the chain rule: `s ↦ F(α s, τ₀ - s)` is the uncurried `F` composed with the parameter curve
  have hcomp := hFd.hasFDerivAt.comp_hasDerivAt t hφ
  -- the value of the derivative of the composite, in coordinates: `fderiv_uncurry3_apply` writes it
  -- as the linear combination of the three partials with the coefficients of the velocity, and the
  -- `τ`-partial is the value `hEq` supplies (`hEq.deriv`)
  have hval : (fderiv ℝ (Work.FTS.StrongGlobal.uncurry3 F) ((α t).1, (α t).2, τ₀ - t))
        (-((α t).1 * Vz (α t).1 (α t).2 (τ₀ - t)),
         (-(Vθ (α t).1 (α t).2 (τ₀ - t)), 0 - 1))
      = cs (α t).1 (α t).2 (τ₀ - t) * F (α t).1 (α t).2 (τ₀ - t) := by
    rw [Work.FTS.StrongGlobal.fderiv_uncurry3_apply hFd, hEq.deriv]
    simp only [Work.Spaces.Dz, Work.Spaces.pz, Work.Spaces.pth]
    ring
  -- `(uncurry3 F) ∘ φ` and `s ↦ F (α s).1 (α s).2 (τ₀ - s)` are the same function
  exact (hcomp.congr_deriv hval).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq rfl)

end Work.FTS.RegPkgGal.R7d
end
