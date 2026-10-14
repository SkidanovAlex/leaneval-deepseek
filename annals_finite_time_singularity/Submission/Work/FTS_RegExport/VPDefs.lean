import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.MinImports
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.FinalV2.Sanitize
import Submission.Work.FTS.GalFields.RHS.SharpAux.Defs
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.RegPkgGal.GalMinAssembly
import Submission.Work.FTS.RegPkgGal.GalMinConv
import Submission.Work.FTS.RegPkgGal.PartsAssembly
import Submission.Work.FTS.RegPkgGal.R5Parts
import Submission.Work.FTS.RegPkgGal.R7d.support_strip
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.RegPkgGal.St1Class
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_EllLimOK.SlotJets.slotPthSliceLe
import Submission.Work.FTS_FinalLeaves.mu6_proved
import Submission.Work.FTS_FinalLeaves.profDerivData_min_proved
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_RegExport.RX0.sup2_extG_ext_hIS
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXB.l12_zero_lim_proved
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_aux
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.omega_facts
import Submission.Work.FTS_RegExport.RXT.st1_fb_theta
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Stability.mul_rpow_le
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge
-- ===== merged: Submission.Work.FTS.GalFields.RHS.SharpAux.WlInfTermsBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.SharpAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000


end Work.FTS.GalFields.RHS.SharpAux
end
end
-- ===== merged: Submission.Work.FTS.GalFields.RHS.SharpMod.N_L12_WlInf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.SharpMod

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000


end Work.FTS.GalFields.RHS.SharpMod
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.Gf_le_defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Tonelli kernel of the `Gf` bound — definitions

This module fixes the vocabulary for the global bound on the radial density
`Gf α U z = w(z)² ∫₀¹ v^β M₁(zv) dv` (with `M₁ = mom U`, `β = beta α`).

The proof substitutes `t = zv` in the inner integral (`mom_subst`) and then applies Tonelli to the
product `(0,∞) × (0,∞)`, with the `t`-variable as the *outer* one.  The joint kernel of that
Tonelli step is naturally split into three factors:

* `GfPhi α U t = |t|^{β+4} A(t) / (1+t)^4`, with `A = mass α U` — the `t`-factor.  On `t > 0` it
  equals `t^β · M₁(t)` (`mass_eq_w2_mom` + `w_sq_mul_z4`), and it is nonnegative everywhere
  (the `|·|` is only there to make the nonnegativity global; for `t > 0` it is the plain power);
* `GfZeta α z = w(z)² |z|^{-(β+1)}` — the `z`-factor;
* `GfKer α U t z = 1_{t<z} · GfZeta α z · GfPhi α U t` — the joint kernel.

For `z > 0`, `z ↦ ∫ₜ GfKer α U t z` is exactly `Gf α U z`; for `t > 0`,
`t ↦ ∫_z GfKer α U t z ≤ A(t)/β`.  Both facts are the content of the pieces of the `Gf_le` proof.
-/
noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH

set_option autoImplicit false

/-- The `t`-factor `φ(t) = |t|^{β+4} A(t)/(1+t)^4` of the Tonelli kernel, where `A = mass α U`. -/
def GfPhi (α : ℝ) (U : ℝ → ℝ → ℝ) (t : ℝ) : ℝ :=
  |t| ^ (beta α + 4) * mass α U t / (1 + t) ^ 4

/-- The `z`-factor `ζ(z) = w(z)² |z|^{-(β+1)}` of the Tonelli kernel. -/
def GfZeta (α : ℝ) (z : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * |z| ^ (-(beta α + 1))

/-- The joint Tonelli kernel `1_{t<z} · ζ(z) · φ(t)`. -/
def GfKer (α : ℝ) (U : ℝ → ℝ → ℝ) (t z : ℝ) : ℝ :=
  (if t < z then 1 else 0) * GfZeta α z * GfPhi α U t

theorem GfPhi_nonneg (α : ℝ) (U : ℝ → ℝ → ℝ) (t : ℝ) : 0 ≤ GfPhi α U t := by
  have h1 : 0 ≤ |t| ^ (beta α + 4) := Real.rpow_nonneg (abs_nonneg t) _
  have h2 : 0 ≤ mass α U t := mass_nonneg α U t
  have h3 : 0 ≤ (1 + t) ^ 4 := by positivity
  unfold GfPhi
  exact div_nonneg (mul_nonneg h1 h2) h3

theorem GfZeta_nonneg (α : ℝ) (z : ℝ) : 0 ≤ GfZeta α z := by
  have h1 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ |z| ^ (-(beta α + 1)) := Real.rpow_nonneg (abs_nonneg z) _
  unfold GfZeta
  positivity

theorem GfKer_nonneg (α : ℝ) (U : ℝ → ℝ → ℝ) (t z : ℝ) : 0 ≤ GfKer α U t z := by
  have h1 : (0 : ℝ) ≤ (if t < z then 1 else 0) := by split <;> norm_num
  unfold GfKer
  exact mul_nonneg (mul_nonneg h1 (GfZeta_nonneg α z)) (GfPhi_nonneg α U t)

/-- On `t > 0` the `t`-factor is the plain power times the mass. -/
theorem GfPhi_eq_of_pos (α : ℝ) (U : ℝ → ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    GfPhi α U t = t ^ (beta α + 4) * mass α U t / (1 + t) ^ 4 := by
  unfold GfPhi
  rw [abs_of_pos ht]

/-- `β = 3/α - 1` is positive (indeed `≥ 2`) for `0 < α ≤ 1`. -/
theorem beta_pos {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : 0 < beta α := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hdiv : 3 ≤ 3 / α := by
    rw [le_div_iff₀ hα]; nlinarith
  unfold beta
  linarith

end Work.FTS_EllLimOK.ProducerH
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.kernel_le_small =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

set_option autoImplicit false

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Auxiliary facts for the small-`z` kernel bound -/

/-- `β + 4 = 3/α + 3 > 0` whenever `0 < α`. -/
theorem beta_add_four_pos {α : ℝ} (hα : 0 < α) : (0 : ℝ) < beta α + 4 := by
  have h : (0 : ℝ) < 3 / α := div_pos (by norm_num) hα
  rw [beta]
  linarith

/-- **Pointwise domination on the small-`z` range.**  For `0 < α` and `0 < t ≤ z`,
`t^β M₁(t) ≤ z^{β+4} A(t)`, where `M₁ = mom U` and `A = mass α U`.

Indeed `M₁(t) = A(t)/w(t)² ≤ t⁴A(t)` (`mom_le_mass_mul_z4`), so
`t^β M₁(t) ≤ t^{β+4}A(t)`, and `t^{β+4} ≤ z^{β+4}` since `β + 4 = 3/α + 3 > 0`. -/
theorem rpow_beta_mul_mom_le {α : ℝ} (hα : 0 < α) (U : ℝ → ℝ → ℝ) {z t : ℝ}
    (ht : 0 < t) (htz : t ≤ z) :
    t ^ (beta α) * mom U t ≤ z ^ (beta α + 4) * mass α U t := by
  have hβ4 : (0 : ℝ) < beta α + 4 := beta_add_four_pos hα
  have hβt : 0 ≤ t ^ (beta α) := Real.rpow_nonneg (le_of_lt ht) _
  have hmom : mom U t ≤ t ^ 4 * mass α U t := mom_le_mass_mul_z4 α U ht
  have hmassnn : 0 ≤ mass α U t := mass_nonneg α U t
  have hkey : t ^ (beta α) * (t ^ 4 * mass α U t) = t ^ (beta α + 4) * mass α U t := by
    rw [← Real.rpow_natCast t 4, ← mul_assoc, ← Real.rpow_add ht]
    norm_num
  have h3 : t ^ (beta α + 4) ≤ z ^ (beta α + 4) :=
    Real.rpow_le_rpow (le_of_lt ht) htz (le_of_lt hβ4)
  calc t ^ (beta α) * mom U t
      ≤ t ^ (beta α) * (t ^ 4 * mass α U t) := mul_le_mul_of_nonneg_left hmom hβt
    _ = t ^ (beta α + 4) * mass α U t := hkey
    _ ≤ z ^ (beta α + 4) * mass α U t := mul_le_mul_of_nonneg_right h3 hmassnn

/-- **The inner integral bound.**  For `0 < α`, `U ∈ ℋ⁰` and `0 < z`,
`∫₀^z t^β M₁(t) dt ≤ z^{β+4} · HkSq α 0 U`.

The integrand is dominated on `(0,z]` by `z^{β+4}A(t)` (previous lemma), and
`∫_{(0,z)} A ≤ ∫_{(0,∞)} A = HkSq α 0 U` by monotonicity of the integral in the domain
(`setIntegral_mono_set`) and `mass_Ioi_eq_HkSq`. -/
theorem integral_rpow_mom_le {α : ℝ} (hα : 0 < α) {U : ℝ → ℝ → ℝ}
    (hU : Work.Spaces.HkMem α 0 U) {z : ℝ} (h1 : 0 < z) :
    (∫ t in (0 : ℝ)..z, t ^ (beta α) * mom U t)
      ≤ z ^ (beta α + 4) * Work.Spaces.HkSq α 0 U := by
  have hle : (0 : ℝ) ≤ z := le_of_lt h1
  have hmassIoc : IntegrableOn (mass α U) (Set.Ioc (0 : ℝ) z) :=
    (mass_integrableOn α U hU).mono_set Set.Ioc_subset_Ioi_self
  have hgint : Integrable (fun t => z ^ (beta α + 4) * mass α U t)
      (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    hmassIoc.const_mul _
  have hfnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) z)]
      (fun t => t ^ (beta α) * mom U t) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt ht.1) _) (mom_nonneg U t)
  have hleae : (fun t => t ^ (beta α) * mom U t) ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) z)]
      (fun t => z ^ (beta α + 4) * mass α U t) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun t ht =>
      rpow_beta_mul_mom_le hα U ht.1 ht.2
  have hmono := MeasureTheory.integral_mono_of_nonneg hfnn hgint hleae
  have hmono_set :
      (∫ t in Set.Ioc (0 : ℝ) z, mass α U t) ≤ ∫ t in Set.Ioi (0 : ℝ), mass α U t :=
    MeasureTheory.setIntegral_mono_set (mass_integrableOn α U hU)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => mass_nonneg α U t)
      (Filter.Eventually.of_forall fun t ht => ht.1)
  have hzpow : 0 ≤ z ^ (beta α + 4) := Real.rpow_nonneg hle _
  calc (∫ t in (0 : ℝ)..z, t ^ (beta α) * mom U t)
      = ∫ t in Set.Ioc (0 : ℝ) z, t ^ (beta α) * mom U t :=
        intervalIntegral.integral_of_le hle
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) z, z ^ (beta α + 4) * mass α U t := hmono
    _ = z ^ (beta α + 4) * ∫ t in Set.Ioc (0 : ℝ) z, mass α U t :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ z ^ (beta α + 4) * ∫ t in Set.Ioi (0 : ℝ), mass α U t :=
        mul_le_mul_of_nonneg_left hmono_set hzpow
    _ = z ^ (beta α + 4) * Work.Spaces.HkSq α 0 U := by rw [mass_Ioi_eq_HkSq]

/-! ## The target -/

/-- **Small-`z` bound for the kernel integral.**  For `0 < α`, `U ∈ ℋ⁰` and `0 < z`:
`∫₀¹ v^β M₁(zv) dv ≤ z³ · HkSq α 0 U` (`β = 3/α - 1`, `M₁ = mom U`).

Route: `mom_subst` turns the left side into `z^{-(β+1)}∫₀^z t^β M₁(t) dt`; the pointwise
`M₁(t) = A(t)/w(t)² ≤ t⁴A(t)` for `t > 0` (`mom_le_mass_mul_z4` in pointwise form,
`mass_eq_w2_mom`, where `A = mass α U`) gives `t^β M₁(t) ≤ t^{β+4}A(t) ≤ z^{β+4}A(t)` for
`0 < t ≤ z` (as `β + 4 = 3/α + 3 > 0`), so the inner integral is
`≤ z^{β+4}∫_{(0,z)} A ≤ z^{β+4} HkSq α 0 U` (`setIntegral_mono_set` against
`mass_Ioi_eq_HkSq`, `mass_integrableOn`), and `z^{-(β+1)}·z^{β+4} = z³`. -/
theorem kernel_le_small {α : ℝ} (hα : 0 < α) {U : ℝ → ℝ → ℝ}
    (hU : Work.Spaces.HkMem α 0 U) {z : ℝ} (h1 : 0 < z) :
    (∫ v in (0 : ℝ)..1, v ^ (Work.FTS_EllLimOK.ProducerH.beta α)
        * Work.FTS_EllLimOK.ProducerH.mom U (z * v))
      ≤ z ^ 3 * Work.Spaces.HkSq α 0 U := by
  have hpow : 0 < z ^ (-(beta α + 1)) := Real.rpow_pos_of_pos h1 _
  rw [mom_subst α U h1]
  calc z ^ (-(beta α + 1)) * (∫ t in (0 : ℝ)..z, t ^ (beta α) * mom U t)
      ≤ z ^ (-(beta α + 1)) * (z ^ (beta α + 4) * Work.Spaces.HkSq α 0 U) :=
        mul_le_mul_of_nonneg_left (integral_rpow_mom_le hα hU h1) (le_of_lt hpow)
    _ = z ^ 3 * Work.Spaces.HkSq α 0 U := by
        rw [← mul_assoc, ← Real.rpow_add h1]
        norm_num

end Work.FTS_EllLimOK.ProducerH
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.psiP_pointwise_cs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Pointwise Cauchy–Schwarz bound for the `psiP` representation

This file proves `psiP_pointwise_cs`: on the open quadrant `Qd = (0,∞) × (0,π/2)`, where
`Φ = psiP α Φ` and `|U'| ≤ M` for `U' = Uprime α Φ`, the quotient `Φ/cos θ` satisfies

`(Φ z θ / cos θ)² ≤ (4/(3α)) ∫₀¹ v^{3/α-1} U'(zv,θ)² dv`.

The proof is the classical Cauchy–Schwarz argument.  In `v`, the representation
`psiP α Φ z θ = -(sin 2θ/α) ∫₀¹ v^{3/α-1} U'(zv,θ) dv` (the fixed point hypothesis) gives
`Φ z θ / cos θ = -(2 sin θ/α) ∫₀¹ v^{3/α-1} U'(zv,θ) dv`; Cauchy–Schwarz in `v`
(`Work.FTS_EllLimOK.ProducerH.cs_rpow_bounded`) gives
`(∫₀¹ v^β U')² ≤ (∫₀¹ v^β)(∫₀¹ v^β U'²) = (α/3) ∫₀¹ v^β U'²` for `β = 3/α - 1`
(`integral_rpow_zero_one`), and `sin²θ ≤ 1` gives the constant `4/(3α)`. -/

namespace Work.FTS_EllLimOK.ProducerH

set_option autoImplicit false

/-- **Pointwise Cauchy–Schwarz bound for the `psiP` representation.**
On the open quadrant, where `Φ = psiP α Φ`, and with `|U'| ≤ M` (`U' = Uprime α Φ`), the quotient
`Φ/cos θ` satisfies `(Φ z θ/cos θ)² ≤ (4/(3α)) ∫₀¹ v^{3/α-1} U'(zv,θ)² dv`.

Route: `Φ z θ = -(sin 2θ/α) ∫₀¹ v^β U'(zv,θ) dv` (the fixed-point hypothesis + the definition of
`psiP`), so `Φ/cos θ = -(2 sin θ/α) ∫₀¹ v^β U'(zv,θ) dv` (as `cos θ ≠ 0` on the quadrant);
Cauchy–Schwarz in `v` on `(0,1)` (Hölder with `p = q = 2`) gives
`(∫₀¹ v^β U')² ≤ (∫₀¹ v^β)(∫₀¹ v^β U'²) = (1/(β+1)) ∫₀¹ v^β U'² = (α/3)∫₀¹ v^β U'²` for
`β = 3/α - 1` (`integral_rpow`), and `sin²θ ≤ 1`. -/
theorem psiP_pointwise_cs {α : ℝ} (hα : 0 < α) {Φ : ℝ → ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hpsi : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Φ z θ = Work.FTS.StreamBdryIface.psiP α Φ z θ)
    (hbnd : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.FTS.StreamBdryIface.Uprime α Φ z θ| ≤ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      (Φ z θ / Real.cos θ) ^ 2
        ≤ (4 / (3 * α)) * ∫ v in (0 : ℝ)..1,
            v ^ (Work.FTS_EllLimOK.ProducerH.beta α)
              * (Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ) ^ 2 := by
  intro z θ hzθ
  -- unfold the quadrant, then the fixed point and the definition of `psiP`
  have hzθ' : (z, θ) ∈ Work.Construction.Qd := hzθ
  simp only [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hzθ'
  obtain ⟨hz, hθ0, hθ1⟩ := hzθ'
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  have hQd : ∀ w : ℝ, 0 < w → (w, θ) ∈ Work.Construction.Qd := by
    intro w hw
    simp only [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
    exact ⟨hw, hθ0, hθ1⟩
  have hΦ : Φ z θ = -(Work.Construction.s2 θ / α) *
      ∫ v in (0:ℝ)..1, v ^ beta α * Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ := by
    rw [hpsi z θ (hQd z hz)]
    rfl
  set I : ℝ := ∫ v in (0:ℝ)..1, v ^ beta α *
    Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ with hI
  set J : ℝ := ∫ v in (0:ℝ)..1, v ^ beta α *
    (Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ)^2 with hJ
  -- `Φ / cos θ = -(2 sin θ / α) · I`
  have hquot : Φ z θ / Real.cos θ = -(2 * Real.sin θ / α) * I := by
    rw [hΦ, Work.Construction.s2_eq, Real.sin_two_mul]
    field_simp
  have hsq : (Φ z θ / Real.cos θ)^2 = (4 * (Real.sin θ)^2 / α^2) * I^2 := by
    rw [hquot]; ring
  -- Cauchy–Schwarz in `v`
  have hβ : -1 < beta α := by
    rw [beta]
    have : 0 < 3 / α := by positivity
    linarith
  have ha : ∀ v, v ∈ Set.Ioc (0:ℝ) 1 →
      |Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ| ≤ M := by
    intro v hv
    exact hbnd (z * v) θ (hQd (z*v) (mul_pos hz hv.1))
  have hcs : I^2 ≤ (∫ v in (0:ℝ)..1, v ^ beta α) * J := by
    rw [hI, hJ]
    exact cs_rpow_bounded hβ hM ha
  have hInt : ∫ v in (0:ℝ)..1, v ^ beta α = α / 3 := by
    rw [integral_rpow_zero_one hβ]
    have h3 : beta α + 1 = 3 / α := by rw [beta]; ring
    rw [h3, one_div_div]
  -- assemble the arithmetic
  calc (Φ z θ / Real.cos θ)^2
      = (4 * (Real.sin θ)^2 / α^2) * I^2 := hsq
    _ ≤ (4 / α^2) * I^2 := by
        have h1 : 4 * Real.sin θ ^ 2 ≤ 4 := by nlinarith [Real.sin_sq_le_one θ]
        have h2 : 4 * Real.sin θ ^ 2 / α^2 ≤ 4 / α^2 := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
        exact mul_le_mul_of_nonneg_right h2 (sq_nonneg I)
    _ ≤ (4 / α^2) * ((α/3) * J) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 4/α^2)
        rw [← hInt]
        exact hcs
    _ = (4 / (3 * α)) * J := by
        rw [← mul_assoc]
        congr 1
        field_simp

end Work.FTS_EllLimOK.ProducerH
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.slice_le_Gf =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The auxiliary integrand of the slice estimate

Everything below is infrastructure for `slice_le_Gf`.  The integrand

  `slgH α z U θ v = sin(2θ)^{-η} · v^β · U(z v, θ)²`

is the (curried) integrand of the product integral over `Iθ × (0,1)` whose two iterated forms
are compared by Tonelli/Fubini in the main proof. -/

/-- The product integrand `σ θ · v^β · U(z v, θ)²` of the slice estimate. -/
noncomputable def slgH (α z : ℝ) (U : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun θ v => Work.FTS.EllipticEst.AngSecond.sig θ * (v ^ (beta α) * (U (z * v) θ) ^ 2)

/-- The angular weight `θ ↦ sin(2θ)^{-η}` is continuous on the open interval `(0,π/2)`. -/
theorem slg_sig_continuousOn :
    ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (π/2)) := by
  unfold Work.FTS.EllipticEst.AngSecond.sig
  refine ContinuousOn.rpow_const
    (Real.continuous_sin.comp_continuousOn
      (continuous_const.mul continuous_id).continuousOn) ?_
  intro θ hθ
  exact Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])))

/-- Continuity on an open box upgrades to a.e. strong measurability for the product of the two
one-dimensional Lebesgue measures restricted to the closed/half-open boxes.  (The closed box and
the open box differ by a null set.) -/
theorem slg_aesm_prod_box {g : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hg : ContinuousOn g (Set.Ioo a b ×ˢ Set.Ioo c d)) :
    AEStronglyMeasurable g
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Ioc c d))) := by
  have h1 : Set.Icc a b =ᵐ[volume] Set.Ioo a b := MeasureTheory.Ioo_ae_eq_Icc.symm
  have h2 : Set.Ioc c d =ᵐ[volume] Set.Ioo c d := MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hprod : (Set.Icc a b ×ˢ Set.Ioc c d : Set (ℝ × ℝ)) =ᵐ[volume.prod volume]
      (Set.Ioo a b ×ˢ Set.Ioo c d) := MeasureTheory.Measure.set_prod_ae_eq h1 h2
  have hmain : AEStronglyMeasurable g
      ((volume.prod volume).restrict (Set.Ioo a b ×ˢ Set.Ioo c d)) :=
    hg.aestronglyMeasurable (isOpen_Ioo.prod isOpen_Ioo).measurableSet
  rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set hprod]
  exact hmain

/-- The `U`-slot `U' = Uprime α Φ` is continuous on the open quadrant as soon as `Φ` is `C^∞`
there: `U' = (-3Φ - α z ∂_zΦ)/sin(2θ)` is a quotient of two continuous functions whose
denominator does not vanish. -/
theorem slg_Uprime_continuousOn {α : ℝ} {Φ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Φ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.StreamBdryIface.Uprime α Φ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have hnum : ContinuousOn
      (fun p : ℝ × ℝ => -3 * Φ p.1 p.2 - α * p.1 * Work.Spaces.pz Φ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
    refine ContinuousOn.sub ?_ ?_
    · exact (continuousOn_const.mul hsm.continuousOn)
    · exact (continuousOn_const.mul continuousOn_fst).mul hsm.pz.continuousOn
  have hden : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp_continuousOn
      ((continuous_const.mul continuous_snd).continuousOn))
  refine hnum.div hden ?_
  intro p hp
  have hp2 : p.2 ∈ Set.Ioo (0:ℝ) (π/2) := hp.2
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp2.1])
    (by linarith [hp2.2, Real.pi_pos]))

/-- The product integrand `slgH α z U` is continuous on the open box `(0,π/2) × (0,1)` whenever
`U` is continuous on the open quadrant and `z > 0` (so that `(zv, θ)` stays in the quadrant). -/
theorem slg_slgH_continuousOn {α : ℝ} {U : ℝ → ℝ → ℝ}
    (hU : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) Work.FTS.EllipticEst.Q0)
    {z : ℝ} (hz : 0 < z) :
    ContinuousOn (fun p : ℝ × ℝ => slgH α z U p.1 p.2)
      (Set.Ioo 0 (π/2) ×ˢ Set.Ioo 0 1) := by
  have hsig : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AngSecond.sig p.1)
      (Set.Ioo 0 (π/2) ×ˢ Set.Ioo 0 1) :=
    slg_sig_continuousOn.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hvp : ContinuousOn (fun p : ℝ × ℝ => p.2 ^ (beta α))
      (Set.Ioo 0 (π/2) ×ˢ Set.Ioo 0 1) :=
    ContinuousOn.rpow_const continuous_snd.continuousOn
      (fun p hp => Or.inl (ne_of_gt hp.2.1))
  have hUp : ContinuousOn (fun p : ℝ × ℝ => U (z * p.2) p.1)
      (Set.Ioo 0 (π/2) ×ˢ Set.Ioo 0 1) :=
    hU.comp ((continuous_const.mul continuous_snd).prodMk continuous_fst).continuousOn
      (fun p hp => ⟨mul_pos hz hp.2.1, hp.1.1, hp.1.2⟩)
  exact hsig.mul (hvp.mul (hUp.pow 2))

/-- **The `ℋ⁰`-slice of `Φ/cos θ` is dominated by `Gf`.**  Let `α > 0`, `Φ` smooth on the open
quadrant (`SmoothOpen Φ`), `U' = Uprime α Φ` bounded by `M ≥ 0` on the quadrant, and suppose the
pointwise Cauchy–Schwarz bound `(Φ z θ/cos θ)² ≤ (4/(3α))∫₀¹ v^β U'(zv,θ)² dv` holds on the open
quadrant (`hpt`; it is the conclusion of `psiP_pointwise_cs`).  Then for every `z > 0`

  `∫_θ HkIntegrand α 0 (Φ/cos θ) z θ ≤ (4/(3α)) · Gf α U' z`,

where `Gf α U' z = w(z)² ∫₀¹ v^β M₁(zv) dv` and `M₁(z) = ∫_θ U'(z,θ)² sin(2θ)^{-η}`.

Route: at level `0` the integrand is `w(z)² · ((Φ z θ/cos θ)² · σ θ)` with `σ = sin(2θ)^{-η}`
(`HkIntegrand_eq_w2_sig`), so it suffices to bound
`∫_θ (Φ/cos θ)²σ ≤ (4/(3α))∫_θ (∫₀¹ v^β U'(zv,θ)²dv) σ dθ` (monotonicity of the `θ`-integral and
`hpt` a.e. on `Iθ`), and then to interchange the two integrals (`Fubini` on the *finite* measure
spaces `Iθ × (0,1)`, e.g. `Work.FTS.H2.swap_iterated_integral_of_nonneg`, whose four hypotheses
are: nonnegativity, joint a.e. strong measurability (uses `SmoothOpen Φ`: `U'` is continuous on
the open quadrant, and `θ ↦ σ θ` is Borel), a.e. `v`-integrability (dominated by
`M²v^βσ`), and `θ`-integrability of the partially integrated function (dominated by
`M²σθ/(β+1)`, `σ ∈ L¹(Iθ)`)) giving `∫_θ∫_v = ∫_v∫_θ = ∫₀¹ v^β M₁(zv) dv`. -/
theorem slice_le_Gf {α : ℝ} (hα : 0 < α) {Φ : ℝ → ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Φ)
    (hbnd : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.FTS.StreamBdryIface.Uprime α Φ z θ| ≤ M)
    (hpt : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      (Φ z θ / Real.cos θ) ^ 2
        ≤ (4 / (3 * α)) * ∫ v in (0 : ℝ)..1,
            v ^ (Work.FTS_EllLimOK.ProducerH.beta α)
              * (Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ) ^ 2) :
    ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
        ≤ (4 / (3 * α))
            * Work.FTS_EllLimOK.ProducerH.Gf α (Work.FTS.StreamBdryIface.Uprime α Φ) z := by
  intro z hz
  -- `U'` is continuous on the open quadrant, hence so is the product integrand.
  have hUc : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.StreamBdryIface.Uprime α Φ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := slg_Uprime_continuousOn hsm
  have hcont_h : ContinuousOn
      (fun p : ℝ × ℝ => slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) p.1 p.2)
      (Set.Ioo 0 (π/2) ×ˢ Set.Ioo 0 1) := slg_slgH_continuousOn hUc hz
  have haesm_h : AEStronglyMeasurable
      (fun p : ℝ × ℝ => slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) p.1 p.2)
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) :=
    slg_aesm_prod_box hcont_h
  -- `σ` and `v ↦ v^β` are integrable on the two (finite) measure spaces.
  have hsigI : Integrable (fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.sig θ)
      (volume.restrict Work.Spaces.Iθ) := by
    have hp1 : (-1:ℝ) < -(Work.Spaces.eta) := by norm_num [Work.Spaces.eta]
    have hp2 : -(Work.Spaces.eta) ≤ 0 := by norm_num [Work.Spaces.eta]
    exact (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) hp1 hp2).1
  have hvI : Integrable (fun v : ℝ => v ^ (beta α)) (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    have hb : (-1:ℝ) < beta α := by
      rw [beta]; have : (0:ℝ) < 3/α := div_pos (by norm_num) hα; linarith
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (intervalIntegral.intervalIntegrable_rpow' hb)
  have hdom_int : Integrable
      (fun p : ℝ × ℝ => M^2 * (Work.FTS.EllipticEst.AngSecond.sig p.1 * p.2 ^ (beta α)))
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) :=
    (hsigI.mul_prod hvI).const_mul (M^2)
  -- a.e. facts on the product: the angle is in the open interval and `v` is positive.
  have haeθ : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0:ℝ) (π/2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0:ℝ)) (b := π/2)] with θ h
    exact fun hmem => h.mpr hmem
  have haev : ∀ᵐ v ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), v ∈ Set.Ioo (0:ℝ) 1 := by
    rw [MeasureTheory.ae_restrict_iff' (s := Set.Ioc (0:ℝ) 1) measurableSet_Ioc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Ioc (μ := volume) (a := (0:ℝ)) (b := 1)] with v h
    exact fun hmem => h.mpr hmem
  have hae_open : ∀ᵐ p ∂((volume.restrict Work.Spaces.Iθ).prod
      (volume.restrict (Set.Ioc (0:ℝ) 1))),
      p.1 ∈ Set.Ioo (0:ℝ) (π/2) ∧ p.2 ∈ Set.Ioo (0:ℝ) 1 := by
    refine (Measure.ae_prod_iff_ae_ae (μ := volume.restrict Work.Spaces.Iθ)
      (ν := volume.restrict (Set.Ioc (0:ℝ) 1))
      (p := fun z : ℝ × ℝ => z.1 ∈ Set.Ioo (0:ℝ) (π/2) ∧ z.2 ∈ Set.Ioo (0:ℝ) 1) ?_).mpr ?_
    · exact measurableSet_Ioo.prod measurableSet_Ioo
    · filter_upwards [haeθ] with θ hθ
      filter_upwards [haev] with v hv
      exact ⟨hθ, hv⟩
  -- the pointwise domination on the product
  have hdom_ae : ∀ᵐ p ∂((volume.restrict Work.Spaces.Iθ).prod
      (volume.restrict (Set.Ioc (0:ℝ) 1))),
      ‖slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) p.1 p.2‖
        ≤ M^2 * (Work.FTS.EllipticEst.AngSecond.sig p.1 * p.2 ^ (beta α)) := by
    filter_upwards [hae_open] with p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hzv : 0 < z * p.2 := mul_pos hz hp2.1
    have hb : |Work.FTS.StreamBdryIface.Uprime α Φ (z * p.2) p.1| ≤ M :=
      hbnd (z * p.2) p.1 ⟨hzv, hp1.1, hp1.2⟩
    have hsq : (Work.FTS.StreamBdryIface.Uprime α Φ (z * p.2) p.1)^2 ≤ M^2 := by
      nlinarith [abs_nonneg (Work.FTS.StreamBdryIface.Uprime α Φ (z * p.2) p.1),
        sq_abs (Work.FTS.StreamBdryIface.Uprime α Φ (z * p.2) p.1), hM]
    have hsnn : 0 ≤ Work.FTS.EllipticEst.AngSecond.sig p.1 :=
      Work.FTS.EllipticEst.AngSecond.sig_nonneg ⟨le_of_lt hp1.1, le_of_lt hp1.2⟩
    have hvnn : 0 ≤ p.2 ^ (beta α) := Real.rpow_nonneg (le_of_lt hp2.1) _
    have hnn : 0 ≤ slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) p.1 p.2 := by
      simp only [slgH]
      exact mul_nonneg hsnn (mul_nonneg hvnn (sq_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) p.1 p.2
        = Work.FTS.EllipticEst.AngSecond.sig p.1 * (p.2 ^ (beta α)
            * (Work.FTS.StreamBdryIface.Uprime α Φ (z * p.2) p.1)^2) := by simp only [slgH]
      _ ≤ Work.FTS.EllipticEst.AngSecond.sig p.1 * (p.2 ^ (beta α) * M^2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hvnn) hsnn
      _ = M^2 * (Work.FTS.EllipticEst.AngSecond.sig p.1 * p.2 ^ (beta α)) := by ring
  -- integrability of the product integrand
  have hInt : Integrable
      (fun p : ℝ × ℝ => slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) p.1 p.2)
      ((volume.restrict Work.Spaces.Iθ).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) :=
    Integrable.mono' hdom_int haesm_h hdom_ae
  -- Tonelli/Fubini on the product of the two *finite* measure spaces
  have hFub := integral_integral_swap (μ := volume.restrict Work.Spaces.Iθ)
    (ν := volume.restrict (Set.Ioc (0:ℝ) 1))
    (f := slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ)) hInt
  -- the angular slice is `v^β · M₁(zv)`
  have hθcongr : ∀ v : ℝ,
      (∫ θ, slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) θ v
          ∂(volume.restrict Work.Spaces.Iθ))
        = v ^ (beta α) * mom (Work.FTS.StreamBdryIface.Uprime α Φ) (z * v) := by
    intro v
    have hcongr : (∫ θ, slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) θ v
        ∂(volume.restrict Work.Spaces.Iθ))
        = ∫ θ, v ^ (beta α)
            * ((Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ)^2
              * Work.FTS.EllipticEst.AngSecond.sig θ)
            ∂(volume.restrict Work.Spaces.Iθ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [slgH]
      ring
    rw [hcongr, MeasureTheory.integral_const_mul]
    rfl
  -- monotonicity of the angular integral against the pointwise bound `hpt`
  have hnn_f : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      fun θ => (Φ z θ / Real.cos θ)^2 * Work.FTS.EllipticEst.AngSecond.sig θ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ))
  have hjeq : ∀ θ : ℝ,
      (∫ v, slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) θ v
          ∂(volume.restrict (Set.Ioc (0:ℝ) 1)))
        = Work.FTS.EllipticEst.AngSecond.sig θ
          * (∫ v in (0:ℝ)..1,
              v ^ (beta α) * (Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ)^2) := by
    intro θ
    rw [show (∫ v in (0:ℝ)..1,
          v ^ (beta α) * (Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ)^2)
        = ∫ v, v ^ (beta α) * (Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ)^2
            ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) from
        intervalIntegral.integral_of_le (by norm_num)]
    exact MeasureTheory.integral_const_mul _ _
  have hle : (fun θ => (Φ z θ / Real.cos θ)^2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (4/(3*α)) * ∫ v, slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) θ v
          ∂(volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    filter_upwards [haeθ] with θ hθ
    have hp := hpt z θ ⟨hz, hθ.1, hθ.2⟩
    have hsnn := Work.FTS.EllipticEst.AngSecond.sig_nonneg
      ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [hjeq θ]
    calc (Φ z θ / Real.cos θ)^2 * Work.FTS.EllipticEst.AngSecond.sig θ
        ≤ ((4/(3*α)) * (∫ v in (0:ℝ)..1,
            v ^ (beta α) * (Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ)^2))
          * Work.FTS.EllipticEst.AngSecond.sig θ :=
          mul_le_mul_of_nonneg_right hp hsnn
      _ = (4/(3*α)) * (Work.FTS.EllipticEst.AngSecond.sig θ
            * (∫ v in (0:ℝ)..1,
              v ^ (beta α) * (Work.FTS.StreamBdryIface.Uprime α Φ (z * v) θ)^2)) := by ring
  have hj_int : Integrable
      (fun θ => ∫ v, slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) θ v
        ∂(volume.restrict (Set.Ioc (0:ℝ) 1))) (volume.restrict Work.Spaces.Iθ) :=
    hInt.integral_prod_left
  have hmono := MeasureTheory.integral_mono_of_nonneg hnn_f (hj_int.const_mul (4/(3*α))) hle
  -- level `0`: `HkIntegrand α 0 U z θ = w(z)² (U z θ)² σ θ` on `Iθ`
  have hstepA : (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
      = (Work.Spaces.w z)^2 * ∫ θ in Work.Spaces.Iθ,
          (Φ z θ / Real.cos θ)^2 * Work.FTS.EllipticEst.AngSecond.sig θ := by
    simp only [Work.Spaces.Iθ]
    have hcongr : ∀ θ ∈ Set.Icc (0:ℝ) (π/2),
        Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ
          = (Work.Spaces.w z)^2 * ((Φ z θ / Real.cos θ)^2
              * Work.FTS.EllipticEst.AngSecond.sig θ) := by
      intro θ hθ
      simpa using HkIntegrand_eq_w2_sig α (fun z θ => Φ z θ / Real.cos θ) hθ
    rw [setIntegral_congr_fun measurableSet_Icc hcongr]
    exact MeasureTheory.integral_const_mul _ _
  -- the swapped iterated integral is the inner `v`-integral of `Gf`
  have hswapmain : (∫ θ in Work.Spaces.Iθ,
        ∫ v, slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) θ v
          ∂(volume.restrict (Set.Ioc (0:ℝ) 1)))
      = ∫ v in (0:ℝ)..1,
          v ^ (beta α) * mom (Work.FTS.StreamBdryIface.Uprime α Φ) (z * v) := by
    rw [hFub]
    rw [show (∫ v, ∫ θ, slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) θ v
            ∂(volume.restrict Work.Spaces.Iθ) ∂(volume.restrict (Set.Ioc (0:ℝ) 1)))
        = ∫ v, v ^ (beta α) * mom (Work.FTS.StreamBdryIface.Uprime α Φ) (z * v)
            ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) from
        integral_congr_ae (Filter.Eventually.of_forall (fun v => hθcongr v))]
    exact (intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)).symm
  calc (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => Φ z θ / Real.cos θ) z θ)
      = (Work.Spaces.w z)^2 * ∫ θ in Work.Spaces.Iθ,
          (Φ z θ / Real.cos θ)^2 * Work.FTS.EllipticEst.AngSecond.sig θ := hstepA
    _ ≤ (Work.Spaces.w z)^2 * ∫ θ in Work.Spaces.Iθ,
          (4/(3*α)) * ∫ v, slgH α z (Work.FTS.StreamBdryIface.Uprime α Φ) θ v
            ∂(volume.restrict (Set.Ioc (0:ℝ) 1)) :=
        mul_le_mul_of_nonneg_left hmono (sq_nonneg _)
    _ = (Work.Spaces.w z)^2 * ((4/(3*α)) * ∫ v in (0:ℝ)..1,
          v ^ (beta α) * mom (Work.FTS.StreamBdryIface.Uprime α Φ) (z * v)) := by
        rw [MeasureTheory.integral_const_mul, hswapmain]
    _ = (4 / (3 * α)) * Gf α (Work.FTS.StreamBdryIface.Uprime α Φ) z := by
        simp only [Gf]
        ring

end Work.FTS_EllLimOK.ProducerH
end
-- ===== merged: Submission.Work.FTS_FinalLeaves.All =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
end
-- ===== merged: Submission.Work.FTS_RegExport.RX0.MainRecut =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS_RegExport.RX0

open Work.FTS.Regularity
open Work.FTS.RegPkgGal (extG extG_of_pos extG_of_nonpos)
open Work.FTS.RegPkgGal

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The right-hand side of the fake-time equation, as a `Fam` (copy of the abbreviation of
`GalMinConv`, which is not exported under a usable name). -/
abbrev rhsFam' (α : ℝ) (g Φ : Fam) : Fam :=
  fun z θ τ => Work.FTS.Galerkin.dynLin (pExp α) g τ z θ
    + Work.FTS.Galerkin.dynRHS (pExp α) Φ g τ z θ

private lemma Gam_zero_at_rx0 (α : ℝ) (hα : 0 < α) : Work.Spaces.Gam α 0 = 0 := by
  have h : (Real.sin (0 : ℝ) * Real.cos (0 : ℝ) ^ 2) = 0 := by
    rw [Real.sin_zero, Real.cos_zero]; ring
  rw [Work.Spaces.Gam, h, Real.zero_rpow (by positivity : α / 3 ≠ 0)]

private lemma Gam_zero_pi_rx0 (α : ℝ) (hα : 0 < α) : Work.Spaces.Gam α (π / 2) = 0 := by
  have h : (Real.sin (π / 2) * Real.cos (π / 2) ^ 2) = 0 := by
    rw [Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  rw [Work.Spaces.Gam, h, Real.zero_rpow (by positivity : α / 3 ≠ 0)]

private lemma Fstar_zero_left_rx0 (α : ℝ) (hα : 0 < α) (z : ℝ) :
    Work.Construction.Fstar α z 0 = 0 := by
  rw [Work.Construction.Fstar, Gam_zero_at_rx0 α hα, zero_div]
  ring

private lemma Fstar_zero_pi_rx0 (α : ℝ) (hα : 0 < α) (z : ℝ) :
    Work.Construction.Fstar α z (π / 2) = 0 := by
  rw [Work.Construction.Fstar, Gam_zero_pi_rx0 α hα, zero_div]
  ring

/-- **THE RE-CUT REDUCTION.**  `GalMinConv.galHyp_of_galMin` with `GalMin` replaced by
`GalMin'` (i.e. `hRQ` replaced by `hIS`). -/
theorem galHyp_of_galMin' {α S : ℝ} {g Φ : Fam} {m : ℝ → ℝ} {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ}
    {a b c Lz7 N0 : ℝ} (H : Work.FTS.RegExportIface.GalMin' α S g m Vz Vθ cs a b c Lz7)
    (H5 : R5Slot α S g Φ N0) :
    ∃ M Lz Lθ Lt Nz Nθ Nt : ℝ,
      GalHyp α S g m Vz Vθ cs a b c Lz7 M Lz Lθ Lt Nz Nθ Nt := by
  have hα := H.hα
  have hα13 := H.hα13
  have hS := H.hS
  have hmin := H.hmin
  have hm := H.hm
  have hmb := H.hmb
  have hmh := H.hmh
  have hSt1 := H.hSt1
  have hHkn := H.hHkn
  have hbase := H.hbase
  have hj0 := H.hj0
  have hjz := H.hjz
  have hjdz := H.hjdz
  have hjdt := H.hjdt
  have hd1 := H.hd1
  have hd1z := H.hd1z
  have hd1z2 := H.hd1z2
  have ht0 := H.ht0
  have hFjoint := H.hFjoint
  have hVjoint := H.hVjoint
  have hVlipU := H.hVlipU
  have hcscont := H.hcscont
  have hEq := H.hEq
  have hVz0 := H.hVz0
  have hVza := H.hVza
  have hVθb := H.hVθb
  have hVθ0 := H.hVθ0
  have hVθπ := H.hVθπ
  have hcsc := H.hcsc
  have hInit := H.hInit
  have hsuppOut := H.hsuppOut
  have hLz7 := H.hLz7
  have ha := H.ha
  have hb := H.hb
  have hc := H.hc
  have hα1 : α ≤ 1 := le_trans hα13 (by norm_num)
  -- the class data of `StData (extG g)` / `StData2 (extG g)`
  obtain ⟨_, Q, _, hQ, hquad⟩ := hSt1.hSt.quad
  -- the angular vanishing of the slices (`RegPkgMin.vanish`)
  have hvan : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0 :=
    fun τ hτ => hmin.vanish τ hτ.1
  -- the angular endpoint continuity, from the `θ`-Hölder class data `St1Class.hhθ` (re-cut)
  have hcont01 := endpoint_cont_of_holder hα hvan hSt1.hhθ
  have hcont0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun θ => extG g z θ τ) (nhdsWithin 0 (Set.Ioi (0:ℝ)))
        (nhds (extG g z 0 τ)) := hcont01.1
  have hcontπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
      Filter.Tendsto (fun θ => extG g z θ τ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds (extG g z (Real.pi / 2) τ)) := hcont01.2
  -- `C¹` on the open quadrant at every strip time, from `RegPkgMin.c4`
  have hsm1 : ∀ τ ∈ Set.Icc 0 S,
      ContDiffOn ℝ 1 (Function.uncurry (fun z θ => extG g z θ τ))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))) := by
    intro τ hτ
    have h4 : ContDiffOn ℝ 4 (Function.uncurry (fun z θ => extG g z θ τ))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))) :=
      (hmin.c4 τ hτ.1).congr (fun p hp => extG_of_pos hp.1 hτ.1)
    exact h4.of_le (by norm_num)
  -- the small-`z` bound on `∂_z g̃` (`StData.quad`'s second clause)
  have hquad' : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ,
      0 ≤ z → z ≤ 2 →
      |Work.Spaces.pz (gSlice (extG g) τ) z θ| ≤ Q * z :=
    ⟨Q, hQ, fun τ hτ θ hθ z hz hz2 => (hquad τ hτ θ hθ).2 z hz hz2⟩
  -- the sup bounds of `g̃` and `∂_zg̃`, from `hIS` (re-cut)
  obtain ⟨M, hM, hsup⟩ := sup_extG_ext_hIS hS H.hIS hvan hquad'
  have hsupP : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (fun z θ => extG g z θ τ) z θ| ≤ M :=
    ⟨M, hM, fun τ hτ z θ hz hθ => (hsup τ hτ z θ hz hθ).2⟩
  -- the second-order `z`-bound of `∂_z²g̃`, from `hIS` and `c4` (re-cut)
  obtain ⟨M₂, hM₂, hsup2⟩ := sup2_extG_ext_hIS hα hS H.hIS
    (fun τ hτ => hmin.c4 τ hτ.1) hvan hSt1.hSt2.quad2
  -- the `C¹` gluing of the extension (R1b)
  have hcontR1 : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ 1 (fun q : ℝ × ℝ => extG g q.1 θ q.2)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)) :=
    R1c.extG_cont hS hbase hj0 hjz hjdz hjdt hd1 hd1z hd1z2 ht0
  -- the `z`-moduli (R3, from the sup data)
  obtain ⟨Lz, hLzn, hhz⟩ := Der.hzmod hα hα1 hS hcontR1 ⟨M, hM, hsup⟩
  obtain ⟨Nz, hNzn, hhzp⟩ := hzmodp_ext_c4 hα hα1 hS (fun τ hτ => hmin.c4 τ hτ.1)
    hcontR1 hvan hsupP ⟨M₂, hM₂, hsup2⟩
  -- the Jet of `∂_τg̃` (the proved R5, from the right-hand side's Jet)
  have hdt : ∃ Nd : ℝ, Jet α S Nd (fun z θ τ => deriv (fun s => extG g z θ s) τ) :=
    R5f.jet_dtg_of_rhs hα hα13 hS hmin H5.hsol H5.h0 H5.hRHS H5.hRz0 H5.hRθ0 H5.hRθπ
  -- the `τ`-modulus of `g̃`
  obtain ⟨Lt, hLtn, hhτ⟩ := Der.htaumod hα hα1 hS hcontR1 hdt ⟨M, hM, hsup⟩
  -- the `τ`-modulus of `∂_zg̃`, from `∂_τg̃ = dynLin + dynRHS` and its `z`-differentiability
  have hid := R5f.deriv_extG_eq_rhs_of_jet hmin H5.hsol H5.h0 H5.hRz0 H5.hRθ0 H5.hRθπ
  obtain ⟨Nt, hNtn, hhτp⟩ :=
    Der.htaumodp (g := g) (R := rhsFam' α g Φ) hα hα1 hS hcontR1 hid H5.hRHz hvan hsupP
  -- the support propagation (R7e: the velocity's Lipschitz constant is needed only on `z > Lz7`)
  have hsupp7 : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lz7 * Real.exp (a * S) < z → 0 < θ →
      θ < Real.pi / 2 → profFull α (extG g) z θ τ = 0 :=
    R7e.support_strip_zL (S := S) (a := a) (b := b) (c := c) (L := Lz7) hS ha hb hc hLz7
      (F := fun z θ τ => profFull α (extG g) z θ τ) hFjoint hVjoint hVlipU hcscont hEq
      hVz0 hVza hVθb hVθ0 hVθπ hcsc hInit
  obtain ⟨Lout, hLout, hsuppOut'⟩ := hsuppOut
  have hsupp : ∃ L : ℝ, 0 < L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L ≤ z →
      profFull α (extG g) z θ τ = 0 := by
    refine ⟨max (Lz7 * Real.exp (a * S) + 1) (Lout + 1), ?_, ?_⟩
    · have h1 : 0 < Lz7 * Real.exp (a * S) + 1 := by
        have h2 : 0 ≤ Lz7 * Real.exp (a * S) :=
          mul_nonneg hLz7 (le_of_lt (Real.exp_pos _))
        linarith
      exact lt_of_lt_of_le h1 (le_max_left _ _)
    · intro τ hτ z θ hz
      have hz7 : Lz7 * Real.exp (a * S) < z :=
        lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_left _ _) hz)
      have hzout : Lout < z :=
        lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right _ _) hz)
      by_cases hθ : θ ∈ Work.Spaces.Iθ
      · rcases eq_or_lt_of_le hθ.1 with h0 | h0
        · subst h0
          rw [profFull, Fstar_zero_left_rx0 (pExp α) (pExp_pos hα) z, zero_add,
            show extG g z 0 τ = 0 from (extG_hvt hmin.vanish τ hτ).1 z]
        · rcases eq_or_lt_of_le hθ.2 with hπ | hπ
          · subst hπ
            rw [profFull, Fstar_zero_pi_rx0 (pExp α) (pExp_pos hα) z, zero_add,
              show extG g z (π / 2) τ = 0 from (extG_hvt hmin.vanish τ hτ).2 z]
          · exact hsupp7 τ hτ z θ hz7 h0 hπ
      · exact hsuppOut' τ hτ z θ (le_of_lt hzout) hθ
  -- the far-field `Γ`-bound, from the support and `F_* ≲ Γ`
  have hfar : ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Cf ≤ z →
      θ ∈ Work.Spaces.Iθ → |extG g z θ τ| ≤ Cf * Gamma α θ :=
    Der.far_of_support hα hα13 hsupp
  -- the two angular moduli (class data)
  obtain ⟨Lθ, hLθn, hhθ⟩ := hSt1.hhθ
  obtain ⟨Nθ, hNθn, hhθp⟩ := hSt1.hhθp
  exact ⟨M, Lz, Lθ, Lt, Nz, Nθ, Nt,
    { hα := hα, hα13 := hα13, hS := hS, hmin := hmin, hm := hm, hmb := hmb, hmh := hmh,
      hSt := hSt1.hSt, hsm1 := hsm1, hcont0 := hcont0, hcontπ := hcontπ, hfar := hfar,
      hsup := hsup, hhz := hhz, hhθ := hhθ, hhτ := hhτ, hhzp := hhzp, hhθp := hhθp,
      hhτp := hhτp, hbase := hbase, hj0 := hj0, hjz := hjz, hjdz := hjdz, hjdt := hjdt,
      hd1 := hd1, hd1z := hd1z, hd1z2 := hd1z2, ht0 := ht0, hFjoint := hFjoint,
      hVjoint := hVjoint, hVlipU := hVlipU, hcscont := hcscont, hEq := hEq, hVz0 := hVz0,
      hVza := hVza, hVθb := hVθb, hVθ0 := hVθ0, hVθπ := hVθπ, hcsc := hcsc, hInit := hInit,
      hsuppOut := ⟨Lout, hLout, hsuppOut'⟩, hLz7 := hLz7, ha := ha, hb := hb, hc := hc,
      hMn := hM,
      hLzn := hLzn, hLθn := hLθn, hLtn := hLtn, hNzn := hNzn, hNθn := hNθn, hNtn := hNtn }⟩

/-- **THE RE-CUT DELIVERABLE.**  `PartsAssembly.forall_regPkg_of_parts` with `GalMin` replaced by
`GalMin'`. -/
theorem forall_regPkg_of_parts' {α : ℝ} {g Φ : Fam} {m : ℝ → ℝ}
    {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ} {a b c : ℝ}
    (H : ∀ S > 0, ∃ Lz7 : ℝ, Work.FTS.RegExportIface.GalMin' α S g m Vz Vθ cs a b c Lz7)
    (H5 : ∀ S > 0, R5Parts α S g Φ) :
    ∀ S > 0, RegPkg' α S (Avort m) (Bdyn m) (extG g) := by
  intro S hS
  obtain ⟨Lz7, hH⟩ := H S hS
  obtain ⟨N0, h5⟩ := R5Slot_of_R5Parts hH.hα hH.hα13 hH.hS (H5 S hS)
  obtain ⟨M, Lz, Lθ, Lt, Nz, Nθ, Nt, hgal⟩ := galHyp_of_galMin' hH h5
  exact regPkg_of_galerkin hgal h5

end Work.FTS_RegExport.RX0
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.HJ.HJBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open Filter Set
open scoped Topology

namespace Work.FTS_RegExport.RXR1

/-! ## The `R5Parts` fields at `τ = 0`: `O(z)` bound and bounded derivative of the right-hand side

The five pieces of `RHSo` are: `-(𝓛_Γ^T G)(0)`, the singular `-μ̄·AK` term, `N₀`, `N` and `N_*`.
The first four are termwise differentiable in `z` with a uniform bound (`R5Parts.hLz`, `hN₀z`,
`hNz`, `hNsz`) and jointly bounded with a joint Hölder modulus (`R5Parts.hJ`); the last one is the
explicit `AK`, controlled by `HJ.AKBounds`.  The right-hand side vanishes at `z = 0`
(`R5Parts.hRz0`), so the Lipschitz-in-`z` bound upgrades to an `O(z)` bound. -/

theorem exists_RHS_bound {αG S : ℝ} {G Φ : Work.FTS.Galerkin.Fam}
    (hαG : 0 < αG) (hαG13 : αG ≤ 1 / 3) (hS : 0 < S)
    (H : Work.FTS.RegPkgGal.R5Parts αG S G Φ) :
    ∃ NZ : ℝ, 0 ≤ NZ ∧
      (∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z → |RHSo αG G Φ z θ| ≤ NZ * z) ∧
      (∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z →
        ∃ d : ℝ, HasDerivAt (fun z' : ℝ => RHSo αG G Φ z' θ) d z ∧ |d| ≤ NZ) := by
  obtain ⟨NJ, hL, hN0, hN, hNs⟩ := H.hJ
  obtain ⟨M, hM0, hMb⟩ := H.hmb
  obtain ⟨NZ1, hNZ1, hLz⟩ := H.hLz
  obtain ⟨NZ2, hNZ2, hN0z⟩ := H.hN₀z
  obtain ⟨NZ3, hNZ3, hNz⟩ := H.hNz
  obtain ⟨NZ4, hNZ4, hNsz⟩ := H.hNsz
  have hp1 : (0 : ℝ) < Work.FTS.Regularity.pExp αG := by
    simp only [Work.FTS.Regularity.pExp]; linarith
  have hp2 : Work.FTS.Regularity.pExp αG ≤ 1 := by
    simp only [Work.FTS.Regularity.pExp]; linarith
  obtain ⟨hAKval, hAKder⟩ := HJ.AKBounds hp1 hp2
  have hmbar : |mbar0 αG G Φ| ≤ M := by
    have h := hMb 0 ⟨le_rfl, hS.le⟩
    simpa only [mbar0] using h
  have hconst : 0 ≤ NZ1 + M * 10 + NZ2 + NZ3 + NZ4 := by
    have h10 : (0 : ℝ) ≤ M * 10 := by positivity
    linarith
  refine ⟨NZ1 + M * 10 + NZ2 + NZ3 + NZ4, hconst, ?_, ?_⟩
  · intro θ hθ z hz
    have hder : ∀ x : ℝ, 0 < x → ∃ d : ℝ,
        HasDerivAt (fun z' => RHSo αG G Φ z' θ) d x ∧
          |d| ≤ NZ1 + M * 10 + NZ2 + NZ3 + NZ4 := by
      intro x hx
      obtain ⟨d1, hd1, hb1⟩ := hLz 0 ⟨le_rfl, hS.le⟩ θ hθ x hx
      obtain ⟨d2, hd2, hb2⟩ := hN0z 0 ⟨le_rfl, hS.le⟩ θ hθ x hx
      obtain ⟨d3, hd3, hb3⟩ := hNz 0 ⟨le_rfl, hS.le⟩ θ hθ x hx
      obtain ⟨d4, hd4, hb4⟩ := hNsz 0 ⟨le_rfl, hS.le⟩ θ hθ x hx
      obtain ⟨da, hda, hba⟩ := hAKder θ hθ x hx
      have hd1' : HasDerivAt (fun z' => RP1 αG G z' θ) d1 x := hd1
      have hd2' : HasDerivAt (fun z' => RP2 αG G z' θ) d2 x := hd2
      have hd3' : HasDerivAt (fun z' => RP3 αG G Φ z' θ) d3 x := hd3
      have hd4' : HasDerivAt (fun z' => RP4 αG G Φ z' θ) d4 x := hd4
      have ha : HasDerivAt (fun z' => (-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) z' θ)
          ((-(mbar0 αG G Φ)) * da) x := hda.const_mul _
      have h5 : HasDerivAt
          (fun z' => RP1 αG G z' θ + ((-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) z' θ
            + RP2 αG G z' θ + RP3 αG G Φ z' θ + RP4 αG G Φ z' θ))
          (d1 + ((-(mbar0 αG G Φ)) * da + d2 + d3 + d4)) x :=
        hd1'.add (((ha.add hd2').add hd3').add hd4')
      have hR : HasDerivAt (fun z' => RHSo αG G Φ z' θ)
          (d1 + ((-(mbar0 αG G Φ)) * da + d2 + d3 + d4)) x := by
        simpa only [RHSo_eq] using h5
      refine ⟨d1 + ((-(mbar0 αG G Φ)) * da + d2 + d3 + d4), hR, ?_⟩
      have hprod : |(-(mbar0 αG G Φ)) * da| ≤ M * 10 := by
        rw [abs_mul, abs_neg]
        exact mul_le_mul hmbar hba (abs_nonneg _) hM0
      calc |d1 + ((-(mbar0 αG G Φ)) * da + d2 + d3 + d4)|
          ≤ |d1| + |(-(mbar0 αG G Φ)) * da + d2 + d3 + d4| := abs_add_le _ _
        _ ≤ |d1| + (|(-(mbar0 αG G Φ)) * da + d2 + d3| + |d4|) := by
              gcongr
              exact abs_add_le _ _
        _ ≤ |d1| + ((|(-(mbar0 αG G Φ)) * da + d2| + |d3|) + |d4|) := by
              gcongr
              exact abs_add_le _ _
        _ ≤ |d1| + (((|(-(mbar0 αG G Φ)) * da| + |d2|) + |d3|) + |d4|) := by
              gcongr
              exact abs_add_le _ _
        _ ≤ NZ1 + M * 10 + NZ2 + NZ3 + NZ4 := by linarith
    have htend : Tendsto (fun z => RHSo αG G Φ z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hl1 : Tendsto (fun z => RP1 αG G z θ) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (RP1 αG G 0 θ)) := by
        have h := HJ.jetZsliceTendsto hL hαG hθ ⟨le_rfl, hS.le⟩
        simpa only [RP1] using h
      have hl2 : Tendsto (fun z => RP2 αG G z θ) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (RP2 αG G 0 θ)) := by
        have h := HJ.jetZsliceTendsto hN0 hαG hθ ⟨le_rfl, hS.le⟩
        simpa only [RP2] using h
      have hl3 : Tendsto (fun z => RP3 αG G Φ z θ) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (RP3 αG G Φ 0 θ)) := by
        have h := HJ.jetZsliceTendsto hN hαG hθ ⟨le_rfl, hS.le⟩
        simpa only [RP3] using h
      have hl4 : Tendsto (fun z => RP4 αG G Φ z θ) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (RP4 αG G Φ 0 θ)) := by
        have h := HJ.jetZsliceTendsto hNs hαG hθ ⟨le_rfl, hS.le⟩
        simpa only [RP4] using h
      have hla : Tendsto (fun z => (-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) z θ)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have hb : ∀ᶠ z : ℝ in nhdsWithin 0 (Set.Ioi 0),
            |(-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) z θ|
              ≤ |mbar0 αG G Φ| * (20 * z ^ 2) := by
          filter_upwards [self_mem_nhdsWithin] with z hz
          rw [abs_mul, abs_neg]
          exact mul_le_mul_of_nonneg_left (hAKval θ hθ z hz.le) (abs_nonneg _)
        have hg : Tendsto (fun z : ℝ => |mbar0 αG G Φ| * (20 * z ^ 2))
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
          have hc : Continuous fun z : ℝ => |mbar0 αG G Φ| * (20 * z ^ 2) := by continuity
          simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
        exact squeeze_zero_norm' hb hg
      have hAK0 : Work.Construction.AK (Work.FTS.Regularity.pExp αG) 0 θ = 0 := by
        simp [Work.Construction.AK]
      have hlim : Tendsto (fun z => RP1 αG G z θ
            + ((-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) z θ
              + RP2 αG G z θ + RP3 αG G Φ z θ + RP4 αG G Φ z θ))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (RP1 αG G 0 θ + ((-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) 0 θ
            + RP2 αG G 0 θ + RP3 αG G Φ 0 θ + RP4 αG G Φ 0 θ))) := by
        rw [hAK0]
        simpa using hl1.add (((hla.add hl2).add hl3).add hl4)
      have hzero : RP1 αG G 0 θ + ((-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) 0 θ
          + RP2 αG G 0 θ + RP3 αG G Φ 0 θ + RP4 αG G Φ 0 θ) = 0 := by
        rw [← RHSo_eq 0 θ]
        exact H.hRz0 0 ⟨le_rfl, hS.le⟩ θ hθ
      have hgoal : Tendsto (fun z => RP1 αG G z θ
            + ((-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) z θ
              + RP2 αG G z θ + RP3 αG G Φ z θ + RP4 αG G Φ z θ))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        simpa only [hzero] using hlim
      exact hgoal.congr' (Eventually.of_forall fun z => (RHSo_eq z θ).symm)
    exact HJ.derivBoundZero hconst hder htend z hz
  · intro θ hθ z hz
    obtain ⟨d1, hd1, hb1⟩ := hLz 0 ⟨le_rfl, hS.le⟩ θ hθ z hz
    obtain ⟨d2, hd2, hb2⟩ := hN0z 0 ⟨le_rfl, hS.le⟩ θ hθ z hz
    obtain ⟨d3, hd3, hb3⟩ := hNz 0 ⟨le_rfl, hS.le⟩ θ hθ z hz
    obtain ⟨d4, hd4, hb4⟩ := hNsz 0 ⟨le_rfl, hS.le⟩ θ hθ z hz
    obtain ⟨da, hda, hba⟩ := hAKder θ hθ z hz
    have hd1' : HasDerivAt (fun z' => RP1 αG G z' θ) d1 z := hd1
    have hd2' : HasDerivAt (fun z' => RP2 αG G z' θ) d2 z := hd2
    have hd3' : HasDerivAt (fun z' => RP3 αG G Φ z' θ) d3 z := hd3
    have hd4' : HasDerivAt (fun z' => RP4 αG G Φ z' θ) d4 z := hd4
    have ha : HasDerivAt (fun z' => (-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) z' θ)
        ((-(mbar0 αG G Φ)) * da) z := hda.const_mul _
    have h5 : HasDerivAt
        (fun z' => RP1 αG G z' θ + ((-(mbar0 αG G Φ)) * Work.Construction.AK (Work.FTS.Regularity.pExp αG) z' θ
          + RP2 αG G z' θ + RP3 αG G Φ z' θ + RP4 αG G Φ z' θ))
        (d1 + ((-(mbar0 αG G Φ)) * da + d2 + d3 + d4)) z :=
      hd1'.add (((ha.add hd2').add hd3').add hd4')
    refine ⟨d1 + ((-(mbar0 αG G Φ)) * da + d2 + d3 + d4), ?_, ?_⟩
    · simpa only [RHSo_eq] using h5
    · have hprod : |(-(mbar0 αG G Φ)) * da| ≤ M * 10 := by
        rw [abs_mul, abs_neg]
        exact mul_le_mul hmbar hba (abs_nonneg _) hM0
      calc |d1 + ((-(mbar0 αG G Φ)) * da + d2 + d3 + d4)|
          ≤ |d1| + |(-(mbar0 αG G Φ)) * da + d2 + d3 + d4| := abs_add_le _ _
        _ ≤ |d1| + (|(-(mbar0 αG G Φ)) * da + d2 + d3| + |d4|) := by
              gcongr
              exact abs_add_le _ _
        _ ≤ |d1| + ((|(-(mbar0 αG G Φ)) * da + d2| + |d3|) + |d4|) := by
              gcongr
              exact abs_add_le _ _
        _ ≤ |d1| + (((|(-(mbar0 αG G Φ)) * da| + |d2|) + |d3|) + |d4|) := by
              gcongr
              exact abs_add_le _ _
        _ ≤ NZ1 + M * 10 + NZ2 + NZ3 + NZ4 := by linarith

end Work.FTS_RegExport.RXR1
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.HJ.HJTriple =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open Filter Set
open scoped Topology

namespace Work.FTS_RegExport.RXR1

/-! ## Elementary facts about `Gs α g = gS α (tauExt g)` near `z = 0` -/

theorem Gs_eq_tauExt {α : ℝ} {g : Work.FTS.Galerkin.Fam} {z θ τ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Gs α g z θ τ = Work.FTS.FinalV2.tauExt g z θ τ := by
  have hθ' : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := hθ
  simp only [Gs, Work.FTS.FinalV2.gS, if_pos hz, if_pos hθ']

theorem Gs_of_nonneg {α : ℝ} {g : Work.FTS.Galerkin.Fam} {z θ τ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) (hτ : 0 ≤ τ) :
    Gs α g z θ τ = g z θ τ := by
  rw [Gs_eq_tauExt hz hθ, Work.FTS.FinalV2.tauExt_of_nonneg g hτ]

theorem Gs_of_neg {α : ℝ} {g : Work.FTS.Galerkin.Fam} {z θ τ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) (hτ : τ < 0) :
    Gs α g z θ τ = g z θ 0 + τ * derivWithin (fun s => g z θ s) (Set.Ici 0) 0 := by
  rw [Gs_eq_tauExt hz hθ, Work.FTS.FinalV2.tauExt_of_neg g hτ]

/-- `gS α (tauExt g)` vanishes identically at the two angular endpoints. -/
theorem Gs_eq_zero_of_ends {α : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (Real.pi / 2) τ = 0)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hends : θ = 0 ∨ θ = Real.pi / 2) :
    ∀ z τ : ℝ, Gs α g z θ τ = 0 := by
  intro z τ
  have key : ∀ θ₀ : ℝ, (∀ s : ℝ, 0 ≤ s → g z θ₀ s = 0) →
      derivWithin (fun s => g z θ₀ s) (Set.Ici 0) 0 = 0 := by
    intro θ₀ hzero
    have hev : (fun s => g z θ₀ s) =ᶠ[𝓝[Set.Ici 0] 0] fun _ => (0 : ℝ) :=
      eventually_nhdsWithin_of_forall fun s hs => hzero s hs
    rw [Filter.EventuallyEq.derivWithin_eq hev (hzero 0 le_rfl)]
    exact congrFun (derivWithin_const (Set.Ici 0) (0 : ℝ)) 0
  rcases hends with rfl | rfl
  · by_cases hz : 0 < z
    · rw [Gs_eq_tauExt hz hθ]
      by_cases hτ : τ < 0
      · rw [Work.FTS.FinalV2.tauExt_of_neg g hτ,
          key 0 (fun s hs => (hv s hs z hz.le).1), (hv 0 le_rfl z hz.le).1]
        ring
      · rw [Work.FTS.FinalV2.tauExt_of_nonneg g (not_lt.mp hτ)]
        exact (hv τ (not_lt.mp hτ) z hz.le).1
    · simp only [Gs, Work.FTS.FinalV2.gS, if_neg hz]
  · by_cases hz : 0 < z
    · rw [Gs_eq_tauExt hz hθ]
      by_cases hτ : τ < 0
      · rw [Work.FTS.FinalV2.tauExt_of_neg g hτ,
          key (Real.pi / 2) (fun s hs => (hv s hs z hz.le).2), (hv 0 le_rfl z hz.le).2]
        ring
      · rw [Work.FTS.FinalV2.tauExt_of_nonneg g (not_lt.mp hτ)]
        exact (hv τ (not_lt.mp hτ) z hz.le).2
    · simp only [Gs, Work.FTS.FinalV2.gS, if_neg hz]

/-! ## The `τ < 0` branch: `gS α (tauExt g) = datum + τ · RHS` -/

theorem derivWithin_g_eq {α : ℝ} {g : Work.FTS.Galerkin.Fam} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    derivWithin (fun s => g z θ s) (Set.Ici 0) 0
      = derivWithin (fun s => Gs α g z θ s) (Set.Ici 0) 0 := by
  refine Filter.EventuallyEq.derivWithin_eq ?_ ?_
  · exact eventually_nhdsWithin_of_forall fun s hs => by
      show g z θ s = Gs α g z θ s
      rw [Gs_of_nonneg hz hθ hs]
  · show g z θ 0 = Gs α g z θ 0
    rw [Gs_of_nonneg hz hθ le_rfl]

theorem derivWithin_eq_RHS {αG S : ℝ} {G Φ : Work.FTS.Galerkin.Fam}
    (H : Work.FTS.RegPkgGal.R5Parts αG S G Φ) {θ z : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hz : 0 < z) :
    derivWithin (fun s => G z θ s) (Set.Ici 0) 0 = RHSo αG G Φ z θ := by
  have hq : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ⟩
  have h := (H.h0 z θ hz hq).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)
  simpa only [RHSo] using h

/-! ## The three cluster limits from three envelope bounds -/

/-- The three cluster limits, from three envelope bounds. -/
theorem hj_triple {G : ℝ → ℝ → ℝ → ℝ} {K Q NZ θ τ₀ : ℝ}
    (hbd1 : ∀ᶠ p : ℝ × ℝ in Filt τ₀, |G p.1 θ p.2| ≤ K * p.1 ^ 2 + NZ * p.1 * |p.2|)
    (hbd2 : ∀ᶠ p : ℝ × ℝ in Filt τ₀, |p.1⁻¹ * G p.1 θ p.2| ≤ K * p.1 + NZ * |p.2|)
    (hbd3 : ∀ᶠ p : ℝ × ℝ in Filt τ₀, |deriv (fun z => G z θ p.2) p.1| ≤ Q * p.1 + NZ * |p.2|)
    (ht1 : Tendsto (fun p : ℝ × ℝ => K * p.1 ^ 2 + NZ * p.1 * |p.2|) (Filt τ₀) (nhds 0))
    (ht2 : Tendsto (fun p : ℝ × ℝ => K * p.1 + NZ * |p.2|) (Filt τ₀) (nhds 0))
    (ht3 : Tendsto (fun p : ℝ × ℝ => Q * p.1 + NZ * |p.2|) (Filt τ₀) (nhds 0)) :
    (Tendsto (fun p : ℝ × ℝ => G p.1 θ p.2) (Filt τ₀) (nhds 0)) ∧
    (Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * G p.1 θ p.2) (Filt τ₀) (nhds 0)) ∧
    (Tendsto (fun p : ℝ × ℝ => deriv (fun z => G z θ p.2) p.1) (Filt τ₀) (nhds 0)) :=
  ⟨squeeze_zero_norm' hbd1 ht1, squeeze_zero_norm' hbd2 ht2, squeeze_zero_norm' hbd3 ht3⟩

/-- The `τ₀ > 0` case: only nonnegative `τ` occur eventually, so the envelopes carry no
`|τ|`-term. -/
theorem hj_triple_pos {G : ℝ → ℝ → ℝ → ℝ} {K Q S θ τ₀ : ℝ} (hτpos : 0 < τ₀)
    (hτS : τ₀ < S + 2)
    (hquadv : ∀ τ ∈ Set.Icc 0 (S + 2), ∀ z ∈ Set.Ioo (0 : ℝ) 2, |G z θ τ| ≤ K * z ^ 2)
    (hquadd : ∀ τ ∈ Set.Icc 0 (S + 2), ∀ z ∈ Set.Ioo (0 : ℝ) 2,
      |deriv (fun z' => G z' θ τ) z| ≤ Q * z) :
    (Tendsto (fun p : ℝ × ℝ => G p.1 θ p.2) (Filt τ₀) (nhds 0)) ∧
    (Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * G p.1 θ p.2) (Filt τ₀) (nhds 0)) ∧
    (Tendsto (fun p : ℝ × ℝ => deriv (fun z => G z θ p.2) p.1) (Filt τ₀) (nhds 0)) := by
  have hzpos : ∀ᶠ p : ℝ × ℝ in Filt τ₀, 0 < p.1 :=
    Filter.mem_of_superset self_mem_nhdsWithin fun p hp => hp.1
  have hlt2 : ∀ᶠ p : ℝ × ℝ in Filt τ₀, p.1 < 2 :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_fst continuous_const).mem_nhds
      (by simp only [Set.mem_setOf_eq]; norm_num))
  have hltS : ∀ᶠ p : ℝ × ℝ in Filt τ₀, p.2 < S + 2 :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_snd continuous_const).mem_nhds
      (by simpa only [Set.mem_setOf_eq] using hτS))
  have hpos : ∀ᶠ p : ℝ × ℝ in Filt τ₀, 0 < p.2 :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_const continuous_snd).mem_nhds hτpos)
  have hfst : Tendsto (fun p : ℝ × ℝ => p.1) (Filt τ₀) (nhds 0) :=
    (continuous_fst.continuousAt (x := ((0 : ℝ), τ₀))).mono_left nhdsWithin_le_nhds
  refine hj_triple (K := K) (Q := Q) (NZ := 0) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hzpos, hlt2, hltS, hpos] with p hp1 hp2 hp3 hp4
    exact le_trans (hquadv p.2 ⟨hp4.le, hp3.le⟩ p.1 ⟨hp1, hp2⟩) (by simp)
  · filter_upwards [hzpos, hlt2, hltS, hpos] with p hp1 hp2 hp3 hp4
    rw [abs_mul, abs_of_pos (inv_pos.mpr hp1)]
    calc p.1⁻¹ * |G p.1 θ p.2| ≤ p.1⁻¹ * (K * p.1 ^ 2) :=
          mul_le_mul_of_nonneg_left (hquadv p.2 ⟨hp4.le, hp3.le⟩ p.1 ⟨hp1, hp2⟩)
            (le_of_lt (inv_pos.mpr hp1))
      _ = K * p.1 := by
          have hne : p.1 ≠ 0 := ne_of_gt hp1
          field_simp
      _ ≤ K * p.1 + 0 * |p.2| := by simp
  · filter_upwards [hzpos, hlt2, hltS, hpos] with p hp1 hp2 hp3 hp4
    exact le_trans (hquadd p.2 ⟨hp4.le, hp3.le⟩ p.1 ⟨hp1, hp2⟩) (by simp)
  · have h1 : Tendsto (fun p : ℝ × ℝ => K * p.1 ^ 2) (Filt τ₀) (nhds 0) := by
      simpa using (hfst.pow 2).const_mul K
    simpa using h1
  · have h1 : Tendsto (fun p : ℝ × ℝ => K * p.1) (Filt τ₀) (nhds 0) := by
      simpa using hfst.const_mul K
    simpa using h1
  · have h1 : Tendsto (fun p : ℝ × ℝ => Q * p.1) (Filt τ₀) (nhds 0) := by
      simpa using hfst.const_mul Q
    simpa using h1

/-- The `τ₀ = 0` case: the `τ < 0` branch is live and contributes the `|τ|`-terms. -/
theorem hj_triple_zero {G : ℝ → ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ} {gd : ℝ → ℝ} {K Q NZ S θ : ℝ}
    (hK : 0 ≤ K) (hNZ : 0 ≤ NZ) (hS2 : 0 < S + 2)
    (hdat0 : ∀ z ∈ Set.Ioo (0 : ℝ) 2, |gd z| ≤ K * z ^ 2)
    (hquadv : ∀ τ ∈ Set.Icc 0 (S + 2), ∀ z ∈ Set.Ioo (0 : ℝ) 2, |G z θ τ| ≤ K * z ^ 2)
    (hquadd : ∀ τ ∈ Set.Icc 0 (S + 2), ∀ z ∈ Set.Ioo (0 : ℝ) 2,
      |deriv (fun z' => G z' θ τ) z| ≤ Q * z)
    (hneg : ∀ z ∈ Set.Ioo (0 : ℝ) 2, ∀ τ < 0, G z θ τ = gd z + τ * R z θ)
    (hRbd : ∀ z ∈ Set.Ioo (0 : ℝ) 2, |R z θ| ≤ NZ * z)
    (hRder : ∀ z ∈ Set.Ioo (0 : ℝ) 2,
      ∃ d : ℝ, HasDerivAt (fun z' => R z' θ) d z ∧ |d| ≤ NZ)
    (hA : ∀ z ∈ Set.Ioo (0 : ℝ) 2,
      ∃ A : ℝ, HasDerivAt gd A z ∧ |A| ≤ Q * z) :
    (Tendsto (fun p : ℝ × ℝ => G p.1 θ p.2) (Filt 0) (nhds 0)) ∧
    (Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * G p.1 θ p.2) (Filt 0) (nhds 0)) ∧
    (Tendsto (fun p : ℝ × ℝ => deriv (fun z => G z θ p.2) p.1) (Filt 0) (nhds 0)) := by
  have hzpos : ∀ᶠ p : ℝ × ℝ in Filt 0, 0 < p.1 :=
    Filter.mem_of_superset self_mem_nhdsWithin fun p hp => hp.1
  have hlt2 : ∀ᶠ p : ℝ × ℝ in Filt 0, p.1 < 2 :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_fst continuous_const).mem_nhds
      (by simp only [Set.mem_setOf_eq]; norm_num))
  have hltS : ∀ᶠ p : ℝ × ℝ in Filt 0, p.2 < S + 2 :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_snd continuous_const).mem_nhds
      (by simpa only [Set.mem_setOf_eq] using hS2))
  have hfst : Tendsto (fun p : ℝ × ℝ => p.1) (Filt 0) (nhds 0) :=
    (continuous_fst.continuousAt (x := ((0 : ℝ), (0 : ℝ)))).mono_left nhdsWithin_le_nhds
  have hsnd0 : Tendsto (fun p : ℝ × ℝ => p.2) (Filt 0) (nhds 0) :=
    (continuous_snd.continuousAt (x := ((0 : ℝ), (0 : ℝ)))).mono_left nhdsWithin_le_nhds
  have hkey : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 < 2 → p.2 < S + 2 →
      |G p.1 θ p.2| ≤ K * p.1 ^ 2 + NZ * p.1 * |p.2| := by
    intro p hp1 hp2 hp3
    rcases lt_or_ge p.2 0 with hτ | hτ
    · rw [hneg p.1 ⟨hp1, hp2⟩ p.2 hτ]
      calc |gd p.1 + p.2 * R p.1 θ| ≤ |gd p.1| + |p.2 * R p.1 θ| := abs_add_le _ _
        _ ≤ K * p.1 ^ 2 + |p.2| * (NZ * p.1) := by
            gcongr
            · exact hdat0 p.1 ⟨hp1, hp2⟩
            · rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (hRbd p.1 ⟨hp1, hp2⟩) (abs_nonneg _)
        _ = K * p.1 ^ 2 + NZ * p.1 * |p.2| := by ring
    · have h := hquadv p.2 ⟨hτ, hp3.le⟩ p.1 ⟨hp1, hp2⟩
      have h2 : 0 ≤ NZ * p.1 * |p.2| := by positivity
      linarith
  refine hj_triple (K := K) (Q := Q) (NZ := NZ) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hzpos, hlt2, hltS] with p hp1 hp2 hp3
    exact hkey p hp1 hp2 hp3
  · filter_upwards [hzpos, hlt2, hltS] with p hp1 hp2 hp3
    rw [abs_mul, abs_of_pos (inv_pos.mpr hp1)]
    calc p.1⁻¹ * |G p.1 θ p.2|
        ≤ p.1⁻¹ * (K * p.1 ^ 2 + NZ * p.1 * |p.2|) :=
          mul_le_mul_of_nonneg_left (hkey p hp1 hp2 hp3) (le_of_lt (inv_pos.mpr hp1))
      _ = K * p.1 + NZ * |p.2| := by
          have hne : p.1 ≠ 0 := ne_of_gt hp1
          field_simp
  · filter_upwards [hzpos, hlt2, hltS] with p hp1 hp2 hp3
    rcases lt_or_ge p.2 0 with hτ | hτ
    · have hev : (fun z => G z θ p.2) =ᶠ[𝓝 p.1] (fun z => gd z + p.2 * R z θ) := by
        filter_upwards [isOpen_Ioo.mem_nhds ⟨hp1, hp2⟩] with z hz
        exact hneg z hz p.2 hτ
      rw [Filter.EventuallyEq.deriv_eq hev]
      obtain ⟨A, hAd, hAb⟩ := hA p.1 ⟨hp1, hp2⟩
      obtain ⟨d, hd, hdb⟩ := hRder p.1 ⟨hp1, hp2⟩
      have hsum : HasDerivAt (fun z => gd z + p.2 * R z θ) (A + p.2 * d) p.1 :=
        hAd.add (hd.const_mul p.2)
      rw [hsum.deriv]
      calc |A + p.2 * d| ≤ |A| + |p.2 * d| := abs_add_le _ _
        _ ≤ Q * p.1 + |p.2| * NZ := by
            gcongr
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left hdb (abs_nonneg _)
        _ = Q * p.1 + NZ * |p.2| := by ring
    · have h := hquadd p.2 ⟨hτ, hp3.le⟩ p.1 ⟨hp1, hp2⟩
      have h2 : 0 ≤ NZ * |p.2| := by positivity
      linarith
  · have h1 : Tendsto (fun p : ℝ × ℝ => K * p.1 ^ 2) (Filt 0) (nhds 0) := by
      simpa using (hfst.pow 2).const_mul K
    have h2 : Tendsto (fun p : ℝ × ℝ => NZ * p.1 * |p.2|) (Filt 0) (nhds 0) := by
      have h := (hfst.mul hsnd0.abs).const_mul NZ
      simpa only [mul_assoc, abs_zero, mul_zero] using h
    simpa using h1.add h2
  · have h1 : Tendsto (fun p : ℝ × ℝ => K * p.1) (Filt 0) (nhds 0) := by
      simpa using hfst.const_mul K
    have h2 : Tendsto (fun p : ℝ × ℝ => NZ * |p.2|) (Filt 0) (nhds 0) := by
      simpa using hsnd0.abs.const_mul NZ
    simpa using h1.add h2
  · have h1 : Tendsto (fun p : ℝ × ℝ => Q * p.1) (Filt 0) (nhds 0) := by
      simpa using hfst.const_mul Q
    have h2 : Tendsto (fun p : ℝ × ℝ => NZ * |p.2|) (Filt 0) (nhds 0) := by
      simpa using hsnd0.abs.const_mul NZ
    simpa using h1.add h2

end Work.FTS_RegExport.RXR1
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.hbase_gS_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR1

open scoped Topology Real
open Set Filter MeasureTheory

/-!
# `Work.FTS_RegExport.RXR1.hbase_gS_aux` — the gluing machinery for `hbase_gS`

The joint `C¹` regularity of `(z,τ) ↦ gS α (tauExt g) z θ τ` on `z > 0, τ > -1`, at every fixed
angle `θ ∈ Iθ`.  This is the `hbase` field of the R1 block (`RegExportIface.R1Block`), one of the
inputs of the Galerkin→regularity assembly.

The proof: on `z > 0`, `θ ∈ Iθ` the sanitiser is transparent, so the function is the right-Taylor
extension `tauExt g`; for `τ ≥ 0` it is `g`, for `τ < 0` the affine jet
`g z θ 0 + τ · ∂_τ⁺g(z,θ,0)`.  The two branches are glued at `τ = 0` by the one-sided Taylor
expansion of `g` at `τ = 0⁺`, which is the fundamental theorem of calculus in `τ` together with
the `Jet` property of the equation's right-hand side (uniform in `(z,θ)`); the `τ = 0` slice is
the explicit datum `locG6`, and the continuity of the candidate derivative at `τ = 0` comes from
the uniform `z`-derivative bound of the right-hand side.  At `θ = 0, π/2` the function vanishes
identically. -/

/-- The right-hand side of the dynamic equation at the sanitised right-Taylor family. -/
noncomputable def hbgRHS (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) :
    ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ => Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α)
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ
    + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ

/-- `x ^ α` is arbitrarily small at small `x`, for `α > 0`. -/
lemma hbg_rpow_small {C α : ℝ} (hC : 0 ≤ C) (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, C * δ ^ α < ε := by
  have hCp : (0:ℝ) < C + 1 := by linarith
  refine ⟨(ε / (C + 1)) ^ (1 / α), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  have hm : ((ε / (C + 1)) ^ (1 / α)) ^ α = ε / (C + 1) := by
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ ε / (C + 1))]
    have hone : 1 / α * α = 1 := by field_simp
    rw [hone, Real.rpow_one]
  rw [hm]
  rw [mul_div_assoc']
  rw [div_lt_iff₀ hCp]
  nlinarith

/-- A function that is `α`-Hölder on `[0,1]` is continuous there. -/
lemma hbg_contOn_of_holder {f : ℝ → ℝ} {C α : ℝ} (hC : 0 ≤ C) (hα : 0 < α)
    (h : ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1, |f x - f y| ≤ C * |x - y| ^ α) :
    ContinuousOn f (Set.Icc (0:ℝ) 1) := by
  refine Metric.continuousOn_iff.2 fun b hb ε hε => ?_
  have hCp : (0:ℝ) < C + 1 := by linarith
  set δ : ℝ := min 1 ((ε / (C + 1)) ^ (1 / α)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨δ, hδpos, fun a ha habs => ?_⟩
  have h1 : |f a - f b| ≤ C * |a - b| ^ α := h a ha b hb
  have h2 : |a - b| ≤ δ := by
    rw [Real.dist_eq] at habs
    exact le_of_lt habs
  have h3 : |a - b| ^ α ≤ δ ^ α := Real.rpow_le_rpow (abs_nonneg _) h2 hα.le
  have h4 : δ ^ α ≤ ε / (C + 1) := by
    rw [hδ]
    have hm : ((ε / (C + 1)) ^ (1 / α)) ^ α = ε / (C + 1) := by
      rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ ε / (C + 1))]
      have hone : 1 / α * α = 1 := by field_simp
      rw [hone, Real.rpow_one]
    calc (min 1 ((ε / (C + 1)) ^ (1 / α))) ^ α
        ≤ ((ε / (C + 1)) ^ (1 / α)) ^ α :=
          Real.rpow_le_rpow (le_min zero_le_one (by positivity)) (min_le_right _ _) hα.le
      _ = ε / (C + 1) := hm
  have h5 : C * δ ^ α < ε := by
    calc C * δ ^ α ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left h4 hC
      _ < ε := by
          rw [mul_div_assoc']
          rw [div_lt_iff₀ hCp]
          nlinarith
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (le_trans h1 (mul_le_mul_of_nonneg_left h3 hC)) h5

/-- The `z`-slice of a `C¹` function on an open set is differentiable, with its `deriv`. -/
lemma hbg_hasDerivAt_slice_z {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s) {z τ : ℝ} (h : (z, τ) ∈ s) :
    HasDerivAt (fun z' => f (z', τ)) (deriv (fun z' => f (z', τ)) z) z := by
  have hAt : HasFDerivAt f (fderiv ℝ f (z, τ)) (z, τ) :=
    Work.FTS.RegPkgGal.R1b.hasFDerivAt_of_contDiffOn_one hs hf h
  have hcurve : HasDerivAt (fun z' : ℝ => ((z', τ) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z τ)
  have hcomp := hAt.comp_hasDerivAt z hcurve
  have hval : (fderiv ℝ f (z, τ)) (1, 0) = deriv (fun z' => f (z', τ)) z := by
    rw [Work.FTS.RegPkgGal.R1b.fderiv_eq_partials hAt.differentiableAt]
    simp
  rwa [hval] at hcomp

/-- The `locG6` datum is smooth in `z` at every fixed interior angle. -/
lemma hbg_locG6_slice {α L β : ℝ} {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2))
    (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ 1 (fun z : ℝ => Work.FTS.LocData6.locG6 α L β z θ) (Set.Ioi 0) := by
  have hSQ : Work.FTS.LocData.SmoothQuad (Work.FTS.LocData6.locG6 α L β) :=
    Work.FTS.LocData.SmoothQuad_locG α L β hα hα1 (Work.FTS.LocData.SmoothQuad_hLoc α)
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => Work.FTS.LocData6.locG6 α L β z θ) (Set.Ioi (-1)) :=
    hSQ.curry_z hθ
  have h2 : ContDiffOn ℝ 1 (fun z : ℝ => Work.FTS.LocData6.locG6 α L β z θ) (Set.Ioi (-1)) :=
    h1.of_le (by simp [Work.Stability.smoothOrder])
  refine h2.mono (fun z hz => ?_)
  exact lt_trans (show (-1:ℝ) < 0 by norm_num) (show (0:ℝ) < z from hz)

/-- The sanitiser is transparent on the closed angular interval, at `z > 0`. -/
lemma hbg_gS_eq {α : ℝ} {h : Work.FTS.Galerkin.Fam} {z θ τ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) : Work.FTS.FinalV2.gS α h z θ τ = h z θ τ := by
  simp only [Work.FTS.FinalV2.gS, hz, hθ.1, hθ.2, and_self, ite_true]

/-- The equation's right-hand side is a `Jet` (uniformly bounded and `α`-Hölder). -/
theorem hbg_RHS_jet {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (H5 : ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))) :
    ∃ Nc : ℝ, Work.FTS.Regularity.Jet α 1 Nc (fun z θ τ => hbgRHS α Φs E g z θ τ) := by
  obtain ⟨NJ, hL, hN0, hN, hNs⟩ := (H5 1 one_pos).hJ
  exact Work.FTS.RegPkgGal.Der.rhs_jet_of_parts (α := α) (S := 1)
    hα hα13 one_pos hL hN0 hN hNs (H5 1 one_pos).hmb (H5 1 one_pos).hmbh

/-- The right-hand side has a `z`-derivative bounded uniformly on the strip and in `θ`. -/
theorem hbg_RHS_zderiv {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (H5 : ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))) :
    ∃ Nz : ℝ, 0 ≤ Nz ∧ ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ θ' ∈ Work.Spaces.Iθ,
      ∀ z' ∈ Set.Ioi (0:ℝ), ∃ d : ℝ,
        HasDerivAt (fun z'' => hbgRHS α Φs E g z'' θ' τ) d z' ∧ |d| ≤ Nz := by
  obtain ⟨N₁, hN₁, h1⟩ := (H5 1 one_pos).hLz
  obtain ⟨N₂, hN₂, h2⟩ := (H5 1 one_pos).hN₀z
  obtain ⟨N₃, hN₃, h3⟩ := (H5 1 one_pos).hNz
  obtain ⟨N₄, hN₄, h4⟩ := (H5 1 one_pos).hNsz
  exact Work.FTS.RegPkgGal.Der.rhs_zderiv_of_parts (α := α) (S := 1)
    hα hα13 one_pos h1 h2 h3 h4 (H5 1 one_pos).hmb

/-- **The `τ > 0` side of the junction**: the one-sided limit of the candidate derivative of the
`τ ≥ 0` branch as `(z,τ) → (z₀,0⁺)` is the jet's derivative at `(z₀,0)`. -/

lemma hbg_hcd {g R : ℝ → ℝ → ℝ → ℝ} {θ α Nc Nz : ℝ} (hα : 0 < α)
    (hθ : θ ∈ Work.Spaces.Iθ)
    (hloc : ContDiffOn ℝ 1 (fun z : ℝ => g z θ 0) (Set.Ioi 0))
    (hbc1 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (0:ℝ))))
    (hjc1 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ 0 + q.2 * R q.1 θ 0)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ))))
    (hjet : Work.FTS.Regularity.Jet α 1 Nc R)
    (hNz0 : 0 ≤ Nz)
    (hE3 : ∀ z' ∈ Set.Ioi (0:ℝ), ∀ τ ∈ Set.Icc (0:ℝ) 1,
      |deriv (fun z'' => g z'' θ τ) z' - deriv (fun z'' => g z'' θ 0) z'| ≤ Nz * τ)
    (hRderiv : ∀ z ∈ Set.Ioi (0:ℝ), ∀ τ ∈ Set.Ioi (0:ℝ), deriv (fun s => g z θ s) τ = R z θ τ) :
    ∀ z ∈ Set.Ioi (0:ℝ), Filter.Tendsto
      (fun q : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => g q.1 θ q.2) q)
      (𝓝[Set.prod Set.univ (Set.Ioi (0:ℝ))] (z, 0))
      (𝓝 (fderiv ℝ (fun q : ℝ × ℝ => g q.1 θ 0 + q.2 * R q.1 θ 0) (z, 0))) := by
  intro z hz
  have hzpos : 0 < z := hz
  have hNc : 0 ≤ Nc := Work.FTS.Regularity.Jet.nonneg hjet
  have hVopen : IsOpen (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (0:ℝ))) := isOpen_Ioi.prod isOpen_Ioi
  have hUopen : IsOpen (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ))) := isOpen_Ioi.prod isOpen_Ioi
  set L : (ℝ × ℝ) →L[ℝ] ℝ := deriv (fun z' : ℝ => g z' θ 0) z • ContinuousLinearMap.fst ℝ ℝ ℝ
      + R z θ 0 • ContinuousLinearMap.snd ℝ ℝ ℝ with hL
  have hjfd : fderiv ℝ (fun q : ℝ × ℝ => g q.1 θ 0 + q.2 * R q.1 θ 0) (z, (0:ℝ)) = L := by
    have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ => g q.1 θ 0 + q.2 * R q.1 θ 0) (z, (0:ℝ)) :=
      (Work.FTS.RegPkgGal.R1b.hasFDerivAt_of_contDiffOn_one hUopen hjc1
        (show ((z, (0:ℝ)) : ℝ × ℝ) ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)) from
          ⟨hzpos, by norm_num⟩)).differentiableAt
    rw [Work.FTS.RegPkgGal.R1b.fderiv_eq_partials hd]
    have e1 : deriv (fun z' : ℝ => g z' θ 0 + (0:ℝ) * R z' θ 0) z
        = deriv (fun z' : ℝ => g z' θ 0) z :=
      Filter.EventuallyEq.deriv_eq (Filter.Eventually.of_forall (fun z' => by ring))
    have e2 : deriv (fun s : ℝ => g z θ 0 + s * R z θ 0) (0:ℝ) = R z θ 0 := by
      have hh : HasDerivAt (fun s : ℝ => g z θ 0 + id s * R z θ 0) (0 + 1 * R z θ 0) (0:ℝ) :=
        (hasDerivAt_const (0:ℝ) (g z θ 0)).add ((hasDerivAt_id (0:ℝ)).mul_const (R z θ 0))
      have hh2 : HasDerivAt (fun s : ℝ => g z θ 0 + s * R z θ 0) (R z θ 0) (0:ℝ) := by
        simpa using hh
      exact hh2.deriv
    rw [e1, e2]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  have hcont0 : ContinuousOn (fun z'' : ℝ => deriv (fun z' : ℝ => g z' θ 0) z'') (Set.Ioi 0) := by
    have h := hloc.continuousOn_fderiv_of_isOpen isOpen_Ioi (by norm_num)
    have h2 : ContinuousOn (fun x : ℝ => (fderiv ℝ (fun z' : ℝ => g z' θ 0) x) 1) (Set.Ioi 0) :=
      h.clm_apply (continuousOn_const (c := (1 : ℝ)))
    exact h2.congr (fun x hx => fderiv_apply_one_eq_deriv)
  obtain ⟨δ₁, hδ₁, h1⟩ := Metric.continuousOn_iff.1 hcont0 z hz (ε / 4) hε4
  have h2α : (0:ℝ) ≤ 2 ^ α := Real.rpow_nonneg (by norm_num) _
  obtain ⟨δ₂, hδ₂, h2⟩ := hbg_rpow_small (mul_nonneg hNc h2α) hα (ε := ε / 4) hε4
  have hNz1 : (0:ℝ) < Nz + 1 := by linarith
  refine ⟨min (min (min δ₁ δ₂) 1) (min (z / 2) (ε / (4 * (Nz + 1)))),
    lt_min (lt_min (lt_min hδ₁ hδ₂) one_pos) (lt_min (by linarith) (by positivity)), ?_⟩
  rintro ⟨q₁, q₂⟩ hqmem hqd
  have hq2pos : 0 < q₂ := hqmem.2
  have hnorm : ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ = max |q₁ - z| |q₂| := by
    rw [Prod.norm_def]
    simp only [Real.norm_eq_abs, Prod.fst_sub, Prod.snd_sub, sub_zero]
  have hq2le : q₂ ≤ ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ := by
    rw [hnorm]
    calc q₂ ≤ |q₂| := le_abs_self _
      _ ≤ max |q₁ - z| |q₂| := le_max_right _ _
  have hq1d : |q₁ - z| ≤ ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ := by
    rw [hnorm]; exact le_max_left _ _
  have hdd : ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ < min (min δ₁ δ₂) 1 :=
    lt_of_lt_of_le hqd (min_le_left _ _)
  have hδ₁le : ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ < δ₁ :=
    lt_of_lt_of_le hdd (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ₂le : ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ < δ₂ :=
    lt_of_lt_of_le hdd (le_trans (min_le_left _ _) (min_le_right _ _))
  have h1le : ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ < 1 :=
    lt_of_lt_of_le hdd (min_le_right _ _)
  have hqd' : ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ < min (z / 2) (ε / (4 * (Nz + 1))) :=
    lt_of_lt_of_le hqd (min_le_right _ _)
  have hz2 : ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ < z / 2 :=
    lt_of_lt_of_le hqd' (min_le_left _ _)
  have hε' : ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ < ε / (4 * (Nz + 1)) :=
    lt_of_lt_of_le hqd' (min_le_right _ _)
  have hq1pos : 0 < q₁ := by
    have h3 : |q₁ - z| < z / 2 := lt_of_le_of_lt hq1d hz2
    rw [abs_lt] at h3
    linarith [h3.1, hzpos]
  have hq2lt1 : q₂ < 1 := lt_of_le_of_lt hq2le h1le
  have hq2Icc : q₂ ∈ Set.Icc (0:ℝ) 1 := ⟨hq2pos.le, hq2lt1.le⟩
  rw [hjfd]
  have hbAt : HasFDerivAt (fun q : ℝ × ℝ => g q.1 θ q.2)
      (fderiv ℝ (fun q : ℝ × ℝ => g q.1 θ q.2) (q₁, q₂)) (q₁, q₂) :=
    Work.FTS.RegPkgGal.R1b.hasFDerivAt_of_contDiffOn_one hVopen hbc1 ⟨hq1pos, hq2pos⟩
  have hparts := Work.FTS.RegPkgGal.R1b.fderiv_eq_partials hbAt.differentiableAt
  have hbval : deriv (fun s : ℝ => g q₁ θ s) q₂ = R q₁ θ q₂ := hRderiv q₁ hq1pos q₂ hq2pos
  have hsub : fderiv ℝ (fun q : ℝ × ℝ => g q.1 θ q.2) (q₁, q₂) - L
      = (deriv (fun z' : ℝ => g z' θ q₂) q₁ - deriv (fun z' : ℝ => g z' θ 0) z)
          • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (R q₁ θ q₂ - R z θ 0) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    rw [hparts, hL, hbval]
    module
  rw [dist_eq_norm, hsub]
  refine lt_of_le_of_lt (Work.FTS.RegPkgGal.R1b.norm_smul_fst_add_smul_snd_le _ _) ?_
  have hA : |deriv (fun z' : ℝ => g z' θ q₂) q₁ - deriv (fun z' : ℝ => g z' θ 0) z|
      ≤ Nz * q₂ + ε / 4 := by
    have e3 := hE3 q₁ hq1pos q₂ hq2Icc
    have e4 : |deriv (fun z' : ℝ => g z' θ 0) q₁ - deriv (fun z' : ℝ => g z' θ 0) z| < ε / 4 := by
      refine h1 q₁ hq1pos ?_
      rw [Real.dist_eq]
      exact lt_of_le_of_lt hq1d hδ₁le
    calc |deriv (fun z' : ℝ => g z' θ q₂) q₁ - deriv (fun z' : ℝ => g z' θ 0) z|
        ≤ |deriv (fun z' : ℝ => g z' θ q₂) q₁ - deriv (fun z' : ℝ => g z' θ 0) q₁|
          + |deriv (fun z' : ℝ => g z' θ 0) q₁ - deriv (fun z' : ℝ => g z' θ 0) z| :=
          abs_sub_le _ _ _
      _ ≤ Nz * q₂ + ε / 4 := add_le_add e3 (le_of_lt e4)
  have hB : |R q₁ θ q₂ - R z θ 0| < ε / 4 := by
    have hJ := hjet.2.2 q₁ z θ θ q₂ 0 hq1pos.le hzpos.le hθ hθ hq2Icc ⟨le_refl 0, zero_le_one⟩
    have hlt : |q₁ - z| + |θ - θ| + |q₂ - 0| ≤ 2 * ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ := by
      rw [sub_self, abs_zero, add_zero, sub_zero, abs_of_pos hq2pos]
      nlinarith [hq1d, hq2le]
    have hpow : (|q₁ - z| + |θ - θ| + |q₂ - 0|) ^ α
        ≤ (2 * ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖) ^ α :=
      Real.rpow_le_rpow (by positivity) hlt hα.le
    have h2δ : (2 * ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖) ^ α ≤ (2 * δ₂) ^ α := by
      refine Real.rpow_le_rpow (by positivity) ?_ hα.le
      nlinarith [hδ₂le]
    have hfin : Nc * (2 * δ₂) ^ α < ε / 4 := by
      have h2αδ : (2 * δ₂) ^ α = 2 ^ α * δ₂ ^ α := Real.mul_rpow (by norm_num) hδ₂.le
      rw [h2αδ]
      calc Nc * (2 ^ α * δ₂ ^ α) = Nc * 2 ^ α * δ₂ ^ α := by ring
        _ < ε / 4 := h2
    calc |R q₁ θ q₂ - R z θ 0|
        ≤ Nc * (|q₁ - z| + |θ - θ| + |q₂ - 0|) ^ α := hJ
      _ ≤ Nc * (2 * ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖) ^ α :=
          mul_le_mul_of_nonneg_left hpow hNc
      _ ≤ Nc * (2 * δ₂) ^ α := mul_le_mul_of_nonneg_left h2δ hNc
      _ < ε / 4 := hfin
  have hA2 : Nz * q₂ ≤ ε / 4 := by
    have h1' : Nz * ‖((q₁, q₂) : ℝ × ℝ) - (z, (0:ℝ))‖ ≤ Nz * (ε / (4 * (Nz + 1))) :=
      mul_le_mul_of_nonneg_left hε'.le hNz0
    have h2' : Nz * (ε / (4 * (Nz + 1))) ≤ ε / 4 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    exact le_trans (mul_le_mul_of_nonneg_left hq2le hNz0) (le_trans h1' h2')
  linarith [hA, hB, hA2]

/-- **The gluing of two half-plane branches along `τ = 0`.**  If `j` is `C¹` on
`{z > 0, τ > -1}`, `b` is `C¹` on `{z > 0, τ > 0}`, `G` agrees with `j` for `τ ≤ 0` and with `b`
for `τ ≥ 0`, the one-sided Taylor expansion of `b` at `τ = 0⁺` has derivative `fderiv j`, and
`fderiv b` tends to `fderiv j` along `τ → 0⁺`, then `G` is `C¹` on `{z > 0, τ > -1}`. -/
theorem hbg_glue
    {j b G : ℝ × ℝ → ℝ}
    (hj_c1 : ContDiffOn ℝ 1 j (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ))))
    (hb_c1 : ContDiffOn ℝ 1 b (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (0:ℝ))))
    (hGj : ∀ q ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)), q.2 ≤ 0 → G q = j q)
    (hGb : ∀ q ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)), 0 ≤ q.2 → G q = b q)
    (hexp : ∀ z ∈ Set.Ioi (0:ℝ), ∀ ε > 0, ∃ δ > 0, ∀ y : ℝ × ℝ, ‖y - (z, (0:ℝ))‖ < δ → 0 ≤ y.2 →
      ‖b y - b (z, (0:ℝ)) - fderiv ℝ j (z, (0:ℝ)) (y - (z, (0:ℝ)))‖ ≤ ε * ‖y - (z, (0:ℝ))‖)
    (hcd : ∀ z ∈ Set.Ioi (0:ℝ), Filter.Tendsto (fun q : ℝ × ℝ => fderiv ℝ b q)
      (𝓝[Set.prod Set.univ (Set.Ioi (0:ℝ))] (z, 0)) (𝓝 (fderiv ℝ j (z, 0)))) :
    ContDiffOn ℝ 1 G (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ))) := by
  have hUopen : IsOpen (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ))) := isOpen_Ioi.prod isOpen_Ioi
  have hVopen : IsOpen (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (0:ℝ))) := isOpen_Ioi.prod isOpen_Ioi
  set Lc : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] ℝ :=
    fun q => if q.2 ≤ 0 then fderiv ℝ j q else fderiv ℝ b q with hLc
  have hjAt : ∀ q ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)), HasFDerivAt j (fderiv ℝ j q) q :=
    fun q hq => Work.FTS.RegPkgGal.R1b.hasFDerivAt_of_contDiffOn_one hUopen hj_c1 hq
  have hbAt : ∀ q ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (0:ℝ)), HasFDerivAt b (fderiv ℝ b q) q :=
    fun q hq => Work.FTS.RegPkgGal.R1b.hasFDerivAt_of_contDiffOn_one hVopen hb_c1 hq
  have hJcont : ContinuousOn (fun q : ℝ × ℝ => fderiv ℝ j q)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ))) :=
    hj_c1.continuousOn_fderiv_of_isOpen hUopen (by norm_num)
  have hBcont : ContinuousOn (fun q : ℝ × ℝ => fderiv ℝ b q)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (0:ℝ))) :=
    hb_c1.continuousOn_fderiv_of_isOpen hVopen (by norm_num)
  have hjEqLc : ∀ q, q.2 ≤ 0 → Lc q = fderiv ℝ j q := by
    intro q hq; rw [hLc]; simp [hq]
  have hbEqLc : ∀ q, ¬ q.2 ≤ 0 → Lc q = fderiv ℝ b q := by
    intro q hq; rw [hLc]; simp [hq]
  have hLc_cont : ContinuousOn Lc (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ))) := by
    rintro ⟨z, τ⟩ hx
    have hz : 0 < z := hx.1
    have hτm : -1 < τ := hx.2
    have hxU : (z, τ) ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)) := hx
    rcases lt_trichotomy τ 0 with h2 | h2 | h2
    · have heq : Lc =ᶠ[𝓝 ((z, τ) : ℝ × ℝ)] (fun q => fderiv ℝ j q) := by
        filter_upwards [(isOpen_Iio.preimage continuous_snd).mem_nhds h2] with q hq
        exact hjEqLc q (le_of_lt hq)
      exact ((hJcont.continuousAt (hUopen.mem_nhds hxU)).congr_of_eventuallyEq heq).continuousWithinAt
    · subst h2
      have hxU0 : (z, (0:ℝ)) ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)) := ⟨hz, by norm_num⟩
      refine ContinuousAt.continuousWithinAt ?_
      refine (Metric.tendsto_nhds).2 fun ε hε => ?_
      rw [hjEqLc (z, (0:ℝ)) le_rfl]
      have hjEv : ∀ᶠ q : ℝ × ℝ in 𝓝 (z, (0:ℝ)),
          dist (fderiv ℝ j q) (fderiv ℝ j (z, (0:ℝ))) < ε :=
        (Metric.tendsto_nhds).1 ((hJcont.continuousAt (hUopen.mem_nhds hxU0))) ε hε
      have hbEv : ∀ᶠ q : ℝ × ℝ in 𝓝 (z, (0:ℝ)), 0 < q.2 →
          dist (fderiv ℝ b q) (fderiv ℝ j (z, (0:ℝ))) < ε := by
        have h := (Metric.tendsto_nhds).1 (hcd z hz) ε hε
        rw [eventually_nhdsWithin_iff] at h
        exact h.mono (fun q hq hq2 => hq ⟨trivial, hq2⟩)
      filter_upwards [hjEv, hbEv] with q hqj hqb
      by_cases hk : 0 < q.2
      · rw [hbEqLc q (not_le.mpr hk)]
        exact hqb hk
      · rw [hjEqLc q (le_of_not_gt hk)]
        exact hqj
    · have hxV : (z, τ) ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (0:ℝ)) := ⟨hz, h2⟩
      have heq : Lc =ᶠ[𝓝 ((z, τ) : ℝ × ℝ)] (fun q => fderiv ℝ b q) := by
        filter_upwards [(isOpen_Ioi.preimage continuous_snd).mem_nhds h2] with q hq
        exact hbEqLc q (not_le.mpr hq)
      exact ((hBcont.continuousAt (hVopen.mem_nhds hxV)).congr_of_eventuallyEq heq).continuousWithinAt
  have hderiv : ∀ x ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)), HasFDerivAt G (Lc x) x := by
    rintro ⟨z, τ⟩ hx
    have hz : 0 < z := hx.1
    have hτm : -1 < τ := hx.2
    have hxU : (z, τ) ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)) := hx
    rcases lt_trichotomy τ 0 with h2 | h2 | h2
    · rw [hjEqLc _ (le_of_lt h2)]
      refine (hjAt (z, τ) hxU).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
        (isOpen_Iio.preimage continuous_snd).mem_nhds h2,
        (isOpen_Ioi.preimage continuous_snd).mem_nhds (show (-1:ℝ) < τ from hτm)] with q hq1 hq2 hq3
      exact hGj q ⟨hq1, hq3⟩ (le_of_lt hq2)
    · subst h2
      have hxU0 : (z, (0:ℝ)) ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)) := ⟨hz, by norm_num⟩
      rw [hjEqLc _ le_rfl]
      refine (hasFDerivAt_iff_isLittleO).2 ?_
      rw [Asymptotics.isLittleO_iff]
      intro c hc
      obtain ⟨δ, hδpos, hδ⟩ := hexp z hz (c / 2) (by positivity)
      have hjEv : ∀ᶠ y : ℝ × ℝ in 𝓝 (z, (0:ℝ)),
          ‖j y - j (z, (0:ℝ)) - fderiv ℝ j (z, (0:ℝ)) (y - (z, (0:ℝ)))‖
            ≤ (c / 2) * ‖y - (z, (0:ℝ))‖ := by
        have h := (hjAt (z, (0:ℝ)) hxU0).isLittleO
        rw [Asymptotics.isLittleO_iff] at h
        exact h (by positivity)
      filter_upwards [hjEv, Metric.ball_mem_nhds ((z, (0:ℝ)) : ℝ × ℝ) hδpos,
        (isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
        (isOpen_Ioi.preimage continuous_snd).mem_nhds (show (-1:ℝ) < (0:ℝ) by norm_num)]
        with y hyj hyball hy1 hy3
      have hball' : ‖y - (z, (0:ℝ))‖ < δ := by
        simpa [Metric.mem_ball, dist_eq_norm] using hyball
      have hr : (0:ℝ) ≤ ‖y - (z, (0:ℝ))‖ := norm_nonneg _
      by_cases hk : 0 ≤ y.2
      · have hyU : y ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)) := ⟨hy1, hy3⟩
        have hGy : G y = b y := hGb y hyU hk
        have hGx : G (z, (0:ℝ)) = b (z, (0:ℝ)) := hGb _ hxU0 le_rfl
        rw [hGy, hGx]
        refine le_trans (hδ y hball' hk) ?_
        nlinarith [hr, hc]
      · have hk' : y.2 < 0 := lt_of_not_ge hk
        have hyU : y ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1:ℝ)) := ⟨hy1, hy3⟩
        have hGy : G y = j y := hGj y hyU (le_of_lt hk')
        have hGx : G (z, (0:ℝ)) = j (z, (0:ℝ)) := hGj _ hxU0 le_rfl
        rw [hGy, hGx]
        refine le_trans hyj ?_
        nlinarith [hr, hc]
    · rw [hbEqLc _ (not_le.mpr h2)]
      refine (hbAt (z, τ) ⟨hz, h2⟩).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds hz,
        (isOpen_Ioi.preimage continuous_snd).mem_nhds h2,
        (isOpen_Ioi.preimage continuous_snd).mem_nhds (show (-1:ℝ) < τ from hτm)]
        with q hq1 hq2 hq3
      exact hGb q ⟨hq1, hq3⟩ (le_of_lt hq2)
  rw [show (1 : WithTop ℕ∞) = (0 : WithTop ℕ∞) + 1 from rfl]
  refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hUopen.uniqueDiffOn).2
    ⟨?_, Lc, ?_, ?_⟩
  · intro h; exact absurd h (by simp)
  · exact contDiffOn_zero.mpr hLc_cont
  · intro x hx; exact (hderiv x hx).hasFDerivWithinAt

end Work.FTS_RegExport.RXR1
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.L12fAux.L12f_C1Jet_hsupp_note =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXR5L.L12fAux

set_option autoImplicit false


end Work.FTS_RegExport.RXR5L.L12fAux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Defs` — the logarithmic coordinates of RX-T

`cz s = eˢ` and `cth ψ = arctan(e^ψ)` put the self-similar quadrant `(0,∞) × (0,π/2)` in
bijection with `ℝ²`; in these coordinates the transport coefficients of `(E)` are bounded and
the weight ratio `φ = u/ω` satisfies a first-order transport equation with bounded
coefficients (see `RXT.Pullback`).  This file collects the definitions together with the
elementary facts about the weight `ω α z θ = z²(sinθcos²θ)^α/(1+z)²` that they need.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

/-! ## §1 The logarithmic coordinates and the pulled-back unknown -/

/-! ### The angular coordinate `ψ ↦ arctan (e^ψ)` -/

theorem arctan_exp_mem (ψ : ℝ) : 0 < Real.arctan (Real.exp ψ) ∧ Real.arctan (Real.exp ψ) < Real.pi / 2 :=
  logcoord_facts.1 ψ

theorem sin_two_arctan_exp_pos (ψ : ℝ) : 0 < Real.sin (2 * Real.arctan (Real.exp ψ)) :=
  logcoord_facts.2.1 ψ

theorem hasDerivAt_arctan_exp (ψ : ℝ) :
    HasDerivAt (fun ψ' => Real.arctan (Real.exp ψ'))
      (Real.sin (2 * Real.arctan (Real.exp ψ)) / 2) ψ :=
  logcoord_facts.2.2.1 ψ

theorem exists_exp (z : ℝ) (hz : 0 < z) : ∃ s : ℝ, Real.exp s = z :=
  logcoord_facts.2.2.2.1 z hz

theorem exists_arctan_exp (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < Real.pi / 2) :
    ∃ ψ : ℝ, Real.arctan (Real.exp ψ) = θ :=
  logcoord_facts.2.2.2.2.1 θ hθ hθπ

theorem sin_two_pos_of_mem {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi / 2) :
    0 < Real.sin (2 * θ) :=
  logcoord_facts.2.2.2.2.2.1 θ hθ hθπ

theorem c2m_abs_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 :=
  logcoord_facts.2.2.2.2.2.2 θ

/-- The radial logarithmic coordinate `s = log z`. -/
def cz (s : ℝ) : ℝ := Real.exp s

/-- The angular logarithmic coordinate `ψ = log (tan θ)`. -/
def cth (ψ : ℝ) : ℝ := Real.arctan (Real.exp ψ)

theorem cz_pos (s : ℝ) : 0 < cz s := Real.exp_pos s

theorem cth_pos (ψ : ℝ) : 0 < cth ψ := (arctan_exp_mem ψ).1

theorem cth_lt (ψ : ℝ) : cth ψ < Real.pi / 2 := (arctan_exp_mem ψ).2

theorem cth_sin_two_pos (ψ : ℝ) : 0 < Real.sin (2 * cth ψ) := sin_two_arctan_exp_pos ψ

/-- The weight of the pulled-back unknown. -/
def om (α s ψ : ℝ) : ℝ := Work.FTS.RegExportIface.ω α (cz s) (cth ψ)

theorem om_pos {α s ψ : ℝ} (hα : 0 < α) : 0 < om α s ψ :=
  (omega_facts α hα).1 (cz s) (cth ψ) (cz_pos s) (cth_pos ψ) (cth_lt ψ)

/-- The pulled-back unknown `φ = u(z,θ,τ)/ω(z,θ)` in the logarithmic coordinates. -/
def phi (α : ℝ) (u : ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ :=
  fun s ψ τ => u (cz s) (cth ψ) τ / om α s ψ







/-! ## §2 The pull-back of the equation to the logarithmic coordinates -/

/-- The domain `(0,∞) × (0,π/2) × [0,S]` on which `u` is `C¹`. -/
def dom (S : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)

theorem hasDerivAt_cz (s : ℝ) : HasDerivAt cz (cz s) s := Real.hasDerivAt_exp s

theorem hasDerivAt_cth (ψ : ℝ) : HasDerivAt cth (Real.sin (2 * cth ψ) / 2) ψ :=
  hasDerivAt_arctan_exp ψ

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.VPDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- **The sup-bounds half of `RegExportIface.VelPkg`** (REVIEW F3a `dbnd` and its companions).
Fields are verbatim copies; this is what StreamBdry (SB4) consumes. -/
structure VelPkgSup (αG : ℝ) (μ : ℝ → ℝ) (G Φ : Fam) (S : ℝ) : Prop where
  bnd : ∃ M : ℝ, ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ →
    |Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ| ≤ M ∧
      |Work.FTS.RegExportIface.Vθ7 αG Φ z θ τ| ≤ M * Real.sin (2 * θ) ∧
      |Work.FTS.RegExportIface.cs7 αG μ G Φ z θ τ| ≤ M
  vz0 : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ →
    0 ≤ Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ
  vth_ends : ∀ z τ, 0 < z → 0 ≤ τ →
    Work.FTS.RegExportIface.Vθ7 αG Φ z 0 τ = 0 ∧
      Work.FTS.RegExportIface.Vθ7 αG Φ z (π / 2) τ = 0
  dbnd : ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ, 0 < z → 0 < θ →
    θ < π / 2 →
    |Work.Spaces.mixed j i (fun z θ => Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ) z θ| ≤ M ∧
    |Work.Spaces.mixed j i (fun z θ => Work.FTS.RegExportIface.Vθ7 αG Φ z θ τ
      / Real.sin (2 * θ)) z θ| ≤ M ∧
    |Work.Spaces.mixed j i (fun z θ => Work.FTS.RegExportIface.cs7 αG μ G Φ z θ τ) z θ| ≤ M ∧
    |Work.Spaces.pth (fun z θ => Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ) z θ| ≤ M
  cont : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      (Work.FTS.RegExportIface.Vz7 αG μ G Φ p.1 p.2.1 p.2.2,
        Work.FTS.RegExportIface.Vθ7 αG Φ p.1 p.2.1 p.2.2,
        Work.FTS.RegExportIface.cs7 αG μ G Φ p.1 p.2.1 p.2.2))
    (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) (π / 2) ×ˢ Set.Icc (0:ℝ) S)

/-- **The endpoint / `Φ̃`-conductor half of `RegExportIface.VelPkg`**: `C²` of the stream
function, the `O(z)` vanishing `vanish0` (F3a) and `vanishK`, and the axis condition
`∂_θΦ̃(z,π/2) = 0` (F2.2).  This is the half shared with StreamBdry's `hΦaxis`. -/
structure VelPkgEnd (αG : ℝ) (G Φ : Fam) (S : ℝ) : Prop where
  c2 : ∀ τ ∈ Icc (0:ℝ) S,
    ContDiffOn ℝ 2 (Function.uncurry (slice Φ τ)) Work.FTS.EllipticEst.Q0
  vanish0 : ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
    ∀ Q ∈ ({(Work.Construction.Rop αG (Work.FTS.RegExportIface.phiTil αG G Φ τ)),
        Work.Construction.Vop (Work.FTS.RegExportIface.phiTil αG G Φ τ),
        fun z θ => Work.Construction.Uop αG (Work.FTS.RegExportIface.phiTil αG G Φ τ) z θ
          / Real.sin (2 * θ)} : Set (ℝ → ℝ → ℝ)),
      |Q z θ| ≤ M * min z 1 ∧ |Work.Spaces.Dz Q z θ| ≤ M * min z 1 ∧
        |Work.Spaces.Dth Q z θ| ≤ M * min z 1
  vanishK : ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ z, 0 < z →
    |Work.Construction.FK (slice G τ) z| + |Work.Construction.L12 (slice G τ) z| ≤ M * min z 1
  axis : ∀ τ ∈ Icc (0:ℝ) S, ∀ z, 0 < z →
    Work.Spaces.pth (Work.FTS.RegExportIface.phiTil αG G Φ τ) z (π / 2) = 0

/- `VelPkgSup.toVelPkg` (the glue of the two halves into the old `VelPkg` with `axis` and the
closed-θ `bnd`/`cont`) was REMOVED 2026-10-11 by the lead's install of the repaired `VelPkg`
(`cbc/fts_velpkg_fix.md` + REVIEW FIX 1): the repaired `VelPkg` = `VelPkgOpen` + `thLip`, with no
`axis` field, so the old glue no longer typechecks. Snapshot:
`~/snapshots/fts_velpkg_fix/Submission/Work/FTS_RegExport/VPDefs.lean`. -/

end Work.FTS_RegExport
end
end
