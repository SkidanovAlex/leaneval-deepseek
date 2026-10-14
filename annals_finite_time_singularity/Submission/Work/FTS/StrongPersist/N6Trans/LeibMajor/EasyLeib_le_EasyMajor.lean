import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Have
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.A_sq_prod_le
import Submission.Work.FTS.EllipticEst.Final.ReHome.H2W_slot20_bound
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.SliceKit
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceBounds
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.LocDataExt.Final
import Submission.Work.FTS.LocDataExt.Zfar5
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.N4Fields.AngSmoothIntHelpers
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.Nonlinear.n4norm_exists
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Assembly6
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.ExcBoundQ
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.T1EasyContQ
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.H2W.weakSliceContinuousKit
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.V_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (RegQ)

set_option autoImplicit false

/-! ## A small helper -/


/-! ## The one-sided norm comparison of the three slots with the next level

This is the `normSub` field of `Assembly.StepReg2` (`Assembly/StepReg2_all.lean`), repeated
here because that module pulls in the elliptic certificates of the a-priori chapter, whose
build is independent of the coercivity layer. -/



/-! ## The lower bound (`lo`) -/


/-! ## The upper bound (`up`) -/



/-! ## The `D_z`-clause: auxiliary estimates

The two tools below turn the paper's `z`-integration by parts (in its integrated form
`Coer1.wip_L_self_Q`) into a bound for the pairing `⟨D_z u, u⟩` of a slot with itself. -/

/-- The triangle inequality for four real numbers. -/
theorem abs_lin4 (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  linarith

/-- `wip` only depends on its weight through the pointwise values. -/
theorem wip_weight_congr {ρ ρ' A B : Fn} (h : ∀ z θ, ρ z θ = ρ' z θ) :
    Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ' A B := by
  rw [Work.Coercivity.wip, Work.Coercivity.wip]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [h z θ]

/-- `|c₁ a + c₂ b + c₃ c + c₄ d| ≤ c₁|a| + c₂|b| + c₃|c| + c₄|d|` for positive
coefficients. -/
theorem abs_lin4_coef (c₁ c₂ c₃ c₄ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hc₄ : 0 < c₄) (a b c d : ℝ) :
    |c₁ * a + c₂ * b + c₃ * c + c₄ * d|
      ≤ c₁ * |a| + c₂ * |b| + c₃ * |c| + c₄ * |d| := by
  have h := abs_lin4 (c₁ * a) (c₂ * b) (c₃ * c) (c₄ * d)
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hc₁, abs_of_pos hc₂, abs_of_pos hc₃,
    abs_of_pos hc₄] at h
  exact h

/-- The triangle inequality with positive coefficients, three terms. -/
theorem abs_lin3_coef (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (a b c : ℝ) :
    |a + c₁ * b + c₂ * c| ≤ |a| + c₁ * |b| + c₂ * |c| := by
  have h1 := abs_add_le (a + c₁ * b) (c₂ * c)
  have h2 := abs_add_le a (c₁ * b)
  have e1 : |c₁ * b| = c₁ * |b| := by rw [abs_mul, abs_of_pos hc₁]
  have e2 : |c₂ * c| = c₂ * |c| := by rw [abs_mul, abs_of_pos hc₂]
  rw [e1] at h2
  rw [e2] at h1
  linarith

/-- The `Rho`-weight written with the explicit angular power. -/
theorem wip_Rho_eq (β : ℝ) (A B : Fn) :
    Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-β)) A B
      = Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho β) A B := by
  refine wip_weight_congr (fun z θ => ?_)
  simp only [Work.FTS.CoercivityFix.Coer1.Rho, Work.FTS.CoercivityFix.Coer1.sig]





/-- `wip` is a congruence in its first argument, almost everywhere. -/
theorem wip_congr_ae' {ρ g₁ g₁' g₂ : Fn}
    (h : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), g₁ z θ = g₁' z θ) :
    Work.Coercivity.wip ρ g₁ g₂ = Work.Coercivity.wip ρ g₁' g₂ := by
  rw [Work.Coercivity.wip, Work.Coercivity.wip]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [h] with z hz
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hz] with θ hθ
  rw [hθ]







end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.V_core =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Assembly/V_core.lean` — the five algebraic clauses of `IP4`

`IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α` is the paper's recursion
`HkIPStep c₁'' c₂'' (HkIPStep c₁' c₂' (HkIPStep c₁ c₂ (H1IP α)))` of `Assembly/Defs.lean`.
This file delivers the five *level-`4`* clauses of the corrected obligation
`Work.FTS.Nonlin.UnifIP` (`Submission/Work/FTS/Vocab.lean`) for it:

* **symmetry** for all profiles `(f,g)` (no membership): `H1IP` is symmetric because the
  integrand is literally symmetric in its two arguments, and `HkIPStep` inherits symmetry
  with no hypothesis at all (`vc_symm`);
* **additivity** and **congruence on the open quadrant** on the class `RegQ α 4`, which are
  the `add` / `congr` clauses of `Assembly.Comm2 α 4 (IP4 ...)` (`Comm2_levels`, built from
  the base `H1IP_core_Q` through three applications of `Comm2_succ`);
* **homogeneity** in the first argument for all profiles (no membership): `D_θ` and `D_z`
  are scalar homogeneous *unconditionally* (`Work.Coercivity.Dth_smul`, `Dz_smul`), and
  `H1IP` is unconditionally homogeneous (`Work.Coercivity.H1IP_homog`), so `HkIPStep`
  inherits homogeneity (`vc_smul`);
* **nonnegativity of the diagonal** for all profiles, from the pointwise nonnegativity of
  `H1IP`'s integrand (`Work.Coercivity.H1IP_nonneg`) and the nonnegativity of the step
  coefficients (`vc_nonneg`).
-/

namespace Work.FTS.CoercivityFix.Assembly

open Work.FTS.Galerkin (Fn)

/-! ## The three clauses inherited by the recursion `HkIPStep c₁ c₂` -/

/-- **Symmetry is inherited by the recursion.**  If `IP` is symmetric then so is
`HkIPStep c₁ c₂ IP`: the three summands are `IP f g`, `IP (D_θ f) (D_θ g)` and
`IP (D_z f) (D_z g)`, and each is symmetric by hypothesis.  No regularity is needed. -/
theorem vc_symm {c₁ c₂ : ℝ} {IP : Fn → Fn → ℝ} (h : ∀ f g : Fn, IP f g = IP g f) :
    ∀ f g : Fn, Work.Coercivity.HkIPStep c₁ c₂ IP f g
      = Work.Coercivity.HkIPStep c₁ c₂ IP g f := by
  intro f g
  simp only [Work.Coercivity.HkIPStep, h f g,
    h (Work.Spaces.Dth f) (Work.Spaces.Dth g), h (Work.Spaces.Dz f) (Work.Spaces.Dz g)]

/-- **Homogeneity in the first argument is inherited by the recursion.**  The two inner
pairings see the derivatives of `fun z θ => c * f z θ`, and `D_θ`, `D_z` commute
unconditionally with scalar multiplication (`Work.Coercivity.Dth_smul`, `Dz_smul`). -/
theorem vc_smul {c₁ c₂ c : ℝ} {IP : Fn → Fn → ℝ}
    (h : ∀ u v : Fn, IP (fun z θ => c * u z θ) v = c * IP u v) :
    ∀ f g : Fn, Work.Coercivity.HkIPStep c₁ c₂ IP (fun z θ => c * f z θ) g
      = c * Work.Coercivity.HkIPStep c₁ c₂ IP f g := by
  intro f g
  simp only [Work.Coercivity.HkIPStep]
  rw [Work.Coercivity.Dth_smul, Work.Coercivity.Dz_smul, h f g,
    h (Work.Spaces.Dth f) (Work.Spaces.Dth g), h (Work.Spaces.Dz f) (Work.Spaces.Dz g)]
  ring

/-- **Nonnegativity of the diagonal is inherited by the recursion**, with nonnegative step
coefficients: the three summands are `IP f f`, `c₁·IP (D_θ f) (D_θ f)` and
`c₂·IP (D_z f) (D_z f)`. -/
theorem vc_nonneg {c₁ c₂ : ℝ} (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) {IP : Fn → Fn → ℝ}
    (h : ∀ u : Fn, 0 ≤ IP u u) :
    ∀ f : Fn, 0 ≤ Work.Coercivity.HkIPStep c₁ c₂ IP f f := by
  intro f
  have h0 : 0 ≤ IP f f := h f
  have h1 : 0 ≤ IP (Work.Spaces.Dth f) (Work.Spaces.Dth f) := h _
  have h2 : 0 ≤ IP (Work.Spaces.Dz f) (Work.Spaces.Dz f) := h _
  have hm1 : 0 ≤ c₁ * IP (Work.Spaces.Dth f) (Work.Spaces.Dth f) := mul_nonneg h₁ h1
  have hm2 : 0 ≤ c₂ * IP (Work.Spaces.Dz f) (Work.Spaces.Dz f) := mul_nonneg h₂ h2
  simp only [Work.Coercivity.HkIPStep]
  linarith

/-! ## The five clauses of `IP4` -/


end Work.FTS.CoercivityFix.Assembly
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Coer1T.coer1_LGammaT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false


end Work.FTS.CoercivityFix.Coer1T
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.RadSAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2pkg

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The open half-line `(0,∞)`. -/
abbrev IoiA : Set ℝ := Set.Ioi (0 : ℝ)

/-! ## The `D_z`-iterates of `Qang f 0` -/



/-! ## Differentiability of the iterates of products and sums -/

/-- `D_z^c` of a product is differentiable on `(0,∞)` when both factors' iterates are. -/
theorem differentiableAt_dzdIter_mul_of {j : ℕ} {u v : ℝ → ℝ}
    (hu : ∀ c ≤ j, ∀ z ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter c u) z)
    (hv : ∀ c ≤ j, ∀ z ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter c v) z)
    {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (Work.Elliptic.DzdIter j (fun z => u z * v z)) z := by
  have hub : ∀ c < j, ∀ z' ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter c u) z' :=
    fun c hc => hu c (le_of_lt hc)
  have hvb : ∀ c < j, ∀ z' ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter c v) z' :=
    fun c hc => hv c (le_of_lt hc)
  have hev : Work.Elliptic.DzdIter j (fun z => u z * v z) =ᶠ[𝓝 z]
      (fun z' => ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
        * (Work.Elliptic.DzdIter b u z' * Work.Elliptic.DzdIter (j - b) v z')) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz j u v hub hvb z' hz'
  have hdiff : DifferentiableAt ℝ (fun z' : ℝ => ∑ b ∈ Finset.range (j + 1),
      (j.choose b : ℝ) * (Work.Elliptic.DzdIter b u z' * Work.Elliptic.DzdIter (j - b) v z')) z := by
    refine DifferentiableAt.fun_sum fun b hb => ?_
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hjb : j - b ≤ j := Nat.sub_le _ _
    exact (differentiableAt_const _).mul ((hu b hbj z hz).mul (hv (j - b) hjb z hz))
  exact hdiff.congr_of_eventuallyEq hev

/-- `D_z^j` of a sum is differentiable on `(0,∞)` when both summands' iterates are. -/
theorem differentiableAt_dzdIter_add_of {j : ℕ} {u v : ℝ → ℝ}
    (hu : ∀ b ≤ j, ∀ z ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter b u) z)
    (hv : ∀ b ≤ j, ∀ z ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter b v) z)
    {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (Work.Elliptic.DzdIter j (fun z => u z + v z)) z := by
  induction j with
  | zero =>
      have h := (hu 0 le_rfl z hz).add (hv 0 le_rfl z hz)
      change DifferentiableAt ℝ (fun z' => u z' + v z') z
      exact h
  | succ k ih =>
      have hku : ∀ b ≤ k, ∀ z' ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter b u) z' :=
        fun b hb => hu b (by omega)
      have hkv : ∀ b ≤ k, ∀ z' ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter b v) z' :=
        fun b hb => hv b (by omega)
      have hub : ∀ b < k, ∀ z' ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter b u) z' :=
        fun b hb => hu b (by omega)
      have hvb : ∀ b < k, ∀ z' ∈ IoiA, DifferentiableAt ℝ (Work.Elliptic.DzdIter b v) z' :=
        fun b hb => hv b (by omega)
      have hfun : (fun z' => z' * deriv (Work.Elliptic.DzdIter k u) z'
              + z' * deriv (Work.Elliptic.DzdIter k v) z')
          =ᶠ[𝓝 z] (fun z' => z' * deriv (Work.Elliptic.DzdIter k (fun z => u z + v z)) z') := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        have h1 : Work.Elliptic.DzdIter k (fun z => u z + v z)
            =ᶠ[𝓝 z'] (Work.Elliptic.DzdIter k u + Work.Elliptic.DzdIter k v) := by
          filter_upwards [isOpen_Ioi.mem_nhds hz'] with w hw
          exact Work.FTS.CoercivityFix.Transfer.E1Parts.DzdIter_add_of_diff k u v hub hvb w hw
        rw [h1.deriv_eq, deriv_add (hu k (by omega) z' hz') (hv k (by omega) z' hz')]
        ring
      have h2u : Work.Elliptic.DzdIter (k + 1) u
          = fun z' => z' * deriv (Work.Elliptic.DzdIter k u) z' := by
        rw [Work.Elliptic.DzdIter_succ]; rfl
      have h2v : Work.Elliptic.DzdIter (k + 1) v
          = fun z' => z' * deriv (Work.Elliptic.DzdIter k v) z' := by
        rw [Work.Elliptic.DzdIter_succ]; rfl
      have hA : DifferentiableAt ℝ (fun z' => z' * deriv (Work.Elliptic.DzdIter k u) z') z := by
        rw [← h2u]; exact hu (k + 1) (by omega) z hz
      have hB : DifferentiableAt ℝ (fun z' => z' * deriv (Work.Elliptic.DzdIter k v) z') z := by
        rw [← h2v]; exact hv (k + 1) (by omega) z hz
      show DifferentiableAt ℝ (fun z' => z' * deriv (Work.Elliptic.DzdIter k (fun z => u z + v z)) z') z
      exact (hA.add hB).congr_of_eventuallyEq hfun.symm

/-! ## `radS` as an explicit three-term sum on `(0,∞)` -/


/-! ## Smoothness of the coefficient profiles -/

/-- `ampA α` is `C^5` on `(0,∞)` (it is the rational function `2z/(c(1+z)²)`). -/
theorem contDiffOn_ampA_five (α : ℝ) :
    ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampA α) IoiA := by
  rcases eq_or_ne (Work.Spaces.c α) 0 with hc | hc
  · have h0 : Work.FTS.CoercivityFix.Transfer.ampA α = fun _ : ℝ => (0 : ℝ) := by
      funext z
      simp only [Work.FTS.CoercivityFix.Transfer.ampA, hc, zero_mul, div_zero]
    rw [h0]
    exact contDiffOn_const
  · have hnum : ContDiffOn ℝ 5 (fun z : ℝ => 2 * z) IoiA :=
      contDiffOn_const.mul contDiffOn_id
    have hden : ContDiffOn ℝ 5 (fun z : ℝ => Work.Spaces.c α * (1 + z) ^ 2) IoiA :=
      contDiffOn_const.mul ((contDiffOn_const.add contDiffOn_id).pow 2)
    have hne : ∀ z ∈ IoiA, Work.Spaces.c α * (1 + z) ^ 2 ≠ 0 := by
      intro z hz
      have h1 : (0 : ℝ) < z := hz
      exact mul_ne_zero hc (pow_ne_zero 2 (by linarith))
    show ContDiffOn ℝ 5 (fun z : ℝ => 2 * z / (Work.Spaces.c α * (1 + z) ^ 2)) IoiA
    exact hnum.div hden hne

/-- `ampB α` is `C^5` on `(0,∞)`. -/
theorem contDiffOn_ampB_five (α : ℝ) :
    ContDiffOn ℝ 5 (Work.FTS.CoercivityFix.Transfer.ampB α) IoiA := by
  have hnum : ContDiffOn ℝ 5 (fun z : ℝ => 2 * z ^ 2) IoiA :=
    contDiffOn_const.mul (contDiffOn_id.pow 2)
  have hden : ContDiffOn ℝ 5 (fun z : ℝ => (1 + z) ^ 3) IoiA :=
    (contDiffOn_const.add contDiffOn_id).pow 3
  have hne : ∀ z ∈ IoiA, (1 + z) ^ 3 ≠ 0 := by
    intro z hz
    have h1 : (0 : ℝ) < z := hz
    exact pow_ne_zero 3 (by linarith)
  show ContDiffOn ℝ 5 (fun z : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) IoiA
  exact hnum.div hden hne

/-- Every iterate of order `c` of a `C^{c+1}` function is differentiable on `(0,∞)`. -/
theorem differentiableAt_dzdIter_of_contDiffOn_general {N : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ N u IoiA) {c : ℕ} (hc : c + 1 ≤ N) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (Work.Elliptic.DzdIter c u) z := by
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
  exact Work.FTS.CoercivityFix.Transfer.E1Parts.differentiableAt_Zop_iter_of_contDiffOn
    (b := c) (hu := hu.of_le (Nat.cast_le.mpr hc)) hz

/-- Every `D_z`-iterate up to order `4` of a `C^5` function is differentiable on `(0,∞)`. -/
theorem differentiableAt_dzdIter_of_contDiffOn_five {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 5 u IoiA) {c : ℕ} (hc : c ≤ 4) {z : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (Work.Elliptic.DzdIter c u) z := by
  have hc5 : c + 1 ≤ 5 := by omega
  exact differentiableAt_dzdIter_of_contDiffOn_general (c := c) (N := 5) hu hc5 hz

/-- `D_z^c` commutes with multiplication by a constant. -/
theorem dzdIter_const_mul (c : ℝ) (j : ℕ) (u : ℝ → ℝ) :
    Work.Elliptic.DzdIter j (fun z => c * u z)
      = fun z => c * Work.Elliptic.DzdIter j u z := by
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter,
    Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
  exact Work.FTS.CoercivityFix.Transfer.E2pkg.Zop_iter_const_mul j c u

/-- `D_z^c` commutes with negation. -/
theorem dzdIter_neg (j : ℕ) (u : ℝ → ℝ) :
    Work.Elliptic.DzdIter j (fun z => -u z) = fun z => -Work.Elliptic.DzdIter j u z := by
  rw [show (fun z => -u z) = fun z => (-1 : ℝ) * u z from by funext z; ring,
    dzdIter_const_mul]
  funext z; ring

end Work.FTS.CoercivityFix.Transfer.E2pkg
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The two null sets -/

/-- Almost every angle of `Iθ` lies in the open interval `(0, π/2)`: `Icc 0 (π/2)` and
`Ioo 0 (π/2)` coincide up to the null set of the two endpoints. -/
theorem ae_mem_Ioo_Iθ_Q0Sm :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  have hset : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    refine MeasureTheory.Measure.restrict_congr_set ?_
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Ioo_ae_eq_Icc.symm
  rw [hset]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- Almost every radius of `Iz = [0, ∞)` is positive: `Ici 0` and `Ioi 0` coincide up to the
null set `{0}`. -/
theorem ae_mem_Ioi_Iz_Q0Sm :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ∈ Set.Ioi (0 : ℝ) := by
  have hset : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.Measure.restrict_congr_set ?_
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Ioi_ae_eq_Ici.symm
  rw [hset]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

/-! ## The integrated estimate -/

theorem HkSq_Dz_le_Q0Sm (α : ℝ) (m : ℕ) {X : ℝ → ℝ → ℝ}
    (h : Work.FTS.CoercivityFix.Transfer.Q0Sm (m + 1) X)
    (hm : Work.Spaces.HkMem α (m + 1) X) :
    Work.Spaces.HkSq α m (Work.Spaces.Dz X) ≤ Work.Spaces.HkSq α (m + 1) X := by
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  -- the outer (radial) comparison
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α m (Work.Spaces.Dz X) z θ) hm.2 ?_
  -- for a.e. `z ∈ Iz` the radius is positive, hence the pointwise domination applies a.e. in θ
  refine ae_mem_Ioi_Iz_Q0Sm.mono fun z hz => ?_
  have hzI : z ∈ Work.Spaces.Iz := by
    simp only [Work.Spaces.Iz, Set.mem_Ici]
    exact le_of_lt hz
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun θ =>
      Work.Spaces.HkIntegrand_nonneg α m (Work.Spaces.Dz X) z θ)
    (hm.1 z hzI) ?_
  exact ae_mem_Ioo_Iθ_Q0Sm.mono fun θ hθ =>
    HkIntegrand_Dz_le_succ_Q0Sm α m h z θ ⟨hz, hθ⟩

end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.EllSol.Shift2Flat.niceSlotBoundHE =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Shift2Flat

open MeasureTheory Set Filter
open scoped Real Topology ContDiff ENNReal
open Work.Spaces
open Work.FTS.EllSol.FlatFT
open Work.FTS.EllSol.SpecAux

noncomputable section

set_option maxHeartbeats 4000000

local notation "thEta" => Work.FTS.EllipticEst.thEta

/-- The left-hand Plancherel identification of the shifted slot, with the *heavy* angular
weight `wE`: the `ξ`-integral of `μ(ξ) = (2πξ)² + b²` times the slice energy of `∂_θu` equals
the `(t,θ)`-integral of `(∂_θ(∂_t - b)u)² wE`.  (This is `hidShiftLhs` with `wA α` replaced
by `wE`.) -/
theorem hidShiftLhsE {u : ℝ → ℝ → ℝ} {b : ℝ} (hg : NiceFlat u)
    (hJ : ∀ ξ : ℝ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => ‖slice (pth u) ξ θ‖ ^ 2 * wE θ) Iθ)
    (hplanch : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      MeasureTheory.Integrable (fun ξ : ℝ => muW b ξ * ‖slice (pth u) ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, muW b ξ * ‖slice (pth u) ξ θ‖ ^ 2)
        = ∫ t : ℝ, (pth (pz u) t θ - b * pth u t θ) ^ 2) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal (muW b ξ
        * ∫ θ in Iθ, ‖slice (pth u) ξ θ‖ ^ 2 * wE θ))
      = ∫⁻ p in Set.univ ×ˢ Iθ, ENNReal.ofReal
          ((pth (pz u) p.1 p.2 - b * pth u p.1 p.2) ^ 2 * wE p.2) := by
  obtain ⟨M, hM0, hM⟩ := niceFlat_supp hg
  have hcd_u : ContDiffOn ℝ 2 (Function.uncurry u) flStrip := hg.1
  have hcd_pth : ContDiffOn ℝ 1 (Function.uncurry (pth u)) flStrip :=
    pth_contDiffOn_succ flStrip_isOpen hcd_u
  have hcd_pz : ContDiffOn ℝ 1 (Function.uncurry (pz u)) flStrip :=
    pz_contDiffOn_succ flStrip_isOpen hcd_u
  have hsupp_pz : ∀ t θ : ℝ, M < |t| → pz u t θ = 0 := supp_pz hM
  have hsupp_pth : ∀ t θ : ℝ, M < |t| → pth u t θ = 0 := supp_pth hM
  have hsupp_pthpz : ∀ t θ : ℝ, M < |t| → pth (pz u) t θ = 0 :=
    fun t θ ht => pth_eq_zero_of_forall (fun θ' => hsupp_pz t θ' ht)
  have hsupp_lhsψ : ∀ t θ : ℝ, M < |t| → pth (pz u) t θ - b * pth u t θ = 0 :=
    fun t θ ht => by rw [hsupp_pthpz t θ ht, hsupp_pth t θ ht]; ring
  have hcont_lhsψ : ContinuousOn
      (Function.uncurry (fun t θ : ℝ => pth (pz u) t θ - b * pth u t θ)) flStrip :=
    ((pth_contDiffOn_succ flStrip_isOpen hcd_pz).continuousOn).sub
      (hcd_pth.continuousOn.const_mul b)
  have hsl_pth : ContinuousOn (fun p : ℝ × ℝ => slice (pth u) p.1 p.2) flStrip :=
    continuousOn_slice_joint hcd_pth.continuousOn ⟨M, hM0, hsupp_pth⟩
  have hφ : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Iθ),
      MeasureTheory.Integrable (fun t : ℝ => (pth (pz u) t θ - b * pth u t θ) ^ 2) :=
    ae_mem_Ioo_Iθ.mono (fun θ hθ => integrable_sq_slice hM0 hcont_lhsψ hsupp_lhsψ hθ)
  exact lintegral_slice_plancherel (pth u) (fun t θ : ℝ => pth (pz u) t θ - b * pth u t θ)
    (muW b) wE (muW_nonneg b) (fun θ hθ => wE_nonneg hθ) hJ hφ hplanch
    (aemeasurable_ofReal_weight_mul hsl_pth (measurable_muW b) measurable_wE)
    (aemeasurable_ofReal_sq_mul_snd hcont_lhsψ measurable_wE)

theorem niceSlotBoundHE {Cc : ℝ} (hCcpos : 0 < Cc)
    (hCc : ∀ F : ℝ → ℂ, ContDiffOn ℝ 2 F (Set.Ioo 0 (Real.pi / 2)) → F 0 = 0 →
      F (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn (fun θ : ℝ => ‖F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => ‖deriv F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => ‖deriv (deriv F) θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, ‖deriv F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) ≤
        Cc * ((∫ θ in Work.Spaces.Iθ, ‖F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) +
          Real.sqrt ((∫ θ in Work.Spaces.Iθ, ‖F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) *
            (∫ θ in Work.Spaces.Iθ, ‖deriv (deriv F) θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ))))
    (b : ℝ) (u : ℝ → ℝ → ℝ) (hg : Work.FTS.EllSol.FlatFT.NiceFlat u)
    (hplanch1 : ∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
      MeasureTheory.Integrable (fun ξ : ℝ => Work.FTS.EllSol.SpecAux.muW b ξ * ‖Work.FTS.EllSol.FlatFT.slice u ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, Work.FTS.EllSol.SpecAux.muW b ξ * ‖Work.FTS.EllSol.FlatFT.slice u ξ θ‖ ^ 2) = ∫ t : ℝ, (Work.Spaces.pz u t θ - b * u t θ) ^ 2)
    (hplanch2 : ∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
      MeasureTheory.Integrable (fun ξ : ℝ => (Work.FTS.EllSol.SpecAux.muW b ξ) ^ 2 * ‖Work.FTS.EllSol.FlatFT.slice u ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, (Work.FTS.EllSol.SpecAux.muW b ξ) ^ 2 * ‖Work.FTS.EllSol.FlatFT.slice u ξ θ‖ ^ 2) = ∫ t : ℝ, (Work.Spaces.pz (Work.Spaces.pz u) t θ - 2 * b * Work.Spaces.pz u t θ + b ^ 2 * u t θ) ^ 2)
    (hplanchlhs : ∀ᵐ θ ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Work.Spaces.Iθ),
      MeasureTheory.Integrable (fun ξ : ℝ => Work.FTS.EllSol.SpecAux.muW b ξ * ‖Work.FTS.EllSol.FlatFT.slice (Work.Spaces.pth u) ξ θ‖ ^ 2) ∧
      (∫ ξ : ℝ, Work.FTS.EllSol.SpecAux.muW b ξ * ‖Work.FTS.EllSol.FlatFT.slice (Work.Spaces.pth u) ξ θ‖ ^ 2) = ∫ t : ℝ, (Work.Spaces.pth (Work.Spaces.pz u) t θ - b * Work.Spaces.pth u t θ) ^ 2)
    (hSp : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ))
    (hSpp : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ))
    (hQ : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2 - b * Work.Spaces.pth u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2))
      ≤ ENNReal.ofReal (Cc * ((∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (Work.Spaces.pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)
          + Real.sqrt ((∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (Work.Spaces.pz (Work.Spaces.pz u) p.1 p.2 - 2 * b * Work.Spaces.pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2) * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2 * Work.FTS.EllSol.FlatFT.wE p.2)))) := by
  obtain ⟨M, hM0, hM⟩ := niceFlat_supp hg
  have hs : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Iθ) :=
    MeasurableSet.univ.prod measurableSet_Iθ
  have hcd_u : ContDiffOn ℝ 2 (Function.uncurry u) flStrip := hg.1
  have hsupp_pthpth : ∀ t θ : ℝ, M < |t| → pth (pth u) t θ = 0 := supp_pthpth hM
  have hsl_u : ContinuousOn (fun p : ℝ × ℝ => slice u p.1 p.2) flStrip :=
    continuousOn_slice_joint hcd_u.continuousOn ⟨M, hM0, hM⟩
  have hsl_q : ContinuousOn (fun p : ℝ × ℝ => slice (pth (pth u)) p.1 p.2) flStrip :=
    continuousOn_slice_joint
      (pth_contDiffOn_succ flStrip_isOpen
        (pth_contDiffOn_succ flStrip_isOpen hcd_u)).continuousOn
      ⟨M, hM0, hsupp_pthpth⟩
  -- ## the slice integrabilities of the three heavy slots (and of the light slot, unused)
  obtain ⟨hJg, hJpth, -, hJq⟩ := slotSliceFacts 0 (by norm_num) hg hQ
  -- ## the four Plancherel identifications
  have hid1 := hidShiftOne hg hJg hplanch1
  have hid2 := hidShiftTwo hg hJg hplanch2
  have hid3 := hidShiftThree hg hJq
  have hidlhs := hidShiftLhsE hg hJpth hplanchlhs
  -- ## the `∫⁻`/`∫` conversion of the three right-hand slots
  have hnn_s : 0 ≤ᵐ[((volume : Measure (ℝ × ℝ))).restrict (Set.univ ×ˢ Iθ)]
      (fun p : ℝ × ℝ => (pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * wE p.2) :=
    (ae_restrict_mem hs).mono fun p hp => mul_nonneg (sq_nonneg _) (wE_nonneg hp.2)
  have hnn_s2 : 0 ≤ᵐ[((volume : Measure (ℝ × ℝ))).restrict (Set.univ ×ˢ Iθ)]
      (fun p : ℝ × ℝ => (pz (pz u) p.1 p.2 - 2 * b * pz u p.1 p.2
        + b ^ 2 * u p.1 p.2) ^ 2 * wE p.2) :=
    (ae_restrict_mem hs).mono fun p hp => mul_nonneg (sq_nonneg _) (wE_nonneg hp.2)
  have hnn_q : 0 ≤ᵐ[((volume : Measure (ℝ × ℝ))).restrict (Set.univ ×ˢ Iθ)]
      (fun p : ℝ × ℝ => (pth (pth u) p.1 p.2) ^ 2 * wE p.2) :=
    (ae_restrict_mem hs).mono fun p hp => mul_nonneg (sq_nonneg _) (wE_nonneg hp.2)
  have hP : (∫⁻ p in Set.univ ×ˢ Iθ, ENNReal.ofReal
        ((pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * wE p.2))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Iθ,
          (pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * wE p.2) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hSp hnn_s).symm
  have hP2 : (∫⁻ p in Set.univ ×ˢ Iθ, ENNReal.ofReal
        ((pz (pz u) p.1 p.2 - 2 * b * pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * wE p.2))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Iθ,
          (pz (pz u) p.1 p.2 - 2 * b * pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * wE p.2) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hSpp hnn_s2).symm
  have hQ2 : (∫⁻ p in Set.univ ×ˢ Iθ, ENNReal.ofReal
        ((pth (pth u) p.1 p.2) ^ 2 * wE p.2))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Iθ,
          (pth (pth u) p.1 p.2) ^ 2 * wE p.2) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hQ hnn_q).symm
  -- ## the per-frequency angular Agmon bound (this is where `hCc` enters)
  have hξA : ∀ ξ : ℝ,
      (∫ θ in Iθ, ‖slice (pth u) ξ θ‖ ^ 2 * wE θ)
        ≤ Cc * ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
          + Real.sqrt ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
              * (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ))) := by
    intro ξ
    have hΦcd : ContDiffOn ℝ 2 (fun θ : ℝ => slice u ξ θ) (Set.Ioo 0 (Real.pi / 2)) :=
      sliceContDiffOn (n := 2) (by norm_num) hcd_u ⟨M, hM0, hM⟩ ξ
    have hderiv_ae : (fun θ : ℝ => deriv (fun θ' => slice u ξ θ') θ)
        =ᵐ[(volume : Measure ℝ).restrict Iθ]
          (fun θ : ℝ => slice (pth u) ξ θ) := by
      have hcongr : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[(volume : Measure ℝ)] Iθ :=
        MeasureTheory.Ioo_ae_eq_Icc
      rw [← MeasureTheory.Measure.restrict_congr_set hcongr]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact (slice_hasDerivAt u hg ξ hθ).1.deriv
    have hderiv2_ae : (fun θ : ℝ => deriv (deriv (fun θ'' => slice u ξ θ'')) θ)
        =ᵐ[(volume : Measure ℝ).restrict Iθ]
          (fun θ : ℝ => slice (pth (pth u)) ξ θ) := by
      have hcongr : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[(volume : Measure ℝ)] Iθ :=
        MeasureTheory.Ioo_ae_eq_Icc
      rw [← MeasureTheory.Measure.restrict_congr_set hcongr]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hev : (fun θ' => deriv (fun θ'' => slice u ξ θ'') θ')
          =ᶠ[𝓝 θ] (fun θ' => slice (pth u) ξ θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact (slice_hasDerivAt u hg ξ hθ').1.deriv
      rw [hev.deriv_eq, (slice_hasDerivAt u hg ξ hθ).2.deriv]
    have hI1 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => ‖deriv (fun θ' => slice u ξ θ') θ‖ ^ 2 * thEta θ) Iθ :=
      (hJpth ξ).congr (by filter_upwards [hderiv_ae] with θ hθ; rw [hθ]; rfl)
    have hI2 : MeasureTheory.IntegrableOn
        (fun θ : ℝ => ‖deriv (deriv (fun θ'' => slice u ξ θ'')) θ‖ ^ 2 * thEta θ) Iθ :=
      (hJq ξ).congr (by filter_upwards [hderiv2_ae] with θ hθ; rw [hθ]; rfl)
    have hkey := hCc (fun θ : ℝ => slice u ξ θ) hΦcd (slice_eq_zero hg ξ)
      (slice_eq_zero_pi hg ξ) (hJg ξ) hI1 hI2
    have e1 : (∫ θ in Iθ, ‖deriv (fun θ' => slice u ξ θ') θ‖ ^ 2 * thEta θ)
        = ∫ θ in Iθ, ‖slice (pth u) ξ θ‖ ^ 2 * wE θ :=
      integral_congr_ae (by filter_upwards [hderiv_ae] with θ hθ; rw [hθ]; rfl)
    have e2 : (∫ θ in Iθ, ‖deriv (deriv (fun θ'' => slice u ξ θ'')) θ‖ ^ 2 * thEta θ)
        = ∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ :=
      integral_congr_ae (by filter_upwards [hderiv2_ae] with θ hθ; rw [hθ]; rfl)
    rw [e1, e2] at hkey
    exact hkey
  -- ## the three right-hand real integrals and their non-negativity
  have hPnn : 0 ≤ ∫ p in Set.univ ×ˢ Iθ,
      (pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * wE p.2 :=
    integral_nonneg_of_ae ((ae_restrict_mem hs).mono fun p hp =>
      mul_nonneg (sq_nonneg _) (wE_nonneg hp.2))
  have hP2nn : 0 ≤ ∫ p in Set.univ ×ˢ Iθ,
      (pz (pz u) p.1 p.2 - 2 * b * pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * wE p.2 :=
    integral_nonneg_of_ae ((ae_restrict_mem hs).mono fun p hp =>
      mul_nonneg (sq_nonneg _) (wE_nonneg hp.2))
  have hQ2nn : 0 ≤ ∫ p in Set.univ ×ˢ Iθ,
      (pth (pth u) p.1 p.2) ^ 2 * wE p.2 :=
    integral_nonneg_of_ae ((ae_restrict_mem hs).mono fun p hp =>
      mul_nonneg (sq_nonneg _) (wE_nonneg hp.2))
  -- ## the slice energies as functions of `ξ`
  have hAnon : ∀ ξ : ℝ, 0 ≤ ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ :=
    fun ξ => integral_nonneg_of_ae
      (ae_mem_Iθ.mono fun θ hθ => mul_nonneg (sq_nonneg _) (wE_nonneg hθ))
  have hDnon : ∀ ξ : ℝ, 0 ≤ ∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ :=
    fun ξ => integral_nonneg_of_ae
      (ae_mem_Iθ.mono fun θ hθ => mul_nonneg (sq_nonneg _) (wE_nonneg hθ))
  have hAmeas : AEStronglyMeasurable
      (fun ξ : ℝ => ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
      (volume : Measure ℝ) :=
    (aemeasurable_slice_sq_mul_snd hsl_u measurable_wE).aestronglyMeasurable
      |>.integral_prod_right'
  have hDmeas : AEStronglyMeasurable
      (fun ξ : ℝ => ∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)
      (volume : Measure ℝ) :=
    (aemeasurable_slice_sq_mul_snd hsl_q measurable_wE).aestronglyMeasurable
      |>.integral_prod_right'
  -- ## the two heavy slots, as `lintegral`s of the shifted squares
  have hlimA : (∫⁻ ξ : ℝ, ENNReal.ofReal (muW b ξ
        * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Iθ,
          (pz u p.1 p.2 - b * u p.1 p.2) ^ 2 * wE p.2) := hid1.trans hP
  have hlimA2 : (∫⁻ ξ : ℝ, ENNReal.ofReal ((muW b ξ) ^ 2
        * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Iθ,
          (pz (pz u) p.1 p.2 - 2 * b * pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2 * wE p.2) :=
    hid2.trans hP2
  have hlimD : (∫⁻ ξ : ℝ, ENNReal.ofReal
        (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Iθ,
          (pth (pth u) p.1 p.2) ^ 2 * wE p.2) := by
    have h := hid3
    rw [show (∫⁻ ξ : ℝ, ENNReal.ofReal ((1 : ℝ)
          * ∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ))
        = ∫⁻ ξ : ℝ, ENNReal.ofReal
            (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ) from
      lintegral_congr fun ξ => by rw [one_mul]] at h
    rw [h, hQ2]
  -- ## integrability of the two `ξ`-side heavy slots
  have hintA2 : MeasureTheory.Integrable (fun ξ : ℝ => (muW b ξ) ^ 2
      * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ) := by
    refine (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).mp ?_
    · exact (measurable_muW b |>.pow_const 2).aestronglyMeasurable.mul hAmeas
    · exact Eventually.of_forall fun ξ => mul_nonneg (by positivity) (hAnon ξ)
    · rw [hlimA2]
      exact ENNReal.ofReal_ne_top
  have hintD : MeasureTheory.Integrable
      (fun ξ : ℝ => ∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ) := by
    refine (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).mp ?_
    · exact hDmeas
    · exact Eventually.of_forall hDnon
    · rw [hlimD]
      exact ENNReal.ofReal_ne_top
  -- ## Cauchy–Schwarz for the geometric-mean term
  have hcs := integral_mul_le_sqrt_mul
    (fun ξ : ℝ => muW b ξ * Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ))
    (fun ξ : ℝ => Real.sqrt (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ))
    (fun ξ => mul_nonneg (muW_nonneg b ξ) (Real.sqrt_nonneg _))
    (fun ξ => Real.sqrt_nonneg _)
    (by
      refine hintA2.congr (Eventually.of_forall fun ξ => ?_)
      show (muW b ξ) ^ 2 * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ
        = (muW b ξ * Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)) ^ 2
      have hsq : (Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)) ^ 2
          = ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ := Real.sq_sqrt (hAnon ξ)
      calc (muW b ξ) ^ 2 * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ
          = (muW b ξ) ^ 2
              * (Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)) ^ 2 := by
            rw [hsq]
        _ = (muW b ξ
              * Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)) ^ 2 := by
            ring)
    (by
      refine hintD.congr (Eventually.of_forall fun ξ => ?_)
      show ∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ
        = (Real.sqrt (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)) ^ 2
      rw [Real.sq_sqrt (hDnon ξ)])
  have h1sq : (∫ ξ : ℝ, (muW b ξ
        * Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)) ^ 2)
      = ∫ p in Set.univ ×ˢ Iθ,
          (pz (pz u) p.1 p.2 - 2 * b * pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2
            * wE p.2 := by
    have h : (∫ ξ : ℝ, (muW b ξ
          * Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)) ^ 2)
        = ∫ ξ : ℝ, (muW b ξ) ^ 2
            * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ :=
      integral_congr_ae (Eventually.of_forall fun ξ => by
        show (muW b ξ
            * Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)) ^ 2
          = (muW b ξ) ^ 2 * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ
        rw [mul_pow, Real.sq_sqrt (hAnon ξ)])
    rw [h]
    refine (ENNReal.ofReal_eq_ofReal_iff ?_ ?_).mp ?_
    · exact integral_nonneg fun ξ => mul_nonneg (by positivity) (hAnon ξ)
    · exact hP2nn
    · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintA2
        (Eventually.of_forall fun ξ => mul_nonneg (by positivity) (hAnon ξ))]
      exact hlimA2
  have h2sq : (∫ ξ : ℝ, (Real.sqrt (∫ θ in Iθ,
        ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)) ^ 2)
      = ∫ p in Set.univ ×ˢ Iθ, (pth (pth u) p.1 p.2) ^ 2 * wE p.2 := by
    have h : (∫ ξ : ℝ, (Real.sqrt (∫ θ in Iθ,
          ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)) ^ 2)
        = ∫ ξ : ℝ, ∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ :=
      integral_congr_ae (Eventually.of_forall fun ξ => by
        show (Real.sqrt (∫ θ in Iθ,
            ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)) ^ 2
          = ∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ
        rw [Real.sq_sqrt (hDnon ξ)])
    rw [h]
    refine (ENNReal.ofReal_eq_ofReal_iff ?_ ?_).mp ?_
    · exact integral_nonneg fun ξ => hDnon ξ
    · exact hQ2nn
    · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintD
        (Eventually.of_forall fun ξ => hDnon ξ)]
      exact hlimD
  have hcs' : (∫ ξ : ℝ, muW b ξ
        * Real.sqrt ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
            * (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)))
      ≤ Real.sqrt ((∫ p in Set.univ ×ˢ Iθ,
              (pz (pz u) p.1 p.2 - 2 * b * pz u p.1 p.2 + b ^ 2 * u p.1 p.2) ^ 2
                * wE p.2)
          * (∫ p in Set.univ ×ˢ Iθ, (pth (pth u) p.1 p.2) ^ 2 * wE p.2)) := by
    have hL : (∫ ξ : ℝ, muW b ξ
          * Real.sqrt ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
              * (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)))
        = ∫ ξ : ℝ, (muW b ξ
              * Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ))
            * Real.sqrt (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ) :=
      integral_congr_ae (Eventually.of_forall fun ξ => by
        show muW b ξ
            * Real.sqrt ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
              * (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ))
          = (muW b ξ * Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ))
              * Real.sqrt (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)
        rw [Real.sqrt_mul (hAnon ξ)]
        ring)
    rw [hL]
    have h := hcs.2
    rw [h1sq, h2sq] at h
    exact h
  -- ## the pointwise (in `ξ`) bound after multiplying by `μ`
  have hptw : ∀ ξ : ℝ,
      ENNReal.ofReal (muW b ξ
          * ∫ θ in Iθ, ‖slice (pth u) ξ θ‖ ^ 2 * wE θ)
        ≤ ENNReal.ofReal Cc * (ENNReal.ofReal (muW b ξ
              * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
          + ENNReal.ofReal (muW b ξ
              * Real.sqrt ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
                  * (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)))) := by
    intro ξ
    have hW0 : (0 : ℝ) ≤ muW b ξ := muW_nonneg b ξ
    have hAξ : 0 ≤ ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ := hAnon ξ
    have hkey : muW b ξ * (∫ θ in Iθ, ‖slice (pth u) ξ θ‖ ^ 2 * wE θ)
        ≤ Cc * (muW b ξ * (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
          + muW b ξ * Real.sqrt ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
              * (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ))) := by
      have h1 := mul_le_mul_of_nonneg_left (hξA ξ) hW0
      refine h1.trans (le_of_eq ?_)
      ring
    refine (ENNReal.ofReal_le_ofReal hkey).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (le_of_lt hCcpos),
      ENNReal.ofReal_add (mul_nonneg hW0 hAξ) (mul_nonneg hW0 (Real.sqrt_nonneg _))]
  have hpair_int : MeasureTheory.Integrable (fun ξ : ℝ => muW b ξ
      * Real.sqrt ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
          * (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ))) :=
    hcs.1.congr (Eventually.of_forall fun ξ => by
      show (muW b ξ * Real.sqrt (∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ))
            * Real.sqrt (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)
          = muW b ξ * Real.sqrt ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
              * (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ))
      rw [Real.sqrt_mul (hAnon ξ)]
      ring)
  have hpair_nn : ∀ ξ : ℝ, 0 ≤ muW b ξ
      * Real.sqrt ((∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)
          * (∫ θ in Iθ, ‖slice (pth (pth u)) ξ θ‖ ^ 2 * wE θ)) :=
    fun ξ => mul_nonneg (muW_nonneg b ξ) (Real.sqrt_nonneg _)
  have hAmeas2 : AEMeasurable (fun ξ : ℝ => ENNReal.ofReal (muW b ξ
      * ∫ θ in Iθ, ‖slice u ξ θ‖ ^ 2 * wE θ)) (volume : Measure ℝ) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((measurable_muW b).aemeasurable).mul hAmeas.aemeasurable)
  -- ## the final chain
  rw [← hidlhs]
  refine (lintegral_mono hptw).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hAmeas2,
    ENNReal.ofReal_mul (le_of_lt hCcpos),
    ENNReal.ofReal_add hPnn (Real.sqrt_nonneg _)]
  refine mul_le_mul' le_rfl (add_le_add ?_ ?_)
  · exact le_of_eq hlimA
  · rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hpair_int
      (Eventually.of_forall hpair_nn)]
    exact ENNReal.ofReal_le_ofReal hcs'

end

end Work.FTS.EllSol.Shift2Flat
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Final.Rep.H2W.Step5.s20_source =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Step5

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000

/-- **The source slot of `s20J2`.**  The `σ₄`-weighted second angular slot of the source
`Gsrc α F Ψ` is bounded by `pPure Ψ + HkSq α 2 F`: the `F`-part is the sibling `s20_Fslot`, and
the two `Ψ`-parts (the `Az Ψ = z²∂_z²Ψ`- and the `D_zΨ`-slot) are dominated by the `j = 1, 2`
summands of `pPure` by the commutation of `∂_θ²` with `D_z` on the open quadrant. -/
theorem s20src_J2_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.FTS.EllipticEst.H2W.s20J2 α F Ψ
        ≤ C * (Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F) := by
  obtain ⟨CF, hCFpos, hFslot⟩ := s20_Fslot
  refine ⟨3 * CF + 12, by positivity, fun α F Ψ hα hα4 h => ?_⟩
  have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hFso : Work.FTS.EllipticEst.SmoothOpen F := Work.H2W.smoothOpen_source h
  obtain ⟨hFint_raw, hFbd_raw⟩ := hFslot α F hα hα4 hFso h.memF
  have hFint : MeasureTheory.IntegrableOn
      (fun z => s20src_slotZ (Work.Spaces.pthIter 2 F)
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) Work.Spaces.Iz := by
    simpa only [s20src_slotZ, s20src_slotFun] using hFint_raw
  have hFbd : (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 F)
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
      ≤ CF * Work.Spaces.HkSq α 2 F := by
    simpa only [s20src_slotZ, s20src_slotFun] using hFbd_raw
  have hAzint := s20src_integrableOn_slotZ_sigma4_Az hΨso h.memB hα4
  have hAzbd := s20src_slotZ_sigma4_Az_le hΨso h.memB hα4
  have hΛint := s20src_integrableOn_slotZ_sigma4_DzIter hΨso h.memB hα4 1 (by norm_num)
  have hΛbd := s20src_slotZ_sigma4_DzIter_le hΨso h.memB hα4 1 (by norm_num)
  have hcmp : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      s20src_slotZ (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
        ≤ 3 * (s20src_slotZ (Work.Spaces.pthIter 2 F)
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
            + α ^ 4 * s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
            + (α * (5 + α)) ^ 2 * s20src_slotZ
              (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) := by
    filter_upwards [s20src_ae_pos_mem_Iz] with z hz
    exact s20src_slotZ_Gsrc_le hα hα4 hFso h.memF hΨso h.memB hz
  have hmaj : MeasureTheory.IntegrableOn
      (fun z => 3 * (s20src_slotZ (Work.Spaces.pthIter 2 F)
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
          + α ^ 4 * s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
          + (α * (5 + α)) ^ 2 * s20src_slotZ
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)) Work.Spaces.Iz :=
    (((hFint.add (hAzint.const_mul (α ^ 4))).add
      (hΛint.const_mul ((α * (5 + α)) ^ 2))).const_mul 3).congr
      (Filter.Eventually.of_forall fun z => by
        simp only [Pi.add_apply, Pi.mul_apply]; try ring)
  have hmain : (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2
        (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
      ≤ ∫ z in Work.Spaces.Iz, 3 * (s20src_slotZ (Work.Spaces.pthIter 2 F)
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
          + α ^ 4 * s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
          + (α * (5 + α)) ^ 2 * s20src_slotZ
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) :=
    MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z _ =>
        s20src_slotZ_nonneg (fun θ' hθ' => s20src_sigma4_nonneg α hθ') z)
      hmaj hcmp
  have hval : (∫ z in Work.Spaces.Iz, 3 * (s20src_slotZ (Work.Spaces.pthIter 2 F)
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
        + α ^ 4 * s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
        + (α * (5 + α)) ^ 2 * s20src_slotZ
          (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z))
      = 3 * ((∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 F)
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
          + α ^ 4 * (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
          + (α * (5 + α)) ^ 2 * (∫ z in Work.Spaces.Iz,
              s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
                (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)) := by
    have hI12 : MeasureTheory.IntegrableOn
        (fun z => s20src_slotZ (Work.Spaces.pthIter 2 F)
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
          + α ^ 4 * s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) Work.Spaces.Iz :=
      hFint.add (hAzint.const_mul (α ^ 4))
    have hI3 : MeasureTheory.IntegrableOn
        (fun z => (α * (5 + α)) ^ 2 * s20src_slotZ
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) Work.Spaces.Iz :=
      hΛint.const_mul ((α * (5 + α)) ^ 2)
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hI12 hI3,
      MeasureTheory.integral_add hFint (hAzint.const_mul (α ^ 4)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    try ring
  have hIΦ : 0 ≤ ∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z :=
    integral_nonneg fun z =>
      s20src_slotZ_nonneg (fun θ' hθ' => s20src_sigma4_nonneg α hθ') z
  have hIΛ : 0 ≤ ∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2
        (Work.Spaces.DzIter 1 Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z :=
    integral_nonneg fun z =>
      s20src_slotZ_nonneg (fun θ' hθ' => s20src_sigma4_nonneg α hθ') z
  have hIF : 0 ≤ ∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 F)
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z :=
    integral_nonneg fun z =>
      s20src_slotZ_nonneg (fun θ' hθ' => s20src_sigma4_nonneg α hθ') z
  have hα4le : α ^ 4 ≤ 1 := by
    have h1 : α ≤ 1 := by linarith
    exact pow_le_one₀ hα.le h1
  have hc2 : (α * (5 + α)) ^ 2 ≤ 2 := by
    have hx : α * (5 + α) ≤ 7 / 5 := by nlinarith [hα.le, hα4]
    have hx0 : 0 ≤ α * (5 + α) := by nlinarith [hα.le]
    nlinarith [hx, hx0]
  have hHk : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have h0 := s20src_pSlot_nonneg 0 Ψ
  have h1 := s20src_pSlot_nonneg 1 Ψ
  have h2 := s20src_pSlot_nonneg 2 Ψ
  have hpure := s20src_pPure_eq_three Ψ
  have hAzQ : α ^ 4 * (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
      ≤ 2 * (s20src_pSlot 2 Ψ + s20src_pSlot 1 Ψ) :=
    calc α ^ 4 * (∫ z in Work.Spaces.Iz,
            s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
        ≤ 1 * (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) :=
          mul_le_mul_of_nonneg_right hα4le hIΦ
      _ = (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) := by ring
      _ ≤ 2 * (s20src_pSlot 2 Ψ + s20src_pSlot 1 Ψ) := hAzbd
  have hΛQ : (α * (5 + α)) ^ 2 * (∫ z in Work.Spaces.Iz,
        s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
      ≤ 2 * s20src_pSlot 1 Ψ :=
    calc (α * (5 + α)) ^ 2 * (∫ z in Work.Spaces.Iz,
            s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
        ≤ 2 * (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2
              (Work.Spaces.DzIter 1 Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) :=
          mul_le_mul_of_nonneg_right hc2 hIΛ
      _ ≤ 2 * s20src_pSlot 1 Ψ := mul_le_mul_of_nonneg_left hΛbd (by norm_num)
  have hFQ : (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 F)
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
      ≤ CF * Work.Spaces.HkSq α 2 F := hFbd
  have hCF : 0 ≤ CF := hCFpos.le
  have key : 3 * ((∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 F)
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
        + α ^ 4 * (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
        + (α * (5 + α)) ^ 2 * (∫ z in Work.Spaces.Iz,
            s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z))
      ≤ (3 * CF + 12) * (Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F) := by
    rw [hpure]
    have e1 : 3 * ((∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 F)
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
          + α ^ 4 * (∫ z in Work.Spaces.Iz, s20src_slotZ (Work.Spaces.pthIter 2 (Az Ψ))
              (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
          + (α * (5 + α)) ^ 2 * (∫ z in Work.Spaces.Iz,
              s20src_slotZ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
                (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z))
        ≤ 3 * (CF * Work.Spaces.HkSq α 2 F
            + (2 * (s20src_pSlot 2 Ψ + s20src_pSlot 1 Ψ) + 2 * s20src_pSlot 1 Ψ)) := by
      have h := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hFQ hAzQ) hΛQ)
        (by norm_num : (0 : ℝ) ≤ 3)
      linarith [h]
    have e2 : 3 * (CF * Work.Spaces.HkSq α 2 F
          + (2 * (s20src_pSlot 2 Ψ + s20src_pSlot 1 Ψ) + 2 * s20src_pSlot 1 Ψ))
        ≤ (3 * CF + 12) * (s20src_pSlot 0 Ψ + s20src_pSlot 1 Ψ + s20src_pSlot 2 Ψ
            + Work.Spaces.HkSq α 2 F) := by
      nlinarith [h0, h1, h2, hHk, hCF]
    linarith [e1, e2]
  rw [s20src_s20J2_eq α F Ψ]
  linarith [hmain, hval.le, key]

theorem s20_source : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.FTS.EllipticEst.H2W.s20J2 α F Ψ
          + (Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
              + Work.FTS.EllipticEst.H2W.s20A0 Ψ)
        ≤ C * (Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F) := by
  obtain ⟨CJ, hCJpos, hJ⟩ := s20src_J2_le
  obtain ⟨CA, hCApos, hA⟩ := s20src_lower_own
  refine ⟨2 * max CJ CA, by positivity, fun α F Ψ hα hα4 h => ?_⟩
  have hR : 0 ≤ Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F :=
    add_nonneg (Work.FTS.EllipticEst.H2W.pPure_nonneg Ψ) (Work.Spaces.HkSq_nonneg α 2 F)
  have hp : 0 ≤ Work.FTS.EllipticEst.H2W.pPure Ψ := Work.FTS.EllipticEst.H2W.pPure_nonneg Ψ
  have hk : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have hM : 0 ≤ max CJ CA := le_trans hCJpos.le (le_max_left CJ CA)
  have hJm : Work.FTS.EllipticEst.H2W.s20J2 α F Ψ
      ≤ max CJ CA * (Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F) :=
    (hJ α F Ψ hα hα4 h).trans (mul_le_mul_of_nonneg_right (le_max_left CJ CA) hR)
  have hAm : Work.FTS.EllipticEst.H2W.s20A2 Ψ + Work.FTS.EllipticEst.H2W.s20A1 Ψ
        + Work.FTS.EllipticEst.H2W.s20A0 Ψ
      ≤ max CJ CA * (Work.FTS.EllipticEst.H2W.pPure Ψ + Work.Spaces.HkSq α 2 F) :=
    ((hA α F Ψ hα hα4 h).trans
      (mul_le_mul_of_nonneg_right (le_max_right CJ CA) hp)).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hk) hM)
  nlinarith [hJm, hAm]

end Work.FTS.EllipticEst.H2W.Step5
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.Step5.s20SliceIntegrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.Step5

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/

/-- The radial weight `w` is positive for `z > 0`. -/
theorem s20si_w_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  positivity

/-- If `c * g` is integrable on `Iθ` and `c ≠ 0`, then so is `g`. -/
theorem s20si_integrableOn_of_const_mul {g : ℝ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : MeasureTheory.IntegrableOn (fun θ => c * g θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn g Work.Spaces.Iθ :=
  MeasureTheory.IntegrableOn.congr_fun (h.const_mul c⁻¹)
    (fun θ _ => by rw [inv_mul_cancel_left₀ hc]) measurableSet_Icc

/-- The `θ`-measurability of the slices of the iterated `∂_θ`-derivatives of `Ψ`, for positive
order (the order `0` slice is an arbitrary function of `θ`). -/
theorem s20si_measurable_pthIter_succ (n : ℕ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Measurable (fun θ : ℝ => Work.Spaces.pthIter (n + 1) Ψ z θ) := by
  have h : Measurable (deriv (fun t : ℝ => Work.Spaces.pthIter n Ψ z t)) := measurable_deriv _
  simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pth] using h

/-- `sig2 γ = sin(2θ)^{2-γ}` is continuous for `γ ≤ 2`. -/
theorem s20si_continuous_sig2 {γ : ℝ} (hγ : γ ≤ 2) :
    Continuous (fun θ : ℝ => Work.FTS.EllipticEst.Mine.sig2 γ θ) := by
  have h : Continuous (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ)) :=
    (Real.continuous_rpow_const (by linarith)).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  simpa only [Work.FTS.EllipticEst.Mine.sig2] using h

/-- `sig4 γ = sin(2θ)^{4-γ}` is continuous for `γ ≤ 4`. -/
theorem s20si_continuous_sig4 {γ : ℝ} (hγ : γ ≤ 4) :
    Continuous (fun θ : ℝ => Work.FTS.EllipticEst.Mine.sig4 γ θ) := by
  have h : Continuous (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (4 - γ)) :=
    (Real.continuous_rpow_const (by linarith)).comp
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  simpa only [Work.FTS.EllipticEst.Mine.sig4] using h

/-! ## The target -/

theorem s20SliceIntegrable :
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      ∀ z : ℝ, 0 < z →
        MeasureTheory.IntegrableOn (fun θ => (Ψ z θ) ^ 2) Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => Ψ z t) θ) ^ 2) Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (fun t => Ψ z t)) θ) ^ 2 *
          Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv (fun t => Ψ z t))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv (deriv (fun t => Ψ z t)))) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) Work.Spaces.Iθ ∧
        MeasureTheory.IntegrableOn (fun θ =>
          (deriv (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t)) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
  intro α F Ψ hα hα4 h z hz
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hw : 0 < Work.Spaces.w z := s20si_w_pos hz
  have hw2 : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hw)
  have hgam2 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  -- the three `H²`-memberships of the datum
  have hFmem : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 2 F z θ) Work.Spaces.Iθ := h.memF.1 z hzI
  have hAmem : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) Work.Spaces.Iθ := h.memA.1 z hzI
  have hBmem : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ) Work.Spaces.Iθ :=
    h.memB.1 z hzI
  -- ======================================================================
  -- (1), (2), (3): the low-order slots of the slice, from the equation
  -- ======================================================================
  obtain ⟨-, -, -, -, h1, h2, h3⟩ :=
    Work.FTS.EllipticEst.remov.weakSliceRegular 2 (by norm_num) α F Ψ hα hα4 h z hz
  -- ======================================================================
  -- (4): `(∂_θ³Ψ)² σ₂`
  -- ======================================================================
  have h4 : MeasureTheory.IntegrableOn (fun θ =>
      (deriv (deriv (deriv (fun t => Ψ z t))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    have hslot : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pthIter 3 Ψ z θ) ^ 2 *
          Work.FTS.EllipticEst.Mine.sig2 (Work.Spaces.gam α) θ)) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.mono' hBmem ?_ ?_
      · exact (measurable_const.mul (((s20si_measurable_pthIter_succ 2 Ψ z).pow_const 2).mul
          (s20si_continuous_sig2 (by linarith [Work.Spaces.gam_pos hα])).measurable)).aestronglyMeasurable
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.Mine.sig2_nonneg_of_mem_Iθ hθ)))]
        exact Work.FTS.EllipticEst.Mine.sig2_slot_pointwise α hα (Work.Spaces.gam α) hgam2
          le_rfl (Work.Spaces.pthIter 2 Ψ) z θ hθ
    exact s20si_integrableOn_of_const_mul hw2 hslot
  -- ======================================================================
  -- (5): `(∂_θ⁴Ψ)² σ₄`
  -- ======================================================================
  have h5 : MeasureTheory.IntegrableOn (fun θ =>
      (deriv (deriv (deriv (deriv (fun t => Ψ z t)))) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    have hslot : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2 *
        ((Work.Spaces.pthIter 4 Ψ z θ) ^ 2 *
          Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)) Work.Spaces.Iθ := by
      refine MeasureTheory.Integrable.mono' (hBmem.const_mul 10) ?_ ?_
      · exact (measurable_const.mul (((s20si_measurable_pthIter_succ 3 Ψ z).pow_const 2).mul
          (s20si_continuous_sig4 (by linarith [Work.Spaces.gam_pos hα])).measurable)).aestronglyMeasurable
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
          (Work.FTS.EllipticEst.Mine.sig4_nonneg_of_mem_Iθ hθ)))]
        exact Work.FTS.EllipticEst.Mine.sig4_slot_pointwise α hα (Work.Spaces.gam α) hgam2
          le_rfl (Work.Spaces.pthIter 2 Ψ) z θ hθ
    exact s20si_integrableOn_of_const_mul hw2 hslot
  -- ======================================================================
  -- (6): `(∂_θ² G)² σ₄`, `G = Gsrc α F Ψ`
  -- ======================================================================
  have h6 : MeasureTheory.IntegrableOn (fun θ =>
      (deriv (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t)) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
    have hFso : Work.FTS.EllipticEst.SmoothOpen F := Work.H2W.smoothOpen_source h
    have hΨso : Work.FTS.EllipticEst.SmoothOpen Ψ :=
      Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
    set Maj : ℝ → ℝ := fun θ => 3 * ((10 * Work.Spaces.HkIntegrand α 2 F z θ
      + 10 * α ^ 4 * Work.Spaces.HkIntegrand α 2
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
      + (α * (5 + α)) ^ 2 * Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ)
      with hMaj
    have hMajint : MeasureTheory.IntegrableOn Maj Work.Spaces.Iθ := by
      rw [hMaj]
      exact (((hFmem.const_mul 10).add (hAmem.const_mul (10 * α ^ 4))).add
        (hBmem.const_mul ((α * (5 + α)) ^ 2))).const_mul 3
    -- the pointwise domination, a.e. on `Iθ`
    have hbd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        ‖(deriv (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t)) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α)‖
          ≤ (Work.Spaces.w z ^ 2)⁻¹ * Maj θ := by
      filter_upwards [Work.FTS.EllipticEst.remov.SourceBound.ae_mem_Ioo_of_mem_Iθ] with θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hsin : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
      have hσ4 : 0 ≤ Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ :=
        Work.FTS.EllipticEst.Mine.sig4_nonneg_of_mem_Iθ hθI
      have hnn : (0 : ℝ) ≤ (deriv (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t)) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)
      rw [Real.norm_of_nonneg hnn]
      -- the expansion of `∂_θ²G`
      have hid := Work.FTS.EllipticEst.SrcBnd.GsrcPthTwo (α := α) hFso hΨso z θ hz hθ
      have hcomm := Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨso 1
        (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) from ⟨hz, hθ⟩)
      -- the three slot bounds
      have b1 : (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
          Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)
          ≤ 10 * Work.Spaces.HkIntegrand α 2 F z θ :=
        Work.FTS.EllipticEst.Mine.sig4_slot_pointwise α hα (Work.Spaces.gam α) hgam2 le_rfl
          F z θ hθI
      have b2 : (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pthIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 *
            Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)
          ≤ 10 * Work.Spaces.HkIntegrand α 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ :=
        Work.FTS.EllipticEst.Mine.sig4_slot_pointwise α hα (Work.Spaces.gam α) hgam2 le_rfl
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ hθI
      have b3 : (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 *
            Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)
          ≤ Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ := by
        have hsig : Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ
            ≤ Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta)) := by
          rw [Work.FTS.EllipticEst.Mine.sig4]
          exact Real.rpow_le_rpow_of_exponent_ge hsin (Real.sin_le_one _)
            (by rw [Work.Spaces.eta]; linarith)
        have hstep : (Work.Spaces.w z) ^ 2 *
            ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 *
              (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            = (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ *
                (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          rw [Work.FTS.EllipticEst.mul_w_sin_rpow_sq _ _ hθI]
          ring
        have hcomm' : Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ
            = Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ := hcomm
        rw [hcomm']
        calc (Work.Spaces.w z) ^ 2 *
              ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 *
                Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)
            ≤ (Work.Spaces.w z) ^ 2 *
              ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (-(Work.Spaces.eta))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hsig (sq_nonneg _)) (sq_nonneg _)
          _ = (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ *
                (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
              hstep
          _ ≤ Work.Spaces.HkIntegrand α 2 (Work.Spaces.pthIter 2 Ψ) z θ :=
              Work.Spaces.sq_le_HkIntegrand_z α 2 (Work.Spaces.pthIter 2 Ψ) z θ 1
                (by norm_num)
      -- the squaring
      have hsq : (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2 *
          Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ
          ≤ 3 * ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
                Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ
              + α ^ 4 * ((Work.Spaces.pthIter 2
                    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 *
                  Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)
              + (α * (5 + α)) ^ 2 *
                  ((Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 *
                    Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)) := by
        rw [hid]
        have h3 : (Work.Spaces.pthIter 2 F z θ
              + α ^ 2 * Work.Spaces.pthIter 2
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              + α * (5 + α) * Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
            ≤ 3 * ((Work.Spaces.pthIter 2 F z θ) ^ 2
              + (α ^ 2 * Work.Spaces.pthIter 2
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
              + (α * (5 + α) * Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2) := by
          nlinarith [sq_nonneg (Work.Spaces.pthIter 2 F z θ
              - α ^ 2 * Work.Spaces.pthIter 2
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ),
            sq_nonneg (α ^ 2 * Work.Spaces.pthIter 2
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              - α * (5 + α) * Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ),
            sq_nonneg (Work.Spaces.pthIter 2 F z θ
              - α * (5 + α) * Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)]
        calc (Work.Spaces.pthIter 2 F z θ
              + α ^ 2 * Work.Spaces.pthIter 2
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
              + α * (5 + α) * Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 *
              Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ
            ≤ 3 * ((Work.Spaces.pthIter 2 F z θ) ^ 2
              + (α ^ 2 * Work.Spaces.pthIter 2
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
              + (α * (5 + α) * Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2) *
                Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ :=
              mul_le_mul_of_nonneg_right h3 hσ4
          _ = 3 * ((Work.Spaces.pthIter 2 F z θ) ^ 2 *
                Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ
              + α ^ 4 * ((Work.Spaces.pthIter 2
                    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 *
                  Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)
              + (α * (5 + α)) ^ 2 *
                  ((Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 *
                    Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)) := by
              ring
      -- assembly
      have hfinal : (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2 *
            Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ) ≤ Maj θ := by
        rw [hMaj]
        have hstep := mul_le_mul_of_nonneg_left hsq (sq_nonneg (Work.Spaces.w z))
        have hd : (Work.Spaces.w z) ^ 2 * (3 *
              ((Work.Spaces.pthIter 2 F z θ) ^ 2 * Work.FTS.EllipticEst.Mine.sig4
                  (Work.Spaces.gam α) θ
                + α ^ 4 * ((Work.Spaces.pthIter 2
                      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 *
                    Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)
                + (α * (5 + α)) ^ 2 *
                    ((Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 *
                      Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ)))
            = 3 * ((Work.Spaces.w z) ^ 2 *
                  ((Work.Spaces.pthIter 2 F z θ) ^ 2 * Work.FTS.EllipticEst.Mine.sig4
                    (Work.Spaces.gam α) θ)
                + α ^ 4 * ((Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter 2
                      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 *
                    Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ))
                + (α * (5 + α)) ^ 2 * ((Work.Spaces.w z) ^ 2 *
                    ((Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 *
                      Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ))) := by
          ring
        rw [hd] at hstep
        have hA : α ^ 4 * ((Work.Spaces.w z) ^ 2 *
              ((Work.Spaces.pthIter 2
                  (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2 *
                Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ))
            ≤ α ^ 4 * (10 * Work.Spaces.HkIntegrand α 2
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) :=
          mul_le_mul_of_nonneg_left b2 (pow_nonneg hα.le 4)
        have hC : (α * (5 + α)) ^ 2 * ((Work.Spaces.w z) ^ 2 *
              ((Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 *
                Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α) θ))
            ≤ (α * (5 + α)) ^ 2 * Work.Spaces.HkIntegrand α 2
                (Work.Spaces.pthIter 2 Ψ) z θ :=
          mul_le_mul_of_nonneg_left b3 (sq_nonneg _)
        linarith [hstep, b1, hA, hC]
      have hle := mul_le_mul_of_nonneg_left hfinal (inv_nonneg.mpr (sq_nonneg (Work.Spaces.w z)))
      rwa [inv_mul_cancel_left₀ hw2] at hle
    refine MeasureTheory.Integrable.mono' (hMajint.const_mul ((Work.Spaces.w z) ^ 2)⁻¹) ?_ hbd
    exact ((measurable_deriv (deriv (fun t => Work.FTS.EllipticEst.Mine.Gsrc α F Ψ z t))).pow_const 2
      |>.mul (s20si_continuous_sig4 (by linarith [Work.Spaces.gam_pos hα])).measurable).aestronglyMeasurable
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Work.FTS.EllipticEst.H2W.Step5
end
-- ===== merged: Submission.Work.FTS.EllipticEst.H2W.sliceStep5Weak =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Elementary facts about the weights on `Iθ` -/

lemma rpow4_nonneg (γ : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Real.sin (2 * θ)) ^ (4 - γ) := Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

lemma rpow2_nonneg (γ : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ (Real.sin (2 * θ)) ^ (2 - γ) := Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _

lemma rpow2_le_one (γ : ℝ) (_hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (2 - γ) ≤ 1 :=
  Real.rpow_le_one (sin_two_nonneg_Iθ hθ) (Real.sin_le_one _) (by linarith)

lemma rpow4_le_one (γ : ℝ) (_hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (4 - γ) ≤ 1 :=
  Real.rpow_le_one (sin_two_nonneg_Iθ hθ) (Real.sin_le_one _) (by linarith)


lemma rpow4_le_sEta (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (4 - γ) ≤ Work.FTS.EllipticEst.sEta θ := by
  have h0 := sin_two_nonneg_Iθ hθ
  have heta : -(Work.Spaces.eta) ≤ (4 : ℝ) - γ := by
    have := Work.Spaces.eta_nonneg; linarith
  rcases eq_or_lt_of_le h0 with h | h
  · have h4 : (4 : ℝ) - γ ≠ 0 := by linarith
    have he : (-(Work.Spaces.eta)) ≠ 0 := by rw [Work.Spaces.eta]; norm_num
    change (Real.sin (2 * θ)) ^ (4 - γ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    rw [← h, Real.zero_rpow h4, Real.zero_rpow he]
  · exact Real.rpow_le_rpow_of_exponent_ge h (Real.sin_le_one _) heta

/-! The same weight facts, stated in `Real.rpow` form (matching the theorem statement). -/

lemma rpow4_nonneg_rp (γ : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.rpow (Real.sin (2 * θ)) (4 - γ) := rpow4_nonneg γ hθ

lemma rpow2_nonneg_rp (γ : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) := rpow2_nonneg γ hθ

lemma rpow4_le_sEta_rp (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.rpow (Real.sin (2 * θ)) (4 - γ) ≤ Work.FTS.EllipticEst.sEta θ :=
  rpow4_le_sEta γ hγ1 hγ2 hθ


lemma rpow2_le_one_rp (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 :=
  rpow2_le_one γ hγ1 hγ2 hθ

lemma rpow4_le_one_rp (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 3 / 2) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.rpow (Real.sin (2 * θ)) (4 - γ) ≤ 1 :=
  rpow4_le_one γ hγ1 hγ2 hθ

/-- `tan²θ · sin(2θ)^{4-γ} = 4 sin⁴θ · sin(2θ)^{2-γ}` on the open interval. -/
lemma tan_sq_mul_rpow4_eq (γ : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.tan θ ^ 2 * (Real.sin (2 * θ)) ^ (4 - γ)
      = 4 * Real.sin θ ^ 4 * (Real.sin (2 * θ)) ^ (2 - γ) := by
  have hS : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hC : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hs : 0 < Real.sin (2 * θ) := by rw [Real.sin_two_mul]; positivity
  have hsplit : (Real.sin (2 * θ)) ^ (4 - γ)
      = (Real.sin (2 * θ)) ^ (2 - γ) * (Real.sin (2 * θ)) ^ 2 := by
    have h := Real.rpow_add hs (2 - γ) 2
    rw [show (2 : ℝ) - γ + 2 = 4 - γ from by ring] at h
    rw [Real.rpow_two] at h
    exact h
  have hcos : Real.cos θ ≠ 0 := hC.ne'
  have hkey : (Real.sin θ / Real.cos θ) ^ 2 * (2 * Real.sin θ * Real.cos θ) ^ 2
      = 4 * Real.sin θ ^ 4 := by
    field_simp
    ring
  rw [Real.tan_eq_sin_div_cos, hsplit, Real.sin_two_mul]
  have hre : (Real.sin θ / Real.cos θ) ^ 2 *
        ((2 * Real.sin θ * Real.cos θ) ^ (2 - γ) * (2 * Real.sin θ * Real.cos θ) ^ 2)
      = ((Real.sin θ / Real.cos θ) ^ 2 * (2 * Real.sin θ * Real.cos θ) ^ 2)
        * (2 * Real.sin θ * Real.cos θ) ^ (2 - γ) := by ring
  rw [hre, hkey]

lemma tan_sq_mul_rpow4_le (γ : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.tan θ ^ 2 * (Real.sin (2 * θ)) ^ (4 - γ)
      ≤ 4 * (Real.sin (2 * θ)) ^ (2 - γ) := by
  rw [tan_sq_mul_rpow4_eq γ hθ]
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hs : 0 ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]; exact mul_nonneg (mul_nonneg (by norm_num) hsin.le) hcos.le
  have h4 : Real.sin θ ^ 4 ≤ 1 := by
    have h2 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    nlinarith [sq_nonneg (Real.sin θ ^ 2), h2]
  have hrp : 0 ≤ (Real.sin (2 * θ)) ^ (2 - γ) := Real.rpow_nonneg hs _
  nlinarith [h4, hrp]


/-! ## The identities of `slice5_rel`, a.e. on `Iθ` -/

lemma tan_sq_mul_rpow4_le_rp (γ : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.tan θ ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
      ≤ 4 * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
  tan_sq_mul_rpow4_le γ hθ
lemma ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ, θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  have h : Work.Spaces.Iθ =ᵐ[(volume : Measure ℝ)] Set.Ioo 0 (Real.pi / 2) := by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ))).symm
  rw [MeasureTheory.Measure.restrict_congr_set h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

lemma eqn_deriv2_ae {u g : ℝ → ℝ} (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      deriv (deriv (deriv (deriv u))) θ
        = deriv (deriv (deriv (fun t => Real.tan t * u t))) θ
          - 6 * deriv (deriv u) θ - deriv (deriv g) θ := by
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  have h := Work.FTS.EllipticEst.remov.slice5_eqn_deriv2 u g hu hode θ hθ
  linarith

lemma tanu3_ae {u : ℝ → ℝ} (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      deriv (deriv (deriv (fun t => Real.tan t * u t))) θ
        = Real.sin θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ
          + 3 * Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ
          - 3 * Real.sin θ * deriv (fun t => u t / Real.cos t) θ
          - Real.cos θ * (u θ / Real.cos θ) := by
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  exact Work.FTS.EllipticEst.remov.slice5_tanu3_weak u hu θ hθ

lemma CV3_ae {u g : ℝ → ℝ} (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      Real.cos θ * deriv (deriv (deriv (fun t => u t / Real.cos t))) θ
        = 4 * deriv (deriv (deriv u)) θ + 15 * deriv u θ
          - Real.sin θ * (u θ / Real.cos θ) + 3 * deriv g θ := by
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  exact Work.FTS.EllipticEst.remov.slice5_v_CV3'' u g hu hode θ hθ

lemma CV2_ae {u g : ℝ → ℝ} (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      Real.cos θ * deriv (deriv (fun t => u t / Real.cos t)) θ
        = deriv (deriv u) θ + u θ
          + 2 * Real.sin θ * deriv (fun t => u t / Real.cos t) θ := by
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  exact Work.FTS.EllipticEst.remov.slice5_v_CV2 u g hu hode θ hθ

lemma cos_mul_ae {u : ℝ → ℝ} :
    ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      Real.cos θ * (u θ / Real.cos θ) = u θ := by
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  exact Work.FTS.EllipticEst.remov.cos_mul_cbV hθ

/-! ## Elementary AM–GM helpers -/

lemma sq_add_le_three (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

lemma sq_sub_sub_le_three (a b c : ℝ) : (a - b - c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b - c)]

lemma sq_add_le_four (a b c d : ℝ) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

lemma Iθ_measurableSet : MeasurableSet Work.Spaces.Iθ := by
  rw [Work.Spaces.Iθ]; exact measurableSet_Icc

lemma Iθ_of_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : θ ∈ Work.Spaces.Iθ :=
  ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩

lemma measurable_rpow_sin_four (γ : ℝ) (hγ2 : γ ≤ 3 / 2) :
    Measurable (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (4 - γ)) := by
  have hpq4 : (0:ℝ) ≤ 4 - γ := by linarith
  exact ((Real.continuous_rpow_const (q := 4 - γ) hpq4).measurable.comp
    (Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id)))

lemma measurable_rpow_sin_two (γ : ℝ) (hγ2 : γ ≤ 3 / 2) :
    Measurable (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by
  have hpq2 : (0:ℝ) ≤ 2 - γ := by linarith
  exact ((Real.continuous_rpow_const (q := 2 - γ) hpq2).measurable.comp
    (Real.continuous_sin.measurable.comp (measurable_const.mul measurable_id)))

lemma sin_mul_sq_le_sq (θ x : ℝ) : (Real.sin θ * x) ^ 2 ≤ x ^ 2 := by
  nlinarith [Real.sin_sq_le_one θ, sq_nonneg x]

lemma sin_mul_sq_eq_tan {θ : ℝ} (hcos : Real.cos θ ≠ 0) (x : ℝ) :
    (Real.sin θ * x) ^ 2 = Real.tan θ ^ 2 * (Real.cos θ * x) ^ 2 := by
  rw [Real.tan_eq_sin_div_cos]
  field_simp

lemma integral_le_of_ae {f g : ℝ → ℝ}
    (hf : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ, 0 ≤ f θ)
    (hg : Integrable g ((volume : Measure ℝ).restrict Work.Spaces.Iθ))
    (h : f ≤ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ] g) :
    (∫ θ in Work.Spaces.Iθ, f θ) ≤ ∫ θ in Work.Spaces.Iθ, g θ :=
  MeasureTheory.integral_mono_of_nonneg hf hg h



end Work.FTS.EllipticEst.H2W
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.AuxAngRad.HkIntegrand_ang_rad_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Nonlinear.RadialProd (smE smG Rint)

namespace Work.FTS.NonlinRows.AuxAngRad

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **Pointwise separation of an angular profile and a radial function in the `ℋ⁴`-integrand.**

For an angular profile `a` with `|a θ| ≤ B0` on `Iθ`, whose `D_θ`-iterates of orders `1..4` are
bounded by `B1 · G`, and a radial function `r`, the weighted integrand of `ℋ⁴` at any
`(z,θ)`, `θ ∈ Iθ`, is bounded by the radial density `Rint r z = Σ_{i≤4}(D_z^i r)²w²` times the
angular factor `B0²σ + 4 B1² G² τ`, with `σ = sin(2θ)^{-η}` and `τ = sin(2θ)^{-γ(α)}`.

The two identities `light_sq_nn`/`heavy_sq_nn` (valid on all of `Iθ`, including the endpoints
where `sin(2θ) = 0`) convert the two weights; `dzIter_ang_rad`/`mixed_ang_rad` separate the
iterates; the coefficient `4` is the number of `i ∈ {1,2,3,4}`. -/
theorem HkIntegrand_ang_rad_le {α : ℝ} {a : ℝ → ℝ} {r : ℝ → ℝ} {G : ℝ → ℝ} {B0 B1 : ℝ}
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B1 * G θ)
    {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * r z) z θ
      ≤ Work.FTS.Nonlinear.RadialProd.Rint r z
          * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  have hsmEnn : 0 ≤ smE θ := Work.FTS.Nonlinear.RadialProd.smE_nonneg hθ
  have hsmGnn : 0 ≤ smG α θ := Work.FTS.Nonlinear.RadialProd.smG_nonneg hθ
  obtain ⟨hain, hain'⟩ := abs_le.mp (ha0 θ hθ)
  -- ### the pure (`D_z`-only) slots
  have hterm : ∀ i ∈ Finset.range 5,
      (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (a θ) ^ 2 * smE θ
            * ((Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    intro i _
    rw [Work.FTS.Nonlinear.Pieces.dzIter_ang_rad,
      show (a θ * Work.Elliptic.DzdIter i r z
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = ((a θ * Work.Elliptic.DzdIter i r z)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        from by ring,
      light_sq_nn _ z θ hs]
    ring
  have hpure : (∑ i ∈ Finset.range 5,
        (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = (a θ) ^ 2 * smE θ * Rint r z := by
    calc (∑ i ∈ Finset.range 5,
            (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∑ i ∈ Finset.range 5, (a θ) ^ 2 * smE θ
            * ((Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
          Finset.sum_congr rfl fun i hi => hterm i hi
      _ = (a θ) ^ 2 * smE θ * Rint r z := by
          rw [← Finset.mul_sum, Rint]
  -- ### the mixed slots
  have hmix : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ Rint r z * (∑ i ∈ Finset.range 5, if 1 ≤ i then
          (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2 * smG α θ else 0) := by
    have hterm2 : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
        ≤ (if 1 ≤ i then
              (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2 * smG α θ else 0)
            * ((Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      intro i hi j hj
      by_cases h1 : 1 ≤ i
      · by_cases h2 : i + j ≤ 4
        · rw [if_pos ⟨h1, h2⟩, if_pos h1]
          rw [Work.FTS.Nonlinear.Pieces.mixed_ang_rad,
            show (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ
                  * Work.Elliptic.DzdIter j r z * Work.Spaces.Wt α z θ) ^ 2
                = ((Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ
                    * Work.Elliptic.DzdIter j r z) * Work.Spaces.Wt α z θ) ^ 2 from by ring,
            heavy_sq_nn α _ z θ hs]
          exact le_of_eq (by ring)
        · rw [if_neg (fun h => h2 h.2), if_pos h1]
          exact mul_nonneg (mul_nonneg (sq_nonneg _) hsmGnn)
            (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      · rw [if_neg (fun h => h1 h.1), if_neg h1]
        simp
    calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i then
                (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2 * smG α θ else 0)
              * ((Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm2 i hi j hj
      _ = Rint r z * (∑ i ∈ Finset.range 5, if 1 ≤ i then
            (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2 * smG α θ else 0) := by
          rw [← Finset.sum_mul_sum, Rint]
          ring
  -- ### the angular profile sum: four terms, each `≤ B1²G²`, whence the coefficient `4`
  have hMsum : (∑ i ∈ Finset.range 5, if 1 ≤ i then
        (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2 * smG α θ else 0)
      ≤ 4 * B1 ^ 2 * (G θ) ^ 2 * smG α θ := by
    have hstep : ∀ i ∈ Finset.range 5,
        (if 1 ≤ i then
            (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2 * smG α θ else 0)
        ≤ (if 1 ≤ i then B1 ^ 2 * (G θ) ^ 2 * smG α θ else 0) := by
      intro i hi
      by_cases h1 : 1 ≤ i
      · rw [if_pos h1, if_pos h1]
        have hi4 : i ≤ 4 := by
          have := Finset.mem_range.mp hi
          omega
        have hb := ha1 i h1 hi4 θ hθ
        have h3 : (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
            ≤ B1 ^ 2 * (G θ) ^ 2 := by
          have h4 := pow_le_pow_left₀ (abs_nonneg _) hb 2
          rw [sq_abs, mul_pow] at h4
          exact h4
        exact mul_le_mul_of_nonneg_right h3 hsmGnn
      · rw [if_neg h1, if_neg h1]
    calc (∑ i ∈ Finset.range 5, if 1 ≤ i then
            (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2 * smG α θ else 0)
        ≤ ∑ i ∈ Finset.range 5,
            (if 1 ≤ i then B1 ^ 2 * (G θ) ^ 2 * smG α θ else 0) :=
          Finset.sum_le_sum hstep
      _ = 4 * B1 ^ 2 * (G θ) ^ 2 * smG α θ := by
          rw [← Finset.sum_filter]
          rw [show (Finset.range 5).filter (fun i => 1 ≤ i) = Finset.Icc 1 4 from by decide,
            Finset.sum_const, Nat.card_Icc]
          norm_num
          ring
  have hM : (a θ) ^ 2 * smE θ
        + (∑ i ∈ Finset.range 5, if 1 ≤ i then
            (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2 * smG α θ else 0)
      ≤ B0 ^ 2 * smE θ + 4 * B1 ^ 2 * (G θ) ^ 2 * smG α θ := by
    refine add_le_add ?_ ?_
    · have h2 : (a θ) ^ 2 ≤ B0 ^ 2 := by
        have h3 := pow_le_pow_left₀ (abs_nonneg (a θ)) (abs_le.mpr ⟨hain, hain'⟩) 2
        rwa [sq_abs] at h3
      exact mul_le_mul_of_nonneg_right h2 hsmEnn
    · exact hMsum
  calc Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * r z) z θ
      = (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ
                * Work.Spaces.Wt α z θ) ^ 2
            else 0) := by
          rw [Work.Spaces.HkIntegrand]
    _ ≤ (a θ) ^ 2 * smE θ * Rint r z
          + Rint r z * (∑ i ∈ Finset.range 5, if 1 ≤ i then
              (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2 * smG α θ else 0) :=
        add_le_add (le_of_eq hpure) hmix
    _ = Rint r z * ((a θ) ^ 2 * smE θ
          + (∑ i ∈ Finset.range 5, if 1 ≤ i then
              (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2 * smG α θ else 0)) := by
        ring
    _ ≤ Rint r z * (B0 ^ 2 * smE θ + 4 * B1 ^ 2 * (G θ) ^ 2 * smG α θ) :=
        mul_le_mul_of_nonneg_left hM (Work.FTS.Nonlinear.RadialProd.Rint_nonneg r z)

end Work.FTS.NonlinRows.AuxAngRad
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.Rop_pointwiseW =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

open Work.FTS.Nonlinear.Pieces.RNP.row10aux (deweight_leibniz_sum_le contDiffAt_phi
  wlInf_nonneg_of_mem DthIter_mul_radial DthIter_congr_nhds DthIter_mul_phi)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The smoothness of the weighted star coefficient on the open quadrant

These are the `Q0`-analogues of the `SmoothQuad`-level algebra of
`Work.FTS.LocData`/`row10aux`; keeping them here makes the file self-contained
(`SmoothOpen` is `C^∞` on the *open* quadrant `(0,∞) × (0,π/2)` only, which is all the
primed rows provide). -/

/-- `SmoothOpen` is closed under subtraction. -/
theorem RopW_sub {F G : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ - G z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => F z θ - G z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ => F z θ - G z θ)
      = fun p : ℝ × ℝ => Function.uncurry F p - Function.uncurry G p := rfl
  rw [h]
  exact hF.sub hG

/-- `SmoothOpen` is closed under products. -/
theorem RopW_mul {F G : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => F z θ * G z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => F z θ * G z θ)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z θ => F z θ * G z θ)
      = fun p : ℝ × ℝ => Function.uncurry F p * Function.uncurry G p := rfl
  rw [h]
  exact hF.mul hG

/-- The radial factor `(z+1)/z` is `C^∞` on the open quadrant. -/
theorem RopW_zdiv :
    Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => (z + 1) / z) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z (_ : ℝ) => (z + 1) / z)) Work.FTS.EllipticEst.Q0
  have h : Function.uncurry (fun z (_ : ℝ) => (z + 1) / z)
      = fun p : ℝ × ℝ => (p.1 + 1) / p.1 := rfl
  rw [h]
  refine ContDiffOn.div (contDiffOn_fst.add contDiffOn_const) contDiffOn_fst ?_
  intro p hp
  exact ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1

/-- The singular part `Θ_*(α) = Θ α (F_*) = sin(2θ)/(2(1+z))` of `Φ̃_*` is `C^∞` on the open
quadrant (its `SmoothQuad`-smoothness restricts, since `Q0 ⊆ quadU`). -/
theorem RopW_ThetaFstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Theta α (Work.Construction.Fstar α)) := by
  have hquad : Work.FTS.LocData.SmoothQuad
      (Work.Construction.Theta α (Work.Construction.Fstar α)) :=
    Work.FTS.Nonlinear.Pieces.RNP.row10aux.smoothQuad_Theta_Fstar hα hα1
  refine hquad.mono ?_
  intro p hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact ⟨Set.mem_Ioi.mpr (by linarith), Set.mem_Ioo.mpr ⟨hθ0, hθ1⟩⟩

/-- **`ℛ(Ψ)` is `C^∞` on the open quadrant when `Ψ` is.**  The division by `cos θ` is legitimate
because `cos θ > 0` for `θ ∈ (0,π/2)`, and `∂_zΨ`, `∂_θΨ` are `C^∞` there. -/
theorem RopW_Rop {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Rop α Ψ) := by
  have hQ : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  have hpz : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz Ψ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.LocData.contDiffOn_pz hQ hΨ
  have hpth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth Ψ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.LocData.contDiffOn_pth hQ hΨ
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p)
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const.mul hsin).mul hΨ
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p)
      Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_const.mul hsin).mul contDiffOn_fst).mul hpz
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p)
      Work.FTS.EllipticEst.Q0 :=
    hcos.mul hpth
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p
        + α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p
        + Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p)
      Work.FTS.EllipticEst.Q0 :=
    (h1.add h2).add h3
  have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  refine (hnum.div hcos hne).congr ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  rfl

/-- **The smoothness input of the main estimate**: the weighted star coefficient
`((z+1)/z)·ℛ(Φ̃_*)` is `C^∞` on the open quadrant, from `SmoothOpen Φs`, `0 < α ≤ 1`.

The only role of `α ≤ 1` is the profile identity `L₁₂(F_*) = 2α/(1+z)` which identifies
`Θ_*(α)` with the explicit smooth function `sin(2θ)/(2(1+z))`. -/
theorem RopW_smoothOpen_local {α : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.EllipticEst.SmoothOpen Φs) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z
      * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) := by
  have hΘ : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Theta α (Work.Construction.Fstar α)) :=
    RopW_ThetaFstar hα hα1
  have hPhi : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) := by
    show Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ)
    exact RopW_sub hs hΘ
  have hR : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    RopW_Rop hPhi
  exact RopW_mul RopW_zdiv hR

/-! ## The core estimate -/

/-- **The core estimate.**  From the weighted `𝒲^{4,∞}`-control of `Rv = ((z+1)/z)·ℛ(Φ̃_*)`
(`WlInfMem α 4 Rv`, `WlInf α 4 Rv ≤ Cs α`) and the *open-quadrant* smoothness of `Rv`, the four
pointwise bounds hold with the universal constant `100`.

The only use made of the smoothness hypothesis is to legitimise the Leibniz rule for `∂_z^k`
on the product `Rv = ψ · ℛ` with `ψ = (1+z)/z` (equivalently `ℛ = (z/(1+z))·Rv`), so that
`∂_z^k ℛ = ∑_{i≤k} C(k,i) ∂_z^i(z/(1+z))·∂_z^{k-i} Rv`; the weighted derivatives of the
de-weighting factor are bounded by `i!` (`phi_deriv_bound`), and the de-weighting Leibniz bound
`deweight_leibniz_sum_le` then converts `|(1+z)^j ∂_z^j Rv| ≤ W` into
`|(1+z)^k ∂_z^k ℛ| ≤ 65·W`. -/
theorem Rop_pointwiseW_aux {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hRvs : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (z + 1) / z
      * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ))
    (hmem : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) / z
      * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ))
    (hle : Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z
      * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) ≤ Cs * α) :
    (∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
        ≤ 100 * (max Cs 1 * α) * z / (1 + z)) ∧
    (∀ c : ℕ, c ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pzIter c (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
        ≤ 100 * (max Cs 1 * α) / (1 + z) ^ c) ∧
    (∀ a c : ℕ, 1 ≤ a → a + c ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pzIter c (Work.Spaces.DthIter a
          (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) z θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ 100 * (max Cs 1 * α) / (1 + z) ^ c) ∧
    (∀ a : ℕ, 1 ≤ a → a ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.DthIter a (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ 100 * (max Cs 1 * α) * z / (1 + z)) := by
  let R : ℝ → ℝ → ℝ := Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)
  let Rv : ℝ → ℝ → ℝ := fun z θ => (z + 1) / z * R z θ
  have hmemR : Work.Spaces.WlInfMem α 4 Rv := hmem
  have hleR : Work.Spaces.WlInf α 4 Rv ≤ Cs * α := hle
  have hRvsS : Work.FTS.EllipticEst.SmoothOpen Rv := hRvs
  have hW0 : 0 ≤ Work.Spaces.WlInf α 4 Rv := wlInf_nonneg_of_mem hmemR
  have hWmax : Work.Spaces.WlInf α 4 Rv ≤ max Cs 1 * α :=
    le_trans hleR (mul_le_mul_of_nonneg_right (le_max_left Cs 1) hα.le)
  have hCM0 : 0 ≤ max Cs 1 * α :=
    mul_nonneg (le_trans zero_le_one (le_max_right Cs 1)) hα.le
  -- the de-weighting identity `ℛ = (z/(1+z))·Rv` on `z > 0`
  have hRQ : ∀ z θ : ℝ, 0 < z → R z θ = z / (1 + z) * Rv z θ := by
    intro z θ hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    have hz1 : (1 : ℝ) + z ≠ 0 := by positivity
    simp only [Rv]
    field_simp
    ring
  -- smoothness of the `z`-slices of `Rv`
  have hRvsSlice : ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ContDiffAt ℝ Work.Stability.smoothOrder (fun z' => Rv z' θ) z :=
    fun z hz θ hθ =>
      (hRvsS.curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds hz)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) the plain pointwise bound
    intro z hz θ hθ
    show |R z θ| ≤ 100 * (max Cs 1 * α) * z / (1 + z)
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
    have hθIz : θ ∈ Work.Spaces.Iθ := Set.mem_Icc.mpr ⟨hθ.1.le, hθ.2.le⟩
    have hφnn : 0 ≤ z / (1 + z) := by positivity
    have hWpt : |Rv z θ| ≤ Work.Spaces.WlInf α 4 Rv := by
      have h := Work.Spaces.WlInf_z_bound α 4 Rv hmemR 0 (by norm_num) z θ hzIz hθIz
      simpa using h
    calc |R z θ| = z / (1 + z) * |Rv z θ| := by
          rw [hRQ z θ hz, abs_mul, abs_of_nonneg hφnn]
      _ ≤ z / (1 + z) * (max Cs 1 * α) :=
          mul_le_mul_of_nonneg_left (le_trans hWpt hWmax) hφnn
      _ ≤ 100 * (max Cs 1 * α) * z / (1 + z) := by
          have hX : 0 ≤ (max Cs 1 * α) * (z / (1 + z)) := mul_nonneg hCM0 hφnn
          calc z / (1 + z) * (max Cs 1 * α)
              = 1 * ((max Cs 1 * α) * (z / (1 + z))) := by ring
            _ ≤ 100 * ((max Cs 1 * α) * (z / (1 + z))) :=
                mul_le_mul_of_nonneg_right (by norm_num) hX
            _ = 100 * (max Cs 1 * α) * z / (1 + z) := by ring
  · -- (2) the radial derivatives `∂_z^c ℛ`
    intro c hc z hz θ hθ
    show |Work.Spaces.pzIter c R z θ| ≤ 100 * (max Cs 1 * α) / (1 + z) ^ c
    rw [show (1 : ℝ) + z = z + 1 from by ring]
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
    have hθIz : θ ∈ Work.Spaces.Iθ := Set.mem_Icc.mpr ⟨hθ.1.le, hθ.2.le⟩
    have hz1 : (0 : ℝ) < z + 1 := by linarith
    have hEq : Work.Spaces.pzIter c R z θ
        = ∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ)
            * (Work.Spaces.pzIter i (fun z θ => z / (1 + z)) z θ
              * Work.Spaces.pzIter (c - i) Rv z θ) := by
      have hcongr : Work.Spaces.pzIter c R z θ
          = Work.Spaces.pzIter c (fun z θ => z / (1 + z) * Rv z θ) z θ := by
        rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv]
        refine Filter.EventuallyEq.iteratedDeriv_eq c ?_
        refine Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz) (fun z' hz' => ?_)
        exact hRQ z' θ (Set.mem_Ioi.mp hz')
      rw [hcongr]
      exact Work.FTS.H2.Q.pzIter_mul_local_sm c (contDiffAt_phi hz)
        ((hRvsS.curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds hz))
    have hkey : |(z + 1) ^ c * Work.Spaces.pzIter c R z θ| ≤ 65 * Work.Spaces.WlInf α 4 Rv := by
      rw [hEq]
      simpa using deweight_leibniz_sum_le (X := Rv) (W := Work.Spaces.WlInf α 4 Rv) (σ := 1)
        hc zero_le_one hz.le hW0 (fun i hi => by
          have hic : i ≤ c := hi
          have h := Work.Spaces.WlInf_z_bound α 4 Rv hmemR (c - i) (by omega) z θ hzIz hθIz
          simpa using h)
    rw [abs_mul, abs_of_nonneg (pow_nonneg hz1.le c)] at hkey
    have hfinal : |Work.Spaces.pzIter c R z θ| ≤ 65 * (max Cs 1 * α) / (z + 1) ^ c := by
      rw [le_div_iff₀ (pow_pos hz1 c)]
      calc |Work.Spaces.pzIter c R z θ| * (z + 1) ^ c
          = (z + 1) ^ c * |Work.Spaces.pzIter c R z θ| := by ring
        _ ≤ 65 * Work.Spaces.WlInf α 4 Rv := hkey
        _ ≤ 65 * (max Cs 1 * α) := mul_le_mul_of_nonneg_left hWmax (by norm_num)
    calc |Work.Spaces.pzIter c R z θ| ≤ 65 * (max Cs 1 * α) / (z + 1) ^ c := hfinal
      _ ≤ 100 * (max Cs 1 * α) / (z + 1) ^ c :=
          div_le_div_of_nonneg_right (by linarith [hCM0]) (pow_nonneg hz1.le c)
  · -- (3) the mixed derivatives `∂_z^c D_θ^a ℛ`, `a ≥ 1`
    intro a c ha hac z hz θ hθ
    show |Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ 100 * (max Cs 1 * α) / (1 + z) ^ c
    rw [show (1 : ℝ) + z = z + 1 from by ring]
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
    have hθIz : θ ∈ Work.Spaces.Iθ := Set.mem_Icc.mpr ⟨hθ.1.le, hθ.2.le⟩
    have hz1 : (0 : ℝ) < z + 1 := by linarith
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    have hσnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
      div_nonneg (Real.rpow_nonneg hsin0 _) (by linarith)
    -- `D_θ^a ℛ = (z/(1+z))·D_θ^a Rv` on the open quadrant
    have hDth : ∀ z' : ℝ, 0 < z' → Work.Spaces.DthIter a R z' θ
        = z' / (1 + z') * Work.Spaces.DthIter a Rv z' θ := by
      intro z' hz'
      have hV : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (π / 2)),
          R p.1 p.2 = p.1 / (1 + p.1) * Rv p.1 p.2 := by
        rintro ⟨z'', θ''⟩ ⟨hz'', -⟩
        exact hRQ z'' θ'' hz''
      rw [DthIter_congr_nhds (u := R) (v := fun z θ => z / (1 + z) * Rv z θ)
        (V := Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (π / 2)) (isOpen_Ioi.prod isOpen_Ioo) hV a z' θ
        ⟨hz', hθ⟩, DthIter_mul_phi]
    have hEq : Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ
        = ∑ i ∈ Finset.range (c + 1), (c.choose i : ℝ)
            * (Work.Spaces.pzIter i (fun z θ => z / (1 + z)) z θ
              * Work.Spaces.pzIter (c - i) (Work.Spaces.DthIter a Rv) z θ) := by
      have hcongr : Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ
          = Work.Spaces.pzIter c
              (fun z θ => z / (1 + z) * Work.Spaces.DthIter a Rv z θ) z θ := by
        rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv]
        refine Filter.EventuallyEq.iteratedDeriv_eq c ?_
        refine Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz) (fun z' hz' => ?_)
        exact hDth z' (Set.mem_Ioi.mp hz')
      rw [hcongr]
      exact Work.FTS.H2.Q.pzIter_mul_local_sm c (contDiffAt_phi hz)
        (((hRvsS.DthIter a).curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds hz))
    have hkey : |(z + 1) ^ c * Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))|
        ≤ 65 * Work.Spaces.WlInf α 4 Rv := by
      rw [hEq]
      simpa using deweight_leibniz_sum_le (X := Work.Spaces.DthIter a Rv)
        (W := Work.Spaces.WlInf α 4 Rv)
        (σ := (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        (by omega : c ≤ 4) hσnn hz.le hW0 (fun i hi => by
          have hic : i ≤ c := hi
          have h := Work.Spaces.WlInf_mixed_bound α 4 Rv hmemR a (c - i) ha (by omega) z θ
            hzIz hθIz
          simpa only [← mul_div_assoc] using h)
    have hkey2 : (z + 1) ^ c * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
        ≤ 65 * Work.Spaces.WlInf α 4 Rv := by
      have h := hkey
      rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hz1.le c), abs_of_nonneg hσnn] at h
      calc (z + 1) ^ c * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))))
          = ((z + 1) ^ c * |Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|)
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by ring
        _ ≤ 65 * Work.Spaces.WlInf α 4 Rv := h
    have hfinal : |Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ 65 * (max Cs 1 * α) / (z + 1) ^ c := by
      rw [le_div_iff₀ (pow_pos hz1 c)]
      calc (|Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) * (z + 1) ^ c
          = (z + 1) ^ c * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by ring
        _ ≤ 65 * Work.Spaces.WlInf α 4 Rv := hkey2
        _ ≤ 65 * (max Cs 1 * α) := mul_le_mul_of_nonneg_left hWmax (by norm_num)
    calc |Work.Spaces.pzIter c (Work.Spaces.DthIter a R) z θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ 65 * (max Cs 1 * α) / (z + 1) ^ c := hfinal
      _ ≤ 100 * (max Cs 1 * α) / (z + 1) ^ c :=
          div_le_div_of_nonneg_right (by linarith [hCM0]) (pow_nonneg hz1.le c)
  · -- (4) the angular derivatives `D_θ^a ℛ`, `a ≥ 1`
    intro a ha ha4 z hz θ hθ
    show |Work.Spaces.DthIter a R z θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ 100 * (max Cs 1 * α) * z / (1 + z)
    have hzIz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
    have hθIz : θ ∈ Work.Spaces.Iθ := Set.mem_Icc.mpr ⟨hθ.1.le, hθ.2.le⟩
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    have hφnn : 0 ≤ z / (1 + z) := by positivity
    have hDth : Work.Spaces.DthIter a R z θ = z / (1 + z) * Work.Spaces.DthIter a Rv z θ := by
      have hV : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (π / 2)),
          R p.1 p.2 = p.1 / (1 + p.1) * Rv p.1 p.2 := by
        rintro ⟨z'', θ''⟩ ⟨hz'', -⟩
        exact hRQ z'' θ'' hz''
      rw [DthIter_congr_nhds (u := R) (v := fun z θ => z / (1 + z) * Rv z θ)
        (V := Set.Ioi 0 ×ˢ Set.Ioo (0 : ℝ) (π / 2)) (isOpen_Ioi.prod isOpen_Ioo) hV a z θ
        ⟨hz, hθ⟩, DthIter_mul_phi]
    have hmix : |Work.Spaces.DthIter a Rv z θ|
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ≤ Work.Spaces.WlInf α 4 Rv := by
      have h := Work.Spaces.WlInf_mixed_bound α 4 Rv hmemR a 0 ha (by omega) z θ hzIz hθIz
      have hσ2 : 0 ≤ (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) :=
        div_nonneg (Real.rpow_nonneg hsin0 _) (by linarith)
      have hden2 : 0 < α + Real.sin (2 * θ) := by linarith
      rw [pow_zero, one_mul, Work.Spaces.pzIter_zero, abs_div, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hsin0 _), abs_of_pos hden2] at h
      simpa only [mul_div_assoc] using h
    calc |Work.Spaces.DthIter a R z θ|
          * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        = z / (1 + z) * (|Work.Spaces.DthIter a Rv z θ|
            * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))) := by
          rw [hDth, abs_mul, abs_of_nonneg hφnn]; ring
      _ ≤ z / (1 + z) * (max Cs 1 * α) :=
          mul_le_mul_of_nonneg_left (le_trans hmix hWmax) hφnn
      _ ≤ 100 * (max Cs 1 * α) * z / (1 + z) := by
          have hX : 0 ≤ (max Cs 1 * α) * (z / (1 + z)) := mul_nonneg hCM0 hφnn
          calc z / (1 + z) * (max Cs 1 * α)
              = 1 * ((max Cs 1 * α) * (z / (1 + z))) := by ring
            _ ≤ 100 * ((max Cs 1 * α) * (z / (1 + z))) :=
                mul_le_mul_of_nonneg_right (by norm_num) hX
            _ = 100 * (max Cs 1 * α) * z / (1 + z) := by ring

/- The pointwise `𝒲^{4,∞}`-bounds for the star coefficient `ℛ(Φ̃_*)` in the primed
(open-quadrant) setting, from the *weighted* field `WlInfMem α 4 Rv ∧ WlInf α 4 Rv ≤ Cs α`
(`Rv = ((z+1)/z)·ℛ(Φ̃_*)`): the exact analogue of the proved `Rop_pointwiseU`
(`Submission/Work/FTS/Nonlinear/Pieces/RNP/Rop_pointwiseU.lean`, which derives the same four
conjuncts from `StarPkg`), with the package hypothesis replaced by the two `WlInf` conjuncts of
`StarPkg.R`.  This is the bridge that turns the (missing) weighted decay of the star coefficient
into the pointwise inputs of the primed rows 10, 11, 15, 19; the proof is `Rop = z/(1+z)·Rv` plus
`WlInf_z_bound`/`WlInf_mixed_bound` and the Leibniz rule in `z` (with `|∂_z^j(z/(1+z))| ≤ j!/(1+z)^{j+1}`),
so no truncation of the angular boundary lines is needed and `SmoothOpen` (not `SmoothQuad`)
suffices. -/

end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row19aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The coefficient `V(Φ̃_*) = ∂_θΦ̃_* - tan θ · Φ̃_*` of `N₃^{**}` (row 19). -/
abbrev Vs (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) : ℝ → ℝ → ℝ :=
  Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)

/-- The factor `D_zF_* = z ∂_zF_*` of `N₃^{**}` (row 19). -/
abbrev Gs (α : ℝ) : ℝ → ℝ → ℝ := Work.Spaces.Dz (Work.Construction.Fstar α)


/-- `N₃^{**} = -2α·(V(Φ̃_*)·D_zF_*)`, with the scalar `-2α` pulled out of the product. -/
theorem N3ss_eq (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) :
    Work.FTS.Nonlin.N3ss α Φs
      = fun z θ => (-(2 * α)) * (Vs α Φs z θ * Gs α z θ) := by
  funext z θ
  simp only [Work.FTS.Nonlin.N3ss, Vs, Gs]
  ring

/-- The `ℋ⁴`-norm of `N₃^{**}` is `2α` times the `ℋ⁴`-norm of the product `V(Φ̃_*)·D_zF_*`. -/
theorem xn_N3ss (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) :
    Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs)
      = |-(2 * α)| * Work.FTS.Nonlin.Xn α (fun z θ => Vs α Φs z θ * Gs α z θ) := by
  rw [N3ss_eq]
  exact Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α (-(2 * α)) _

/-- For `α ≥ 0` the prefactor is `2α`. -/
theorem xn_N3ss_of_nonneg {α : ℝ} (hα : 0 ≤ α) (Φs : Work.FTS.Galerkin.Fn) :
    Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs)
      = 2 * α * Work.FTS.Nonlin.Xn α (fun z θ => Vs α Φs z θ * Gs α z θ) := by
  rw [xn_N3ss, abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * α)]

/-- **The pointwise bound on the coefficient.**  `StarPkg.V` bounds `V(Φ̃_*)` in `𝒲^{4,∞}` by
`Cs·α`; the `k = 0` summand of the `𝒲^{4,∞}`-norm is the honest supremum, so
`|V(Φ̃_*)(z,θ)| ≤ max Cs 0 · α` on the domain. -/
theorem abs_Vs_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Vs α Φs z θ| ≤ max Cs 0 * α := by
  intro z hz θ hθ
  have hle : Cs * α ≤ max Cs 0 * α :=
    mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le
  exact Work.FTS.Nonlinear.Pieces.rl1Tools.abs_le_WlInf_of_mem hs.V.1
    (le_trans hs.V.2 hle) hz hθ

/-- The first `z`-derivative of `V(Φ̃_*)` is bounded: the `k = 1` summand of the `𝒲^{4,∞}`-norm
gives `|(z+1)·∂_zV| ≤ max Cs 0 · α`. -/
theorem abs_dVs_le {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) * Work.Spaces.pz (Vs α Φs) z θ| ≤ max Cs 0 * α := by
  intro z hz θ hθ
  have hle : Cs * α ≤ max Cs 0 * α :=
    mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le
  have h := Work.Spaces.WlInf_z_bound α 4 (Vs α Φs) hs.V.1 1 (by norm_num) z θ hz hθ
  simpa using le_trans h (le_trans hs.V.2 hle)

end Work.FTS.Nonlinear.Pieces.RNP
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.RNP.row23 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The order-one angular bound for `Γ` -/

/-- The first `D_θ`-iterate of `Γ` is `≤ (4/3)αΓ` on the whole closed angular interval:
in the interior `D_θΓ = α q Γ` with `|q| ≤ 4/3`, and at the two endpoints both sides vanish. -/
theorem dthIter_one_Gam_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter 1 (fun _ (θ' : ℝ) => Work.Spaces.Gam α θ') 0 θ|
        ≤ (4 / 3) * α * Work.Spaces.Gam α θ := by
  intro θ hθ
  have hΓ0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  rw [Work.FTS.LocData.DthIter_rad_eq 1 (fun t => Work.Spaces.Gam α t) 0 θ,
    Function.iterate_one]
  rcases lt_or_eq_of_le hθ.1 with h0 | h0
  · rcases lt_or_eq_of_le hθ.2 with h1 | h1
    · rw [Work.Spaces.dthU_Gam α θ hα ⟨h0, h1⟩, abs_mul, abs_mul, abs_of_pos hα,
        abs_of_nonneg hΓ0]
      have hq : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
        rw [Work.Spaces.qfun, abs_le]
        constructor <;> linarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
      calc α * |Work.Spaces.qfun θ| * Work.Spaces.Gam α θ
          ≤ α * (4 / 3) * Work.Spaces.Gam α θ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hq (le_of_lt hα)) hΓ0
        _ = (4 / 3) * α * Work.Spaces.Gam α θ := by ring
    · subst h1
      rw [Work.Spaces.dthU_apply, show 2 * (Real.pi / 2) = Real.pi from by ring,
        Real.sin_pi, zero_mul, abs_zero, Work.Spaces.Gam_zero_right α (ne_of_gt hα)]
      simp
  · subst h0
    rw [Work.Spaces.dthU_apply, show 2 * (0 : ℝ) = 0 from by ring, Real.sin_zero, zero_mul,
      abs_zero, Work.Spaces.Gam_zero_left α (ne_of_gt hα)]
    simp

/-! ## Separation of an angular profile from a radial function, with an arbitrary angular
majorant -/

open Work.FTS.Nonlinear.RadialProd in
/-- **Separation of an angular profile and a radial function in `ℋ⁴`, with a general angular
majorant.**  For an angular profile `a` bounded by `B0` whose `D_θ`-iterates up to order `4` are
bounded by `B1·G` (with `G ≥ 0` a fixed angular function), and a radial function `r` of class
`ℋ⁴`,

  `|a·r|_{ℋ⁴} ≤ √(10000·B0² + 4·B1²·M1)·|r|_{ℋ⁴}`,

where `M1 ≥ ∫_θ G(θ)²·sin(2θ)^{-γ}dθ`.  This is `Xn_ang_rad_le` with `sin(2θ)^κ` replaced by
`G`; it is lossless in the factor `r` (the `θ`-integration is separated). -/
theorem Xn_ang_rad_le_gen (α : ℝ) (hα : 0 < α) (a : ℝ → ℝ) (r : ℝ → ℝ) (G : ℝ → ℝ)
    {B0 B1 M1 : ℝ} (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hM1 : 0 ≤ M1)
    (hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ)
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ| ≤ B1 * G θ)
    (hI1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => G θ ^ 2 * smG α θ) Work.Spaces.Iθ)
    (hm1 : ∫ θ in Work.Spaces.Iθ, G θ ^ 2 * smG α θ ≤ M1)
    (hrmem : Work.Spaces.HkMem α 4 (fun z θ => r z)) :
    Work.FTS.Nonlin.Xn α (fun z θ => a θ * r z)
      ≤ Real.sqrt (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1)
        * Work.FTS.Nonlin.Xn α (fun z θ => r z) := by
  have hLam : (0 : ℝ) ≤ B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1 := by positivity
  -- ### Step 1: the pointwise (in `θ`) bound on the `ℋ⁴`-integrand
  have hpt : ∀ z θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * r z) z θ
        ≤ Rint r z * (B0 ^ 2 * smE θ + 4 * B1 ^ 2 * (G θ ^ 2 * smG α θ)) := by
    intro z θ hθ
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    obtain ⟨hain, hain'⟩ := abs_le.mp (ha0 θ hθI)
    -- the pure slots
    have hpure : (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = (a θ) ^ 2 * smE θ * Rint r z := by
      have hterm : ∀ i : ℕ, (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (a θ) ^ 2 * smE θ
            * ((Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
        intro i
        rw [dzIter_ang_rad,
          show (a θ * Work.Elliptic.DzdIter i r z
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              = ((a θ * Work.Elliptic.DzdIter i r z)
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            from by ring,
          light_sq _ z θ hsin]
        ring
      calc (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          = ∑ i ∈ Finset.range 5, (a θ) ^ 2 * smE θ
              * ((Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
            Finset.sum_congr rfl fun i _ => hterm i
        _ = (a θ) ^ 2 * smE θ * Rint r z := by
            rw [← Finset.mul_sum, Rint]
    -- the mixed slots
    have hmix : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ Rint r z * (∑ i ∈ Finset.range 5, if 1 ≤ i then
            (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0) := by
      have hterm2 : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
          ≤ (if 1 ≤ i then
                (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0)
            * ((Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
        intro i hi j hj
        by_cases h1 : 1 ≤ i
        · by_cases h2 : i + j ≤ 4
          · rw [if_pos ⟨h1, h2⟩, if_pos h1]
            rw [mixed_ang_rad,
              show (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ
                    * Work.Elliptic.DzdIter j r z * Work.Spaces.Wt α z θ) ^ 2
                  = ((Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ
                      * Work.Elliptic.DzdIter j r z) * Work.Spaces.Wt α z θ) ^ 2 from by ring,
              heavy_sq α _ z θ hsin]
            exact le_of_eq (by ring)
          · rw [if_neg (fun h => h2 h.2), if_pos h1]
            exact mul_nonneg (mul_nonneg (sq_nonneg _) (smG_nonneg hθI))
              (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        · rw [if_neg (fun h => h1 h.1), if_neg h1]
          simp
      calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
            else 0)
          ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i then
                  (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0)
                * ((Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
            Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm2 i hi j hj
        _ = Rint r z * (∑ i ∈ Finset.range 5, if 1 ≤ i then
              (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0) := by
            rw [← Finset.sum_mul_sum, Rint]
            ring
    -- the comparison of the two profiles
    have hMsum : (∑ i ∈ Finset.range 5, if 1 ≤ i then
          (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0)
        ≤ ∑ i ∈ Finset.range 5, if 1 ≤ i then
            B1 ^ 2 * (G θ ^ 2 * smG α θ) else 0 := by
      refine Finset.sum_le_sum fun i hi => ?_
      by_cases h1 : 1 ≤ i
      · rw [if_pos h1, if_pos h1]
        have hi4 : i ≤ 4 := by
          have := Finset.mem_range.mp hi
          omega
        have hb := ha1 i h1 hi4 θ hθI
        have h3 : (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 ≤ B1 ^ 2 * G θ ^ 2 := by
          have h4 := pow_le_pow_left₀ (abs_nonneg _) hb 2
          rw [sq_abs, mul_pow] at h4
          exact h4
        calc (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ
            ≤ (B1 ^ 2 * G θ ^ 2) * smG α θ :=
              mul_le_mul_of_nonneg_right h3 (smG_nonneg hθI)
          _ = B1 ^ 2 * (G θ ^ 2 * smG α θ) := by ring
      · rw [if_neg h1, if_neg h1]
    have hMs : (∑ i ∈ Finset.range 5, if 1 ≤ i then
          B1 ^ 2 * (G θ ^ 2 * smG α θ) else 0)
        = 4 * B1 ^ 2 * (G θ ^ 2 * smG α θ) := by
      rw [← Finset.sum_filter]
      rw [show (Finset.range 5).filter (fun i => 1 ≤ i) = Finset.Icc 1 4 from by decide,
        Finset.sum_const, Nat.card_Icc]
      norm_num
      ring
    have hM : (a θ) ^ 2 * smE θ + (∑ i ∈ Finset.range 5, if 1 ≤ i then
          (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0)
        ≤ B0 ^ 2 * smE θ + 4 * B1 ^ 2 * (G θ ^ 2 * smG α θ) := by
      refine add_le_add ?_ ?_
      · have h2 : (a θ) ^ 2 ≤ B0 ^ 2 := by
          have h3 := pow_le_pow_left₀ (abs_nonneg (a θ)) (abs_le.mpr ⟨hain, hain'⟩) 2
          rwa [sq_abs] at h3
        exact mul_le_mul_of_nonneg_right h2 (smE_nonneg hθI)
      · exact hMsum.trans (le_of_eq hMs)
    calc Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * r z) z θ
        = (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              if 1 ≤ i ∧ i + j ≤ 4 then
                (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ
                  * Work.Spaces.Wt α z θ) ^ 2
              else 0) := by
            rw [Work.Spaces.HkIntegrand]
      _ ≤ (a θ) ^ 2 * smE θ * Rint r z
            + Rint r z * (∑ i ∈ Finset.range 5, if 1 ≤ i then
                (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0) :=
          add_le_add (le_of_eq hpure) hmix
      _ = Rint r z * ((a θ) ^ 2 * smE θ
            + (∑ i ∈ Finset.range 5, if 1 ≤ i then
                (Work.Spaces.DthIter i (fun _ θ' => a θ') 0 θ) ^ 2 * smG α θ else 0)) := by
          ring
      _ ≤ Rint r z * (B0 ^ 2 * smE θ + 4 * B1 ^ 2 * (G θ ^ 2 * smG α θ)) :=
          mul_le_mul_of_nonneg_left hM (Rint_nonneg r z)
  -- ### Step 2: the angular integrals
  have hexp1 : -1 < -(Work.Spaces.eta) := by
    have := Work.Spaces.eta_lt_one; linarith
  have hle0 : -(Work.Spaces.eta) ≤ 0 := by
    have := Work.Spaces.eta_pos; linarith
  have hIf : MeasureTheory.IntegrableOn (fun θ : ℝ => B0 ^ 2 * smE θ) Work.Spaces.Iθ := by
    change MeasureTheory.IntegrableOn
      (fun θ : ℝ => B0 ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ
    exact (Work.Spaces.sin_two_rpow _ hexp1 hle0).1.const_mul _
  have hIg : MeasureTheory.IntegrableOn (fun θ : ℝ => 4 * B1 ^ 2 * (G θ ^ 2 * smG α θ))
      Work.Spaces.Iθ := hI1.const_mul _
  have hIntA : MeasureTheory.IntegrableOn (fun θ : ℝ => B0 ^ 2 * smE θ
      + 4 * B1 ^ 2 * (G θ ^ 2 * smG α θ)) Work.Spaces.Iθ := hIf.add hIg
  have hA : (∫ θ in Work.Spaces.Iθ, smE θ) ≤ 10000 := by
    change (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ 10000
    have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) hexp1 hle0).2
    have h1 : -(Work.Spaces.eta) + 1 = (1 : ℝ) / 100 := by rw [Work.Spaces.eta]; norm_num
    rw [h1] at h
    norm_num at h
    exact h
  have hboundA : (∫ θ in Work.Spaces.Iθ, B0 ^ 2 * smE θ
        + 4 * B1 ^ 2 * (G θ ^ 2 * smG α θ)) ≤ B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1 := by
    rw [MeasureTheory.integral_add hIf hIg, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    have h1 := mul_le_mul_of_nonneg_left hA (sq_nonneg B0)
    have h2 := mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℝ) ≤ 4 * B1 ^ 2)
    linarith
  -- ### Step 3: integrate in `θ` and then in `z`
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * r z) z θ)
        ≤ Rint r z * (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1) := by
    intro z
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * r z) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, Rint r z * (B0 ^ 2 * smE θ
            + 4 * B1 ^ 2 * (G θ ^ 2 * smG α θ)) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
            (hIntA.const_mul _) ?_
          filter_upwards [Work.H2.T1Q.ae_mem_Ioo_Iθ] with θ hθ
          exact hpt z θ hθ
      _ = Rint r z * (∫ θ in Work.Spaces.Iθ, B0 ^ 2 * smE θ
            + 4 * B1 ^ 2 * (G θ ^ 2 * smG α θ)) :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Rint r z * (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1) :=
          mul_le_mul_of_nonneg_left hboundA (Rint_nonneg r z)
  have houter : Work.Spaces.HkSq α 4 (fun z θ => a θ * r z)
      ≤ (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1) * ∫ z in Work.Spaces.Iz, Rint r z := by
    rw [Work.Spaces.HkSq]
    have hEq : (∫ z in Work.Spaces.Iz, Rint r z
          * (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1))
        = (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1)
          * ∫ z in Work.Spaces.Iz, Rint r z := by
      rw [MeasureTheory.integral_mul_const]; ring
    rw [← hEq]
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
      ((integrable_Rint α r hrmem).mul_const _)
      (Filter.Eventually.of_forall hinner)
  have hfin : Work.Spaces.HkSq α 4 (fun z θ => a θ * r z)
      ≤ (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1)
        * Work.Spaces.HkSq α 4 (fun z θ => r z) := by
    refine houter.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hLam
    rw [show (∫ z in Work.Spaces.Iz, Rint r z) = Rr r from rfl]
    exact Rr_le_HkSq α r
  calc Work.FTS.Nonlin.Xn α (fun z θ => a θ * r z)
      = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => a θ * r z)) := rfl
    _ ≤ Real.sqrt ((B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1)
          * Work.Spaces.HkSq α 4 (fun z θ => r z)) := Real.sqrt_le_sqrt hfin
    _ = Real.sqrt (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1)
          * Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => r z)) := Real.sqrt_mul hLam _
    _ = Real.sqrt (B0 ^ 2 * 10000 + 4 * B1 ^ 2 * M1)
          * Work.FTS.Nonlin.Xn α (fun z θ => r z) := rfl


end Work.FTS.Nonlinear.Pieces.RNP
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.angmul_field =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem angmul_field :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (a : ℝ → ℝ) (f : Work.FTS.Galerkin.Fn) (Ca : ℝ),
      Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
      (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ca) →
      (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ca * Real.sin (2 * θ)) →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => a θ * f z θ) ≤ C * Ca * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.Nonlinear.N4Fields.HkIntegrand_ang_mul_unit_le_Int 4
  refine ⟨1 + Real.sqrt C₁, by positivity, ?_⟩
  intro α hα0 hα1 a f Ca hSO haB haIt hf hmem
  -- the profile hypothesis is `C^∞`-on-`Q0` of the uncurried profile
  have hCD : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2)
      Work.FTS.EllipticEst.Q0 := hSO
  -- the bound `|a θ| ≤ Ca` for the nonempty `Iθ` forces `0 ≤ Ca`
  have hCa : 0 ≤ Ca := le_trans (abs_nonneg (a 0)) (haB 0 Work.Spaces.zero_mem_Iθ)
  rcases eq_or_lt_of_le hCa with hCa0 | hCapos
  · -- ## `Ca = 0`: the profile vanishes on `Iθ`
    have ha0 : ∀ θ ∈ Work.Spaces.Iθ, a θ = 0 := by
      intro θ hθ
      have h1 := haB θ hθ
      rw [← hCa0] at h1
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    have hzero : ∀ z θ : ℝ, θ ∈ Work.Spaces.Iθ →
        Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) z θ = 0 := by
      intro z θ hθ
      rw [Work.Spaces.HkIntegrand]
      have h1 : (∑ i ∈ Finset.range (4 + 1),
          (Work.Spaces.DzIter i (fun z θ => a θ * f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        simp only [Work.FTS.EllipticEst.Blocks.DzIter_angular_mul i a f]
        simp [ha0 θ hθ]
      have h2 : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
          if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => a θ * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0) = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        split_ifs with hc
        · rw [Work.Spaces.mixed]
          rw [Work.Coercivity.DzIter_eq_zero_of_forall_eq_zero
            (Work.Spaces.DthIter i (fun z θ => a θ * f z θ)) θ
            (fun z' => Work.FTS.Nonlinear.N4Fields.DthIter_angmul_eq_zero a f ha0 i hc.1 z' θ hθ)
            j z,
            zero_mul, sq, mul_zero]
        · rfl
      rw [h1, h2, add_zero]
    have hmem' : Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) := by
      refine Work.FTS.LocData.HkMem_of_majorant (M := fun _ _ => (0 : ℝ)) α 4 ?_ ?_ ?_ ?_
      · have h0 : ContinuousOn (fun _ : ℝ × ℝ => (0 : ℝ)) Work.FTS.EllipticEst.Q0 :=
          continuousOn_const
        refine h0.congr ?_
        intro p hp
        exact hzero p.1 p.2 ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩
      · intro z hz; exact integrableOn_zero
      · have hthis : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (fun _ _ => (0 : ℝ)) z θ)
            = fun _ => (0 : ℝ) := by
          funext z; simp
        rw [hthis]
        exact integrableOn_zero
      · intro z hz θ hθ; rw [hzero z θ hθ]
    refine ⟨hmem', ?_⟩
    have hsq : Work.Spaces.HkSq α 4 (fun z θ => a θ * f z θ) = 0 := by
      rw [Work.Spaces.HkSq]
      have hinner : ∀ z : ℝ,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) z θ)
            = 0 := by
        intro z
        rw [MeasureTheory.integral_eq_zero_of_ae]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun θ hθ => hzero z θ hθ)
      simp only [hinner, integral_zero]
    rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, hsq, Real.sqrt_zero, ← hCa0]
    simp
  · -- ## `Ca > 0`: rescale to `a' = a / Ca` and use the uniform unit bound
    set a' : ℝ → ℝ := fun θ => a θ / Ca with ha'def
    have hCane : Ca ≠ 0 := hCapos.ne'
    have ha'CD : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a' p.2)
        Work.FTS.EllipticEst.Q0 := by
      have h := hCD.div_const Ca
      simpa only [ha'def] using h
    have ha'1 : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |a' θ| ≤ 1 := by
      intro θ hθ
      have h1 := haB θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have h2 : |a' θ| = |a θ| / Ca := by
        rw [ha'def, abs_div, abs_of_pos hCapos]
      rw [h2]
      exact (div_le_one hCapos).mpr h1
    have ha'It : ∀ m : ℕ, 1 ≤ m → m ≤ 4 → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        (Work.FTS.EllipticEst.LopIter m a' θ) ^ 2 ≤ (Real.sin (2 * θ)) ^ 2 := by
      intro m hm1 hm4 θ hθ
      -- the `Lop`-iterate of the rescaled profile
      have hlin : ∀ θ' : ℝ,
          Work.FTS.EllipticEst.LopIter m a' θ'
            = Ca⁻¹ * Work.FTS.EllipticEst.LopIter m a θ' := by
        have h1 : a' = fun θ => Ca⁻¹ * a θ := by
          funext θ'; rw [ha'def]; field_simp
        intro θ'
        rw [h1, congrFun (Work.FTS.EllipticEst.Blocks.LopIter_const_mul Ca⁻¹ m a) θ']
      -- the interface hypothesis, in `Lop`-form
      have hbound : |Work.FTS.EllipticEst.LopIter m a θ| ≤ Ca * Real.sin (2 * θ) := by
        have h2 : Work.FTS.EllipticEst.LopIter m a θ
            = Work.Spaces.DthIter m (fun _ (θ' : ℝ) => a θ') 0 θ := by
          rw [Work.Spaces.DthIter_eq_iterate_Lop]
          rfl
        rw [h2]
        exact haIt m hm1 hm4 θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hsq : (Work.FTS.EllipticEst.LopIter m a θ) ^ 2
          ≤ (Ca * Real.sin (2 * θ)) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hbound 2
      rw [hlin θ]
      calc (Ca⁻¹ * Work.FTS.EllipticEst.LopIter m a θ) ^ 2
          = Ca⁻¹ ^ 2 * (Work.FTS.EllipticEst.LopIter m a θ) ^ 2 := by ring
        _ ≤ Ca⁻¹ ^ 2 * (Ca * Real.sin (2 * θ)) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ = (Real.sin (2 * θ)) ^ 2 := by
            field_simp
    -- the pointwise bound for the rescaled profile, on the open then on the closed quadrant
    have hopen : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α 4 (fun z θ => a' θ * f z θ) z θ
          ≤ C₁ * Work.Spaces.HkIntegrand α 4 f z θ :=
      hC₁ a' ha'1 ha'CD ha'It α f hα0 hα1 hf
    have hclosed := Work.FTS.Nonlinear.N4Fields.closed_of_interior (k := 4) (a := a') (C := C₁)
      (fun α' f' hα' hα'1 hf' => hC₁ a' ha'1 ha'CD ha'It α' f' hα' hα'1 hf') α f hα0 hα1 hf
    -- transport back to `a·f = Ca · (a'·f)`
    have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) z θ
          ≤ (Ca ^ 2 * C₁) * Work.Spaces.HkIntegrand α 4 f z θ := by
      intro z hz θ hθ
      have hrew : (fun z θ => a θ * f z θ) = fun z θ => Ca * (a' θ * f z θ) := by
        funext z' θ'
        have hCamul : Ca * (a θ' / Ca) = a θ' := by field_simp
        rw [ha'def]
        calc a θ' * f z' θ' = (Ca * (a θ' / Ca)) * f z' θ' := by rw [hCamul]
          _ = Ca * (a θ' / Ca * f z' θ') := by ring
      rw [hrew, Work.FTS.LocData.HkIntegrand_const_mul]
      calc Ca ^ 2 * Work.Spaces.HkIntegrand α 4 (fun z θ => a' θ * f z θ) z θ
          ≤ Ca ^ 2 * (C₁ * Work.Spaces.HkIntegrand α 4 f z θ) :=
            mul_le_mul_of_nonneg_left (hclosed z hz θ hθ) (sq_nonneg Ca)
        _ = (Ca ^ 2 * C₁) * Work.Spaces.HkIntegrand α 4 f z θ := by ring
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α 4 (fun z θ => a θ * f z θ) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.Nonlinear.N4Fields.smoothOpen_angMul_On hCD hf).continuousOn_HkIntegrand α 4
    have hmem' : Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) := by
      refine Work.FTS.LocData.HkMem_of_majorant α 4 hcont ?_ ?_ hpt
      · intro z hz
        exact (hmem.1 z hz).const_mul (Ca ^ 2 * C₁)
      · have h2 := hmem.2.const_mul (Ca ^ 2 * C₁)
        have heq : (fun z => ∫ θ in Work.Spaces.Iθ,
              (Ca ^ 2 * C₁) * Work.Spaces.HkIntegrand α 4 f z θ)
            = fun z => (Ca ^ 2 * C₁) * ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 4 f z θ := by
          funext z
          rw [MeasureTheory.integral_const_mul]
        rw [heq]
        exact h2
    have hsq : Work.Spaces.HkSq α 4 (fun z θ => a θ * f z θ)
        ≤ (Ca ^ 2 * C₁) * Work.Spaces.HkSq α 4 f :=
      Work.FTS.Nonlinear.N4Fields.HkSq_le_of_integrand_le α 4 (Ca ^ 2 * C₁) hmem hpt
    refine ⟨hmem', ?_⟩
    have hsqrt : Work.Spaces.HkNorm α 4 (fun z θ => a θ * f z θ)
        ≤ (Ca * Real.sqrt C₁) * Work.FTS.Nonlin.Xn α f := by
      have h1 : Real.sqrt (Ca ^ 2 * C₁) = Ca * Real.sqrt C₁ := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Ca ^ 2), Real.sqrt_sq_eq_abs,
          abs_of_nonneg hCa]
      have h2 : Work.FTS.Nonlin.Xn α f = Real.sqrt (Work.Spaces.HkSq α 4 f) := rfl
      rw [Work.Spaces.HkNorm, h2]
      calc Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => a θ * f z θ))
          ≤ Real.sqrt ((Ca ^ 2 * C₁) * Work.Spaces.HkSq α 4 f) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt (Ca ^ 2 * C₁) * Real.sqrt (Work.Spaces.HkSq α 4 f) :=
            Real.sqrt_mul (by positivity) (Work.Spaces.HkSq α 4 f)
        _ = (Ca * Real.sqrt C₁) * Real.sqrt (Work.Spaces.HkSq α 4 f) := by rw [h1]
    have hXnnn : 0 ≤ Work.FTS.Nonlin.Xn α f := by
      rw [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
      exact Real.sqrt_nonneg _
    calc Work.FTS.Nonlin.Xn α (fun z θ => a θ * f z θ)
        ≤ (Ca * Real.sqrt C₁) * Work.FTS.Nonlin.Xn α f := hsqrt
      _ ≤ (1 + Real.sqrt C₁) * Ca * Work.FTS.Nonlin.Xn α f := by
          refine mul_le_mul_of_nonneg_right ?_ hXnnn
          nlinarith [hCa, Real.sqrt_nonneg C₁]

end Work.FTS.OpenPkg
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.l12diff_field =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.OpenPkg


/-- **`z ↦ L₁₂(g)(z)` is differentiable at every `z > 0`** for an interior-smooth honest datum
`g ∈ ℋ⁴`.

`Work.Construction.L12 g` is the paper's `L₁₂` (`Work.Elliptic.L12`), so the statement is a
special case of `Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk`, which shows that
`L₁₂(F)` is `C^{k-1}` on `(0,∞)` with derivative `-3 F_*(z)/z` for every
`SmoothOpen F` with `HkMem α k F`, `k ≥ 2`; the hypothesis `HQo α 4 g` unfolds by definition to
exactly `SmoothOpen g ∧ HkMem α 4 g`. -/
theorem l12diff_field :
    ∀ (α : ℝ) (g : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 → Work.FTS.VocabO.HQo α 4 g →
      ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z := by
  intro α g _hα _hα1 hg z hz
  obtain ⟨hopen, hmem⟩ := hg
  have h := (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α 4 g hopen hmem
    (by norm_num)).2 z hz
  exact h.differentiableAt

end Work.FTS.OpenPkg
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Est.WlInf_psiSol =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Psi0Est

set_option autoImplicit false

/-! ## The value of `∂_θθψ` at the two endpoints -/

theorem iteratedDeriv_two_psiSol_zero (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    iteratedDeriv 2 (psiSol α) 0 = 0 := by
  obtain ⟨hq0, hqπ⟩ := qfun_tendsto_endpoints_alt α hα hα1
  have heq := (deriv_psiSol_eventuallyEq_M1 α hα hα1 hq0 hqπ).1
  have hder := (hasDerivAt_M1_endpoints α hα hα1 hq0 hqπ).1
  have h := HasDerivAt.congr_of_eventuallyEq hder heq
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_zero]
  exact h.deriv

theorem iteratedDeriv_two_psiSol_pi_div_two (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    iteratedDeriv 2 (psiSol α) (Real.pi / 2) = 0 := by
  obtain ⟨hq0, hqπ⟩ := qfun_tendsto_endpoints_alt α hα hα1
  have heq := (deriv_psiSol_eventuallyEq_M1 α hα hα1 hq0 hqπ).2
  have hder := (hasDerivAt_M1_endpoints α hα hα1 hq0 hqπ).2
  have h := HasDerivAt.congr_of_eventuallyEq hder heq
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_zero]
  exact h.deriv

/-! ## The target -/

theorem WlInf_psiSol (C : ℝ) (hC : 0 < C) :
    ∀ α : ℝ, 0 < α → α ≤ 1 / 4 →
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |iteratedDeriv 2 (psiSol α) θ| ≤ C) →
    (∀ j : ℕ, 1 ≤ j → j ≤ 5 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.dthU^[j] (fun θ' : ℝ => iteratedDeriv 2 (psiSol α) θ') θ|
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) ≤ C) →
    Work.Spaces.WlInfMem α 5 (fun _ θ => iteratedDeriv 2 (psiSol α) θ) ∧
    Work.Spaces.WlInf α 5 (fun _ θ => iteratedDeriv 2 (psiSol α) θ) ≤ 6 * C := by
  intro α hα hα14 h1 h2
  refine WlInf_theta_only_six α C hα hC (fun θ => iteratedDeriv 2 (psiSol α) θ) ?_ ?_
  · intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with h | h
    · rw [← h, iteratedDeriv_two_psiSol_zero α hα hα14, abs_zero]
      exact le_of_lt hC
    rcases eq_or_lt_of_le hθ.2 with h2' | h2'
    · rw [h2', iteratedDeriv_two_psiSol_pi_div_two α hα hα14, abs_zero]
      exact le_of_lt hC
    · exact h1 θ ⟨h, h2'⟩
  · intro j hj1 hj5 θ hθ
    rcases eq_or_lt_of_le hθ.1 with h | h
    · rw [← h, dthU_iter_apply_zero (fun θ' => iteratedDeriv 2 (psiSol α) θ') hj1]
      simp only [abs_zero, zero_mul, zero_div]
      exact le_of_lt hC
    rcases eq_or_lt_of_le hθ.2 with h2' | h2'
    · rw [h2', dthU_iter_apply_pi_half (fun θ' => iteratedDeriv 2 (psiSol α) θ') hj1]
      simp only [abs_zero, zero_mul, zero_div]
      exact le_of_lt hC
    · exact h2 j hj1 hj5 θ ⟨h, h2'⟩


end Work.FTS.PhiStar.Psi0Est
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Psi0Est.exists_AClass =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Psi0Est

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Differentiation bookkeeping for `dthU` -/

theorem dthU_add_apply' (f g : ℝ → ℝ) (θ : ℝ) (hf : DifferentiableAt ℝ f θ)
    (hg : DifferentiableAt ℝ g θ) :
    Work.Spaces.dthU (f + g) θ = Work.Spaces.dthU f θ + Work.Spaces.dthU g θ := by
  simp only [Work.Spaces.dthU_apply]
  rw [deriv_add hf hg]
  ring

theorem dthU_sum_apply {ι : Type*} (s : Finset ι) (φ : ι → ℝ → ℝ) (θ : ℝ)
    (h : ∀ i ∈ s, DifferentiableAt ℝ (φ i) θ) :
    Work.Spaces.dthU (∑ i ∈ s, φ i) θ = ∑ i ∈ s, Work.Spaces.dthU (φ i) θ := by
  simp only [Work.Spaces.dthU_apply]
  rw [deriv_sum h, Finset.mul_sum]

theorem dthU_four_cos_sq (θ : ℝ) :
    Work.Spaces.dthU (fun θ' : ℝ => 4 * Real.cos θ' ^ 2) θ
      = -16 * Real.sin θ ^ 2 * Real.cos θ ^ 2 := by
  have h : HasDerivAt (fun θ' : ℝ => 4 * Real.cos θ' ^ 2)
      (4 * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) θ :=
    ((Real.hasDerivAt_cos θ).pow 2).const_mul 4
  rw [Work.Spaces.dthU_apply, h.deriv, Real.sin_two_mul]
  norm_num
  ring

theorem dthU_iter_succ_apply (m : ℕ) (f : ℝ → ℝ) :
    Work.Spaces.dthU^[m + 1] f = Work.Spaces.dthU (Work.Spaces.dthU^[m] f) :=
  Function.iterate_succ_apply' _ _ _

theorem dthU_iter_succ_apply' (m : ℕ) (f : ℝ → ℝ) :
    Work.Spaces.dthU (Work.Spaces.dthU^[m] f) = Work.Spaces.dthU^[m + 1] f :=
  (dthU_iter_succ_apply m f).symm

/-- `dthU`-iterates of a function that is `C^∞` on the open angular interval. -/
theorem contDiffOn_dthU_iter_aux {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (∞ : ℕ∞ω) f (Set.Ioo 0 (Real.pi / 2))) (m : ℕ) :
    ContDiffOn ℝ (∞ : ℕ∞ω) (Work.Spaces.dthU^[m] f) (Set.Ioo 0 (Real.pi / 2)) := by
  induction m with
  | zero => simpa using hf
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      have hone : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by simp
      have hd : ContDiffOn ℝ (∞ : ℕ∞ω) (deriv (Work.Spaces.dthU^[m] f))
          (Set.Ioo 0 (Real.pi / 2)) :=
        ih.deriv_of_isOpen isOpen_Ioo (m := (∞ : ℕ∞ω)) hone
      have hsin : ContDiffOn ℝ (∞ : ℕ∞ω) (fun θ : ℝ => Real.sin (2 * θ))
          (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
      have hfun : Work.Spaces.dthU (Work.Spaces.dthU^[m] f)
          = (fun θ : ℝ => Real.sin (2 * θ)) * deriv (Work.Spaces.dthU^[m] f) := by
        funext θ
        rw [Work.Spaces.dthU_apply]
        rfl
      rw [hfun]
      exact hsin.mul hd

/-- Interior differentiability of the `dthU`-iterates. -/
theorem dthUIter_diffAt_aux {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (∞ : ℕ∞ω) f (Set.Ioo 0 (Real.pi / 2))) (m : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    DifferentiableAt ℝ (Work.Spaces.dthU^[m] f) θ :=
  ((contDiffOn_dthU_iter_aux hf m).contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt
    (by simp)

/-! ## Two elementary index rewritings -/

/-- The `range (j+1)`-shift: the index `r` can be replaced by `r - 1` (with the `r = 0` term
killed), at the cost of the single boundary term `f j`. -/
theorem sum_range_shift (f : ℕ → ℝ) (j : ℕ) :
    (∑ r ∈ Finset.range (j + 1), f r)
      = (∑ r ∈ Finset.range (j + 1), (if r = 0 then 0 else f (r - 1))) + f j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have h1 : (∑ r ∈ Finset.range (j + 1 + 1), f r)
          = (∑ r ∈ Finset.range (j + 1), f r) + f (j + 1) :=
        Finset.sum_range_succ f (j + 1)
      have h2 : (∑ r ∈ Finset.range (j + 1 + 1), (if r = 0 then 0 else f (r - 1)))
          = (∑ r ∈ Finset.range (j + 1), (if r = 0 then 0 else f (r - 1)))
            + (if j + 1 = 0 then 0 else f (j + 1 - 1)) :=
        Finset.sum_range_succ (fun r => if r = 0 then 0 else f (r - 1)) (j + 1)
      rw [h1, ih, h2, if_neg (by omega : ¬ (j + 1 = 0)),
        show (j + 1) - 1 = j from by omega]

/-- Inside the shifted sum the index `(r-1)+1` of `D_θ^·ψ` simplifies to `r`, and the `if` can be
pulled out of the product. -/
theorem cVec_shift_term' (α : ℝ) (j : ℕ) (θ : ℝ) (r : ℕ) :
    (if r = 0 then (0 : ℝ)
        else cVec j (r - 1) θ * (Work.Spaces.dthU^[r - 1 + 1] (psiSol α)) θ)
      = (if r = 0 then 0 else cVec j (r - 1) θ) * (Work.Spaces.dthU^[r] (psiSol α)) θ := by
  by_cases h : r = 0
  · simp [h]
  · rw [if_neg h, if_neg h, show r - 1 + 1 = r from by omega]

/-! ## The identity `D_θ^{j+1}ψ = 4cos²θ·D_θ^j P + ∑_r c_{j,r}·D_θ^rψ` -/

/-- The right-hand side of the `j`-th identity. -/
noncomputable def rhsFun (α : ℝ) (j : ℕ) : ℝ → ℝ :=
  (fun θ : ℝ => 4 * Real.cos θ ^ 2) * (Work.Spaces.dthU^[j] (Pfun α))
    + ∑ r ∈ Finset.range (j + 1), cVec j r * Work.Spaces.dthU^[r] (psiSol α)

theorem A_ident (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) (j : ℕ) :
    Set.EqOn (Work.Spaces.dthU^[j + 1] (psiSol α)) (rhsFun α j)
      (Set.Ioo 0 (Real.pi / 2)) := by
  induction j with
  | zero =>
      intro θ hθ
      have h := dthU_psiSol α hα hα1 hθ
      rw [Function.iterate_one]
      simp only [rhsFun, Pi.mul_apply, Pi.add_apply, Finset.sum_apply,
        show (0 : ℕ) + 1 = 1 from rfl, Finset.sum_range_one, cVec_zero_zero,
        Function.iterate_zero]
      simp only [id_eq]
      linarith [h]
  | succ j ih =>
      intro θ hθ
      have hs : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
      have hPS : ContDiffOn ℝ (∞ : ℕ∞ω) (psiSol α) (Set.Ioo 0 (Real.pi / 2)) :=
        contDiffOn_psiSol α hα hα1
      have hPF : ContDiffOn ℝ (∞ : ℕ∞ω) (Pfun α) (Set.Ioo 0 (Real.pi / 2)) :=
        contDiffOn_Pfun α (le_of_lt hα)
      have hdψ : ∀ r : ℕ, DifferentiableAt ℝ (Work.Spaces.dthU^[r] (psiSol α)) θ :=
        fun r => dthUIter_diffAt_aux hPS r hθ
      have hdP : ∀ r : ℕ, DifferentiableAt ℝ (Work.Spaces.dthU^[r] (Pfun α)) θ :=
        fun r => dthUIter_diffAt_aux hPF r hθ
      have hdc : ∀ r : ℕ, DifferentiableAt ℝ (cVec j r) θ :=
        fun r => IsCoef_differentiableAt (cVec_isCoef j r) θ
      have hd4 : DifferentiableAt ℝ (fun θ : ℝ => 4 * Real.cos θ ^ 2) θ := by fun_prop
      have hih : (Work.Spaces.dthU^[j + 1] (psiSol α)) θ
          = 4 * Real.cos θ ^ 2 * (Work.Spaces.dthU^[j] (Pfun α)) θ
            + ∑ r ∈ Finset.range (j + 1),
                cVec j r θ * (Work.Spaces.dthU^[r] (psiSol α)) θ := by
        have h := ih hθ
        simpa only [rhsFun, Pi.add_apply, Pi.mul_apply, Finset.sum_apply] using h
      have hev : Filter.EventuallyEq (𝓝 θ) (Work.Spaces.dthU^[j + 1] (psiSol α))
          (rhsFun α j) := ih.eventuallyEq_of_mem hs
      rw [Function.iterate_succ_apply']
      have hstep1 : Work.Spaces.dthU (Work.Spaces.dthU^[j + 1] (psiSol α)) θ
          = Work.Spaces.dthU (rhsFun α j) θ := by
        rw [Work.Spaces.dthU_apply, Work.Spaces.dthU_apply, hev.deriv_eq]
      rw [hstep1, rhsFun]
      have hd1 : DifferentiableAt ℝ ((fun θ : ℝ => 4 * Real.cos θ ^ 2)
          * (Work.Spaces.dthU^[j] (Pfun α))) θ := hd4.mul (hdP j)
      have hd2 : ∀ r ∈ Finset.range (j + 1),
          DifferentiableAt ℝ (cVec j r * (Work.Spaces.dthU^[r] (psiSol α))) θ :=
        fun r _ => (hdc r).mul (hdψ r)
      have hd3 : DifferentiableAt ℝ (∑ r ∈ Finset.range (j + 1),
          cVec j r * (Work.Spaces.dthU^[r] (psiSol α))) θ := DifferentiableAt.sum hd2
      rw [dthU_add_apply' _ _ θ hd1 hd3, dthU_sum_apply _ _ θ hd2,
        Work.Spaces.dthU_mul_apply _ _ θ hd4 (hdP j), dthU_four_cos_sq,
        dthU_iter_succ_apply' j (Pfun α)]
      have hterm : ∀ r ∈ Finset.range (j + 1),
          Work.Spaces.dthU (cVec j r * (Work.Spaces.dthU^[r] (psiSol α))) θ
            = Work.Spaces.dthU (cVec j r) θ * (Work.Spaces.dthU^[r] (psiSol α)) θ
              + cVec j r θ * (Work.Spaces.dthU^[r + 1] (psiSol α)) θ := by
        intro r _
        rw [Work.Spaces.dthU_mul_apply _ _ θ (hdc r) (hdψ r),
          dthU_iter_succ_apply' r (psiSol α)]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      have hZj : 4 * Real.cos θ ^ 2 * (Work.Spaces.dthU^[j] (Pfun α)) θ
          = (Work.Spaces.dthU^[j + 1] (psiSol α)) θ
            - ∑ r ∈ Finset.range (j + 1),
                cVec j r θ * (Work.Spaces.dthU^[r] (psiSol α)) θ := by
        linarith [hih]
      rw [show (rhsFun α (j + 1)) θ
          = 4 * Real.cos θ ^ 2 * (Work.Spaces.dthU^[j + 1] (Pfun α)) θ
            + ((∑ r ∈ Finset.range (j + 1),
                  cVec (j + 1) r θ * (Work.Spaces.dthU^[r] (psiSol α)) θ)
                + cVec (j + 1) (j + 1) θ * (Work.Spaces.dthU^[j + 1] (psiSol α)) θ) from by
        simp only [rhsFun, Pi.mul_apply, Pi.add_apply, Finset.sum_apply,
          Finset.sum_range_succ]]
      rw [cVec_succ_self j]
      -- lower the `Z_j`-term with the induction hypothesis
      have hZj0 : 4 * Real.cos θ ^ 2 * (Work.Spaces.dthU^[j] (Pfun α)) θ
          = (Work.Spaces.dthU^[j + 1] (psiSol α)) θ
            - ∑ r ∈ Finset.range (j + 1),
                cVec j r θ * (Work.Spaces.dthU^[r] (psiSol α)) θ := by
        linarith [hih]
      have hZj : -16 * Real.sin θ ^ 2 * Real.cos θ ^ 2 * (Work.Spaces.dthU^[j] (Pfun α)) θ
          = -4 * Real.sin θ ^ 2
              * ((Work.Spaces.dthU^[j + 1] (psiSol α)) θ
                - ∑ r ∈ Finset.range (j + 1),
                    cVec j r θ * (Work.Spaces.dthU^[r] (psiSol α)) θ) := by
        linear_combination (-4 * Real.sin θ ^ 2) * hZj0
      -- the shift of the `A_{r+1}`-sum
      have hshift : (∑ r ∈ Finset.range (j + 1),
            cVec j r θ * (Work.Spaces.dthU^[r + 1] (psiSol α)) θ)
          = (∑ r ∈ Finset.range (j + 1),
              (if r = 0 then 0 else cVec j (r - 1) θ)
                * (Work.Spaces.dthU^[r] (psiSol α)) θ)
            + cVec j j θ * (Work.Spaces.dthU^[j + 1] (psiSol α)) θ := by
        rw [sum_range_shift (fun r => cVec j r θ
          * (Work.Spaces.dthU^[r + 1] (psiSol α)) θ) j]
        rw [Finset.sum_congr rfl (fun r _ => cVec_shift_term' α j θ r)]
      -- the recursion, summed over `range (j+1)`
      have hrec : (∑ r ∈ Finset.range (j + 1),
            cVec (j + 1) r θ * (Work.Spaces.dthU^[r] (psiSol α)) θ)
          = (∑ r ∈ Finset.range (j + 1),
              Work.Spaces.dthU (cVec j r) θ * (Work.Spaces.dthU^[r] (psiSol α)) θ)
            + (∑ r ∈ Finset.range (j + 1), 4 * Real.sin θ ^ 2 * cVec j r θ
                * (Work.Spaces.dthU^[r] (psiSol α)) θ)
            + (∑ r ∈ Finset.range (j + 1),
              (if r = 0 then 0 else cVec j (r - 1) θ)
                * (Work.Spaces.dthU^[r] (psiSol α)) θ) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        have hr' : r ≠ j + 1 := by
          have := Finset.mem_range.mp hr
          omega
        rcases eq_or_ne r 0 with h0 | h0
        · subst h0
          rw [cVec_succ_zero]
          simp only []
          rw [if_pos trivial]
          ring
        · rw [cVec_succ_of_ne j r hr' h0]
          simp only []
          rw [if_neg h0]
          ring
      -- pulling the constant out of the middle sum
      have hW : (∑ r ∈ Finset.range (j + 1), 4 * Real.sin θ ^ 2 * cVec j r θ
            * (Work.Spaces.dthU^[r] (psiSol α)) θ)
          = 4 * Real.sin θ ^ 2
            * (∑ r ∈ Finset.range (j + 1),
                cVec j r θ * (Work.Spaces.dthU^[r] (psiSol α)) θ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
      rw [hZj, hrec, hshift, hW]
      ring

/-! ## The uniform bound for `ψ` -/

theorem psiSol_bound_aux : ∃ ν0 : ℝ, 0 ≤ ν0 ∧ ∀ α : ℝ, 0 < α → α ≤ 1 / 4 →
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |psiSol α θ| ≤ ν0 * Real.sin (2 * θ) := by
  refine ⟨500 * π, by positivity, fun α hα hα1 θ hθ => ?_⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hK : |Kc α| ≤ 250 * π := abs_Kc_le α hα hα1
  have hw : |wZer α θ| ≤ 500 * (π / 2) := abs_wZer_le α hα hα1 ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsum : |Kc α + wZer α θ| ≤ 500 * π := by
    calc |Kc α + wZer α θ| ≤ |Kc α| + |wZer α θ| := abs_add_le _ _
      _ ≤ 250 * π + 500 * (π / 2) := add_le_add hK hw
      _ = 500 * π := by ring
  rw [show psiSol α θ = Real.sin (2 * θ) * (Kc α + wZer α θ) from rfl, abs_mul,
    abs_of_pos hsin]
  calc Real.sin (2 * θ) * |Kc α + wZer α θ| ≤ Real.sin (2 * θ) * (500 * π) :=
        mul_le_mul_of_nonneg_left hsum (le_of_lt hsin)
    _ = (500 * π) * Real.sin (2 * θ) := by ring

noncomputable def nu0c : ℝ := Classical.choose psiSol_bound_aux

theorem nu0c_nonneg : 0 ≤ nu0c := (Classical.choose_spec psiSol_bound_aux).1

theorem psiSol_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |psiSol α θ| ≤ nu0c * Real.sin (2 * θ) :=
  (Classical.choose_spec psiSol_bound_aux).2 α hα hα1 θ hθ

noncomputable def CPc : ℝ := Classical.choose fourCosSqBounds.1

theorem CPc_spec :
    0 ≤ CPc ∧ ∀ α : ℝ, 0 < α → α ≤ 1 / 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      4 * Real.cos θ ^ 2 * |Pfun α θ| ≤ CPc * Real.sin (2 * θ) :=
  Classical.choose_spec fourCosSqBounds.1

noncomputable def cBc : ℕ → ℕ → ℝ := Classical.choose cVecBound

theorem cBc_nonneg (j r : ℕ) : 0 ≤ cBc j r := (Classical.choose_spec cVecBound).1 j r

theorem cBc_spec (j r : ℕ) (θ : ℝ) : |cVec j r θ| ≤ cBc j r :=
  (Classical.choose_spec cVecBound).2 j r θ

/-! ## The constants of the final bound -/

/-- The level-`k` constant multiplying `sin 2θ` in the bound for `4cos²θ·D_θ^k P`. -/
noncomputable def Cf (κ ℓ : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then CPc else κ k / 4 + 4 * ℓ k

/-- The geometric factor of the final bound. -/
noncomputable def KK (κ ℓ : ℕ → ℝ) : ℝ :=
  1 + ∑ k ∈ Finset.range 6, ∑ r ∈ Finset.range (k + 1), cBc k r

/-- The base of the final bound `ν j = MM · KK^j`. -/
noncomputable def MM (κ ℓ : ℕ → ℝ) : ℝ :=
  1 + nu0c + ∑ k ∈ Finset.range 6, Cf κ ℓ k

/-- The candidate `ν`-sequence: `ν j = MM · KK^j`. -/
noncomputable def nuFun (κ ℓ : ℕ → ℝ) : ℕ → ℝ := fun j => MM κ ℓ * (KK κ ℓ) ^ j

theorem Cf_nonneg (κ ℓ : ℕ → ℝ) (hκ0 : ∀ j, 0 ≤ κ j) (hℓ0 : ∀ j, 0 ≤ ℓ j) (k : ℕ) :
    0 ≤ Cf κ ℓ k := by
  rcases eq_or_ne k 0 with h | h
  · subst h
    simp only [Cf, if_pos rfl]
    exact CPc_spec.1
  · simp only [Cf, if_neg h]
    have h1 := hκ0 k
    have h2 := hℓ0 k
    linarith

theorem KK_ge_one (κ ℓ : ℕ → ℝ) : 1 ≤ KK κ ℓ := by
  have : 0 ≤ ∑ k ∈ Finset.range 6, ∑ r ∈ Finset.range (k + 1), cBc k r :=
    Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun r _ => cBc_nonneg k r))
  simp only [KK]
  linarith

theorem MM_ge_one (κ ℓ : ℕ → ℝ) (hκ0 : ∀ j, 0 ≤ κ j) (hℓ0 : ∀ j, 0 ≤ ℓ j) :
    1 ≤ MM κ ℓ := by
  have h1 : 0 ≤ nu0c := nu0c_nonneg
  have h2 : 0 ≤ ∑ k ∈ Finset.range 6, Cf κ ℓ k :=
    Finset.sum_nonneg (fun k _ => Cf_nonneg κ ℓ hκ0 hℓ0 k)
  simp only [MM]
  linarith

theorem MM_nonneg (κ ℓ : ℕ → ℝ) (hκ0 : ∀ j, 0 ≤ κ j) (hℓ0 : ∀ j, 0 ≤ ℓ j) :
    0 ≤ MM κ ℓ := le_trans (by norm_num) (MM_ge_one κ ℓ hκ0 hℓ0)

/-- `Cf k ≤ MM` for `k ≤ 5`. -/
theorem Cf_le_MM (κ ℓ : ℕ → ℝ) (hκ0 : ∀ j, 0 ≤ κ j) (hℓ0 : ∀ j, 0 ≤ ℓ j)
    {k : ℕ} (hk : k ≤ 5) : Cf κ ℓ k ≤ MM κ ℓ := by
  have hmem : k ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
  have h1 : Cf κ ℓ k ≤ ∑ i ∈ Finset.range 6, Cf κ ℓ i :=
    Finset.single_le_sum (fun i _ => Cf_nonneg κ ℓ hκ0 hℓ0 i) hmem
  have h2 : 0 ≤ nu0c := nu0c_nonneg
  simp only [MM]
  linarith

/-- `∑_{r ≤ j} cBc j r ≤ KK - 1` for `j ≤ 5`. -/
theorem sum_cBc_le (κ ℓ : ℕ → ℝ) {j : ℕ} (hj : j ≤ 5) :
    (∑ r ∈ Finset.range (j + 1), cBc j r) ≤ KK κ ℓ - 1 := by
  have hmem : j ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
  have hnonneg : ∀ k ∈ Finset.range 6, 0 ≤ ∑ r ∈ Finset.range (k + 1), cBc k r :=
    fun k _ => Finset.sum_nonneg (fun r _ => cBc_nonneg k r)
  have h1 : (∑ r ∈ Finset.range (j + 1), cBc j r)
      ≤ ∑ k ∈ Finset.range 6, ∑ r ∈ Finset.range (k + 1), cBc k r :=
    Finset.single_le_sum hnonneg hmem
  simp only [KK]
  linarith

/-- The `Z`-bound: `|4cos²θ·D_θ^k P| ≤ Cf k · sin 2θ` for `k ≤ 5`. -/
theorem Z_bound (κ ℓ : ℕ → ℝ) (hZ : ZClass κ ℓ) {k : ℕ} (hk : k ≤ 5) (α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |4 * Real.cos θ ^ 2 * Work.Spaces.dthU^[k] (Pfun α) θ| ≤ Cf κ ℓ k * Real.sin (2 * θ) := by
  obtain ⟨hκ0, hℓ0, hZb⟩ := hZ
  rcases eq_or_ne k 0 with h0 | h0
  · subst h0
    have hCf0 : Cf κ ℓ 0 = CPc := by simp only [Cf, ↓reduceIte]
    have habs : |4 * Real.cos θ ^ 2 * (Work.Spaces.dthU^[0] (Pfun α)) θ|
        = 4 * Real.cos θ ^ 2 * |Pfun α θ| := by
      simp only [Function.iterate_zero, id_eq]
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
        abs_of_nonneg (sq_nonneg (Real.cos θ))]
    rw [habs, hCf0]
    exact CPc_spec.2 α hα hα1 θ hθ
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr h0
    have hCfn : Cf κ ℓ k = κ k / 4 + 4 * ℓ k := by simp only [Cf, h0, ↓reduceIte]
    have habs : |4 * Real.cos θ ^ 2 * (Work.Spaces.dthU^[k] (Pfun α)) θ|
        = 4 * Real.cos θ ^ 2 * |Work.Spaces.dthU^[k] (Pfun α) θ| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
        abs_of_nonneg (sq_nonneg (Real.cos θ))]
    rw [habs, hCfn]
    exact fourCosSqBounds.2 k hk1 hk κ ℓ ⟨hκ0, hℓ0, hZb⟩ α hα hα1 θ hθ

theorem exists_AClass (hZ : ∃ κ ell : ℕ → ℝ, ZClass κ ell) : ∃ ν : ℕ → ℝ, AClass ν := by
  obtain ⟨κ, ℓ, hκ0, hℓ0, hZb⟩ := hZ
  have hZ : ZClass κ ℓ := ⟨hκ0, hℓ0, hZb⟩
  refine ⟨nuFun κ ℓ, ?_, ?_⟩
  · intro j
    exact mul_nonneg (MM_nonneg κ ℓ hκ0 hℓ0) (pow_nonneg (le_trans (by norm_num) (KK_ge_one κ ℓ)) j)
  · intro α hα hα1 j hj6 θ hθ
    have hsin : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    have hMnn : 0 ≤ MM κ ℓ := MM_nonneg κ ℓ hκ0 hℓ0
    have hK1 : 1 ≤ KK κ ℓ := KK_ge_one κ ℓ
    have hKnn : 0 ≤ KK κ ℓ := le_trans (by norm_num) hK1
    -- strong induction on the level
    have hA : ∀ N ≤ 6, ∀ j ≤ N,
        |Work.Spaces.dthU^[j] (psiSol α) θ| ≤ nuFun κ ℓ j * Real.sin (2 * θ) := by
      intro N hN
      induction N with
      | zero =>
          intro j hj
          have hj0 : j = 0 := by omega
          subst hj0
          have h1 := psiSol_le α hα hα1 hθ
          have h2 : nu0c ≤ MM κ ℓ := by
            have h3 : 0 ≤ ∑ k ∈ Finset.range 6, Cf κ ℓ k :=
              Finset.sum_nonneg (fun k _ => Cf_nonneg κ ℓ hκ0 hℓ0 k)
            simp only [MM]
            linarith
          simpa only [Function.iterate_zero, id_eq, nuFun, pow_zero, mul_one] using
            le_trans h1 (mul_le_mul_of_nonneg_right h2 (le_of_lt hsin))
      | succ N ih =>
          intro j hj
          rcases Nat.lt_or_eq_of_le hj with hlt | heq
          · exact ih (by omega) j (by omega)
          · subst heq
            have hN5 : N ≤ 5 := by omega
            have hid := A_ident α hα hα1 N hθ
            rw [hid]
            simp only [rhsFun, Pi.add_apply, Pi.mul_apply, Finset.sum_apply]
            have hZbN : |4 * Real.cos θ ^ 2 * (Work.Spaces.dthU^[N] (Pfun α)) θ|
                ≤ Cf κ ℓ N * Real.sin (2 * θ) := Z_bound κ ℓ hZ hN5 α hα hα1 hθ
            have hsum : |∑ r ∈ Finset.range (N + 1),
                  cVec N r θ * (Work.Spaces.dthU^[r] (psiSol α)) θ|
                ≤ (∑ r ∈ Finset.range (N + 1), cBc N r * (MM κ ℓ * (KK κ ℓ) ^ N))
                  * Real.sin (2 * θ) := by
              refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
              rw [Finset.sum_mul]
              apply Finset.sum_le_sum
              intro r hr
              have hrN : r ≤ N := by simpa using Finset.mem_range.mp hr
              have h1 : |cVec N r θ| ≤ cBc N r := cBc_spec N r θ
              have h2 : |Work.Spaces.dthU^[r] (psiSol α) θ| ≤ nuFun κ ℓ r * Real.sin (2 * θ) :=
                ih (by omega) r hrN
              have h3 : nuFun κ ℓ r * Real.sin (2 * θ)
                  ≤ (MM κ ℓ * (KK κ ℓ) ^ N) * Real.sin (2 * θ) := by
                apply mul_le_mul_of_nonneg_right _ (le_of_lt hsin)
                have := pow_le_pow_right₀ hK1 hrN
                simpa only [nuFun] using mul_le_mul_of_nonneg_left this hMnn
              calc |cVec N r θ * (Work.Spaces.dthU^[r] (psiSol α)) θ|
                  = |cVec N r θ| * |Work.Spaces.dthU^[r] (psiSol α) θ| := abs_mul _ _
                _ ≤ cBc N r * (nuFun κ ℓ r * Real.sin (2 * θ)) :=
                    mul_le_mul h1 h2 (abs_nonneg _) (cBc_nonneg N r)
                _ ≤ cBc N r * ((MM κ ℓ * (KK κ ℓ) ^ N) * Real.sin (2 * θ)) :=
                    mul_le_mul_of_nonneg_left h3 (cBc_nonneg N r)
                _ = cBc N r * (MM κ ℓ * (KK κ ℓ) ^ N) * Real.sin (2 * θ) := by ring
            have hsum2 : (∑ r ∈ Finset.range (N + 1), cBc N r * (MM κ ℓ * (KK κ ℓ) ^ N))
                ≤ (KK κ ℓ - 1) * (MM κ ℓ * (KK κ ℓ) ^ N) := by
              rw [← Finset.sum_mul]
              exact mul_le_mul_of_nonneg_right (sum_cBc_le κ ℓ hN5)
                (mul_nonneg hMnn (pow_nonneg hKnn N))
            refine le_trans (abs_add_le _ _) ?_
            refine le_trans (add_le_add hZbN hsum) ?_
            refine le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hsum2 (le_of_lt hsin))) ?_
            rw [← add_mul, nuFun, pow_succ]
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hsin)
            have hCf : Cf κ ℓ N ≤ MM κ ℓ := Cf_le_MM κ ℓ hκ0 hℓ0 hN5
            have hM1 : MM κ ℓ ≤ MM κ ℓ * (KK κ ℓ) ^ N :=
              le_mul_of_one_le_right hMnn (one_le_pow₀ hK1)
            nlinarith [hCf, hM1, hMnn]
    exact hA j hj6 j le_rfl

end Work.FTS.PhiStar.Psi0Est
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.slotPairing_abs_le_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two-level Cauchy–Schwarz engine, in general order -/

/-- **The `L²`-Cauchy–Schwarz bound for a single slot with a general weight and general order.**

This is `Work.FTS.IPGen.cs_slotInt_abs_le` with `4` replaced by `n`: suppose `ρ ≥ 0` on `Iθ`
and that, for `θ ∈ (0,π/2)` (the endpoints being null), the weight times the square of each
slot is dominated by the `ℋ^n`-integrand of the corresponding datum.  Then

  `|∫_z ∫_θ ρ · X · Y| ≤ |f|_{ℋ^n} · |g|_{ℋ^n}`. -/
theorem cs_slotInt_abs_le_gen {α : ℝ} {n : ℕ} {ρ X Y f g : ℝ → ℝ → ℝ}
    (hmf : Work.Spaces.HkMem α n f) (hmg : Work.Spaces.HkMem α n g)
    (hρnn : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ)
    (hdf : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ρ z θ * (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α n f z θ)
    (hdg : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ρ z θ * (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α n g z θ) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ|
      ≤ Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  set F : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ with hF
  set G : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ with hG
  have hFnn : ∀ z, 0 ≤ F z := fun z =>
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α n f z θ
  have hGnn : ∀ z, 0 ≤ G z := fun z =>
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α n g z θ
  have hFint : IntegrableOn F Work.Spaces.Iz := by rw [hF]; exact hmf.2
  have hGint : IntegrableOn G Work.Spaces.Iz := by rw [hG]; exact hmg.2
  -- the `z`-majorant `√F · √G` is integrable, `F` and `G` being in `L¹`
  have hprod : IntegrableOn (fun z => Real.sqrt (F z) * Real.sqrt (G z)) Work.Spaces.Iz := by
    have hFm : AEStronglyMeasurable (fun z => Real.sqrt (F z)) (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hFint.aestronglyMeasurable
    have hGm : AEStronglyMeasurable (fun z => Real.sqrt (G z)) (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hGint.aestronglyMeasurable
    have hFsq : Integrable (fun z => Real.sqrt (F z) ^ 2) (volume.restrict Work.Spaces.Iz) :=
      hFint.congr (Eventually.of_forall (fun z => (Real.sq_sqrt (hFnn z)).symm))
    have hGsq : Integrable (fun z => Real.sqrt (G z) ^ 2) (volume.restrict Work.Spaces.Iz) :=
      hGint.congr (Eventually.of_forall (fun z => (Real.sq_sqrt (hGnn z)).symm))
    have hFlp : MemLp (fun z => Real.sqrt (F z)) 2 (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq hFm).mpr hFsq
    have hGlp : MemLp (fun z => Real.sqrt (G z)) 2 (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq hGm).mpr hGsq
    exact memLp_one_iff_integrable.mp (hFlp.mul hGlp)
  -- the angular estimate, for every `z ∈ Iz`
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ| ≤ Real.sqrt (F z) * Real.sqrt (G z) := by
    intro z hz
    have hprodθ : IntegrableOn (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)
        * Real.sqrt (Work.Spaces.HkIntegrand α n g z θ)) Work.Spaces.Iθ := by
      have hfm : AEStronglyMeasurable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n f z θ))
          (volume.restrict Work.Spaces.Iθ) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable (hmf.1 z hz).aestronglyMeasurable
      have hgm : AEStronglyMeasurable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n g z θ))
          (volume.restrict Work.Spaces.Iθ) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable (hmg.1 z hz).aestronglyMeasurable
      have hfsq : Integrable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n f z θ) ^ 2)
          (volume.restrict Work.Spaces.Iθ) :=
        (hmf.1 z hz).congr (Eventually.of_forall (fun θ =>
          (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α n f z θ)).symm))
      have hgsq : Integrable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n g z θ) ^ 2)
          (volume.restrict Work.Spaces.Iθ) :=
        (hmg.1 z hz).congr (Eventually.of_forall (fun θ =>
          (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α n g z θ)).symm))
      have hflp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)) 2
          (volume.restrict Work.Spaces.Iθ) :=
        (memLp_two_iff_integrable_sq hfm).mpr hfsq
      have hglp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n g z θ)) 2
          (volume.restrict Work.Spaces.Iθ) :=
        (memLp_two_iff_integrable_sq hgm).mpr hgsq
      exact memLp_one_iff_integrable.mp (hflp.mul hglp)
    have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        |ρ z θ * X z θ * Y z θ|
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α n g z θ) := by
      filter_upwards [Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ] with θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hρ0 : 0 ≤ ρ z θ := hρnn z hz θ hθI
      have hsX : Real.sqrt (ρ z θ * (X z θ) ^ 2)
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α n f z θ) :=
        Real.sqrt_le_sqrt (hdf z hz θ hθ)
      have hsY : Real.sqrt (ρ z θ * (Y z θ) ^ 2)
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α n g z θ) :=
        Real.sqrt_le_sqrt (hdg z hz θ hθ)
      have hs : Real.sqrt (ρ z θ) * Real.sqrt (ρ z θ) = ρ z θ := by
        rw [← sq, Real.sq_sqrt hρ0]
      calc |ρ z θ * X z θ * Y z θ|
          = ρ z θ * |X z θ| * |Y z θ| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
        _ = (Real.sqrt (ρ z θ) * Real.sqrt (ρ z θ)) * |X z θ| * |Y z θ| := by rw [hs]
        _ = Real.sqrt (ρ z θ * (X z θ) ^ 2) * Real.sqrt (ρ z θ * (Y z θ) ^ 2) := by
            rw [Real.sqrt_mul hρ0, Real.sqrt_mul hρ0, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
            ring
        _ ≤ Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α n g z θ) :=
            mul_le_mul hsX hsY (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc |∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |ρ z θ * X z θ * Y z θ| := abs_integral_le_integral_abs
      _ ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α n g z θ) :=
          integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _) hprodθ hpt
      _ ≤ Real.sqrt (F z) * Real.sqrt (G z) := by
          rw [hF, hG]
          exact Work.FTS.IPGen.cs_sqrt_le (hmf.1 z hz) (hmg.1 z hz)
            (fun θ => Work.Spaces.HkIntegrand_nonneg α n f z θ)
            (fun θ => Work.Spaces.HkIntegrand_nonneg α n g z θ)
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ|
      ≤ ∫ z in Work.Spaces.Iz,
          |∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ| := abs_integral_le_integral_abs
    _ ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (F z) * Real.sqrt (G z) :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) hprod
          (ae_restrict_of_forall_mem hIzm hslice)
    _ ≤ Real.sqrt (∫ z in Work.Spaces.Iz, F z) * Real.sqrt (∫ z in Work.Spaces.Iz, G z) :=
        Work.FTS.IPGen.cs_sqrt_le hFint hGint hFnn hGnn
    _ = Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g := by
        rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.Spaces.HkSq, Work.Spaces.HkSq, hF, hG]

/-! ## The pointwise slot domination, in general order -/

/-- **The pointwise slot domination of a leaf weight, in general order.**  For the slot `(a,b)`
with `a + b ≤ n` and any leaf weight `ρ` attached to `a`, the weight times the square of the
slot of `h` is dominated by the `ℋ^n`-integrand of `h` at every point with `z ∈ Iz`,
`θ ∈ (0,π/2)`:

  `ρ z θ · (D_z^bD_θ^a h z θ)² ≤ HkIntegrand α n h z θ`.

This is `Work.FTS.IPGen.leaf_dom` with `4` replaced by `n`. -/
theorem leaf_dom_gen {α : ℝ} (hα : 0 < α) {a b n : ℕ} (hab : a + b ≤ n)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) (h : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ρ z θ * (Work.Spaces.mixed b a h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α n h z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hσ : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
  rcases hρ with rfl | rfl | ⟨ha, rfl⟩
  · -- `ρ = leafEta = Whz²`
    rcases eq_or_ne a 0 with h0 | h0
    · subst h0
      rw [Work.Spaces.mixed_zero_right]
      have hb : b ≤ n := by omega
      have hkey : Work.FTS.TransportS.leafEta z θ * (Work.Spaces.DzIter b h z θ) ^ 2
          = (Work.Spaces.DzIter b h z θ * Work.FTS.H2.Whz z θ) ^ 2 := by
        rw [Work.FTS.TransportS.leafEta, ← Work.FTS.H2.hbi_Whz_sq z θ hσ]
        ring
      rw [hkey]
      exact Work.Spaces.sq_le_HkIntegrand_z α n h z θ b hb
    · have h1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr h0
      have hWm := Work.FTS.H2.hbi_Wm_sq α z θ hσ
      simp only [Work.FTS.H2.Wm] at hWm
      have hle : Work.FTS.TransportS.leafEta z θ ≤ Work.Spaces.Wt α z θ ^ 2 := by
        rw [Work.FTS.TransportS.leafEta, hWm]
        exact mul_le_mul_of_nonneg_left (Work.FTS.H2.rpow_eta_le_gam hα hθI) (sq_nonneg _)
      calc Work.FTS.TransportS.leafEta z θ * (Work.Spaces.mixed b a h z θ) ^ 2
          ≤ Work.Spaces.Wt α z θ ^ 2 * (Work.Spaces.mixed b a h z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = (Work.Spaces.mixed b a h z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
        _ ≤ Work.Spaces.HkIntegrand α n h z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α n h z θ a b h1 (by omega)
  · -- `ρ = leafOne = 1²`
    rcases eq_or_ne a 0 with h0 | h0
    · subst h0
      rw [Work.Spaces.mixed_zero_right]
      have hb : b ≤ n := by omega
      have hle : Work.FTS.TransportS.leafOne z θ ≤ Work.FTS.H2.Whz z θ ^ 2 := by
        rw [Work.FTS.TransportS.leafOne, Work.FTS.H2.hbi_Whz_sq z θ hσ]
        exact le_mul_of_one_le_right (sq_nonneg _)
          (Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ)
      calc Work.FTS.TransportS.leafOne z θ * (Work.Spaces.DzIter b h z θ) ^ 2
          ≤ Work.FTS.H2.Whz z θ ^ 2 * (Work.Spaces.DzIter b h z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = (Work.Spaces.DzIter b h z θ * Work.FTS.H2.Whz z θ) ^ 2 := by ring
        _ ≤ Work.Spaces.HkIntegrand α n h z θ :=
            Work.Spaces.sq_le_HkIntegrand_z α n h z θ b hb
    · have h1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr h0
      have hWm := Work.FTS.H2.hbi_Wm_sq α z θ hσ
      simp only [Work.FTS.H2.Wm] at hWm
      have hle : Work.FTS.TransportS.leafOne z θ ≤ Work.Spaces.Wt α z θ ^ 2 := by
        rw [Work.FTS.TransportS.leafOne, hWm]
        exact le_mul_of_one_le_right (sq_nonneg _)
          (Work.FTS.TransportS.one_le_rpow_neg (le_of_lt (Work.Spaces.gam_pos hα)) hθ)
      calc Work.FTS.TransportS.leafOne z θ * (Work.Spaces.mixed b a h z θ) ^ 2
          ≤ Work.Spaces.Wt α z θ ^ 2 * (Work.Spaces.mixed b a h z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = (Work.Spaces.mixed b a h z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
        _ ≤ Work.Spaces.HkIntegrand α n h z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α n h z θ a b h1 (by omega)
  · -- `ρ = leafGam α = Wm²`, only at slots with `a ≥ 1`
    have hWm := Work.FTS.H2.hbi_Wm_sq α z θ hσ
    simp only [Work.FTS.H2.Wm] at hWm
    have hle : Work.FTS.TransportS.leafGam α z θ = Work.Spaces.Wt α z θ ^ 2 := by
      rw [Work.FTS.TransportS.leafGam, ← hWm]
    calc Work.FTS.TransportS.leafGam α z θ * (Work.Spaces.mixed b a h z θ) ^ 2
        = Work.Spaces.Wt α z θ ^ 2 * (Work.Spaces.mixed b a h z θ) ^ 2 := by rw [hle]
      _ = (Work.Spaces.mixed b a h z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α n h z θ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α n h z θ a b ha (by omega)

/-! ## The requested general-order per-slot bound -/

theorem slotPairing_abs_le_gen {α : ℝ} (hα : 0 < α) {a b n : ℕ} (hab : a + b ≤ n) {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {f g : Work.FTS.Galerkin.Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmf : Work.Spaces.HkMem α n f) (hmg : Work.Spaces.HkMem α n g) : |Work.FTS.TransportS.slotPairing ρ a b f g| ≤ Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g := by
  have hmain : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      ρ z θ * Work.Spaces.mixed b a f z θ * Work.Spaces.mixed b a g z θ|
      ≤ Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g :=
    cs_slotInt_abs_le_gen hmf hmg (Work.FTS.IPGen.leaf_nonneg hρ)
      (fun z hz θ hθ => leaf_dom_gen hα hab hρ f hz hθ)
      (fun z hz θ hθ => leaf_dom_gen hα hab hρ g hz hθ)
  rw [Work.FTS.TransportS.slotPairing]
  exact hmain

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mixed_le_WlInf6_cd6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `mixed_le_WlInf6_cd6`

Pointwise control of every mixed derivative `D_z^b D_θ^a f` (`1 ≤ a`, `a + b ≤ 6`) inside the
open quadrant by the `𝒲^{6,∞}`-norm, for a datum that is only `C^6` on the open quadrant
`Q0 = (0,∞) × (0,π/2)`:

`|D_z^b D_θ^a f (z,θ)| ≤ 1000 · |f|_{𝒲^{6,∞}} · (α + sin 2θ) · sin(2θ)^{α/5}`.

This is the `C^6`-only companion of `Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6` (the
proved statement for `SmoothOpen` data), and of `Work.FTS.OpenPkg.Mixed_le_WlInf_open` (the
order-4 version).

## Route

The angular summands of the `𝒲^{6,∞}`-norm control
`(z+1)^k ∂_z^k D_θ^a f · sin(2θ)^{-α/5}/(α + sin 2θ)`, and
`Work.Spaces.pz_Dth_sup_bound` turns this into

`|z^k ∂_z^k D_θ^a f| ≤ |f|_𝒲 · (z+1)^{-k} (α + sin 2θ) sin(2θ)^{α/5}`   (`1 ≤ a`, `k + a ≤ 6`),

which is `Work.FTS.StrongPersist.N6Trans.L6FBound.zpz_Dth_le_WlInf6`.

It remains to write `D_z^b` as a combination of the `z^k∂_z^k`.  The Stirling expansion
`D_z^b = ∑_{k≤b} S(b,k) z^k ∂_z^k` holds on the open set where the *`z`-slices* of the function
are `C^b`; for a `C^6` datum the function `D_θ^a f` has precisely `6 - a ≥ b` orders of joint
smoothness on `Q0` (`contDiffOn_uncurry_DthIter_le`), so the order-`b` expansion
`DzIter_eq_sum_scoef_of_contDiffOn_order` applies.  The total coefficient mass is the Bell
number `bell b ≤ 1000` for `b ≤ 6` (`Work.Spaces.abs_sum_scoef_mul_le`), and since
`z^k/(z+1)^k ≤ 1` for `z > 0`, each of the at most `b+1 ≤ 7` summands is bounded by the same
quantity `|f|_𝒲 (α + sin 2θ) sin(2θ)^{α/5}`.
-/

open scoped Real Topology

namespace Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6

set_option autoImplicit false

/-! ## Finite-order smoothness of the angular operator `D_θ` and its iterates

(The open-quadrant analogue of `Work.FTS.GalBasis.Xmb.contDiffOn_uncurry_pzIter_le`; `D_θ` is
`sin(2θ) ∂_θ`, and the extra factor is smooth on the whole plane, so it costs no order.) -/

theorem contDiffOn_uncurry_Dth_le {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (h : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry f) V) :
    ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.Dth f)) V := by
  have hpth := Work.FTS.GalBasis.Xmb.contDiffOn_uncurry_pth_le hV h
  have hs : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun p : ℝ × ℝ => Real.sin (2 * p.2)) V := by
    fun_prop
  have hmul := hs.mul hpth
  rw [show Function.uncurry (Work.Spaces.Dth f)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth f) p from rfl]
  exact hmul

/-- Every iterate of `D_θ` costs one order of differentiability on an open set. -/
theorem contDiffOn_uncurry_DthIter_le {f : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry f) V) :
    ∀ j k : ℕ, j + k ≤ N →
      ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.DthIter j f)) V := by
  intro j
  induction j with
  | zero => intro k hk; simpa using h.of_le (by exact_mod_cast (show k ≤ N by omega))
  | succ j ih =>
      intro k hjk
      have h2 : ContDiffOn ℝ (((k + 1 : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.DthIter j f)) V := ih (k + 1) (by omega)
      simpa [Work.Spaces.DthIter_succ] using contDiffOn_uncurry_Dth_le hV h2

/-! ## The pointwise bound -/

theorem mixed_le_WlInf6_cd6 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hfm : Work.Spaces.WlInfMem α 6 f) {a b : ℕ} (ha : 1 ≤ a) (hab : a + b ≤ 6)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.mixed b a f z θ| ≤ 1000 * (Work.Spaces.WlInf α 6 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hb6 : b ≤ 6 := by omega
  have hzθQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθ.1, hθ.2⟩
  -- the target factor is nonnegative, and so is the bound
  have hsin0 : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg' hθI
  have hY : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hsin0 _)
  have hW : 0 ≤ Work.Spaces.WlInf α 6 f :=
    Work.FTS.StrongPersist.N6Trans.L6FBound.WlInf6_nonneg hfm
  have hM : 0 ≤ Work.Spaces.WlInf α 6 f
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := mul_nonneg hW hY
  -- `D_θ^a f` is `C^b` on the open quadrant, since `a + b ≤ 6`
  have hsmD : ContDiffOn ℝ ((b : ℕ) : WithTop ℕ∞)
      (Function.uncurry (Work.Spaces.DthIter a f)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_DthIter_le Work.FTS.EllipticEst.isOpen_Q0 hf a b hab
  -- the Stirling expansion of `D_z^b` on the open quadrant
  have hStir := DzIter_eq_sum_scoef_of_contDiffOn_order Work.FTS.EllipticEst.isOpen_Q0 b hsmD
    z θ hzθQ
  rw [Work.Spaces.mixed, hStir]
  -- every summand is bounded by `|f|_𝒲 · (α + sin 2θ) sin(2θ)^{α/5}`
  have hterm : ∀ k ≤ b, |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter a f) z θ|
      ≤ Work.Spaces.WlInf α 6 f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
    fun k _ => Work.FTS.StrongPersist.N6Trans.L6FBound.zpz_Dth_le_WlInf6 hα hfm ha (by omega)
      hzI hθI
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b
      (Work.Spaces.WlInf α 6 f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
      (fun k => z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter a f) z θ) hterm
  calc |∑ k ∈ Finset.range (b + 1), (Work.Spaces.scoef b k : ℝ)
        * (z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter a f) z θ)|
      ≤ (Work.Spaces.bell b : ℝ) * (Work.Spaces.WlInf α 6 f
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := hsum
    _ ≤ 1000 * (Work.Spaces.WlInf α 6 f
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast Work.FTS.StrongPersist.N6Trans.L6FBound.bell_le_six b hb6) hM

end Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L6Aux.gamCoef_angBlk6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L6Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- For `1 ≤ i ≤ 6` the `i`-th `dthU`-iterate of the angular coefficient `Γ(θ)/c(α)` is
dominated by `10⁶·α·Γ(θ)`: the factor `c(α)⁻¹` costs at most `10` (`Spaces.c_bounds`), the
iterate of `Γ` costs `α·10⁵·Γ(θ)` (`Spaces.dthU_iter_Gam_abs_bound` with the uniform bound
`M = 10⁵` for the coefficients `Tfun j`, `j ≤ 5`, supplied by `LocData6.Tfun_abs_le5`). -/
lemma dthU_gamCoefAng_le6 {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) {i : ℕ} (hi1 : 1 ≤ i) (hi6 : i ≤ 6) :
    |Work.Spaces.dthU^[i] (fun t => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t) θ|
      ≤ 10 ^ 6 * α * Work.Spaces.Gam α θ := by
  have hdec : (fun t : ℝ => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t)
      = fun t : ℝ => (Work.Spaces.c α)⁻¹ * Work.Spaces.Gam α t := by
    funext t; rw [Work.FTS.StrongPersist.L3Aux.gamCoefAng_eq]; ring
  have hcpos : 0 < Work.Spaces.c α := Work.FTS.StrongPersist.L3Aux.c_pos hα hα1
  have h1 : (Work.Spaces.c α)⁻¹ ≤ 10 := by
    rw [inv_le_iff_one_le_mul₀ hcpos]
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  have h2 : |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
      ≤ α * 100000 * Work.Spaces.Gam α θ :=
    Work.Spaces.dthU_iter_Gam_abs_bound i hi1 α hα 100000
      (fun t _ => Work.FTS.LocData6.Tfun_abs_le5 (i - 1) (by omega) α hα hα1 t) θ hθ
  rw [hdec, Work.Spaces.dthU_iter_const_mul, abs_mul, abs_of_pos (inv_pos.mpr hcpos)]
  calc (Work.Spaces.c α)⁻¹ * |Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ|
      ≤ 10 * (α * 100000 * Work.Spaces.Gam α θ) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 10 ^ 6 * α * Work.Spaces.Gam α θ := by ring

/-- Pointwise square bound for the angular jets: for `1 ≤ i ≤ 6` the square of the `i`-th
`dthU`-iterate of `Γ(θ)/c(α)` is at most `10¹²·α²Γ(θ)²`. -/
lemma dthU_gamCoefAng_sq_le6 {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Work.Spaces.Iθ) {i : ℕ} (hi1 : 1 ≤ i) (hi6 : i ≤ 6) :
    (Work.Spaces.dthU^[i] (fun t => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t) θ) ^ 2
      ≤ 10 ^ 12 * α ^ 2 * (Work.Spaces.Gam α θ) ^ 2 := by
  have habs := dthU_gamCoefAng_le6 hα hα1 hθ hi1 hi6
  have hnon : 0 ≤ 10 ^ 6 * α * Work.Spaces.Gam α θ := by
    have hG := (Work.Spaces.Gam_bounds α θ hα hθ).1
    positivity
  have h4 : (Work.Spaces.dthU^[i] (fun t => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t) θ) ^ 2
      ≤ (10 ^ 6 * α * Work.Spaces.Gam α θ) ^ 2 :=
    sq_le_sq.mpr (by rw [abs_of_nonneg hnon]; exact habs)
  calc (Work.Spaces.dthU^[i] (fun t => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t) θ) ^ 2
      ≤ (10 ^ 6 * α * Work.Spaces.Gam α θ) ^ 2 := h4
    _ = 10 ^ 12 * α ^ 2 * (Work.Spaces.Gam α θ) ^ 2 := by ring

-- The angular block of the order-`6` separation bound: the `θ`-integrand factor of
-- `HkIntegrand α 6` of the separated function `gamCoefAng α θ * bcoefRad z` is dominated by
-- `radAngInt α θ = sin(2θ)^{-η} + α²Γ(θ)²sin(2θ)^{-γ}` with a constant uniform in `α ∈ (0,1]`.
-- Route: `gamCoefAng² ≤ 100` (`L3Aux.gamCoefAng_sq_le`); for `1 ≤ i ≤ 6`,
-- `dthU^[i] (Γ/c) = c⁻¹ · dthU^[i] Γ` (`Spaces.dthU_iter_const_mul`) with
-- `|dthU^[i] Γ| ≤ α·10⁵·Γ` (`Spaces.dthU_iter_Gam_abs_bound` with `M = 10⁵` furnished by
-- `LocData6.Tfun_abs_le5`; keep the factor `α`!), and `c ≥ 1/10` (`Spaces.c_bounds`), so each
-- square is `≤ 10¹²·α²Γ²`; six of them plus the `≤ 100` first term give
-- `K = 10¹³`.  At the endpoints both sides vanish (`Real.zero_rpow`).
theorem gamCoef_angBlk6 : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
    (Work.FTS.StrongPersist.L3Aux.gamCoefAng α θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + ∑ i ∈ Finset.range 7,
          (if 1 ≤ i then
            (Work.Spaces.dthU^[i] (fun t => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t) θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
           else 0)
      ≤ K * Work.FTS.StrongPersist.L3Aux.radAngInt α θ := by
  refine ⟨10 ^ 13, by norm_num, ?_⟩
  intro α hα hα1 θ hθ
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.StrongPersist.L3Aux.sin_two_nonneg_of_mem_Iθ hθ
  have hG : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  have hR : 0 ≤ Work.FTS.StrongPersist.L3Aux.radAngInt α θ :=
    Work.FTS.StrongPersist.L3Aux.radAngInt_nonneg hs
  have hsE : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hs _
  have hsG : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hs _
  -- the two `radAngInt`-comparisons
  have hleE : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ Work.FTS.StrongPersist.L3Aux.radAngInt α θ := by
    rw [Work.FTS.StrongPersist.L3Aux.radAngInt_apply]
    have : 0 ≤ α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsG
    linarith
  have hleG : α ^ 2 * (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ Work.FTS.StrongPersist.L3Aux.radAngInt α θ := by
    rw [Work.FTS.StrongPersist.L3Aux.radAngInt_apply]
    linarith [hsE]
  -- the first summand
  have h1 : (Work.FTS.StrongPersist.L3Aux.gamCoefAng α θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ 100 * Work.FTS.StrongPersist.L3Aux.radAngInt α θ := by
    calc _ ≤ 100 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_right
            (Work.FTS.StrongPersist.L3Aux.gamCoefAng_sq_le hα hα1 hθ) hsE
      _ ≤ 100 * Work.FTS.StrongPersist.L3Aux.radAngInt α θ :=
          mul_le_mul_of_nonneg_left hleE (by norm_num)
  -- the angular sum
  have h3 : ∀ i ∈ Finset.range 7,
      (if 1 ≤ i then
        (Work.Spaces.dthU^[i] (fun t => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
       else 0)
      ≤ 10 ^ 12 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    intro i hi
    by_cases hi1 : 1 ≤ i
    · rw [if_pos hi1]
      have hi6 : i ≤ 6 := by
        have := Finset.mem_range.mp hi
        omega
      have hb := dthU_gamCoefAng_sq_le6 hα hα1 hθ hi1 hi6
      calc (Work.Spaces.dthU^[i] (fun t => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          ≤ (10 ^ 12 * α ^ 2 * (Work.Spaces.Gam α θ) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
            mul_le_mul_of_nonneg_right hb hsG
        _ = 10 ^ 12 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
    · rw [if_neg hi1]
      exact mul_nonneg (by norm_num)
        (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsG)
  have h2 : (∑ i ∈ Finset.range 7,
        (if 1 ≤ i then
          (Work.Spaces.dthU^[i] (fun t => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
         else 0))
      ≤ 7 * 10 ^ 12 * Work.FTS.StrongPersist.L3Aux.radAngInt α θ := by
    calc (∑ i ∈ Finset.range 7, (if 1 ≤ i then
              (Work.Spaces.dthU^[i] (fun t => Work.FTS.StrongPersist.L3Aux.gamCoefAng α t) θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
             else 0))
        ≤ ∑ _i ∈ Finset.range 7, 10 ^ 12 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := Finset.sum_le_sum h3
      _ = 7 * (10 ^ 12 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
            simp [Finset.sum_const, Finset.card_range]
      _ = 7 * 10 ^ 12 * (α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
      _ ≤ 7 * 10 ^ 12 * Work.FTS.StrongPersist.L3Aux.radAngInt α θ :=
            mul_le_mul_of_nonneg_left hleG (by norm_num)
  have hh : (100 : ℝ) + 7 * 10 ^ 12 ≤ 10 ^ 13 := by norm_num
  have hfin := mul_le_mul_of_nonneg_right hh hR
  linarith [h1, h2, hfin]

end Work.FTS.StrongPersist.L6Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L6Aux.radSnorm6_int_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L6Aux

set_option maxHeartbeats 1600000

/-- Measurability of the radial block `∑_{q<7} ((Zop^[q] bcoefRad) z · w z)²`. -/
lemma measurable_radSnorm6 :
    Measurable (fun z : ℝ => ∑ q ∈ Finset.range 7,
      ((Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
        * Work.Spaces.w z) ^ 2) := by
  refine Finset.measurable_sum _ fun j _ => ?_
  have h3 : Measurable (fun a : ℝ =>
      (Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad) a * Work.Spaces.w a) :=
    (Work.FTS.StrongPersist.L3Aux.measurable_Zop_iter j).mul
      Work.FTS.StrongPersist.L3Aux.measurable_w
  have hgoal : (fun a : ℝ =>
        ((Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad) a
          * Work.Spaces.w a) ^ 2)
      = fun a : ℝ =>
        ((Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad) a * Work.Spaces.w a)
        * ((Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad) a * Work.Spaces.w a) := by
    funext a; rw [pow_two]
  rw [hgoal]
  exact h3.mul h3

/-- Nonnegativity of the radial block `∑_{q<7} ((Zop^[q] bcoefRad) z · w z)²`. -/
lemma radSnorm6_nonneg (z : ℝ) : 0 ≤ ∑ q ∈ Finset.range 7,
    ((Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad) z * Work.Spaces.w z) ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

-- The `z`-integral of the radial block `∑_{q<7} ((Zop^[q] bcoefRad) z · w z)²` of the order-`6`
-- separation bound, given the pointwise bound `|(Zop^[j] bcoefRad) z · w z| ≤ K/(1+z)` for
-- `j ≤ 6`.  This is the `range 7` analogue of the proved `L3Aux.radSnorm_int_le`
-- (`range 4`, constant `8K²`): the sum is `≤ 7K²/(1+z)²` pointwise and `∫_Iz 1/(1+z)² ≤ 2`
-- (`Work.Elliptic.WtoH_IntZ`), whence `14K²`.  The measurability lemmas
-- `L3Aux.measurable_Zop_iter`, `L3Aux.measurable_w` are in the imported module.
theorem radSnorm6_int_le {K : ℝ} (hK : 0 ≤ K)
    (hrb : ∀ j ≤ 6, ∀ z ∈ Set.Ici (0 : ℝ),
      |(Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad) z * Work.Spaces.w z|
        ≤ K / (1 + z)) :
    MeasureTheory.IntegrableOn
        (fun z => ∑ q ∈ Finset.range 7,
          ((Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad) z * Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ q ∈ Finset.range 7,
          ((Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad) z * Work.Spaces.w z) ^ 2)
        ≤ 14 * K ^ 2 := by
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      (∑ q ∈ Finset.range 7,
          ((Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
            * Work.Spaces.w z) ^ 2) ≤ 7 * K ^ 2 * (1 / (1 + z) ^ 2) := by
    intro z hz
    have h1z : (0 : ℝ) < 1 + z := by
      have hz0 : 0 ≤ z := hz
      linarith
    have h1 : ∀ j ∈ Finset.range 7,
        ((Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
            * Work.Spaces.w z) ^ 2 ≤ K ^ 2 * (1 / (1 + z) ^ 2) := by
      intro j hj
      have hj6 : j ≤ 6 := by have := Finset.mem_range.mp hj; omega
      have h := hrb j hj6 z hz
      have h2 : ((Work.Spaces.Zop^[j] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
            * Work.Spaces.w z) ^ 2 ≤ (K / (1 + z)) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ K / (1 + z))]
        exact h
      refine h2.trans (le_of_eq ?_)
      rw [div_pow, one_div]
      ring
    have hsum := Finset.sum_le_sum h1
    refine hsum.trans ?_
    have hsum' : (∑ _j ∈ Finset.range 7, K ^ 2 * (1 / (1 + z) ^ 2))
        = 7 * K ^ 2 * (1 / (1 + z) ^ 2) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    rw [hsum']
  have hdom : MeasureTheory.IntegrableOn (fun z : ℝ => 7 * K ^ 2 * (1 / (1 + z) ^ 2))
      Work.Spaces.Iz := Work.Elliptic.WtoH_IntZ.1.const_mul (7 * K ^ 2)
  have hSint : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∑ q ∈ Finset.range 7,
        ((Work.Spaces.Zop^[q] Work.FTS.StrongPersist.L3Aux.bcoefRad) z
          * Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    refine hdom.mono' measurable_radSnorm6.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (radSnorm6_nonneg z)]
    exact hpt z hz
  refine ⟨hSint, ?_⟩
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => radSnorm6_nonneg z) hdom
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hpt)
  refine hmono.trans ?_
  rw [MeasureTheory.integral_const_mul]
  have h2 : (∫ z in Work.Spaces.Iz, 1 / (1 + z) ^ 2) ≤ 2 := Work.Elliptic.WtoH_IntZ.2
  have h3 : (0 : ℝ) ≤ 7 * K ^ 2 := by positivity
  calc 7 * K ^ 2 * (∫ z in Work.Spaces.Iz, 1 / (1 + z) ^ 2) ≤ 7 * K ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left h2 h3
    _ = 14 * K ^ 2 := by ring

end Work.FTS.StrongPersist.L6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.LeibMajor

-- The statement uses `π` (i.e. `Real.pi`); the package sets `autoImplicit = false`, so the
-- scoped `Real` notation has to be opened for `π` to elaborate at all.
open scoped Real Topology
open MeasureTheory Set Filter
open Finset

noncomputable section

/-! ## The matching of the two Leibniz majorants

Both `EasyLeib` (the easy Leibniz majorant of the `D_θ`-transport pairing) and `EasyMajor`
(the workspace majorant of the flat `ℋ⁴`-pairing) are finite sums of *absolute values* of
Leibniz summands, so the comparison is purely combinatorial: the Leibniz summand of the slot
`(a,b)` is literally a summand of `EasyMajor` up to the binomial factor of the Leibniz rule,
and `EasyMajor` retains *at least* every summand that `EasyLeib` keeps.

The proof proceeds through three purely algebraic facts, all pointwise in `(z,θ)` and
independent of the `SmoothOpen` hypotheses:

* `FL_zero_le_ZL` : the `a = 0` slot of `EasyLeib` (the `D_z`-slot) is dominated by the
  `D_z`-part `ZL` of `EasyMajor` (the `xD` summands, with the hard slot `(i,b) = (4,0)`
  removed on both sides);
* `FL_le_MiL` : every slot with `a ≥ 1` (a mixed slot) is dominated by the corresponding
  mixed slot `MiL` (the `yM` summands, with the hard family `(a1,b1) = (0,0)`,
  `i + j = 4` removed on both sides);
* splitting the outer `range 5`-sums with `Finset.sum_range_succ'` and adding. -/

/-- The `a`-th slot sum of `EasyLeib` (the inner double sum over the Leibniz splits). -/
private def FL (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) (a : ℕ) : ℝ :=
  ∑ b ∈ Finset.range 5,
    (if a + b ≤ 4 then
      ∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
        (if a1 = 0 ∧ b1 = 0 then 0 else
          Work.FTS.TransportS.slotW α a z θ * |Work.Spaces.mixed b1 a1 f z θ|
            * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ|
            * |Work.Spaces.mixed b a g z θ|)
    else 0)

/-- The `D_z`-part of `EasyMajor` (the `xD` summands). -/
private def ZL (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
    (if i = 4 ∧ b = 0 then 0 else |Work.FTS.H2.xD f g i b z θ|)

/-- The `i`-th mixed slot of `EasyMajor` (the `yM` summands). -/
private def MiL (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 5,
    (if 1 ≤ i ∧ i + j ≤ 4 then
      ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |Work.FTS.H2.yM α f g i j a b z θ|)
    else 0)

private lemma EasyLeib_eq_sum_FL (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.StrongPersist.N6Trans.EasyLeib α f g z θ
      = ∑ a ∈ Finset.range 5, FL α f g z θ a := rfl

private lemma EasyMajor_eq (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.H2.EasyMajor α f g z θ
      = ZL f g z θ + ∑ i ∈ Finset.range 5, MiL α f g z θ i := rfl

/-- The elementary product inequality behind every summand comparison: a nonnegative weight
`W` times three nonnegative factors is dominated by the same expression with the coefficient
`c ≥ 1` in front and the weight `W` moved to the back. -/
private lemma prod_four_le {W c A B C : ℝ} (hW : 0 ≤ W) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hc : 1 ≤ c) : W * A * B * C ≤ c * A * B * C * W := by
  have hX : 0 ≤ A * B * C := by positivity
  have h1 : W ≤ c * W := by nlinarith
  calc W * A * B * C = W * (A * B * C) := by ring
    _ ≤ (c * W) * (A * B * C) := mul_le_mul_of_nonneg_right h1 hX
    _ = c * A * B * C * W := by ring

/-- The `a = 0` summand (`a1 = 0` fixed): the `D_z`-slot Leibniz summand of `EasyLeib` is
dominated by the `xD` summand of `EasyMajor` with the same split `k`, the factor
`(m.choose k) ≥ 1` accounting for the binomial coefficient of the Leibniz rule. -/
private lemma xD_term_le {α : ℝ} {f g : ℝ → ℝ → ℝ} {z θ : ℝ} {m k : ℕ} (hk : k ≤ m) :
    (if (0:ℕ) = 0 ∧ k = 0 then 0 else
      Work.FTS.TransportS.slotW α 0 z θ * |Work.Spaces.mixed k 0 f z θ|
        * |Work.Spaces.mixed (m - k) (0 - 0 + 1) g z θ| * |Work.Spaces.mixed m 0 g z θ|)
      ≤ (if m = 4 ∧ k = 0 then 0 else |Work.FTS.H2.xD f g m k z θ|) := by
  by_cases hk0 : k = 0
  · rw [if_pos ⟨rfl, hk0⟩]
    split_ifs
    · exact le_rfl
    · exact abs_nonneg _
  · rw [if_neg (fun h => hk0 h.2), if_neg (fun h => hk0 h.2)]
    simp only [Work.FTS.TransportS.slotW_zero]
    have hxabs : |Work.FTS.H2.xD f g m k z θ|
        = (m.choose k : ℝ) * |Work.Spaces.DzIter k f z θ|
          * |Work.Spaces.mixed (m - k) 1 g z θ| * |Work.Spaces.DzIter m g z θ|
          * Work.FTS.H2.Whz z θ ^ 2 := by
      unfold Work.FTS.H2.xD
      rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (m.choose k : ℝ) from Nat.cast_nonneg _),
        abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (sq_nonneg (Work.FTS.H2.Whz z θ))]
      ring
    rw [hxabs]
    have hc : (1:ℝ) ≤ (m.choose k : ℝ) := by
      have h := Nat.choose_pos hk
      exact_mod_cast h
    exact prod_four_le (sq_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hc

/-- The `a ≥ 1` summand: the mixed-slot Leibniz summand of `EasyLeib` is dominated by the
`yM` summand of `EasyMajor` with the same split `(a1,b1)`, the binomial product
`(a.choose a1)·(b.choose b1) ≥ 1` accounting for the Leibniz coefficients. -/
private lemma yM_term_le {α : ℝ} {f g : ℝ → ℝ → ℝ} {z θ : ℝ} {a b a1 b1 : ℕ}
    (ha : 1 ≤ a) (ha1 : a1 ≤ a) (hb1 : b1 ≤ b) :
    (if a1 = 0 ∧ b1 = 0 then 0 else
      Work.FTS.TransportS.slotW α a z θ * |Work.Spaces.mixed b1 a1 f z θ|
        * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ| * |Work.Spaces.mixed b a g z θ|)
      ≤ (if a1 = 0 ∧ b1 = 0 ∧ a + b = 4 then 0
          else |Work.FTS.H2.yM α f g a b a1 b1 z θ|) := by
  by_cases h00 : a1 = 0 ∧ b1 = 0
  · rw [if_pos h00]
    split_ifs
    · exact le_rfl
    · exact abs_nonneg _
  · rw [if_neg h00, if_neg (fun h => h00 ⟨h.1, h.2.1⟩)]
    simp only [Work.FTS.TransportS.slotW_of_pos' α ha]
    have hyabs : |Work.FTS.H2.yM α f g a b a1 b1 z θ|
        = ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)) * |Work.Spaces.mixed b1 a1 f z θ|
          * |Work.Spaces.mixed (b - b1) (a - a1 + 1) g z θ| * |Work.Spaces.mixed b a g z θ|
          * Work.FTS.H2.Wm α z θ ^ 2 := by
      unfold Work.FTS.H2.yM
      rw [abs_mul, abs_mul,
        abs_of_nonneg (show (0:ℝ) ≤ (a.choose a1 : ℝ) from Nat.cast_nonneg _),
        abs_of_nonneg (show (0:ℝ) ≤ (b.choose b1 : ℝ) from Nat.cast_nonneg _),
        abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (sq_nonneg (Work.FTS.H2.Wm α z θ))]
      ring
    rw [hyabs]
    have h1 : (1:ℝ) ≤ (a.choose a1 : ℝ) := by
      have h := Nat.choose_pos ha1
      exact_mod_cast h
    have h2 : (1:ℝ) ≤ (b.choose b1 : ℝ) := by
      have h := Nat.choose_pos hb1
      exact_mod_cast h
    have hc : (1:ℝ) ≤ ((a.choose a1 : ℝ) * (b.choose b1 : ℝ)) := by nlinarith
    exact prod_four_le (sq_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hc

/-- The `a = 0` slot of `EasyLeib` is dominated by the `D_z`-part `ZL` of `EasyMajor`. -/
private lemma FL_zero_le_ZL (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    FL α f g z θ 0 ≤ ZL f g z θ := by
  unfold FL ZL
  refine Finset.sum_le_sum fun b hb => ?_
  have hb4 : b ≤ 4 := by have := Finset.mem_range.mp hb; omega
  rw [if_pos (by omega : 0 + b ≤ 4)]
  rw [show (0:ℕ) + 1 = 1 from rfl, Finset.sum_range_one]
  refine Finset.sum_le_sum fun b1 hb1 => ?_
  have hb1' : b1 ≤ b := by have := Finset.mem_range.mp hb1; omega
  exact xD_term_le (α := α) (f := f) (g := g) (z := z) (θ := θ) (m := b) (k := b1) hb1'

/-- Every mixed slot of `EasyMajor` is nonnegative. -/
private lemma MiL_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) (i : ℕ) :
    0 ≤ MiL α f g z θ i := by
  unfold MiL
  refine Finset.sum_nonneg fun j hj => ?_
  split_ifs
  · exact Finset.sum_nonneg fun a ha => Finset.sum_nonneg fun b hb => by
      split_ifs
      · exact le_rfl
      · exact abs_nonneg _
  · exact le_rfl

/-- Every slot of `EasyLeib` with `a ≥ 1` is dominated by the corresponding mixed slot of
`EasyMajor`. -/
private lemma FL_le_MiL (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) (i : ℕ) (hi : 1 ≤ i) :
    FL α f g z θ i ≤ MiL α f g z θ i := by
  unfold FL MiL
  refine Finset.sum_le_sum fun b hb => ?_
  by_cases hg : i + b ≤ 4
  · rw [if_pos hg, if_pos ⟨hi, hg⟩]
    refine Finset.sum_le_sum fun a1 ha1 => Finset.sum_le_sum fun b1 hb1 => ?_
    exact yM_term_le (α := α) (f := f) (g := g) (z := z) (θ := θ) (a := i) (b := b)
      (a1 := a1) (b1 := b1) hi (by have := Finset.mem_range.mp ha1; omega)
      (by have := Finset.mem_range.mp hb1; omega)
  · rw [if_neg hg, if_neg (fun h => hg h.2)]

theorem EasyLeib_le_EasyMajor {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Work.FTS.StrongPersist.N6Trans.EasyLeib α f g z θ ≤ Work.FTS.H2.EasyMajor α f g z θ := by
  intro z θ hz hθ hθ2
  rw [EasyMajor_eq, EasyLeib_eq_sum_FL]
  have hA : FL α f g z θ 0 ≤ ZL f g z θ := FL_zero_le_ZL α f g z θ
  have hB : (∑ a ∈ Finset.range 4, FL α f g z θ (a + 1))
      ≤ MiL α f g z θ 0 + ∑ a ∈ Finset.range 4, MiL α f g z θ (a + 1) := by
    have h1 : (∑ a ∈ Finset.range 4, FL α f g z θ (a + 1))
        ≤ ∑ a ∈ Finset.range 4, MiL α f g z θ (a + 1) :=
      Finset.sum_le_sum fun a ha => FL_le_MiL α f g z θ (a + 1) (by omega)
    have h2 : (0:ℝ) ≤ MiL α f g z θ 0 := MiL_nonneg α f g z θ 0
    linarith
  have hsplit1 : (∑ a ∈ Finset.range 5, FL α f g z θ a)
      = (∑ a ∈ Finset.range 4, FL α f g z θ (a + 1)) + FL α f g z θ 0 :=
    Finset.sum_range_succ' (fun a => FL α f g z θ a) 4
  have hsplit2 : (∑ i ∈ Finset.range 5, MiL α f g z θ i)
      = (∑ i ∈ Finset.range 4, MiL α f g z θ (i + 1)) + MiL α f g z θ 0 :=
    Finset.sum_range_succ' (fun i => MiL α f g z θ i) 4
  rw [hsplit1, hsplit2]
  linarith

end

end Work.FTS.StrongPersist.N6Trans.LeibMajor
end
