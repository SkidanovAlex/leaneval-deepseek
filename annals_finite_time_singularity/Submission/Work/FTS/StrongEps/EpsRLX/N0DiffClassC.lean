import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.CoercivityFix.PsiMul.PsiZop
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.OpenPkg.l12_open_bundle
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.BdryTraces_psi_mul_open
import Submission.Work.FTS.StrongEps.EpsSqTools.Shift
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.LGammaTMem
import Submission.Work.FTS.StrongEps.EpsZero.Nstar_zero_classC
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongEps.wtZ_shift_le
import Submission.Work.FTS.StrongPersist.H6Aux.E2Facts
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.N6Trans.slotT2Six
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RXR1.mixed_abs_le_weighted
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.THL.angular_L2_noTrace
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.PzJeps_abs_le_unif =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-- **A pointwise bound for the projected, mollified profile** in terms of the honest `ℋ⁴`-norm of
its argument, uniformly in the mollification scale `ε ∈ (0,1]`: the mollified profile is an average
of the shifted values (bounded by the `ℋ⁴ → L^∞` trade-off `v2_hkMem_pointwise_min`, which needs no
trace hypothesis) weighted by the mass-one kernel `Jker ρ ε`, and the `P₀`-correction is controlled
by the zero-mode bound `l12zero_field`. -/
theorem PzJeps_abs_le_unif {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ Z : Fn,
      Work.FTS.EllipticEst.SmoothOpen Z → Work.Spaces.HkMem α 4 Z →
        ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
          |Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Z) z θ|
            ≤ C * Work.Spaces.HkNorm α 4 Z := by
  obtain ⟨Cv2, hCv2nn, hv2⟩ := Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min hα hα1
  obtain ⟨CJ, hCJpos, hCJ⟩ := Work.FTS.StrongEps.HkSq_Jeps_le ρ hρ.moll
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FTS.OpenPkg.l12zero_field
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  refine ⟨Cv2 + C1 * Real.exp (CJ / 2) / Work.FTS.StrongEps.pzNorm, by positivity, ?_⟩
  intro ε hε Z hsm hmem z θ hz hθ
  have hN0 : 0 ≤ Work.Spaces.HkNorm α 4 Z := Work.Spaces.HkNorm_nonneg α 4 Z
  have hquad : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Z) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Z).mp hsm
  -- ## the pointwise bound of the shifted integrand
  have hstep : ∀ x : ℝ, Cv2 * min x 1 * Work.Spaces.HkNorm α 4 Z
      ≤ Cv2 * Work.Spaces.HkNorm α 4 Z := by
    intro x
    calc Cv2 * min x 1 * Work.Spaces.HkNorm α 4 Z
        = (Cv2 * min x 1) * Work.Spaces.HkNorm α 4 Z := rfl
      _ ≤ (Cv2 * 1) * Work.Spaces.HkNorm α 4 Z :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (min_le_right x 1) hCv2nn) hN0
      _ = Cv2 * Work.Spaces.HkNorm α 4 Z := by ring
  have hpw : ∀ p : ℝ × ℝ,
      |Z (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|
        ≤ Cv2 * Work.Spaces.HkNorm α 4 Z := by
    intro p
    have hθ' := Work.FTS.StrongEps.thShift_mem (p := p.2) hθ
    have h := hv2 Z (hquad 4) hmem 0 0 (by norm_num)
      (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
      (Work.FTS.StrongEps.zShift_pos (p := p.1) hz) hθ'.1 hθ'.2
    simp only [Work.Spaces.mixed_zero_right] at h
    exact le_trans h (hstep (Work.FTS.StrongEps.zShift z p.1))
  -- ## the mollifier part
  have hJnn : ∀ p : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.Jker ρ ε p := by
    intro p
    simp only [Work.FTS.StrongEps.Jker]
    exact mul_nonneg (by positivity) (hρ.moll.nonneg _)
  have hJbound : |Work.FTS.StrongEps.Jeps ρ ε Z z θ| ≤ Cv2 * Work.Spaces.HkNorm α 4 Z := by
    rw [Work.FTS.StrongEps.Jeps_eq_integral ρ ε Z hz hθ]
    have hJint : Integrable (Work.FTS.StrongEps.Jker ρ ε) :=
      Work.FTS.StrongEps.Jker_integrable hρ.moll hε.1
    have hJmass : ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p = 1 :=
      Work.FTS.StrongEps.Jker_integral_eq_one ρ hρ.moll hε.1
    have h1 : |∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p *
        Z (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|
        ≤ ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.Jker ρ ε p *
            Z (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)| := by
      simpa only [Real.norm_eq_abs] using
        (MeasureTheory.norm_integral_le_integral_norm
          (f := fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
            Z (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
    refine le_trans h1 ?_
    rw [show (fun p : ℝ × ℝ => |Work.FTS.StrongEps.Jker ρ ε p *
          Z (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|)
        = (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
            |Z (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|) from by
      funext p
      rw [abs_mul, abs_of_nonneg (hJnn p)]]
    have hle : (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
          |Z (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|)
        ≤ᵐ[MeasureTheory.volume]
        (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p
          * (Cv2 * Work.Spaces.HkNorm α 4 Z)) :=
      Filter.Eventually.of_forall (fun p => mul_le_mul_of_nonneg_left (hpw p) (hJnn p))
    have hIntG : Integrable (fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p
        * (Cv2 * Work.Spaces.HkNorm α 4 Z)) := hJint.mul_const _
    refine le_trans (MeasureTheory.integral_mono_of_nonneg
      (f := fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p *
        |Z (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|)
      (g := fun p : ℝ × ℝ => Work.FTS.StrongEps.Jker ρ ε p
        * (Cv2 * Work.Spaces.HkNorm α 4 Z))
      (Filter.Eventually.of_forall (fun p => mul_nonneg (hJnn p) (abs_nonneg _))) hIntG hle) ?_
    rw [MeasureTheory.integral_mul_const, hJmass, one_mul]
  -- ## the correction part
  have hJsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε Z) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε.1 hquad
  have hJmem : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε Z) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll ⟨hα, hα1⟩ hε.1 hquad hmem
  have hnormJ : Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.Jeps ρ ε Z)
      ≤ Real.exp (CJ / 2) * Work.Spaces.HkNorm α 4 Z := by
    have hsq := hCJ α ⟨hα, hα1⟩ 4 ε hε.1 hε.2 Z hquad hmem hJmem
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.Jeps ρ ε Z))
        ≤ Real.sqrt (Real.exp (CJ * ε) * Work.Spaces.HkSq α 4 Z) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (Real.exp (CJ * ε)) * Real.sqrt (Work.Spaces.HkSq α 4 Z) :=
          Real.sqrt_mul (Real.exp_pos _).le _
      _ = Real.exp (CJ * ε / 2) * Work.Spaces.HkNorm α 4 Z := by
          rw [Real.exp_half, Work.Spaces.HkNorm]
      _ ≤ Real.exp (CJ / 2) * Work.Spaces.HkNorm α 4 Z := by
          refine mul_le_mul_of_nonneg_right ?_ (Work.Spaces.HkNorm_nonneg _ _ _)
          exact Real.exp_le_exp.mpr (by nlinarith [hε.2, hCJpos])
  have hL12 : |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε Z) 0|
      ≤ C1 * (Real.exp (CJ / 2) * Work.Spaces.HkNorm α 4 Z) := by
    refine le_trans (hC1 α hα hα1 (Work.FTS.StrongEps.Jeps ρ ε Z) ⟨hJsm, hJmem⟩) ?_
    exact mul_le_mul_of_nonneg_left hnormJ hC1pos.le
  have hbump : |Work.FTS.StrongEps.bump z θ| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [Work.FTS.StrongEps.bump_nonneg z θ],
      Work.FTS.StrongEps.EpsSqTools.bump_le_one z θ⟩
  have hc : |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε Z) 0
        / Work.FTS.StrongEps.pzNorm| * |Work.FTS.StrongEps.bump z θ|
      ≤ (C1 * Real.exp (CJ / 2) / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 Z := by
    rw [abs_div, abs_of_pos hpzpos]
    calc |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε Z) 0| / Work.FTS.StrongEps.pzNorm
          * |Work.FTS.StrongEps.bump z θ|
        ≤ (C1 * (Real.exp (CJ / 2) * Work.Spaces.HkNorm α 4 Z)) / Work.FTS.StrongEps.pzNorm
            * 1 := by
          refine mul_le_mul (div_le_div_of_nonneg_right hL12 hpzpos.le) hbump (abs_nonneg _)
            (div_nonneg (mul_nonneg hC1pos.le (mul_nonneg (Real.exp_pos _).le hN0)) hpzpos.le)
      _ = (C1 * Real.exp (CJ / 2) / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 Z := by
          ring
  -- ## assembly
  rw [Work.FTS.StrongEps.Pz_apply]
  have hsplit : |Work.FTS.StrongEps.Jeps ρ ε Z z θ
        - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε Z) 0 / Work.FTS.StrongEps.pzNorm
          * Work.FTS.StrongEps.bump z θ|
      ≤ |Work.FTS.StrongEps.Jeps ρ ε Z z θ|
        + |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε Z) 0 / Work.FTS.StrongEps.pzNorm
          * Work.FTS.StrongEps.bump z θ| := by
    have h := abs_add_le (Work.FTS.StrongEps.Jeps ρ ε Z z θ)
      (-(Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε Z) 0 / Work.FTS.StrongEps.pzNorm
        * Work.FTS.StrongEps.bump z θ))
    simpa only [sub_eq_add_neg, abs_neg] using h
  refine le_trans hsplit ?_
  have h2 : |Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε Z) 0 / Work.FTS.StrongEps.pzNorm
        * Work.FTS.StrongEps.bump z θ|
      ≤ (C1 * Real.exp (CJ / 2) / Work.FTS.StrongEps.pzNorm) * Work.Spaces.HkNorm α 4 Z := by
    rw [abs_mul]
    exact hc
  refine le_trans (add_le_add hJbound h2) (le_of_eq ?_)
  ring


end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_LGammaT_Aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongEps.EpsE4Thr.regQo_LGammaT_Aux`

Supporting bounds for `Work.FTS.StrongEps.EpsE4Thr.regQo_LGammaT` (its §0--§3).

`𝓛_Γ^T x ∈ RegQo α 4` for every profile `x` of the class `ClassC α`, `α ∈ (0,1]`.

`RegQo α k f = SmoothOpen f ∧ HkMem α k f ∧ BdryTraces α k f` (`EpsE4Thr/OpenClass.lean`).
The first two conjuncts are available (`smoothOpen_LGammaT_of_L12` with
`ClassCRHS.smoothOpen_L12_radial_classC`, and `ClassCHk.LGammaTMem` / `ClassCRHS.HkMemXnLGammaT`).
This file supplies the third.

## Route

`𝓛_Γ^T x = 𝓛̂x + Corr α x` (`CoercivityFix.LGammaT_eq_Lhat_add_Corr`), where
`𝓛̂x = x + D_z x − 2x/(1+z) − 3D_θx/(1+z)` and, by `Transfer.Corr_eq_radA`,
`Corr α x = Γ(θ)·radA α x (z)` with
`radA α x z = −ampA α z·L₁₂(x)(z) + (ampB α z/c α)·L₁₂(Transport x)(0)`.

* `BdryTraces α 4 (𝓛̂x)`: the summands are `x`, `D_z x`, `D_θ x` (the `RegQo`-ports
  `regQo_dth_dz` plus monotonicity) and the radial multiples `x/(1+z)`, `D_θx/(1+z)`
  (`TracesAux.BdryTraces_psi_mul_open` with `PsiMul.zop_psi_bound`); additivity is
  `ClassC.bdryTraces_add`.
* `BdryTraces α 4 (Corr α x)`: the separated-product lemma
  `TracesAux.BdryTraces_Gam_mul_rad` with the radial trace hypotheses proved here from the
  bounds on `radA`: `‖D_z^b radA(x)‖ ≤ C z^{5/2}` for `z ∈ (0,1)` and `≤ C/z` for `z ≥ 1`.
  These come from the Leibniz expansion of `D_z^b (ampA·L₁₂ x)`
  (`OpenPkg.ProdOpen.leibniz_open_mixed`), the jets of `ampA` (`L12Aux.ampA_dzdIter_abs_le`),
  the jets of `ampB` (`DzBoundR0`) and the angular-moment bound `Qang x k = O(z^{3/2})`
  (`L12Aux.Qang_small_z`) together with its uniform boundedness
  (`StrongEps.classC_mixed_sup_le_four`).

All inputs are `sorry`-free.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## §0  Vocabulary -/

/-- `L₁₂` in the `Coercivity` and in the `Elliptic` vocabulary are the same radial function. -/
theorem L12f_eq_elliptic (f : Fn) :
    Work.Coercivity.L12f f = Work.Elliptic.L12 f := by
  funext z
  show (∫ s in Set.Ioi z,
      (∫ θ in Set.Icc 0 (π / 2), Work.Spaces.K θ * f s θ / s)) =
    ∫ r in Set.Ioi z, ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * f r θ / r
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [Work.Spaces.Iθ]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by
    rw [Work.Elliptic.Ktheta_eq_K]

/-- `x` of class `ClassC` gives `L₁₂(x)(0) = 0` in the `Elliptic` vocabulary. -/
theorem elliptic_L12_zero {α : ℝ} {x : Fn} (hx : Work.FTS.ClassC.ClassC α x) :
    Work.Elliptic.L12 x 0 = 0 := by
  rw [← Work.FTS.H2.constructionL12_eq_ellipticL12]
  exact hx.l12

/-- `L₁₂dens x` is integrable on `(0,∞)` for a `ClassC` profile. -/
theorem integrableOn_L12dens {α : ℝ} {x : Fn} (hx : Work.FTS.ClassC.ClassC α x) :
    MeasureTheory.IntegrableOn (Work.Elliptic.L12dens x) (Set.Ioi 0) := by
  have hF : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar x r / r)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 x hx.reg hx.mem
  refine hF.const_mul 3 |> fun h => h.congr (Filter.Eventually.of_forall fun r => ?_)
  rw [Work.Elliptic.L12dens_eq_three_Fstar_div]

/-! ## §1  The angular-moment bounds -/

/-- The angular moment `Qang x k` of a `ClassC` profile is bounded on `(0,∞)`, uniformly in `z`. -/
theorem Qang_bdd {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Fn} (hx : Work.FTS.ClassC.ClassC α x)
    {k : ℕ} (hk : k ≤ 4) :
    ∃ M : ℝ, 0 < M ∧ ∀ z : ℝ, 0 < z → |Work.Elliptic.Qang x k z| ≤ M := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.classC_mixed_sup_le_four
  set T : ℝ := C / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.StrongGlobal.Xn6 α x with hT
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact mul_nonneg (div_nonneg hCpos.le (Real.sqrt_nonneg _)) (Work.Spaces.HkNorm_nonneg α 6 x)
  refine ⟨3 * (Real.pi / 2) * T + 1, by nlinarith [hT0, Real.pi_pos], fun z hz => ?_⟩
  have hKθ : ∀ θ ∈ Work.Spaces.Iθ, |Work.Elliptic.Ktheta θ| ≤ 3 := by
    intro θ hθ
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [Real.pi_pos]⟩
    have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hc0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ.2⟩
    have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hcsq : Real.cos θ ^ 2 ≤ 1 := by nlinarith
    rw [Work.Elliptic.Ktheta, abs_of_nonneg (by positivity)]
    nlinarith
  have hKzero : Work.Elliptic.Ktheta 0 = 0 := by simp [Work.Elliptic.Ktheta]
  have hKpi : Work.Elliptic.Ktheta (Real.pi / 2) = 0 := by
    rw [Work.Elliptic.Ktheta, Real.sin_pi_div_two, Real.cos_pi_div_two]
    norm_num
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k x z θ‖ ≤ 3 * T := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun θ hθ => ?_
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      rw [hKzero, zero_mul, norm_zero]
      nlinarith [hT0, Real.pi_pos]
    · rcases eq_or_lt_of_le hθ.2 with h1 | h1
      · subst h1
        rw [hKpi, zero_mul, norm_zero]
        nlinarith [hT0, Real.pi_pos]
      · rw [Real.norm_eq_abs, abs_mul]
        have hmix : |Work.Spaces.DzIter k x z θ| ≤ T := by
          have hQd : (z, θ) ∈ Work.Construction.Qd := ⟨hz, h0, h1⟩
          have h := hC α hα hx k 0 (by omega) hQd
          simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DthIter_zero, hT] using h
        exact mul_le_mul (hKθ θ hθ) hmix (abs_nonneg _) (by norm_num)
  calc |Work.Elliptic.Qang x k z|
      = |∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k x z θ| := by
        rw [Work.Elliptic.Qang]
    _ = ‖∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k x z θ‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ ∫ θ in Work.Spaces.Iθ, ‖Work.Elliptic.Ktheta θ * Work.Spaces.DzIter k x z θ‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ θ in Work.Spaces.Iθ, (3 * T) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun θ => norm_nonneg _)
          (MeasureTheory.integrable_const _) hae
    _ = 3 * T * (Real.pi / 2) := by
        rw [Work.Elliptic.integral_Iθ_eq_interval, intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        ring
    _ ≤ 3 * (Real.pi / 2) * T + 1 := by
        nlinarith [hT0, Real.pi_pos]

/-! ## §2  Bounds for the radial jets of `L₁₂(x)` -/

/-- `L₁₂ x` is bounded on `[0,∞)`. -/
theorem L12f_bdd {α : ℝ} {x : Fn} (hx : Work.FTS.ClassC.ClassC α x) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ℝ, 0 ≤ z → |Work.Elliptic.L12 x z| ≤ D := by
  have hint := integrableOn_L12dens hx
  refine ⟨∫ s in Set.Ioi (0 : ℝ), |Work.Elliptic.L12dens x s|,
    MeasureTheory.integral_nonneg (fun _ => abs_nonneg _), fun z hz => ?_⟩
  have hsub : Set.Ioi z ≤ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    Filter.Eventually.of_forall fun s hs => Set.mem_Ioi.mpr (lt_of_le_of_lt hz hs)
  have hmono : (∫ s in Set.Ioi z, |Work.Elliptic.L12dens x s|)
      ≤ ∫ s in Set.Ioi (0 : ℝ), |Work.Elliptic.L12dens x s| :=
    MeasureTheory.setIntegral_mono_set hint.abs
      (Filter.Eventually.of_forall fun _ => abs_nonneg _) hsub
  calc |Work.Elliptic.L12 x z|
      = |∫ s in Set.Ioi z, Work.Elliptic.L12dens x s| := by rw [Work.Elliptic.L12]
    _ = ‖∫ s in Set.Ioi z, Work.Elliptic.L12dens x s‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ s in Set.Ioi z, ‖Work.Elliptic.L12dens x s‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ s in Set.Ioi z, |Work.Elliptic.L12dens x s| := by simp only [Real.norm_eq_abs]
    _ ≤ ∫ s in Set.Ioi (0 : ℝ), |Work.Elliptic.L12dens x s| := hmono

/-- Near the origin `L₁₂ x` is `O(z^{3/2})`, from the angular-moment bound on `Qang x 0`. -/
theorem L12f_small {α : ℝ} {x : Fn} (hx : Work.FTS.ClassC.ClassC α x) {C : ℝ} (hC : 0 < C)
    (hQ : ∀ z : ℝ, 0 < z → z < 1 → |Work.Elliptic.Qang x 0 z| ≤ C * z ^ ((3 : ℝ) / 2)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ℝ, 0 < z → z < 1 →
      |Work.Elliptic.L12 x z| ≤ D * z ^ ((3 : ℝ) / 2) := by
  have hint := integrableOn_L12dens hx
  refine ⟨C, hC.le, fun z hz hz1 => ?_⟩
  have hFTC := (Work.Elliptic.L12_values x hint (elliptic_L12_zero hx)).1 z hz.le
  rw [hFTC, abs_neg]
  have hz0 : (0 : ℝ) ≤ z := hz.le
  have hden : ∀ s ∈ Set.uIcc (0 : ℝ) z,
      |Work.Elliptic.L12dens x s| ≤ C * s ^ ((1 : ℝ) / 2) := by
    intro s hs
    rw [Set.uIcc_of_le hz0, Set.mem_Icc] at hs
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0, Work.Elliptic.L12dens_eq_Qang_div, div_zero, abs_zero,
        Real.zero_rpow (by norm_num : ((1 : ℝ) / 2) ≠ 0), mul_zero]
    · have hs1 : s < 1 := lt_of_le_of_lt hs.2 hz1
      have hsq : |Work.Elliptic.Qang x 0 s| ≤ C * s ^ ((3 : ℝ) / 2) := hQ s h0 hs1
      have hspow : s ^ ((3 : ℝ) / 2) = s ^ ((1 : ℝ) / 2) * s := by
        rw [show ((3 : ℝ) / 2) = (1 : ℝ) / 2 + 1 by norm_num, Real.rpow_add h0,
          Real.rpow_one, mul_comm]
      have hs1' : s ^ ((1 : ℝ) / 2) ≤ 1 := by
        have h := Real.rpow_le_rpow h0.le (le_of_lt hs1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        rwa [Real.one_rpow] at h
      rw [Work.Elliptic.L12dens_eq_Qang_div, abs_div, abs_of_pos h0, div_le_iff₀ h0]
      rw [hspow] at hsq
      simpa only [mul_assoc] using hsq
  have h1 : |∫ s in (0 : ℝ)..z, Work.Elliptic.L12dens x s|
      ≤ ∫ s in (0 : ℝ)..z, C * s ^ ((1 : ℝ) / 2) := by
    refine (intervalIntegral.abs_integral_le_integral_abs hz0).trans ?_
    refine intervalIntegral.integral_mono_on hz0 ?_ ?_ ?_
    · have hI : MeasureTheory.IntegrableOn (fun s => |Work.Elliptic.L12dens x s|)
          (Set.Ioi (0 : ℝ)) := hint.abs
      have hIcc : MeasureTheory.IntegrableOn (fun s => |Work.Elliptic.L12dens x s|)
          (Set.uIcc (0 : ℝ) z) := by
        rw [Set.uIcc_of_le hz0]
        exact (integrableOn_Icc_iff_integrableOn_Ioc (a := (0 : ℝ)) (b := z) (by simp)).mpr
          (hI.mono_set Set.Ioc_subset_Ioi_self)
      exact hIcc.intervalIntegrable
    · exact (intervalIntegral.intervalIntegrable_rpow (Or.inl (by norm_num : (0 : ℝ) ≤ 1 / 2))).const_mul C
    · intro s hs
      exact hden s (by rw [Set.uIcc_of_le hz0]; exact hs)
  have h2 : (∫ s in (0 : ℝ)..z, C * s ^ ((1 : ℝ) / 2))
      = C * ((2 / 3) * z ^ ((3 : ℝ) / 2)) := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2))]
    rw [show ((1 : ℝ) / 2 + 1) = (3 : ℝ) / 2 by norm_num]
    rw [Real.zero_rpow (by norm_num : ((3 : ℝ) / 2) ≠ 0)]
    ring
  have h3 : C * ((2 / 3) * z ^ ((3 : ℝ) / 2)) ≤ C * z ^ ((3 : ℝ) / 2) := by
    have hzr : 0 ≤ z ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hz0 _
    nlinarith [hC.le]
  calc |∫ s in (0 : ℝ)..z, Work.Elliptic.L12dens x s|
      ≤ ∫ s in (0 : ℝ)..z, C * s ^ ((1 : ℝ) / 2) := h1
    _ = C * ((2 / 3) * z ^ ((3 : ℝ) / 2)) := h2
    _ ≤ C * z ^ ((3 : ℝ) / 2) := h3

/-- The `D_z`-jets of `L₁₂ x` are the angular moments: `D_z^{k+1} (L₁₂ x) = -Qang x k`. -/
theorem DzdIter_L12f_eq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {x : Fn}
    (hx : Work.FTS.ClassC.ClassC α x) :
    ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.DzdIter (k + 1) (Work.Elliptic.L12 x) z = -Work.Elliptic.Qang x k z := by
  intro k hk z hz
  have hmem : Work.Spaces.HkMem α 4 x :=
    Work.FTS.OpenPkg.HkMem_mono_open hx.reg 4 (by norm_num) hx.mem
  exact (Work.FTS.OpenPkg.l12_open_bundle α x hα hα1 hx.reg hmem (elliptic_L12_zero hx)).1
    k hk z hz

/-- The `D_z`-jets of `L₁₂ x` are bounded on `(0,∞)`. -/
theorem DzdIter_L12f_bdd {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Fn}
    (hx : Work.FTS.ClassC.ClassC α x) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ m : ℕ, m ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter m (Work.Elliptic.L12 x) z| ≤ D := by
  obtain ⟨D₀, hD₀, hΛ⟩ := L12f_bdd hx
  obtain ⟨M0, hM0, hQ0⟩ := Qang_bdd hα hx (k := 0) (by omega)
  obtain ⟨M1, hM1, hQ1⟩ := Qang_bdd hα hx (k := 1) (by omega)
  obtain ⟨M2, hM2, hQ2⟩ := Qang_bdd hα hx (k := 2) (by omega)
  obtain ⟨M3, hM3, hQ3⟩ := Qang_bdd hα hx (k := 3) (by omega)
  refine ⟨D₀ + M0 + M1 + M2 + M3, by positivity, fun m hm z hz => ?_⟩
  interval_cases m
  · exact le_trans (hΛ z hz.le) (by linarith)
  · rw [DzdIter_L12f_eq hα.1 hα.2 hx 0 (by omega) z hz, abs_neg]
    exact le_trans (hQ0 z hz) (by linarith)
  · rw [DzdIter_L12f_eq hα.1 hα.2 hx 1 (by omega) z hz, abs_neg]
    exact le_trans (hQ1 z hz) (by linarith)
  · rw [DzdIter_L12f_eq hα.1 hα.2 hx 2 (by omega) z hz, abs_neg]
    exact le_trans (hQ2 z hz) (by linarith)
  · rw [DzdIter_L12f_eq hα.1 hα.2 hx 3 (by omega) z hz, abs_neg]
    exact le_trans (hQ3 z hz) (by linarith)

/-- The `D_z`-jets of `L₁₂ x` are `O(z^{3/2})` near the origin. -/
theorem DzdIter_L12f_small {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Fn}
    (hx : Work.FTS.ClassC.ClassC α x) {C : ℝ} (hC : 0 < C)
    (hQ : ∀ k : ℕ, k ≤ 3 → ∀ z : ℝ, 0 < z → z < 1 →
      |Work.Elliptic.Qang x k z| ≤ C * z ^ ((3 : ℝ) / 2)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ m : ℕ, m ≤ 4 → ∀ z : ℝ, 0 < z → z < 1 →
      |Work.Elliptic.DzdIter m (Work.Elliptic.L12 x) z| ≤ D * z ^ ((3 : ℝ) / 2) := by
  obtain ⟨D₀, hD₀, hΛ⟩ := L12f_small hx hC (hQ 0 (by omega))
  refine ⟨D₀ + C + C + C, by positivity, fun m hm z hz hz1 => ?_⟩
  have hzr : 0 ≤ z ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hz.le _
  interval_cases m
  · exact le_trans (hΛ z hz hz1) (by nlinarith)
  · rw [DzdIter_L12f_eq hα.1 hα.2 hx 0 (by omega) z hz, abs_neg]
    exact le_trans (hQ 0 (by omega) z hz hz1) (by nlinarith)
  · rw [DzdIter_L12f_eq hα.1 hα.2 hx 1 (by omega) z hz, abs_neg]
    exact le_trans (hQ 1 (by omega) z hz hz1) (by nlinarith)
  · rw [DzdIter_L12f_eq hα.1 hα.2 hx 2 (by omega) z hz, abs_neg]
    exact le_trans (hQ 2 (by omega) z hz hz1) (by nlinarith)
  · rw [DzdIter_L12f_eq hα.1 hα.2 hx 3 (by omega) z hz, abs_neg]
    exact le_trans (hQ 3 (by omega) z hz hz1) (by nlinarith)

/-! ## §3  Bounds for the radial jets of `ampB` -/

/-- The `D_z`-jets of `ampB α = 2z²/(1+z)³` are bounded by `C z²/(1+z)³`. -/
theorem DzdIter_ampB_bdd (α : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 ≤ z →
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampB α) z|
        ≤ D * z ^ 2 / (1 + z) ^ 3 := by
  obtain ⟨C, hC, hCb⟩ := Work.FTS.StrongEps.ClassCRHS.DzBoundR0
  refine ⟨C, hC.le, fun b hb z hz => ?_⟩
  have hfun : Work.FTS.CoercivityFix.Transfer.ampB α
      = Work.FTS.StrongEps.ClassCRHS.SR0 := by
    funext w
    simp only [Work.FTS.CoercivityFix.Transfer.ampB, Work.FTS.StrongEps.ClassCRHS.SR0]
  rw [hfun]
  exact hCb b hb z hz

end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.N0DiffClassC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The `ClassC`-level auxiliary facts underlying `N0DiffClassC`

The target `N0DiffClassC` is the `ClassC`-analogue of
`Work.FTS.GalFields.RHS.sharp_N0_diff`: for `W₁, W₂` of class `C` (`ClassC α`), the
`N₀`-difference `N₀ α (F_*+W₁) W₁ − N₀ α (F_*+W₂) W₂` is `ℋ⁴`-honest and `C^∞` on the open
quadrant, and its `ℋ⁴`-norm is bounded by
`K(α)·(1 + |W₁|_{ℋ⁵} + |W₂|_{ℋ⁵})·|W₁−W₂|_{ℋ⁵}` — a *linear-in-the-difference* bound.

The construction is in three layers:

1. **the telescoping identity** (`Work.FTS.StrongEps.EpsRLX.N0SubEqRsum`): on the open quadrant
   the difference equals the nine-piece sum `Rsum α W₁ W₂ (W₁−W₂)` of
   `GalFields/RHS/sharpN0_defs.lean`;
2. **the `ℋ⁴`-bound for the nine pieces** (`Work.FTS.StrongEps.EpsRLX.RsumClassC`), which is
   where the estimate lives (products, `c2m`, the fixed atoms `F_*`, `D_θF_*`, `D_zF_*`,
   `L₁₂F_*` and the linearity of `L₁₂`);
3. **the transfer of smoothness/honesty from `Rsum` to the difference** plus the `L₁₂`-zero-mode
   clause, which is what this file supplies below (`smoothOpen_of_eqOn_Q0`, `hkMem_sub_of`,
   `hkMem_N0_of_classC`, `smoothOpen_N0_of_classC`, `abs_L12_N0_sub_le`, `hkSq_N0_diff_eq`,
   `hkMem_N0_diff_of_Rsum`).  The two `Hᵏ`-transfers along the pointwise identity `D = Rsum` use
   `Work.FTS.EllipticEst.HkSq_congr_open` and `…Cert.GbarSin.HkMem_congr_Q0`.

The constants are allowed to depend on `α` (the pieces carry `α^{-1}`, `α^{-1/2}` and `α^{+1}`
factors), which is why `∃ K` sits *inside* the `∀ α ∈ Ioc 0 1` in the statement. -/


/-- **`HkMem α k` is closed under subtraction** (pointwise, in the open class). -/
theorem hkMem_sub_of {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ - g z θ) := by
  have hgsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => -g z θ) :=
    Work.FTS.GalFields.RHS.smoothOpen_neg' hg
  have hadd : Work.Spaces.HkMem α k (fun z θ => f z θ + -g z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hf hgsm hmf
      (Work.FTS.StrongEps.ClassCRHS.mem_neg hmg)
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k hadd (fun z hz θ hθ => ?_)
  ring

/-- **The `N₀`-block of a class-`C` datum is `ℋ⁴`-honest.**

`HkMemXnN0` is stated with the two *size* hypotheses `Xn α w ≤ C₀ α²` and `HkNorm α 6 w ≤ B`
(the constant `K` depends on them); here they are met by taking `C₀ := Xn α W / α²` and
`B := HkNorm α 6 W`, both of which are legitimate because the right-hand sides are exactly the
available norms. -/
theorem hkMem_N0_of_classC {α : ℝ} (hαIoc : α ∈ Set.Ioc 0 1)
    {W : Work.FTS.Galerkin.Fn} (hW : Work.FTS.ClassC.ClassC α W) :
    Work.Spaces.HkMem α 4 (Work.Construction.N0 α (Work.Construction.Ftot α W) W) := by
  obtain ⟨K, -, hN⟩ := Work.FTS.StrongEps.ClassCRHS.HkMemXnN0 (α := α) hαIoc
    (C₀ := Work.FTS.Nonlin.Xn α W / α ^ 2) (B := Work.Spaces.HkNorm α 6 W)
  refine (hN hW ?_ le_rfl).1
  exact le_of_eq (div_mul_cancel₀ _ (pow_ne_zero 2 hαIoc.1.ne')).symm

/-- **Open-quadrant smoothness of the `N₀`-block of a class-`C` datum** (from the smoothness of
`W` and of the radial function `z ↦ L₁₂(W)(z)`, which the class supplies). -/
theorem smoothOpen_N0_of_classC {α : ℝ} (hα : 0 < α)
    {W : Work.FTS.Galerkin.Fn} (hW : Work.FTS.ClassC.ClassC α W) :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.N0 α (Work.Construction.Ftot α W) W) :=
  Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0 hα hW.reg
    (Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_aux hα hW)

/-- **The `L₁₂`-zero-mode of the `N₀`-difference is controlled by the `ℋ⁴`-norm of that
difference.**  This is the `L₁₂`-clause of `N0DiffClassC`, in the factored form which composes
with the `ℋ⁴`-bound for the difference.

Route: `L₁₂` is additive on pointwise differences of `C^∞`-on-the-open-quadrant, `ℋ⁴`-honest
profiles (`Work.FTS.GalFields.RHS.L12_sub_eq_of_smoothOpen`), and its zero mode at `z = 0` is
controlled by the `ℋ⁴`-norm (`Work.FTS.GalBasis.cc.abs_L12_le_HkNorm`). -/
theorem abs_L12_N0_sub_le {α : ℝ} (hαIoc : α ∈ Set.Ioc 0 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
        - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0|
      ≤ C * Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
            - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ) := by
  obtain ⟨C, hC, hspec⟩ := Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
  refine ⟨C, hC, ?_⟩
  intro W₁ W₂ hW₁ hW₂
  have hα : 0 < α := hαIoc.1
  have hsm₁ := smoothOpen_N0_of_classC hα hW₁
  have hsm₂ := smoothOpen_N0_of_classC hα hW₂
  have hm₁ := hkMem_N0_of_classC hαIoc hW₁
  have hm₂ := hkMem_N0_of_classC hαIoc hW₂
  have hmemD : Work.Spaces.HkMem α 4 (fun z θ =>
      Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
        - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ) :=
    hkMem_sub_of hsm₁ hsm₂ hm₁ hm₂
  have hlin := Work.FTS.GalFields.RHS.L12_sub_eq_of_smoothOpen hsm₁ hsm₂ hm₁ hm₂ 0 (le_refl 0)
  rw [hlin]
  exact hspec α _ hmemD

/-- **The `ℋ⁴`-energy of the `N₀`-difference is that of the nine-piece sum** (the a.e.-in-`z`
transfer of `Work.FTS.StrongEps.EpsRLX.N0SubEqRsum` across the null set `{z = 0}`). -/
theorem hkSq_N0_diff_eq {α : ℝ} (hα : 0 < α) {W₁ W₂ : Work.FTS.Galerkin.Fn}
    (hsm₁ : Work.FTS.EllipticEst.SmoothOpen W₁)
    (hsm₂ : Work.FTS.EllipticEst.SmoothOpen W₂)
    (hm₁ : Work.Spaces.HkMem α 4 W₁) (hm₂ : Work.Spaces.HkMem α 4 W₂) :
    Work.Spaces.HkSq α 4 (fun z θ =>
        Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
          - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ)
      = Work.Spaces.HkSq α 4 (Work.FTS.GalFields.RHS.Rsum α W₁ W₂
          (fun z θ => W₁ z θ - W₂ z θ)) := by
  refine Work.FTS.EllipticEst.HkSq_congr_open α 4 (fun z θ hz hθ0 hθ1 => ?_)
  exact Work.FTS.StrongEps.EpsRLX.N0SubEqRsum hα hsm₁ hsm₂ hm₁ hm₂ z θ ⟨hz, hθ0, hθ1⟩

/-- **The `ℋ⁴`-honesty of the `N₀`-difference**, transported from the nine-piece sum. -/
theorem hkMem_N0_diff_of_Rsum {α : ℝ} (hα : 0 < α) {W₁ W₂ : Work.FTS.Galerkin.Fn}
    (hsm₁ : Work.FTS.EllipticEst.SmoothOpen W₁)
    (hsm₂ : Work.FTS.EllipticEst.SmoothOpen W₂)
    (hm₁ : Work.Spaces.HkMem α 4 W₁) (hm₂ : Work.Spaces.HkMem α 4 W₂)
    (hRmem : Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Rsum α W₁ W₂
      (fun z θ => W₁ z θ - W₂ z θ))) :
    Work.Spaces.HkMem α 4 (fun z θ =>
        Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
          - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ) := by
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hRmem (fun z hz θ hθ => ?_)
  exact (Work.FTS.StrongEps.EpsRLX.N0SubEqRsum hα hsm₁ hsm₂ hm₁ hm₂ z θ
    ⟨hz, hθ.1, hθ.2⟩).symm

/-- **The `ℋ⁴`-norm of the `N₀`-difference is that of the nine-piece sum.** -/
theorem Xn_N0_diff_eq {α : ℝ} (hα : 0 < α) {W₁ W₂ : Work.FTS.Galerkin.Fn}
    (hsm₁ : Work.FTS.EllipticEst.SmoothOpen W₁)
    (hsm₂ : Work.FTS.EllipticEst.SmoothOpen W₂)
    (hm₁ : Work.Spaces.HkMem α 4 W₁) (hm₂ : Work.Spaces.HkMem α 4 W₂) :
    Work.FTS.Nonlin.Xn α (fun z θ =>
        Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
          - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ)
      = Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Rsum α W₁ W₂
          (fun z θ => W₁ z θ - W₂ z θ)) := by
  show Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ =>
        Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
          - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ))
      = Real.sqrt (Work.Spaces.HkSq α 4 (Work.FTS.GalFields.RHS.Rsum α W₁ W₂
          (fun z θ => W₁ z θ - W₂ z θ)))
  rw [hkSq_N0_diff_eq hα hsm₁ hsm₂ hm₁ hm₂]

theorem N0DiffClassC :
    ∀ α ∈ Set.Ioc 0 1, ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
          Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
            - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ) ∧
      Work.Spaces.HkMem α 4 (fun z θ =>
          Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
            - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
            - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ)
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) ∧
      |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
          - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0|
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
  intro α hαIoc
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  -- the two ingredients: the `ℋ⁴`-bound for the nine pieces, and the `L₁₂`-clause
  obtain ⟨K₁, hK₁, hRsum⟩ := Work.FTS.StrongEps.EpsRLX.RsumClassC (α := α) hα hα1
  obtain ⟨CL, hCL, hL12⟩ := abs_L12_N0_sub_le (α := α) hαIoc
  have hprod : 0 < CL * K₁ := mul_pos hCL hK₁
  refine ⟨K₁ + CL * K₁ + 1, by linarith, ?_⟩
  intro W₁ W₂ hW₁ hW₂
  have hsm₁ : Work.FTS.EllipticEst.SmoothOpen W₁ := hW₁.reg
  have hsm₂ : Work.FTS.EllipticEst.SmoothOpen W₂ := hW₂.reg
  have hm₁ : Work.Spaces.HkMem α 4 W₁ :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm₁ 4 (by norm_num) hW₁.mem
  have hm₂ : Work.Spaces.HkMem α 4 W₂ :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm₂ 4 (by norm_num) hW₂.mem
  obtain ⟨hRmem, hRxn⟩ := hRsum hW₁ hW₂
  -- the pairwise abbreviations
  have hTnn : 0 ≤ (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
      * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
    refine mul_nonneg (by linarith [Work.Spaces.HkNorm_nonneg α 5 W₁,
      Work.Spaces.HkNorm_nonneg α 5 W₂]) ?_
    exact Work.Spaces.HkNorm_nonneg α 5 _
  have hleK : K₁ ≤ K₁ + CL * K₁ + 1 := by linarith
  have hleK' : CL * K₁ ≤ K₁ + CL * K₁ + 1 := by linarith
  have hxnD := Xn_N0_diff_eq (α := α) hα hsm₁ hsm₂ hm₁ hm₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `SmoothOpen` of the difference
    exact Work.FTS.EllipticEst.smoothOpen_sub (smoothOpen_N0_of_classC hα hW₁)
      (smoothOpen_N0_of_classC hα hW₂)
  · -- `ℋ⁴`-honesty of the difference
    exact hkMem_N0_diff_of_Rsum hα hsm₁ hsm₂ hm₁ hm₂ hRmem
  · -- the `ℋ⁴`-bound for the difference
    rw [hxnD]
    calc Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Rsum α W₁ W₂
            (fun z θ => W₁ z θ - W₂ z θ))
        ≤ K₁ * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := hRxn
      _ = K₁ * ((1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) := by ring
      _ ≤ (K₁ + CL * K₁ + 1) * ((1 + Work.FTS.GalFields.Xn5 α W₁
            + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) :=
          mul_le_mul_of_nonneg_right hleK hTnn
      _ = (K₁ + CL * K₁ + 1) * (1 + Work.FTS.GalFields.Xn5 α W₁
            + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by ring
  · -- the `L₁₂`-zero-mode clause
    calc |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
          - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0|
        ≤ CL * Work.FTS.Nonlin.Xn α (fun z θ =>
            Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
              - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ) :=
          hL12 hW₁ hW₂
      _ = CL * Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Rsum α W₁ W₂
            (fun z θ => W₁ z θ - W₂ z θ)) := by rw [hxnD]
      _ ≤ CL * (K₁ * ((1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ))) :=
          mul_le_mul_of_nonneg_left
            (le_trans hRxn (le_of_eq (by ring))) hCL.le
      _ = CL * K₁ * ((1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) := by ring
      _ ≤ (K₁ + CL * K₁ + 1) * ((1 + Work.FTS.GalFields.Xn5 α W₁
            + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) :=
          mul_le_mul_of_nonneg_right hleK' hTnn
      _ = (K₁ + CL * K₁ + 1) * (1 + Work.FTS.GalFields.Xn5 α W₁
            + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by ring

end Work.FTS.StrongEps.EpsRLX
end
