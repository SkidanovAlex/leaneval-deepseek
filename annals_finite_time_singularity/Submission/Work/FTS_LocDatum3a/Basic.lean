import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.FireFix.Prime.PhysVortHolderSlice
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.Physical.Omega
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.RegPkgGal.R7d.support_strip
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.LogInt
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Recur
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS.StrongEps.EpsODE
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leafSlotSliceIntegrable
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3DataFinal
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_FinalLeaves.Min.SliceTheta
import Submission.Work.FTS_LocDatum3a.Defs
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.EpsEngine.HkSq_JepsPz_le8Bump =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


namespace Work.FTS.EpsEngine

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- **The correction profile is uniformly bounded in `ℋᵏ`, up to order `8`.**  There is a single
constant `B` with `‖bump‖_{ℋᵏ} ≤ B` for every `α ∈ (0,1]` and every `k ≤ 8`.  This is
`Work.FTS.StrongEps.PZeroAux.exists_HkNorm_bump_le` (`k ≤ 6`, same proof) with the maximum of
the integrand taken at `k = 8` instead of `k = 6`. -/
theorem exists_HkNorm_bump_le8 :
    ∃ B : ℝ, 0 < B ∧ ∀ α ∈ Set.Ioc 0 1, ∀ k : ℕ, k ≤ 8 →
      Work.Spaces.HkNorm α k Work.FTS.StrongEps.bump ≤ B := by
  obtain ⟨M, hMnn, hM⟩ := Work.FTS.StrongEps.exists_bound_HkIntegrand_bump 1 8
  refine ⟨max 1 (Real.sqrt (M * (Real.pi / 2) * (1 + 1))), lt_max_of_lt_left one_pos, ?_⟩
  intro α hα k hk
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hbound : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k Work.FTS.StrongEps.bump z θ ≤ M := by
    intro z hz θ hθ
    refine le_trans (le_trans ?_ (Work.FTS.OpenPkg.HkIntegrand_mono_le 1 hk _ z θ)) (hM z θ)
    exact Work.FTS.StrongEps.PZeroAux.HkIntegrand_gam_mono hα0 hα1 k _ hθ
  have hfg : ∀ z θ : ℝ, 1 < z → Work.FTS.StrongEps.bump z θ = 0 := by
    intro z θ hz
    rw [Work.FTS.StrongEps.bump_eq_zero_iff]
    exact Or.inr (Or.inl (le_of_lt hz))
  have hsq := Work.Spaces.HkSq_le_of_bound α k Work.FTS.StrongEps.bump 1 M
    (by norm_num) hMnn hfg hbound
  rw [Work.Spaces.HkNorm]
  exact le_trans (Real.sqrt_le_sqrt hsq) (le_max_right _ _)

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.PressureOn.CurlGrad.vorticity_gradient_integral_eq_zero =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `∫ ⟪ω, ∇ψ⟫ = 0` for a curl and a compactly supported `C¹` test function

`Work.FTS.PressureOn.CurlGrad.vorticity_gradient_integral_eq_zero`: for `u : ℝ³ → ℝ³` of class `C¹`
and `ψ : ℝ³ → ℝ` of class `C¹` with compact support,

  `∫ x, ⟪vorticity u x, gradient ψ x⟫ = 0`.

This is the statement that `div (curl u) = 0` in the sense of distributions: it is what turns the
distributional Poisson equation of the pressure reconstruction into an identity against test
functions.

## Route

* **Smooth case** (`integral_vorticity_gradient_eq_zero_of_contDiff_two`): for `φ ∈ C²` with compact
  support, the field `X := u × ∇φ` is `C¹` with compact support, so `∫ div X = 0`
  (`Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt`); and pointwise
  `div X = ⟪curl u, ∇φ⟫ - ⟪u, curl ∇φ⟫ = ⟪curl u, ∇φ⟫`, the second term vanishing because the curl
  of a gradient is zero (`div_crossVec_eq`, `vorticity_gradient_eq_zero`).
* **General `ψ ∈ C¹`**: approximate by convolution with the bump family `bumpSeq ρ n`
  (`HasCompactSupport.contDiff_convolution_left`), apply the smooth case to each approximation and
  pass to the limit (`tendsto_integral_inner_fderiv_convolution`).
-/

open FiniteTimeSingularity MeasureTheory Filter
open scoped Convolution Gradient Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.CurlGrad

open Work.FTS.PressureOn (R3 crossVec)

/-! ## The smooth case -/

/-- **The smooth case**: for a `C²` compactly supported test function `φ`, `∫ ⟪curl u, ∇φ⟫ = 0`. -/
theorem integral_vorticity_gradient_eq_zero_of_contDiff_two {u : R3 → R3} (hu : ContDiff ℝ 1 u)
    {φ : R3 → ℝ} (hφ : ContDiff ℝ 2 φ) (hφcs : HasCompactSupport φ) :
    ∫ x, inner ℝ (vorticity u x) (gradient φ x) = 0 := by
  -- regularity of the field `X := fun x => u x × ∇φ x`
  have hreg := gradient_crossVec_bundle hu hφ hφcs
  obtain ⟨hgrad, hXcont, hXdiff, hXcs, hXint⟩ := hreg
  -- the pointwise identity `div X = ⟪curl u, ∇φ⟫`
  have hpoint : ∀ x, div (fun y => crossVec (u y) (gradient φ y)) x
      = inner ℝ (vorticity u x) (gradient φ x) := by
    intro x
    rw [div_crossVec_eq ((hu.differentiable_one x).hasFDerivAt) (hgrad x)]
    have hcurl : vorticity (gradient φ) x = 0 :=
      vorticity_gradient_eq_zero (x := x) hφ.contDiffAt
    rw [hcurl, inner_zero_right, sub_zero]
  rw [show (∫ x, inner ℝ (vorticity u x) (gradient φ x))
      = ∫ x, div (fun y => crossVec (u y) (gradient φ y)) x from by
        congr 1 with x
        exact (hpoint x).symm]
  exact integral_div_eq_zero_of_hasFDerivAt _ hXcs hXcont hXdiff hXint

/-! ## The bump family -/

/-- A sequence of bump functions with `rOut → 0`: `bumpSeq ρ n` has the radii of `ρ` divided by
`n + 1`. -/
noncomputable def bumpSeq (ρ : ContDiffBump (0 : R3)) (n : ℕ) : ContDiffBump (0 : R3) :=
  ⟨ρ.rIn / ((n : ℝ) + 1), ρ.rOut / ((n : ℝ) + 1), div_pos ρ.rIn_pos (by positivity),
    div_lt_div_of_pos_right ρ.rIn_lt_rOut (by positivity)⟩

@[simp] theorem bumpSeq_rIn (ρ : ContDiffBump (0 : R3)) (n : ℕ) :
    (bumpSeq ρ n).rIn = ρ.rIn / ((n : ℝ) + 1) := rfl

@[simp] theorem bumpSeq_rOut (ρ : ContDiffBump (0 : R3)) (n : ℕ) :
    (bumpSeq ρ n).rOut = ρ.rOut / ((n : ℝ) + 1) := rfl

/-- The outer radii of `bumpSeq ρ n` tend to `0`. -/
theorem tendsto_rOut_bumpSeq (ρ : ContDiffBump (0 : R3)) :
    Tendsto (fun n : ℕ => (bumpSeq ρ n).rOut) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => ρ.rOut / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) ρ.rOut).comp
      (tendsto_add_atTop_nat 1)
    convert h using 1
    ext n
    simp [Nat.cast_add, Nat.cast_one]
  simpa only [bumpSeq_rOut] using h0

/-! ## The general case -/

/-- **The main statement**: `∫ ⟪vorticity u, ∇ψ⟫ = 0` for `u ∈ C¹` and `ψ ∈ C¹` compactly
supported. -/
theorem vorticity_gradient_integral_eq_zero {u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : ContDiff ℝ 1 u) (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ) :
    ∫ x, inner ℝ (FiniteTimeSingularity.vorticity u x) (gradient ψ x) = 0 := by
  -- step 1: the integrand is `dψ(ω)`
  have h1 : (∫ x, inner ℝ (vorticity u x) (gradient ψ x))
      = ∫ x, fderiv ℝ ψ x (vorticity u x) := by
    congr 1 with x
    rw [real_inner_comm, inner_gradient_left]
  rw [h1]
  -- step 2: approximate `ψ` by smooth compactly supported functions
  let ρ : ContDiffBump (0 : R3) := default
  have hφ : Tendsto (fun n : ℕ => (bumpSeq ρ n).rOut) atTop (𝓝 0) := tendsto_rOut_bumpSeq ρ
  have hlim := tendsto_integral_inner_fderiv_convolution (ω := vorticity u)
    (Work.FTS.BSIdent.Liouville.continuous_vorticity_of_contDiff hu) hψ hψcs
    (φ := fun n => bumpSeq ρ n) hφ
  -- step 3: each approximating integral vanishes by the smooth case
  have hsmooth : ∀ n : ℕ,
      (∫ x, fderiv ℝ (MeasureTheory.convolution ((bumpSeq ρ n).normed volume) ψ
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (vorticity u x)) = 0 := by
    intro n
    set ψn : R3 → ℝ := MeasureTheory.convolution ((bumpSeq ρ n).normed volume) ψ
      (ContinuousLinearMap.lsmul ℝ ℝ) volume with hψndef
    have hsm : ContDiff ℝ 2 ψn :=
      ((bumpSeq ρ n).hasCompactSupport_normed).contDiff_convolution_left
        (L := ContinuousLinearMap.lsmul ℝ ℝ) (n := (2 : ℕ∞))
        (bumpSeq ρ n).contDiff_normed hψ.continuous.locallyIntegrable
    have hcs : HasCompactSupport ψn :=
      ((bumpSeq ρ n).hasCompactSupport_normed).convolution
        (L := ContinuousLinearMap.lsmul ℝ ℝ) hψcs
    have h0 := integral_vorticity_gradient_eq_zero_of_contDiff_two hu hsm hcs
    rw [show (∫ x, fderiv ℝ ψn x (vorticity u x))
        = ∫ x, inner ℝ (vorticity u x) (gradient ψn x) from by
          congr 1 with x
          rw [real_inner_comm, inner_gradient_left]]
    exact h0
  -- step 4: pass to the limit
  have hzero : (∫ x, fderiv ℝ ψ x (vorticity u x)) = 0 :=
    tendsto_nhds_unique hlim
      (Filter.Tendsto.congr' (Eventually.of_forall fun n => (hsmooth n).symm)
        tendsto_const_nhds)
  exact hzero

end Work.FTS.PressureOn.CurlGrad
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Transfer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JepsTransfer/Transfer.lean` — the weighted transfer estimate for the mollifier

This is the assembly of the log-coordinate transfer estimate: for a weight `w` whose log
pull-back `logW w` is nonnegative, measurable and log-Lipschitz in both directions, and two
profiles `g₁`, `g₂` smooth on the open quadrant,

  `|∫_Quad w · (J_ε g₁) · g₂ − ∫_Quad w · g₁ · (J_ε g₂)| ≤ C ε √(∫_Quad w g₁²) √(∫_Quad w g₂²)`

— with **no derivative loss**.  The analytic content (the even convolution on the log plane)
is isolated in the hypothesis `LogPlaneTransfer`; the work here is the two log-coordinate
substitutions (`integral_quad_log_subst`), which turn each of the four quadrant integrals into
its plane counterpart, and the identification `logPull (J_ε g) = ∫_p Jker ρ ε p · logPull g (·−p)`.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The log-plane transfer inequality**, abstracted: this is exactly the conclusion of
`JepsTransfer.logPair_conv_transfer_iter` with its hypotheses bound. -/
def LogPlaneTransfer : Prop :=
  ∀ {k : ℝ × ℝ → ℝ} {ε Cw : ℝ}, 0 < ε → ε ≤ 1 → 0 ≤ Cw →
    Continuous k → (∀ p : ℝ × ℝ, 0 ≤ k p) → (∫ p : ℝ × ℝ, k p = 1) →
    (∀ p : ℝ × ℝ, k p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε) →
    (∀ p : ℝ × ℝ, k (-p) = k p) →
    MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * (|p.1| + |p.2|)) →
    ∀ {Q : ℝ × ℝ → ℝ}, (∀ y : ℝ × ℝ, 0 ≤ Q y) → Measurable Q →
    (∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y) →
    (∀ y p : ℝ × ℝ, Q y ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q (y + p)) →
    ∀ {G₁ G₂ : ℝ × ℝ → ℝ}, Measurable G₁ → Measurable G₂ →
    (∀ y : ℝ × ℝ, MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * G₁ (y - p))) →
    (∀ y : ℝ × ℝ, MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * G₂ (y - p))) →
    MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2) →
    MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₂ y ^ 2) →
    |(∫ s, ∫ ζ, Q (s, ζ) * (∫ p : ℝ × ℝ, k p * G₁ ((s, ζ) - p)) * G₂ (s, ζ))
      - (∫ s, ∫ ζ, Q (s, ζ) * G₁ (s, ζ) * (∫ p : ℝ × ℝ, k p * G₂ ((s, ζ) - p)))|
      ≤ 100 * (Cw + 1) * Real.exp (4 * Cw) * ε
          * Real.sqrt (∫ s, ∫ ζ, Q (s, ζ) * G₁ (s, ζ) ^ 2)
          * Real.sqrt (∫ s, ∫ ζ, Q (s, ζ) * G₂ (s, ζ) ^ 2)

/-- The mollifier as a convolution, in the form matching `logPull`. -/
theorem logPull_Jeps_apply (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (g : Fn) (y : ℝ × ℝ) :
    Work.FTS.StrongEps.Jeps ρ ε g (Real.exp y.1) (Real.arctan (Real.exp y.2))
      = ∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g (y - p) := by
  rw [← Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_Jeps_eq ρ ε g y]
  rfl

/-- **The weighted transfer estimate in the quadrant form.** -/
theorem pairing_transfer {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hρs : ∀ p : ℝ × ℝ, ρ (-p) = ρ p) (hLT : LogPlaneTransfer)
    {w : ℝ → ℝ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hw0 : ∀ y : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
    (hwm : Measurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w))
    (hwsh : ∀ y p : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)
      ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
    (hwsh' : ∀ y p : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p))
    {ε : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    {g₁ g₂ : Fn} (hs1 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g₁)
        Work.FTS.EllipticEst.Q0)
    (hs2 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g₂) Work.FTS.EllipticEst.Q0)
    (hJ1 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => w z θ * Work.FTS.StrongEps.Jeps ρ ε g₁ z θ * g₂ z θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))))
    (hJ2 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => w z θ * g₁ z θ * Work.FTS.StrongEps.Jeps ρ ε g₂ z θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))))
    (hG1 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => w z θ * g₁ z θ ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))))
    (hG2 : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => w z θ * g₂ z θ ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))))
    (hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ
      => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ y) ^ 2))
    (hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ
      => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ y) ^ 2)) :
    |(∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        w z θ * Work.FTS.StrongEps.Jeps ρ ε g₁ z θ * g₂ z θ)
      - (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          w z θ * g₁ z θ * Work.FTS.StrongEps.Jeps ρ ε g₂ z θ)|
      ≤ 100 * (Cw + 1) * Real.exp (4 * Cw) * ε
          * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ * g₁ z θ ^ 2)
          * Real.sqrt (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ * g₂ z θ ^ 2) := by
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := hε.2
  have hc1 : Continuous (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁) :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hs1
  have hc2 : Continuous (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂) :=
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.logPull_continuous hs2
  -- the abstract log-plane transfer
  have hT := hLT hε0 hε1 hCw (Work.FTS.StrongEps.Jker_continuous hρ.moll ε)
    (Work.FTS.StrongEps.HkSqAux.Jker_nonneg ρ hρ.moll ε)
    (Work.FTS.StrongEps.Jker_integral_eq_one ρ hρ.moll hε0)
    (fun p hp => Work.FTS.StrongEps.HkSqAux.Jker_support_abs hρ.moll hε0 hp)
    (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.jker_even hρs ε)
    (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.jker_momint hρ.moll hε0)
    hw0 hwm hwsh hwsh' hc1.measurable hc2.measurable
    (fun y => Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.jker_conv_integrable
      hρ.moll hε0 hc1 y)
    (fun y => Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.jker_conv_integrable
      hρ.moll hε0 hc2 y) hI1 hI2
  -- the four conversions
  have hm1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        w z θ * Work.FTS.StrongEps.Jeps ρ ε g₁ z θ * g₂ z θ)
      = ∫ s, ∫ ζ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ ((s, ζ) - p))
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ (s, ζ) := by
    rw [Work.FTS.CoercivityStep.Base.wip_eq_Ioi_Ioo]
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst hJ1]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun s => ?_)
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun ζ => ?_)
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply,
      logPull_Jeps_apply ρ ε g₁ (s, ζ)]
    ring
  have hm2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        w z θ * g₁ z θ * Work.FTS.StrongEps.Jeps ρ ε g₂ z θ)
      = ∫ s, ∫ ζ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ (s, ζ)
          * (∫ p : ℝ × ℝ, Work.FTS.StrongEps.Jker ρ ε p
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ ((s, ζ) - p)) := by
    rw [Work.FTS.CoercivityStep.Base.wip_eq_Ioi_Ioo]
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst hJ2]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun s => ?_)
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun ζ => ?_)
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply,
      logPull_Jeps_apply ρ ε g₂ (s, ζ)]
    ring
  have hq1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ * g₁ z θ ^ 2)
      = ∫ s, ∫ ζ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₁ (s, ζ)) ^ 2 := by
    rw [Work.FTS.CoercivityStep.Base.wip_eq_Ioi_Ioo]
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst hG1]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun s => ?_)
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun ζ => ?_)
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply]
    ring
  have hq2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, w z θ * g₂ z θ ^ 2)
      = ∫ s, ∫ ζ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (s, ζ)
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g₂ (s, ζ)) ^ 2 := by
    rw [Work.FTS.CoercivityStep.Base.wip_eq_Ioi_Ioo]
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.integral_quad_log_subst hG2]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun s => ?_)
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun ζ => ?_)
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply]
    ring
  rw [hm1, hm2, hq1, hq2]
  exact hT

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4Slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TransferDeriv/IP4Slots.lean` — the slot level of the derivative-priced transfer

* The diagonal slot factor `√(wip w (slot) (slot))` is bounded by the `ℋ^m`-norm of the datum,
  through the composed-slot identity `mixed_comp` and the single-slot Cauchy–Schwarz
  `slotPairing_abs_le_gen` (`sqrt_wip_comp_le`, `sqrt_wip_cut_le`).
* The composed slot of a leaf weight is dominated by the `ℋ^m`-integrand (`dom_comp_slot`,
  `dom_comp_slot_Jeps`).
* The six integrability certificates of `SlotIntegrableDeriv` at the cuts of the shifted slots
  (`slotIntegrableDeriv_cut`), discharged from the above through `integrable_slot_of_dom`.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The diagonal slot factor is bounded by the `ℋ^m`-norm -/

/-- **The diagonal factor of a slot transfer.**  For a leaf weight of the angular slot `a + a₀` and
a slot of order at most `m`, the flat pairing of the composed slot of `f` is at most `|f|_{ℋ^m}²`,
so its square root is at most `|f|_{ℋ^m}`.

The slot `D_z^bD_θ^a(D_z^{b₀}D_θ^{a₀}f)` of `f` is rewritten as the composed slot
`D_z^{b+b₀}D_θ^{a+a₀}f` on the open quadrant (`mixed_comp`), where the single-slot Cauchy–Schwarz
applies. -/
theorem sqrt_wip_comp_le {α : ℝ} (hα : 0 < α) {f : Fn}
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) {m a b a₀ b₀ : ℕ}
    (hab : (a + a₀) + (b + b₀) ≤ m) {w : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α (a + a₀) w) (hmf : Work.Spaces.HkMem α m f) :
    Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f)))
      ≤ Work.Spaces.HkNorm α m f := by
  have hcomp : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f) z θ
        = Work.Spaces.mixed (b + b₀) (a + a₀) f z θ :=
    fun z θ hh => mixed_comp hfs b₀ a₀ b a hh
  have hwip : Work.Coercivity.wip w (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f))
      = Work.FTS.TransportS.slotPairing w (a + a₀) (b + b₀) f f := by
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.slotPairing_eq_wip]
    exact Work.FTS.StrongEps.EpsE4Thr.wip_congr_Q0_both hcomp hcomp
  rw [hwip]
  refine Real.sqrt_le_iff.mpr ⟨Work.Spaces.HkNorm_nonneg α m f, ?_⟩
  have hcs := Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.slotPairing_abs_le_gen
    hα (a := a + a₀) (b := b + b₀) (n := m) (by omega) hleaf hfs hfs hmf hmf
  have hsq : Work.FTS.TransportS.slotPairing w (a + a₀) (b + b₀) f f
      ≤ (Work.Spaces.HkNorm α m f) ^ 2 := by
    rw [sq]
    exact (abs_le.mp hcs).2
  exact hsq

/-- The same bound for a slot of the *cut* of a profile: the cut agrees with the profile on the
open quadrant, where the pairings live. -/
theorem sqrt_wip_cut_le {α : ℝ} (hα : 0 < α) {f : Fn}
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) {m a b a₀ b₀ : ℕ}
    (hab : (a + a₀) + (b + b₀) ≤ m) {w : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α (a + a₀) w) (hmf : Work.Spaces.HkMem α m f) :
    Real.sqrt (Work.Coercivity.wip w
        (Work.Spaces.mixed b a (cut (Work.Spaces.mixed b₀ a₀ f)))
        (Work.Spaces.mixed b a (cut (Work.Spaces.mixed b₀ a₀ f))))
      ≤ Work.Spaces.HkNorm α m f := by
  have heq : Work.Coercivity.wip w (Work.Spaces.mixed b a (cut (Work.Spaces.mixed b₀ a₀ f)))
        (Work.Spaces.mixed b a (cut (Work.Spaces.mixed b₀ a₀ f)))
      = Work.Coercivity.wip w (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f)) :=
    Work.FTS.StrongEps.EpsE4Thr.wip_congr_Q0_both
      (fun z θ h => mixed_cut_eqOn_Q0 (Work.Spaces.mixed b₀ a₀ f) b a h)
      (fun z θ h => mixed_cut_eqOn_Q0 (Work.Spaces.mixed b₀ a₀ f) b a h)
  rw [heq]
  exact sqrt_wip_comp_le hα hfs hab hleaf hmf

/-! ## The pointwise domination of a composed slot -/

/-- The composed slot of a leaf weight is dominated by the `ℋ^m`-integrand. -/
theorem dom_comp_slot {α : ℝ} (hα : 0 < α) {f : Fn}
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) {m a b a₀ b₀ : ℕ}
    (hab : (a + a₀) + (b + b₀) ≤ m) {w : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α (a + a₀) w) {z θ : ℝ}
    (hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    w z θ * (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f) z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α m f z θ := by
  have h : Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f) z θ
      = Work.Spaces.mixed (b + b₀) (a + a₀) f z θ := mixed_comp hfs b₀ a₀ b a hp
  rw [h]
  exact Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leaf_dom_gen hα hab hleaf
    ⟨hp.2.1, hp.2.2⟩

/-- The composed slot of a leaf weight applied to `J_ε h` is dominated by the `ℋ^m`-integrand of
`J_ε h`. -/
theorem dom_comp_slot_Jeps {α : ℝ} (hα : 0 < α) {h : Fn}
    (hhs : Work.FTS.EllipticEst.SmoothOpen h) {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) {m a b a₀ b₀ : ℕ}
    (hab : (a + a₀) + (b + b₀) ≤ m) {w : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α (a + a₀) w) {z θ : ℝ}
    (hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    w z θ * (Work.Spaces.mixed b a
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h)) z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε h) z θ := by
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry h) Work.FTS.StrongEps.Quad :=
    fun n => hhs.forall n
  have e1 : Work.Spaces.mixed b a
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h)) z θ
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ h)) z θ :=
    Work.FTS.StrongEps.mixed_Jeps ρ hρ hε (fun n => (hhs.mixed b₀ a₀).forall n) hp.1 hp.2 b a
  have e2 : Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ h))
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed (b + b₀) (a + a₀) h) :=
    Jeps_congr_Q0 (fun z' θ' h' => mixed_comp hhs b₀ a₀ b a h') ρ ε
  have e3 : Work.FTS.StrongEps.Jeps ρ ε
        (Work.Spaces.mixed (b + b₀) (a + a₀) h) z θ
      = Work.Spaces.mixed (b + b₀) (a + a₀) (Work.FTS.StrongEps.Jeps ρ ε h) z θ :=
    (Work.FTS.StrongEps.mixed_Jeps ρ hρ hε (fun n => hhs.forall n) hp.1 hp.2
      (b + b₀) (a + a₀)).symm
  rw [e1, e2, e3]
  exact Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leaf_dom_gen hα hab hleaf
    ⟨hp.2.1, hp.2.2⟩

/-! ## The integrability certificates of the slot transfer -/

/-- **The integrability certificates of the slot transfer, at the cuts of the shifted slots.**  The
six conditions of `SlotIntegrableDeriv`, all discharged from the composed-slot identity, the
`ℋ⁴`- (respectively `ℋ⁵`-) membership of the two data, and the vanishing of the cuts — and of
`J_ε` — outside the open quadrant. -/
theorem slotIntegrableDeriv_cut {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc (0 : ℝ) 1) {ε : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    {f h : Fn} (hfs : Work.FTS.EllipticEst.SmoothOpen f)
    (hhs : Work.FTS.EllipticEst.SmoothOpen h) (hmf : Work.Spaces.HkMem α 4 f)
    (hmh : Work.Spaces.HkMem α 5 h) {a₀ b₀ a b : ℕ} (hab₀ : a₀ + b₀ ≤ 3)
    (hab : a + b ≤ 1) {w : ℝ → ℝ → ℝ} (hleaf : Work.FTS.TransportS.IsLeafW α a w) :
    SlotIntegrableDeriv ρ ε w a b (cut (Work.Spaces.mixed b₀ a₀ f))
      (cut (Work.Spaces.mixed b₀ a₀ h)) := by
  have hα0 : 0 < α := hα.1
  have hε0 : 0 < ε := hε.1
  have hmh5 : Work.Spaces.HkMem α 5 h := hmh
  -- the cuts and the mollified second slot
  have hAsm : Work.FTS.EllipticEst.SmoothOpen (cut (Work.Spaces.mixed b₀ a₀ f)) :=
    smoothOpen_cut (hfs.mixed b₀ a₀)
  have hBsm : Work.FTS.EllipticEst.SmoothOpen (cut (Work.Spaces.mixed b₀ a₀ h)) :=
    smoothOpen_cut (hhs.mixed b₀ a₀)
  have hJsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.Jeps ρ ε (cut (Work.Spaces.mixed b₀ a₀ h))) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε0 (fun n => hBsm.forall n)
  have hJmh : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε h) :=
    Work.FTS.StrongEps.HkMem_Jeps (ρ := ρ) (k := 4) hρ.moll hα hε0
      (fun n => hhs.forall n) (Work.FTS.OpenPkg.HkMem_mono_open hhs 4 (by norm_num) hmh)
  have hJsme : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε h) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε0 (fun n => hhs.forall n)
  -- the cuts agree with the data on the open quadrant
  have hcutA : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed b a (cut (Work.Spaces.mixed b₀ a₀ f)) z θ
        = Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f) z θ :=
    fun z θ hh => mixed_cut_eqOn_Q0 (Work.Spaces.mixed b₀ a₀ f) b a hh
  have hcutB : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed b a (cut (Work.Spaces.mixed b₀ a₀ h)) z θ
        = Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ h) z θ :=
    fun z θ hh => mixed_cut_eqOn_Q0 (Work.Spaces.mixed b₀ a₀ h) b a hh
  -- the order bounds
  have hord1 : (a + a₀) + (b + b₀) ≤ 4 := by omega
  have hord2 : (a + a₀) + (b + 1 + b₀) ≤ 5 := by omega
  have hord3 : (a + 1 + a₀) + (b + b₀) ≤ 5 := by omega
  -- the three diagonal certificates
  have i1 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      w z θ * (Work.Spaces.mixed b a (cut (Work.Spaces.mixed b₀ a₀ f)) z θ) ^ 2)) volume := by
    refine integrable_slot_of_dom (m := 4) (ρ := w) (A := cut (Work.Spaces.mixed b₀ a₀ f))
      (D := f) hAsm (cut_zero_off _)
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.continuousOn_leafW hleaf)
      (Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leaf_nonneg hleaf) ?_
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.integrable_HkIntegrand
        hfs hmf)
    intro z θ hθ
    rw [hcutA z θ hθ]
    exact dom_comp_slot hα0 hfs hord1 (IsLeafW.add hleaf) hθ
  have i2 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      w z θ * (Work.Spaces.mixed b a (cut (Work.Spaces.mixed b₀ a₀ h)) z θ) ^ 2)) volume := by
    refine integrable_slot_of_dom (m := 5) (ρ := w) (A := cut (Work.Spaces.mixed b₀ a₀ h))
      (D := h) hBsm (cut_zero_off _)
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.continuousOn_leafW hleaf)
      (Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leaf_nonneg hleaf) ?_
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.integrable_HkIntegrand
        hhs hmh5)
    intro z θ hθ
    rw [hcutB z θ hθ]
    exact dom_comp_slot hα0 hhs (by omega : (a + a₀) + (b + b₀) ≤ 5) (IsLeafW.add hleaf) hθ
  have i3 : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ
      * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε
          (cut (Work.Spaces.mixed b₀ a₀ h))) z θ) ^ 2)) volume := by
    refine integrable_slot_of_dom (m := 4) (ρ := w)
      (A := Work.FTS.StrongEps.Jeps ρ ε (cut (Work.Spaces.mixed b₀ a₀ h)))
      (D := Work.FTS.StrongEps.Jeps ρ ε h) hJsm (Jeps_zero_off ρ ε _)
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.continuousOn_leafW hleaf)
      (Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leaf_nonneg hleaf) ?_
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.integrable_HkIntegrand
        hJsme hJmh)
    intro z θ hθ
    rw [Jeps_cut ρ ε (Work.Spaces.mixed b₀ a₀ h)]
    exact dom_comp_slot_Jeps hα0 hhs hρ.moll hε0 hord1 (IsLeafW.add hleaf) hθ
  -- the cross term
  have i4 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      w z θ * Work.Spaces.mixed b a (cut (Work.Spaces.mixed b₀ a₀ f)) z θ
        * Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε
            (cut (Work.Spaces.mixed b₀ a₀ h))) z θ)) volume :=
    integrable_cross_of_zero_off
      (mixed_eq_zero_of_zero_off (cut_zero_off _) b a)
      (mixed_eq_zero_of_zero_off (Jeps_zero_off ρ ε _) b a)
      (hAsm.mixed b a).continuousOn (hJsm.mixed b a).continuousOn
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.continuousOn_leafW hleaf)
      (Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leaf_nonneg hleaf) i1 i3
  -- the two shifted slots of the second argument
  have i5 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      w z θ * (Work.Spaces.mixed (b + 1) a (cut (Work.Spaces.mixed b₀ a₀ h)) z θ) ^ 2))
      volume := by
    refine integrable_slot_of_dom (m := 5) (ρ := w) (A := cut (Work.Spaces.mixed b₀ a₀ h))
      (D := h) hBsm (cut_zero_off _)
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.continuousOn_leafW hleaf)
      (Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leaf_nonneg hleaf) ?_
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.integrable_HkIntegrand
        hhs hmh5)
    intro z θ hθ
    rw [show Work.Spaces.mixed (b + 1) a (cut (Work.Spaces.mixed b₀ a₀ h)) z θ
        = Work.Spaces.mixed (b + 1) a (Work.Spaces.mixed b₀ a₀ h) z θ from
      mixed_cut_eqOn_Q0 (Work.Spaces.mixed b₀ a₀ h) (b + 1) a hθ]
    exact dom_comp_slot hα0 hhs hord2 (IsLeafW.mono hleaf (Nat.le_add_right a a₀)) hθ
  have i6 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      w z θ * (Work.Spaces.mixed b (a + 1) (cut (Work.Spaces.mixed b₀ a₀ h)) z θ) ^ 2))
      volume := by
    refine integrable_slot_of_dom (m := 5) (ρ := w) (A := cut (Work.Spaces.mixed b₀ a₀ h))
      (D := h) hBsm (cut_zero_off _)
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.continuousOn_leafW hleaf)
      (Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leaf_nonneg hleaf) ?_
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.integrable_HkIntegrand
        hhs hmh5)
    intro z θ hθ
    rw [show Work.Spaces.mixed b (a + 1) (cut (Work.Spaces.mixed b₀ a₀ h)) z θ
        = Work.Spaces.mixed b (a + 1) (Work.Spaces.mixed b₀ a₀ h) z θ from
      mixed_cut_eqOn_Q0 (Work.Spaces.mixed b₀ a₀ h) b (a + 1) hθ]
    exact dom_comp_slot hα0 hhs hord3 (IsLeafW.mono hleaf (by omega : a ≤ a + 1 + a₀)) hθ
  exact ⟨i1, i2, i3, i4, i5, i6⟩


end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsGdotThirdH =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

open Work.FTS.Galerkin (Fn Fam slice)

/-! ## Helper lemmas: the quadrant, and the modulation at the mollified slice -/






/-! ## The target -/


end Work.FTS.StrongEps
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsZero.Bridge.BdryClassC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.EpsZero.Bridge

/-- **The boundary/trace facts for a `ClassC` datum that vanishes off the open quadrant.**

For `f` in the linear elliptic class `Work.FTS.ClassC.ClassC α` (`C^∞` on the open quadrant
`(0,∞) × (0,π/2)`, with the weighted boundary traces `BdryTraces` of all slots `a+b ≤ 6`, the
`ℋ⁷`/`ℋ⁸` integrability `HkMem`, the all-order smoothness of the angular moment, the axis
condition `f z θ / z → 0` at `z → 0⁺` and the vanishing `L₁₂` mode) which is supported in the open
quadrant, the radial slices and the radial derivative slices have the following regular behaviour,
for **every** angle `θ ∈ Iθ = [0, π/2]`, endpoints included:

* `s ↦ ∂_z f (s, θ)` extends continuously to `[0, ∞)` (the first conjunct);
* `s ↦ f (s, θ)` tends to `0` at `z → +∞` (the second conjunct);
* `s ↦ f (s, θ)` is differentiable on `(0,∞)` with derivative `Work.Spaces.pz f z θ`
  (the third conjunct).

The proof has two parts.

* The last two clauses, and the differentiability, are the sibling
  `Work.FTS.StrongEps.EpsZero.slice_facts_of_classC` (`SmoothOpen` + `BdryTraces α 6` +
  support), which produces them in the order
  `HasDerivAt, ContinuousOn f, Tendsto f atTop` — only the order of the conjuncts differs.

* The remaining clause (continuity of the *derivative* slice `∂_z f (·, θ)` on `[0,∞)`) is not
  part of that sibling: `f` itself vanishes on the outer radial half-line, so for
  `θ ∉ (0, π/2)` the slice `∂_z f (·, θ)` is identically zero, while for `θ ∈ (0, π/2)`
  * `SmoothOpen.pz` gives continuity on the open half-line `(0,∞)`;
  * the `BdryTraces` slot `(a,b) = (0,1)` — that is, the trace of `D_z f = z ∂_z f` — reads
    `z * (D_z f (z,θ) * w z)^2 → 0` as `z → 0⁺`, which for `z > 0` is
    `(∂_z f)^2 * (1+z)^4 / z → 0`; since `z ≤ (1+z)^4` it dominates `(∂_z f)^2`, so
    `∂_z f (z,θ) → 0` at `z → 0⁺`.  This is precisely the delegated lemma
    `Work.FTS.StrongEps.EpsZero.Bridge.tendsto_pz_zero_of_trace`;
  * the `ClassC` axis condition `f z θ / z → 0` (via `pz_zero_of_tendsto_div`) gives
    `∂_z f (0, θ) = 0`, the value at the endpoint, so the limit along `𝓝[>] 0` upgrades to a limit
    along `𝓝[≥] 0` and continuity on `[0,∞)` follows. -/
theorem BdryClassC {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hC : Work.FTS.ClassC.ClassC α f)
    (hzero : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → f z θ = 0) :
    (∀ θ ∈ Work.Spaces.Iθ, ContinuousOn (fun s : ℝ => Work.Spaces.pz f s θ) (Set.Ici 0)) ∧
    (∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun s : ℝ => f s θ) Filter.atTop (nhds 0)) ∧
    (∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s : ℝ => f s θ) (Work.Spaces.pz f z θ) z) := by
  -- the two decay clauses and differentiability come from the sibling slice fact
  obtain ⟨hdiff, -, hdec⟩ :=
    Work.FTS.StrongEps.EpsZero.slice_facts_of_classC hC.reg hC.tr hzero
  refine ⟨?_, hdec, hdiff⟩
  intro θ hθ
  by_cases hI : θ ∈ Set.Ioo 0 (π / 2)
  · -- interior angle: the boundary trace of `D_z f` at `z = 0` plus the axis condition
    have htr : Filter.Tendsto
        (fun z : ℝ => z * (Work.Spaces.Dz f z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) :=
      ((hC.tr 0 1 (by norm_num)).1 θ hI).1
    have hlim : Filter.Tendsto (fun s : ℝ => Work.Spaces.pz f s θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) :=
      tendsto_pz_zero_of_trace htr
    have h0 : Work.Spaces.pz f 0 θ = 0 :=
      Work.FTS.StrongEps.pz_zero_of_tendsto_div hI (fun z hz => hzero z θ hz) (hC.axis θ hI)
    exact Work.FTS.StrongEps.EpsZero.continuousOn_Ici_of_continuousOn_Ioi_of_tendsto
      (hC.reg.pz.curry_z hI).continuousOn h0
      (Work.FTS.StrongEps.EpsZero.tendsto_Ici_of_tendsto_Ioi hlim h0)
  · -- outside the open angle interval the whole slice vanishes identically, hence so does `∂_z f`
    have hslice : (fun s : ℝ => f s θ) = fun _ => (0 : ℝ) :=
      funext (fun s => hzero s θ (fun hc => hI hc.2))
    have hzero_pz : (fun s : ℝ => Work.Spaces.pz f s θ) = fun _ => (0 : ℝ) := by
      funext s
      show deriv (fun z : ℝ => f z θ) s = 0
      rw [hslice, deriv_const]
    rw [hzero_pz]
    exact continuousOn_const

end Work.FTS.StrongEps.EpsZero.Bridge
end
-- ===== merged: Submission.Work.FTS_BSIdentP.RegPkgPrime.PhysVelNegSlice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdentP

noncomputable section

open FiniteTimeSingularity Set MeasureTheory Filter Gradient
open scoped Topology

/-- **Weak divergence-freeness is stable under pointwise negation.**  (Local copy of the private
lemma of `BSIdent.Weyl.physVel_neg_physOmega_slice`.) -/
private theorem weakDivFree_neg {ω : Work.FTS.BSIdent.R3 → Work.FTS.BSIdent.R3}
    (h : Work.FTS.BSSwirl.WeakDivFree ω) :
    Work.FTS.BSSwirl.WeakDivFree (fun x => -ω x) := by
  intro k hk hks
  have h1 := h k hk hks
  have h2 : (fun x => inner ℝ (-ω x) (gradient k x))
      = fun x => -(inner ℝ (ω x) (gradient k x)) := by
    funext x
    rw [inner_neg_left]
  rw [h2, integral_neg, h1, neg_zero]

theorem physVel_neg_physOmega_slice' {α : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    {C : Work.FTS.Physical.PhysClock} {S t : ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g)
    (hτ : Work.FTS.Physical.clockInv C t ∈ Set.Icc 0 S) :
    ContDiff ℝ 1 (Work.FTS.Physical.physVel (-(Work.FTS.Physical.physOmega α A B g C)) · t)
      ∧ (∀ x : Work.FTS.BSIdent.R3,
          FiniteTimeSingularity.vorticity
            (Work.FTS.Physical.physVel (-(Work.FTS.Physical.physOmega α A B g C)) · t) x
          = -(Work.FTS.Physical.physOmega α A B g C x t))
      ∧ (∀ x : Work.FTS.BSIdent.R3,
          FiniteTimeSingularity.div
            (Work.FTS.Physical.physVel (-(Work.FTS.Physical.physOmega α A B g C)) · t) x = 0)
      ∧ Filter.Tendsto (Work.FTS.Physical.physVel (-(Work.FTS.Physical.physOmega α A B g C)) · t)
          (Filter.cocompact Work.FTS.BSIdent.R3) (nhds 0) := by
  -- the four quantitative data of the unnegated physical vorticity slice, from `RegPkg'`
  obtain ⟨M, hM0, hbdd0⟩ := Work.FTS.FireFix.Prime.physVort_bound h
  obtain ⟨R, hR0, hsupp0⟩ := Work.FTS.FireFix.Prime.physVort_support h
  obtain ⟨Cd, hCd0, hhold0⟩ := Work.FTS.FireFix.Prime.physVort_holder_slice h
  -- the slice of `physVel` is the Biot–Savart field of the negated vorticity slice
  have hslice : (Work.FTS.Physical.physVel (-(Work.FTS.Physical.physOmega α A B g C)) · t)
      = Work.LWP.biotSavart (fun y : Work.FTS.BSIdent.R3 =>
          -(Work.FTS.Regularity.physVort α A B g y (Work.FTS.Physical.clockInv C t))) := by
    funext x; rfl
  -- abbreviate the negated vorticity slice
  let ω : Work.FTS.BSIdent.R3 → Work.FTS.BSIdent.R3 := fun y =>
    -(Work.FTS.Regularity.physVort α A B g y (Work.FTS.Physical.clockInv C t))
  have hbdd : ∀ y : Work.FTS.BSIdent.R3, ‖ω y‖ ≤ M := fun y => by
    simp only [ω, norm_neg]
    exact hbdd0 _ hτ y
  have hsupp : ∀ y : Work.FTS.BSIdent.R3, ω y ≠ 0 → y ∈ Metric.closedBall 0 R := fun y hy => by
    simp only [ω] at hy
    exact hsupp0 _ hτ y (by simpa using hy)
  have hhold : ∀ a b : Work.FTS.BSIdent.R3, ‖ω a - ω b‖ ≤ Cd * ‖a - b‖ ^ α := fun a b => by
    have h2 : ω a - ω b
        = -(Work.FTS.Regularity.physVort α A B g a (Work.FTS.Physical.clockInv C t)
            - Work.FTS.Regularity.physVort α A B g b (Work.FTS.Physical.clockInv C t)) := by
      simp only [ω]; abel
    rw [h2, norm_neg]
    exact hhold0 _ hτ a b
  have hcontω : Continuous ω := Work.FTS.BSSwirl.continuous_of_holder_pointwise h.hα hhold
  have hmeas : AEStronglyMeasurable ω volume := hcontω.aestronglyMeasurable
  -- the negated slice is a swirl field: `physVort · τ = swirlField φ`, hence `ω = −swirlField φ`
  let φ : ℝ → ℝ → ℝ := fun r z => (A (Work.FTS.Physical.clockInv C t))⁻¹ *
      Work.ConstructionInstance.profile (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.thetaP r z)
  have hsw : (Work.FTS.Regularity.physVort α A B g · (Work.FTS.Physical.clockInv C t))
      = Work.FTS.BSSwirl.swirlField φ :=
    Work.FTS.BSIdent.Weyl.physVort_slice_eq_swirlField α (Work.FTS.Physical.clockInv C t) A B g
  have hbdd_sw : ∀ x : Work.FTS.BSIdent.R3, ‖Work.FTS.BSSwirl.swirlField φ x‖ ≤ M := fun x => by
    rw [← congrFun hsw x]; exact hbdd0 _ hτ x
  have hsupp_sw : ∀ x : Work.FTS.BSIdent.R3,
      Work.FTS.BSSwirl.swirlField φ x ≠ 0 → x ∈ Metric.closedBall 0 R :=
    fun x hx => hsupp0 _ hτ x (by rwa [← congrFun hsw x] at hx)
  have hhold_sw : ∀ a b : Work.FTS.BSIdent.R3,
      ‖Work.FTS.BSSwirl.swirlField φ a - Work.FTS.BSSwirl.swirlField φ b‖
        ≤ Cd * ‖a - b‖ ^ α := fun a b => by
    rw [← congrFun hsw a, ← congrFun hsw b]; exact hhold0 _ hτ a b
  have hmeas_sw : AEStronglyMeasurable (Work.FTS.BSSwirl.swirlField φ) volume :=
    (Work.FTS.BSSwirl.continuous_of_holder_pointwise h.hα hhold_sw).aestronglyMeasurable
  have hdiv_sw : Work.FTS.BSSwirl.WeakDivFree (Work.FTS.BSSwirl.swirlField φ) :=
    Work.FTS.BSSwirl.weakDivFree_swirlField hM0 hR0.le hbdd_sw hmeas_sw hsupp_sw
  have hdiv : Work.FTS.BSSwirl.WeakDivFree ω := by
    have h1 : ω = fun x => -(Work.FTS.BSSwirl.swirlField φ x) := by
      funext x; simp only [ω]; rw [congrFun hsw x]
    rw [h1]
    exact weakDivFree_neg hdiv_sw
  -- the four conclusions for `BS ω`
  have hcd : ContDiff ℝ 1 (Work.LWP.biotSavart ω) :=
    Work.CoreResiduals.BiotSavart.biotSavart_contDiff_one hR0 hM0 h.hα hbdd hsupp hmeas hhold
  have hcurl : ∀ x, FiniteTimeSingularity.vorticity (Work.LWP.biotSavart ω) x = ω x :=
    Work.FTS.BSSwirl.vorticity_biotSavart_of_weakDivFree hR0 hM0 h.hα hCd0 hbdd hsupp hmeas hhold
      hdiv
  have hdivBS : ∀ x, FiniteTimeSingularity.div (Work.LWP.biotSavart ω) x = 0 :=
    Work.FTS.BSSwirl.div_biotSavart_eq_zero hR0 hM0 h.hα hCd0 hbdd hsupp hmeas hhold
  obtain ⟨Cd2, _hCd20, hdec⟩ := Work.FTS.PressureOn.biotSavart_decay hM0 hbdd hsupp
  have htend : Filter.Tendsto (Work.LWP.biotSavart ω)
      (Filter.cocompact Work.FTS.BSIdent.R3) (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _)
      (Eventually.of_forall fun x => by simpa using hdec x) ?_
    have h4 : Filter.Tendsto (fun x : Work.FTS.BSIdent.R3 => 1 + ‖x‖ ^ 2)
        (Filter.cocompact Work.FTS.BSIdent.R3) Filter.atTop :=
      Filter.tendsto_atTop_mono (fun x => by nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1 / 2)])
        tendsto_norm_cocompact_atTop
    have h5 : Filter.Tendsto (fun x : Work.FTS.BSIdent.R3 => (1 + ‖x‖ ^ 2)⁻¹)
        (Filter.cocompact Work.FTS.BSIdent.R3) (nhds 0) :=
      h4.inv_tendsto_atTop
    simpa [div_eq_mul_inv] using h5.const_mul Cd2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hslice]; exact hcd
  · intro x
    rw [hslice, hcurl x]
    show -(Work.FTS.Regularity.physVort α A B g x (Work.FTS.Physical.clockInv C t))
      = -(Work.FTS.Physical.physOmega α A B g C x t)
    rfl
  · intro x
    rw [hslice]; exact hdivBS x
  · rw [hslice]; exact htend

end

end Work.FTS.BSIdentP
end
-- ===== merged: Submission.Work.FTS_FinalLeaves.Min.ChainCont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_FinalLeaves.Min

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Continuity of the angular moment and of the `L₁₂`-density of a `C⁴` datum -/

/-- **Continuity of the angular moment** from the four analytic inputs, with the smoothness
hypothesis of `Work.FTS.CoercivityFix.Coer1T.HardyAlt.Fstar_continuousAt_of_aux` replaced by the
*chain relation* `F_*(F)(b) = F_*(F)(a) + ∫_a^b (∂_z-moment)`.  The proof is that of the
`HardyAlt` lemma verbatim. -/
theorem Fstar_continuousAt_of_chain (α : ℝ) {f : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hchain : ∀ a b : ℝ, 0 < a → a < b →
      Work.Elliptic.Fstar f b = Work.Elliptic.Fstar f a
        + ∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ))
    (hsl : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => f z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hB : MeasureTheory.IntegrableOn
      (fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ) Work.Spaces.Iz)
    (hmom : ∀ s : ℝ, 0 < s →
      |∫ θ in Work.Spaces.Iθ, Work.Spaces.pz f s θ * Work.Elliptic.sinCos2 θ|
        ≤ Real.sqrt (Real.pi / 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f s θ)) :
    ContinuousAt (Work.Elliptic.Fstar f) z := by
  have hle : z / 2 ≤ 2 * z := by linarith
  set M : ℝ → ℝ := fun r =>
    ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz f r θ * Work.Elliptic.sinCos2 θ with hMdef
  set Ψ : ℝ → ℝ := fun r => Real.sqrt (Real.pi / 2)
    * Real.sqrt (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ) with hΨdef
  have hΨnn : ∀ r : ℝ, 0 ≤ Ψ r := fun r => by
    rw [hΨdef]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hchain' : ∀ a b : ℝ, 0 < a → a < b →
      Work.Elliptic.Fstar f b - Work.Elliptic.Fstar f a = ∫ r in Set.Icc a b, M r := by
    intro a b ha hab
    have h := hchain a b ha hab
    simp only [hMdef]
    linarith [h]
  -- integrability of the majorant near `z`
  have hBint : MeasureTheory.IntegrableOn
      (fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)
      (Set.Icc (z / 2) (2 * z)) :=
    hB.mono_set (fun x hx => by
      simp only [Work.Spaces.Iz, Set.mem_Ici]
      linarith [hz, hx.1])
  have hdom : MeasureTheory.IntegrableOn
      (fun r => Real.sqrt (Real.pi / 2)
        * (|(∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)| + 1))
      (Set.Icc (z / 2) (2 * z)) := by
    have h1 : MeasureTheory.IntegrableOn
        (fun r => |(∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)| + 1)
        (Set.Icc (z / 2) (2 * z)) :=
      hBint.abs.add (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (by simp))
    exact h1.const_mul (Real.sqrt (Real.pi / 2))
  have hΨint : MeasureTheory.IntegrableOn Ψ (Set.Icc (z / 2) (2 * z)) := by
    refine hdom.mono' ?_ ?_
    · rw [hΨdef]
      exact aestronglyMeasurable_const.mul
        ((hBint.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable)
    · filter_upwards with r
      rw [hΨdef, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left (sqrt_le_abs_add_one _)
        (Real.sqrt_nonneg _)
  have hΨu : MeasureTheory.IntegrableOn Ψ (Set.uIcc (z / 2) (2 * z)) := by
    rw [Set.uIcc_of_le hle]
    exact hΨint
  have hprim : ContinuousOn (fun t => ∫ r in z..t, Ψ r) (Set.uIcc (z / 2) (2 * z)) :=
    intervalIntegral.continuousOn_primitive_interval' hΨu.intervalIntegrable
      (by rw [Set.uIcc_of_le hle]; exact ⟨by linarith, by linarith⟩)
  have hprim_at : ContinuousAt (fun t => ∫ r in z..t, Ψ r) z :=
    hprim.continuousAt
      (by
        rw [Set.uIcc_of_le hle]
        exact Icc_mem_nhds (by linarith) (by linarith))
  have htend : Tendsto (fun t => ‖∫ r in z..t, Ψ r‖) (𝓝 z) (𝓝 0) := by
    have h := hprim_at.norm
    rw [ContinuousAt] at h
    simpa using h
  have hsymm : ∀ t : ℝ, t ≤ z → ‖∫ r in z..t, Ψ r‖ = ∫ r in t..z, Ψ r := by
    intro t ht
    rw [Real.norm_eq_abs, intervalIntegral.integral_symm t z, abs_neg,
      abs_of_nonneg (intervalIntegral.integral_nonneg ht (fun r _ => hΨnn r))]
  have hbd_of : ∀ a b : ℝ, z / 2 ≤ a → a ≤ b → b ≤ 2 * z →
      |∫ r in a..b, M r| ≤ ∫ r in a..b, Ψ r := by
    intro a b ha hab hb
    have ha' : 0 < a := by linarith
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le hab ?_ ?_
    · refine Filter.Eventually.of_forall fun r hr => ?_
      have hrpos : 0 < r := lt_trans ha' hr.1
      simp only [Real.norm_eq_abs, hMdef, hΨdef]
      exact hmom r hrpos
    · have hss : Set.uIcc a b ⊆ Set.Icc (z / 2) (2 * z) := by
        rw [Set.uIcc_of_le hab]
        exact Set.Icc_subset_Icc ha hb
      exact (hΨint.mono_set hss).intervalIntegrable
  have hev : ∀ᶠ s in 𝓝 z, ‖Work.Elliptic.Fstar f s - Work.Elliptic.Fstar f z‖
      ≤ ‖∫ r in z..s, Ψ r‖ := by
    filter_upwards [Icc_mem_nhds (by linarith : z / 2 < z) (by linarith : z < 2 * z)]
      with s hs
    have hs1 : 0 < s := by linarith [hs.1]
    have hs2 : s ≤ 2 * z := by linarith [hs.2]
    rcases lt_trichotomy z s with hzs | hzs | hsz
    · have hch := hchain' z s hz hzs
      have hIcc : (∫ r in Set.Icc z s, M r) = ∫ r in z..s, M r := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hzs.le]
      have hbd := hbd_of z s (by linarith) hzs.le hs2
      have hΨi : 0 ≤ ∫ r in z..s, Ψ r :=
        intervalIntegral.integral_nonneg hzs.le (fun r _ => hΨnn r)
      rw [hch, hIcc, Real.norm_eq_abs]
      calc |∫ r in z..s, M r| ≤ ∫ r in z..s, Ψ r := hbd
        _ = |∫ r in z..s, Ψ r| := by rw [abs_of_nonneg hΨi]
    · subst hzs
      simp
    · have hch := hchain' s z hs1 hsz
      have hIcc : (∫ r in Set.Icc s z, M r) = ∫ r in s..z, M r := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hsz.le]
      have hbd := hbd_of s z hs.1 hsz.le (by linarith [hs2])
      rw [norm_sub_rev]
      rw [hch, hIcc, Real.norm_eq_abs]
      calc |∫ r in s..z, M r| ≤ ∫ r in s..z, Ψ r := hbd
        _ = |∫ r in z..s, Ψ r| := by rw [← Real.norm_eq_abs, hsymm s hsz.le]
  have hnorm : Tendsto (fun s => ‖Work.Elliptic.Fstar f s - Work.Elliptic.Fstar f z‖)
      (𝓝 z) (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun s => norm_nonneg _) hev htend
  have hdiff : Tendsto (fun s => Work.Elliptic.Fstar f s - Work.Elliptic.Fstar f z)
      (𝓝 z) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hcont : ContinuousAt (Work.Elliptic.Fstar f) z := by
    have h2 := hdiff.add_const (Work.Elliptic.Fstar f z)
    have h3 : (fun s => (Work.Elliptic.Fstar f s - Work.Elliptic.Fstar f z)
        + Work.Elliptic.Fstar f z) = Work.Elliptic.Fstar f := by
      funext s; ring
    rw [h3] at h2
    simpa [ContinuousAt] using h2
  exact hcont

end Work.FTS_FinalLeaves.Min
end
-- ===== merged: Submission.Work.FTS_LocDatum3a.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

set_option autoImplicit false

/-! ## Smoothness of the datum -/

/-- `locG6 α L β` is `C^∞` on `(-1,∞) × (0,π/2)`: it is the separable product `locR · Γ` of a
`C^∞`-on-`(-1,∞)` radial factor with the angular factor `Γ`. -/
theorem smoothQuad_locG6 (α L β : ℝ) : Work.FTS.LocData.SmoothQuad (locG6 α L β) := by
  rw [locG6_eq_locR_mul]
  exact Work.FTS.LocDataExt.smoothQuad_sepGam (Work.FTS.LocDataExt.contDiffOn_locR α L β)

/-- `locG6 α L β` is `C^∞` on the open quadrant `(0,∞) × (0,π/2)`. -/
theorem smoothOpen_locG6 (α L β : ℝ) : Work.FTS.EllipticEst.SmoothOpen (locG6 α L β) := by
  rw [Work.FTS.EllipticEst.SmoothOpen, Work.FTS.EllipticEst.Q0]
  exact (smoothQuad_locG6 α L β).mono
    (Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num)) subset_rfl)

/-- All finite orders of smoothness of `locG6 α L β` on the open quadrant `Quad` of the mollifier
chapter (the hypothesis `hsm` of `Work.FTS.StrongEps.softClass_Jeps`). -/
theorem forall_contDiffOn_locG6 (α L β : ℝ) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (locG6 α L β)) Work.FTS.StrongEps.Quad := by
  have h := smoothQuad_locG6 α L β
  rw [Work.FTS.LocData.SmoothQuad, contDiffOn_infty] at h
  intro n
  refine (h n).mono ?_
  rw [Work.FTS.StrongEps.Quad]
  exact Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num)) subset_rfl

/-! ## The axis condition -/


/-- The axis condition of the datum in the `ε`-`δ` shape consumed by
`Work.FTS.StrongEps.softClass_Jeps` (`hax`), as opposed to the `Tendsto` shape `hax_locG6`
consumed by `Work.FTS.StrongEps.axis_Jeps`. -/
theorem hax_locG6_eps (α L β : ℝ) (hL : 1 ≤ L) :
    ∀ ε' > 0, ∃ δ > 0, ∀ z : ℝ, 0 < z → z < δ →
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) → |locG6 α L β z θ / z| ≤ ε' := by
  intro ε' hε'
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  refine ⟨min L (3 / 4), lt_min hLpos (by norm_num), fun z hz0 hz θ _hθ => ?_⟩
  have hzL : z ≤ L := le_of_lt (lt_of_lt_of_le hz (min_le_left _ _))
  have hzb : z ≤ 3 / 4 := le_of_lt (lt_of_lt_of_le hz (min_le_right _ _))
  have hzval : locG6 α L β z θ = 0 := by
    have h1 : Work.FTS.LocDataExt.locR α L β z = 0 :=
      Work.FTS.LocDataExt.locR_eq_zero_of_le hLpos hz0.le hzL hzb
    rw [locG6_eq_locR_mul]
    change Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ = 0
    rw [h1, zero_mul]
  rw [hzval, zero_div, abs_zero]
  exact hε'.le

/-! ## The log-pull-back -/

/-- **The log-pull-back of the datum is continuous.**  In the log coordinates
`(s, ζ) ↦ (exp s, arctan (exp ζ))` the datum becomes
`locR (exp s) · Γ (arctan (exp ζ))`, a product of a continuous function of `s` (the `C^∞`
radial factor composed with `exp`) and a continuous function of `ζ` (`Γ` on `(0,π/2)` composed
with `arctan ∘ exp`, whose values lie in `(0,π/2)`). -/
theorem continuous_logPull_locG6 (α L β : ℝ) :
    Continuous (Work.FTS.StrongEps.logPull (locG6 α L β)) := by
  have h1 : Continuous (fun s : ℝ => Work.FTS.LocDataExt.locR α L β (Real.exp s)) :=
    (Work.FTS.LocDataExt.contDiffOn_locR α L β).continuousOn.comp_continuous
      Real.continuous_exp (fun s => by
        show (-1 : ℝ) < Real.exp s
        linarith [Real.exp_pos s])
  have h2 : Continuous (fun ζ : ℝ => Work.Spaces.Gam α (Real.arctan (Real.exp ζ))) :=
    (Work.FTS.LocData.contDiffOn_Gam_Ioo α).continuousOn.comp_continuous
      (Real.continuous_arctan.comp Real.continuous_exp)
      (fun ζ => ⟨Real.arctan_pos.mpr (Real.exp_pos ζ), Real.arctan_lt_pi_div_two _⟩)
  have hfun : (fun x : ℝ × ℝ => Work.FTS.LocDataExt.locR α L β (Real.exp x.1)
        * Work.Spaces.Gam α (Real.arctan (Real.exp x.2)))
      = Work.FTS.StrongEps.logPull (locG6 α L β) := by
    funext x
    rw [locG6_eq_locR_mul]
    rfl
  rw [← hfun]
  exact (h1.comp continuous_fst).mul (h2.comp continuous_snd)

/-- **`logPull (locG6 α L β)` is locally integrable** (the hypothesis `hloc` of
`Work.FTS.StrongEps.softClass_Jeps`), being continuous. -/
theorem locallyIntegrable_logPull_locG6 (α L β : ℝ) :
    LocallyIntegrable (Work.FTS.StrongEps.logPull (locG6 α L β)) volume :=
  (continuous_logPull_locG6 α L β).locallyIntegrable

end Work.FTS_LocDatum3a
end
end
