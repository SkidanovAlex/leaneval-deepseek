import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.ClassCHon.CmodeDefs
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.StabilityFar.Decay.hasDerivAt_bsK
-- ===== merged: Submission.Work.FTS.EllSol.FlatFT.slice_hasDerivAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The open strip of smoothness -/

/-- The open strip `ℝ × (0, π/2)` on which the data of `NiceFlat` is `C²`. -/
private def sliceStrp_prv : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

private theorem isOpen_sliceStrp_prv : IsOpen sliceStrp_prv := isOpen_univ.prod isOpen_Ioo

/-! ## Finite-order smoothness of the `θ`-partial on an open set -/

/-- The `θ`-partial of a `C^{n+1}` function on an open set is `C^n` there.

This is the finite-order form of `Work.Spaces.contDiffOn_uncurry_pth` (the `C^∞` case),
following `Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin`. -/
private theorem pth_smooth {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1 : ℕ) (Function.uncurry G) sliceStrp_prv) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) sliceStrp_prv := by
  have hchain : ∀ p ∈ sliceStrp_prv,
      Work.Spaces.pth G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by norm_num : (n + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (isOpen_sliceStrp_prv.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) sliceStrp_prv :=
    h.fderiv_of_isOpen isOpen_sliceStrp_prv (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) sliceStrp_prv :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  exact hchain p hp

/-! ## Continuity of the `t`-slices on the strip -/

/-- For `x ∈ (0,π/2)` the slice `t ↦ G t x` of a function which is `C^0` on the strip is
continuous. -/
private theorem continuous_slice {G : ℝ → ℝ → ℝ} {k : WithTop ℕ∞}
    (hG : ContDiffOn ℝ k (Function.uncurry G) sliceStrp_prv) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    Continuous fun t : ℝ => G t x := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hmem : (t, x) ∈ sliceStrp_prv := ⟨trivial, hx⟩
  have hca : ContDiffAt ℝ k (Function.uncurry G) (t, x) :=
    hG.contDiffAt (isOpen_sliceStrp_prv.mem_nhds hmem)
  have hc : ContinuousAt (fun t' : ℝ => (t', x)) t := continuousAt_id.prodMk continuousAt_const
  have hcomp := ContinuousAt.comp (f := fun t' : ℝ => (t', x)) (g := Function.uncurry G)
    (x := t) hca.continuousAt hc
  simpa only [Function.comp_def, Function.uncurry] using hcomp

/-! ## A support bookkeeping lemma -/

/-- If `M ≥ 0` and `t ∉ [-M, M]` then `M < |t|`. -/
private theorem abs_lt_of_notMem_Icc {M t : ℝ} (hM : 0 ≤ M) (h : t ∉ Set.Icc (-M) M) :
    M < |t| := by
  rcases lt_trichotomy t 0 with hlt | heq | hgt
  · rw [abs_of_neg hlt]
    by_contra hc
    push Not at hc
    exact h (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
  · subst heq
    exact absurd (Set.mem_Icc.mpr ⟨by linarith, hM⟩) h
  · rw [abs_of_pos hgt]
    by_contra hc
    push Not at hc
    exact h (Set.mem_Icc.mpr ⟨by linarith, hc⟩)

/-! ## The parameter differentiation -/

/-- **Differentiation under the `t`-integral defining a slice.**

Let `φ` be of class `C¹` on the open strip `ℝ × (0,π/2)` with continuous `θ`-partial there,
let `φ` vanish for `M < |t|` with `M ≥ 0`, and let `κ` be continuous with `‖κ t‖ = 1`.
Then for `x₀ ∈ (0,π/2)` the function `x ↦ ∫_t (φ t x : ℂ) · κ t` is differentiable at `x₀`
with derivative `∫_t (∂_θφ t x₀ : ℂ) · κ t`. -/
private theorem slice_hasDerivAt_aux_prv
    (φ : ℝ → ℝ → ℝ) (κ : ℝ → ℂ)
    (hφ : ContDiffOn ℝ 1 (Function.uncurry φ) sliceStrp_prv)
    (hφ' : ContinuousOn (Function.uncurry (Work.Spaces.pth φ)) sliceStrp_prv)
    (hκ : Continuous κ) (hκ1 : ∀ t, ‖κ t‖ = 1)
    {M : ℝ} (hM : 0 ≤ M) (hsupp : ∀ t θ, M < |t| → φ t θ = 0)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun x => ∫ t, (φ t x : ℂ) * κ t)
      (∫ t, ((Work.Spaces.pth φ) t x₀ : ℂ) * κ t) x₀ := by
  -- the angle window `(x₀-ε, x₀+ε)` on which everything is differentiated
  set ε : ℝ := min x₀ (Real.pi / 2 - x₀) / 2 with hεdef
  have hmin0 : 0 < min x₀ (Real.pi / 2 - x₀) :=
    lt_min hx₀.1 (by linarith [hx₀.2, Real.pi_pos])
  have hε0 : 0 < ε := by rw [hεdef]; linarith
  have hεx : ε < x₀ := by
    have h := min_le_left x₀ (Real.pi / 2 - x₀)
    rw [hεdef]; linarith
  have hεπ : ε < Real.pi / 2 - x₀ := by
    have h := min_le_right x₀ (Real.pi / 2 - x₀)
    rw [hεdef]; linarith
  have hs : Set.Ioo (x₀ - ε) (x₀ + ε) ∈ 𝓝 x₀ :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hsub : Set.Ioo (x₀ - ε) (x₀ + ε) ⊆ Set.Ioo 0 (Real.pi / 2) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- the `θ`-partial vanishes off the `t`-support of `φ`
  have hpth_zero : ∀ t, M < |t| → ∀ x, Work.Spaces.pth φ t x = 0 := by
    intro t ht x
    simp only [Work.Spaces.pth]
    rw [show (fun y : ℝ => φ t y) = fun _ => (0 : ℝ) from funext fun y => hsupp t y ht]
    simp
  -- the compact box on which `∂_θφ` is bounded
  have hBox : Set.Icc (-M) M ×ˢ Set.Icc (x₀ - ε) (x₀ + ε) ⊆ sliceStrp_prv := by
    intro p hp
    obtain ⟨-, hp2⟩ := Set.mem_prod.mp hp
    exact ⟨trivial, ⟨by linarith [hp2.1], by linarith [hp2.2]⟩⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -M) (b := M)).prod
      (isCompact_Icc (a := x₀ - ε) (b := x₀ + ε)) |>.exists_bound_of_continuousOn
        (hφ'.mono hBox)
  have hCnn : 0 ≤ C := by
    refine le_trans (norm_nonneg _) (hC (0, x₀) ?_)
    exact Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨by linarith, hM⟩,
      Set.mem_Icc.mpr ⟨by linarith, by linarith⟩⟩
  -- continuity of the `θ`-partial on the vertical line `t = x₀`
  have hpth_cont : Continuous fun t : ℝ => Work.Spaces.pth φ t x₀ := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hmem : (t, x₀) ∈ sliceStrp_prv := ⟨trivial, hx₀⟩
    have hc : ContinuousAt (fun p : ℝ × ℝ => Work.Spaces.pth φ p.1 p.2) (t, x₀) :=
      hφ'.continuousAt (isOpen_sliceStrp_prv.mem_nhds hmem)
    have hc' : ContinuousAt (fun t' : ℝ => (t', x₀)) t :=
      continuousAt_id.prodMk continuousAt_const
    have hcomp := ContinuousAt.comp (f := fun t' : ℝ => (t', x₀))
      (g := fun p : ℝ × ℝ => Work.Spaces.pth φ p.1 p.2) (x := t) hc hc'
    simpa only [Function.comp_def, Function.uncurry] using hcomp
  -- the four side conditions of the domination theorem
  have hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun t : ℝ => (φ t x : ℂ) * κ t)
      (volume.restrict (Set.Icc (-M) M)) := by
    filter_upwards [hs] with x hx
    have hcont : Continuous fun t : ℝ => φ t x := continuous_slice hφ (hsub hx)
    exact ((Complex.continuous_ofReal.comp hcont).mul hκ).aestronglyMeasurable
  have hF_int : Integrable (fun t : ℝ => (φ t x₀ : ℂ) * κ t)
      (volume.restrict (Set.Icc (-M) M)) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc (a := -M) (b := M))
      ((Complex.continuous_ofReal.comp (continuous_slice hφ hx₀)).mul hκ).continuousOn
  have hF'_meas : AEStronglyMeasurable (fun t : ℝ => ((Work.Spaces.pth φ) t x₀ : ℂ) * κ t)
      (volume.restrict (Set.Icc (-M) M)) :=
    ((Complex.continuous_ofReal.comp hpth_cont).mul hκ).aestronglyMeasurable
  have hbound : ∀ᵐ a ∂(volume.restrict (Set.Icc (-M) M)),
      ∀ x ∈ Set.Ioo (x₀ - ε) (x₀ + ε),
        ‖((Work.Spaces.pth φ) a x : ℂ) * κ a‖ ≤ (fun _ : ℝ => C) a := by
    refine Filter.Eventually.of_forall fun a x hx => ?_
    by_cases ha : a ∈ Set.Icc (-M) M
    · have h1 : ‖((Work.Spaces.pth φ) a x : ℂ)‖ ≤ C := by
        simpa using hC (a, x) (Set.mem_prod.mpr ⟨ha,
          Set.mem_Icc.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩)
      calc ‖((Work.Spaces.pth φ) a x : ℂ) * κ a‖
          = ‖((Work.Spaces.pth φ) a x : ℂ)‖ * ‖κ a‖ := norm_mul _ _
        _ = ‖((Work.Spaces.pth φ) a x : ℂ)‖ := by rw [hκ1 a, mul_one]
        _ ≤ C := h1
    · rw [hpth_zero a (abs_lt_of_notMem_Icc hM ha) x, Complex.ofReal_zero, zero_mul, norm_zero]
      exact hCnn
  have hb_int : Integrable (fun _ : ℝ => C) (volume.restrict (Set.Icc (-M) M)) :=
    MeasureTheory.integrableOn_const (μ := volume) (s := Set.Icc (-M) M) (C := C)
      (ne_of_lt (measure_Icc_lt_top (a := -M) (b := M))) (by simp)
  have hdiff : ∀ᵐ a ∂(volume.restrict (Set.Icc (-M) M)),
      ∀ x ∈ Set.Ioo (x₀ - ε) (x₀ + ε),
        HasDerivAt (fun x' : ℝ => (φ a x' : ℂ) * κ a)
          (((Work.Spaces.pth φ) a x : ℂ) * κ a) x := by
    refine Filter.Eventually.of_forall fun a x hx => ?_
    have hmem : (a, x) ∈ sliceStrp_prv := ⟨trivial, hsub hx⟩
    have hd : DifferentiableAt ℝ (fun x' : ℝ => φ a x') x :=
      Work.Spaces.differentiableAt_curry_right
        ((hφ.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
          (isOpen_sliceStrp_prv.mem_nhds hmem))
    exact (hd.hasDerivAt.ofReal_comp).mul_const (κ a)
  obtain ⟨-, hmain⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Icc (-M) M)) (𝕜 := ℝ)
    (F := fun x t => (φ t x : ℂ) * κ t)
    (F' := fun x t => ((Work.Spaces.pth φ) t x : ℂ) * κ t)
    (bound := fun _ : ℝ => C) (x₀ := x₀) (s := Set.Ioo (x₀ - ε) (x₀ + ε))
    hs hF_meas hF_int hF'_meas hbound hb_int hdiff
  -- transfer the two restricted integrals back to the full line
  have hsupp_int : ∀ x ∈ Set.Ioo (x₀ - ε) (x₀ + ε),
      (∫ t, (φ t x : ℂ) * κ t) = ∫ t in Set.Icc (-M) M, (φ t x : ℂ) * κ t := by
    intro x hx
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun t ht => by
        rw [hsupp t x (abs_lt_of_notMem_Icc hM ht), Complex.ofReal_zero, zero_mul])).symm
  have hdersupp : (∫ t in Set.Icc (-M) M, ((Work.Spaces.pth φ) t x₀ : ℂ) * κ t)
      = ∫ t, ((Work.Spaces.pth φ) t x₀ : ℂ) * κ t := by
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
    rw [hpth_zero t (abs_lt_of_notMem_Icc hM ht) x₀, Complex.ofReal_zero, zero_mul]
  refine (hmain.congr_of_eventuallyEq ?_).congr_deriv hdersupp
  filter_upwards [hs] with x hx
  exact hsupp_int x hx

/-! ## The slice of a `NiceFlat` datum is differentiable in the angle -/

theorem slice_hasDerivAt (g : ℝ → ℝ → ℝ) (hg : Work.FTS.EllSol.FlatFT.NiceFlat g) (ξ : ℝ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun θ' => Work.FTS.EllSol.FlatFT.slice g ξ θ') (Work.FTS.EllSol.FlatFT.slice (Work.Spaces.pth g) ξ θ) θ ∧
      HasDerivAt (fun θ' => Work.FTS.EllSol.FlatFT.slice (Work.Spaces.pth g) ξ θ')
        (Work.FTS.EllSol.FlatFT.slice (Work.Spaces.pth (Work.Spaces.pth g)) ξ θ) θ := by
  obtain ⟨hcd, -, -, N, hN⟩ := hg
  have hM : (0 : ℝ) ≤ max N 0 := le_max_right N 0
  have hsupp : ∀ t θ', max N 0 < |t| → g t θ' = 0 :=
    fun t θ' ht => hN t θ' (lt_of_le_of_lt (le_max_left N 0) ht)
  have hκc : Continuous fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * ξ * t)) := by
    fun_prop
  have hκ1 : ∀ t : ℝ, ‖Complex.exp (-(2 * Real.pi * Complex.I * ξ * t))‖ = 1 := by
    intro t
    rw [show -(2 * Real.pi * Complex.I * ξ * t) = (-(2 * Real.pi * ξ * t) : ℝ) * Complex.I from by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hpth1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth g)) sliceStrp_prv :=
    pth_smooth (n := 1) hcd
  constructor
  · have h := slice_hasDerivAt_aux_prv g (fun t => Complex.exp (-(2 * Real.pi * Complex.I * ξ * t)))
      (hcd.of_le (by norm_num)) hpth1.continuousOn hκc hκ1 hM hsupp hθ
    exact h
  · have hpth2 : ContDiffOn ℝ 0
        (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth g))) sliceStrp_prv :=
      pth_smooth (n := 0) hpth1
    have hsupp2 : ∀ t θ', max N 0 < |t| → Work.Spaces.pth g t θ' = 0 := by
      intro t θ' ht
      simp only [Work.Spaces.pth]
      rw [show (fun y : ℝ => g t y) = fun _ => (0 : ℝ) from funext fun y => hsupp t y ht]
      simp
    have h := slice_hasDerivAt_aux_prv (Work.Spaces.pth g)
      (fun t => Complex.exp (-(2 * Real.pi * Complex.I * ξ * t)))
      hpth1 hpth2.continuousOn hκc hκ1 hM hsupp2 hθ
    exact h

end

end Work.FTS.EllSol.FlatFT
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngAWeak.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AngAWeak/Basic` — the interface of Step 2 of Elgindi's `prop:H2` in the a.e. class

This module is the *interface* of the analytic input `Step2` of
`Submission/Work/FTS/EllipticEst/H2W/Ae/Assembly.lean`, i.e. the paper's Step 2 in the weak
class `Work.FTS.EllipticEst.H2W.Ae.AeData`:

  `‖∂_θθu‖_ρ ≤ C (‖G‖_ρ + α ‖z∂_zu‖_ρ)`,  `‖g‖_ρ = √(HkSq α 0 g)`.

## Design

The proof is the paper's: multiply `bslOp α u = G` by `-∂_θθu·w²σ`, integrate over the quadrant
(the *pairing identity*), bound the five pieces

* `I₁ = α²⟨z²∂_zzu, ∂_θθu⟩` (the lower bound: the deep input `AeI1`),
* `I₂ = α(5+α)⟨z∂_zu, ∂_θθu⟩` (Cauchy–Schwarz),
* `I₄ = ⟨∂_θ(tan θ·u), ∂_θθu⟩` (the upper bound: the deep input `AeI4`),
* `I₅ = 6⟨u, ∂_θθu⟩`, `I₆ = ⟨G, ∂_θθu⟩` (Cauchy–Schwarz),

and solve the resulting quadratic inequality.  The Step 1 inputs (`‖u‖_ρ` and the `Ψ̄ = u/cos θ`
analogue in terms of `‖G‖_ρ` and `α‖z∂_zu‖_ρ`, together with the honesty of `u`, `z∂_zu`,
`u/cos θ`) form the input `AeStep1`, and the `IPMem` bookkeeping of the identity is the input
`AeIPMems`.

It contains, sorry-free: (a) the pairing identity in the form needed here — the file
`AngSecond/I_identity.lean` states it for `IsBslSol`, which *includes the pointwise decay at
`z → ∞`* that `AeData` does not have, while its proof only uses the equation on the open
quadrant, so we restate it here; (b) the four `Prop`s `AeStep1`, `AeI1`, `AeI4`, `AeIPMems`
collecting the analytic inputs (each proved elsewhere as a theorem of that `Prop`); (c) the
assembly `step2Ae_of` of the estimate from the four inputs.  The target `step2Ae` itself lives in
`AngAWeak/step2Ae.lean`, which imports this module together with the four proofs.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

open Work.FTS.EllipticEst.AngSecond

/-! ## The pairing identity for data with no decay at `z = ∞` -/

/-- **Linearity of the weighted pairing in its first slot, in finite-sum form.**

With `IP g h = ∫_z ∫_θ g z θ * h z θ * w z² * σ θ` and `IPMem` the honesty of that iterated
integral, a finite linear combination of pairings is the pairing of the linear combination.
(A copy of the private helper of `AngSecond/I_identity.lean`, with the same proof.) -/
private theorem IP_sum_left'' {ι : Type*} [Fintype ι] (c : ι → ℝ) (f : ι → ℝ → ℝ → ℝ)
    (h : ℝ → ℝ → ℝ) (hf : ∀ i, IPMem (f i) h) :
    IP (fun z θ => ∑ i, c i * f i z θ) h = ∑ i, c i * IP (f i) h := by
  simp only [IP]
  have hmid : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (∑ i, c i * f i z θ) * h z θ * w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
        = ∑ i, c i * (∫ θ in Work.Spaces.Iθ, f i z θ * h z θ * w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    intro z hz
    rw [show (∫ θ in Work.Spaces.Iθ, (∑ i, c i * f i z θ) * h z θ * w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
        = ∫ θ in Work.Spaces.Iθ, ∑ i, c i * (f i z θ * h z θ * w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) from
      setIntegral_congr_fun (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        (fun θ _ => by
          rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by ring))]
    rw [MeasureTheory.integral_finsetSum]
    · exact Finset.sum_congr rfl (fun i _ => MeasureTheory.integral_const_mul (c i) _)
    · intro i _; exact ((hf i).1 z hz).const_mul (c i)
  rw [MeasureTheory.setIntegral_congr_fun
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) hmid]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    exact MeasureTheory.integral_const_mul (c i) _
  · intro i _; exact ((hf i).2).const_mul (c i)

/-- **The weighted pairing vanishes on functions vanishing in the open quadrant.**

If `g` vanishes on `(0,∞) × (0,π/2)` then `IP g h = 0`: the complement of the open quadrant
inside `Iz × Iθ` is the null set of the two boundary lines.  No hypothesis on `h` is needed.
(A copy of the private helper of `AngSecond/I_identity.lean`, with the same proof.) -/
private theorem IP_eq_zero_of_openQuadrant'' (g h : ℝ → ℝ → ℝ)
    (hg : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g z θ = 0) :
    IP g h = 0 := by
  simp only [IP]
  have hslice : ∀ z ∈ Work.Spaces.Iz, z ≠ 0 →
      (∫ θ in Work.Spaces.Iθ, g z θ * h z θ * w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) = 0 := by
    intro z hz hz0
    rw [show (∫ θ in Work.Spaces.Iθ, g z θ * h z θ * w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
        = ∫ θ in Work.Spaces.Iθ, (0 : ℝ) from
      setIntegral_congr_ae (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc) ?_]
    · simp
    · rw [MeasureTheory.ae_iff]
      refine measure_mono_null (t := ({0, Real.pi / 2} : Set ℝ)) ?_ ?_
      · intro θ hθ
        simp only [Set.mem_ofPred_eq] at hθ
        by_contra hbad
        apply hθ
        intro hθI
        have h0 : 0 < θ := lt_of_le_of_ne hθI.1 (fun h => hbad (by rw [h]; simp))
        have h1 : θ < Real.pi / 2 := lt_of_le_of_ne hθI.2 (fun h => hbad (by rw [h]; simp))
        have hzpos : 0 < z := lt_of_le_of_ne hz (fun h => hz0 h.symm)
        rw [hg z hzpos θ ⟨h0, h1⟩]; ring
      · rw [show ({0, Real.pi / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {Real.pi / 2} from by
          ext x; simp only [mem_insert_iff, mem_singleton_iff, mem_union]]
        exact measure_union_null (measure_singleton 0) (measure_singleton (Real.pi / 2))
  have hae : ∀ᵐ x ∂(volume : MeasureTheory.Measure ℝ), x ∈ Work.Spaces.Iz →
      (∫ θ in Work.Spaces.Iθ, g x θ * h x θ * w2 x * Work.FTS.EllipticEst.AngSecond.sig θ) = 0 := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null (t := ({0} : Set ℝ)) ?_ (measure_singleton 0)
    intro z hz
    by_contra hz0
    exact hz (fun hzI => hslice z hzI hz0)
  rw [MeasureTheory.setIntegral_congr_ae
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) hae]
  simp

/-- **The Step 2 integral identity without any decay hypothesis.**

Multiplying the equation `bslOp α Ψ = F` (on the *open* quadrant only) by
`-∂_θθΨ · w²/sin(2θ)^η` and integrating over the quadrant gives

  `I₁ + I₂ + I₃ + I₄ + I₅ = - IP F (∂_θθΨ)`

with `I₁ = α²·IP (z²∂_zzΨ) (∂_θθΨ)`, `I₂ = α(5+α)·IP (z∂_zΨ) (∂_θθΨ)`,
`I₃ = IP (∂_θθΨ) (∂_θθΨ)`, `I₄ = - IP (∂_θ(tan θ Ψ)) (∂_θθΨ)`, `I₅ = 6·IP Ψ (∂_θθΨ)`.

This is `Work.FTS.EllipticEst.AngSecond.I_identity` with the hypothesis `IsBslSol α F Ψ`
(which contains the pointwise decay `Ψ(·,θ) → 0` at `z → ∞`, unavailable in `AeData`) replaced by
the single equation on the open quadrant — which is all the proof of `I_identity` uses. -/
theorem I_identity_weak (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (heq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ)
    (hF : IPMem F (Work.Spaces.pthIter 2 Ψ))
    (hQ : IPMem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Work.Spaces.pthIter 2 Ψ))
    (hU : IPMem (fun z θ => z * Work.Spaces.pz Ψ z θ) (Work.Spaces.pthIter 2 Ψ))
    (hG : IPMem (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
      (Work.Spaces.pthIter 2 Ψ))
    (hPsi : IPMem Ψ (Work.Spaces.pthIter 2 Ψ))
    (hphi : IPMem (Work.Spaces.pthIter 2 Ψ) (Work.Spaces.pthIter 2 Ψ)) :
    α ^ 2 * IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Work.Spaces.pthIter 2 Ψ)
      + α * (5 + α) * IP (fun z θ => z * Work.Spaces.pz Ψ z θ) (Work.Spaces.pthIter 2 Ψ)
      + IP (Work.Spaces.pthIter 2 Ψ) (Work.Spaces.pthIter 2 Ψ)
      - IP (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ)
          (Work.Spaces.pthIter 2 Ψ)
      + 6 * IP Ψ (Work.Spaces.pthIter 2 Ψ)
      = - IP F (Work.Spaces.pthIter 2 Ψ) := by
  set Ph : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ with hPhdef
  set Q : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ with hQdef
  set U : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz Ψ z θ with hUdef
  set G₁ : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ
    with hGdef
  -- the bracket whose vanishing on the open quadrant *is* the elliptic equation
  set B : ℝ → ℝ → ℝ := fun z θ =>
    F z θ + α ^ 2 * Q z θ + α * (5 + α) * U z θ + Ph z θ - G₁ z θ + 6 * Ψ z θ with hBdef
  set c : Fin 6 → ℝ := ![1, α ^ 2, α * (5 + α), 1, -1, 6] with hcdef
  set f : Fin 6 → ℝ → ℝ → ℝ := ![F, Q, U, Ph, G₁, Ψ] with hfdef
  have hBz : ∀ z, 0 < z → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), B z θ = 0 := by
    intro z hz θ hθ
    have hbs := heq z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] at hbs
    simp only [hBdef, hQdef, hUdef, hGdef, hPhdef]
    rw [← hbs]
    ring
  have hzero : IP B Ph = 0 := IP_eq_zero_of_openQuadrant'' B Ph hBz
  have hBeq : B = fun z θ => ∑ i : Fin 6, c i * f i z θ := by
    funext z θ
    rw [Fin.sum_univ_six, hcdef, hfdef, hBdef]
    simp
    ring
  have hsum : IP B Ph = ∑ i : Fin 6, c i * IP (f i) Ph := by
    rw [hBeq]
    exact IP_sum_left'' c f Ph (fun i => by
      fin_cases i <;> simp [hfdef, hF, hQ, hU, hphi, hG, hPsi])
  have hexp : (∑ i : Fin 6, c i * IP (f i) Ph)
      = 1 * IP F Ph + α ^ 2 * IP Q Ph + α * (5 + α) * IP U Ph + 1 * IP Ph Ph
        + (-1) * IP G₁ Ph + 6 * IP Ψ Ph := by
    rw [Fin.sum_univ_six, hcdef, hfdef]
    simp
  have hsum0 : (∑ i : Fin 6, c i * IP (f i) Ph) = 0 := by
    rw [← hsum]; exact hzero
  have hcomb : α ^ 2 * IP Q Ph + α * (5 + α) * IP U Ph + IP Ph Ph - IP G₁ Ph
      + 6 * IP Ψ Ph + IP F Ph = 0 := by
    rw [show α ^ 2 * IP Q Ph + α * (5 + α) * IP U Ph + IP Ph Ph - IP G₁ Ph
        + 6 * IP Ψ Ph + IP F Ph = ∑ i : Fin 6, c i * IP (f i) Ph from by
      rw [hexp]; ring]
    exact hsum0
  rw [eq_neg_iff_add_eq_zero]
  exact hcomb

/-! ## The four inputs of the assembly

Each is a genuinely independent piece of the paper's Step 2; each is stated with the *full*
`AeData` hypothesis (so that the prover has the equation, the Dirichlet data and the two a.e.
moment conditions available) plus the honesty statements that `AeData` does not supply. -/


/-- **The `I₁` lower bound in the class `AeData`**:
`-C α²(IP (z∂_zu) (z∂_zu) + √(IP (z∂_zu)(z∂_zu))·√(IP (∂_θθu)(∂_θθu))) ≤ α² IP (z²∂_zzu) (∂_θθu)`.

The full `AeData` hypothesis class is used (in particular **both** a.e. moment conditions
`F_* u = 0`, `F_* G = 0`): the lower bound is *false* without the moment condition on the
source `G`, since a slice with a jump at `θ = 0` whose angular moment vanishes gives
`IP (z²∂_zzu) (∂_θθu)` of the wrong size (see `AngAWeak/NOTES_aeI1Lower_FALSE.md`); it is the
equation together with `F_* u = F_* G = 0` that forces the slices to have no jump. -/
def AeI1 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) →
      - C * α ^ 2 * (IP (fun z θ => z * Work.Spaces.pz u z θ)
            (fun z θ => z * Work.Spaces.pz u z θ)
          + Real.sqrt (IP (fun z θ => z * Work.Spaces.pz u z θ)
                (fun z θ => z * Work.Spaces.pz u z θ))
            * Real.sqrt (IP (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)))
        ≤ α ^ 2 * IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ)
            (Work.Spaces.pthIter 2 u)


/-- **The `IPMem` bookkeeping of the identity in the class `AeData`.** -/
def AeIPMems : Prop :=
  ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    Work.Spaces.HkMem α 0 u →
    Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) →
      IPMem G (Work.Spaces.pthIter 2 u) ∧
      IPMem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) (Work.Spaces.pthIter 2 u) ∧
      IPMem (fun z θ => z * Work.Spaces.pz u z θ) (Work.Spaces.pthIter 2 u) ∧
      IPMem (fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ)
        (Work.Spaces.pthIter 2 u) ∧
      IPMem u (Work.Spaces.pthIter 2 u) ∧
      IPMem (Work.Spaces.pthIter 2 u) (Work.Spaces.pthIter 2 u)

/-! ## The assembly -/



end Work.FTS.EllipticEst.AngAWeak
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RPFresh.DdIntSlotBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.RPFresh



end Work.FTS.EllipticEst.RPFresh
end
-- ===== merged: Submission.Work.FTS.EllipticEst.RPFresh.LHSDecomp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The value decomposition of the `ℋ^k`-square of `α D_z ∂_θ V`

`Work.Spaces.HkSq α k (α D_z∂_θV)` is, by definition, the iterated integral of the nonnegative
`ℋ^k`-integrand.  This module proves that it is bounded by the sum of the integrals of the two
families of slices `mixIntS (D_z^r V)` (`r ≤ k`) and `mixedIntS α i j V` (`1 ≤ i`, `i + j ≤ k`),
*provided* the `z`-integrand of that sum is integrable (`IntegrableOn` in the statement).

The pointwise content is the Clairaut identity `D_z^j D_θ^i(D_z∂_θV) = D_z^{j+1}D_θ^i(∂_θV)` on
the open quadrant, which allows the `D_θ`-family of the `ℋ^k`-integrand of `D_z∂_θV` to be
rewritten as the `D_θ`-family of `∂_θV` shifted in `D_z`; the `D_z`-family is rewritten the same
way.  The `IntegrableOn` hypothesis is genuinely needed: the outer Bochner integral is not
monotone with respect to a non-integrable majorant (the summand Bochner integrals may be junk
`0`), so without it the two sides can lose different pieces.
-/

namespace Work.FTS.EllipticEst.RPFresh

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The two families of slice integrands -/

/-- The `D_z`-family slice integrand: the integrand of `mixIntS (D_z^r V)`. -/
def lhsZ (V : ℝ → ℝ → ℝ) (r : ℕ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 *
    ((Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
      * Work.FTS.EllipticEst.thEta θ)

/-- The mixed-family slice integrand: the integrand of `mixedIntS α i j V` (with the same
`if`-condition as in `HkIntegrand`). -/
def lhsM (α : ℝ) (k : ℕ) (V : ℝ → ℝ → ℝ) (i j : ℕ) (z θ : ℝ) : ℝ :=
  if 1 ≤ i ∧ i + j ≤ k then
    (Work.Spaces.w z) ^ 2 *
      ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ)
  else 0

/-! ## Elementary facts -/

theorem measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc

theorem measurableSet_Iz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici

theorem measurable_w : Measurable (fun z : ℝ => Work.Spaces.w z) := by
  have h : (fun z : ℝ => Work.Spaces.w z) = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
  rw [h]
  have h1 : Measurable (fun z : ℝ => (1 + z) ^ 2) :=
    (measurable_const.add measurable_id).pow_const 2
  have h2 : Measurable (fun z : ℝ => z ^ 2) := measurable_id.pow_const 2
  exact h1.div h2

theorem pth_const_mul (c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * g z θ) = fun z θ => c * Work.Spaces.pth g z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  rw [deriv_const_mul_field]

theorem pz_const_mul (c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * g z θ) = fun z θ => c * Work.Spaces.pz g z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [deriv_const_mul_field]

theorem DzIter_const_mul (c : ℝ) (i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.DzIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      show z * Work.Spaces.pz (fun z θ => c * Work.Spaces.DzIter i g z θ) z θ
        = c * (z * Work.Spaces.pz (Work.Spaces.DzIter i g) z θ)
      rw [pz_const_mul]
      ring

theorem DzIter_const_mul_apply (c : ℝ) (i : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter i (fun z θ => c * g z θ) z θ = c * Work.Spaces.DzIter i g z θ := by
  simpa using congrFun (congrFun (DzIter_const_mul c i g) z) θ

theorem DthIter_const_mul (c : ℝ) (i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      show Real.sin (2 * θ) * Work.Spaces.pth (fun z θ => c * Work.Spaces.DthIter i g z θ) z θ
        = c * (Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DthIter i g) z θ)
      rw [pth_const_mul]
      ring

theorem mixed_const_mul (c : ℝ) (j i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.mixed j i g z θ := by
  rw [Work.Spaces.mixed, Work.Spaces.mixed, DthIter_const_mul, DzIter_const_mul]

theorem mixed_const_mul_apply (c : ℝ) (j i : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * g z θ) z θ
      = c * Work.Spaces.mixed j i g z θ := by
  simpa using congrFun (congrFun (mixed_const_mul c j i g) z) θ

theorem DzIter_succ_apply_pt (j : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter j (Work.Spaces.Dz g) z θ = Work.Spaces.DzIter (j + 1) g z θ := by
  simpa using congrFun (congrFun (Work.Blocks.DzIter_succ_apply j g) z) θ

theorem aesm_finset_sum {ι : Type*} {s : Finset ι} {φ : ι → ℝ → ℝ}
    {μ : MeasureTheory.Measure ℝ}
    (h : ∀ i ∈ s, AEStronglyMeasurable (φ i) μ) :
    AEStronglyMeasurable (fun a : ℝ => ∑ i ∈ s, φ i a) μ := by
  have h' : (fun a : ℝ => ∑ i ∈ s, φ i a) = ∑ i ∈ s, φ i := by
    funext a
    simp only [Finset.sum_apply]
  rw [h']
  exact Finset.aestronglyMeasurable_sum s h

theorem aesm_ite_pos {c : Prop} [Decidable c] {f : ℝ → ℝ} {μ : MeasureTheory.Measure ℝ}
    (hc : c) (h : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun a : ℝ => if c then f a else 0) μ := by
  have h' : (fun a : ℝ => if c then f a else 0) = f := by
    funext a; rw [if_pos hc]
  rwa [h']

theorem aesm_ite_neg {c : Prop} [Decidable c] {f : ℝ → ℝ} {μ : MeasureTheory.Measure ℝ}
    (hc : ¬c) :
    AEStronglyMeasurable (fun a : ℝ => if c then f a else 0) μ := by
  have h' : (fun a : ℝ => if c then f a else 0) = fun _ => (0 : ℝ) := by
    funext a; rw [if_neg hc]
  rw [h']
  exact aestronglyMeasurable_const

theorem mixIntS_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ Work.EllipticEst.Core.mixIntS u z := by
  rw [Work.EllipticEst.Core.mixIntS]
  exact mul_nonneg (sq_nonneg _)
    (MeasureTheory.setIntegral_nonneg measurableSet_Iθ
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))

theorem mixedIntS_nonneg (α : ℝ) (i j : ℕ) (u : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ Work.EllipticEst.Core.mixedIntS α i j u z := by
  rw [Work.EllipticEst.Core.mixedIntS]
  exact mul_nonneg (sq_nonneg _)
    (MeasureTheory.setIntegral_nonneg measurableSet_Iθ
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hθ)))

theorem lhsZ_nonneg (V : ℝ → ℝ → ℝ) (r : ℕ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ lhsZ V r z θ := by
  rw [lhsZ]
  exact mul_nonneg (sq_nonneg _)
    (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))

theorem lhsM_nonneg (α : ℝ) (k : ℕ) (V : ℝ → ℝ → ℝ) (i j : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ lhsM α k V i j z θ := by
  rw [lhsM]
  split_ifs with hc
  · exact mul_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hθ))
  · exact le_refl 0

theorem thEta_zero_left : Work.FTS.EllipticEst.thEta 0 = 0 := by
  rw [Work.FTS.EllipticEst.thEta, show (2 : ℝ) * 0 = 0 from by ring, Real.sin_zero,
    Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]

theorem thEta_zero_right : Work.FTS.EllipticEst.thEta (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.thEta, show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring,
    Real.sin_pi, Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]

theorem thGam_zero_left {α : ℝ} (hα : 0 < α) : Work.FTS.EllipticEst.thGam α 0 = 0 := by
  rw [Work.FTS.EllipticEst.thGam, show (2 : ℝ) * 0 = 0 from by ring, Real.sin_zero,
    Real.zero_rpow (by rw [Work.Spaces.gam]; intro hc; linarith)]

theorem thGam_zero_right {α : ℝ} (hα : 0 < α) :
    Work.FTS.EllipticEst.thGam α (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.thGam, show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring,
    Real.sin_pi, Real.zero_rpow (by rw [Work.Spaces.gam]; intro hc; linarith)]

theorem lhsZ_zero_z (V : ℝ → ℝ → ℝ) (r : ℕ) (θ : ℝ) : lhsZ V r 0 θ = 0 := by
  have hw : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
  rw [lhsZ, hw]
  ring

theorem lhsM_zero_z (α : ℝ) (k : ℕ) (V : ℝ → ℝ → ℝ) (i j : ℕ) (θ : ℝ) :
    lhsM α k V i j 0 θ = 0 := by
  have hw : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
  rw [lhsM]
  split_ifs with hc
  · rw [hw]; ring
  · rfl

theorem lhsZ_of_thEta_zero (V : ℝ → ℝ → ℝ) (r : ℕ) {z θ : ℝ}
    (h : Work.FTS.EllipticEst.thEta θ = 0) : lhsZ V r z θ = 0 := by
  rw [lhsZ, h, mul_zero, mul_zero]

theorem lhsM_of_thGam_zero (α : ℝ) (k : ℕ) (V : ℝ → ℝ → ℝ) (i j : ℕ) {z θ : ℝ}
    (h : Work.FTS.EllipticEst.thGam α θ = 0) : lhsM α k V i j z θ = 0 := by
  rw [lhsM]
  split_ifs with hc
  · rw [h, mul_zero, mul_zero]
  · rfl

theorem HkIntegrand_eq_zero_of_weights {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hH : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0)
    (hW : Work.Spaces.Wt α z θ = 0) :
    Work.Spaces.HkIntegrand α k f z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  simp [hH, hW]

/-! ## The `θ`-integrals of the two families -/

theorem lhsZ_integral (V : ℝ → ℝ → ℝ) (r : ℕ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, lhsZ V r z θ)
      = Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z := by
  simp only [lhsZ, Work.EllipticEst.Core.mixIntS]
  rw [MeasureTheory.integral_const_mul]

theorem lhsM_integral (α : ℝ) (k : ℕ) (V : ℝ → ℝ → ℝ) (i j : ℕ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, lhsM α k V i j z θ)
      = (if 1 ≤ i ∧ i + j ≤ k then Work.EllipticEst.Core.mixedIntS α i j V z else 0) := by
  by_cases hc : 1 ≤ i ∧ i + j ≤ k
  · simp only [lhsM, if_pos hc, Work.EllipticEst.Core.mixedIntS]
    rw [MeasureTheory.integral_const_mul]
  · simp only [lhsM, if_neg hc, MeasureTheory.integral_zero]

/-! ## Subadditivity of the (Bochner) integral over nonnegative, a.e. strongly measurable
summands -/

/-- For nonnegative a.e. strongly measurable summands, the integral of the sum is bounded by
the sum of the integrals.  (The a.e. strong measurability cannot be dropped: without it the
Bochner integral of a summand may be junk `0` while the integral of the sum is not.) -/
theorem setIntegral_finset_sum_le {ι : Type*} (s : Set ℝ) (hs : MeasurableSet s) (t : Finset ι)
    (φ : ι → ℝ → ℝ)
    (hnn : ∀ i ∈ t, ∀ a ∈ s, 0 ≤ φ i a)
    (hsm : ∀ i ∈ t, AEStronglyMeasurable (φ i) (MeasureTheory.volume.restrict s)) :
    (∫ a in s, ∑ i ∈ t, φ i a) ≤ ∑ i ∈ t, ∫ a in s, φ i a := by
  by_cases h : IntegrableOn (fun a => ∑ i ∈ t, φ i a) s
  · have hEach : ∀ i ∈ t, IntegrableOn (φ i) s := by
      intro i hi
      refine MeasureTheory.Integrable.mono' h (hsm i hi) ?_
      exact MeasureTheory.ae_restrict_of_forall_mem hs (fun a ha => by
        rw [Real.norm_of_nonneg (hnn i hi a ha)]
        exact Finset.single_le_sum (fun j hj => hnn j hj a ha) hi)
    rw [MeasureTheory.integral_finsetSum t hEach]
  · rw [MeasureTheory.integral_undef h]
    exact Finset.sum_nonneg fun i hi => MeasureTheory.setIntegral_nonneg hs (hnn i hi)

/-- The two-term case of `setIntegral_finset_sum_le`. -/
theorem setIntegral_add_le (s : Set ℝ) (hs : MeasurableSet s) {f g : ℝ → ℝ}
    (hf : ∀ a ∈ s, 0 ≤ f a) (hg : ∀ a ∈ s, 0 ≤ g a)
    (hfm : AEStronglyMeasurable f (MeasureTheory.volume.restrict s))
    (hgm : AEStronglyMeasurable g (MeasureTheory.volume.restrict s)) :
    (∫ a in s, (f a + g a)) ≤ (∫ a in s, f a) + ∫ a in s, g a := by
  by_cases h : IntegrableOn (fun a => f a + g a) s
  · have hfint : IntegrableOn f s :=
      MeasureTheory.Integrable.mono' h hfm
        (MeasureTheory.ae_restrict_of_forall_mem hs (fun a ha => by
          rw [Real.norm_of_nonneg (hf a ha)]; exact le_add_of_nonneg_right (hg a ha)))
    have hgint : IntegrableOn g s :=
      MeasureTheory.Integrable.mono' h hgm
        (MeasureTheory.ae_restrict_of_forall_mem hs (fun a ha => by
          rw [Real.norm_of_nonneg (hg a ha)]; exact le_add_of_nonneg_left (hf a ha)))
    rw [MeasureTheory.integral_add hfint hgint]
  · rw [MeasureTheory.integral_undef h]
    exact add_nonneg (MeasureTheory.setIntegral_nonneg hs hf)
      (MeasureTheory.setIntegral_nonneg hs hg)

/-! ## A.e. strong measurability of the pieces -/

theorem lhsZ_slice_aesm {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun θ : ℝ => lhsZ V r z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · have hzero : (fun θ : ℝ => lhsZ V r z θ) = fun _ => (0 : ℝ) := by
      funext θ; rw [← hz0]; exact lhsZ_zero_z V r θ
    rw [hzero]; exact aestronglyMeasurable_const
  · have hX : ContinuousOn (fun θ : ℝ =>
        Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      (((hV.DzIter r).pth).Dz).curry_θ hzpos |>.continuousOn
    have hT : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ)
        (Set.Ioo 0 (Real.pi / 2)) := by
      have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
      have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
        intro θ hθ
        exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos]))
      have h := hsin.rpow_const (p := -(Work.Spaces.eta))
        (fun θ hθ => Or.inl (hne θ hθ))
      simpa only [Work.FTS.EllipticEst.thEta] using h
    have hcont : ContinuousOn (fun θ : ℝ => lhsZ V r z θ) (Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContinuousOn (fun θ : ℝ =>
          (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2)
          (Set.Ioo 0 (Real.pi / 2)) := hX.pow 2
      have h2 := (h1.mul hT).const_mul ((Work.Spaces.w z) ^ 2)
      simpa only [lhsZ, Pi.mul_apply] using h2
    have h1 : AEStronglyMeasurable (fun θ : ℝ => lhsZ V r z θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      ContinuousOn.aestronglyMeasurable (μ := MeasureTheory.volume) hcont measurableSet_Ioo
    have heq : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
      rw [Work.Spaces.Iθ]
      exact (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
    rwa [heq]

theorem lhsM_slice_aesm {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (α : ℝ)
    (k : ℕ) (i j : ℕ) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun θ : ℝ => lhsM α k V i j z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  by_cases hc : 1 ≤ i ∧ i + j ≤ k
  · rw [show (fun θ : ℝ => lhsM α k V i j z θ) = fun θ : ℝ =>
        (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ) from by
      funext θ; rw [lhsM, if_pos hc]]
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · have hzero : (fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ)) = fun _ => (0 : ℝ) := by
        funext θ; rw [← hz0]; simp [Work.Spaces.w]
      rw [hzero]; exact aestronglyMeasurable_const
    · have hX : ContinuousOn (fun θ : ℝ =>
          Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ)
          (Set.Ioo 0 (Real.pi / 2)) :=
        ((hV.pth).mixed (j + 1) i).curry_θ hzpos |>.continuousOn
      have hT : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thGam α θ)
          (Set.Ioo 0 (Real.pi / 2)) := by
        have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
          (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
        have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
          intro θ hθ
          exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
            (by linarith [hθ.2, Real.pi_pos]))
        have h := hsin.rpow_const (p := -(Work.Spaces.gam α))
          (fun θ hθ => Or.inl (hne θ hθ))
        simpa only [Work.FTS.EllipticEst.thGam] using h
      have hcont : ContinuousOn (fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ)) (Set.Ioo 0 (Real.pi / 2)) :=
        (((hX.pow 2).mul hT)).const_mul ((Work.Spaces.w z) ^ 2)
      have h1 : AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ))
          (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
        ContinuousOn.aestronglyMeasurable (μ := MeasureTheory.volume) hcont measurableSet_Ioo
      have heq : MeasureTheory.volume.restrict Work.Spaces.Iθ
          = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
        rw [Work.Spaces.Iθ]
        exact (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
      rwa [heq]
  · rw [show (fun θ : ℝ => lhsM α k V i j z θ) = fun _ => (0 : ℝ) from by
      funext θ; rw [lhsM, if_neg hc]]
    exact aestronglyMeasurable_const

/-- `z ↦ mixIntS (D_z^r V) z` is a.e. strongly measurable. -/
theorem mixIntS_aesm {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ) :
    AEStronglyMeasurable (fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.thEta p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hX : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (((hV.DzIter r).pth).Dz).continuousOn
    have hT : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
      have hne : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)),
          Real.sin (2 * p.2) ≠ 0 := by
        intro p hp
        exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
          (by linarith [hp.2.2, Real.pi_pos]))
      have h := hsin.rpow_const (p := -(Work.Spaces.eta))
        (fun p hp => Or.inl (hne p hp))
      simpa only [Work.FTS.EllipticEst.thEta] using h
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hX.pow 2
    exact h1.mul hT
  have haesm := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have hint : AEStronglyMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    haesm.integral_prod_right'
  have hprod : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ)) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((measurable_w.pow_const 2).aestronglyMeasurable).mul hint
  simpa only [Work.EllipticEst.Core.mixIntS] using hprod

/-- `z ↦ mixedIntS α i j V z` is a.e. strongly measurable. -/
theorem mixedIntS_aesm {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (α : ℝ)
    (i j : ℕ) :
    AEStronglyMeasurable (fun z : ℝ => Work.EllipticEst.Core.mixedIntS α i j V z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.thGam α p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hX : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := ((hV.pth).mixed (j + 1) i).continuousOn
    have hT : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thGam α p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
      have hne : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)),
          Real.sin (2 * p.2) ≠ 0 := by
        intro p hp
        exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
          (by linarith [hp.2.2, Real.pi_pos]))
      have h := hsin.rpow_const (p := -(Work.Spaces.gam α))
        (fun p hp => Or.inl (hne p hp))
      simpa only [Work.FTS.EllipticEst.thGam] using h
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hX.pow 2
    exact h1.mul hT
  have haesm := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have hint : AEStronglyMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    haesm.integral_prod_right'
  have hprod : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ)) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((measurable_w.pow_const 2).aestronglyMeasurable).mul hint
  simpa only [Work.EllipticEst.Core.mixedIntS] using hprod

/-! ## The pointwise value decomposition of the `ℋ^k`-integrand -/

theorem HkIntegrand_alpha_Dz_pth {k : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V) (hα : 0 < α) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
        = α ^ 2 * ((∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
            + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), lhsM α k V i j z θ)) := by
  intro z hz θ hθ
  by_cases hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0
  · -- interior: the Clairaut identities apply
    have hZterm : ∀ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = α ^ 2 * lhsZ V i z θ := by
      intro i hi
      have hid : Work.Spaces.DzIter i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
          = α * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter i V)) z θ := by
        rw [DzIter_const_mul_apply, DzIter_succ_apply_pt, OpIdentDz hV i hQ]
      rw [hid]
      have hY : (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
          = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
        Work.EllipticEst.Core.w_div_sin_sq_eq z hθ
      calc (α * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter i V)) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = α ^ 2 * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter i V)) z θ) ^ 2
              * ((Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2) := by ring
        _ = α ^ 2 * lhsZ V i z θ := by rw [lhsZ, hY]; ring
    have hMterm : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
          = α ^ 2 * lhsM α k V i j z θ := by
      intro i hi j hj
      have hid : Work.Spaces.mixed j i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
          = α * Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ := by
        rw [mixed_const_mul_apply, OpIdentMixed hV i j hQ]
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · have hRHS : lhsM α k V i j z θ
            = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
                * Work.FTS.EllipticEst.thGam α θ) := by
          rw [lhsM, if_pos hc]
        rw [if_pos hc, hid, hRHS]
        have hY : (Work.Spaces.Wt α z θ) ^ 2
            = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ :=
          Work.EllipticEst.Core.Wt_sq_eq hα z hθ
        calc (α * Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ
                * Work.Spaces.Wt α z θ) ^ 2
            = α ^ 2 * (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
                * (Work.Spaces.Wt α z θ) ^ 2 := by ring
          _ = α ^ 2 * ((Work.Spaces.w z) ^ 2
                * ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
                  * Work.FTS.EllipticEst.thGam α θ)) := by rw [hY]; ring
      · have hLHS : (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0) = 0 := by rw [if_neg hc]
        have hRHS : lhsM α k V i j z θ = 0 := by rw [lhsM, if_neg hc]
        rw [hLHS, hRHS, mul_zero]
    rw [Work.Spaces.HkIntegrand]
    have hZ : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = α ^ 2 * ∑ i ∈ Finset.range (k + 1), lhsZ V i z θ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i hi => hZterm i hi)
    have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = α ^ 2 * ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            lhsM α k V i j z θ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j hj => hMterm i hi j hj)
    rw [hZ, hM]
    ring
  · -- boundary: both sides vanish
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0]
      rw [Work.Blocks.HkIntegrand_zero_z]
      rw [show (∑ r ∈ Finset.range (k + 1), lhsZ V r 0 θ) = 0 from
        Finset.sum_eq_zero (fun r _ => lhsZ_zero_z V r θ)]
      rw [show (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          lhsM α k V i j 0 θ) = 0 from
        Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => lhsM_zero_z α k V i j θ))]
      ring
    · -- `z > 0` and `¬ Q0` force `θ = 0` or `θ = π/2`
      have hθb : θ = 0 ∨ θ = Real.pi / 2 := by
        rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
        rcases eq_or_lt_of_le hθ.1 with h0 | h0
        · exact Or.inl h0.symm
        · rcases eq_or_lt_of_le hθ.2 with h2 | h2
          · exact Or.inr h2
          · exact absurd ⟨hzpos, h0, h2⟩ hQ
      have hH : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
        rcases hθb with h0 | hpi
        · rw [h0, show (2 : ℝ) * 0 = 0 from by ring, Real.sin_zero,
            Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num), div_zero]
        · rw [hpi, show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi,
            Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num), div_zero]
      have hW : Work.Spaces.Wt α z θ = 0 := by
        rw [Work.Spaces.Wt, Work.Spaces.wTheta]
        rcases hθb with h0 | hpi
        · rw [h0, show (2 : ℝ) * 0 = 0 from by ring, Real.sin_zero,
            Real.zero_rpow (by rw [Work.Spaces.gam]; intro hc; linarith), mul_zero]
        · rw [hpi, show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi,
            Real.zero_rpow (by rw [Work.Spaces.gam]; intro hc; linarith), mul_zero]
      rw [HkIntegrand_eq_zero_of_weights hH hW]
      rw [show (∑ r ∈ Finset.range (k + 1), lhsZ V r z θ) = 0 from by
        refine Finset.sum_eq_zero (fun r _ => ?_)
        rcases hθb with h0 | hpi
        · exact lhsZ_of_thEta_zero V r (by rw [h0]; exact thEta_zero_left)
        · exact lhsZ_of_thEta_zero V r (by rw [hpi]; exact thEta_zero_right)]
      rw [show (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          lhsM α k V i j z θ) = 0 from by
        refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
        rcases hθb with h0 | hpi
        · exact lhsM_of_thGam_zero α k V i j (by rw [h0]; exact thGam_zero_left hα)
        · exact lhsM_of_thGam_zero α k V i j (by rw [hpi]; exact thGam_zero_right hα)]
      ring

/-! ## The main statement -/

theorem LHSDecomp (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α →
      Work.FTS.EllipticEst.SmoothOpen V →
      MeasureTheory.IntegrableOn (fun z : ℝ =>
          α ^ 2 * (∑ r ∈ Finset.range (k + 1),
              Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
          + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                Work.EllipticEst.Core.mixedIntS α i j V z
              else 0)) Work.Spaces.Iz →
      Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
        ≤ C * (α ^ 2 * (∑ r ∈ Finset.range (k + 1),
                  ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
            + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then
                  ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
                else 0)) := by
  refine ⟨1, one_pos, ?_⟩
  intro α V hα hV hint
  -- the two families of `z`-integrands
  set A : ℝ → ℝ := fun z => ∑ r ∈ Finset.range (k + 1),
      Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z with hA
  set B : ℝ → ℝ := fun z => ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then Work.EllipticEst.Core.mixedIntS α i j V z else 0) with hB
  set T : ℝ → ℝ := fun z => α ^ 2 * (A z + B z) with hT
  -- the hypothesis, in the form of the statement's integrand
  have hintT : MeasureTheory.IntegrableOn T Work.Spaces.Iz := by
    rw [hT, hA, hB]
    simpa only [mul_add] using hint
  have hTnonneg : ∀ z : ℝ, 0 ≤ T z := by
    intro z
    rw [hT]
    refine mul_nonneg (sq_nonneg α) (add_nonneg ?_ ?_)
    · rw [hA]; exact Finset.sum_nonneg fun r _ => mixIntS_nonneg _ _
    · rw [hB]
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
        by_cases hc : 1 ≤ i ∧ i + j ≤ k
        · rw [if_pos hc]; exact mixedIntS_nonneg α i j V z
        · rw [if_neg hc]
  -- a.e. strong measurability of the two `z`-integrands
  have hAaesm : AEStronglyMeasurable A (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [hA]
    exact aesm_finset_sum (fun r _ => mixIntS_aesm hV r)
  have hBaesm : AEStronglyMeasurable B (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [hB]
    refine aesm_finset_sum (fun i _ => ?_)
    exact aesm_finset_sum (fun j _ => by
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · exact aesm_ite_pos hc (mixedIntS_aesm hV α i j)
      · exact aesm_ite_neg hc)
  -- the `θ`-level bound
  have hzle : ∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ)
        ≤ T z := by
    intro z hz
    have hrew : (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ)
        = α ^ 2 * (∫ θ in Work.Spaces.Iθ,
            ((∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
              + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                  lhsM α k V i j z θ)) := by
      rw [MeasureTheory.setIntegral_congr_fun (μ := MeasureTheory.volume)
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Iθ)
        (fun θ hθ => HkIntegrand_alpha_Dz_pth hV hα z hz θ hθ)]
      rw [MeasureTheory.integral_const_mul]
    rw [hrew, hT]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg α)
    have hsumZ_aesm : AEStronglyMeasurable
        (fun θ : ℝ => ∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      aesm_finset_sum (fun r _ => lhsZ_slice_aesm hV r hz)
    have hsumM_aesm : AEStronglyMeasurable
        (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          lhsM α k V i j z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      aesm_finset_sum (fun i _ => aesm_finset_sum (fun j _ => lhsM_slice_aesm hV α k i j hz))
    have h1 : (∫ θ in Work.Spaces.Iθ,
          ((∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), lhsM α k V i j z θ))
        ≤ (∫ θ in Work.Spaces.Iθ, ∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
          + (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1),
              ∑ j ∈ Finset.range (k + 1), lhsM α k V i j z θ) :=
      setIntegral_add_le Work.Spaces.Iθ measurableSet_Iθ
        (fun θ hθ => Finset.sum_nonneg fun r _ => lhsZ_nonneg V r hθ)
        (fun θ hθ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          lhsM_nonneg α k V i j hθ)
        hsumZ_aesm hsumM_aesm
    have h2 : (∫ θ in Work.Spaces.Iθ, ∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
        ≤ ∑ r ∈ Finset.range (k + 1), ∫ θ in Work.Spaces.Iθ, lhsZ V r z θ :=
      setIntegral_finset_sum_le Work.Spaces.Iθ measurableSet_Iθ (Finset.range (k + 1))
        (fun r θ => lhsZ V r z θ)
        (fun r _ θ hθ => lhsZ_nonneg V r hθ)
        (fun r _ => lhsZ_slice_aesm hV r hz)
    have h3 : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1),
          ∑ j ∈ Finset.range (k + 1), lhsM α k V i j z θ)
        ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            ∫ θ in Work.Spaces.Iθ, lhsM α k V i j z θ := by
      refine le_trans (setIntegral_finset_sum_le Work.Spaces.Iθ measurableSet_Iθ
        (Finset.range (k + 1))
        (fun i θ => ∑ j ∈ Finset.range (k + 1), lhsM α k V i j z θ)
        (fun i _ θ hθ => Finset.sum_nonneg fun j _ => lhsM_nonneg α k V i j hθ)
        (fun i _ => aesm_finset_sum (fun j _ => lhsM_slice_aesm hV α k i j hz))) ?_
      exact Finset.sum_le_sum (fun i _ => setIntegral_finset_sum_le Work.Spaces.Iθ
        measurableSet_Iθ (Finset.range (k + 1)) (fun j θ => lhsM α k V i j z θ)
        (fun j _ θ hθ => lhsM_nonneg α k V i j hθ)
        (fun j _ => lhsM_slice_aesm hV α k i j hz))
    have h4 : (∑ r ∈ Finset.range (k + 1), ∫ θ in Work.Spaces.Iθ, lhsZ V r z θ) = A z := by
      rw [hA]
      exact Finset.sum_congr rfl (fun r _ => lhsZ_integral V r z)
    have h5 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          ∫ θ in Work.Spaces.Iθ, lhsM α k V i j z θ) = B z := by
      rw [hB]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
        lhsM_integral α k V i j z))
    calc (∫ θ in Work.Spaces.Iθ,
          ((∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), lhsM α k V i j z θ))
        ≤ (∫ θ in Work.Spaces.Iθ, ∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
          + (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1),
              ∑ j ∈ Finset.range (k + 1), lhsM α k V i j z θ) := h1
      _ ≤ (∑ r ∈ Finset.range (k + 1), ∫ θ in Work.Spaces.Iθ, lhsZ V r z θ)
          + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              ∫ θ in Work.Spaces.Iθ, lhsM α k V i j z θ) := add_le_add h2 h3
      _ = A z + B z := by simp only [h4, h5]
  -- the `z`-level bound
  have hzT : (∫ z in Work.Spaces.Iz, T z)
      ≤ α ^ 2 * (∑ r ∈ Finset.range (k + 1),
            ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
        + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
            else 0) := by
    have hTexp : (∫ z in Work.Spaces.Iz, T z) = α ^ 2 * ∫ z in Work.Spaces.Iz, (A z + B z) := by
      rw [hT]
      exact MeasureTheory.integral_const_mul _ _
    rw [hTexp]
    have h1 : (∫ z in Work.Spaces.Iz, (A z + B z))
        ≤ (∫ z in Work.Spaces.Iz, A z) + ∫ z in Work.Spaces.Iz, B z :=
      setIntegral_add_le Work.Spaces.Iz measurableSet_Iz
        (fun z _ => by rw [hA]; exact Finset.sum_nonneg fun r _ => mixIntS_nonneg _ _)
        (fun z _ => by
          rw [hB]
          exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
            by_cases hc : 1 ≤ i ∧ i + j ≤ k
            · rw [if_pos hc]; exact mixedIntS_nonneg α i j V z
            · rw [if_neg hc])
        hAaesm hBaesm
    have h2 : (∫ z in Work.Spaces.Iz, A z)
        ≤ ∑ r ∈ Finset.range (k + 1),
            ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z := by
      rw [hA]
      exact setIntegral_finset_sum_le Work.Spaces.Iz measurableSet_Iz (Finset.range (k + 1))
        (fun r z => Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
        (fun r _ z _ => mixIntS_nonneg _ _) (fun r _ => mixIntS_aesm hV r)
    have h3 : (∫ z in Work.Spaces.Iz, B z)
        ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
            else 0 := by
      have hnnij : ∀ i j : ℕ, ∀ z ∈ Work.Spaces.Iz,
          0 ≤ (if 1 ≤ i ∧ i + j ≤ k then
            Work.EllipticEst.Core.mixedIntS α i j V z else 0) := by
        intro i j z hz
        by_cases hc : 1 ≤ i ∧ i + j ≤ k
        · rw [if_pos hc]; exact mixedIntS_nonneg α i j V z
        · rw [if_neg hc]
      have haesmij : ∀ i j : ℕ, AEStronglyMeasurable
          (fun z : ℝ => if 1 ≤ i ∧ i + j ≤ k then
            Work.EllipticEst.Core.mixedIntS α i j V z else 0)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
        intro i j
        by_cases hc : 1 ≤ i ∧ i + j ≤ k
        · exact aesm_ite_pos hc (mixedIntS_aesm hV α i j)
        · exact aesm_ite_neg hc
      rw [hB]
      calc (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then Work.EllipticEst.Core.mixedIntS α i j V z else 0))
          ≤ ∑ i ∈ Finset.range (k + 1), ∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then Work.EllipticEst.Core.mixedIntS α i j V z else 0) :=
            setIntegral_finset_sum_le Work.Spaces.Iz measurableSet_Iz (Finset.range (k + 1))
              (fun i z => ∑ j ∈ Finset.range (k + 1),
                (if 1 ≤ i ∧ i + j ≤ k then Work.EllipticEst.Core.mixedIntS α i j V z else 0))
              (fun i _ z hz => Finset.sum_nonneg fun j _ => hnnij i j z hz)
              (fun i _ => aesm_finset_sum (fun j _ => haesmij i j))
        _ ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              ∫ z in Work.Spaces.Iz,
                (if 1 ≤ i ∧ i + j ≤ k then Work.EllipticEst.Core.mixedIntS α i j V z else 0) :=
            Finset.sum_le_sum (fun i _ => setIntegral_finset_sum_le Work.Spaces.Iz
              measurableSet_Iz (Finset.range (k + 1))
              (fun j z => (if 1 ≤ i ∧ i + j ≤ k then
                Work.EllipticEst.Core.mixedIntS α i j V z else 0))
              (fun j _ z hz => hnnij i j z hz) (fun j _ => haesmij i j))
        _ = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then
                ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z else 0) := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
            by_cases hc : 1 ≤ i ∧ i + j ≤ k
            · simp only [if_pos hc]
            · simp only [if_neg hc, MeasureTheory.integral_zero]
    calc α ^ 2 * (∫ z in Work.Spaces.Iz, (A z + B z))
        ≤ α ^ 2 * ((∫ z in Work.Spaces.Iz, A z) + ∫ z in Work.Spaces.Iz, B z) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg α)
      _ ≤ α ^ 2 * ((∑ r ∈ Finset.range (k + 1),
              ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
            + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then
                  ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
                else 0)) := mul_le_mul_of_nonneg_left (add_le_add h2 h3) (sq_nonneg α)
      _ = α ^ 2 * (∑ r ∈ Finset.range (k + 1),
              ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
            + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then
                  ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
                else 0) := by ring
  -- the smoothness hypothesis for `HkSq_eq_lintegral`
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    have h1 : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth V)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hV.pth).Dz |>.forall n
    have h3 := (contDiffOn_const (c := α)).mul h1
    have h4 : Function.uncurry (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
        = fun p : ℝ × ℝ => α * Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth V)) p := by
      funext p; rfl
    rwa [h4]
  -- the `lintegral` presentation of `HkSq`
  have hfin : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (T z)) ≠ ⊤ := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintT
      (Filter.Eventually.of_forall hTnonneg)]
    exact ENNReal.ofReal_ne_top
  have hbound : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (T z) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Iz
      (fun z hz => ENNReal.ofReal_le_ofReal (hzle z hz))
  calc Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
      = (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ)).toReal :=
        Work.FTS.EllipticEst.HkSq_eq_lintegral α k _ hsm
    _ ≤ (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (T z)).toReal :=
        ENNReal.toReal_mono hfin hbound
    _ = ∫ z in Work.Spaces.Iz, T z :=
        (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Iz
            (fun z _ => hTnonneg z)) hintT.aestronglyMeasurable).symm
    _ ≤ α ^ 2 * (∑ r ∈ Finset.range (k + 1),
            ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
          + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
              else 0) := hzT
    _ = 1 * (α ^ 2 * (∑ r ∈ Finset.range (k + 1),
              ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
            + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then
                  ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
                else 0)) := by ring

end

end Work.FTS.EllipticEst.RPFresh
end
-- ===== merged: Submission.Work.FTS.EllipticEst.TT.psiDerivSq_lower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The three ingredients

The proof of `psiDerivSq_lower` below is assembled from the three lemmas of this section:

* `integrableOn_sq_mul_sig_of_hkMem` extracts, from the `H^0`-honesty `HkMem α 0 g` and for
  `z > 0`, the `θ`-integrability of the single weighted square `g z θ² · σ θ` (the constant
  factor `w z² ≠ 0` of the level-`0` `HkIntegrand` is divided out);
* `deriv_divCos_eq` is the quotient rule for the slice variable `θ ↦ u θ / cos θ`;
* `div_cos_sq_le` is the numerical core `((a + t b)/c)² ≤ 4 (a² + b²)` valid when
  `0 < c`, `c² ≥ 1/2` and `t² ≤ 1` — precisely the regime `θ ∈ (0, π/4)` with
  `c = cos θ`, `t = tan θ`.

Their combination (`psi_deriv_sq_le`) is the pointwise bound `(ψ')² ≤ 4 f'² + 4 f²` on
`(0, π/4)`, which together with `Honest.sliceInterp` (giving `f'²σ ∈ L¹` from `f²σ`, `f''²σ`)
and `Integrable.mono'` yields the target. -/

/-- **Slice honesty of the level-`0` `HkMem`.**  For `z > 0` the single weighted square
`g z θ² · σ θ` (`σ = sin(2θ)^{-η}`) is integrable on `Iθ`.

At level `0` the `HkIntegrand` is `(g z θ · w z / sin(2θ)^{η/2})²`, i.e. `w z²` times the
present integrand (`remov.HkIntegrand_zero_eq`); since `w z ≠ 0` for `z > 0`, the constant
`w z²` can be divided out. -/
lemma integrableOn_sq_mul_sig_of_hkMem {α z : ℝ} {g : ℝ → ℝ → ℝ} (hz : 0 < z)
    (hmem : Work.Spaces.HkMem α 0 g) :
    MeasureTheory.IntegrableOn
      (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := by
    have h1 : Work.Spaces.w z ≠ 0 := by
      rw [Work.Spaces.w]
      exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
    exact pow_ne_zero 2 h1
  have hbase : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 0 g z θ * ((Work.Spaces.w z) ^ 2)⁻¹)
      Work.Spaces.Iθ :=
    (hmem.1 z hzI).mul_const _
  refine hbase.congr_fun (fun θ hθ => ?_) measurableSet_Icc
  show Work.Spaces.HkIntegrand α 0 g z θ * ((Work.Spaces.w z) ^ 2)⁻¹
    = (g z θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
  rw [Work.FTS.EllipticEst.remov.HkIntegrand_zero_eq α g z hθ,
    Work.FTS.EllipticEst.AngSecond.sig]
  calc (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
        * ((Work.Spaces.w z) ^ 2)⁻¹
      = (g z θ) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
          * ((Work.Spaces.w z) ^ 2 * ((Work.Spaces.w z) ^ 2)⁻¹) := by ring
    _ = (g z θ) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta) := by
        rw [mul_inv_cancel₀ hw, mul_one]

/-- **The quotient rule for the slice variable.**  If the slice `u` is differentiable at `θ` and
`cos θ ≠ 0`, then `∂_θ(u/cos θ) = (u' + tan θ · u)/cos θ` at `θ`. -/
lemma deriv_divCos_eq (u : ℝ → ℝ) {θ : ℝ} (hu : DifferentiableAt ℝ u θ)
    (hcos : Real.cos θ ≠ 0) :
    deriv (fun t => u t / Real.cos t) θ
      = (deriv u θ + Real.tan θ * u θ) / Real.cos θ := by
  change deriv (u / Real.cos) θ = (deriv u θ + Real.tan θ * u θ) / Real.cos θ
  rw [deriv_div hu Real.differentiableAt_cos hcos, Real.deriv_cos, Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- **Numerical core.**  If `0 < c`, `c² ≥ 1/2` and `t² ≤ 1` then `((a + t b)/c)² ≤ 4(a² + b²)`.
On `(0, π/4)` the hypotheses hold with `c = cos θ`, `t = tan θ`. -/
lemma div_cos_sq_le (a b t c : ℝ) (hc : 0 < c) (hc2 : (1 : ℝ) / 2 ≤ c ^ 2)
    (ht : t ^ 2 ≤ 1) : ((a + t * b) / c) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  have hc2pos : (0 : ℝ) < c ^ 2 := pow_pos hc 2
  have hsqab : (0 : ℝ) ≤ a ^ 2 + b ^ 2 := by positivity
  have hAB : (a + t * b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (a - t * b)]
  have hfac : (2 : ℝ) * (a ^ 2 + b ^ 2) ≤ 4 * (a ^ 2 + b ^ 2) * c ^ 2 := by
    have h1 : ((1 : ℝ) / 2) * (a ^ 2 + b ^ 2) ≤ c ^ 2 * (a ^ 2 + b ^ 2) :=
      mul_le_mul_of_nonneg_right hc2 hsqab
    linarith
  rw [div_pow, div_le_iff₀ hc2pos]
  linarith

/-- **The pointwise bound on the derivative of the slice variable** on the lower half
`(0, π/4)`.  For a slice `θ ↦ Ψ z θ` that is `C²` on `(0, π/2)`:

  `(∂_θ(Ψ z ·/cos))² ≤ 4 (∂_θΨ z ·)² + 4 (Ψ z ·)²`. -/
lemma psi_deriv_sq_le {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hslice : ContDiffOn ℝ 2 (fun t => Ψ z t) (Set.Ioo 0 (Real.pi / 2)))
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 4)) :
    (deriv (fun t => Ψ z t / Real.cos t) θ) ^ 2
      ≤ 4 * (deriv (fun t => Ψ z t) θ) ^ 2 + 4 * (Ψ z θ) ^ 2 := by
  obtain ⟨hθ0, hθ4⟩ := hθ
  have hθmid : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hθ0, by linarith [hθ4, Real.pi_pos]⟩
  have hcosp : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [hθmid.2, Real.pi_pos]⟩
  have hcosne : Real.cos θ ≠ 0 := ne_of_gt hcosp
  have hd : DifferentiableAt ℝ (fun t => Ψ z t) θ :=
    (hslice.contDiffAt (isOpen_Ioo.mem_nhds hθmid)).differentiableAt (by simp)
  have hcos2 : (1 : ℝ) / 2 ≤ Real.cos θ ^ 2 := by
    rw [Real.cos_sq]
    have h2 : 0 ≤ Real.cos (2 * θ) :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [Real.pi_pos], by linarith [hθmid.2, Real.pi_pos]⟩
    linarith
  have htan2 : (Real.tan θ) ^ 2 ≤ 1 := by
    have hmono : Real.tan θ < Real.tan (Real.pi / 4) :=
      Real.strictMonoOn_tan
        ⟨by linarith [Real.pi_pos], by linarith [hθmid.2, Real.pi_pos]⟩
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hθ4
    rw [Real.tan_pi_div_four] at hmono
    have hnn : 0 ≤ Real.tan θ :=
      Real.tan_nonneg_of_nonneg_of_le_pi_div_two hθ0.le (by linarith [hθmid.2])
    nlinarith
  rw [deriv_divCos_eq (fun t => Ψ z t) hd hcosne]
  have hkey := div_cos_sq_le (deriv (fun t => Ψ z t) θ) (Ψ z θ) (Real.tan θ) (Real.cos θ)
    hcosp hcos2 htan2
  nlinarith [hkey]

/-- The slice `θ ↦ Ψ z θ` of a function that is smooth on the open strip `(0,∞) × (0,π/2)` is
`Cⁿ` on the open interval `(0, π/2)`. -/
lemma contDiffOn_slice_of_strip {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) {z : ℝ} (hz : 0 < z) (n : ℕ) :
    ContDiffOn ℝ n (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hz, hθ⟩
  have hp : ContDiffOn ℝ n (fun θ : ℝ => (z, θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    contDiffOn_const.prodMk contDiffOn_id
  have h := (hsm n).comp hp hmap
  simpa [Function.comp_def, Function.uncurry] using h

/-- The slice variable `θ ↦ Ψ z θ / cos θ` is `C²` on `(0, π/2)` whenever the slice itself
is. -/
lemma contDiffOn_divCos {Ψ : ℝ → ℝ → ℝ} {z : ℝ}
    (hslice : ContDiffOn ℝ 2 (fun t => Ψ z t) (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ 2 (fun t => Ψ z t / Real.cos t) (Set.Ioo 0 (Real.pi / 2)) :=
  hslice.div Real.contDiff_cos.contDiffOn (fun t ht =>
    ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩))

/-- `σ = sin(2θ)^{-η}` is (Borel) measurable. -/
lemma measurable_sigEta : Measurable Work.FTS.EllipticEst.AngSecond.sig := by
  change Measurable (fun θ : ℝ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
  exact Measurable.pow_const (Real.measurable_sin.comp (measurable_const.mul measurable_id)) _


end Work.FTS.EllipticEst.TT
end
