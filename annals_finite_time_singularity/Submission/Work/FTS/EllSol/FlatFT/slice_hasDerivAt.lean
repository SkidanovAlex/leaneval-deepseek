/-
Copyright: work module for the Elgindi finite-time singularity project.

# Differentiation of the `t`-Fourier slice in the angle

For a `NiceFlat` datum `g` the slice `Φ_ξ(θ) = ∫_t g(t,θ) e^{-2πiξt} dt` is an absolutely
convergent integral (the `t`-support of `g` is uniformly compact), and the `θ`-derivatives
may be taken under the integral sign:

* `∂_θ Φ_ξ(θ) = ∫_t ∂_θ g(t,θ) e^{-2πiξt} dt`, i.e. the slice of `pth g`;
* `∂_θ² Φ_ξ(θ) = ∫_t ∂_θ²g(t,θ) e^{-2πiξt} dt`, i.e. the slice of `pth (pth g)`.

Both are instances of the parameter-differentiation theorem
`MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, applied with the measure
`volume.restrict (Icc (-M) M)` (where `M ≥ 0` bounds the `t`-support of `g`); the domination
comes from the compactness of the box `Icc (-M) M ×ˢ Icc (θ-ε) (θ+ε)` and the continuity of
`∂_θg` resp. `∂_θ²g` there, which is the finite-order smoothness of the `θ`-partial of a
`C^{n+1}` function on an open set.

The body of the argument is the auxiliary lemma `slice_hasDerivAt_aux`, stated for an
arbitrary `φ` (the datum, resp. its `θ`-partial) with compact `t`-support, of class `C¹` on
the strip `ℝ × (0,π/2)` whose `θ`-partial is continuous there; both conjuncts of the target
are then that lemma with `φ := g` and `φ := pth g`.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.EllSol.FlatFT.Defs

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
private def sliceStrp : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

private theorem isOpen_sliceStrp : IsOpen sliceStrp := isOpen_univ.prod isOpen_Ioo

/-! ## Finite-order smoothness of the `θ`-partial on an open set -/

/-- The `θ`-partial of a `C^{n+1}` function on an open set is `C^n` there.

This is the finite-order form of `Work.Spaces.contDiffOn_uncurry_pth` (the `C^∞` case),
following `Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin`. -/
private theorem pth_smooth {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1 : ℕ) (Function.uncurry G) sliceStrp) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) sliceStrp := by
  have hchain : ∀ p ∈ sliceStrp,
      Work.Spaces.pth G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by norm_num : (n + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (isOpen_sliceStrp.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) sliceStrp :=
    h.fderiv_of_isOpen isOpen_sliceStrp (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) sliceStrp :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  exact hchain p hp

/-! ## Continuity of the `t`-slices on the strip -/

/-- For `x ∈ (0,π/2)` the slice `t ↦ G t x` of a function which is `C^0` on the strip is
continuous. -/
private theorem continuous_slice {G : ℝ → ℝ → ℝ} {k : WithTop ℕ∞}
    (hG : ContDiffOn ℝ k (Function.uncurry G) sliceStrp) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :
    Continuous fun t : ℝ => G t x := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hmem : (t, x) ∈ sliceStrp := ⟨trivial, hx⟩
  have hca : ContDiffAt ℝ k (Function.uncurry G) (t, x) :=
    hG.contDiffAt (isOpen_sliceStrp.mem_nhds hmem)
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
private theorem slice_hasDerivAt_aux
    (φ : ℝ → ℝ → ℝ) (κ : ℝ → ℂ)
    (hφ : ContDiffOn ℝ 1 (Function.uncurry φ) sliceStrp)
    (hφ' : ContinuousOn (Function.uncurry (Work.Spaces.pth φ)) sliceStrp)
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
  have hBox : Set.Icc (-M) M ×ˢ Set.Icc (x₀ - ε) (x₀ + ε) ⊆ sliceStrp := by
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
    have hmem : (t, x₀) ∈ sliceStrp := ⟨trivial, hx₀⟩
    have hc : ContinuousAt (fun p : ℝ × ℝ => Work.Spaces.pth φ p.1 p.2) (t, x₀) :=
      hφ'.continuousAt (isOpen_sliceStrp.mem_nhds hmem)
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
    have hmem : (a, x) ∈ sliceStrp := ⟨trivial, hsub hx⟩
    have hd : DifferentiableAt ℝ (fun x' : ℝ => φ a x') x :=
      Work.Spaces.differentiableAt_curry_right
        ((hφ.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
          (isOpen_sliceStrp.mem_nhds hmem))
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
  have hpth1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth g)) sliceStrp :=
    pth_smooth (n := 1) hcd
  constructor
  · have h := slice_hasDerivAt_aux g (fun t => Complex.exp (-(2 * Real.pi * Complex.I * ξ * t)))
      (hcd.of_le (by norm_num)) hpth1.continuousOn hκc hκ1 hM hsupp hθ
    exact h
  · have hpth2 : ContDiffOn ℝ 0
        (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth g))) sliceStrp :=
      pth_smooth (n := 0) hpth1
    have hsupp2 : ∀ t θ', max N 0 < |t| → Work.Spaces.pth g t θ' = 0 := by
      intro t θ' ht
      simp only [Work.Spaces.pth]
      rw [show (fun y : ℝ => g t y) = fun _ => (0 : ℝ) from funext fun y => hsupp t y ht]
      simp
    have h := slice_hasDerivAt_aux (Work.Spaces.pth g)
      (fun t => Complex.exp (-(2 * Real.pi * Complex.I * ξ * t)))
      hpth1 hpth2.continuousOn hκc hκ1 hM hsupp2 hθ
    exact h

end

end Work.FTS.EllSol.FlatFT
