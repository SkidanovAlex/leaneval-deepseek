/-
Copyright: work module for the Elgindi finite-time singularity project.

# Smoothness of the `t`-Fourier slice in the angle

For a datum `φ : ℝ → ℝ → ℝ` which is `C^n` (`n ≤ 2`) on the open strip
`ℝ × (0, π/2)` and whose `t`-support is uniformly compact, the slice

`Φ(θ) = ∫_t φ(t,θ) e^{-2πiξt} dt`

is `C^n` on `(0, π/2)`.  The proof is the parameter-differentiation argument: since `φ`
vanishes for `|t| > M`, the defining integral is an integral over the compact set
`[-M,M]`; the integrand is jointly as smooth as `φ`, so all derivatives in `θ` may be
taken under the integral sign.

The file proves this by induction on `n`, using

* the `C^1` identity `∂_θ Φ(θ) = ∫_t (∂_θφ)(t,θ) e^{-2πiξt} dt` (derivative under the
  integral sign, Mathlib's `hasDerivAt_integral_of_dominated_loc_of_deriv_le`), and
* continuity of the parameterized integral
  (`continuousOn_integral_of_compact_support`),

together with the fact that the `θ`-partial of a `C^{n+1}` function on an open set is
`C^n` (`pth_contDiffOn_succ`, from the sibling file `pth_contDiffOn_succ.lean`).

The main theorem is `sliceContDiffOn`.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Have
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllSol.FlatFT.Defs
import Submission.Work.FTS.EllSol.FlatFT.pth_contDiffOn_succ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open scoped Real Topology ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The open strip, the angular interval and the oscillatory factor -/

/-- The open half-strip `ℝ × (0, π/2)` on which the datum is smooth. -/
abbrev sliceStrp : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- The angular interval `(0, π/2)`. -/
abbrev sliceSθ : Set ℝ := Set.Ioo 0 (Real.pi / 2)

/-- The oscillatory factor `t ↦ e^{-2πiξt}`. -/
abbrev sliceK (ξ : ℝ) : ℝ → ℂ := fun t => Complex.exp (-(2 * Real.pi * Complex.I * ξ * t))

theorem isOpen_sliceStrp : IsOpen sliceStrp := isOpen_univ.prod isOpen_Ioo

theorem isOpen_sliceSθ : IsOpen sliceSθ := isOpen_Ioo

theorem continuous_sliceK (ξ : ℝ) : Continuous (sliceK ξ) := by
  fun_prop

theorem norm_sliceK (ξ t : ℝ) : ‖sliceK ξ t‖ = 1 := by
  dsimp only [sliceK]
  rw [show -(2 * Real.pi * Complex.I * ξ * t) = (-(2 * Real.pi * ξ * t) : ℝ) * Complex.I from by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem slice_eq_integral_sliceK (ψ : ℝ → ℝ → ℝ) (ξ θ : ℝ) :
    slice ψ ξ θ = ∫ t, (ψ t θ : ℂ) * sliceK ξ t := rfl

/-! ## Continuity of the `t`-slices of a smooth function on the strip -/

/-- For `x ∈ (0,π/2)` the slice `t ↦ G t x` of a function which is `C^k` on the strip is
continuous. -/
theorem continuous_tslice {G : ℝ → ℝ → ℝ} {k : ℕ∞ω}
    (hG : ContDiffOn ℝ k (Function.uncurry G) sliceStrp) {x : ℝ}
    (hx : x ∈ sliceSθ) :
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
theorem abs_lt_of_notMem_Icc' {M t : ℝ} (hM : 0 ≤ M) (h : t ∉ Set.Icc (-M) M) :
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

/-! ## Parametric continuity -/

/-- The slice of a datum which is continuous on the strip and has uniformly compact
`t`-support is continuous on `(0, π/2)`. -/
theorem slice_continuousOn (ψ : ℝ → ℝ → ℝ) (ξ : ℝ)
    (hψ : ContDiffOn ℝ 0 (Function.uncurry ψ) sliceStrp)
    (hsupp : ∃ M : ℝ, 0 ≤ M ∧ ∀ t θ : ℝ, M < |t| → ψ t θ = 0) :
    ContinuousOn (fun θ : ℝ => slice ψ ξ θ) sliceSθ := by
  obtain ⟨M, hM, hsuppM⟩ := hsupp
  have hψc : ContinuousOn (Function.uncurry ψ) sliceStrp := contDiffOn_zero.mp hψ
  -- joint continuity of the integrand on the product of the angular interval with the line
  have hjoint : ContinuousOn (fun p : ℝ × ℝ => Function.uncurry ψ (p.2, p.1))
      (sliceSθ ×ˢ Set.univ) :=
    hψc.comp continuous_swap.continuousOn (fun p hp => ⟨trivial, hp.1⟩)
  have hf : ContinuousOn (Function.uncurry (fun θ t : ℝ => (ψ t θ : ℂ) * sliceK ξ t))
      (sliceSθ ×ˢ Set.univ) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => ((Function.uncurry ψ) (p.2, p.1) : ℂ))
        (sliceSθ ×ˢ Set.univ) := Complex.continuous_ofReal.comp_continuousOn hjoint
    have h2 : ContinuousOn (fun p : ℝ × ℝ => sliceK ξ p.2) (sliceSθ ×ˢ Set.univ) :=
      (continuous_sliceK ξ).comp_continuousOn continuous_snd.continuousOn
    refine (h1.mul h2).congr ?_
    intro p _
    rfl
  have hfs : ∀ θ : ℝ, ∀ x : ℝ, θ ∈ sliceSθ → x ∉ Set.Icc (-M) M →
      (fun θ t : ℝ => (ψ t θ : ℂ) * sliceK ξ t) θ x = 0 := by
    intro θ x _ hx
    show (ψ x θ : ℂ) * sliceK ξ x = 0
    rw [hsuppM x θ (abs_lt_of_notMem_Icc' hM hx), Complex.ofReal_zero, zero_mul]
  have hmain := continuousOn_integral_of_compact_support (μ := volume)
    (f := fun θ t : ℝ => (ψ t θ : ℂ) * sliceK ξ t)
    (s := sliceSθ) (k := Set.Icc (-M) M) isCompact_Icc hf hfs
  show ContinuousOn (fun θ : ℝ => ∫ t, (ψ t θ : ℂ) * sliceK ξ t) sliceSθ
  exact hmain

/-! ## Differentiation under the `t`-integral -/

/-- **Differentiation under the `t`-integral defining a slice.**

Let `φ` be of class `C¹` on the open strip `ℝ × (0,π/2)` with continuous `θ`-partial
there, let `φ` vanish for `M < |t|` with `M ≥ 0`, and let `κ` be continuous with
`‖κ t‖ = 1`.  Then for `x₀ ∈ (0,π/2)` the function `x ↦ ∫_t (φ t x : ℂ) · κ t` is
differentiable at `x₀` with derivative `∫_t (∂_θφ t x₀ : ℂ) · κ t`. -/
theorem slice_hasDerivAt_aux
    (φ : ℝ → ℝ → ℝ) (κ : ℝ → ℂ)
    (hφ : ContDiffOn ℝ 1 (Function.uncurry φ) sliceStrp)
    (hφ' : ContinuousOn (Function.uncurry (Work.Spaces.pth φ)) sliceStrp)
    (hκ : Continuous κ) (hκ1 : ∀ t, ‖κ t‖ = 1)
    {M : ℝ} (hM : 0 ≤ M) (hsupp : ∀ t θ, M < |t| → φ t θ = 0)
    {x₀ : ℝ} (hx₀ : x₀ ∈ sliceSθ) :
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
    have hcont : Continuous fun t : ℝ => φ t x := continuous_tslice hφ (hsub hx)
    exact ((Complex.continuous_ofReal.comp hcont).mul hκ).aestronglyMeasurable
  have hF_int : Integrable (fun t : ℝ => (φ t x₀ : ℂ) * κ t)
      (volume.restrict (Set.Icc (-M) M)) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc (a := -M) (b := M))
      ((Complex.continuous_ofReal.comp (continuous_tslice hφ hx₀)).mul hκ).continuousOn
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
    · rw [hpth_zero a (abs_lt_of_notMem_Icc' hM ha) x, Complex.ofReal_zero, zero_mul, norm_zero]
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
        ((hφ.differentiableOn (by norm_num : (1 : ℕ∞ω) ≠ 0)).differentiableAt
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
        rw [hsupp t x (abs_lt_of_notMem_Icc' hM ht), Complex.ofReal_zero, zero_mul])).symm
  have hdersupp : (∫ t in Set.Icc (-M) M, ((Work.Spaces.pth φ) t x₀ : ℂ) * κ t)
      = ∫ t, ((Work.Spaces.pth φ) t x₀ : ℂ) * κ t := by
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
    rw [hpth_zero t (abs_lt_of_notMem_Icc' hM ht) x₀, Complex.ofReal_zero, zero_mul]
  refine (hmain.congr_of_eventuallyEq ?_).congr_deriv hdersupp
  filter_upwards [hs] with x hx
  exact hsupp_int x hx

/-! ## The `θ`-derivative of the slice is the slice of the `θ`-partial -/

theorem slice_deriv_eq (ψ : ℝ → ℝ → ℝ) (ξ : ℝ)
    (hψ : ContDiffOn ℝ 1 (Function.uncurry ψ) sliceStrp)
    (hψ' : ContinuousOn (Function.uncurry (Work.Spaces.pth ψ)) sliceStrp)
    {M : ℝ} (hM : 0 ≤ M) (hsupp : ∀ t θ : ℝ, M < |t| → ψ t θ = 0) {θ : ℝ}
    (hθ : θ ∈ sliceSθ) :
    deriv (fun θ' : ℝ => slice ψ ξ θ') θ = slice (Work.Spaces.pth ψ) ξ θ :=
  (slice_hasDerivAt_aux ψ (sliceK ξ) hψ hψ' (continuous_sliceK ξ) (norm_sliceK ξ) hM hsupp hθ).deriv

/-! ## The induction -/

/-- The slice of a `C^k` datum with uniformly compact `t`-support is `C^k` on `(0,π/2)`. -/
theorem slice_contDiffOn_aux : ∀ (k : ℕ) (ψ : ℝ → ℝ → ℝ) (ξ : ℝ),
    ContDiffOn ℝ k (Function.uncurry ψ) sliceStrp →
      (∃ M : ℝ, 0 ≤ M ∧ ∀ t θ : ℝ, M < |t| → ψ t θ = 0) →
      ContDiffOn ℝ k (fun θ : ℝ => slice ψ ξ θ) sliceSθ := by
  intro k
  induction k with
  | zero =>
      intro ψ ξ hψ hsupp
      exact contDiffOn_zero.mpr (slice_continuousOn ψ ξ hψ hsupp)
  | succ k ih =>
      intro ψ ξ hψ hsupp
      obtain ⟨M, hM, hsuppM⟩ := hsupp
      have hψ1 : ContDiffOn ℝ 1 (Function.uncurry ψ) sliceStrp :=
        hψ.of_le (by simp)
      have hpth : ContDiffOn ℝ k (Function.uncurry (Work.Spaces.pth ψ)) sliceStrp :=
        pth_contDiffOn_succ isOpen_sliceStrp hψ
      have hsupppth : ∃ M : ℝ, 0 ≤ M ∧ ∀ t θ : ℝ, M < |t| → Work.Spaces.pth ψ t θ = 0 := by
        refine ⟨M, hM, fun t θ ht => ?_⟩
        simp only [Work.Spaces.pth]
        rw [show (fun y : ℝ => ψ t y) = fun _ => (0 : ℝ) from funext fun y => hsuppM t y ht]
        simp
      have hpthc : ContinuousOn (Function.uncurry (Work.Spaces.pth ψ)) sliceStrp :=
        hpth.continuousOn
      have hderivcd : ContDiffOn ℝ k
          (fun θ : ℝ => slice (Work.Spaces.pth ψ) ξ θ) sliceSθ :=
        ih (Work.Spaces.pth ψ) ξ hpth hsupppth
      have hpoint : ∀ θ ∈ sliceSθ,
          deriv (fun θ' : ℝ => slice ψ ξ θ') θ = slice (Work.Spaces.pth ψ) ξ θ :=
        fun θ hθ => slice_deriv_eq ψ ξ hψ1 hpthc hM hsuppM hθ
      have hderiv : ContDiffOn ℝ k (deriv (fun θ' : ℝ => slice ψ ξ θ')) sliceSθ :=
        hderivcd.congr fun θ hθ => hpoint θ hθ
      have hdiff : DifferentiableOn ℝ (fun θ' : ℝ => slice ψ ξ θ') sliceSθ := fun θ hθ =>
        ((slice_hasDerivAt_aux ψ (sliceK ξ) hψ1 hpthc (continuous_sliceK ξ) (norm_sliceK ξ)
          hM hsuppM hθ).differentiableAt).differentiableWithinAt
      have hsucc : ContDiffOn ℝ ((k : ℕ∞ω) + 1) (fun θ' : ℝ => slice ψ ξ θ') sliceSθ :=
        (contDiffOn_succ_iff_deriv_of_isOpen isOpen_sliceSθ).mpr
          ⟨hdiff, fun h => absurd h (by simp), hderiv⟩
      rw [show ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 from by simp]
      exact hsucc

end

/-- **Smoothness of the `t`-Fourier slice in the angle.**  A datum which is `C^n` (`n ≤ 2`)
on the open strip `ℝ × (0,π/2)` and has uniformly compact `t`-support has `C^n` slices
`θ ↦ ∫_t φ(t,θ) e^{-2πiξt} dt` on `(0,π/2)`. -/
theorem sliceContDiffOn {φ : ℝ → ℝ → ℝ} {n : ℕ} (hn : n ≤ 2)
    (hφ : ContDiffOn ℝ n (Function.uncurry φ) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hsupp : ∃ M : ℝ, 0 ≤ M ∧ ∀ t θ : ℝ, M < |t| → φ t θ = 0) (ξ : ℝ) :
    ContDiffOn ℝ n (fun θ : ℝ => Work.FTS.EllSol.FlatFT.slice φ ξ θ) (Set.Ioo 0 (Real.pi / 2)) := by
  -- the induction of `slice_contDiffOn_aux` works for every order, so `hn` is not needed
  have _ := hn
  exact slice_contDiffOn_aux n φ ξ hφ hsupp

end Work.FTS.EllSol.FlatFT
