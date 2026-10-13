import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Have
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.StrongEps.EpsLocalPStar.ConvInjective
import Submission.Work.FTS.StrongEps.EpsLocalPStar.FourierZeroNull
import Submission.Work.FTS.StrongEps.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TraceZeroOfConv` — a vanishing test for the log-coordinate trace

If `ρ` is a mollifier kernel (`IsMollKernel`), `ε > 0`, `lam` measurable with
`u ↦ lam (exp u)` integrable, and for every `z > 0`

  `∫ s, (∫ t, ρ (s,t)) * lam (z * exp (-(ε * s))) = 0`,

then `lam = 0` a.e. on `(0,∞)`.

The argument: let `F` be the `s`-marginal of `ρ` (integrable, supported in `[-1,1]`, mass `1`),
and `L v := lam (exp (ε * v))`.  Writing `z = exp (ε σ)` the hypothesis says that `F ⋆ L = 0`
identically.  Both are integrable, so taking Fourier transforms gives `𝓕 F · 𝓕 L = 0`; by
`FourierZeroNull` the first factor is nonzero a.e., whence `𝓕 L = 0` a.e. and `L = 0` a.e.
(duality against Schwartz functions).  Finally the substitution `v ↦ exp (ε v)` carries the
null set back to `(0,∞)`.

The Fourier-injectivity step is `ConvInjective` in the form where its hypothesis
`Continuous ρ` — used there only to obtain `Integrable ρ` — is replaced by `Integrable ρ`.
-/

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology FourierTransform ContDiff SchwartzMap ENNReal
open MeasureTheory Set Filter

noncomputable section

/-- `ConvInjective` with the integrability of the kernel supplied directly (its continuity is used
in that proof only to deduce integrability).  Complex-valued version, in the multiplicative
form of the convolution matching `convolution_def`. -/
private theorem convInjective_int {ρ f : ℝ → ℂ} (hρ_int : MeasureTheory.Integrable ρ)
    (hF : ∀ᵐ ξ ∂MeasureTheory.volume, 𝓕 ρ ξ ≠ 0)
    (hf : MeasureTheory.Integrable f)
    (hconv : ∀ u : ℝ, ∫ s, ρ s * f (u - s) = 0) :
    f =ᵐ[MeasureTheory.volume] 0 := by
  have hconv_zero : convolution ρ f (ContinuousLinearMap.mul ℂ ℂ) volume = 0 := by
    funext u
    rw [convolution_def]
    have h1 : (fun t : ℝ => (ContinuousLinearMap.mul ℂ ℂ) (ρ t) (f (u - t))) =
        fun t => ρ t * f (u - t) := funext fun t => rfl
    rw [h1, hconv u]
    simp
  -- hence the Fourier transform of `f` vanishes a.e.
  have hprod : ∀ ξ : ℝ, 𝓕 ρ ξ * 𝓕 f ξ = 0 := by
    intro ξ
    rw [← Real.fourier_mul_convolution_eq (f₁ := ρ) (f₂ := f) hρ_int hf ξ, hconv_zero]
    simp [Real.fourier_eq]
  have hzero : (fun ξ => 𝓕 f ξ) =ᵐ[MeasureTheory.volume] 0 := by
    filter_upwards [hF] with ξ hξ
    exact (mul_eq_zero.mp (hprod ξ)).resolve_left hξ
  -- it remains to deduce `f = 0` a.e., by duality against compactly supported smooth tests
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable ?_
  intro ψ hψ hψc
  let Ψ : 𝓢(ℝ, ℂ) := (hψc.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)).toSchwartzMap
    (ContDiff.comp (ContinuousLinearMap.contDiff Complex.ofRealCLM) hψ)
  have hΨcoe : (Ψ : ℝ → ℂ) = fun x => (ψ x : ℂ) := by
    ext x; simp [Ψ]
  let g₀ : 𝓢(ℝ, ℂ) := 𝓕⁻ Ψ
  have hg₀ : (𝓕 (g₀ : ℝ → ℂ)) = fun x => (ψ x : ℂ) := by
    rw [← SchwartzMap.fourier_coe g₀, show 𝓕 g₀ = Ψ from FourierInvPair.fourier_fourierInv_eq Ψ]
    exact hΨcoe
  -- the Fourier duality identity `∫ f 𝓕 g = ∫ 𝓕 f g`
  have hdual : ∫ x, f x • (𝓕 (g₀ : ℝ → ℂ)) x =
      ∫ ξ, (𝓕 f) ξ • (g₀ : ℝ → ℂ) ξ := by
    have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.lsmul ℂ ℂ)
      (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hf
      (SchwartzMap.integrable (μ := volume) g₀)
    simpa [ContinuousLinearMap.lsmul_apply, VectorFourier.fourierIntegral, Real.fourier_eq,
      LinearMap.flip_apply] using h.symm
  have hrhs : ∫ ξ, (𝓕 f) ξ • (g₀ : ℝ → ℂ) ξ = 0 := by
    have : (fun ξ => (𝓕 f) ξ • (g₀ : ℝ → ℂ) ξ) =ᵐ[volume] 0 := by
      filter_upwards [hzero] with ξ hξ
      simp [hξ]
    rw [integral_congr_ae this]
    simp
  have key : (∫ x : ℝ, ψ x • f x) = 0 := by
    have h1 : (∫ x : ℝ, f x • (𝓕 (g₀ : ℝ → ℂ)) x) = ∫ x : ℝ, ψ x • f x := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hg₀]
      simp only [Complex.real_smul]
      ring
    rw [← h1, hdual, hrhs]
  exact key

/-! ## The `s`-marginal of the kernel and the log-coordinate trace -/

/-- The `s`-marginal of a kernel `ρ : ℝ × ℝ → ℝ`. -/
private noncomputable def marg (ρ : ℝ × ℝ → ℝ) : ℝ → ℝ := fun s => ∫ t, ρ (s, t)

/-- The trace of `lam` in the log-coordinate `v` (with `z = exp (ε v)`). -/
private noncomputable def logTrace (lam : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  fun v => lam (Real.exp (ε * v))

private theorem marg_integrable {ρ : ℝ × ℝ → ℝ} (hρ : MeasureTheory.Integrable ρ) :
    MeasureTheory.Integrable (marg ρ) := by
  have h : MeasureTheory.Integrable ρ
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume) := by
    rwa [← MeasureTheory.Measure.volume_eq_prod]
  exact h.integral_prod_left

private theorem marg_integral {ρ : ℝ × ℝ → ℝ} (hρ : MeasureTheory.Integrable ρ) :
    (∫ s : ℝ, marg ρ s) = ∫ p : ℝ × ℝ, ρ p := by
  have h : MeasureTheory.Integrable ρ
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume) := by
    rwa [← MeasureTheory.Measure.volume_eq_prod]
  have hf : (∫ s : ℝ, ∫ t : ℝ, ρ (s, t)) = (∫ p : ℝ × ℝ, ρ p) := by
    have h2 := MeasureTheory.integral_prod (μ := MeasureTheory.volume) (ν := MeasureTheory.volume) ρ h
    rw [← MeasureTheory.Measure.volume_eq_prod] at h2
    exact h2.symm
  simpa only [marg] using hf

private theorem marg_eq_zero_of_not_mem {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {x : ℝ} (hx : x ∉ Set.Icc (-1 : ℝ) 1) : marg ρ x = 0 := by
  have hzero : ∀ t : ℝ, ρ (x, t) = 0 := by
    intro t
    by_contra hne
    have hle : x ^ 2 + t ^ 2 ≤ 1 := hρ.support (x, t) hne
    have h1 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
    exact hx (abs_le.mp ((sq_le_one_iff_abs_le_one x).mp h1))
  simp only [marg, hzero, integral_zero]

private theorem fourier_marg_ne_zero {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    (hρint : MeasureTheory.Integrable ρ) (hmass : (∫ p : ℝ × ℝ, ρ p) = 1) :
    ∀ᵐ ξ ∂MeasureTheory.volume, 𝓕 (fun x : ℝ => (marg ρ x : ℂ)) ξ ≠ 0 := by
  refine FourierZeroNull (marg_integrable hρint).ofReal ?_ ?_
  · intro x hx
    simp only [marg_eq_zero_of_not_mem hρ hx, Complex.ofReal_zero]
  · have h0 : (∫ x : ℝ, ((marg ρ x : ℝ) : ℂ)) = ((1 : ℝ) : ℂ) := by
      have h1 : (∫ x : ℝ, ((marg ρ x : ℝ) : ℂ)) = ((∫ x : ℝ, marg ρ x : ℝ) : ℂ) :=
        integral_ofReal
      rw [h1, marg_integral hρint, hmass]
    rw [h0]
    exact one_ne_zero

/-- Integrability of the log-coordinate trace, from the integrability of `u ↦ lam (exp u)`. -/
private theorem integrable_logTrace {ε : ℝ} (hε : 0 < ε) {lam : ℝ → ℝ}
    (hint : MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u))) :
    MeasureTheory.Integrable (logTrace lam ε) :=
  hint.comp_mul_left' hε.ne'

/-- A null set of log-coordinates has null image under `v ↦ exp (ε v)`. -/
private theorem ae_zero_on_Ioi_of_logTrace {ε : ℝ} (hε : 0 < ε) {lam : ℝ → ℝ}
    (hlamm : Measurable lam) (h : logTrace lam ε =ᵐ[MeasureTheory.volume] 0) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), lam z = 0 := by
  set S : Set ℝ := {z : ℝ | ¬ lam z = 0} ∩ Set.Ioi 0 with hSdef
  have hSmeas : MeasurableSet S := by
    rw [hSdef]
    exact ((hlamm (measurableSet_singleton 0)).compl).inter measurableSet_Ioi
  have hkey : MeasureTheory.volume S = 0 := by
    have hderiv : ∀ x ∈ (Set.univ : Set ℝ), HasDerivWithinAt (fun v : ℝ => Real.exp (ε * v))
        (Real.exp (ε * x) * ε) Set.univ x := fun x _ => by
      simpa only [Function.comp_def] using
        ((Real.hasDerivAt_exp (ε * x)).comp x (hasDerivAt_const_mul (x := x) ε)).hasDerivWithinAt
          (s := Set.univ)
    have hinj : Set.InjOn (fun v : ℝ => Real.exp (ε * v)) Set.univ := by
      intro a _ b _ hab
      exact mul_left_cancel₀ hε.ne' (Real.exp_eq_exp.mp hab)
    have hrange : (fun v : ℝ => Real.exp (ε * v)) '' Set.univ = Set.Ioi 0 := by
      ext z
      constructor
      · rintro ⟨v, -, rfl⟩
        simpa using Real.exp_pos (ε * v)
      · intro hz
        refine ⟨Real.log z / ε, Set.mem_univ _, ?_⟩
        show Real.exp (ε * (Real.log z / ε)) = z
        rw [mul_div_cancel₀ (Real.log z) hε.ne', Real.exp_log hz]
    let g : ℝ → ℝ≥0∞ := S.indicator (fun _ => 1)
    have hlint := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.univ)
      (f := fun v : ℝ => Real.exp (ε * v)) (f' := fun x : ℝ => Real.exp (ε * x) * ε)
      MeasurableSet.univ hderiv hinj g
    rw [hrange, MeasureTheory.Measure.restrict_univ] at hlint
    have hlhs : (∫⁻ z in Set.Ioi (0 : ℝ), g z) = MeasureTheory.volume S := by
      have h1 : (∫⁻ z in Set.Ioi (0 : ℝ), g z) =
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) S :=
        MeasureTheory.lintegral_indicator_one hSmeas
      rw [h1, MeasureTheory.Measure.restrict_apply hSmeas,
        Set.inter_eq_left.mpr Set.inter_subset_right]
    have hrhs : (∫⁻ x : ℝ, ENNReal.ofReal |Real.exp (ε * x) * ε| * g (Real.exp (ε * x))) = 0 := by
      have hz : (fun x : ℝ => ENNReal.ofReal |Real.exp (ε * x) * ε| * g (Real.exp (ε * x)))
          =ᵐ[MeasureTheory.volume] 0 := by
        filter_upwards [h] with x hx
        have hxS : Real.exp (ε * x) ∉ S := by
          intro hmem
          exact hmem.1 (by simpa only [logTrace, Pi.zero_apply] using hx)
        simp only [g, Set.indicator_of_notMem hxS, mul_zero, Pi.zero_apply]
      rw [MeasureTheory.lintegral_congr_ae hz]
      simp
    rw [hlhs, hrhs] at hlint
    exact hlint
  rw [MeasureTheory.ae_iff]
  have hgoal : (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) {z : ℝ | ¬ lam z = 0} = 0 := by
    rw [MeasureTheory.Measure.restrict_apply' measurableSet_Ioi, ← hSdef]
    exact hkey
  exact hgoal

theorem TraceZeroOfConv (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {lam : ℝ → ℝ}
    (hint : MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u)))
    (hlamm : Measurable lam)
    (hconv : ∀ z : ℝ, 0 < z →
      (∫ s : ℝ, (∫ t : ℝ, ρ (s, t)) * lam (z * Real.exp (-(ε * s)))) = 0) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))), lam z = 0 := by
  have hρint : MeasureTheory.Integrable ρ := by
    refine hρ.cont.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) (isCompact_Icc.prod isCompact_Icc) ?_
    intro p hp
    have hle : p.1 ^ 2 + p.2 ^ 2 ≤ 1 := hρ.support p hp
    have h1 : p.1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg p.2]
    have h2 : p.2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg p.1]
    exact ⟨abs_le.mp ((sq_le_one_iff_abs_le_one p.1).mp h1),
      abs_le.mp ((sq_le_one_iff_abs_le_one p.2).mp h2)⟩
  have hFint : MeasureTheory.Integrable (marg ρ) := marg_integrable hρint
  have hFourier : ∀ᵐ ξ ∂MeasureTheory.volume, 𝓕 (fun x : ℝ => (marg ρ x : ℂ)) ξ ≠ 0 :=
    fourier_marg_ne_zero hρ hρint hρ.mass
  have hLint : MeasureTheory.Integrable (logTrace lam ε) := integrable_logTrace hε hint
  have hLzero : logTrace lam ε =ᵐ[MeasureTheory.volume] 0 := by
    have hLc : (fun v : ℝ => (logTrace lam ε v : ℂ)) =ᵐ[MeasureTheory.volume] 0 := by
      refine convInjective_int (ρ := fun x : ℝ => (marg ρ x : ℂ))
        (f := fun v : ℝ => (logTrace lam ε v : ℂ)) hFint.ofReal hFourier hLint.ofReal ?_
      intro σ
      have hpt : ∀ s : ℝ, lam (Real.exp (ε * σ) * Real.exp (-(ε * s))) =
          logTrace lam ε (σ - s) := by
        intro s
        have hxy : Real.exp (ε * σ) * Real.exp (-(ε * s)) = Real.exp (ε * (σ - s)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hxy, logTrace]
      have hreal : (∫ s : ℝ, marg ρ s * logTrace lam ε (σ - s)) = 0 := by
        have hbig := hconv (Real.exp (ε * σ)) (Real.exp_pos _)
        rw [← hbig]
        refine integral_congr_ae (Eventually.of_forall fun s => ?_)
        simp only [marg]
        rw [hpt s]
      have hcmul : (fun s : ℝ => (marg ρ s : ℂ) * ((logTrace lam ε (σ - s) : ℝ) : ℂ)) =
          fun s => ((marg ρ s * logTrace lam ε (σ - s) : ℝ) : ℂ) :=
        funext fun s => (Complex.ofReal_mul _ _).symm
      have h0 : (∫ s : ℝ, ((marg ρ s * logTrace lam ε (σ - s) : ℝ) : ℂ)) =
          ((∫ s : ℝ, marg ρ s * logTrace lam ε (σ - s) : ℝ) : ℂ) := integral_ofReal
      rw [hcmul, h0, hreal, Complex.ofReal_zero]
    filter_upwards [hLc] with v hv
    exact Complex.ofReal_eq_zero.mp hv
  exact ae_zero_on_Ioi_of_logTrace hε hlamm hLzero

end

end Work.FTS.StrongEps.EpsLocalPStar
