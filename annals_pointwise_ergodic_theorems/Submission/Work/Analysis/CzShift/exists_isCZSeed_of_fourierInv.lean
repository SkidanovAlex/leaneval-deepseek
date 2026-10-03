import Mathlib
import Submission.Work.Analysis.CzShift.Defs

namespace Work.Analysis.CzShift

open MeasureTheory Filter
open scoped FourierTransform Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000

private lemma abs_lt_of_notMem_Icc {C x : ℝ} (h : x ∉ Set.Icc (-C) C) : C < |x| := by
  rw [Set.mem_Icc, not_and_or] at h
  rcases h with h | h
  · rw [not_le] at h
    calc C < -x := by linarith
      _ ≤ |x| := neg_le_abs x
  · rw [not_le] at h
    calc C < x := h
      _ ≤ |x| := le_abs_self x

private lemma integrable_of_support {E : Type*} [NormedAddCommGroup E] {g : ℝ → E} {C M : ℝ}
    (hmeas : AEStronglyMeasurable g volume) (h : ∀ x, ‖g x‖ ≤ M)
    (hsupp : ∀ x, C < |x| → g x = 0) : Integrable g volume := by
  have hgint : Integrable ((Set.Icc (-C) C).indicator (fun _ : ℝ => M)) volume := by
    rw [integrable_indicator_iff measurableSet_Icc]
    refine integrableOn_const (C := M) ?_ ?_
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · simp
  refine Integrable.mono' hgint hmeas (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Set.Icc (-C) C
  · rw [Set.indicator_of_mem hx]; exact h x
  · rw [Set.indicator_of_notMem hx, hsupp x (abs_lt_of_notMem_Icc hx)]
    simp

private lemma integral_norm_le_of_support {g : ℝ → ℂ} {C M : ℝ} (hC : 0 < C) (hM : 0 ≤ M)
    (hg : Integrable g volume) (h : ∀ x, ‖g x‖ ≤ M) (hsupp : ∀ x, C < |x| → g x = 0) :
    ∫ x, ‖g x‖ ≤ 2 * C * M := by
  have hgint : Integrable ((Set.Icc (-C) C).indicator (fun _ : ℝ => M)) volume := by
    rw [integrable_indicator_iff measurableSet_Icc]
    refine integrableOn_const (C := M) ?_ ?_
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · simp
  have hvol : volume.real (Set.Icc (-C) C) = 2 * C := by
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hmono : ∫ x, ‖g x‖ ≤ ∫ x, (Set.Icc (-C) C).indicator (fun _ : ℝ => M) x := by
    refine integral_mono hg.norm hgint fun x => ?_
    by_cases hx : x ∈ Set.Icc (-C) C
    · rw [Set.indicator_of_mem hx]; exact h x
    · rw [Set.indicator_of_notMem hx, hsupp x (abs_lt_of_notMem_Icc hx)]
      simp
  refine hmono.trans ?_
  rw [integral_indicator_const M measurableSet_Icc, hvol, smul_eq_mul]

/-- **Fourier decay of a compactly supported `C²` function.**  If `f` vanishes outside `[-C,C]`
and `f`, `f'`, `f''` are bounded by `M` (where `f'`, `f''` are the first and second derivatives of
`f`), then the Fourier transform of `f` decays like `u^{-2}`:
`‖𝓕 f u‖ ≤ 4 C M / (1 + u²)`.

This is the classical two-fold integration by parts, in the form `𝓕 f'' = (2πi·)² 𝓕 f`
(`Real.fourier_deriv`) combined with `‖𝓕 g u‖ ≤ ∫‖g‖`. -/
private lemma fourier_decay {f f' f'' : ℝ → ℂ} {C M : ℝ} (hC : 0 < C) (hM : 0 ≤ M)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hd2 : ∀ x, HasDerivAt f' (f'' x) x)
    (hsupp : ∀ x, C < |x| → f x = 0)
    (hbd : ∀ x, ‖f x‖ ≤ M) (hbd' : ∀ x, ‖f' x‖ ≤ M) (hbd'' : ∀ x, ‖f'' x‖ ≤ M) :
    ∀ u, ‖𝓕 f u‖ ≤ 4 * C * M / (1 + u ^ 2) := by
  -- locality of the derivative: `f'` and `f''` also vanish outside `[-C,C]`
  have hloc : ∀ x, C < |x| → f =ᶠ[𝓝 x] 0 := by
    intro x hx
    have hpos : ∀ᶠ y in 𝓝 x, C < |y| :=
      continuous_abs.continuousAt (isOpen_Ioi.mem_nhds hx)
    filter_upwards [hpos] with y hy
    exact hsupp y hy
  have hsupp' : ∀ x, C < |x| → f' x = 0 := by
    intro x hx
    have h0 : HasDerivAt f (0 : ℂ) x :=
      (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq (hloc x hx)
    exact (hd x).unique h0
  have hsupp'' : ∀ x, C < |x| → f'' x = 0 := by
    intro x hx
    have hloc' : f' =ᶠ[𝓝 x] 0 := by
      have hpos : ∀ᶠ y in 𝓝 x, C < |y| :=
        continuous_abs.continuousAt (isOpen_Ioi.mem_nhds hx)
      filter_upwards [hpos] with y hy
      exact hsupp' y hy
    have h0 : HasDerivAt f' (0 : ℂ) x :=
      (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hloc'
    exact (hd2 x).unique h0
  -- integrability
  have haesm : AEStronglyMeasurable f volume :=
    (Differentiable.continuous (fun x => (hd x).differentiableAt)).aestronglyMeasurable
  have haesm' : AEStronglyMeasurable f' volume :=
    (Differentiable.continuous (fun x => (hd2 x).differentiableAt)).aestronglyMeasurable
  have hderiv' : f'' = deriv f' := funext fun x => (hd2 x).deriv.symm
  have haesm'' : AEStronglyMeasurable f'' volume := by
    rw [hderiv']
    exact (aemeasurable_deriv f' volume).aestronglyMeasurable
  have hfint : Integrable f volume := integrable_of_support haesm hbd hsupp
  have hfint' : Integrable f' volume := integrable_of_support haesm' hbd' hsupp'
  have hfint'' : Integrable f'' volume := integrable_of_support haesm'' hbd'' hsupp''
  have hbound : ∫ x, ‖f x‖ ≤ 2 * C * M :=
    integral_norm_le_of_support hC hM hfint hbd hsupp
  have hbound'' : ∫ x, ‖f'' x‖ ≤ 2 * C * M :=
    integral_norm_le_of_support hC hM hfint'' hbd'' hsupp''
  -- `‖𝓕 g u‖ ≤ ∫ ‖g‖`
  have hFbound : ∀ u, ‖𝓕 f'' u‖ ≤ 2 * C * M := by
    intro u
    rw [Real.fourier_eq']
    refine (norm_integral_le_integral_norm _).trans ?_
    have : (fun x : ℝ => ‖Complex.exp (↑(-2 * Real.pi * inner ℝ x u) * Complex.I) • f'' x‖)
        = fun x => ‖f'' x‖ := by
      funext x
      rw [norm_smul, Complex.norm_exp]
      simp
    rw [this]
    exact hbound''
  have hFbound0 : ∀ u, ‖𝓕 f u‖ ≤ 2 * C * M := by
    intro u
    rw [Real.fourier_eq']
    refine (norm_integral_le_integral_norm _).trans ?_
    have : (fun x : ℝ => ‖Complex.exp (↑(-2 * Real.pi * inner ℝ x u) * Complex.I) • f x‖)
        = fun x => ‖f x‖ := by
      funext x
      rw [norm_smul, Complex.norm_exp]
      simp
    rw [this]
    exact hbound
  -- the derivative relations
  have hderiv : deriv f = f' := funext fun x => (hd x).deriv
  have h1 : ∀ u, 𝓕 f' u = (2 * Real.pi * Complex.I * u) • 𝓕 f u := by
    have hI : Integrable (deriv f) volume := by rwa [hderiv]
    have h := Real.fourier_deriv hfint (fun x => (hd x).differentiableAt) hI
    rw [hderiv] at h
    exact fun u => congr_fun h u
  have h2 : ∀ u, 𝓕 f'' u = (2 * Real.pi * Complex.I * u) • 𝓕 f' u := by
    have hI : Integrable (deriv f') volume := by rwa [← hderiv']
    have h := Real.fourier_deriv hfint' (fun x => (hd2 x).differentiableAt) hI
    rw [← hderiv'] at h
    exact fun u => congr_fun h u
  intro u
  by_cases hu : u ^ 2 ≤ 1
  · -- small `|u|`
    have hpos : 0 < 1 + u ^ 2 := by positivity
    have hle : 1 + u ^ 2 ≤ 2 := by linarith
    rw [le_div_iff₀ hpos]
    have h1u : ‖𝓕 f u‖ ≤ 2 * C * M := hFbound0 u
    have h2cm : 0 ≤ 2 * C * M := by positivity
    have hstep : ‖𝓕 f u‖ * (1 + u ^ 2) ≤ (2 * C * M) * (1 + u ^ 2) :=
      mul_le_mul_of_nonneg_right h1u hpos.le
    have hfin : (2 * C * M) * (1 + u ^ 2) ≤ 4 * C * M := by nlinarith [h2cm, hle]
    linarith
  · -- large `|u|`
    have hu1 : 1 < u ^ 2 := not_le.mp hu
    have hpos : 0 < 1 + u ^ 2 := by positivity
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    rw [le_div_iff₀ hpos]
    have hnorm : ‖(2 * Real.pi * Complex.I * u : ℂ)‖ = 2 * Real.pi * |u| := by
      have h1 : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
        rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [Real.pi_pos])]
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, h1, Complex.norm_real, Real.norm_eq_abs]
    have hkey : ‖𝓕 f'' u‖ = (2 * Real.pi * u) ^ 2 * ‖𝓕 f u‖ := by
      rw [h2 u, h1 u, norm_smul, hnorm, norm_smul, hnorm]
      ring_nf
      rw [sq_abs]
      ring
    have hsq : (2 * Real.pi * u) ^ 2 = 4 * Real.pi ^ 2 * u ^ 2 := by ring
    have hfin : 4 * Real.pi ^ 2 * u ^ 2 * ‖𝓕 f u‖ ≤ 2 * C * M := by
      rw [← hsq, ← hkey]
      exact hFbound u
    have hcmp : 1 + u ^ 2 ≤ 4 * Real.pi ^ 2 * u ^ 2 := by
      have hpi2 : 1 ≤ Real.pi ^ 2 := by nlinarith [hpi, Real.pi_pos]
      have huu : u ^ 2 ≤ Real.pi ^ 2 * u ^ 2 := by
        calc u ^ 2 = 1 * u ^ 2 := by ring
          _ ≤ Real.pi ^ 2 * u ^ 2 := mul_le_mul_of_nonneg_right hpi2 (sq_nonneg u)
      have hu2 : 1 ≤ u ^ 2 := le_of_lt hu1
      nlinarith [huu, hu2]
    have hstep1 : ‖𝓕 f u‖ * (1 + u ^ 2) ≤ ‖𝓕 f u‖ * (4 * Real.pi ^ 2 * u ^ 2) :=
      mul_le_mul_of_nonneg_left hcmp (norm_nonneg _)
    have hstep2 : ‖𝓕 f u‖ * (4 * Real.pi ^ 2 * u ^ 2) = 4 * Real.pi ^ 2 * u ^ 2 * ‖𝓕 f u‖ := by
      ring
    have hCM : 2 * C * M ≤ 4 * C * M := by nlinarith [hC.le, hM]
    linarith [hstep1, hstep2, hfin, hCM]


private lemma deriv_eq_zero_of_eventuallyEq {f f' : ℝ → ℂ} {x : ℝ}
    (h : HasDerivAt f (f' x) x) (hloc : f =ᶠ[𝓝 x] 0) : f' x = 0 := by
  have h0 : HasDerivAt f (0 : ℂ) x := (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hloc
  exact h.unique h0

private lemma eventuallyEq_zero_of_lt {f : ℝ → ℂ} {C x : ℝ} (hsupp : ∀ y, C < |y| → f y = 0)
    (hx : C < |x|) : f =ᶠ[𝓝 x] 0 := by
  have hpos : ∀ᶠ y in 𝓝 x, C < |y| :=
    continuous_abs.continuousAt (isOpen_Ioi.mem_nhds hx)
  filter_upwards [hpos] with y hy
  exact hsupp y hy

private lemma hasDerivAt_re {f : ℝ → ℂ} {c : ℂ} {u : ℝ} (h : HasDerivAt f c u) :
    HasDerivAt (fun x => (f x).re) c.re u := by
  have hF : HasFDerivAt f (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c) u :=
    (hasFDerivAt_iff_hasDerivAt).mpr (by simpa using h)
  have h2 : HasFDerivAt (fun x => (f x).re)
      (Complex.reCLM.comp (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c)) u :=
    Complex.reCLM.hasFDerivAt.comp u hF
  have h3 := h2.hasDerivAt
  simpa [ContinuousLinearMap.comp_apply] using h3

private lemma norm_two_pi : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
  rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [Real.pi_pos])]

private lemma norm_neg_two_pi_I : ‖(-2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
  rw [show (-2 * Real.pi * Complex.I : ℂ) = -(2 * (Real.pi : ℂ)) * Complex.I by ring,
    norm_mul, norm_neg, norm_two_pi, Complex.norm_I, mul_one]

/-- **The seed bridge.**  If `Ψ` is (the real part of) the inverse Fourier transform of a
compactly supported `C²` symbol `ψ` with `‖ψ‖`, `‖ψ'‖`, `‖ψ''‖ ≤ C`, then `Ψ` satisfies the
shifted Calderón–Zygmund seed bounds: `|Ψ u| ≤ B/(1+u²)` and `|Ψ' u| ≤ B/(1+u²)` for some
explicit `B` depending only on `C`.

This is the step "`Ψ := 𝓕⁻¹ψ` is a rescaled Schwartz kernel" of Appendix B of Krause–Mirek–Tao:
the decay is a two-fold integration by parts, formalised here as `𝓕 g'' = (2πi·)² 𝓕 g`
(`Real.fourier_deriv`) together with `‖𝓕 g u‖ ≤ ∫‖g‖`. -/
theorem isCZSeed_of_fourierInv_explicit (ψ ψ' ψ'' : ℝ → ℂ) (Ψ : ℝ → ℝ) (C : ℝ)
    (hC : 0 < C)
    (hΨform : ∀ u : ℝ, (Ψ u : ℂ) = FourierTransform.fourierInv ψ u)
    (hsupp : ∀ ξ : ℝ, C < |ξ| → ψ ξ = 0)
    (hbd : ∀ ξ : ℝ, ‖ψ ξ‖ ≤ C)
    (hd : ∀ ξ : ℝ, HasDerivAt ψ (ψ' ξ) ξ) (hbd' : ∀ ξ : ℝ, ‖ψ' ξ‖ ≤ C)
    (hd2 : ∀ ξ : ℝ, HasDerivAt ψ' (ψ'' ξ) ξ) (hbd'' : ∀ ξ : ℝ, ‖ψ'' ξ‖ ≤ C) :
    ∃ Ψ' : ℝ → ℝ,
      IsCZSeed Ψ Ψ' (max 1 (4 * C * (C + 2 * Real.pi * (2 * C + C ^ 2)))) := by
  have hdecψ : ∀ u : ℝ, ‖𝓕 ψ u‖ ≤ 4 * C * C / (1 + u ^ 2) :=
    fourier_decay hC hC.le hd hd2 hsupp hbd hbd' hbd''
  have hinv : ∀ u : ℝ, 𝓕⁻ ψ u = 𝓕 ψ (-u) := fun u => Real.fourierInv_eq_fourier_neg ψ u
  have hΨeq : Ψ = fun u : ℝ => (𝓕⁻ ψ u).re := by
    funext u
    conv_lhs => rw [← Complex.ofReal_re (Ψ u)]
    rw [hΨform u]
  have hlocψ : ∀ x : ℝ, C < |x| → ψ =ᶠ[𝓝 x] 0 := fun x hx =>
    eventuallyEq_zero_of_lt hsupp hx
  have hsupp' : ∀ x : ℝ, C < |x| → ψ' x = 0 := fun x hx =>
    deriv_eq_zero_of_eventuallyEq (hd x) (hlocψ x hx)
  have hlocψ' : ∀ x : ℝ, C < |x| → ψ' =ᶠ[𝓝 x] 0 := fun x hx =>
    eventuallyEq_zero_of_lt hsupp' hx
  have hsupp'' : ∀ x : ℝ, C < |x| → ψ'' x = 0 := fun x hx =>
    deriv_eq_zero_of_eventuallyEq (hd2 x) (hlocψ' x hx)
  set g : ℝ → ℂ := fun x => (-2 * Real.pi * Complex.I * x) • ψ x with hg
  set g' : ℝ → ℂ := fun x => (-2 * Real.pi * Complex.I) * (ψ x + x * ψ' x) with hg'
  set g'' : ℝ → ℂ := fun x => (-2 * Real.pi * Complex.I) * (2 * ψ' x + x * ψ'' x) with hg''
  have hgd : ∀ x : ℝ, HasDerivAt g (g' x) x := by
    intro x
    simp only [hg, hg']
    have hbase : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have h1 : HasDerivAt (fun y : ℝ => (-2 * Real.pi * Complex.I) * (y : ℂ))
        (-2 * Real.pi * Complex.I) x := by
      simpa using hbase.const_mul (-2 * Real.pi * Complex.I)
    have h2 : HasDerivAt (fun y : ℝ => (-2 * Real.pi * Complex.I) * (y : ℂ) * ψ y)
        ((-2 * Real.pi * Complex.I) * ψ x + (-2 * Real.pi * Complex.I) * (x : ℂ) * ψ' x) x :=
      h1.mul (hd x)
    have heq : (-2 * Real.pi * Complex.I) * (ψ x + x * ψ' x)
        = (-2 * Real.pi * Complex.I) * ψ x + (-2 * Real.pi * Complex.I) * (x : ℂ) * ψ' x := by
      ring
    rw [heq]
    simpa [smul_eq_mul, mul_assoc] using h2
  have hgd2 : ∀ x : ℝ, HasDerivAt g' (g'' x) x := by
    intro x
    simp only [hg', hg'']
    have hbase : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have hmul : HasDerivAt (fun y : ℝ => (y : ℂ) * ψ' y) (1 * ψ' x + (x : ℂ) * ψ'' x) x :=
      hbase.mul (hd2 x)
    have h1 : HasDerivAt (fun y : ℝ => ψ y + (y : ℂ) * ψ' y)
        (ψ' x + (1 * ψ' x + (x : ℂ) * ψ'' x)) x := (hd x).add hmul
    have h2 := (hasDerivAt_const x (-2 * Real.pi * Complex.I)).mul h1
    have heq : (-2 * Real.pi * Complex.I) * (2 * ψ' x + x * ψ'' x)
        = 0 * (ψ x + (x : ℂ) * ψ' x)
          + (-2 * Real.pi * Complex.I) * (ψ' x + (1 * ψ' x + (x : ℂ) * ψ'' x)) := by
      ring
    rw [heq]
    have hfull : (fun y : ℝ => -2 * Real.pi * Complex.I * (ψ y + y * ψ' y))
        = ((fun _ : ℝ => -2 * Real.pi * Complex.I) * fun y : ℝ => ψ y + y * ψ' y) := by
      funext y
      simp only [Pi.mul_apply]
    rw [hfull]
    exact h2
  have hgsupp : ∀ x : ℝ, C < |x| → g x = 0 := by
    intro x hx
    simp only [hg]
    rw [hsupp x hx, smul_zero]
  have hg'supp : ∀ x : ℝ, C < |x| → g' x = 0 := by
    intro x hx
    simp only [hg']
    rw [hsupp x hx, hsupp' x hx]
    ring
  have hg''supp : ∀ x : ℝ, C < |x| → g'' x = 0 := by
    intro x hx
    simp only [hg'']
    rw [hsupp' x hx, hsupp'' x hx]
    ring
  set Cg : ℝ := 2 * Real.pi * (2 * C + C ^ 2) with hCg
  have hpi : 0 < Real.pi := Real.pi_pos
  have hCg0 : 0 ≤ Cg := by rw [hCg]; positivity
  have hgbd : ∀ x : ℝ, ‖g x‖ ≤ Cg := by
    intro x
    by_cases hx : |x| ≤ C
    · have h1 : ‖(-2 * Real.pi * Complex.I * x : ℂ)‖ = 2 * Real.pi * |x| := by
        rw [show (-2 * Real.pi * Complex.I * x : ℂ) = (-2 * Real.pi * Complex.I) * (x : ℂ) by
          push_cast; ring,
          norm_mul, norm_neg_two_pi_I, Complex.norm_real, Real.norm_eq_abs]
      rw [hg, norm_smul, h1]
      have h4 : |x| * ‖ψ x‖ ≤ C * C := mul_le_mul hx (hbd x) (norm_nonneg _) hC.le
      rw [hCg]
      nlinarith [h4, hpi, hC.le, sq_nonneg C]
    · rw [hgsupp x (not_le.mp hx)]; simpa using hCg0
  have hg'bd : ∀ x : ℝ, ‖g' x‖ ≤ Cg := by
    intro x
    by_cases hx : |x| ≤ C
    · have h1 : ‖ψ x + x * ψ' x‖ ≤ C + C * C := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add (hbd x) ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul hx (hbd' x) (norm_nonneg _) hC.le
      rw [hg', norm_mul, norm_neg_two_pi_I]
      refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans ?_
      rw [hCg]
      nlinarith [hpi, hC.le, sq_nonneg C]
    · rw [hg'supp x (not_le.mp hx)]; simpa using hCg0
  have hg''bd : ∀ x : ℝ, ‖g'' x‖ ≤ Cg := by
    intro x
    by_cases hx : |x| ≤ C
    · have h1 : ‖2 * ψ' x + x * ψ'' x‖ ≤ 2 * C + C * C := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ?_ ?_
        · rw [norm_mul, Complex.norm_ofNat]
          nlinarith [hbd' x, hC.le]
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul hx (hbd'' x) (norm_nonneg _) hC.le
      rw [hg'', norm_mul, norm_neg_two_pi_I]
      refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans ?_
      rw [hCg]
      nlinarith [hpi, hC.le, sq_nonneg C]
    · rw [hg''supp x (not_le.mp hx)]; simpa using hCg0
  have hdecg : ∀ u : ℝ, ‖𝓕 g u‖ ≤ 4 * C * Cg / (1 + u ^ 2) :=
    fourier_decay hC hCg0 hgd hgd2 hgsupp hgbd hg'bd hg''bd
  have hψcont : Continuous ψ := Differentiable.continuous fun x => (hd x).differentiableAt
  have hψint : Integrable ψ volume := integrable_of_support hψcont.aestronglyMeasurable hbd hsupp
  have hxψint : Integrable (fun x : ℝ => x • ψ x) volume := by
    refine integrable_of_support (C := C) (M := C * C)
      (continuous_id.smul hψcont).aestronglyMeasurable ?_ ?_
    · intro x
      rw [norm_smul, Real.norm_eq_abs]
      by_cases hx : |x| ≤ C
      · exact mul_le_mul hx (hbd x) (norm_nonneg _) hC.le
      · rw [hsupp x (not_le.mp hx), norm_zero, mul_zero]
        exact mul_nonneg hC.le hC.le
    · intro x hx
      rw [hsupp x hx, smul_zero]
  have hdFψ : ∀ u : ℝ, HasDerivAt (𝓕 ψ) (𝓕 g u) u := fun u =>
    Real.hasDerivAt_fourier hψint hxψint u
  have hdFinv : ∀ u : ℝ, HasDerivAt (fun w : ℝ => 𝓕⁻ ψ w) (-(𝓕 g (-u))) u := by
    intro u
    have hcomp : HasDerivAt (fun w : ℝ => 𝓕 ψ (-w)) (-(𝓕 g (-u))) u := by
      have h1 : HasFDerivAt (fun w : ℝ => 𝓕 ψ (-w))
          ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (𝓕 g (-u))).comp
            (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-1))) u :=
        (hdFψ (-u)).hasFDerivAt.comp u (hasDerivAt_neg u).hasFDerivAt
      have h2 := h1.hasDerivAt
      simpa using h2
    refine hcomp.congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun w => hinv w
  have hdΨ : ∀ u : ℝ, HasDerivAt Ψ (-(𝓕 g (-u)).re) u := by
    intro u
    have h1 := hasDerivAt_re (hdFinv u)
    refine h1.congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun w => congr_fun hΨeq w
  have hCgunfold : Cg = 2 * Real.pi * (2 * C + C ^ 2) := hCg
  rw [hCgunfold]
  refine ⟨(fun u => -(𝓕 g (-u)).re), le_max_left _ _, hdΨ, ?_, ?_⟩
  · intro u
    have hpos : 0 < 1 + u ^ 2 := by positivity
    have h2 : (Ψ u : ℂ) = 𝓕 ψ (-u) := by rw [hΨform u, hinv u]
    have h1 : ‖Ψ u‖ ≤ 4 * C * C / (1 + u ^ 2) := by
      calc ‖Ψ u‖ = ‖(Ψ u : ℂ)‖ := by simp
        _ = ‖𝓕 ψ (-u)‖ := by rw [h2]
        _ ≤ 4 * C * C / (1 + (-u) ^ 2) := hdecψ (-u)
        _ = 4 * C * C / (1 + u ^ 2) := by ring_nf
    have hle : 4 * C * C ≤ max 1 (4 * C * (C + 2 * Real.pi * (2 * C + C ^ 2))) := by
      refine le_trans ?_ (le_max_right _ _)
      nlinarith [hC.le, hCg0, Real.pi_pos, sq_nonneg C]
    calc ‖Ψ u‖ ≤ 4 * C * C / (1 + u ^ 2) := h1
      _ ≤ max 1 (4 * C * (C + 2 * Real.pi * (2 * C + C ^ 2))) / (1 + u ^ 2) := by
          rw [div_le_div_iff_of_pos_right hpos]; exact hle
  · intro u
    have hpos : 0 < 1 + u ^ 2 := by positivity
    have h1 : ‖-(𝓕 g (-u)).re‖ ≤ 4 * C * Cg / (1 + u ^ 2) := by
      rw [Real.norm_eq_abs, abs_neg]
      refine (Complex.abs_re_le_norm _).trans ?_
      calc ‖𝓕 g (-u)‖ ≤ 4 * C * Cg / (1 + (-u) ^ 2) := hdecg (-u)
        _ = 4 * C * Cg / (1 + u ^ 2) := by ring_nf
    have hle : 4 * C * Cg ≤ max 1 (4 * C * (C + 2 * Real.pi * (2 * C + C ^ 2))) := by
      refine le_trans ?_ (le_max_right _ _)
      nlinarith [hC.le, hCg0, Real.pi_pos, sq_nonneg C]
    calc ‖-(𝓕 g (-u)).re‖ ≤ 4 * C * Cg / (1 + u ^ 2) := h1
      _ ≤ max 1 (4 * C * (C + 2 * Real.pi * (2 * C + C ^ 2))) / (1 + u ^ 2) := by
          rw [div_le_div_iff_of_pos_right hpos]; exact hle

lemma one_le_max_C (C : ℝ) (hC : 0 < C) :
    1 ≤ max 1 (4 * C * (C + 2 * Real.pi * (2 * C + C ^ 2))) := le_max_left _ _

/-- **The seed bridge** (the reviewed form): if `Ψ` is the real part of the inverse Fourier
transform of a compactly supported `C²` symbol `ψ` with `‖ψ‖, ‖ψ'‖, ‖ψ''‖ ≤ C`, then `Ψ`
satisfies the shifted Calderón–Zygmund seed bounds for some `B` depending only on `C`. -/
theorem exists_isCZSeed_of_fourierInv (ψ ψ' ψ'' : ℝ → ℂ) (Ψ : ℝ → ℝ) (C : ℝ)
    (hC : 0 < C)
    (hΨform : ∀ u : ℝ, (Ψ u : ℂ) = FourierTransform.fourierInv ψ u)
    (hsupp : ∀ ξ : ℝ, C < |ξ| → ψ ξ = 0)
    (hbd : ∀ ξ : ℝ, ‖ψ ξ‖ ≤ C)
    (hd : ∀ ξ : ℝ, HasDerivAt ψ (ψ' ξ) ξ) (hbd' : ∀ ξ : ℝ, ‖ψ' ξ‖ ≤ C)
    (hd2 : ∀ ξ : ℝ, HasDerivAt ψ' (ψ'' ξ) ξ) (hbd'' : ∀ ξ : ℝ, ‖ψ'' ξ‖ ≤ C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ Ψ' : ℝ → ℝ, IsCZSeed Ψ Ψ' B :=
  ⟨_, one_le_max_C C hC,
    isCZSeed_of_fourierInv_explicit ψ ψ' ψ'' Ψ C hC hΨform hsupp hbd hd hbd' hd2 hbd''⟩

end Work.Analysis.CzShift
