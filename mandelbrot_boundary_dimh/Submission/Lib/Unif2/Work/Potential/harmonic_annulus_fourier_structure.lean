import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
import Submission.Lib.Unif2.Work.Potential.strip_integral_hasDerivAt
import Submission.Lib.Unif2.Work.Potential.periodic_integral_deriv_deriv_exp


/-!
# The Fourier structure of a harmonic function on an annulus

If `u : ℂ → ℝ` is harmonic on the open annulus `{z | r₁ < ‖z‖ < r₂}`, then the `k`-th Fourier
coefficient of `u` on the circle `‖z‖ = r` is a linear combination of `r ^ k` and `r ^ (-k)`
(for `k ≠ 0`), while the average over the circle is `α + β log r`.

The proof lifts `u` to the logarithmic strip `{w | log r₁ < Re w < log r₂}` by
`w ↦ u (exp w)`, where the vertical lines `Re w = log r` correspond to the circles `‖z‖ = r`.
The Fourier coefficient then satisfies the second order ODE `F'' = k² F` (a computation with the
Laplacian, `∂_s² + ∂_θ² = 0`, integration by parts and periodicity), whose solutions are
`A e^{ks} + B e^{-ks}`; substituting `s = log r` gives the claim.

## Main result

* `Work.Potential.harmonic_annulus_fourier_structure`
-/

noncomputable section
open MeasureTheory Filter Set Function
open scoped Real Topology Interval
namespace Work.Potential

/-! ## Definitions -/

def expLiftR (u : ℂ → ℝ) : ℂ → ℝ := fun w => u (Complex.exp w)
def expLift (u : ℂ → ℝ) : ℂ → ℂ := fun w => (u (Complex.exp w) : ℂ)
def dS (f : ℂ → ℂ) : ℂ → ℂ := fun w => fderiv ℝ f w 1
def dI (f : ℂ → ℂ) : ℂ → ℂ := fun w => fderiv ℝ f w Complex.I
def stripCoeff (f : ℂ → ℂ) (k : ℤ) (s : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    f ((s : ℂ) + (θ : ℂ) * Complex.I) * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))

/-- The `k`-th Fourier coefficient of `u` along the circle `‖z‖ = r`. -/
def circleCoeff (u : ℂ → ℝ) (k : ℤ) (r : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (u (r * Complex.exp (θ * Complex.I)) : ℂ) *
      Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))

variable {u : ℂ → ℝ} {r₁ r₂ : ℝ}

lemma harmonicAt_expLiftR (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hu : ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → InnerProductSpace.HarmonicAt u z)
    {w : ℂ} (hw₁ : Real.log r₁ < w.re) (hw₂ : w.re < Real.log r₂) :
    InnerProductSpace.HarmonicAt (expLiftR u) w := by
  have hmem₁ : r₁ < ‖Complex.exp w‖ := by
    rw [Complex.norm_exp, ← Real.exp_log h₁]; exact Real.exp_lt_exp.mpr hw₁
  have hmem₂ : ‖Complex.exp w‖ < r₂ := by
    rw [Complex.norm_exp, ← Real.exp_log (lt_trans h₁ h₁₂)]
    exact Real.exp_lt_exp.mpr hw₂
  exact Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic (f := Complex.exp)
    ((Complex.differentiable_exp (𝕜 := ℂ)).analyticAt w) (hu _ hmem₁ hmem₂)

lemma harmonicAt_expLift (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hu : ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → InnerProductSpace.HarmonicAt u z)
    {w : ℂ} (hw₁ : Real.log r₁ < w.re) (hw₂ : w.re < Real.log r₂) :
    InnerProductSpace.HarmonicAt (expLift u) w := by
  have h := (harmonicAt_expLiftR h₁ h₁₂ hu hw₁ hw₂).comp_CLM Complex.ofRealCLM
  exact h

lemma contDiffAt_expLift (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hu : ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → InnerProductSpace.HarmonicAt u z)
    {n : WithTop ℕ∞} {w : ℂ} (hw₁ : Real.log r₁ < w.re) (hw₂ : w.re < Real.log r₂) :
    ContDiffAt ℝ n (expLift u) w := by
  have h0 : ContDiffAt ℝ n (expLiftR u) w :=
    (HarmonicAt.analyticAt (harmonicAt_expLiftR h₁ h₁₂ hu hw₁ hw₂)).contDiffAt
  have h1 : ContDiffAt ℝ n ((fun x : ℝ => (x : ℂ)) ∘ expLiftR u) w :=
    (Complex.ofRealCLM.contDiff (n := n)).comp_contDiffAt w h0
  exact h1

lemma expLift_add_two_pi (u : ℂ → ℝ) (w : ℂ) :
    expLift u (w + 2 * Real.pi * Complex.I) = expLift u w := by
  simp only [expLift, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

lemma line_re (s θ : ℝ) : ((s : ℂ) + (θ : ℂ) * Complex.I).re = s := by
  simp [Complex.add_re, Complex.mul_re]

lemma hasDerivAt_line (s θ : ℝ) :
    HasDerivAt (fun θ : ℝ => (s : ℂ) + (θ : ℂ) * Complex.I) Complex.I θ := by
  have h := (hasDerivAt_id' θ).ofReal_comp.mul_const Complex.I
  have h' : HasDerivAt (fun y : ℝ => (y : ℂ) * Complex.I) ((1 : ℂ) * Complex.I) θ := h
  simpa using h'.const_add (s : ℂ)

lemma hasDerivAt_expLift_line (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hu : ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → InnerProductSpace.HarmonicAt u z)
    {s : ℝ} (hs₁ : Real.log r₁ < s) (hs₂ : s < Real.log r₂) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => expLift u ((s : ℂ) + (θ : ℂ) * Complex.I))
      (dI (expLift u) ((s : ℂ) + (θ : ℂ) * Complex.I)) θ := by
  have hm₁ : Real.log r₁ < ((s : ℂ) + (θ : ℂ) * Complex.I).re := by rw [line_re]; exact hs₁
  have hm₂ : ((s : ℂ) + (θ : ℂ) * Complex.I).re < Real.log r₂ := by rw [line_re]; exact hs₂
  exact ((contDiffAt_expLift h₁ h₁₂ hu (n := 1) hm₁ hm₂).differentiableAt (by norm_num)).hasFDerivAt
    |>.comp_hasDerivAt θ (hasDerivAt_line s θ)

lemma contDiffAt_dI (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hu : ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → InnerProductSpace.HarmonicAt u z)
    {n : WithTop ℕ∞} {w : ℂ} (hw₁ : Real.log r₁ < w.re) (hw₂ : w.re < Real.log r₂) :
    ContDiffAt ℝ n (dI (expLift u)) w :=
  ((contDiffAt_expLift h₁ h₁₂ hu (n := n+1) hw₁ hw₂).fderiv_right (m := n) (le_refl _)).clm_apply
    (contDiffAt_const (x := w) (c := Complex.I))

lemma contDiffAt_dS (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hu : ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → InnerProductSpace.HarmonicAt u z)
    {n : WithTop ℕ∞} {w : ℂ} (hw₁ : Real.log r₁ < w.re) (hw₂ : w.re < Real.log r₂) :
    ContDiffAt ℝ n (dS (expLift u)) w :=
  ((contDiffAt_expLift h₁ h₁₂ hu (n := n+1) hw₁ hw₂).fderiv_right (m := n) (le_refl _)).clm_apply
    (contDiffAt_const (x := w) (c := (1:ℂ)))

lemma hasDerivAt_dI_expLift_line (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hu : ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → InnerProductSpace.HarmonicAt u z)
    {s : ℝ} (hs₁ : Real.log r₁ < s) (hs₂ : s < Real.log r₂) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => dI (expLift u) ((s : ℂ) + (θ : ℂ) * Complex.I))
      (dI (dI (expLift u)) ((s : ℂ) + (θ : ℂ) * Complex.I)) θ := by
  have hm₁ : Real.log r₁ < ((s : ℂ) + (θ : ℂ) * Complex.I).re := by rw [line_re]; exact hs₁
  have hm₂ : ((s : ℂ) + (θ : ℂ) * Complex.I).re < Real.log r₂ := by rw [line_re]; exact hs₂
  exact ((contDiffAt_dI h₁ h₁₂ hu (n := 1) hm₁ hm₂).differentiableAt (by norm_num)).hasFDerivAt
    |>.comp_hasDerivAt θ (hasDerivAt_line s θ)

lemma deriv_deriv_expLift_line (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hu : ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → InnerProductSpace.HarmonicAt u z)
    {s : ℝ} (hs₁ : Real.log r₁ < s) (hs₂ : s < Real.log r₂) (θ : ℝ) :
    deriv (deriv (fun θ : ℝ => expLift u ((s : ℂ) + (θ : ℂ) * Complex.I))) θ
      = dI (dI (expLift u)) ((s : ℂ) + (θ : ℂ) * Complex.I) := by
  have h1 : deriv (fun θ : ℝ => expLift u ((s : ℂ) + (θ : ℂ) * Complex.I))
      = fun θ : ℝ => dI (expLift u) ((s : ℂ) + (θ : ℂ) * Complex.I) :=
    funext (fun θ : ℝ => (hasDerivAt_expLift_line h₁ h₁₂ hu hs₁ hs₂ θ).deriv)
  rw [h1]
  exact (hasDerivAt_dI_expLift_line h₁ h₁₂ hu hs₁ hs₂ θ).deriv

/-! ## The Laplacian relates the two second derivatives -/

lemma dS_dS_eq_iteratedFDeriv {f : ℂ → ℂ} {w : ℂ} (hd : DifferentiableAt ℝ (fderiv ℝ f) w) :
    dS (dS f) w = iteratedFDeriv ℝ 2 f w ![1,1] := by
  have hdS : fderiv ℝ (dS f) w
      = (ContinuousLinearMap.apply ℝ ℂ (1:ℂ)) ∘SL (fderiv ℝ (fderiv ℝ f) w) := by
    rw [show dS f = (ContinuousLinearMap.apply ℝ ℂ (1:ℂ)) ∘ (fderiv ℝ f) from rfl]
    rw [fderiv_comp w (ContinuousLinearMap.differentiableAt _) hd, ContinuousLinearMap.fderiv]
  rw [show dS (dS f) w = fderiv ℝ (dS f) w 1 from rfl, hdS, iteratedFDeriv_two_apply]
  rfl

lemma dI_dI_eq_iteratedFDeriv {f : ℂ → ℂ} {w : ℂ} (hd : DifferentiableAt ℝ (fderiv ℝ f) w) :
    dI (dI f) w = iteratedFDeriv ℝ 2 f w ![Complex.I,Complex.I] := by
  have hdS : fderiv ℝ (dI f) w
      = (ContinuousLinearMap.apply ℝ ℂ (Complex.I)) ∘SL (fderiv ℝ (fderiv ℝ f) w) := by
    rw [show dI f = (ContinuousLinearMap.apply ℝ ℂ (Complex.I)) ∘ (fderiv ℝ f) from rfl]
    rw [fderiv_comp w (ContinuousLinearMap.differentiableAt _) hd, ContinuousLinearMap.fderiv]
  rw [show dI (dI f) w = fderiv ℝ (dI f) w Complex.I from rfl, hdS, iteratedFDeriv_two_apply]
  rfl

lemma dS_dS_add_dI_dI {f : ℂ → ℂ} {w : ℂ}
    (hf : InnerProductSpace.HarmonicAt f w) : dS (dS f) w + dI (dI f) w = 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) w :=
    ((hf.1.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  rw [dS_dS_eq_iteratedFDeriv hd, dI_dI_eq_iteratedFDeriv hd]
  have h := congr_fun (InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane f) w
  have h0 : Laplacian.laplacian f w = 0 := hf.2.eq_of_nhds
  rw [h0] at h
  exact h.symm

/-! ## Periodicity of the derivative -/

lemma fderiv_expLift_add_two_pi (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hu : ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → InnerProductSpace.HarmonicAt u z)
    {w : ℂ} (hw₁ : Real.log r₁ < w.re) (hw₂ : w.re < Real.log r₂) :
    fderiv ℝ (expLift u) (w + 2 * Real.pi * Complex.I) = fderiv ℝ (expLift u) w := by
  have hper : ∀ z : ℂ, expLift u (z + 2 * Real.pi * Complex.I) = expLift u z :=
    expLift_add_two_pi u
  have hm₁ : Real.log r₁ < (w + 2 * Real.pi * Complex.I).re := by
    rw [Complex.add_re, Complex.mul_re]; simpa using hw₁
  have hm₂ : (w + 2 * Real.pi * Complex.I).re < Real.log r₂ := by
    rw [Complex.add_re, Complex.mul_re]; simpa using hw₂
  have hd : DifferentiableAt ℝ (expLift u) (w + 2 * Real.pi * Complex.I) :=
    (contDiffAt_expLift h₁ h₁₂ hu (n := 1) hm₁ hm₂).differentiableAt (by norm_num)
  have hg : DifferentiableAt ℝ (fun z : ℂ => z + 2 * Real.pi * Complex.I) w :=
    differentiableAt_id.add_const _
  have hcomp : fderiv ℝ (fun z : ℂ => expLift u (z + 2 * Real.pi * Complex.I)) w
      = fderiv ℝ (expLift u) (w + 2 * Real.pi * Complex.I) := by
    rw [show (fun z : ℂ => expLift u (z + 2 * Real.pi * Complex.I))
        = expLift u ∘ (fun z : ℂ => z + 2 * Real.pi * Complex.I) from rfl]
    rw [fderiv_comp w hd hg, fderiv_add_const, fderiv_id']
    simp
  have hfun : (fun z : ℂ => expLift u (z + 2 * Real.pi * Complex.I)) = expLift u :=
    funext hper
  rw [hfun] at hcomp
  exact hcomp.symm

/-! ## The ODE satisfied by the Fourier coefficients -/

theorem stripCoeff_second_deriv (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hu : ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → InnerProductSpace.HarmonicAt u z)
    (k : ℤ) {s : ℝ} (hs₁ : Real.log r₁ < s) (hs₂ : s < Real.log r₂) :
    stripCoeff (dS (dS (expLift u))) k s
      = ((k : ℂ) ^ 2) * stripCoeff (expLift u) k s := by
  have h2f : ∀ w : ℂ, Real.log r₁ < w.re → w.re < Real.log r₂ →
      ContDiffAt ℝ 2 (expLift u) w := fun w hw₁ hw₂ => contDiffAt_expLift h₁ h₁₂ hu hw₁ hw₂
  have h2dS : ∀ w : ℂ, Real.log r₁ < w.re → w.re < Real.log r₂ →
      ContDiffAt ℝ 2 (dS (expLift u)) w := fun w hw₁ hw₂ => contDiffAt_dS h₁ h₁₂ hu hw₁ hw₂
  have e1 : ∀ s' ∈ Set.Ioo (Real.log r₁) (Real.log r₂),
      deriv (stripCoeff (expLift u) k) s' = stripCoeff (dS (expLift u)) k s' :=
    fun s' hs' => (strip_integral_hasDerivAt hs'.1 hs'.2 h2f).deriv
  have e2 : ∀ s' ∈ Set.Ioo (Real.log r₁) (Real.log r₂),
      deriv (stripCoeff (dS (expLift u)) k) s' = stripCoeff (dS (dS (expLift u))) k s' :=
    fun s' hs' => (strip_integral_hasDerivAt hs'.1 hs'.2 h2dS).deriv
  have hEq : (fun s' : ℝ => stripCoeff (dS (expLift u)) k s')
      =ᶠ[𝓝 s] (fun s' : ℝ => deriv (stripCoeff (expLift u) k) s') :=
    Filter.eventually_of_mem (Ioo_mem_nhds hs₁ hs₂) (fun s' hs' => (e1 s' hs').symm)
  have hfirst : deriv (deriv (stripCoeff (expLift u) k)) s
      = stripCoeff (dS (dS (expLift u))) k s := by
    rw [Filter.EventuallyEq.deriv_eq hEq.symm]
    exact e2 s ⟨hs₁, hs₂⟩
  rw [← hfirst]
  -- replace the integrand, using harmonicity and the chain rule
  have hpt : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
      dS (dS (expLift u)) ((s : ℂ) + (θ : ℂ) * Complex.I)
        * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))
      = -((deriv (deriv (fun θ : ℝ => expLift u ((s : ℂ) + (θ : ℂ) * Complex.I))) θ)
        * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))) := by
    intro θ _
    have hm₁ : Real.log r₁ < ((s : ℂ) + (θ : ℂ) * Complex.I).re := by rw [line_re]; exact hs₁
    have hm₂ : ((s : ℂ) + (θ : ℂ) * Complex.I).re < Real.log r₂ := by rw [line_re]; exact hs₂
    have hsum := dS_dS_add_dI_dI (harmonicAt_expLift h₁ h₁₂ hu hm₁ hm₂)
    have hC : dI (dI (expLift u)) ((s : ℂ) + (θ : ℂ) * Complex.I)
        = - dS (dS (expLift u)) ((s : ℂ) + (θ : ℂ) * Complex.I) :=
      eq_neg_of_add_eq_zero_right hsum
    rw [deriv_deriv_expLift_line h₁ h₁₂ hu hs₁ hs₂ θ, hC]
    ring
  have hstep : stripCoeff (dS (dS (expLift u))) k s
      = - (∫ θ in (0:ℝ)..(2 * Real.pi),
          deriv (deriv (fun θ : ℝ => expLift u ((s : ℂ) + (θ : ℂ) * Complex.I))) θ
            * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I))) := by
    simp only [stripCoeff]
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_neg]
  rw [hfirst, hstep]
  -- integration by parts
  have hIB := periodic_integral_deriv_deriv_exp
    (h := fun θ : ℝ => expLift u ((s : ℂ) + (θ : ℂ) * Complex.I))
    (ε := 1) (by norm_num) k ?_ ?_ ?_
  · rw [hIB]
    simp only [stripCoeff]
    push_cast
    ring
  · -- ContDiffOn
    intro θ _
    have hm₁ : Real.log r₁ < ((s : ℂ) + (θ : ℂ) * Complex.I).re := by rw [line_re]; exact hs₁
    have hm₂ : ((s : ℂ) + (θ : ℂ) * Complex.I).re < Real.log r₂ := by rw [line_re]; exact hs₂
    have hlin : ContDiffAt ℝ 2 (fun θ : ℝ => (s : ℂ) + (θ : ℂ) * Complex.I) θ :=
      (contDiffAt_const (n := 2) (c := (s : ℂ))).add
        (((Complex.ofRealCLM.contDiff (n := 2)).contDiffAt).mul
          (contDiffAt_const (n := 2) (c := Complex.I)))
    exact (ContDiffAt.comp (f := fun θ : ℝ => (s : ℂ) + (θ : ℂ) * Complex.I) (g := expLift u) θ
      (contDiffAt_expLift h₁ h₁₂ hu (n := 2) hm₁ hm₂) hlin).contDiffWithinAt
  · -- periodicity of h
    have h1 : (s : ℂ) + ((0:ℝ) : ℂ) * Complex.I = (s : ℂ) := by simp
    have h2 : (s : ℂ) + (((2 * Real.pi : ℝ)) : ℂ) * Complex.I
        = (s : ℂ) + 2 * Real.pi * Complex.I := by push_cast; ring
    rw [h1, h2]
    exact (expLift_add_two_pi u (s : ℂ)).symm
  · -- periodicity of deriv h
    rw [(hasDerivAt_expLift_line h₁ h₁₂ hu hs₁ hs₂ 0).deriv,
      (hasDerivAt_expLift_line h₁ h₁₂ hu hs₁ hs₂ (2 * Real.pi)).deriv]
    have hkey := fderiv_expLift_add_two_pi (u := u) h₁ h₁₂ hu (w := (s : ℂ))
      (by simpa using hs₁) (by simpa using hs₂)
    have h1 : (s : ℂ) + ((0:ℝ) : ℂ) * Complex.I = (s : ℂ) := by simp
    have h2 : (s : ℂ) + (((2 * Real.pi : ℝ)) : ℂ) * Complex.I
        = (s : ℂ) + 2 * Real.pi * Complex.I := by push_cast; ring
    rw [h1, h2]
    show dI (expLift u) (s : ℂ) = dI (expLift u) ((s : ℂ) + 2 * Real.pi * Complex.I)
    simp only [dI]
    rw [hkey]

/-! ## Solving the two second-order ODEs (in `HasDerivAt` form) -/

/-- The real exponential `s ↦ e^{c s}`, viewed as a complex number. -/
def E (c s : ℝ) : ℂ := (Real.exp (c * s) : ℂ)

lemma E_ne_zero (c s : ℝ) : E c s ≠ 0 := by
  simp only [E, Complex.ofReal_ne_zero]; exact Real.exp_ne_zero _

lemma E_inv (c s : ℝ) : (E c s)⁻¹ = E (-c) s := by
  rw [E, E, ← Complex.ofReal_inv, ← Real.exp_neg]
  congr 1
  ring_nf

lemma hasDerivAt_E (c s : ℝ) : HasDerivAt (fun s : ℝ => E c s) (E c s * (c : ℂ)) s := by
  have hreal : HasDerivAt (fun s : ℝ => Real.exp (c * s)) (Real.exp (c * s) * c) s := by
    simpa using ((hasDerivAt_id' s).const_mul c).exp
  have h := hreal.ofReal_comp
  simpa only [E, Complex.ofReal_mul] using h

lemma hasDerivAt_E_neg (c s : ℝ) : HasDerivAt (fun s : ℝ => E (-c) s) (E (-c) s * (-(c : ℂ))) s := by
  have h := hasDerivAt_E (-c) s
  have : ((-c : ℝ) : ℂ) = -(c : ℂ) := by push_cast; ring
  rw [← this]
  exact h

lemma ode_exp_hasDerivAt {c : ℝ} (hc : c ≠ 0) {F F' F'' : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (h1 : ∀ s ∈ Set.Ioo a b, HasDerivAt F (F' s) s)
    (h2 : ∀ s ∈ Set.Ioo a b, HasDerivAt F' (F'' s) s)
    (hode : ∀ s ∈ Set.Ioo a b, F'' s = (c : ℂ) ^ 2 * F s) :
    ∃ A B : ℂ, ∀ s ∈ Set.Ioo a b, F s = A * E c s + B * E (-c) s := by
  set U := Set.Ioo a b with hU
  have hUopen : IsOpen U := isOpen_Ioo
  have hUconn : IsPreconnected U := isPreconnected_Ioo
  have hmid : (a + b) / 2 ∈ U := ⟨by linarith, by linarith⟩
  set G₁ : ℝ → ℂ := fun s => (F' s - (c : ℂ) * F s) * E c s with hG₁
  set G₂ : ℝ → ℂ := fun s => (F' s + (c : ℂ) * F s) * E (-c) s with hG₂
  have hcc : (c : ℂ) ^ 2 = (c : ℂ) * (c : ℂ) := by ring
  have hG₁deriv : ∀ s ∈ U, HasDerivAt G₁ 0 s := by
    intro s hs
    have hsub : HasDerivAt (fun s => F' s - (c : ℂ) * F s) (F'' s - (c : ℂ) * F' s) s :=
      (h2 s hs).sub ((h1 s hs).const_mul (c : ℂ))
    have hmul := hsub.mul (hasDerivAt_E c s)
    have hzero : (F'' s - (c : ℂ) * F' s) * E c s + (F' s - (c : ℂ) * F s) * (E c s * (c : ℂ)) = 0 := by
      rw [hode s hs, hcc]; ring
    rw [hzero] at hmul
    rw [hG₁]
    exact hmul
  have hG₂deriv : ∀ s ∈ U, HasDerivAt G₂ 0 s := by
    intro s hs
    have hadd : HasDerivAt (fun s => F' s + (c : ℂ) * F s) (F'' s + (c : ℂ) * F' s) s :=
      (h2 s hs).add ((h1 s hs).const_mul (c : ℂ))
    have hmul := hadd.mul (hasDerivAt_E_neg c s)
    have hzero : (F'' s + (c : ℂ) * F' s) * E (-c) s + (F' s + (c : ℂ) * F s) * (E (-c) s * (-(c : ℂ))) = 0 := by
      rw [hode s hs, hcc]; ring
    rw [hzero] at hmul
    rw [hG₂]
    exact hmul
  have hG₁const : ∀ s' ∈ U, G₁ s' = G₁ ((a + b) / 2) := fun s' hs' => by
    exact IsOpen.is_const_of_deriv_eq_zero hUopen hUconn
      (fun t ht => (hG₁deriv t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hG₁deriv t ht).deriv) hs' hmid
  have hG₂const : ∀ s' ∈ U, G₂ s' = G₂ ((a + b) / 2) := fun s' hs' => by
    exact IsOpen.is_const_of_deriv_eq_zero hUopen hUconn
      (fun t ht => (hG₂deriv t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hG₂deriv t ht).deriv) hs' hmid
  refine ⟨G₂ ((a + b) / 2) / (2 * (c : ℂ)), -(G₁ ((a + b) / 2) / (2 * (c : ℂ))), ?_⟩
  intro s hs
  have hcC : (c : ℂ) ≠ 0 := by simpa using hc
  have h2c : 2 * (c : ℂ) ≠ 0 := by
    simp [hcC]
  have hK₁ : (F' s - (c : ℂ) * F s) * E c s = G₁ ((a + b) / 2) := hG₁const s hs
  have hK₂ : (F' s + (c : ℂ) * F s) * E (-c) s = G₂ ((a + b) / 2) := hG₂const s hs
  have h₁' : F' s - (c : ℂ) * F s = G₁ ((a + b) / 2) * E (-c) s := by
    have h := (eq_div_iff (E_ne_zero c s)).mpr hK₁
    rw [div_eq_mul_inv, E_inv] at h
    exact h
  have h₂' : F' s + (c : ℂ) * F s = G₂ ((a + b) / 2) * E c s := by
    have h := (eq_div_iff (E_ne_zero (-c) s)).mpr hK₂
    rw [div_eq_mul_inv, E_inv] at h
    simpa using h
  have hmain : (2 * (c : ℂ)) * F s
      = G₂ ((a + b) / 2) * E c s - G₁ ((a + b) / 2) * E (-c) s := by
    linear_combination h₂' - h₁'
  have hfin : F s = (G₂ ((a + b) / 2) * E c s - G₁ ((a + b) / 2) * E (-c) s) / (2 * (c : ℂ)) := by
    rw [eq_div_iff h2c]
    rw [mul_comm]
    exact hmain
  rw [hfin]
  ring

lemma ode_affine_hasDerivAt {F F' F'' : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (h1 : ∀ s ∈ Set.Ioo a b, HasDerivAt F (F' s) s)
    (h2 : ∀ s ∈ Set.Ioo a b, HasDerivAt F' (F'' s) s)
    (hode : ∀ s ∈ Set.Ioo a b, F'' s = 0) :
    ∃ A B : ℂ, ∀ s ∈ Set.Ioo a b, F s = A + B * (s : ℂ) := by
  set U := Set.Ioo a b with hU
  have hUopen : IsOpen U := isOpen_Ioo
  have hUconn : IsPreconnected U := isPreconnected_Ioo
  have hmid : (a + b) / 2 ∈ U := ⟨by linarith, by linarith⟩
  have hF'const : ∀ s ∈ U, F' s = F' ((a + b) / 2) := fun s hs =>
    IsOpen.is_const_of_deriv_eq_zero hUopen hUconn
      (fun t ht => (h2 t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => by rw [(h2 t ht).deriv, hode t ht]; rfl) hs hmid
  set K : ℂ := F' ((a + b) / 2) with hK
  have hderiv : ∀ s ∈ U, HasDerivAt (fun t : ℝ => F t - K * (t : ℂ)) 0 s := by
    intro s hs
    have hK' : F' s = K := hF'const s hs
    have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := by
      simpa using (hasDerivAt_id' s).ofReal_comp
    have h := (h1 s hs).sub (hid.const_mul K)
    have hz : F' s - K * 1 = 0 := by rw [hK']; ring
    rw [hz] at h
    exact h
  have hconst : ∀ s ∈ U, F s - K * (s : ℂ) = F ((a + b) / 2) - K * (((a + b) / 2 : ℝ) : ℂ) := fun s hs =>
    IsOpen.is_const_of_deriv_eq_zero hUopen hUconn
      (fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hderiv t ht).deriv) hs hmid
  refine ⟨F ((a + b) / 2) - K * (((a + b) / 2 : ℝ) : ℂ), K, fun s hs => ?_⟩
  have h := hconst s hs
  linear_combination (norm := ring) h
/-! ## The circle integral versus the strip integral -/

lemma circleCoeff_eq_stripCoeff {u : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (k : ℤ) :
    circleCoeff u k r = stripCoeff (expLift u) k (Real.log r) := by
  simp only [circleCoeff, stripCoeff]
  congr 1
  funext θ
  congr 1
  simp only [expLift]
  congr 1
  rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]

/-! ## Converting the exponential solutions into powers of `r` -/

lemma E_eq_zpow {r : ℝ} (hr : 0 < r) (k : ℤ) : E (k : ℝ) (Real.log r) = (r : ℂ) ^ k := by
  have h1 : Real.exp ((k : ℝ) * Real.log r) = r ^ (k : ℝ) := by
    rw [Real.rpow_def_of_pos hr]
    congr 1
    ring
  have h2 : r ^ (k : ℝ) = r ^ k := by simpa using Real.rpow_intCast r k
  simp only [E]
  rw [h1, h2, Complex.ofReal_zpow]

lemma E_neg_eq_zpow {r : ℝ} (hr : 0 < r) (k : ℤ) : E (-(k : ℝ)) (Real.log r) = (r : ℂ) ^ (-k) := by
  have hx : -(k : ℝ) * Real.log r = -((k : ℝ) * Real.log r) := by ring
  have h2 : (↑(Real.exp ((k : ℝ) * Real.log r)) : ℂ) = (r : ℂ) ^ k := E_eq_zpow hr k
  simp only [E]
  rw [hx, Real.exp_neg, Complex.ofReal_inv, h2, zpow_neg]

/-! ## The main theorem -/

theorem harmonic_annulus_fourier_structure
    {u : ℂ → ℝ} {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂)
    (hu : ∀ z : ℂ, r₁ < ‖z‖ → ‖z‖ < r₂ → InnerProductSpace.HarmonicAt u z) :
    (∃ α : ℝ, ∃ β : ℝ, ∀ r : ℝ, r₁ < r → r < r₂ →
        (∫ θ in (0:ℝ)..(2 * Real.pi), u (r * Complex.exp (θ * Complex.I)))
          = 2 * Real.pi * (α + β * Real.log r)) ∧
    (∀ k : ℤ, k ≠ 0 → ∃ A B : ℂ, ∀ r : ℝ, r₁ < r → r < r₂ →
        (∫ θ in (0:ℝ)..(2 * Real.pi),
            (u (r * Complex.exp (θ * Complex.I)) : ℂ) * Complex.exp (-(((k : ℝ) * θ : ℂ) * Complex.I)))
          = 2 * Real.pi * (A * (r : ℂ) ^ k + B * (r : ℂ) ^ (-k))) := by
  have hδ : Real.log r₁ < Real.log r₂ := Real.log_lt_log h₁ h₁₂
  have hF2 : ∀ w : ℂ, Real.log r₁ < w.re → w.re < Real.log r₂ → ContDiffAt ℝ 2 (expLift u) w :=
    fun w hw₁ hw₂ => contDiffAt_expLift h₁ h₁₂ hu hw₁ hw₂
  have hG2 : ∀ w : ℂ, Real.log r₁ < w.re → w.re < Real.log r₂ →
      ContDiffAt ℝ 2 (dS (expLift u)) w :=
    fun w hw₁ hw₂ => contDiffAt_dS h₁ h₁₂ hu hw₁ hw₂
  have hd1 : ∀ k : ℤ, ∀ s ∈ Set.Ioo (Real.log r₁) (Real.log r₂),
      HasDerivAt (stripCoeff (expLift u) k) (stripCoeff (dS (expLift u)) k s) s :=
    fun k s hs => strip_integral_hasDerivAt hs.1 hs.2 hF2
  have hd2 : ∀ k : ℤ, ∀ s ∈ Set.Ioo (Real.log r₁) (Real.log r₂),
      HasDerivAt (stripCoeff (dS (expLift u)) k) (stripCoeff (dS (dS (expLift u))) k s) s :=
    fun k s hs => strip_integral_hasDerivAt hs.1 hs.2 hG2
  have hode : ∀ k : ℤ, ∀ s ∈ Set.Ioo (Real.log r₁) (Real.log r₂),
      stripCoeff (dS (dS (expLift u))) k s = ((k : ℝ) : ℂ) ^ 2 * stripCoeff (expLift u) k s := by
    intro k s hs
    have h := stripCoeff_second_deriv h₁ h₁₂ hu k hs.1 hs.2
    simpa using h
  constructor
  · -- the `k = 0` case
    obtain ⟨A, B, hAB⟩ := ode_affine_hasDerivAt (F := stripCoeff (expLift u) 0)
      (F' := stripCoeff (dS (expLift u)) 0) (F'' := stripCoeff (dS (dS (expLift u))) 0)
      hδ (hd1 0) (hd2 0) (by intro s hs; rw [hode 0 s hs]; simp)
    refine ⟨A.re / (2 * Real.pi), B.re / (2 * Real.pi), fun r hr₁ hr₂ => ?_⟩
    have hr : 0 < r := lt_trans h₁ hr₁
    have hs₁ : Real.log r₁ < Real.log r := Real.log_lt_log h₁ hr₁
    have hs₂ : Real.log r < Real.log r₂ := Real.log_lt_log hr hr₂
    have hval : circleCoeff u 0 r = A + B * (Real.log r : ℂ) := by
      rw [circleCoeff_eq_stripCoeff hr 0, hAB (Real.log r) ⟨hs₁, hs₂⟩]
    have hcirc : circleCoeff u 0 r
        = ((∫ θ in (0:ℝ)..(2 * Real.pi), u (r * Complex.exp (θ * Complex.I)) : ℝ) : ℂ) := by
      simp only [circleCoeff]
      rw [show (fun θ : ℝ => (u (r * Complex.exp (θ * Complex.I)) : ℂ)
              * Complex.exp (-((((0 : ℤ) : ℝ) * θ : ℂ) * Complex.I)))
          = fun θ : ℝ => (u (r * Complex.exp (θ * Complex.I)) : ℂ) by
        funext θ; simp]
      rw [intervalIntegral.integral_ofReal]
    have heq : ((∫ θ in (0:ℝ)..(2 * Real.pi), u (r * Complex.exp (θ * Complex.I)) : ℝ) : ℂ)
        = A + B * (Real.log r : ℂ) := by rw [← hcirc, hval]
    have hre : (∫ θ in (0:ℝ)..(2 * Real.pi), u (r * Complex.exp (θ * Complex.I)))
        = (A + B * (Real.log r : ℂ)).re := congrArg Complex.re heq
    have hre' : (A + B * (Real.log r : ℂ)).re = A.re + B.re * Real.log r := by
      simp [Complex.add_re, Complex.mul_re]
    rw [hre, hre']
    field_simp
  · -- the `k ≠ 0` case
    intro k hk
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    obtain ⟨A, B, hAB⟩ := ode_exp_hasDerivAt hkR (F := stripCoeff (expLift u) k)
      (F' := stripCoeff (dS (expLift u)) k) (F'' := stripCoeff (dS (dS (expLift u))) k)
      hδ (hd1 k) (hd2 k) (hode k)
    refine ⟨A / (2 * Real.pi), B / (2 * Real.pi), fun r hr₁ hr₂ => ?_⟩
    have hr : 0 < r := lt_trans h₁ hr₁
    have hs₁ : Real.log r₁ < Real.log r := Real.log_lt_log h₁ hr₁
    have hs₂ : Real.log r < Real.log r₂ := Real.log_lt_log hr hr₂
    have hval : circleCoeff u k r = A * (r : ℂ) ^ k + B * (r : ℂ) ^ (-k) := by
      rw [circleCoeff_eq_stripCoeff hr k, hAB (Real.log r) ⟨hs₁, hs₂⟩,
        E_eq_zpow hr k, E_neg_eq_zpow hr k]
    change circleCoeff u k r
      = 2 * Real.pi * (A / (2 * Real.pi) * (r : ℂ) ^ k + B / (2 * Real.pi) * (r : ℂ) ^ (-k))
    rw [hval]
    have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
    field_simp

end Work.Potential
