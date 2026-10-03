import Submission.Work.Fatou.Smooth
import Submission.Work.Fatou.DevH.basic

/-!
# `devH`: the derivative, its correction term, and the elementary estimates

`devH x₀ F ζ = (x₀ : ℂ) + ζ + χ(Re ζ) · ε(x₀ + ζ - 1)` is the interpolation between the
translation `ζ ↦ x₀ + ζ` and `F`; here `χ = Work.Fatou.smoothstep` and `ε = Work.Fatou.eps F`.

This file sets up the notation used to *differentiate* `devH`:

* `shiftArg x₀ ζ = x₀ + ζ - 1` is the point at which the error term is evaluated;
* `chiDerivCLM d` is the `ℝ`-linear map `v ↦ (Re v)·d`, the derivative of `ζ ↦ χ(Re ζ)`;
* `c1`, `c2` are the two complex numbers in which the derivative is expressed:
  `D devH ζ = id + c2·id + c1·(Re ·)`, i.e. `c1 = ε(w)·χ'(Re ζ)` and `c2 = χ(Re ζ)·ε'(w)`;
* `devHCorr x₀ F ζ` and `devHDeriv x₀ F ζ` are the correction term and the candidate derivative.

It also contains the elementary facts used by the estimates: `Qreg` is open,
`smoothstep` and its derivative vanish off the transition strip `(1/8, 15/8)`, and the chain
rules for `ζ ↦ χ(Re ζ)` and for the error term.
-/

namespace Work.Fatou.DevH

open MandelDim Filter Set
open scoped Topology

noncomputable section

/-! ### The point at which `devH` reads off `F` -/

/-- `x₀ + ζ - 1`: the argument at which `devH x₀ F ζ` evaluates `eps F`. -/
def shiftArg (x₀ : ℝ) (ζ : ℂ) : ℂ := (x₀ : ℂ) + ζ - 1

@[simp] theorem shiftArg_eq (x₀ : ℝ) (ζ : ℂ) : shiftArg x₀ ζ = (x₀ : ℂ) + ζ - 1 := rfl

@[simp] theorem shiftArg_re (x₀ : ℝ) (ζ : ℂ) : (shiftArg x₀ ζ).re = x₀ + ζ.re - 1 := by
  simp [shiftArg]

/-- If `1/8 ≤ Re ζ ≤ 15/8` then the point read by `devH` lies in `Qreg`. -/
theorem shiftArg_mem_Qreg {b₁ b₂ : Option ℂ} (hadm : QAdm b₁ b₂) {ζ : ℂ}
    (h₁ : (1 / 8 : ℝ) ≤ ζ.re) (h₂ : ζ.re ≤ 15 / 8) :
    shiftArg (xOf b₁ b₂) ζ ∈ Qreg b₁ b₂ :=
  xOf_add_mem_Qreg hadm h₁ h₂

/-! ### `Qreg` is open, and `F` is differentiable at its points -/

theorem isOpen_Qreg (b₁ b₂ : Option ℂ) : IsOpen (Qreg b₁ b₂) := by
  have h₁ : ∀ a : ℂ, IsOpen {z : ℂ | -|(z - a).im| < (z - a).re} := by
    intro a
    have heq : {z : ℂ | -|(z - a).im| < (z - a).re} =
        {z : ℂ | 0 < (z - a).re + |(z - a).im|} := by
      ext z
      simp only [Set.mem_ofPred_eq]
      constructor <;> intro h <;> linarith [abs_nonneg ((z - a).im)]
    rw [heq]
    exact isOpen_lt continuous_const (by fun_prop)
  have h₂ : ∀ b : ℂ, IsOpen {z : ℂ | (z - b).re < |(z - b).im|} := by
    intro b
    have heq : {z : ℂ | (z - b).re < |(z - b).im|} =
        {z : ℂ | 0 < |(z - b).im| - (z - b).re} := by
      ext z
      simp only [Set.mem_ofPred_eq]
      constructor <;> intro h <;> linarith [abs_nonneg ((z - b).im)]
    rw [heq]
    exact isOpen_lt continuous_const (by fun_prop)
  rcases b₁ with - | a
  · rcases b₂ with - | b
    · have h : Qreg (none : Option ℂ) none = Set.univ := by ext z; simp [Qreg]
      rw [h]; exact isOpen_univ
    · have h : Qreg (none : Option ℂ) (some b) = {z : ℂ | (z - b).re < |(z - b).im|} := by
        ext z; simp [Qreg]
      rw [h]; exact h₂ b
  · rcases b₂ with - | b
    · have h : Qreg (some a) none = {z : ℂ | -|(z - a).im| < (z - a).re} := by
        ext z; simp [Qreg]
      rw [h]; exact h₁ a
    · have h : Qreg (some a) (some b) =
          {z : ℂ | -|(z - a).im| < (z - a).re} ∩ {z : ℂ | (z - b).re < |(z - b).im|} := by
        ext z; simp [Qreg]
      rw [h]; exact (h₁ a).inter (h₂ b)

/-- `F` is complex differentiable at every point of `Qreg`. -/
theorem differentiableAt_of_mem_Qreg {b₁ b₂ : Option ℂ} {F : ℂ → ℂ}
    (hF : NearTranslationOn F (Qreg b₁ b₂)) {z : ℂ} (hz : z ∈ Qreg b₁ b₂) :
    DifferentiableAt ℂ F z := by
  have hs : Qreg b₁ b₂ ∈ 𝓝 z := (isOpen_Qreg b₁ b₂).mem_nhds hz
  exact hF.1.differentiableAt hs

/-- `F` is `C¹` on `Qreg` (it is holomorphic there). -/
theorem contDiffOn_of_nearTranslation {b₁ b₂ : Option ℂ} {F : ℂ → ℂ}
    (hF : NearTranslationOn F (Qreg b₁ b₂)) : ContDiffOn ℝ 1 F (Qreg b₁ b₂) :=
  ContDiffOn.restrict_scalars ℝ (hF.1.contDiffOn (isOpen_Qreg b₁ b₂))

/-! ### The norm bounds for `ε` on `Qreg` -/

theorem norm_eps_le {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hF : NearTranslationOn F (Qreg b₁ b₂))
    {z : ℂ} (hz : z ∈ Qreg b₁ b₂) : ‖eps F z‖ ≤ 1 / 32 := (hF.2 z hz).1

theorem norm_deriv_sub_one_le {b₁ b₂ : Option ℂ} {F : ℂ → ℂ}
    (hF : NearTranslationOn F (Qreg b₁ b₂)) {z : ℂ} (hz : z ∈ Qreg b₁ b₂) :
    ‖deriv F z - 1‖ ≤ 1 / 32 := (hF.2 z hz).2

/-! ### `smoothstep` and its derivative vanish off the transition strip -/

/-- `smoothstep` is differentiable everywhere, with derivative its `deriv`. -/
theorem hasDerivAt_smoothstep_deriv (t : ℝ) : HasDerivAt smoothstep (deriv smoothstep t) t := by
  rw [(hasDerivAt_smoothstep t).deriv]
  exact hasDerivAt_smoothstep t

theorem deriv_smoothstep_eq_zero_of_le {t : ℝ} (h : t ≤ 1 / 8) : deriv smoothstep t = 0 := by
  rw [(hasDerivAt_smoothstep t).deriv, rampD_of_nonpos (ramp_arg₁_nonpos h),
    rampD_of_nonpos (ramp_arg₂_nonpos (by linarith))]
  ring

theorem deriv_smoothstep_eq_zero_of_ge {t : ℝ} (h : 15 / 8 ≤ t) : deriv smoothstep t = 0 := by
  rw [(hasDerivAt_smoothstep t).deriv, rampD_of_one_le (ramp_arg₁_one_le (by linarith)),
    rampD_of_one_le (ramp_arg₂_one_le h)]
  ring

/-- The transition strip: the set where `smoothstep` (or its derivative) can be non-zero. -/
theorem lt_re_of_smoothstep_ne_zero {t : ℝ} (h : smoothstep t ≠ 0) : 1 / 8 < t := by
  by_contra hc
  exact h (smoothstep_eq_zero_of_le (not_lt.mp hc))

theorem re_lt_of_smoothstep_ne_zero {t : ℝ} (h : smoothstep t ≠ 0) : t < 15 / 8 := by
  by_contra hc
  exact h (smoothstep_eq_zero_of_ge (not_lt.mp hc))

theorem lt_re_of_deriv_smoothstep_ne_zero {t : ℝ} (h : deriv smoothstep t ≠ 0) : 1 / 8 < t := by
  by_contra hc
  exact h (deriv_smoothstep_eq_zero_of_le (not_lt.mp hc))

theorem re_lt_of_deriv_smoothstep_ne_zero {t : ℝ} (h : deriv smoothstep t ≠ 0) : t < 15 / 8 := by
  by_contra hc
  exact h (deriv_smoothstep_eq_zero_of_ge (not_lt.mp hc))

/-! ### The derivative of `ζ ↦ χ(Re ζ)` -/

/-- The `ℝ`-linear map `v ↦ (Re v)·d`: the derivative of `ζ ↦ χ(Re ζ)` where `χ' = d`. -/
def chiDerivCLM (d : ℝ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℝ ((d : ℝ) : ℂ)).comp Complex.reCLM

@[simp] theorem chiDerivCLM_apply (d : ℝ) (v : ℂ) :
    chiDerivCLM d v = ((v.re : ℝ) : ℂ) * (d : ℂ) := by
  simp [chiDerivCLM, ContinuousLinearMap.toSpanSingleton_apply]

@[simp] theorem chiDerivCLM_zero : chiDerivCLM 0 = 0 := by
  ext v
  simp

/-- Chain rule for a differentiable function of `Re ζ`. -/
theorem hasFDerivAt_ofReal_comp_re {f : ℝ → ℝ} {f' : ℝ} {ζ : ℂ} (hf : HasDerivAt f f' ζ.re) :
    HasFDerivAt (fun ζ' : ℂ => ((f ζ'.re : ℝ) : ℂ)) (chiDerivCLM f') ζ := by
  have h1 : HasFDerivAt (fun ζ' : ℂ => f ζ'.re)
      ((ContinuousLinearMap.toSpanSingleton ℝ f').comp Complex.reCLM) ζ :=
    hf.hasFDerivAt.comp ζ Complex.reCLM.hasFDerivAt
  have hCLM : chiDerivCLM f' = Complex.ofRealCLM ∘SL
      (ContinuousLinearMap.toSpanSingleton ℝ f' ∘SL Complex.reCLM) := by
    ext v
    simp [chiDerivCLM, ContinuousLinearMap.toSpanSingleton_apply]
  rw [hCLM]
  exact Complex.ofRealCLM.hasFDerivAt.comp ζ h1

/-- `devH x₀ F` and the cut-off `ζ ↦ χ(Re ζ)`: the derivative of the cut-off factor. -/
theorem hasFDerivAt_smoothstep_re (ζ : ℂ) :
    HasFDerivAt (fun ζ' : ℂ => ((smoothstep ζ'.re : ℝ) : ℂ))
      (chiDerivCLM (deriv smoothstep ζ.re)) ζ :=
  hasFDerivAt_ofReal_comp_re (hasDerivAt_smoothstep_deriv ζ.re)

/-! ### The real derivative of the error term -/

/-- For a holomorphic `F`, the real derivative of `eps F = F - (· + 1)` at `w` is multiplication
by `deriv F w - 1`. -/
theorem hasFDerivAt_eps {F : ℂ → ℂ} {w : ℂ} (hF : DifferentiableAt ℂ F w) :
    HasFDerivAt (eps F) (ContinuousLinearMap.mul ℝ ℂ (deriv F w - 1)) w := by
  have h1 : HasFDerivAt F ((ContinuousLinearMap.toSpanSingleton ℂ (deriv F w)).restrictScalars ℝ) w :=
    hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hCLM : (ContinuousLinearMap.toSpanSingleton ℂ (deriv F w)).restrictScalars ℝ =
      ContinuousLinearMap.mul ℝ ℂ (deriv F w) := by
    ext z
    simp [ContinuousLinearMap.toSpanSingleton_apply]
    ring
  rw [hCLM] at h1
  have h2 : HasFDerivAt (fun z : ℂ => z + 1) (1 : ℂ →L[ℝ] ℂ) w :=
    (hasFDerivAt_id (𝕜 := ℝ) w).add_const (1 : ℂ)
  have h3 := h1.sub h2
  have h4 : ContinuousLinearMap.mul ℝ ℂ (deriv F w) - (1 : ℂ →L[ℝ] ℂ) =
      ContinuousLinearMap.mul ℝ ℂ (deriv F w - 1) := by
    ext v
    simp
  rwa [h4] at h3

/-- The real derivative of `ζ ↦ ε(x₀ + ζ - 1)`. -/
theorem hasFDerivAt_eps_shift {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ}
    (hF : DifferentiableAt ℂ F (shiftArg x₀ ζ)) :
    HasFDerivAt (fun ζ' : ℂ => eps F (shiftArg x₀ ζ'))
      (ContinuousLinearMap.mul ℝ ℂ (deriv F (shiftArg x₀ ζ) - 1)) ζ := by
  have he : HasFDerivAt (eps F)
      (ContinuousLinearMap.mul ℝ ℂ (deriv F (shiftArg x₀ ζ) - 1)) (shiftArg x₀ ζ) :=
    hasFDerivAt_eps hF
  have haff : HasFDerivAt (fun ζ' : ℂ => shiftArg x₀ ζ') (ContinuousLinearMap.id ℝ ℂ) ζ := by
    have h1 : HasFDerivAt (fun ζ' : ℂ => ζ' + ((x₀ : ℂ) - 1)) (ContinuousLinearMap.id ℝ ℂ) ζ :=
      (hasFDerivAt_id (𝕜 := ℝ) ζ).add_const ((x₀ : ℂ) - 1)
    have hfun : (fun ζ' : ℂ => ζ' + ((x₀ : ℂ) - 1)) = fun ζ' : ℂ => shiftArg x₀ ζ' := by
      ext w
      simp [shiftArg]
      ring
    rw [hfun] at h1
    exact h1
  have h := he.comp ζ haff
  simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using h

/-! ### The correction term and the candidate derivative of `devH` -/

/-- `c1 = ε(x₀+ζ-1)·χ'(Re ζ)`: the coefficient of the `Re`-derivative. -/
def c1 (x₀ : ℝ) (F : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  eps F (shiftArg x₀ ζ) * ((deriv smoothstep ζ.re : ℝ) : ℂ)

/-- `c2 = χ(Re ζ)·(F'(x₀+ζ-1) - 1)`: the coefficient of the identity part. -/
def c2 (x₀ : ℝ) (F : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  ((smoothstep ζ.re : ℝ) : ℂ) * (deriv F (shiftArg x₀ ζ) - 1)

/-- The correction term `D devH - id`. -/
def devHCorr (x₀ : ℝ) (F : ℂ → ℂ) (ζ : ℂ) : ℂ →L[ℝ] ℂ :=
  (((smoothstep ζ.re : ℝ) : ℂ)) • (ContinuousLinearMap.mul ℝ ℂ (deriv F (shiftArg x₀ ζ) - 1))
    + (eps F (shiftArg x₀ ζ)) • (chiDerivCLM (deriv smoothstep ζ.re))

/-- The candidate derivative of `devH`: `id + corr` (written as `corr + id` so that it matches the
shape produced by `HasFDerivAt.mul`). -/
def devHDeriv (x₀ : ℝ) (F : ℂ → ℂ) (ζ : ℂ) : ℂ →L[ℝ] ℂ :=
  devHCorr x₀ F ζ + ContinuousLinearMap.id ℝ ℂ

theorem devHCorr_eq (x₀ : ℝ) (F : ℂ → ℂ) (ζ : ℂ) :
    devHCorr x₀ F ζ =
      (((smoothstep ζ.re : ℝ) : ℂ)) • (ContinuousLinearMap.mul ℝ ℂ (deriv F (shiftArg x₀ ζ) - 1))
        + (eps F (shiftArg x₀ ζ)) • (chiDerivCLM (deriv smoothstep ζ.re)) := rfl

/-- `(ContinuousLinearMap.mul ℝ ℂ a) b = a * b`. -/
@[simp] theorem mulCLM_apply (a b : ℂ) : (ContinuousLinearMap.mul ℝ ℂ a) b = a * b := rfl

/-- The explicit action of the candidate derivative. -/
theorem devHDeriv_apply (x₀ : ℝ) (F : ℂ → ℂ) (ζ v : ℂ) :
    devHDeriv x₀ F ζ v = v + c2 x₀ F ζ * v + c1 x₀ F ζ * (v.re : ℂ) := by
  simp only [devHDeriv, devHCorr, add_apply, ContinuousLinearMap.id_apply,
    smul_apply, chiDerivCLM_apply, mulCLM_apply, smul_eq_mul]
  simp only [c1, c2, shiftArg]
  ring

theorem devHDeriv_one (x₀ : ℝ) (F : ℂ → ℂ) (ζ : ℂ) :
    devHDeriv x₀ F ζ 1 = 1 + c1 x₀ F ζ + c2 x₀ F ζ := by
  rw [devHDeriv_apply]
  simp
  ring

theorem devHDeriv_I (x₀ : ℝ) (F : ℂ → ℂ) (ζ : ℂ) :
    devHDeriv x₀ F ζ Complex.I = Complex.I + c2 x₀ F ζ * Complex.I := by
  rw [devHDeriv_apply]
  simp

/-- `c1` vanishes when the cut-off is inactive. -/
theorem c1_eq_zero_of_le {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ} (h : ζ.re ≤ 1 / 8) : c1 x₀ F ζ = 0 := by
  simp [c1, deriv_smoothstep_eq_zero_of_le h]

theorem c1_eq_zero_of_ge {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ} (h : 15 / 8 ≤ ζ.re) : c1 x₀ F ζ = 0 := by
  simp [c1, deriv_smoothstep_eq_zero_of_ge h]

theorem c2_eq_zero_of_le {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ} (h : ζ.re ≤ 1 / 8) : c2 x₀ F ζ = 0 := by
  simp [c2, smoothstep_eq_zero_of_le h]

theorem c2_eq_zero_of_ge {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ} (h : 15 / 8 ≤ ζ.re) : c2 x₀ F ζ = 0 := by
  simp [c2, smoothstep_eq_zero_of_ge h]

end

end Work.Fatou.DevH
