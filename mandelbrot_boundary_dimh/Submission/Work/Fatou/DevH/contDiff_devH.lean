import Mathlib
import Submission.Work.Fatou.DevH.deriv_setup
import Submission.Work.Fatou.DevH.basic
import Submission.Work.Fatou.Smooth
import Submission.Work.Fatou.Setup

namespace Work.Fatou.DevH

open MandelDim

/-!
# `devH` is `C¹`

`devH x₀ F ζ = x₀ + ζ + χ(Re ζ)·ε(x₀+ζ-1)` is a *convex combination*, with weight `χ = smoothstep`,
of the translation `ζ ↦ x₀ + ζ` and of the perturbed map `ζ ↦ F(x₀+ζ-1)`:

`devH x₀ F ζ = (1 - χ(Re ζ))·(x₀ + ζ) + χ(Re ζ)·F(x₀+ζ-1)`.

Since `χ` is `C¹` (it depends only on `Re ζ`) and `ζ ↦ x₀+ζ-1` is affine, this displays `devH` as a
`C¹` function as soon as `F` is `C¹` at the single point `x₀+ζ-1`.

The hypothesis on `F` is only that it is a near-translation on the *open* region `Qreg b₁ b₂`, so
`F` is holomorphic — hence `C¹` — only at points of `Qreg`.  The perturbation `devH` evaluates `F`
only at `x₀+ζ-1`, and `x₀+ζ-1 ∈ Qreg` exactly when `1/8 ≤ Re ζ ≤ 15/8` (the transition strip of
`χ`, modulo the boundary points, where `strip_seven_subset_Qreg` still applies).  Outside that
strip the cut-off `χ` vanishes identically on a *neighbourhood* of `ζ`, so `devH` agrees locally
with the translation.  This is the only point at which the shape of the region `/ the cut-off
matters; the rest is the chain rule.
-/

noncomputable section

/-- `smoothstep` is `C¹`; proved from the identity `smoothstep = Φ(·+4/3) - Φ` where `Φ` is the
glued cubic, using only the `C¹`-regularity of the elementary ramp `Work.Fatou.ramp`. -/
theorem contDiff_smoothstep' : ContDiff ℝ 1 Work.Fatou.smoothstep := by
  have hfun : Work.Fatou.smoothstep = fun s : ℝ =>
      Work.Fatou.ramp ((s - 1 / 8) / (3 / 4)) - Work.Fatou.ramp ((s - 9 / 8) / (3 / 4)) :=
    funext Work.Fatou.smoothstep_eq_ramp
  rw [hfun]
  exact (Work.Fatou.contDiff_ramp.comp (by fun_prop)).sub
    (Work.Fatou.contDiff_ramp.comp (by fun_prop))

/-- The cut-off `ζ ↦ χ(Re ζ)` viewed as a complex-valued function of `ζ` is `C¹`. -/
theorem contDiffAt_smoothstep_re (ζ : ℂ) :
    ContDiffAt ℝ 1 (fun ζ' : ℂ => ((Work.Fatou.smoothstep ζ'.re : ℝ) : ℂ)) ζ := by
  have h1 : ContDiff ℝ 1 (fun ζ' : ℂ => Work.Fatou.smoothstep ζ'.re) :=
    contDiff_smoothstep'.comp Complex.reCLM.contDiff
  have h2 : ContDiff ℝ 1 (fun ζ' : ℂ => ((Work.Fatou.smoothstep ζ'.re : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h1
  exact h2.contDiffAt

/-- The convex-combination form of `devH`, valid for every `ζ` (no hypotheses on `F`). -/
theorem devH_eq_combination (x₀ : ℝ) (F : ℂ → ℂ) (ζ : ℂ) :
    Work.Fatou.devH x₀ F ζ = (1 - ((Work.Fatou.smoothstep ζ.re : ℝ) : ℂ)) * ((x₀ : ℂ) + ζ)
      + ((Work.Fatou.smoothstep ζ.re : ℝ) : ℂ) * F (shiftArg x₀ ζ) := by
  rw [Work.Fatou.devH_apply, Work.Fatou.eps_apply, shiftArg_eq]
  ring

/-- If `F` is `C¹` at the point read by `devH x₀ F` at `ζ`, then `devH x₀ F` is `C¹` at `ζ`. -/
theorem contDiffAt_devH_of_contDiffAt {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ}
    (hF : ContDiffAt ℝ 1 F (shiftArg x₀ ζ)) : ContDiffAt ℝ 1 (Work.Fatou.devH x₀ F) ζ := by
  have hchi := contDiffAt_smoothstep_re ζ
  have hone : ContDiffAt ℝ 1
      (fun ζ' : ℂ => (1 : ℂ) - ((Work.Fatou.smoothstep ζ'.re : ℝ) : ℂ)) ζ :=
    contDiffAt_const.sub hchi
  have hlin : ContDiffAt ℝ 1 (fun ζ' : ℂ => (x₀ : ℂ) + ζ') ζ := by fun_prop
  have harg : ContDiffAt ℝ 1 (fun ζ' : ℂ => shiftArg x₀ ζ') ζ := by
    have hfun : (fun ζ' : ℂ => shiftArg x₀ ζ') = fun ζ' : ℂ => ζ' + ((x₀ : ℂ) - 1) := by
      ext w; simp [shiftArg]; ring
    rw [hfun]; fun_prop
  have hcomp : ContDiffAt ℝ 1 (fun ζ' : ℂ => F (shiftArg x₀ ζ')) ζ := hF.comp ζ harg
  have hmain : ContDiffAt ℝ 1 (fun ζ' : ℂ =>
      (1 - ((Work.Fatou.smoothstep ζ'.re : ℝ) : ℂ)) * ((x₀ : ℂ) + ζ')
        + ((Work.Fatou.smoothstep ζ'.re : ℝ) : ℂ) * F (shiftArg x₀ ζ')) ζ :=
    (hone.mul hlin).add (hchi.mul hcomp)
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards with ζ'
  exact devH_eq_combination x₀ F ζ'

/-- `devH` is `C¹` at points strictly left of the transition strip: there `χ` vanishes on a
neighbourhood and `devH` is locally the translation `ζ ↦ x₀ + ζ` (no hypothesis on `F`). -/
theorem contDiffAt_devH_of_re_lt {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ} (h : ζ.re < 1 / 8) :
    ContDiffAt ℝ 1 (Work.Fatou.devH x₀ F) ζ := by
  have hlin : ContDiffAt ℝ 1 (fun ζ' : ℂ => (x₀ : ℂ) + ζ') ζ := by fun_prop
  refine hlin.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds h] with ζ' hζ
  exact Work.Fatou.devH_of_le_one_eighth hζ.le

/-- `devH` is `C¹` at points strictly right of the transition strip (no hypothesis on `F`). -/
theorem contDiffAt_devH_of_re_gt {x₀ : ℝ} {F : ℂ → ℂ} {ζ : ℂ} (h : 15 / 8 < ζ.re) :
    ContDiffAt ℝ 1 (Work.Fatou.devH x₀ F) ζ := by
  have hlin : ContDiffAt ℝ 1 (fun ζ' : ℂ => (x₀ : ℂ) + ζ') ζ := by fun_prop
  refine hlin.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h] with ζ' hζ
  exact Work.Fatou.devH_of_ge_fifteen hζ.le

/-- `devH x₀ F ζ = x₀ + ζ + χ(Re ζ)·ε(x₀+ζ-1)` (with `χ = Work.Fatou.smoothstep`, the `C¹` cut-off
which is `0` on `(-∞,1/8]`, `1` on `[7/8,9/8]` and `0` on `[15/8,∞)`, and `ε = Work.Fatou.eps F`) is
`C¹` on the whole plane, for `F` a near-translation on `Qreg b₁ b₂`. -/
theorem contDiff_devH {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂)) :
    ContDiff ℝ 1 (Work.Fatou.devH (Work.Fatou.xOf b₁ b₂) F) := by
  rw [contDiff_iff_contDiffAt]
  intro ζ
  rcases lt_or_ge ζ.re (1 / 8) with h | h
  · exact contDiffAt_devH_of_re_lt h
  rcases le_or_gt ζ.re (15 / 8) with h2 | h2
  · -- inside the transition strip: `F` reads a point of the open region `Qreg`
    have hw : shiftArg (Work.Fatou.xOf b₁ b₂) ζ ∈ MandelDim.Qreg b₁ b₂ :=
      Work.Fatou.xOf_add_mem_Qreg hadm h h2
    exact contDiffAt_devH_of_contDiffAt
      ((contDiffOn_of_nearTranslation hF).contDiffAt ((isOpen_Qreg b₁ b₂).mem_nhds hw))
  · exact contDiffAt_devH_of_re_gt h2

end

end Work.Fatou.DevH
