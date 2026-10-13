/-
# `EpsE4Thr/ZeroOrderFlow.lean` — the projected family and the scheme's right-hand side

Two definitional/rewriting bridges used by the class-invariance analysis of the projected
`ε`-scheme (and by the first-order refutation of `NOTES_EpsLocalPStar_FALSE.md`):

* `epsWP_eq_profRHS` — the pre-mollified right-hand side of the projected scheme at a *family* is
  `profRHS` at the projected slice (the family-level form of
  `EpsLocalPStar.epsRHPSlice_eq_profRHS`; it is `rfl`, because `epsWP` is slice-determined);
* `epsRHSP_eq_profRHS_family` — consequently the scheme's right-hand side is
  `Pz (J_ε (profRHS (slice (JfamP ρ ε g) τ)))`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.ZeroOrder
import Submission.Work.FTS.StrongEps.EpsLocalPSmall
import Submission.Work.FTS.StrongEps.JepsBasic
import Submission.Work.FTS.StrongEps.BumpDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- The pre-mollified right-hand side of the projected scheme at the family `g` is `profRHS`
evaluated at the projected slice `slice (JfamP ρ ε g) τ`.  This is the family-level form of
`EpsLocalPStar.epsRHPSlice_eq_profRHS`, and it is definitional. -/
theorem epsWP_eq_profRHS (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn)
    (g : Fam) (τ : ℝ) :
    Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ
      = Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (slice (JfamP ρ ε g) τ) :=
  rfl

/-- The projected scheme's right-hand side is the projection of the mollification of `profRHS`
at the projected slice: `∂_τ g = Pz (J_ε (profRHS (slice (JfamP ρ ε g) τ)))`. -/
theorem epsRHSP_eq_profRHS_family (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn)
    (g : Fam) (τ : ℝ) :
    Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g τ
      = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
          (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E (slice (JfamP ρ ε g) τ))) := by
  show Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
      (Work.FTS.StrongEps.epsWP α ρ ε Φs E g τ)) = _
  rw [epsWP_eq_profRHS]

/-- **`J_ε` preserves the vanishing order `z²` at the origin.**  If `f` vanishes like `z²` on a
radial interval `(0,z₀]`, then so does `J_ε f` on `(0, z₀e^{-ε}]`: on the support of the kernel,
`p.1 ≥ -ε`, so the shifted argument `z e^{-p.1}` stays below `z e^{ε} ≤ z₀` and
`(z e^{-p.1})² ≤ e^{2ε}z²`. -/
theorem Jeps_le_zsq {ρ : ℝ × ℝ → ℝ} {ε : ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    (hε : 0 < ε) {f : Fn} {C z₀ : ℝ} (hC : 0 ≤ C) (hz₀ : 0 < z₀)
    (hf : ∀ w θ : ℝ, 0 < w → w ≤ z₀ → θ ∈ Set.Ioo 0 (Real.pi / 2) → |f w θ| ≤ C * w ^ 2) :
    ∀ z θ : ℝ, 0 < z → z * Real.exp ε ≤ z₀ → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |Work.FTS.StrongEps.Jeps ρ ε f z θ| ≤ C * Real.exp (2 * ε) * z ^ 2 := by
  intro z θ hz hzz hθ
  refine Work.FTS.StrongEps.abs_Jeps_le_sup ρ hρ hε hz hθ ?_ (by positivity)
  intro p hp1 _
  have hp1' : -ε ≤ p.1 := by
    have h := (abs_le.mp hp1).1; linarith
  have hshift_pos : 0 < Work.FTS.StrongEps.zShift z p.1 := Work.FTS.StrongEps.zShift_pos hz
  have hle : Work.FTS.StrongEps.zShift z p.1 ≤ z₀ := by
    have h1 : Real.exp (-p.1) ≤ Real.exp ε := Real.exp_le_exp.mpr (by linarith)
    simp only [Work.FTS.StrongEps.zShift]
    nlinarith [h1, hzz, Real.exp_pos (-p.1), Real.exp_pos ε]
  have hb := hf (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
    hshift_pos hle (Work.FTS.StrongEps.thShift_mem hθ)
  have h2 : (Work.FTS.StrongEps.zShift z p.1) ^ 2
      ≤ Real.exp (2 * ε) * z ^ 2 := by
    have h1 : Real.exp (-p.1) ≤ Real.exp ε := Real.exp_le_exp.mpr (by linarith)
    have h1p : 0 < Real.exp (-p.1) := Real.exp_pos _
    have he : Real.exp (-p.1) ^ 2 ≤ Real.exp (2 * ε) := by
      rw [pow_two, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    simp only [Work.FTS.StrongEps.zShift]
    nlinarith [h1, h1p, he, sq_nonneg z, sq_nonneg (Real.exp (-p.1)),
      Real.exp_pos ε, Real.exp_pos (-p.1)]
  calc |f (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)|
      ≤ C * (Work.FTS.StrongEps.zShift z p.1) ^ 2 := hb
    _ ≤ C * (Real.exp (2 * ε) * z ^ 2) := by
        exact mul_le_mul_of_nonneg_left h2 hC
    _ = C * Real.exp (2 * ε) * z ^ 2 := by ring

/-- **`Pz ∘ J_ε` preserves the vanishing order `z²`.**  If `f` vanishes like `z²` on `(0,1]` then
so does `Pz (J_ε f)`: `J_ε` preserves the order on `(0, e^{-ε}/2]` (`Jeps_le_zsq`) and the
projection is invisible there because `bump` is supported in `[1/2,1] × [π/4,3π/8]`. -/
theorem Pz_Jeps_le_zsq {ρ : ℝ × ℝ → ℝ} {ε : ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ)
    (hε : 0 < ε) {f : Fn} {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ z θ : ℝ, 0 < z → z ≤ 1 → θ ∈ Set.Ioo 0 (Real.pi / 2) → |f z θ| ≤ C * z ^ 2) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ z : ℝ, 0 < z → z * Real.exp ε ≤ 1 / 4 →
      |Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f) z θ|
        ≤ C * Real.exp (2 * ε) * z ^ 2 := by
  intro θ hθ z hz hz1
  have hexp : (1 : ℝ) ≤ Real.exp ε := Real.one_le_exp hε.le
  have hJ : |Work.FTS.StrongEps.Jeps ρ ε f z θ| ≤ C * Real.exp (2 * ε) * z ^ 2 :=
    Jeps_le_zsq hρ hε hC (by norm_num) (fun w φ hw hw1 hφ => hbd w φ hw hw1 hφ) z θ hz
      (by nlinarith [hz1, hexp]) hθ
  have hz2 : z < 1 / 2 := by nlinarith [hz1, hexp, hz]
  have hbump : Work.FTS.StrongEps.bump z θ = 0 := by
    simp only [Work.FTS.StrongEps.bump]
    rw [Work.FTS.StrongEps.bump_zCut_eq_zero_of_lt hz2, zero_mul]
  rw [Work.FTS.StrongEps.Pz_apply, hbump, mul_zero, sub_zero]
  exact hJ

end Work.FTS.StrongEps.EpsE4Thr
