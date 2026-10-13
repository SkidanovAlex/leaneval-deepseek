import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.EllExist.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS_RegExport.RXT.SysAux.DzIter_two_pt_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.SecondDeriv

set_option autoImplicit false

/-! ## Two algebraic rewrites used by the slice-package bounds -/

/-- On the open quadrant, `z² ∂_z² h = D_z² h − D_z h` (rewritten through the open-quadrant
expansion `Work.FTS_RegExport.RXT.SysAux.DzIter_two_pt_open`). -/
theorem zsq_pzIter_two_eq {h : ℝ → ℝ → ℝ}
    (hslice : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ContDiffOn ℝ 2 (fun z => h z θ) (Set.Ioi 0))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    z ^ 2 * Work.Spaces.pzIter 2 h z θ
      = Work.Spaces.mixed 2 0 h z θ - Work.Spaces.mixed 1 0 h z θ := by
  have hexp := Work.FTS_RegExport.RXT.SysAux.DzIter_two_pt_open hslice hz hθ
  have h1 : Work.Spaces.mixed 1 0 h z θ = z * Work.Spaces.pzIter 1 h z θ := rfl
  have h2 : Work.Spaces.mixed 2 0 h z θ = Work.Spaces.DzIter 2 h z θ := rfl
  rw [h1, h2, hexp]
  ring

/-- `Lzero` in terms of the full operator `bslOp` and the plain radial derivatives (the sign
convention of `Work.Elliptic.bslOp`). -/
theorem Lzero_eq_bslOp_add (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Elliptic.Lzero Ψ z θ = Work.Elliptic.bslOp α Ψ z θ
      + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ := by
  rw [Work.Elliptic.bslOp_apply]
  ring

/-! ## The slice package of bounds -/

theorem slice_package_bounds {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g (E g) ∧
        Work.FTS.VocabO.EllPkgGo α Ce g (E g) ∧
        Work.FTS.ClassC.EllPkgK α 6 Ce g (E g))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ M : ℝ, 0 < M ∧ ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(E g) z θ| ≤ M * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Real.sin (2 * θ) / 2 * Work.Spaces.pth (E g) z θ + (E g) z θ|
            ≤ M * Work.FTS.StrongGlobal.Xn6 α g ∧
        |Work.Elliptic.Lzero (E g) z θ| ≤ M * Work.FTS.StrongGlobal.Xn6 α g := by
  have hα1 : α ≤ 1 := by linarith
  -- the level-`4` mixed-jet bound of the solution operator
  obtain ⟨K, hK0, hK⟩ :=
    Work.FTS_EllLimOK.ProducerH.MixedJets.mixed_jets_le_Xn6 hα hα4 hE
  have hKg0 : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  refine ⟨1 + (10 / Real.sqrt (Work.Spaces.gam α - 1)) + 10 * K, by linarith, ?_⟩
  intro g hg z hz θ hθ
  have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
  have hQd : (z, θ) ∈ Work.Construction.Qd := ⟨hz0, hθ⟩
  have hX0 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Work.Spaces.HkNorm_nonneg α 6 g
  -- the pointwise jet bound at the point `(z,θ)`
  have hjet : ∀ j i : ℕ, j + i ≤ 4 →
      |Work.Spaces.mixed j i (E g) z θ| ≤ K * Work.FTS.StrongGlobal.Xn6 α g :=
    fun j i hji => hK g hg j i hji z θ hQd
  -- the `z`-slice smoothness of `E g` (for the expansion `D_z² = D_z + z²∂_z²`)
  have hslice : ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
      ContDiffOn ℝ 2 (fun z' => (E g) z' θ') (Set.Ioi 0) :=
    fun θ' hθ' => (((hE g hg).1.2.1).curry_z hθ').of_le (by simp [Work.Stability.smoothOrder])
  -- the bound on the source `g` (the interior `L^∞`–`ℋ⁴` trade-off of the class `C`)
  have hgsrc : |g z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1)
      * Work.FTS.StrongGlobal.Xn6 α g := by
    have h1 : |g z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1)
        * Work.FTS.Nonlin.Xn α g :=
      Work.FTS.StrongEps.SupPort.classC_mixed_sup_le hα hα1 hg 0 0 (by norm_num) hQd
    have hmem6 : Work.Spaces.HkMem α 6 g :=
      Work.FTS.OpenPkg.HkMem_mono_open hg.reg 6 (by norm_num) hg.mem
    have hnorm : Work.Spaces.HkNorm α 4 g ≤ Work.Spaces.HkNorm α 6 g :=
      Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 4) (by norm_num) hmem6
    calc |g z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 g := h1
      _ ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 6 g :=
          mul_le_mul_of_nonneg_left hnorm hKg0
  refine ⟨?_, ?_, ?_⟩
  · -- `|E g| ≤ K·|g|_{ℋ⁶}`
    calc |(E g) z θ| = |Work.Spaces.mixed 0 0 (E g) z θ| := rfl
      _ ≤ K * Work.FTS.StrongGlobal.Xn6 α g := hjet 0 0 (by norm_num)
      _ ≤ (1 + (10 / Real.sqrt (Work.Spaces.gam α - 1)) + 10 * K)
            * Work.FTS.StrongGlobal.Xn6 α g := by
          exact mul_le_mul_of_nonneg_right (show K ≤ 1 + (10 / Real.sqrt (Work.Spaces.gam α - 1))
            + 10 * K by linarith) hX0
  · -- `|(1/2) D_θ(E g) + E g| ≤ (3/2) K·|g|_{ℋ⁶}`
    have hrepr : Real.sin (2 * θ) / 2 * Work.Spaces.pth (E g) z θ + (E g) z θ
        = (1 / 2) * Work.Spaces.mixed 0 1 (E g) z θ
          + Work.Spaces.mixed 0 0 (E g) z θ := by
      rw [show Work.Spaces.mixed 0 1 (E g) z θ
            = Real.sin (2 * θ) * Work.Spaces.pth (E g) z θ from rfl,
          show Work.Spaces.mixed 0 0 (E g) z θ = (E g) z θ from rfl]
      ring
    rw [hrepr]
    calc |(1 / 2) * Work.Spaces.mixed 0 1 (E g) z θ + Work.Spaces.mixed 0 0 (E g) z θ|
        ≤ |(1 / 2) * Work.Spaces.mixed 0 1 (E g) z θ|
            + |Work.Spaces.mixed 0 0 (E g) z θ| := abs_add_le _ _
      _ = (1 / 2) * |Work.Spaces.mixed 0 1 (E g) z θ|
            + |Work.Spaces.mixed 0 0 (E g) z θ| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      _ ≤ (1 / 2) * (K * Work.FTS.StrongGlobal.Xn6 α g)
            + K * Work.FTS.StrongGlobal.Xn6 α g :=
          add_le_add (mul_le_mul_of_nonneg_left (hjet 0 1 (by norm_num)) (by norm_num))
            (hjet 0 0 (by norm_num))
      _ ≤ (1 + (10 / Real.sqrt (Work.Spaces.gam α - 1)) + 10 * K)
            * Work.FTS.StrongGlobal.Xn6 α g := by
          nlinarith [hX0, hK0, hKg0]
  · -- `|Lzero (E g)| ≤ (Kg + (2α² + α(5+α))K)·|g|_{ℋ⁶}` via the elliptic equation
    have hsol : Work.Elliptic.bslOp α (E g) z θ = g z θ := (hE g hg).1.1.1 z hz0 θ hθ.1 hθ.2
    have hL : Work.Elliptic.Lzero (E g) z θ = g z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (E g) z θ)
        + (α * (5 + α) * z) * Work.Spaces.pz (E g) z θ := by
      rw [Lzero_eq_bslOp_add, hsol]
    have hfac : (0 : ℝ) ≤ α * (5 + α) := by nlinarith [hα]
    have hb2 : |α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (E g) z θ)|
        ≤ α ^ 2 * (2 * (K * Work.FTS.StrongGlobal.Xn6 α g)) := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg α)]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg α)
      have hident : z ^ 2 * Work.Spaces.pzIter 2 (E g) z θ
          = Work.Spaces.mixed 2 0 (E g) z θ - Work.Spaces.mixed 1 0 (E g) z θ :=
        zsq_pzIter_two_eq hslice hz0 hθ
      rw [hident]
      calc |Work.Spaces.mixed 2 0 (E g) z θ - Work.Spaces.mixed 1 0 (E g) z θ|
          ≤ |Work.Spaces.mixed 2 0 (E g) z θ| + |Work.Spaces.mixed 1 0 (E g) z θ| :=
            abs_sub _ _
        _ ≤ K * Work.FTS.StrongGlobal.Xn6 α g + K * Work.FTS.StrongGlobal.Xn6 α g :=
            add_le_add (hjet 2 0 (by norm_num)) (hjet 1 0 (by norm_num))
        _ = 2 * (K * Work.FTS.StrongGlobal.Xn6 α g) := by ring
    have hb3 : |(α * (5 + α) * z) * Work.Spaces.pz (E g) z θ|
        ≤ (α * (5 + α)) * (K * Work.FTS.StrongGlobal.Xn6 α g) := by
      rw [show (α * (5 + α) * z) * Work.Spaces.pz (E g) z θ
            = (α * (5 + α)) * (z * Work.Spaces.pz (E g) z θ) from by ring]
      rw [abs_mul, abs_of_nonneg hfac]
      refine mul_le_mul_of_nonneg_left ?_ hfac
      rw [show z * Work.Spaces.pz (E g) z θ = Work.Spaces.mixed 1 0 (E g) z θ from rfl]
      exact hjet 1 0 (by norm_num)
    rw [hL]
    have hsum : |g z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (E g) z θ)
          + (α * (5 + α) * z) * Work.Spaces.pz (E g) z θ|
        ≤ |g z θ| + |α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (E g) z θ)|
          + |(α * (5 + α) * z) * Work.Spaces.pz (E g) z θ| := by
      have h1 := abs_add_le (g z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (E g) z θ))
        ((α * (5 + α) * z) * Work.Spaces.pz (E g) z θ)
      have h2 := abs_add_le (g z θ) (α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (E g) z θ))
      linarith
    refine le_trans hsum ?_
    have hnum : |g z θ| + |α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (E g) z θ)|
          + |(α * (5 + α) * z) * Work.Spaces.pz (E g) z θ|
        ≤ (10 / Real.sqrt (Work.Spaces.gam α - 1)) * Work.FTS.StrongGlobal.Xn6 α g
          + α ^ 2 * (2 * (K * Work.FTS.StrongGlobal.Xn6 α g))
          + (α * (5 + α)) * (K * Work.FTS.StrongGlobal.Xn6 α g) := by linarith
    refine le_trans hnum ?_
    have hcoef : 2 * α ^ 2 + α * (5 + α) ≤ 10 := by
      nlinarith [mul_le_mul hα1 hα1 hα.le (by norm_num : (0 : ℝ) ≤ 1), hα.le, hα]
    have hKX : 0 ≤ K * Work.FTS.StrongGlobal.Xn6 α g := mul_nonneg hK0.le hX0
    have h4 : (2 * α ^ 2 + α * (5 + α)) * (K * Work.FTS.StrongGlobal.Xn6 α g)
        ≤ 10 * (K * Work.FTS.StrongGlobal.Xn6 α g) :=
      mul_le_mul_of_nonneg_right hcoef hKX
    nlinarith [h4, hX0, hK0, hKg0]

end Work.FTS_EllLimOK.ProducerH.SecondDeriv
