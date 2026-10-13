/-
Copyright: work module for the Elgindi finite-time singularity project.

# `PT.Basic` — elementary helpers for the pointwise convergence `prof_pt_tendsto`

Two families of small facts used by the assembly of
`Work.FTS.StrongEps.E5Aux2.prof_pt_tendsto`:

* differentiability of the slices of a function which is `C¹` on the open quadrant, and the
  resulting **order-one additivity of the mixed slots**
  `mixed j i (f + g) = mixed j i f + mixed j i g` for `j + i ≤ 1` (the all-order lemma
  `Work.FTS.StrongEps.mixed_add` needs `C^∞` of both summands, which the *limit* slice
  `slice g s` — only `C⁴` there — does not have);
* the pointwise bound on the low slots of a class-`C` profile
  (`classC_mixed_sup_le` composed with `Xn ≤ Xn6`), which turns the uniform `ℋ⁶`-bound of the
  approximating family into the θ-uniform domination used in the dominated-convergence steps.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.E5Aux2.MuHGlue
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS_RegExport.RXR7.Support.FstarPartCont
import Submission.Work.FTS.StrongPersist.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2.PT

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## Slice differentiability from `C¹` on the open quadrant -/

theorem differentiableAt_zslice_of_contDiffOn_one {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 (Function.uncurry F) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    DifferentiableAt ℝ (fun z' => F z' θ) z := by
  have hd : DifferentiableAt ℝ (Function.uncurry F) (z, θ) :=
    (hF.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)).differentiableAt (by norm_num)
  change DifferentiableAt ℝ (Function.uncurry F ∘ fun z' : ℝ => (z', θ)) z
  exact hd.comp z (hasFDerivAt_prodMk_left z θ).differentiableAt

theorem differentiableAt_tslice_of_contDiffOn_one {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 1 (Function.uncurry F) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    DifferentiableAt ℝ (fun θ' => F z θ') θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry F) (z, θ) :=
    (hF.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)).differentiableAt (by norm_num)
  change DifferentiableAt ℝ (Function.uncurry F ∘ fun θ' : ℝ => (z, θ')) θ
  exact hd.comp θ (hasFDerivAt_prodMk_right z θ).differentiableAt

theorem differentiableAt_slice_of_smoothOpen {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) {z θ : ℝ}
    (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    DifferentiableAt ℝ (fun z' => F z' θ) z ∧ DifferentiableAt ℝ (fun θ' => F z θ') θ :=
  ⟨differentiableAt_zslice_of_contDiffOn_one (hF.forall 1) hzθ,
    differentiableAt_tslice_of_contDiffOn_one (hF.forall 1) hzθ⟩

/-! ## The three slots of order `≤ 1` -/

@[simp] theorem mixed_zero_zero (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 0 f z θ = f z θ := by
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero]

theorem mixed_one_zero (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 1 0 f z θ = Work.Spaces.Dz f z θ := by
  simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
    Work.Spaces.DthIter_zero]

theorem mixed_zero_one (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 1 f z θ = Work.Spaces.Dth f z θ := by
  simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero,
    Work.Spaces.DzIter_zero]

theorem mixed_one_zero_eq_Dz (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed 1 0 f = Work.Spaces.Dz f := by
  funext z θ; exact mixed_one_zero f z θ

theorem mixed_zero_one_eq_Dth (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed 0 1 f = Work.Spaces.Dth f := by
  funext z θ; exact mixed_zero_one f z θ

/-! ## Order-one additivity of the mixed slots -/

theorem mixed_add_one {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hji : j + i ≤ 1) {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.mixed j i (fun z' θ' => f z' θ' + g z' θ') z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ := by
  have hj : j = 0 ∨ j = 1 := by omega
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hj with rfl | rfl <;> rcases hi with rfl | rfl
  · rw [mixed_zero_zero, mixed_zero_zero, mixed_zero_zero]
  · rw [mixed_zero_one, mixed_zero_one, mixed_zero_one]
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rw [show (fun θ' => f z θ' + g z θ') = (fun θ' => f z θ') + (fun θ' => g z θ') from rfl,
      deriv_add (differentiableAt_tslice_of_contDiffOn_one hf hzθ)
        (differentiableAt_tslice_of_contDiffOn_one hg hzθ)]
    ring
  · rw [mixed_one_zero, mixed_one_zero, mixed_one_zero]
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rw [show (fun z' => f z' θ + g z' θ) = (fun z' => f z' θ) + (fun z' => g z' θ) from rfl,
      deriv_add (differentiableAt_zslice_of_contDiffOn_one hf hzθ)
        (differentiableAt_zslice_of_contDiffOn_one hg hzθ)]
    ring
  · exfalso; omega

/-! ## The reference profile `F_*` -/

/-- `F_*` is `C¹` on the open quadrant. -/
theorem contDiffOn_one_Fstar (α : ℝ) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Fstar α)) Work.FTS.EllipticEst.Q0 :=
  (Work.FTS_RegExport.RXR7.Support.smoothOpen_Fstar α).forall 1

/-- **The slots of order `≤ 1` of `F_* + w` split.** -/
theorem mixed_Fstar_add {α : ℝ} {w : ℝ → ℝ → ℝ}
    (hw : ContDiffOn ℝ 1 (Function.uncurry w) Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hji : j + i ≤ 1) {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.mixed j i (fun z' θ' => Work.Construction.Fstar α z' θ' + w z' θ') z θ
      = Work.Spaces.mixed j i (Work.Construction.Fstar α) z θ + Work.Spaces.mixed j i w z θ :=
  mixed_add_one (contDiffOn_one_Fstar α) hw hji hzθ

/-! ## The pointwise bound on the low slots of a class-`C` profile -/

/-- **θ-uniform pointwise bound.**  A class-`C` profile of `ℋ⁶`-size `≤ B` has
`|D_z^bD_θ^a w| ≤ 10/√(γ-1)·B` at every point of the open quadrant, for `a + b ≤ 2`.  This is
`SupPort.classC_mixed_sup_le` composed with the order-monotonicity `Xn ≤ Xn6`. -/
theorem classC_mixed_sup_le_of_Xn6 {α B : ℝ} (hα : α ∈ Set.Ioc 0 1) {w : ℝ → ℝ → ℝ}
    (hw : Work.FTS.ClassC.ClassC α w) (hB : Work.FTS.StrongGlobal.Xn6 α w ≤ B)
    {b a : ℕ} (hab : a + b ≤ 2) {z θ : ℝ} (hzθ : (z, θ) ∈ Work.Construction.Qd) :
    |Work.Spaces.mixed b a w z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * B := by
  have h6 : Work.FTS.StrongPersist.H6Mem α w :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hw.reg hw.mem
  have h1 := Work.FTS.StrongEps.SupPort.classC_mixed_sup_le hα.1 hα.2 hw b a hab hzθ
  have h2 : Work.FTS.Nonlin.Xn α w ≤ B := le_trans (Work.FTS.StrongPersist.Xn_le_Xn6 α h6) hB
  have h3 : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 h3)

/-- The same bound in the two slots that the density estimates use. -/
theorem classC_abs_le_of_Xn6 {α B : ℝ} (hα : α ∈ Set.Ioc 0 1) {w : ℝ → ℝ → ℝ}
    (hw : Work.FTS.ClassC.ClassC α w) (hB : Work.FTS.StrongGlobal.Xn6 α w ≤ B)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.Construction.Qd) :
    |w z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * B ∧
      |Work.Spaces.Dz w z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * B :=
  ⟨by simpa using classC_mixed_sup_le_of_Xn6 hα hw hB (b := 0) (a := 0) (by norm_num) hzθ,
    by simpa [Work.Spaces.mixed, Work.Spaces.DthIter_zero, Work.Spaces.DzIter_succ,
      Work.Spaces.DzIter_zero] using
      classC_mixed_sup_le_of_Xn6 hα hw hB (b := 1) (a := 0) (by norm_num) hzθ⟩

end Work.FTS.StrongEps.E5Aux2.PT
