import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `C^∞` order and the half-strip -/

/-- The *smooth* order `∞` of `ContDiff`, as opposed to the analytic order `⊤ = ω`. -/
abbrev smoothOrder : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)


/-- The half-strip `(0,∞) × (-1, π/2 + 1)` on which the data of the angular Poincaré estimate
are `C^∞`.  Its `θ`-range contains the closed angular interval `Iθ` in its interior, which is
what makes the one-dimensional slice estimates (FTC, Rolle, vanishing of the boundary terms)
available. -/
def halfStrip : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)

theorem isOpen_halfStrip : IsOpen halfStrip := isOpen_Ioi.prod isOpen_Ioo


theorem Iθ_subset_Ioo : Work.Spaces.Iθ ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
  intro θ hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-! ## The class `SliceSmoothO` -/

/-- `u` is `C^∞` on the neighbourhood `(-1, π/2 + 1)` of the closed angular interval `Iθ`.
This is the class of the one-dimensional slice estimates, weakened from the analytic
`Work.FTS.EllipticEst.SliceSmooth` to honest `C^∞`. -/
abbrev SliceSmoothO (u : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ smoothOrder u (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))

/-- `SliceSmoothO` is the `∀ n : ℕ, ContDiffOn ℝ n …` shape. -/
theorem sliceSmoothO_iff (u : ℝ → ℝ) :
    SliceSmoothO u ↔ ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
  contDiffOn_infty

theorem SliceSmoothO.of_le {u : ℝ → ℝ} (h : SliceSmoothO u) (n : ℕ) :
    ContDiffOn ℝ n u (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
  contDiffOn_infty.mp h n

theorem SliceSmoothO.mono {u : ℝ → ℝ} (h : SliceSmoothO u) {s : Set ℝ}
    (hs : s ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) : ContDiffOn ℝ smoothOrder u s :=
  ContDiffOn.mono h hs



/-! ## Slices of `SmoothOpenθ` data -/



/-- The uncurried iterate `D_z^j f` of a `SmoothOpenθ` datum is again `C^∞` on the half-strip. -/
theorem SmoothOpenθ.DzIter {f : ℝ → ℝ → ℝ} (h : SmoothOpenθ f) (j : ℕ) :
    SmoothOpenθ (Work.Spaces.DzIter j f) := by
  have hf : ContDiffOn ℝ smoothOrder (Function.uncurry f) halfStrip :=
    contDiffOn_infty.mpr h
  intro n
  exact (Work.FTS.LocData.contDiffOn_DzIter isOpen_halfStrip hf j).of_le (by norm_num)

/-- The uncurried iterate `D_θ^i f` of a `SmoothOpenθ` datum is again `C^∞` on the half-strip. -/
theorem SmoothOpenθ.DthIter {f : ℝ → ℝ → ℝ} (h : SmoothOpenθ f) (i : ℕ) :
    SmoothOpenθ (Work.Spaces.DthIter i f) := by
  have hf : ContDiffOn ℝ smoothOrder (Function.uncurry f) halfStrip :=
    contDiffOn_infty.mpr h
  intro n
  exact (Work.FTS.LocData.contDiffOn_DthIter isOpen_halfStrip hf i).of_le (by norm_num)

/-- The uncurried iterate `∂_θ^m f` of a `SmoothOpenθ` datum is again `C^∞` on the half-strip. -/
theorem SmoothOpenθ.pthIter {f : ℝ → ℝ → ℝ} (h : SmoothOpenθ f) (m : ℕ) :
    SmoothOpenθ (Work.Spaces.pthIter m f) := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
      have hf : ContDiffOn ℝ smoothOrder (Function.uncurry (Work.Spaces.pthIter m f))
          halfStrip := contDiffOn_infty.mpr ih
      intro n
      exact (Work.FTS.LocData.contDiffOn_pth isOpen_halfStrip hf).of_le (by norm_num)

/-- The uncurried iterate `D_z^j D_θ^i f` of a `SmoothOpenθ` datum is `C^∞` on the half-strip. -/
theorem SmoothOpenθ.mixed {f : ℝ → ℝ → ℝ} (h : SmoothOpenθ f) (j i : ℕ) :
    SmoothOpenθ (Work.Spaces.mixed j i f) := (h.DthIter i).DzIter j



end Work.FTS.EllipticEst.ThetaU
