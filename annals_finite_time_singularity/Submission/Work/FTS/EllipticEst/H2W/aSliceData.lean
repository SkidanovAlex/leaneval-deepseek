import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The `θ`-slice data of `z² ∂_z² Ψ`

For a datum `Ψ` of the weak class `TT.EllWeakPos α 2 F Ψ` (i.e. `bslOp α Ψ = F` on the open
quadrant, the two Dirichlet data, the two moment conditions, and `HkMem`-honesty of `F`, of
`z²∂_z²Ψ` and of `∂_θ²Ψ`), this file records the two elementary facts about the *angular slices*
of `z²∂_z²Ψ` that the level-`0` angular estimate consumes:

* as a function of `θ` it is `C^n` on `(0,π/2)` for every `n`, and it *vanishes* at the two
  endpoints `θ = 0`, `θ = π/2` (this is where the Dirichlet data `Ψ(z,0) = Ψ(z,π/2) = 0` is
  used: the `θ₀`-slice of `Ψ` vanishes identically, hence so do all its `z`-derivatives);
* it is the pointwise difference `D_z²Ψ - D_zΨ` of the first two `D_z`-iterates on the open
  quadrant, which is the identity `z²∂_z² = D_z² - D_z` used to transfer the elliptic equation
  to `z²∂_z²Ψ`. -/

/-- If the `θ₀`-slice of `f` vanishes identically, then so does the `θ₀`-slice of every
iterated `z`-derivative `∂_z^n f`: the slice `z ↦ ∂_z^n f z θ₀` is the `n`-th derivative of the
zero function.  (`deriv` is totalised but agrees with the usual derivative on the constant
function `0`.) -/
theorem pzIter_eq_zero_of_slice_eq_zero {f : ℝ → ℝ → ℝ} {θ₀ : ℝ}
    (h0 : ∀ z, f z θ₀ = 0) : ∀ n : ℕ, ∀ z : ℝ, Work.Spaces.pzIter n f z θ₀ = 0 := by
  intro n
  induction n with
  | zero => intro z; exact h0 z
  | succ n ih =>
      intro z
      have hfun : (fun a : ℝ => Work.Spaces.pzIter n f a θ₀) = fun _ => (0 : ℝ) := funext ih
      show deriv (fun a : ℝ => Work.Spaces.pzIter n f a θ₀) z = 0
      rw [hfun]
      simp

/-- **The slice data of `z²∂_z²Ψ`.**  For a datum of the weak class: every angular slice of
`z²∂_z²Ψ` is `C^∞` on the open interval and vanishes at the two endpoints. -/
theorem aSliceData : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      (∀ z ∈ Work.Spaces.Iz,
          (∀ n : ℕ, ContDiffOn ℝ n (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              (Set.Ioo 0 (Real.pi / 2)))
            ∧ (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) 0 = 0
            ∧ (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Real.pi / 2) = 0)
        ∧ ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
            z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
              = Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.DzIter 1 Ψ z θ := by
  intro α F Ψ hα hα4 h
  -- `Ψ` is `C^∞` on the open quadrant
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  refine ⟨?_, ?_⟩
  · -- the slice data at every `z ∈ [0,∞)`
    intro z hz
    have hzle : (0 : ℝ) ≤ z := by simpa [Work.Spaces.Iz] using hz
    rcases eq_or_lt_of_le hzle with hz0 | hzpos
    · -- at `z = 0` the slice is identically zero, whatever `Ψ` does there
      have hfun : (fun θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) = fun _ => (0 : ℝ) := by
        funext θ
        rw [show z = 0 from hz0.symm]
        simp
      refine ⟨fun n => ?_, ?_, ?_⟩
      · rw [hfun]
        exact contDiffOn_const
      · show z ^ 2 * Work.Spaces.pzIter 2 Ψ z 0 = 0
        rw [show z = 0 from hz0.symm]
        simp
      · show z ^ 2 * Work.Spaces.pzIter 2 Ψ z (Real.pi / 2) = 0
        rw [show z = 0 from hz0.symm]
        simp
    · -- at `z > 0` the slice of `∂_z²Ψ` is smooth on the open quadrant, by `curry_θ`
      have hslice : ∀ n : ℕ,
          ContDiffOn ℝ n (fun θ => Work.Spaces.pzIter 2 Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
        fun n => contDiffOn_iff_forall_nat_le.mp ((hΨ.pzIter 2).curry_θ hzpos) n le_top
      refine ⟨fun n => ?_, ?_, ?_⟩
      · exact (contDiffOn_const (c := z ^ 2)).mul (hslice n)
      · -- `∂_z²Ψ z 0 = 0`, because the slice `z' ↦ Ψ z' 0` vanishes identically
        have h2 : Work.Spaces.pzIter 2 Ψ z 0 = 0 :=
          pzIter_eq_zero_of_slice_eq_zero (fun z' => h.zero z') 2 z
        show z ^ 2 * Work.Spaces.pzIter 2 Ψ z 0 = 0
        rw [h2, mul_zero]
      · -- `∂_z²Ψ z (π/2) = 0`, for the same reason
        have h2 : Work.Spaces.pzIter 2 Ψ z (Real.pi / 2) = 0 :=
          pzIter_eq_zero_of_slice_eq_zero (fun z' => h.pi_half z') 2 z
        show z ^ 2 * Work.Spaces.pzIter 2 Ψ z (Real.pi / 2) = 0
        rw [h2, mul_zero]
  · -- the identity `z²∂_z²Ψ = D_z²Ψ - D_zΨ` on the open quadrant
    intro z hz θ hθ0 hθ1
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using
      Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open Ψ hΨ hz ⟨hθ0, hθ1⟩

end Work.FTS.EllipticEst.H2W
