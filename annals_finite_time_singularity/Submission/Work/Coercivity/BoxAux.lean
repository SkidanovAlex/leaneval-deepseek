/-
# Auxiliary smoothness and continuity lemmas for `Work.Coercivity.box_deriv_ftc`

The target lemma `box_deriv_ftc` is the fundamental theorem of calculus in the radial
variable, applied to the `θ`-slice of the function

  `BoxG f (z,θ) = z · (D_z f(z,θ) · w(z))²`,

followed by a Fubini exchange with the angular integral.  This file collects the
elementary analytic facts about `BoxG f` which that argument needs:

* `w` is smooth on `(0,∞)`;
* `BoxG f` is smooth on `(0,∞) × (-1, π/2+1)` whenever `SmoothNbhd f`;
* hence each radial slice `z ↦ BoxG f z θ` (`θ ∈ Iθ`) is smooth on `(0,∞)`, and so is
  the derivative `∂_z BoxG f`;
* the slice is continuous on `[0,R]` as soon as the boundary term `BoxG f z θ` tends
  to `0` as `z → 0⁺`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.DzIterSmoothOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The radial function `z ↦ z (D_z f(z,θ) w(z))²` whose `z`-derivative is integrated
in `box_deriv_ftc`. -/
def BoxG (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => z * (Spaces.Dz f z θ * Spaces.w z) ^ 2

@[simp]
theorem BoxG_apply (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    BoxG f z θ = z * (Spaces.Dz f z θ * Spaces.w z) ^ 2 := rfl

@[simp]
theorem BoxG_zero_left (f : ℝ → ℝ → ℝ) (θ : ℝ) : BoxG f 0 θ = 0 := by
  simp [BoxG]

/-- The radial weight `w(z) = (1+z)²/z²` is smooth on the open half-line `(0,∞)`. -/
theorem contDiffOn_w : ContDiffOn ℝ ⊤ Spaces.w (Set.Ioi (0 : ℝ)) := by
  have hnum : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    have h : ContDiffOn ℝ ⊤ (fun z : ℝ => (1 : ℝ) + z) (Set.Ioi (0 : ℝ)) :=
      contDiffOn_const.add contDiffOn_id
    exact h.pow 2
  have hden : ContDiffOn ℝ ⊤ (fun z : ℝ => z ^ 2) (Set.Ioi (0 : ℝ)) := contDiffOn_id.pow 2
  have hne : ∀ z ∈ Set.Ioi (0 : ℝ), z ^ 2 ≠ 0 := fun z hz => pow_ne_zero 2 (ne_of_gt hz)
  exact hnum.div hden hne

/-- `BoxG f` is smooth on `(0,∞) × (-1, π/2+1)` whenever `f` is `SmoothNbhd`. -/
theorem contDiffOn_uncurry_BoxG (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) :
    ContDiffOn ℝ ⊤ (Function.uncurry (BoxG f))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := by
  set V : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1) with hV
  have hDzbox : ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.Dz f))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) :=
    Spaces.contDiffOn_uncurry_Dz (isOpen_Ioi.prod isOpen_Ioo) hsm
  have hsub : V ⊆ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1) := by
    rintro ⟨z, θ⟩ hp
    rw [hV] at hp
    simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
    exact ⟨by linarith [hp.1], hp.2⟩
  have hDz : ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.Dz f)) V := hDzbox.mono hsub
  have hw : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Spaces.w p.1) V :=
    contDiffOn_w.comp contDiffOn_fst (fun p hp => hp.1)
  have hz : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => p.1) V := contDiffOn_fst
  have h : ContDiffOn ℝ ⊤
      (fun p : ℝ × ℝ => p.1 * (Function.uncurry (Spaces.Dz f) p * Spaces.w p.1) ^ 2) V :=
    hz.mul ((hDz.mul hw).pow 2)
  refine h.congr (fun p _ => ?_)
  simp only [Function.uncurry, BoxG]

/-- The radial slice `z ↦ BoxG f z θ` is smooth on `(0,∞)`, for every `θ ∈ Iθ`. -/
theorem contDiffOn_BoxG_slice (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) {θ : ℝ}
    (hθ : θ ∈ Spaces.Iθ) :
    ContDiffOn ℝ ⊤ (fun z => BoxG f z θ) (Set.Ioi (0 : ℝ)) := by
  have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi (0 : ℝ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := fun z hz =>
    ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩⟩
  have h := (contDiffOn_uncurry_BoxG f hsm).comp
    (contDiffOn_id.prodMk contDiffOn_const) hmap
  exact h.congr (fun z _ => rfl)

/-- The radial derivative `∂_z BoxG f` is smooth on `(0,∞) × (-1, π/2+1)`. -/
theorem contDiffOn_uncurry_pz_BoxG (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.pz (BoxG f)))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1) (π / 2 + 1)) :=
  Spaces.contDiffOn_uncurry_pz (isOpen_Ioi.prod isOpen_Ioo) (contDiffOn_uncurry_BoxG f hsm)

/-- The radial slice `z ↦ BoxG f z θ` is continuous on `[0,R]` when the boundary term
vanishes at `z = 0⁺`. -/
theorem continuousOn_BoxG_slice_Icc (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hbd : ∀ θ ∈ Spaces.Iθ, Filter.Tendsto (fun z => BoxG f z θ)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    {R : ℝ} (hR : 0 < R) {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    ContinuousOn (fun z => BoxG f z θ) (Set.Icc 0 R) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · subst hx0
    have h1 : Tendsto (fun z => BoxG f z θ) (𝓝[>] (0 : ℝ)) (𝓝 (BoxG f 0 θ)) := by
      simpa using hbd θ hθ
    have h2 : Tendsto (fun z => BoxG f z θ) (𝓝[{(0 : ℝ)}] 0) (𝓝 (BoxG f 0 θ)) := by
      rw [nhdsWithin_singleton]
      exact tendsto_pure_nhds _ _
    have h3 : Tendsto (fun z => BoxG f z θ) (𝓝[Set.Ici (0 : ℝ)] 0) (𝓝 (BoxG f 0 θ)) := by
      rw [← nhdsGT_sup_nhdsWithin_singleton]
      exact h1.sup h2
    exact Filter.Tendsto.mono_left h3 (nhdsWithin_mono 0 Set.Icc_subset_Ici_self)
  · exact ((contDiffOn_BoxG_slice f hsm hθ).continuousOn.continuousAt
      (isOpen_Ioi.mem_nhds hx0)).continuousWithinAt

end Work.Coercivity
