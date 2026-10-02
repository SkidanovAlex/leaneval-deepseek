import Mathlib
import Submission.Work.FatouCoord.Flower.GermDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Basic properties of the petal union `Pa = WidePetal M ∪ Ψ '' {Re w < -R₀, |Im w| > T}`

This file assembles the elementary topological and dynamical properties of the union `Pa` of the
wide petal `WidePetal M` with the image under the (open, continuous) coordinate map `Ψ` of the
far-left region `{w : ℂ | w.re < -R₀ ∧ T < |w.im|}` of the chart plane.

The far-left region splits into an *upper* convex half `pbUp` and a *lower* convex half `pbLo`.
Each of their images under `Ψ` meets `WidePetal M` through the *window* hypothesis `hwin`, so the
whole union `Pa` is preconnected: images of preconnected sets under the continuous map `Ψ` are
preconnected, and the pieces glue through the nonempty intersections with the wide petal.
Openness comes from `Ψ` being an open map and the far-left region being open; the remaining
properties (nonvanishing at `0`, forward invariance and escape to `0`) are inherited from
`WidePetal M` and the escape hypothesis `hlim`.
-/

open scoped Topology
open Set Filter Metric Function

namespace Work.FatouCoord.Flower

noncomputable section

/-- The far-left region of the chart plane: `Re w < -R` and `|Im w| > T`. -/
def pbS (R T : ℝ) : Set ℂ := {w : ℂ | w.re < -R ∧ T < |w.im|}

/-- The upper half of the far-left region. -/
def pbUp (R T : ℝ) : Set ℂ := {w : ℂ | w.re < -R ∧ T < w.im}

/-- The lower half of the far-left region. -/
def pbLo (R T : ℝ) : Set ℂ := {w : ℂ | w.re < -R ∧ w.im < -T}

@[simp] theorem mem_pbS {R T : ℝ} {w : ℂ} :
    w ∈ pbS R T ↔ w.re < -R ∧ T < |w.im| := Iff.rfl

@[simp] theorem mem_pbUp {R T : ℝ} {w : ℂ} :
    w ∈ pbUp R T ↔ w.re < -R ∧ T < w.im := Iff.rfl

@[simp] theorem mem_pbLo {R T : ℝ} {w : ℂ} :
    w ∈ pbLo R T ↔ w.re < -R ∧ w.im < -T := Iff.rfl

/-- The far-left region is the union of its upper and lower halves. -/
theorem pbS_eq_union (R T : ℝ) : pbS R T = pbUp R T ∪ pbLo R T := by
  ext w; simp only [mem_pbS, mem_pbUp, mem_pbLo, Set.mem_union]
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_abs.mp h2 with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨h1, by linarith⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, lt_abs.mpr (Or.inl h2)⟩
    · exact ⟨h1, lt_abs.mpr (Or.inr (by linarith))⟩

/-- The far-left region is open. -/
theorem pb_isOpen (R T : ℝ) : IsOpen (pbS R T) := by
  have h1 : IsOpen {w : ℂ | w.re < -R} := isOpen_lt Complex.continuous_re continuous_const
  have h2 : IsOpen {w : ℂ | T < |w.im|} :=
    isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_im)
  rw [show pbS R T = {w : ℂ | w.re < -R} ∩ {w : ℂ | T < |w.im|} by ext w; simp [pbS]]
  exact h1.inter h2

/-- The upper half of the far-left region is convex, hence preconnected. -/
theorem pb_convex_up (R T : ℝ) : Convex ℝ (pbUp R T) := by
  have h1 : Convex ℝ {w : ℂ | w.re < -R} := (convex_Iio (-R)).linear_preimage Complex.reLm
  have h2 : Convex ℝ {w : ℂ | T < w.im} := (convex_Ioi T).linear_preimage Complex.imLm
  rw [show pbUp R T = {w : ℂ | w.re < -R} ∩ {w : ℂ | T < w.im} by ext w; simp [pbUp]]
  exact h1.inter h2

/-- The lower half of the far-left region is convex, hence preconnected. -/
theorem pb_convex_lo (R T : ℝ) : Convex ℝ (pbLo R T) := by
  have h1 : Convex ℝ {w : ℂ | w.re < -R} := (convex_Iio (-R)).linear_preimage Complex.reLm
  have h2 : Convex ℝ {w : ℂ | w.im < -T} := (convex_Iio (-T)).linear_preimage Complex.imLm
  rw [show pbLo R T = {w : ℂ | w.re < -R} ∩ {w : ℂ | w.im < -T} by ext w; simp [pbLo]]
  exact h1.inter h2

theorem Pa_basic {f Ψ : ℂ → ℂ} {M R₀ T : ℝ} {Pa : Set ℂ}
    (hΨdiff : Differentiable ℂ Ψ) (hopen : IsOpenMap Ψ)
    (hPa : Pa = Work.FatouCoord.Flower.WidePetal M ∪ Ψ '' {w : ℂ | w.re < -R₀ ∧ T < |w.im|})
    (hne : ∀ w : ℂ, w.re < -R₀ → T < |w.im| → Ψ w ≠ 0)
    (hWide : IsOpen (Work.FatouCoord.Flower.WidePetal M) ∧ IsPreconnected (Work.FatouCoord.Flower.WidePetal M) ∧ (0 : ℂ) ∉ Work.FatouCoord.Flower.WidePetal M ∧
      Set.MapsTo f (Work.FatouCoord.Flower.WidePetal M) (Work.FatouCoord.Flower.WidePetal M) ∧
      (∀ u ∈ Work.FatouCoord.Flower.WidePetal M, Filter.Tendsto (fun n : ℕ => f^[n] u) Filter.atTop (nhds 0)))
    (hwin : ∀ w : ℂ, -R₀ - 1 ≤ w.re → w.re < -R₀ + 1 → T < |w.im| → Ψ w ∈ Work.FatouCoord.Flower.WidePetal M)
    (hshift : ∀ w : ℂ, Ψ (w+1) = f (Ψ w))
    (hlim : ∀ w : ℂ, w.re < -R₀ → T < |w.im| → Filter.Tendsto (fun n : ℕ => f^[n] (Ψ w)) Filter.atTop (nhds 0)) :
    IsOpen Pa ∧ IsPreconnected Pa ∧ (0 : ℂ) ∉ Pa ∧ Set.MapsTo f Pa Pa ∧
    (∀ z ∈ Pa, Filter.Tendsto (fun n : ℕ => f^[n] z) Filter.atTop (nhds 0)) := by
  have hcont : Continuous Ψ := hΨdiff.continuous
  have hPa' : Pa = Work.FatouCoord.Flower.WidePetal M ∪ Ψ '' (pbS R₀ T) := by rw [hPa]; rfl
  rw [hPa']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- openness: union of the open wide petal and the open image of the far-left region
    exact hWide.1.union (hopen (pbS R₀ T) (pb_isOpen R₀ T))
  · -- preconnectedness: glue `WidePetal`, `Ψ '' pbUp` and `Ψ '' pbLo` through the window
    have hWpre : IsPreconnected (Work.FatouCoord.Flower.WidePetal M) := hWide.2.1
    have hUp_pre : IsPreconnected (Ψ '' pbUp R₀ T) :=
      (pb_convex_up R₀ T).isPreconnected.image Ψ hcont.continuousOn
    have hLo_pre : IsPreconnected (Ψ '' pbLo R₀ T) :=
      (pb_convex_lo R₀ T).isPreconnected.image Ψ hcont.continuousOn
    let wU : ℂ := ⟨-R₀ - 1/2, |T| + 1⟩
    let wL : ℂ := ⟨-R₀ - 1/2, -(|T| + 1)⟩
    have hwU_re : wU.re = -R₀ - 1/2 := rfl
    have hwU_im : wU.im = |T| + 1 := rfl
    have hwL_re : wL.re = -R₀ - 1/2 := rfl
    have hwL_im : wL.im = -(|T| + 1) := rfl
    have hTU : T < |T| + 1 := by linarith [le_abs_self T]
    have hU_win : wU ∈ Work.FatouCoord.Flower.Window R₀ T := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hwU_re]; linarith
      · rw [hwU_re]; linarith
      · rw [hwU_im, abs_of_nonneg (by positivity)]; exact hTU
    have hL_win : wL ∈ Work.FatouCoord.Flower.Window R₀ T := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hwL_re]; linarith
      · rw [hwL_re]; linarith
      · rw [hwL_im, abs_neg, abs_of_nonneg (by positivity)]; exact hTU
    have hU_up : wU ∈ pbUp R₀ T := by
      refine ⟨?_, ?_⟩
      · rw [hwU_re]; linarith
      · rw [hwU_im]; exact hTU
    have hL_lo : wL ∈ pbLo R₀ T := by
      refine ⟨?_, ?_⟩
      · rw [hwL_re]; linarith
      · rw [hwL_im]; linarith
    have hUP_ne : (Work.FatouCoord.Flower.WidePetal M ∩ Ψ '' pbUp R₀ T).Nonempty :=
      ⟨Ψ wU, hwin wU hU_win.1 hU_win.2.1 hU_win.2.2, ⟨wU, hU_up, rfl⟩⟩
    have hLO_ne : (Work.FatouCoord.Flower.WidePetal M ∩ Ψ '' pbLo R₀ T).Nonempty :=
      ⟨Ψ wL, hwin wL hL_win.1 hL_win.2.1 hL_win.2.2, ⟨wL, hL_lo, rfl⟩⟩
    have hstep1 : IsPreconnected (Work.FatouCoord.Flower.WidePetal M ∪ Ψ '' pbUp R₀ T) :=
      IsPreconnected.union' hUP_ne hWpre hUp_pre
    have hstep2 : IsPreconnected
        ((Work.FatouCoord.Flower.WidePetal M ∪ Ψ '' pbUp R₀ T) ∪ Ψ '' pbLo R₀ T) :=
      IsPreconnected.union'
        ⟨Ψ wL, Or.inl (hwin wL hL_win.1 hL_win.2.1 hL_win.2.2), ⟨wL, hL_lo, rfl⟩⟩ hstep1 hLo_pre
    rw [pbS_eq_union, Set.image_union, ← Set.union_assoc]
    exact hstep2
  · -- `0` is in neither piece
    rintro (h | ⟨w, hw, h0⟩)
    · exact hWide.2.2.1 h
    · exact hne w hw.1 hw.2 h0
  · -- forward invariance
    intro z hz
    rcases hz with hz | ⟨w, hw, rfl⟩
    · exact Or.inl (hWide.2.2.2.1 hz)
    · rw [← hshift w]
      by_cases hcase : (w + 1).re < -R₀
      · exact Or.inr ⟨w + 1, ⟨hcase, by simpa using hw.2⟩, rfl⟩
      · have hre_ge : -R₀ ≤ (w + 1).re := not_lt.mp hcase
        refine Or.inl (hwin (w + 1) ?_ ?_ ?_)
        · linarith
        · have h1 : (w + 1).re = w.re + 1 := by simp
          rw [h1]; linarith [hw.1]
        · have h1 : (w + 1).im = w.im := by simp
          rw [h1]; exact hw.2
  · -- escape to `0`
    intro z hz
    rcases hz with hz | ⟨w, hw, rfl⟩
    · exact hWide.2.2.2.2 z hz
    · exact hlim w hw.1 hw.2

end

end Work.FatouCoord.Flower
