import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB2

/-- **Odd reflection preserves `C²`.** If `h : ℝ → ℝ → ℝ` is odd in its second variable and its
uncurried form is `C²` on the upper half-strip `(0,∞) × (0,π)`, then it is `C²` on the lower
half-strip `(0,∞) × (-π,0)` as well.

On the lower half-strip `h w θ = -h w (-θ)`, and `(w,θ) ↦ (w,-θ)` is a smooth diffeomorphism
carrying `(0,∞) × (-π,0)` onto `(0,∞) × (0,π)`; the claim is therefore `ContDiffOn`-invariance
under composition with that reflection, followed by taking the negative. -/
theorem OddReflectC2 {h : ℝ → ℝ → ℝ} (hodd : ∀ w θ, h w (-θ) = -h w θ)
    (h2 : ContDiffOn ℝ 2 (Function.uncurry h) (Set.Ioi 0 ×ˢ Set.Ioo 0 Real.pi)) :
    ContDiffOn ℝ 2 (Function.uncurry h) (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) 0) := by
  set s : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) 0 with hs
  -- the reflection `(w,θ) ↦ (w,-θ)` maps the lower half-strip into the upper one
  have hmap : Set.MapsTo (fun p : ℝ × ℝ => (p.1, -p.2)) s (Set.Ioi 0 ×ˢ Set.Ioo 0 Real.pi) := by
    rintro ⟨w, θ⟩ ⟨hw, hθ⟩
    exact ⟨hw, by linarith [hθ.2], by linarith [hθ.1]⟩
  -- the reflection is smooth on the lower half-strip
  have hσ : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (p.1, -p.2)) s :=
    contDiffOn_fst.prodMk contDiffOn_snd.neg
  -- hence so is the composition
  have hcomp : ContDiffOn ℝ 2 ((Function.uncurry h) ∘ (fun p : ℝ × ℝ => (p.1, -p.2))) s :=
    h2.comp hσ hmap
  -- and that composition is `-(uncurry h)` on the lower half-strip, by oddness
  refine (hcomp.neg).congr ?_
  rintro ⟨w, θ⟩ ⟨hw, hθ⟩
  simp only [Function.comp_apply, Function.uncurry]
  simpa using hodd w (-θ)

end Work.FTS_StreamBdry.SB2
