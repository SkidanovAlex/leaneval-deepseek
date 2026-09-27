import Mathlib
import Submission.Work.Drive.surjective_pUp_of_private

namespace Work.Drive

/-!
# `surjective_pUp_of_blockRanges`

The companion of `Work.Drive.surjective_pUp_of_private`.  There, surjectivity of the
charted difference map is deduced from *private directions* of the two linear maps
`D₁`, `D₂` (directions that kill the other two maps and hit all of `ℝ⁴`).

Here the hypothesis is the block-range statement itself: for every pair `(w₁, w₂)`
there is a *common* vector `a` in the range of `f₀` with `a - b = w₁` for some
`b ∈ range f₁` and `a - c = w₂` for some `c ∈ range f₂`.  (This is the situation in the
encoded-chain counting: blocks 1 and 2 each have private parameter directions, so every
pair of differences is realised by one triple of parameters, sharing the base point in
`range f₀`.)

The content is then pure bookkeeping: pick the three preimages of `a`, `b`, `c` and use
`Work.Drive.TParity.pUp_fst8_snd8`, which says that every `w : Tgt 8` is the stack of its
two blocks `fst8 w` and `snd8 w`.
-/

/-- If for every pair `(w₁, w₂)` there are `a ∈ f₀.range`, `b ∈ f₁.range`, `c ∈ f₂.range`
with `a - b = w₁` and `a - c = w₂`, then the triple of differences
`v ↦ pUp (f₀ v.1 - f₁ v.2.1) (f₀ v.1 - f₂ v.2.2)` is surjective onto `ℝ⁸`. -/
theorem surjective_pUp_of_blockRanges {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f₀ f₁ f₂ : E →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (h : ∀ w₁ w₂ : EuclideanSpace ℝ (Fin 4),
      ∃ a ∈ f₀.range, ∃ b ∈ f₁.range, ∃ c ∈ f₂.range, a - b = w₁ ∧ a - c = w₂) :
    Function.Surjective (fun v : E × E × E =>
      Work.Drive.TParity.pUp (f₀ v.1 - f₁ v.2.1) (f₀ v.1 - f₂ v.2.2)) := by
  intro w
  obtain ⟨a, ha, b, hb, c, hc, hab, hac⟩ :=
    h (Work.Drive.TParity.fst8 w) (Work.Drive.TParity.snd8 w)
  rw [LinearMap.mem_range] at ha hb hc
  obtain ⟨x₀, hx₀⟩ := ha
  obtain ⟨x₁, hx₁⟩ := hb
  obtain ⟨x₂, hx₂⟩ := hc
  subst hx₀
  subst hx₁
  subst hx₂
  refine ⟨(x₀, x₁, x₂), ?_⟩
  show Work.Drive.TParity.pUp (f₀ x₀ - f₁ x₁) (f₀ x₀ - f₂ x₂) = w
  have h₁ : f₀ x₀ - f₁ x₁ = Work.Drive.TParity.fst8 w := hab
  have h₂ : f₀ x₀ - f₂ x₂ = Work.Drive.TParity.snd8 w := hac
  rw [h₁, h₂, Work.Drive.TParity.pUp_fst8_snd8]

end Work.Drive
