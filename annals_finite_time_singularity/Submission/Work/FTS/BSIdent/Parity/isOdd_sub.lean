import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.Parity

/-!
# Parity (`FiniteTimeSingularity.IsOdd`) is preserved by subtraction

`FiniteTimeSingularity.IsOdd u` says that for each `i` the component `uᵢ` is an odd function of
the `i`-th coordinate and an even function of the other two coordinates.  Since
`R3 = EuclideanSpace ℝ (Fin 3)` is definitionally `Fin 3 → ℝ`, both the pointwise subtraction of
vector fields and the extraction of a component are (definitionally) pointwise, so the statement
reduces to the two elementary facts that the difference of two odd functions is odd and the
difference of two even functions is even.
-/

/-- The difference of two odd functions `ℝ → ℝ` is odd. -/
private theorem odd_sub_fun {f g : ℝ → ℝ} (hf : Function.Odd f) (hg : Function.Odd g) :
    Function.Odd (f - g) := by
  intro a
  simp only [Pi.sub_apply, hf a, hg a]
  ring

/-- The difference of two even functions `ℝ → ℝ` is even. -/
private theorem even_sub_fun {f g : ℝ → ℝ} (hf : Function.Even f) (hg : Function.Even g) :
    Function.Even (f - g) := by
  intro a
  simp only [Pi.sub_apply, hf a, hg a]

theorem isOdd_sub {u v : Work.FTS.BSIdent.R3 → Work.FTS.BSIdent.R3}
    (hu : FiniteTimeSingularity.IsOdd u) (hv : FiniteTimeSingularity.IsOdd v) :
    FiniteTimeSingularity.IsOdd (u - v) := by
  obtain ⟨hu1, hu2, hu3⟩ := hu
  obtain ⟨hv1, hv2, hv3⟩ := hv
  refine ⟨fun x₁ x₂ => ?_, fun x₀ x₂ => ?_, fun x₀ x₁ => ?_⟩
  · obtain ⟨a, b, c⟩ := hu1 x₁ x₂
    obtain ⟨a', b', c'⟩ := hv1 x₁ x₂
    exact ⟨odd_sub_fun a a', even_sub_fun b b', even_sub_fun c c'⟩
  · obtain ⟨a, b, c⟩ := hu2 x₀ x₂
    obtain ⟨a', b', c'⟩ := hv2 x₀ x₂
    exact ⟨even_sub_fun a a', odd_sub_fun b b', even_sub_fun c c'⟩
  · obtain ⟨a, b, c⟩ := hu3 x₀ x₁
    obtain ⟨a', b', c'⟩ := hv3 x₀ x₁
    exact ⟨even_sub_fun a a', even_sub_fun b b', odd_sub_fun c c'⟩

end Work.FTS.BSIdent.Parity
