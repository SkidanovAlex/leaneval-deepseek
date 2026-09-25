import Mathlib
import Submission.Work.Beltrami.beurlingV
import Submission.Work.Beltrami.beurling_bounded
import Submission.Work.Beltrami.beurling_holder_difference
import Submission.Work.Beltrami.beurling_holder_uniform

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff

/-- **Schauder (Calderón–Zygmund) estimates for the Beurling transform with a constant that is
uniform in the function.**  There is a positive constant `C`, depending only on `α` with
`0 < α < 1`, such that `IsSchauderBound α C` holds; here `Work.Beltrami.IsSchauderBound` (defined in
the module `Submission.Work.Beltrami.beurlingV`) says that for *every* function `f` bounded by `M`,
globally `α`-Hölder with constant `K` and supported in the ball of radius `R ≥ 0`, the Beurling
transform `beurling f` is bounded by `C (M + K) (1 + R)` and is globally `α`-Hölder with constant
`C (M + K) (1 + R)`.

The explicit constants are provided by `Work.Beltrami.beurling_holder_uniform`
(module `Submission.Work.Beltrami.beurling_holder_uniform`), which makes the constants in the
proofs of `Work.Beltrami.beurling_bounded` and `Work.Beltrami.beurling_holder_difference`
explicit: the pointwise bound uses `2 / α + 10` and the Hölder bound uses
`max (12π/α + 72π + (12π·2^(α-1)/(1-α) + C₃ + 12 + π)) (2·(2/α+10)) + 1`, where `C₃` is the
absolute constant of `Work.Beltrami.Holder.W_translate_L1_bound`.  Both constants are independent
of the function, so choosing `C = Cfun α` for the uniform family `Cfun` yields the claim. -/
theorem beurling_schauder_uniform (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, Work.Beltrami.IsSchauderBound α C := by
  obtain ⟨Cfun, hCfun_pos, hCfun⟩ := beurling_holder_uniform
  refine ⟨Cfun α, hCfun_pos α hα, ?_⟩
  intro M K R f hR hM hK hsupp
  exact hCfun α M K R f hα hα1 hR hM hK hsupp

end Work.Beltrami
