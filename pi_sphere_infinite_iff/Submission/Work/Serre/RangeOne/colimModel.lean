import Mathlib
import Submission.Work.Serre.RangeOne.Defs
import Submission.Work.Serre.RangeOne.towerColim

/-!
# The range model of `K(π₁W, 1)`: the colimit of the truncation tower

The target `Work.Serre.RangeOne.colimModel` (the comparison input of `Serre.serreRangeEMVanOne`)
is proved from the colimit `Z` of the truncation tower of `W` (`Work.Serre.RangeOne.chain`):

* the inclusion `inclChain : W → Z` is a `πᵢ`-bijection for `i ≤ N`
  (`Work.Serre.RangeOne.bijective_piMapN`),
* `π₁(Z,pt) ≅ π₁(W,w₀)` (`Work.Serre.RangeOne.piOneMulEquiv`),
* `πᵢ(Z,pt) = 0` for `i ≠ 1` (`subsingleton_pi_zero`, `subsingleton_pi_of_two_le`).

The hypotheses `hcomm` and `htors` are not used by the construction: they belong to the
*application* of Serre's theorem to the range model, not to the model itself.
-/

namespace Work.Serre.RangeOne

theorem colimModel (N : ℕ) (W : Type) [TopologicalSpace W] (w₀ : W)
    (h0 : Subsingleton (HomotopyGroup (Fin 0) W w₀))
    (hcomm : ∀ a b : HomotopyGroup (Fin 1) W w₀, a * b = b * a)
    (htors : ∀ α : HomotopyGroup (Fin 1) W w₀, ∃ K : ℕ, 0 < K ∧ α ^ K = 1)
    (hvan : ∀ i : ℕ, 2 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) W w₀)) :
    Work.Serre.RangeModelComparison N W w₀ := by
  refine ⟨(chain W w₀).Z, (chain W w₀).instTopologicalSpace, pt w₀, inclChain W w₀,
    ⟨piOneMulEquiv (W := W) (w₀ := w₀), fun i hi => ?_⟩, ?_⟩
  · rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      exact subsingleton_pi_zero (W := W) (w₀ := w₀) h0
    · exact subsingleton_pi_of_two_le (W := W) (w₀ := w₀) i (by omega)
  · intro i hi x
    exact bijective_piMapN (W := W) (w₀ := w₀) N h0 hvan i hi x

end Work.Serre.RangeOne
