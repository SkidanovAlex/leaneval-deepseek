import Mathlib
import Submission.Work.WilkiesB.Defs

namespace Work.WilkiesB

/-- Pullback of an existentially definable set along a map of the ambient index types.

If `X` is the projection of the zero set of an exp-polynomial in the ambient variables `κ` with
finitely many witnesses, then `{z : ν → ℝ | z ∘ f ∈ X}` is again of that form: rename the ambient
variables along `Sum.map f id` and use that `Sum.elim z y ∘ Sum.map f id = Sum.elim (z ∘ f) y`. -/
theorem ExpExistI_pullback {κ ν : Type*} (f : κ → ν) {X : Set (κ → ℝ)} (hX : ExpExistI X) :
    ExpExistI {z : ν → ℝ | z ∘ f ∈ X} := by
  obtain ⟨μ, hμ, P, hP⟩ := hX
  refine ⟨μ, hμ, MvPolynomial.rename (polyMap (Sum.map f id)) P, ?_⟩
  rw [hP]
  ext z
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by
      rw [expEval_rename (Sum.map f id) (Sum.elim z y) P, sumElim_comp_map]
      exact hy⟩
  · rintro ⟨y, hy⟩
    rw [expEval_rename (Sum.map f id) (Sum.elim z y) P, sumElim_comp_map] at hy
    exact ⟨y, hy⟩

end Work.WilkiesB
