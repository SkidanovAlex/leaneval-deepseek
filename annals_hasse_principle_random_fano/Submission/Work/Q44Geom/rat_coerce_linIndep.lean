import Mathlib
import Submission.Work.Q44Geom.Setup
import Submission.Work.HP.Q44Child.lam_attained

namespace Work.Q44Geom

/-- The coefficientwise coercion `ℤ^5 → ℚ^5` sends `ℤ`-linearly independent pairs of
integral vectors to `ℚ`-linearly independent pairs of rational vectors.

This is the "fraction ring" direction of `LinearIndependent.iff_fractionRing`: for the finite
index set `Fin 5`, `algebraMap ℤ ℚ ∘ b = toRatLM b`, so the result follows from
`linearIndependent_algebraMap_comp_iff`. -/
theorem rat_coerce_linIndep (b₁ b₂ : Fin 5 → ℤ) :
    LinearIndependent ℤ ![b₁, b₂] →
      LinearIndependent ℚ ![Work.Q44Geom.toRatLM b₁, Work.Q44Geom.toRatLM b₂] := by
  intro h
  have key :=
    (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℚ) (v := ![b₁, b₂])).mpr h
  have hfun : (![Work.Q44Geom.toRatLM b₁, Work.Q44Geom.toRatLM b₂] : Fin 2 → (Fin 5 → ℚ))
      = fun i => algebraMap ℤ ℚ ∘ ![b₁, b₂] i := by
    funext i j
    fin_cases i <;> rfl
  rw [hfun]
  exact key

end Work.Q44Geom
