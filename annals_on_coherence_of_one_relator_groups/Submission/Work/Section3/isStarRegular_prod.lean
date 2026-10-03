import Mathlib
import Submission.Work.ORHughesFree.StarRegular

universe u

namespace Work.Section3

open Work.ORHughesFree

/-- The product of two ∗-regular rings is ∗-regular, componentwise. -/
theorem isStarRegular_prod {U₁ U₂ : Type u} [Ring U₁] [StarRing U₁]
    [Work.ORHughesFree.IsStarRegular U₁] [Ring U₂] [StarRing U₂]
    [Work.ORHughesFree.IsStarRegular U₂] : Work.ORHughesFree.IsStarRegular (U₁ × U₂) := by
  constructor
  · refine ⟨fun x => ?_⟩
    obtain ⟨y₁, hy₁⟩ := (inferInstance : VonNeumannRegularRing U₁).exists_mul_inverse x.1
    obtain ⟨y₂, hy₂⟩ := (inferInstance : VonNeumannRegularRing U₂).exists_mul_inverse x.2
    exact ⟨(y₁, y₂), Prod.ext hy₁ hy₂⟩
  · intro x hx
    have h1 : star x.1 * x.1 = 0 := congrArg Prod.fst hx
    have h2 : star x.2 * x.2 = 0 := congrArg Prod.snd hx
    exact Prod.ext ((inferInstance : IsStarRegular U₁).proper x.1 h1)
      ((inferInstance : IsStarRegular U₂).proper x.2 h2)

end Work.Section3
