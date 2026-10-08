import Mathlib
import Submission.Work.BG.Defs
import Submission.Work.BG.Lambda

namespace Work.BG

open Subgroup
open OddOrder.RepresentationTheory

/-- `Λ` is closed under the pointwise product of class functions: the product of the inflations
of `β₁, β₂ : H₀/U →* ℂˣ` is the inflation of `β₁ * β₂`, because
`linearClassFunction` is multiplicative and pullback along `quotMk P` commutes with the
pointwise product. -/
theorem lambda_mul_mem {G : Type} [Group G] [Finite G] (P : Work.BG.Hyp12 G)
    [(P.U.subgroupOf P.H0).Normal]
    {δ₁ δ₂ : OddOrder.RepresentationTheory.ClassFunction ↥P.H0 ℂ}
    (h₁ : δ₁ ∈ Work.BG.Lambda P) (h₂ : δ₂ ∈ Work.BG.Lambda P) :
    δ₁ * δ₂ ∈ Work.BG.Lambda P := by
  obtain ⟨β₁, rfl⟩ := h₁
  obtain ⟨β₂, rfl⟩ := h₂
  exact ⟨β₁ * β₂, by ext h; simp [ClassFunction.mul_apply]⟩

end Work.BG
