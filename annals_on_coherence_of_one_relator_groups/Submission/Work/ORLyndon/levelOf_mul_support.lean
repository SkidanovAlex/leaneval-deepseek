import Mathlib
import Submission.Work.ORLyndon.powDefs

namespace Work.ORLyndon

theorem levelOf_mul_support {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1) {m n : ℤ}
    {a b : MonoidAlgebra K (OneRelatorGroup r)}
    (ha : ∀ g ∈ a.coeff.support, Work.ORLyndon.levelOf t r u l hpow hσ g = Multiplicative.ofAdd m)
    (hb : ∀ g ∈ b.coeff.support, Work.ORLyndon.levelOf t r u l hpow hσ g = Multiplicative.ofAdd n) :
    ∀ g ∈ (a * b).coeff.support,
      Work.ORLyndon.levelOf t r u l hpow hσ g = Multiplicative.ofAdd (m + n) := by
  classical
  intro g hg
  -- The support of a product is contained in the product of the supports.
  have hmem := MonoidAlgebra.support_coeff_mul_subset (x := a) (y := b) hg
  rw [Finset.mem_mul] at hmem
  obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hmem
  rw [map_mul, ha g₁ hg₁, hb g₂ hg₂]
  simp

end Work.ORLyndon
