import Mathlib
import Submission.Work.ORLyndon.powDefs

/-!
# A level part of an element supported in a single level

Let `G = ⟨α | r⟩` with `r = u ^ l`, and let `σ_t u = 1`, so that the exponent sum `σ_t` descends to
the `σ_t`-level map `levelOf t r u l hpow hσ : G →* Multiplicative ℤ` of the decomposition
`G = ker(σ_t) ⋊ ⟨t̄⟩`.

If every group element occurring in the support of `a : K[G]` has level exactly `Multiplicative.ofAdd j`,
then the `i`-th level part of `a` is `a` itself when `i = j` and `0` otherwise:

`levelPart t r u l hpow hσ i a = if i = j then a else 0`.

The proof is the definition of `levelPart` as the coefficient function filtered by the level: the
filter keeps a term `g` exactly when `levelOf … g = ofAdd i`, and on the support of `a` the level is
`ofAdd j` throughout, while outside the support the coefficient vanishes anyway.
-/

namespace Work.ORLyndon

theorem levelPart_eq_of_support_level {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1) (i j : ℤ) (a : MonoidAlgebra K (OneRelatorGroup r))
    (h : ∀ g ∈ a.coeff.support,
      Work.ORLyndon.levelOf t r u l hpow hσ g = Multiplicative.ofAdd j) :
    Work.ORLyndon.levelPart t r u l hpow hσ i a = if i = j then a else 0 := by
  classical
  by_cases hij : i = j
  · rw [if_pos hij]
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro g
    rw [Work.ORLyndon.levelPart_coeff]
    by_cases hg : g ∈ a.coeff.support
    · have hlev := h g hg
      rw [if_pos (hlev.trans (congrArg Multiplicative.ofAdd hij).symm)]
    · have hz : a.coeff g = 0 := by
        simpa using (Finsupp.mem_support_iff (f := a.coeff) (a := g)).not.mp hg
      rw [hz]
      split <;> rfl
  · rw [if_neg hij]
    apply MonoidAlgebra.ext
    rw [MonoidAlgebra.coeff_zero]
    apply Finsupp.ext
    intro g
    rw [Finsupp.zero_apply, Work.ORLyndon.levelPart_coeff]
    by_cases hg : g ∈ a.coeff.support
    · have hlev := h g hg
      exact if_neg (fun hc => hij (Multiplicative.ofAdd.injective (hlev.symm.trans hc)).symm)
    · have hz : a.coeff g = 0 := by
        simpa using (Finsupp.mem_support_iff (f := a.coeff) (a := g)).not.mp hg
      rw [hz]
      split <;> rfl

end Work.ORLyndon
