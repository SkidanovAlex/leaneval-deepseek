import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.subIdealDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.BW

/-
  Mathlib's graded primality criterion (`Ideal.IsHomogeneous.isPrime_iff`) is stated for a grading
  indexed by a linearly ordered cancellative additive monoid.  The multidegree monoid
  `Fin (N+1) →₀ ℕ` carries its lexicographic order only through the `Lex` synonym (which is
  definitionally the identity), and the instance arguments of `Ideal.IsHomogeneous` (`DecidableEq`
  and the `GradedRing` structure) are not proof-irrelevant, so their choice has to be pinned
  explicitly for the statements used here to agree with the statement of Mathlib's lemma: the
  `DecidableEq` has to be the one coming from the linear order, and the grading has to be
  `multigrade N` with that same `DecidableEq` (it is definitionally the weighted grading whose
  pieces are `homPiece N d`).
-/
lemma isPrime_of_multiHom {N : ℕ} (I : Ideal (MR N)) (hne : I ≠ ⊤) (hI : MultiHom N I)
    (h : ∀ f g : MR N, (∃ d, f ∈ homPiece N d) → (∃ d, g ∈ homPiece N d) →
      f * g ∈ I → f ∈ I ∨ g ∈ I) : I.IsPrime := by
  letI : LinearOrder (Lex (Fin (N + 1) →₀ ℕ)) := Finsupp.Lex.linearOrder
  letI : DecidableEq (Lex (Fin (N + 1) →₀ ℕ)) := LinearOrder.toDecidableEq
  letI : GradedRing (multigrade N) := MvPolynomial.weightedGradedAlgebra ℂ (mdegLex N)
  -- `I` is closed under the multihomogeneous components, i.e. it is a homogeneous ideal.
  have hIhom : I.IsHomogeneous (multigrade N) := by
    intro i p hp
    have key : (DirectSum.decompose (multigrade N) p i : MR N)
        = MvPolynomial.weightedHomogeneousComponent (mdeg N) (ofLex i) p :=
      MvPolynomial.weightedDecomposition.decompose'_apply ℂ (mdegLex N) p i
    rw [key]
    exact hI p hp (ofLex i)
  -- Hence the graded criterion applies.
  refine (Ideal.IsHomogeneous.isPrime_iff (𝒜 := multigrade N) hIhom).mpr ⟨hne, ?_⟩
  intro x y hx hy hxy
  obtain ⟨dx, hdx⟩ := hx
  obtain ⟨dy, hdy⟩ := hy
  exact h x y ⟨ofLex dx, hdx⟩ ⟨ofLex dy, hdy⟩ hxy

end Work.BW
