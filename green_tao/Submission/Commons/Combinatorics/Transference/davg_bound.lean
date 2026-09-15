import Mathlib
import Submission.Commons.Combinatorics.Transference.poly_lemma_abstract
import Submission.Commons.Combinatorics.Transference.dualFunc_bound

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- The two ways of writing the `ω`-linear combination of `h` agree. -/
private lemma shift_eq {p : ℕ} {d : ℕ} (b : ZMod p) (ω : Fin d → Bool) (h : Fin d → ZMod p) :
    b + ∑ i : Fin d, (if ω i then h i else 0)
      = b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j := by
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : ω j <;> simp [hj]

/-- **Sup-norm bound for the dual function** (Green–Tao `(dual-bounded)`), from the *local
linear forms condition* on `ν`: for every nonempty family `A` of nonzero Boolean vectors, the
`A`-cube average of `ν` is `1 + O(ε)`.  Under this condition and `|F| ≤ ν + 1` the dual function
`𝒟F` is bounded by `2^{2^d - 1}(1+ε)`. -/
theorem davg_bound {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) (ν F : ZMod p → ℝ)
    (hF : ∀ x, |F x| ≤ ν x + 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hLFC : ∀ A : Finset (Fin d → Bool), A ⊆ Finset.univ.erase (0 : Fin d → Bool) →
      A.Nonempty → ∀ b : ZMod p,
      |((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
        (∑ h : Fin d → ZMod p,
          ∏ ω ∈ A, ν (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)) - 1| ≤ ε)
    (b : ZMod p) : |davg d F b| ≤ ((2 : ℝ) ^ (2 ^ d - 1)) * (1 + ε) := by
  have h := dualFunc_bound hd ν F hF hε hLFC b
  have key : davg d F b = ((Fintype.card (Fin d → ZMod p) : ℝ))⁻¹ *
      (∑ h : Fin d → ZMod p, ∏ ω ∈ Finset.univ.erase (0 : Fin d → Bool),
        F (b + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)) := by
    rw [davg]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.prod_congr rfl
    intro ω _
    rw [shift_eq]
  rw [key]
  exact h

end Commons.Combinatorics.Transference
