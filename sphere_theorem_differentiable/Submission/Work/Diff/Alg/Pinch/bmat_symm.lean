import Mathlib
import Submission.Work.Diff.Alg.Pinch.RicFormDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Symmetry of `bmat`

`bmat v R p q = ∑ᵢⱼ vᵢ vⱼ R i p j q` is the `(0,2)`-tensor obtained by contracting the first and
third index of the four-index array `R` with `v`; in frame notation it is `R(v, e_p, v, e_q)`.

For an algebraic curvature tensor the pair symmetry `R i p j q = R j q i p` gives
`bmat v R p q = bmat v R q p`: the two "pairs" of `R(v, e_p, v, e_q)` are `(v, e_p)` and
`(v, e_q)`, and swapping them exchanges `p` and `q`.

This is used by `Work.Diff.Alg.Pinch.ricForm_X_strict_at_tight_a` and the
`EFun`/`ricForm` pointwise lemmas, where `∑_{p q} M p q · bmat v R p q` is symmetrised.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

theorem bmat_symm (n : ℕ) {S : Submission.Diff.Alg.Curv4 n}
    (hS : Submission.Diff.Alg.IsAlgCurv S) (v : Fin n → ℝ) :
    ∀ p q, Work.Diff.Alg.Pinch.bmat v S p q = Work.Diff.Alg.Pinch.bmat v S q p := by
  obtain ⟨hanti, hpair, _⟩ := hS
  intro p q
  simp only [bmat]
  -- pair symmetry of an algebraic curvature tensor: `S i p j q = S j q i p`
  have h1 : (∑ i, ∑ j, v i * v j * S i p j q) = ∑ i, ∑ j, v i * v j * S j q i p := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hpair j q i p]
  rw [h1]
  -- swap the two summation indices: `∑ᵢⱼ f i j = ∑ᵢⱼ f j i`
  trans ∑ i, ∑ j, v j * v i * S i q j p
  · rw [Finset.sum_comm]
  · apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring

end Work.Diff.Alg.Pinch
