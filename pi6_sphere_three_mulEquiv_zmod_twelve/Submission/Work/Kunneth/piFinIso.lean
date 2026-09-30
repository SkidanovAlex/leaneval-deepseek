import Mathlib
import Submission.Work.Kunneth.Basic

/-!
# Collapsing a finite product of free `ℤ`-modules

`Work.Kunneth.piFinIso` writes a finite product of copies of `ℤ`, indexed by `Fin (k i)` over a
finite type `α`, as a single `ℤ`-module `Fin (∑ i, k i) → ℤ`: the product is free on the disjoint
union `Σ i, Fin (k i)` of the bases, whose cardinality is `∑ i, k i`.

This is the bookkeeping that turns a Künneth target `∏_{p+q=n} Hᵖ(X) ⊗ H^q(Y)` into `ℤ^r` once the
individual factors are known to be copies of `ℤ` or `0`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Kunneth

noncomputable section

/-- A finite product of copies of `ℤ` indexed by `Fin (k i)` is `ℤ^{∑ i, k i}`. -/
theorem piFinIso (α : Type*) [Fintype α] (k : α → ℕ) :
    Nonempty ((∀ i : α, Fin (k i) → ℤ) ≃ₗ[ℤ] (Fin (∑ i, k i) → ℤ)) := by
  have hcard : Fintype.card (Σ i : α, Fin (k i)) = ∑ i, k i := by
    rw [Fintype.card_sigma]
    simp
  -- the sigma type of the individual bases
  have e : Fin (∑ i, k i) ≃ (Σ i : α, Fin (k i)) :=
    (finCongr hcard.symm).trans (Fintype.equivFin (Σ i : α, Fin (k i))).symm
  -- curry a dependent product into a product over the sigma type, then reindex
  refine ⟨(LinearEquiv.piCurry ℤ (fun (i : α) (_ : Fin (k i)) => ℤ)).symm.trans
    (LinearEquiv.piCongrLeft ℤ (fun _ : (Σ i : α, Fin (k i)) => ℤ) e).symm⟩

end

end Work.Kunneth
