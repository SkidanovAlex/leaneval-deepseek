import Mathlib
import Submission.Work.Cohomology.relChains_free
import Submission.Work.Cohomology.relChains_empty_homology_iso

/-!
# The singular chains are degreewise free

For a topological space `X` and `n : ℕ`, the singular `n`-chains `C_n(X;ℤ)` form a free
`ℤ`-module (`singularChains_free`).

They are the coproduct, over the singular `n`-simplices of `X`, of copies of `ℤ`, hence a direct
sum of free modules.  Rather than re-deriving this from the coproduct description, we obtain it
from the relative chains of the *empty* subset: the empty space has no simplices, so its chain
complex is a zero object, the inclusion `C_*(∅) ⟶ C_*(X)` is the zero morphism, and consequently
the cokernel projection `C_*(X) ⟶ C_*(X,∅)` is an isomorphism (degreewise the cokernel projection
of `0 : C_n(∅) ⟶ C_n(X)`).  Since `C_n(X,∅)` is free by `relChains_free`, so is `C_n(X)`.

## Main result

* `singularChains_free` — `C_n(X;ℤ)` is a free `ℤ`-module.
-/

set_option linter.style.haveILetI false

open CategoryTheory Limits

namespace Work.Cohomology

noncomputable section

theorem singularChains_free (X : TopCat) (n : ℕ) :
    Module.Free ℤ ↥((Work.Cohomology.singularChains ℤ X).X n) := by
  -- The inclusion `C_*(∅) ⟶ C_*(X)` is the zero morphism, hence so is its `n`-th component.
  have h0 : (inclChains X (∅ : Set X)).f n = 0 := by
    rw [inclChains_empty_eq_zero X]
    simp
  -- The cokernel projection of a zero morphism is an isomorphism.
  haveI : IsIso (cokernel.π ((inclChains X (∅ : Set X)).f n)) :=
    cokernel.π_of_zero h0
  -- `C_n(X,∅)` is free, and the projection `C_n(X) ⟶ C_n(X,∅)` is an isomorphism.
  refine Module.Free.of_equiv' (relChains_free X (∅ : Set X) n) ?_
  exact (relChains_cokernelIso X (∅ : Set X) n).toLinearEquiv.trans
    (asIso (cokernel.π ((inclChains X (∅ : Set X)).f n))).toLinearEquiv.symm

end

end Work.Cohomology
