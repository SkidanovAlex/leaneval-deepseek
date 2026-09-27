import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.SmallChains

/-!
# Notation for the relative Mayer–Vietoris argument

Self-contained notation (not depending on `Work.Compact.Noncompact.Good`) for the chains, boundary
and support submodules used in `Submission/Work/Compact/Noncompact/relChains_diagonal_injective.lean`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Compact.Noncompact

noncomputable section

/-- The singular `k`-chains of `X` with `ℤ` coefficients. -/
abbrev rCh (X : TopCat) (k : ℕ) : Type := (Work.Cohomology.singularChains ℤ X).X k

/-- The singular boundary `C_{k+1}(X) → C_k(X)` as a linear map. -/
abbrev rbd (X : TopCat) (k : ℕ) : rCh X (k + 1) →ₗ[ℤ] rCh X k :=
  ((Work.Cohomology.singularChains ℤ X).d (k + 1) k).hom

/-- The submodule of `k`-chains of `X` supported in `S ⊆ X`: the image of the map
`C_k(S) → C_k(X)` induced by the inclusion. -/
abbrev rSupp (X : TopCat) (S : Set X) (k : ℕ) : Submodule ℤ (rCh X k) :=
  LinearMap.range (((Work.Cohomology.inclChains X S).f k).hom)

end

end Work.Compact.Noncompact
