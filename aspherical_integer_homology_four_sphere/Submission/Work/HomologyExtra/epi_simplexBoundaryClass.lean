import Mathlib
import Submission.Work.HomologyExtra.SimplexClass
import Submission.Work.HomologyExtra.simplexGenMap_pairdelta
import Submission.Work.HomologyExtra.GeneratorReduction
import Submission.Work.HomologyExtra.SimplexStar
import Submission.Work.HomologyExtra.simplexBoundaryClass_one_epi
import Submission.Work.HomologyExtra.epi_simplexBoundaryClass_of_epi_simplexGenMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The fundamental class of `∂Δⁿ⁺¹` generates `Hₙ(∂Δⁿ⁺¹)`

The class `simplexBoundaryClass n` of the alternating sum of the faces of the identity
`(n+1)`-simplex is the fundamental class of the sphere `∂Δⁿ⁺¹ ≅ Sⁿ`; it generates
`Hₙ(∂Δⁿ⁺¹; ℤ) ≅ ℤ`.

The two ingredients of the induction on `n` are

* `simplexGenMap_pairdelta`: `simplexGenMap (m+1) ≫ pairδ = simplexBoundaryClass m`, where
  `pairδ` is the connecting homomorphism of the pair `(Δᵐ⁺¹, ∂Δᵐ⁺¹)`; it is an isomorphism for
  `m ≥ 1` (`isIso_pairdelta_of_isZero`, the outer terms vanishing because the simplex is
  contractible).  Hence `Epi (simplexBoundaryClass m)` follows from `Epi (simplexGenMap (m+1))`,
  and conversely.
* `epi_simplexBoundaryClass_of_epi_simplexGenMap`: the geometric transfer from the pair
  `(Δⁿ, ∂Δⁿ)` to the sphere `∂Δⁿ⁺¹`, using the splitting of the fundamental cycle of `∂Δⁿ⁺¹`
  into the part carried by the closed star of the last vertex and the face opposite that vertex
  (see `Submission/Work/HomologyExtra/SimplexStar.lean`): `Epi (simplexGenMap n)` implies
  `Epi (simplexBoundaryClass n)`.

The base case is `simplexBoundaryClass_one_epi` (`∂Δ² ≅ S¹`).
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.HomologyExtra

noncomputable section

/-- The connecting homomorphism `pairδ` of the pair `(Δ^{k+2}, ∂Δ^{k+2})` in degree `k+1` is an
isomorphism: the outer terms of the pair sequence vanish because the simplex `Δ^{k+2}` is
contractible. -/
theorem isIso_pairdelta_succ_succ (k : ℕ) :
    IsIso (Work.Homology.pairδ Work.Homology.ZMod (simplex (k + 2)) (simplexBoundary (k + 2))
      (k + 1)) := by
  have h1 : IsZero (Work.Homology.singHomology Work.Homology.ZMod (k + 2) (simplex (k + 2))) := by
    have h := Work.Homology.StdSimplexHomology Work.Homology.ZMod (k + 2) (k + 1)
    simpa [simplex] using h
  have h2 : IsZero (Work.Homology.singHomology Work.Homology.ZMod (k + 1) (simplex (k + 2))) := by
    have h := Work.Homology.StdSimplexHomology Work.Homology.ZMod (k + 2) k
    simpa [simplex] using h
  exact isIso_pairδ_of_isZero (k + 2) (k + 1) h1 h2

/-- **The class of the identity simplex generates the top relative homology of
`(Δ^{k+2}, ∂Δ^{k+2})` as soon as the fundamental cycle generates `H_{k+1}(∂Δ^{k+2})`**: by
`simplexGenMap_pairdelta` the class of the identity simplex is the image of the fundamental class
of the boundary sphere under the inverse of the connecting homomorphism of the pair, which is an
isomorphism. -/
theorem epi_simplexGenMap_of_epi_simplexBoundaryClass (k : ℕ)
    (h : CategoryTheory.Epi (simplexBoundaryClass (k + 1))) :
    CategoryTheory.Epi (simplexGenMap (k + 2)) := by
  haveI : IsIso (Work.Homology.pairδ Work.Homology.ZMod (simplex (k + 2))
      (simplexBoundary (k + 2)) (k + 1)) := isIso_pairdelta_succ_succ k
  have hcomp : CategoryTheory.CategoryStruct.comp (simplexGenMap (k + 2))
      (Work.Homology.pairδ Work.Homology.ZMod (simplex (k + 2)) (simplexBoundary (k + 2))
        (k + 1)) = simplexBoundaryClass (k + 1) := simplexGenMap_pairdelta (k + 1)
  have heq : simplexGenMap (k + 2) =
      CategoryTheory.CategoryStruct.comp (simplexBoundaryClass (k + 1))
        (inv (Work.Homology.pairδ Work.Homology.ZMod (simplex (k + 2))
          (simplexBoundary (k + 2)) (k + 1))) := by
    rw [← hcomp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [heq]
  exact epi_comp _ _

/-- **The fundamental class of the sphere `∂Δⁿ⁺¹` generates `Hₙ(∂Δⁿ⁺¹; ℤ)`** for every `n ≥ 1`:
the alternating sum `∑ᵢ (-1)ⁱ Fᵢ` of the codimension-one faces of the identity `(n+1)`-simplex —
the fundamental cycle of the simplicial sphere `∂Δⁿ⁺¹ ≅ Sⁿ` — is a generator of
`Hₙ(∂Δⁿ⁺¹; ℤ) ≅ ℤ`, i.e. the corresponding map `ℤ ⟶ Hₙ(∂Δⁿ⁺¹; ℤ)` is surjective.

(`n = 0` is excluded because `∂Δ¹` is a two-point space, whose zeroth homology is `ℤ²`, and the
class of `F₀ - F₁` generates only the augmentation kernel.) -/
theorem epi_simplexBoundaryClass (n : ℕ) (hn : 1 ≤ n) :
    CategoryTheory.Epi (Work.HomologyExtra.simplexBoundaryClass n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · -- base case `n = 1`
      interval_cases n
      exact simplexBoundaryClass_one_epi
    · -- induction step: `Epi (simplexBoundaryClass n)` follows from `Epi (simplexGenMap n)`,
      -- which follows from `Epi (simplexBoundaryClass (k+1))` with `n = k+2`
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
      have hk : 1 ≤ k + 1 := by omega
      have hprev : CategoryTheory.Epi (simplexBoundaryClass (k + 1)) :=
        ih (k + 1) (by omega) hk
      exact epi_simplexBoundaryClass_of_epi_simplexGenMap (k + 2) (by omega)
        (epi_simplexGenMap_of_epi_simplexBoundaryClass k hprev)

end

end Work.HomologyExtra
