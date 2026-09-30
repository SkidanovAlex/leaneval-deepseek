import Mathlib
import ChallengeDeps
import Submission.Work.HomologyExtra.Basic
import Submission.Work.HomologyExtra.SimplexClass
import Submission.Work.HomologyExtra.SimplexPairHomology
import Submission.Work.HomologyExtra.Generator
import Submission.Work.HomologyExtra.GeneratorOne
import Submission.Work.HomologyExtra.isIso_simplexGenMap_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `H_k(Δⁿ, ∂Δⁿ; ℤ)` with the identity simplex as explicit generator

The headline results of the chapter, in the form a consumer should use.

* `Work.HomologyExtra.simplexPair_homology` — **`H_k(Δⁿ, ∂Δⁿ; ℤ) ≅ ℤ` for `k = n` and `0`
  otherwise** (`n ≥ 1`);
* `Work.HomologyExtra.epi_simplexGenMap` — **the class `[ιₙ]` of the identity singular simplex
  generates `Hₙ(Δⁿ,∂Δⁿ; ℤ)``**: the map `ℤ ⟶ Hₙ(Δⁿ,∂Δⁿ; ℤ)`, `1 ↦ [ιₙ]`, is an epimorphism;
* `Work.HomologyExtra.isIso_simplexGenMap` — and it is an isomorphism, i.e. `[ιₙ]` is a *free
  generator* of the rank-`1` group `Hₙ(Δⁿ,∂Δⁿ; ℤ)`;
* `Work.HomologyExtra.isIso_simplexGenMap_all n : IsIso (simplexGenMap n)` — the same in **every**
  degree, including `n = 0` (`∂Δ⁰ = ∅`), where it is `isIso_simplexGenMap_zero`;
* `Work.HomologyExtra.simplexGenMapIso n (hn : 1 ≤ n) : ℤ ≅ Hₙ(Δⁿ,∂Δⁿ;ℤ)` — the same as an
  explicit isomorphism, with `simplexGenMapIso_hom : (simplexGenMapIso n hn).hom = simplexGenMap n`
  and `simplexPair_homology_top_generator` its `∃ e, e.hom = simplexGenMap n` form.

Here `Δⁿ = Work.HomologyExtra.simplex n = TopCat.of (Convexity.StdSimplex ℝ (Fin (n+1)))`, the same
simplex that the singular chain complex uses, and `∂Δⁿ = Work.HomologyExtra.simplexBoundary n` is
its boundary (the union of the codimension-one faces).

The cases `n = 1, 2, 3, …` are handled by `epi_simplexGenMap_one`
(`Submission/Work/HomologyExtra/GeneratorOne.lean`) and `epi_simplexGenMap_of_two_le`
(`Submission/Work/HomologyExtra/Generator.lean`) respectively; the case `n = 0`, where the boundary
is empty, is `Work.HomologyExtra.isIso_simplexGenMap_zero`
(`Submission/Work/HomologyExtra/isIso_simplexGenMap_zero.lean`), and is not needed by the
`Δ`-complex comparison, which works in degrees `n ≥ 1`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.HomologyExtra

noncomputable section

/-- **The class of the identity simplex generates `Hₙ(Δⁿ,∂Δⁿ)` for every `n ≥ 1`**: the map
`ℤ ⟶ Hₙ(Δⁿ,∂Δⁿ;ℤ)`, `1 ↦ [ιₙ]`, is an epimorphism. -/
theorem epi_simplexGenMap (n : ℕ) (hn : 1 ≤ n) : Epi (simplexGenMap n) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    exact epi_simplexGenMap_one
  · exact epi_simplexGenMap_of_two_le n h

/-- **The class of the identity simplex is a generator of `Hₙ(Δⁿ,∂Δⁿ)` for every `n ≥ 1`**: the map
`ℤ ⟶ Hₙ(Δⁿ,∂Δⁿ;ℤ)`, `1 ↦ [ιₙ]`, is an isomorphism. -/
theorem isIso_simplexGenMap (n : ℕ) (hn : 1 ≤ n) : IsIso (simplexGenMap n) :=
  isIso_simplexGenMap_of_epi n (epi_simplexGenMap n hn) (relHomology_simplexPair_top n hn)

/-- **The class of the identity simplex generates `Hₙ(Δⁿ,∂Δⁿ;ℤ)` in every degree** — this is
`isIso_simplexGenMap n (by omega)` for `n ≥ 1`, and `isIso_simplexGenMap_zero` for `n = 0`, where
`∂Δ⁰ = ∅`. -/
theorem isIso_simplexGenMap_all (n : ℕ) : IsIso (simplexGenMap n) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    exact isIso_simplexGenMap_zero
  · exact isIso_simplexGenMap n h

/-- **The isomorphism `ℤ ≅ Hₙ(Δⁿ,∂Δⁿ)` whose underlying map is `1 ↦ [ιₙ]`**: this is the explicit
form of the statement that the class of the identity singular simplex is a *generator* of the
relative homology of the standard simplex pair. -/
noncomputable def simplexGenMapIso (n : ℕ) (hn : 1 ≤ n) :
    Work.Homology.ZMod ≅ Work.Homology.relHomology Work.Homology.ZMod n (simplex n)
      (simplexBoundary n) :=
  letI : IsIso (simplexGenMap n) := isIso_simplexGenMap n hn
  { hom := simplexGenMap n
    inv := CategoryTheory.inv (simplexGenMap n)
    hom_inv_id := IsIso.hom_inv_id (simplexGenMap n)
    inv_hom_id := IsIso.inv_hom_id (simplexGenMap n) }

@[simp]
theorem simplexGenMapIso_hom (n : ℕ) (hn : 1 ≤ n) :
    (simplexGenMapIso n hn).hom = simplexGenMap n := rfl

/-- **The class of the identity simplex exhibits `Hₙ(Δⁿ,∂Δⁿ;ℤ) ≅ ℤ`**: there is an isomorphism
whose underlying morphism is `simplexGenMap n`, i.e. which sends `1` to the relative homology class
of the identity singular simplex. -/
theorem simplexPair_homology_top_generator (n : ℕ) (hn : 1 ≤ n) :
    ∃ e : Work.Homology.ZMod ≅ Work.Homology.relHomology Work.Homology.ZMod n (simplex n)
      (simplexBoundary n), e.hom = simplexGenMap n :=
  ⟨simplexGenMapIso n hn, rfl⟩

/-- **The top relative homology of the standard simplex pair is `ℤ`, generated by `[ιₙ]`.** -/
theorem simplexPair_homology_top (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (Work.Homology.relHomology Work.Homology.ZMod n (simplex n)
      (simplexBoundary n) ≅ Work.Homology.ZMod) :=
  relHomology_simplexPair_top n hn

/-- **The homology of the standard simplex pair**: `H_k(Δⁿ, ∂Δⁿ; ℤ) ≅ ℤ` for `k = n` and `0`
otherwise (`n ≥ 1`).  In degree `n` the group is generated by the class of the identity singular
simplex (`isIso_simplexGenMap`). -/
theorem simplexPair_homology (n k : ℕ) (hn : 1 ≤ n) :
    Nonempty (Work.Homology.relHomology Work.Homology.ZMod k (simplex n) (simplexBoundary n) ≅
      (if k = n then Work.Homology.ZMod else ModuleCat.of ℤ PUnit)) :=
  relHomology_simplexPair n k hn

end

end Work.HomologyExtra
