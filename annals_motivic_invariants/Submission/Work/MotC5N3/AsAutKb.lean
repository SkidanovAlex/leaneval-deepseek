import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.TorsorExistence.ArtinSchreier.Irreducible
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Artin–Schreier automorphism `α ↦ α + 1` of the algebraic closure of `𝕜(t)`

Let `𝕜` be a field of characteristic `5`, `K = 𝕜(t) = K`, `K̄ = Work.MotC5N3.KbA K` an algebraic
closure of `K`, and `g ∈ K` a class which is **not** in the image of the Artin–Schreier map
`℘(u) = u⁵ - u` (the hypothesis `hg`).  Let `α = asRoot g ∈ K̄` be a root of `X⁵ - X - g`
(`asRoot_spec`).

The main result of this file, `asAut_Kb`, produces a `K`-algebra automorphism `σ` of `K̄` with
`σ α = α + 1`: the Artin–Schreier generator of the cyclic quintic extension `K(α)/K`, extended
to the algebraic closure.

The mathematical content is the standard Artin–Schreier package in characteristic `5`:

* `X⁵ - X - g` is irreducible over `K` as soon as `g ∉ ℘(K)`
  (`Work.TorsorExistence.ArtinSchreier.irreducible_X_pow_five_sub_X_sub_C`), so it is the
  minimal polynomial of `α` (`minpoly_asRoot`);
* Frobenius additivity `(α + 1)⁵ = α⁵ + 1` in characteristic `5` shows that `α + 1` is again a
  root (`asPolyK_aeval_root_add_one`), hence an `K`-embedding `K(α) → K̄` with `α ↦ α + 1`;
* the extension lemma for algebraically closed fields
  (`IntermediateField.exists_algHom_of_splits_of_aeval`) extends it to a `K`-endomorphism of
  `K̄`, which is bijective because `K̄/K` is algebraic
  (`Algebra.IsAlgebraic.algHom_bijective`).
-/

set_option linter.style.haveILetI false

namespace Work.MotC5N3
open Work.MotV5
open Polynomial

noncomputable section

/-! ## §1 The Artin–Schreier polynomial over `𝕜(t)` -/

/-- The Artin–Schreier polynomial `X ^ 5 - X - g` over `K`, that is, over the base
field `K = 𝕜(t)` (as opposed to `asPoly g`, which has coefficients in `Work.MotC5N3.KbA K`). -/
def asPolyK {K : Type} [Field K] (g : K) : (K)[X] :=
  X ^ 5 - X - C g

theorem asPolyK_monic {K : Type} [Field K] (g : K) : (asPolyK g).Monic := by
  rw [asPolyK]
  have h : (X ^ 5 - X - C g : (K)[X]) = (X ^ 5 - C g) - X := by ring
  rw [h]
  refine (monic_X_pow_sub_C g (by norm_num : (5 : ℕ) ≠ 0)).sub_of_left ?_
  have h5 : (X ^ 5 - C g : (K)[X]).degree = 5 := by
    rw [degree_X_pow_sub_C (by norm_num : 0 < 5)]
    norm_num
  rw [h5, degree_X]
  norm_num

/-- `X ^ 5 - X - g` is irreducible over `𝕜(t)` when `g` is not of the form `u ^ 5 - u`:
the Artin–Schreier irreducibility criterion in characteristic `5`. -/
theorem asPolyK_irreducible {K : Type} [Field K] [CharP K 5] (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) : Irreducible (asPolyK g) :=
  Work.TorsorExistence.ArtinSchreier.irreducible_X_pow_five_sub_X_sub_C g hg

/-- `asRoot g` is a root of `asPolyK g`. -/
theorem asPolyK_aeval_root {K : Type} [Field K] (g : K) :
    aeval (asRoot g) (asPolyK g) = 0 := by
  rw [asPolyK]
  simp only [map_sub, map_pow, aeval_X, aeval_C]
  rw [asRoot_spec g, sub_self]

/-- Frobenius in characteristic `5`: `α + 1` is again a root of `asPolyK g`, because
`(α + 1) ^ 5 - (α + 1) = α ^ 5 - α`. -/
theorem asPolyK_aeval_root_add_one {K : Type} [Field K] [CharP K 5] (g : K) :
    aeval (asRoot g + 1) (asPolyK g) = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [asPolyK]
  simp only [map_sub, map_pow, aeval_X, aeval_C]
  have h := asRoot_spec g
  have hc : (asRoot g + 1) ^ 5 = asRoot g ^ 5 + 1 := by
    rw [add_pow_char, one_pow]
  rw [hc]
  linear_combination (norm := first | refl_ring1 | ring1) h

/-- Under the pointless hypothesis `hg`, `X ^ 5 - X - g` **is** the minimal polynomial of
`asRoot g` over `K`. -/
theorem minpoly_asRoot {K : Type} [Field K] [CharP K 5] (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    minpoly (K) (asRoot g) = asPolyK g :=
  (minpoly.eq_of_irreducible_of_monic (asPolyK_irreducible g hg) (asPolyK_aeval_root g)
    (asPolyK_monic g)).symm

/-! ## §2 The automorphism -/

theorem asAut_Kb (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5] (g : K)
    (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    ∃ σ : Work.MotC5N3.KbA K ≃ₐ[K] Work.MotC5N3.KbA K,
      σ (Work.MotC5N3.asRoot g) = Work.MotC5N3.asRoot g + 1 := by
  -- `α + 1` is a root of the minimal polynomial of `α`
  have hy : aeval (asRoot g + 1) (minpoly (K) (asRoot g)) = 0 := by
    rw [minpoly_asRoot g hg]
    exact asPolyK_aeval_root_add_one g
  -- the resulting `K`-embedding `Work.MotC5N3.KbA K → Work.MotC5N3.KbA K` with `α ↦ α + 1`
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
    (F := K) (E := Work.MotC5N3.KbA K) (K := Work.MotC5N3.KbA K)
    (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) hy
  -- an endomorphism of an algebraic field extension is bijective
  exact ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ),
    by rw [AlgEquiv.ofBijective_apply]; exact hφ⟩

end

end Work.MotC5N3