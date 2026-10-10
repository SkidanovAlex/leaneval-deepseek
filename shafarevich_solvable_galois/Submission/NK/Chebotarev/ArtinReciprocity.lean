import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Submission.NK.Chebotarev.HasDirichletDensityFrobClassOfCharacterData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Artin-reciprocity input of Čebotarev, as an explicit structure

The classical proof of Čebotarev's density theorem for a finite Galois extension `L/K` of number
fields proceeds from

* **artin reciprocity**: the Artin map is an isomorphism `C_K / N(C_L) ≅ Gal(L/K)` from a quotient
  of the ray class group of `K`, compatible with the local Frobenius at almost all primes (`C_K` is
  the idèle class group and `N(C_L)` the norm group of `L`); and
* **the analytic theory of Hecke `L`-functions**: the `L`-function of every non-trivial character
  of a ray class group is holomorphic and non-zero at `s = 1`.

Neither of these is available in the library, so the *consequences* that Čebotarev consumes are
packaged in the structure `NK.Chebotarev.ArtinReciprocityInput`.  Concretely, the Artin
isomorphism turns the characters of `Gal(L/K)` into characters of a ray class group, giving a
family of class functions `χ i` with the orthogonality relations of a character table (which is
where "the reduction from class functions to characters" enters), and the analytic input gives the
boundedness of the character-twisted prime sums, which is the Euler-product form of the
non-vanishing of the Hecke `L`-functions at `s = 1`.

From that structure the full density statement for a conjugacy class follows, unconditionally:
`NK.Chebotarev.hasDirichletDensity_frobClass_of_artinReciprocity`.
-/

set_option linter.unusedSectionVars false

namespace NK.Chebotarev

open Filter IsDedekindDomain Asymptotics
open scoped BigOperators

/-- **The Artin-reciprocity input for `L/K`.**  It records the character table of the Galois group
(as produced by the Artin isomorphism `C_K/N(C_L) ≅ Gal(L/K)`) together with the Hecke `L`-function
bounds for its non-trivial members. -/
structure ArtinReciprocityInput (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] where
  /-- the index set of the characters -/
  ι : Type
  [fintype : Fintype ι]
  /-- the index of the trivial character -/
  i₀ : ι
  /-- the characters, as class functions on the Galois group -/
  χ : ι → Gal(L/K) → ℂ
  /-- every `χ i` is a class function -/
  χ_class : ∀ (i : ι) (g h : Gal(L/K)), χ i (h⁻¹ * g * h) = χ i g
  /-- `i₀` is the trivial character -/
  χ_trivial : ∀ g : Gal(L/K), χ i₀ g = 1
  /-- the second orthogonality relation, off the diagonal -/
  orth_off : ∀ g h : Gal(L/K), ¬ IsConj g h → ∑ i, χ i g * star (χ i h) = 0
  /-- the second orthogonality relation on the diagonal -/
  orth_norm : ∀ g : Gal(L/K), ∑ i, χ i g * star (χ i g) =
    (Nat.card (Subgroup.centralizer ({g} : Set (Gal(L/K)))) : ℂ)
  /-- the Hecke `L`-function bound for the non-trivial characters -/
  bounded : ∀ i : ι, i ≠ i₀ → (fun s : ℝ =>
      ∑' p : PrimeIdeal K,
        star (χ i (frobAtPrime (K := K) (L := L) p)) *
          (((Ideal.absNorm p.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ))

/-- **Čebotarev's density theorem from Artin reciprocity and the Hecke `L`-function bounds.**
For every `g₀ : Gal(L/K)`, the set of primes of `K` whose Frobenius is conjugate to `g₀` has
Dirichlet density `|Cl(g₀)| / |Gal(L/K)|`. -/
theorem hasDirichletDensity_frobClass_of_artinReciprocity {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (h : ArtinReciprocityInput K L) (g₀ : Gal(L/K)) :
    NumberField.Set.HasDirichletDensity
      {p : PrimeIdeal K | IsConj (frobAtPrime (K := K) (L := L) p) g₀}
      ((Nat.card {x : Gal(L/K) // IsConj x g₀} : ℝ) / (Nat.card (Gal(L/K)) : ℝ)) := by
  letI := h.fintype
  exact HasDirichletDensityFrobClassOfCharacterData h.χ h.i₀ h.χ_class h.χ_trivial
    h.orth_off h.orth_norm h.bounded g₀

end NK.Chebotarev
