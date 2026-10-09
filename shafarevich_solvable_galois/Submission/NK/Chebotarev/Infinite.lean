/-
Work of the Neukirch–Uchida team: the Čebotarev density theorem.
-/
import Submission.NK.Chebotarev.Density
import Mathlib.FieldTheory.KrullTopology
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Čebotarev at the finite levels of an infinite Galois extension

Let `K' / K` be a Galois extension of number fields (possibly infinite) and `L / K` a finite Galois
subextension.  For every `σ : Gal(K'/K)`, the restriction `σ|_L` is a Frobenius element at the
primes of a set of Dirichlet density `1/[L : K]` (for abelian `L/K`; in general the density is
`|C|/[L:K]` for `C` the conjugacy class of `σ|_L`).  This is the form in which Čebotarev is used
for infinite extensions: the "Frobenius distribution" is that of the finite quotient `Gal(L/K)`,
and `σ ∈ Gal(K'/K)` selects the conjugacy class through its restriction.

The file also records the topological determinacy principle: a continuous homomorphism of
topological groups is determined by its values on a dense subset, which is how the density of the
Frobenius elements is consumed in the Neukirch–Uchida endgame.
-/

set_option linter.unusedSectionVars false

namespace NK.Chebotarev

open Filter IsDedekindDomain

/-- **Determinacy on a dense subset.**  Two continuous monoid homomorphisms into a Hausdorff
topological group which agree on a dense set are equal. -/
theorem MulEquiv_eq_of_eqOn_dense {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] [T2Space G] (φ ψ : H →* G) (hφ : Continuous φ) (hψ : Continuous ψ)
    {S : Set H} (hS : Dense S) (h : ∀ s ∈ S, φ s = ψ s) : φ = ψ :=
  MonoidHom.ext fun x =>
    congrFun (Continuous.ext_on hS hφ hψ fun s hs => h s hs) x

/-- **Čebotarev at a finite level of an infinite Galois extension.**  Let `K'/K` be Galois,
`L/K` a finite Galois subextension, and assume Čebotarev for `L/K` (the hypothesis `hC`).  Then for
every `σ : Gal(K'/K)`, the primes of `K` whose Frobenius in `L/K` is the restriction `σ|_L` have
Dirichlet density `1/[L:K]`. -/
theorem FiniteLevelFrobDensity {K K' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsGalois K K']
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    (hC : ∀ σ : Gal(↥L/K), NumberField.Set.HasDirichletDensity
      {p : PrimeIdeal K | IsFrobAtPrime (K := K) (L := ↥L) p σ}
      (1 / (Module.finrank K ↥L : ℝ)))
    (σ : Gal(K'/K)) :
    NumberField.Set.HasDirichletDensity
      {p : PrimeIdeal K |
        IsFrobAtPrime (K := K) (L := ↥L) p (AlgEquiv.restrictNormalHom L σ)}
      (1 / (Module.finrank K ↥L : ℝ)) :=
  hC _

end NK.Chebotarev
