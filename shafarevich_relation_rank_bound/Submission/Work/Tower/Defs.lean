import Mathlib
import Submission.Work.Defs.Basic

/-!
# Vocabulary for the class-field tower (paper Section 3)

This file fixes the shared vocabulary of the tower part of the proof that Erdős's
unit-distance conjecture is false (Section 3 of the paper).  It contains only definitions
(no proofs), so that the several subprojects of the tower construction can all speak about
the same objects.

## Main definitions

* `Work.Tower.IsUnramifiedExtension F L`: the finite extension `L/F` is unramified at every
  finite prime.
* `Work.Tower.SplitsCompletelyIn F L 𝔭`: the prime `𝔭` of `𝓞 F` splits completely in `L/F`.
* `Work.Tower.generatorRank G`: the minimal number of generators of a group `G`.
* `Work.Tower.relationRankWith G d`: the minimal number of relations among presentations of `G`
  with `d` generators.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Tower

/-- A finite extension `L/F` of number fields is **unramified at every finite prime** if every
prime `𝔓` of `𝓞 L` lying over a prime `𝔭` of `𝓞 F` has ramification index `1`.  (The
archimedean condition — that `L/F` is also unramified at infinity — is handled separately by
the total-realness hypotheses in the tower construction.) -/
def IsUnramifiedExtension (F L : Type*) [Field F] [Field L] [Algebra F L] : Prop :=
  ∀ (𝔓 : Ideal (𝓞 L)), 𝔓.IsPrime → ∀ (𝔭 : Ideal (𝓞 F)), 𝔓.LiesOver 𝔭 →
    Ideal.ramificationIdxIn 𝔭 (𝓞 L) = 1

/-- The prime `𝔭` of `𝓞 F` **splits completely** in the finite extension `L/F`: there are
exactly `[L : F]` primes of `𝓞 L` above `𝔭`, pairwise distinct, each with residue field
canonically isomorphic to `(𝓞 F) ⧸ 𝔭`. -/
def SplitsCompletelyIn (F L : Type*) [Field F] [Field L] [Algebra F L]
    (𝔭 : Ideal (𝓞 F)) : Prop :=
  ∃ 𝔔 : Fin (Module.finrank F L) → Ideal (𝓞 L),
    (∀ i, (𝔔 i).IsPrime) ∧ (∀ i, (𝔔 i).LiesOver 𝔭) ∧ Function.Injective 𝔔 ∧
    (∀ i, Nonempty ((𝓞 L) ⧸ 𝔔 i ≃+* (𝓞 F) ⧸ 𝔭))

/-- The **minimal number of generators** of a group `G`: the least `d` such that `G` is a quotient
of the free group on `d` generators.  For a finite `p`-group this is `dim G/Φ(G)`. -/
noncomputable def generatorRank (G : Type*) [Group G] : ℕ :=
  sInf {d : ℕ | ∃ φ : FreeGroup (Fin d) →* G, Function.Surjective φ}

/-- The **minimal number of relations** among presentations of `G` with `d` generators: the least
`r` such that `G` has a presentation with `d` generators and `r` relators. -/
noncomputable def relationRankWith (G : Type*) [Group G] (d : ℕ) : ℕ :=
  sInf {r : ℕ | ∃ φ : FreeGroup (Fin d) →* G, Function.Surjective φ ∧
      ∃ R : Fin r → FreeGroup (Fin d), φ.ker = Subgroup.normalClosure (Set.range R)}

end Tower
end Work
