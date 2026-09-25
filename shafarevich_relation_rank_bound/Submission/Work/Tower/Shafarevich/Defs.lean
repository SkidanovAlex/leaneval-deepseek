import Mathlib
import Submission.Work.Tower.Defs

/-!
# Shafarevich's relation-rank estimate: vocabulary

This file fixes the vocabulary for the area `Work.Tower.Shafarevich`, the formalisation of
Shafarevich's relation-rank estimate for the Galois group of the maximal everywhere-unramified
pro-`p` extension of a number field (paper Proposition 3.5 / A.10).

The two numerical invariants of a finitely generated (pro-)`p` group `G` that the estimate
compares are

* `d(G)`, the minimal number of generators, and
* `r(G)`, the minimal number of relations.

In this workspace these are `Work.Tower.generatorRank` and `Work.Tower.relationRankWith`
(defined in `Submission.Work.Tower.Defs`).  Cohomologically,
`d(G) = dim_{𝔽_p} H¹(G, 𝔽_p)` and `r(G) = dim_{𝔽_p} H²(G, 𝔽_p)`; the cohomology groups
`H¹`, `H²` with trivial `𝔽_p` coefficients are the ones this file names.

## Main definitions

* `Work.Tower.Shafarevich.H1Fp p G` — `H¹(G, 𝔽_p)` with trivial coefficients.
* `Work.Tower.Shafarevich.H2Fp p G` — `H²(G, 𝔽_p)` with trivial coefficients.
* `Work.Tower.Shafarevich.relationRank G` — `r(G)` for a minimal generating set.
* `Work.Tower.Shafarevich.IsFrobeniusTrivialInFrattini F T` — the hypothesis that every prime of
  `T` splits completely in every everywhere-unramified elementary abelian `3`-extension of `F`
  (equivalently, that the Frobenius classes of the primes of `T` lie in the Frattini subgroup of
  `Gal(F^{ur,3}/F)`).
* `Work.Tower.Shafarevich.IsMaximalSplittingExtension F K T` — `K` is maximal among
  everywhere-unramified Galois `3`-extensions of `F` in which every prime of `T` splits
  completely.
-/

open NumberField
open scoped Classical

namespace Work.Tower.Shafarevich

/-- `H¹(G, 𝔽_p)` with trivial coefficients, for `G` a group. -/
noncomputable abbrev H1Fp (p : ℕ) (G : Type) [Group G] : ModuleCat (ZMod p) :=
  groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 1

/-- `H²(G, 𝔽_p)` with trivial coefficients, for `G` a group. -/
noncomputable abbrev H2Fp (p : ℕ) (G : Type) [Group G] : ModuleCat (ZMod p) :=
  groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 2

/-- The **relation rank** `r(G)`: the minimal number of relations among presentations of `G`
with a minimal number of generators.  (Cohomologically `r(G) = dim_{𝔽_p} H²(G, 𝔽_p)` for a
finite `p`-group.) -/
noncomputable def relationRank (G : Type*) [Group G] : ℕ :=
  relationRankWith G (generatorRank G)

/-- The **Frattini (Frobenius-trivial) splitting condition** on a set `T` of primes of `F`: every
prime of `T` splits completely in every everywhere-unramified abelian extension of `F` whose
Galois group is killed by `3`.  Equivalently every Frobenius class at a prime of `T` lies in the
Frattini subgroup `Φ(Gal(F^{ur,3}/F))`. -/
def IsFrobeniusTrivialInFrattini (F : Type*) [Field F] [NumberField F]
    (T : Finset (Ideal (𝓞 F))) : Prop :=
  ∀ 𝔭 ∈ T, ∀ (L : Type) [Field L] [NumberField L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L],
    Work.Tower.IsUnramifiedExtension F L → IsAbelianGalois F L →
    (∀ σ : Gal(L/F), σ ^ 3 = 1) → Work.Tower.SplitsCompletelyIn F L 𝔭

/-- `K` is **maximal among everywhere-unramified Galois `3`-extensions of `F` in which every
prime of `T` splits completely**: every everywhere-unramified Galois `3`-extension `L/F` in
which every prime of `T` splits completely embeds `F`-linearly into `K`. -/
def IsMaximalSplittingExtension (F : Type*) [Field F] [NumberField F] (K : Type*) [Field K]
    [NumberField K] [Algebra F K] (T : Finset (Ideal (𝓞 F))) : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L],
    Work.Tower.IsUnramifiedExtension F L → IsPGroup 3 (Gal(L/F)) →
    (∀ 𝔭 ∈ T, Work.Tower.SplitsCompletelyIn F L 𝔭) →
    ∃ (_ : L →ₐ[F] K), True

end Work.Tower.Shafarevich

namespace Work.Tower.Shafarevich

/-- The **pro-`p` relation rank** of a group `G`: the `𝔽_p`-dimension of `H²(G, 𝔽_p)` with
trivial coefficients.  For a finite `p`-group this is the minimal number of relators in a *pro-`p`*
presentation (Serre; Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Prop. 3.9.5), and
it is the invariant that Shafarevich's relation-rank estimate bounds.

It is related to the abstract relation rank `Work.Tower.relationRankWith G (generatorRank G)` by

`proPRelationRank p G ≤ relationRankWith G (generatorRank G)`,

the difference being the *efficiency defect* of `G`; whether the defect always vanishes for finite
`p`-groups is Mann's Question 18 (Kourovka notebook), open.  See
`Work.Tower.Shafarevich.IsEfficient`. -/
noncomputable def proPRelationRank (p : ℕ) (G : Type) [Group G] : ℕ :=
  Module.finrank (ZMod p) (H2Fp p G)

/-- The **pro-`p` generator rank** `dim_{𝔽_p} H¹(G, 𝔽_p)` with trivial coefficients; for a finite
`p`-group it equals the abstract minimal number of generators `Work.Tower.generatorRank G`. -/
noncomputable def proPGeneratorRank (p : ℕ) (G : Type) [Group G] : ℕ :=
  Module.finrank (ZMod p) (H1Fp p G)

end Work.Tower.Shafarevich

namespace Work.Tower.Shafarevich

/-- A group `G` is **efficient** (in the sense of the theory of group presentations) if the
minimal number of relators in an abstract presentation on a minimal generating set equals its
pro-`p` relation rank `dim_{𝔽_p} H²(G, 𝔽_p)`.

For finite `p`-groups one always has `proPRelationRank p G ≤ relationRankWith G (generatorRank G)`
(`Work.Tower.Shafarevich.finrank_H2Fp_le_relationRankWith`); whether equality always holds is
Mann's Question 18 (Kourovka notebook), open — there is no known example of a non-efficient finite
`p`-group.  This is precisely the gap that separates Shafarevich's estimate (a bound on
`proPRelationRank`) from the deliverable `Work.Tower.shafarevich_relation_bound` (a bound on
`relationRankWith`). -/
def IsEfficient (p : ℕ) (G : Type) [Group G] : Prop :=
  Work.Tower.relationRankWith G (Work.Tower.generatorRank G) = proPRelationRank p G

end Work.Tower.Shafarevich
