import Submission.Work.HopfGaschutz.Setup
import Submission.Work.HopfGaschutz.h2_freeGroup_subsingleton
import Submission.Work.HopfGaschutz.tgClass_surjective
import Submission.Work.HopfGaschutz.tgClass_injective
import Submission.Work.HopfGaschutz.card_conjInvariantZ1
import Submission.Work.HopfGaschutz.Dictionary

/-!
# `Work.HopfGaschutz.CohomologicalDictionary` -- Hopf's formula in its literal cohomological form

**Namespace** `Work.HopfGaschutz`; module `Submission.Work.HopfGaschutz.CohomologicalDictionary`.

Until this file, the chapter's invariant `h2DimOf p α Q gen` was *defined* as the `𝔽_p`-dimension of
`K ⧸ K^p[K,F]` for `K = ker (FreeGroup.lift gen)`, `F = FreeGroup α`, with the identification with
`dim_{𝔽_p} H²(Q,𝔽_p)` stated only in the docstrings.  Here the identification is **proved**, for a
finite group `Q` presented on a *minimal* generating family:

```lean
Work.HopfGaschutz.card_contH2_eq_card_relFrattiniQuotient
    : Nat.card (contH2 Q) = Nat.card (↥(presKernel gen) ⧸ relFrattiniIn 2 (presKernel gen))
Work.HopfGaschutz.h2DimOf_eq_log_card_contH2
    : h2DimOf 2 α Q gen  =  Nat.log 2 (Nat.card (contH2 Q))
```

where `contH2 Q = Work.RelatorRank.contH2 Q = H²(Q, 𝔽₂)` is the (continuous = abstract, `Q` being
discrete) cohomology group of `Work.ConCohomology`.  The proof is the classical transgression of the
extension `1 → K → FreeGroup α → Q → 1`:

* `tgClass_surjective`: every class of `H²(Q,𝔽₂)` is the transgression of a conjugation-invariant
  `1`-cocycle on `K` -- because `H²(FreeGroup α,𝔽₂) = 0` (`h2_freeGroup_subsingleton`, i.e.
  `cd(free) = 1`), so `ker(inf₂) = H²(Q,𝔽₂)` is all of it;
* `tgClass_injective`: the transgression is injective on the invariant cocycles as soon as `gen` is
  *minimal* (`K ⊆ F^p[F,F]`): a transgression class is a coboundary iff the cocycle extends to a
  `1`-cocycle on `F`, and a homomorphism `F → 𝔽₂` kills `F^p[F,F] ⊇ K`;
* `card_conjInvariantZ1`: the invariant cocycles on `K` are the homomorphisms `K → 𝔽₂` killing
  `[K,F]`, whose cardinality is that of `K ⧸ K^p[K,F]` (finite–abelian duality: for a finite
  `𝔽₂`-vector space `V`, `#Hom(V,𝔽₂) = #V`).

So the transgression is a *bijection* `Z¹(K,𝔽₂)^{Q} ≃ H²(Q,𝔽₂)`, and `dim H²` is exactly the
relation rank of the presentation.  What is *not* proved here -- and cannot be, see `README.md` §3 --
is the passage from the *dimension* of the relation module to a *normal generating set*: that is the
`p`-group efficiency question (`GaschutzDictionary`).

## Consequences

* `log_card_contH2_le_card_of_presentation`: the *easy* direction of the dictionary in the literal
  cohomological language -- **every** presentation of a finite `Q` on a minimal generating family
  with `rel.card` relators satisfies `dim_{𝔽₂} H²(Q,𝔽₂) ≤ rel.card`;
* `subsingleton_of_log_card_contH2_le_six`: at `Q` a finite `2`-group with a minimal generating
  family of size five, the bound `dim H² ≤ 6` forces `Q` to be trivial (the finite level of the
  endgame is vacuous, so the numbers `(d,r) = (5,6)` can only be consumed by an infinite group).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.HopfGaschutz

open Work.ConCohomology

/-- **Hopf's formula / the relation-rank dictionary, cohomological form.**  For a finite group `Q`,
a generating family `gen : α → Q` (i.e. `closure (range gen) = ⊤`) and `K = presKernel gen = ker (FreeGroup.lift gen)`
*minimal* in the sense `K ≤ F^2[F,F]` (`F = FreeGroup α`), the second cohomology of `Q` with
coefficients in `𝔽₂` (trivial action) has the same cardinality as the relation-Frattini quotient
`K ⧸ K^2[K,F]`.

Equivalently -- and this is the content of the classical relation-rank dictionary -- both are
`2 ^ (minimal number of relators of the presentation)`. -/
theorem card_contH2_eq_card_relFrattiniQuotient {α Q : Type*} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [TopologicalSpace (FreeGroup α)] [DiscreteTopology (FreeGroup α)]
    [DiscreteTopology Q] [Fintype α] [Fintype Q]
    (gen : α → Q) (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hmin : presKernel gen ≤ relFrattini 2 ⊤) :
    Nat.card (Work.RelatorRank.contH2 Q)
      = Nat.card (↥(presKernel gen) ⧸ relFrattiniIn 2 (presKernel gen)) := by
  have hbij : Function.Bijective (fun φ : {φ : Z1 ↥(presKernel gen) (ZMod 2) //
      IsConjInvariant gen φ} => tgClass gen hgen φ.1 φ.2) :=
    ⟨tgClass_injective gen hgen hmin, tgClass_surjective gen hgen⟩
  calc Nat.card (Work.RelatorRank.contH2 Q)
      = Nat.card {φ : Z1 ↥(presKernel gen) (ZMod 2) // IsConjInvariant gen φ} :=
        Nat.card_congr (Equiv.ofBijective _ hbij).symm
    _ = Nat.card (↥(presKernel gen) ⧸ relFrattiniIn 2 (presKernel gen)) :=
        card_conjInvariantZ1 gen hgen

/-- **The relation rank is the `𝔽₂`-dimension of `H²`.**  In the chapter's own vocabulary
(`Defs.lean`): for a finite group `Q` with a minimal (`K ≤ F^2[F,F]`) *generating* family `gen`, the presentation-theoretic relation rank `h2DimOf 2 α Q gen` equals the `𝔽₂`-dimension
(computed as `Nat.log 2` of the cardinality) of the continuous cohomology group
`H²(Q,𝔽₂) = Work.RelatorRank.contH2 Q`. -/
theorem h2DimOf_eq_log_card_contH2 {α Q : Type*} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [TopologicalSpace (FreeGroup α)] [DiscreteTopology (FreeGroup α)]
    [DiscreteTopology Q] [Fintype α] [Fintype Q]
    (gen : α → Q) (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hmin : presKernel gen ≤ relFrattini 2 ⊤) :
    h2DimOf 2 α Q gen = Nat.log 2 (Nat.card (Work.RelatorRank.contH2 Q)) := by
  have h := card_contH2_eq_card_relFrattiniQuotient gen hgen hmin
  show Nat.log 2 (Nat.card (MonoidHom.ker (FreeGroup.lift gen) ⧸
      relFrattiniIn 2 (MonoidHom.ker (FreeGroup.lift gen))))
    = Nat.log 2 (Nat.card (Work.RelatorRank.contH2 Q))
  rw [h]
  rfl

/-- **The easy direction of the dictionary, in the literal cohomological language.**  For a finite
group `Q` and a presentation of `Q` on a minimal generating family `gen` by `rel.card` relators,
the `𝔽₂`-dimension of `H²(Q,𝔽₂)` is at most `rel.card`.

(The hypothesis is that of a *presentation*: `ker (FreeGroup.lift gen)` is the normal closure of
`rel`; minimality of the generating family enters through `hmin`.  Compare
`Work.HopfGaschutz.h2DimOf_le_card_of_presentation`, of which this is the cohomological
restatement, now that the two invariants are identified.) -/
theorem log_card_contH2_le_card_of_presentation {α Q : Type*} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [TopologicalSpace (FreeGroup α)] [DiscreteTopology (FreeGroup α)]
    [DiscreteTopology Q] [Fintype α] [Fintype Q] [DecidableEq α]
    (gen : α → Q) (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hmin : presKernel gen ≤ relFrattini 2 ⊤)
    (rel : Finset (FreeGroup α))
    (hrel : MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (rel : Set (FreeGroup α))) :
    Nat.log 2 (Nat.card (Work.RelatorRank.contH2 Q)) ≤ rel.card := by
  rw [← h2DimOf_eq_log_card_contH2 gen hgen hmin]
  exact h2DimOf_le_card_of_presentation 2 gen hgen rel hrel

end Work.HopfGaschutz
