import Mathlib
import Submission.Work.RelatorRank.CohomologyH2
import Submission.Work.HopfGaschutz.ClosedDictionary
import Submission.Work.ClassFieldTower.ProTwoDefs

/-!
# `Work.AbstractDictionary` -- the abstract/closed seam of the relation-rank dictionary

**Namespace** `Work.AbstractDictionary`; module `Submission.Work.AbstractDictionary.Defs`.

This area is the second and last input of the assembled endgame
`Work.TameRelation.tameRelationBound` (the `sorry` at `Submission.lean:89`): the **relation-rank
dictionary** `RelatorRank.GaschutzCohomologicalValue (K ≃ₐ[ℚ] K)` for a maximal tame pro-`2`
extension `K` of `ℚ`.

The bookkeeping of that dictionary -- generator rank `5`, the presentation vocabulary, the Sha
bound -- is all in the neighbouring areas (`Work.RelatorRank`, `Work.HopfGaschutz`,
`Work.TameArithmetic`, `Work.TameSalle`, `Work.ShaAssembly`).  What is *not* there, and what this
area supplies, is the honest reduction of

  `∀ r, RelatorRankLe Γ r ↔ ContH2DimLe Γ r`   (`Γ = Gal(K/ℚ)`)

to (a) **one** named classical theorem of pro-`2` group theory and (b) **one** named residual
finiteness side condition.  Both faces of the seam are isolated here, with docstrings, and
everything connecting them is proved.

## The two normalisations

The workspace's `RelatorRank.HasProP2Presentation Γ d r` asks for a *dense* generating family
`gen : Fin d → Γ` and a finite relator set `rel ⊆ FreeGroup (Fin d)` with

  `ker (FreeGroup.lift gen) = ⟪rel⟫`

-- the **abstract** normal closure, in the discrete free group on the generators.  The classical
Gaschütz/Koch/Shafarevich--Koch theorem produces only the **closed** (pro-`2`) statement

  `ClosedNormalGenerates 2 (ker (FreeGroup.lift gen)) S`,

i.e. every finite `2`-group quotient of `FreeGroup (Fin d)` that kills `S` kills the whole kernel
(`Work.HopfGaschutz.ClosedDictionary`; this is `ClosedRelationData` of
`Work.ShafarevichKoch.ProTwoClosed`).  The passage closed ⟹ abstract is **not** a formality: for
`Γ = ℤ/2`, `gen` the generator and `S = {x⁶}` one has `⟪S⟫ = 6ℤ ⊊ 2ℤ = ker` while the closed
condition *does* hold (`Work.HopfGaschutz.Counterexample`, `Submission/PLAN.md` §31 item 4).  What
the passage needs is residual `2`-finiteness of the presented abstract group
(`Work.ShafarevichKoch.ker_eq_normalClosure_of_closed`), and `Work.AbstractDictionary.Seam` proves
that, in this setting, residual `2`-finiteness is *equivalent* to the abstract kernel equality
itself.

## Contents of this file

* `GaschutzProP2Value d gen` -- **the classical input**, the Gaschütz value theorem for pro-`2`
  groups in the closed normalisation, for the generating family `gen`:
  `dim_{𝔽₂} H²(Γ,𝔽₂) ≤ r` iff the relation kernel has `≤ r` closed normal generators on `gen`.
  It is equivalent to the conjunction of `Work.HopfGaschutz.ProPHopfCohomologicalInput` (the
  workspace's existing named input, its `⟸`-half) with `ProPHopfCohomologicalBound` (its `⟹`-half)
  -- see `Work.AbstractDictionary.ClosedEquiv`.
* `ProPHopfCohomologicalBound d gen` -- the second half alone, named separately so that the
  relationship with the workspace's existing input is explicit.
* `ResidualTwoFinitenessPresentations Γ` -- **the residual finiteness side condition**, isolated as
  one named `Prop`: for every dense generating family and every relator set satisfying the closed
  condition, the presented abstract group is residually a finite `2`-group.  This is exactly the
  hypothesis of `Work.ShafarevichKoch.ker_eq_normalClosure_of_closed`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.dupNamespace false

open scoped Classical

namespace Work.AbstractDictionary

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-! ## A universe-pinned name for the closed normal generation predicate -/

/-- `Work.HopfGaschutz.ClosedNormalGenerates` at the prime `2`, with the auxiliary finite
`2`-group pinned to universe `0`.  Every finite group is isomorphic to one carried by a type in
`Type 0`, and this is the shape in which the *closed* relation condition is consumed by
`Work.ShafarevichKoch.ker_eq_normalClosure_of_closed`; pinning the universe keeps the statements of
this area free of universe metavariables. -/
abbrev ClosedNormalGeneratesTwo {α : Type} (K : Subgroup (FreeGroup α))
    (S : Finset (FreeGroup α)) : Prop :=
  Work.HopfGaschutz.ClosedNormalGenerates.{0, 0} 2 K S

/-! ## The two named inputs -/

/-- **The classical Gaschütz value theorem for pro-`2` groups** (Gaschütz 1953; Koch, *Galois
theory of `p`-extensions*, Ch. 11; Neukirch--Schmidt--Wingberg I §4.3), in the *closed* (pro-`2`)
normalisation, stated for a fixed dense generating family `gen : Fin d → Γ`:

> `dim_{𝔽₂} H²_cont(Γ, 𝔽₂) ≤ r` if and only if the relation kernel `ker (FreeGroup.lift gen)` is
> generated, as a **closed** normal subgroup of the free *pro-`2* group on `d` generators, by at
> most `r` elements.

Both halves are classical:

* `⟸` (`ProPHopfCohomologicalBound`): a closed presentation with `r` relators bounds
  `dim_{𝔽₂} H²` by `r` -- the pro-`2` five-term sequence for `1 → K → F̂_d → Γ → 1` together with
  `H²_cont(F̂_d) = 0` and the fact that a continuous `Γ`-equivariant functional on `K` is
  determined by its values on the (finitely many) relators.
* `⟹` (`Work.HopfGaschutz.ProPHopfCohomologicalInput`): Gaschütz's theorem proper -- the
  transgression `H²_cont(Γ,𝔽₂) ≅ H¹_cont(K,𝔽₂)^Γ/im` together with Nakayama for the compact module
  `K ⧸ K^2[K,Γ]` over `𝔽₂[[Γ]]`.

The statement is *not* the open efficiency question of `Work.HopfGaschutz.GaschutzDictionary`
(`Submission/PLAN.md` §30): there the kernels are abstract normal subgroups of the *discrete* free
group, where the pro-`2` Frattini/Nakayama step is unavailable
(`Work.HopfGaschutz.Counterexample.naive_engine_fails`). -/
def GaschutzProP2Value (d : ℕ) (gen : Fin d → Γ) : Prop :=
  ∀ r : ℕ, Work.RelatorRank.ContH2DimLe Γ r ↔
    ∃ S : Finset (FreeGroup (Fin d)), S.card ≤ r ∧
      (∀ s ∈ S, FreeGroup.lift gen s = 1) ∧
      ClosedNormalGeneratesTwo (MonoidHom.ker (FreeGroup.lift gen)) S

/-- **The easy half of the closed Gaschütz value theorem**: a closed presentation of `Γ` on the
generating family `gen` with at most `r` relators bounds `dim_{𝔽₂} H²_cont(Γ,𝔽₂)` by `r`.

This is the other half of `GaschutzProP2Value`; it is the pro-`2` analogue of the workspace's
*finiteness-level* easy direction `Work.HopfGaschutz.h2DimOf_le_card_of_presentation`, and the
`⟹`-direction of `GaschutzProP2Value`. -/
def ProPHopfCohomologicalBound (d : ℕ) (gen : Fin d → Γ) : Prop :=
  ∀ r : ℕ, (∃ S : Finset (FreeGroup (Fin d)), S.card ≤ r ∧
      (∀ s ∈ S, FreeGroup.lift gen s = 1) ∧
      ClosedNormalGeneratesTwo (MonoidHom.ker (FreeGroup.lift gen)) S) →
    Work.RelatorRank.ContH2DimLe Γ r

/-- **The residual finiteness side condition, isolated as one named `Prop`.**

For every dense generating family `gen : Fin d → Γ` of a pro-`2` group and every finite relator set
`S` whose elements die in `Γ` and whose *closed* normal closure is the relation kernel
(`Work.HopfGaschutz.ClosedNormalGenerates 2 (ker (FreeGroup.lift gen)) S`), the abstract group

  `FreeGroup (Fin d) ⧸ Subgroup.normalClosure (S : Set (FreeGroup (Fin d)))`

presented by `S` is **residually a finite `2`-group**.

This is *exactly* the hypothesis of `Work.ShafarevichKoch.ker_eq_normalClosure_of_closed`
(`Work.ClassFieldTower.ResiduallyFiniteTwoGroup`), i.e. the extra input that turns a closed
presentation into an abstract one.  It is not a formality: the passage closed ⟹ abstract fails
without it (`ℤ/2`, `S = {x⁶}`; `Work.HopfGaschutz.Counterexample`), and
`Work.AbstractDictionary.Seam` proves that in this setting it is *equivalent* to the abstract kernel
equality `ker (FreeGroup.lift gen) = ⟪S⟫` itself -- so what this `Prop` isolates is precisely the
seam between the two normalisations, no more and no less.  It is plausibly provable from the
maximality of the arithmetic extension `K` (the Galois group `Γ = Gal(K/ℚ)` is residually a finite
`2`-group, `Work.TameArithmetic.residuallyFiniteTwoGroup_galoisGroup_tame`), but that implication is
*not* established here. -/
def ResidualTwoFinitenessPresentations : Prop :=
  ∀ (d : ℕ) (gen : Fin d → Γ) (S : Finset (FreeGroup (Fin d))),
    Work.RelatorRank.DenseGenerating gen →
    (∀ s ∈ S, FreeGroup.lift gen s = 1) →
    ClosedNormalGeneratesTwo (MonoidHom.ker (FreeGroup.lift gen)) S →
    Work.ClassFieldTower.ResiduallyFiniteTwoGroup
      (FreeGroup (Fin d) ⧸ Subgroup.normalClosure (S : Set (FreeGroup (Fin d))))

/-! ## Elementary API of the named inputs -/

/-- The `⟹`-half of `GaschutzProP2Value`, unpacked. -/
theorem GaschutzProP2Value.exists_closedRelators {d : ℕ} {gen : Fin d → Γ}
    (h : GaschutzProP2Value d gen) {r : ℕ} (hr : Work.RelatorRank.ContH2DimLe Γ r) :
    ∃ S : Finset (FreeGroup (Fin d)), S.card ≤ r ∧
      (∀ s ∈ S, FreeGroup.lift gen s = 1) ∧
      ClosedNormalGeneratesTwo (MonoidHom.ker (FreeGroup.lift gen)) S :=
  (h r).mp hr

/-- The `⟸`-half of `GaschutzProP2Value`, unpacked. -/
theorem GaschutzProP2Value.contH2DimLe {d : ℕ} {gen : Fin d → Γ}
    (h : GaschutzProP2Value d gen) {r : ℕ}
    (hS : ∃ S : Finset (FreeGroup (Fin d)), S.card ≤ r ∧
      (∀ s ∈ S, FreeGroup.lift gen s = 1) ∧
      ClosedNormalGeneratesTwo (MonoidHom.ker (FreeGroup.lift gen)) S) :
    Work.RelatorRank.ContH2DimLe Γ r :=
  (h r).mpr hS

/-- `GaschutzProP2Value` is monotone in the conclusion, in the shape in which it is consumed: a
cohomological bound at `r` gives one at every `r' ≥ r`. -/
theorem GaschutzProP2Value.contH2DimLe_mono {d : ℕ} {gen : Fin d → Γ}
    (h : GaschutzProP2Value d gen) {r r' : ℕ}
    (hS : ∃ S : Finset (FreeGroup (Fin d)), S.card ≤ r ∧
      (∀ s ∈ S, FreeGroup.lift gen s = 1) ∧
      ClosedNormalGeneratesTwo (MonoidHom.ker (FreeGroup.lift gen)) S)
    (hr : r ≤ r') : Work.RelatorRank.ContH2DimLe Γ r' :=
  (h.contH2DimLe hS).mono hr

/-- `ResidualTwoFinitenessPresentations` at a concrete generating family and relator set. -/
theorem ResidualTwoFinitenessPresentations.presented
    (h : ResidualTwoFinitenessPresentations (Γ := Γ)) {d : ℕ} {gen : Fin d → Γ}
    {S : Finset (FreeGroup (Fin d))}
    (hgen : Work.RelatorRank.DenseGenerating gen)
    (hS : ∀ s ∈ S, FreeGroup.lift gen s = 1)
    (hclosed : ClosedNormalGeneratesTwo (MonoidHom.ker (FreeGroup.lift gen)) S) :
    Work.ClassFieldTower.ResiduallyFiniteTwoGroup
      (FreeGroup (Fin d) ⧸ Subgroup.normalClosure (S : Set (FreeGroup (Fin d)))) :=
  h d gen S hgen hS hclosed

end Work.AbstractDictionary
