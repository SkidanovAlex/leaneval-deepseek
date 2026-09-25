import Mathlib
import Submission.Work.HopfGaschutz.Defs
import Submission.Work.HopfGaschutz.Setup
import Submission.Work.HopfGaschutz.closedRelationData_of_spanningModulo
import Submission.Work.HopfGaschutz.cochainFactorization
import Submission.Work.HopfGaschutz.Profinite
import Submission.Work.RelatorRank.CohomologyH2

/-!
# `Work.HopfGaschutz.ClosedDictionary` -- the relation-rank dictionary in the *closed* (`p`-adic)
normalisation

**Namespace** `Work.HopfGaschutz`; module `Submission.Work.HopfGaschutz.ClosedDictionary`.

`README.md` §0/§3 explains that the *discrete* ("abstract free group") normalisation of the
relation-rank dictionary is equivalent to *efficiency* of finite `p`-groups, which is open.  This
module records the same dictionary in the **closed** normalisation, where it is the classical
*theorem* of Gaschütz (Koch, *Galois theory of `p`-extensions*, Ch. 11; Neukirch--Schmidt--Wingberg
I §4.3):

* `ClosedNormalGenerates p K S`: the finite-quotient encoding of "`S` generates `K` as a *closed*
  normal subgroup", i.e. every finite `p`-group quotient of `FreeGroup α` that kills `S` kills `K`
  (the closed normal closure of `S` is the intersection of the kernels of the finite `p`-quotients
  killing `S`).  This is `ClosedRelationData` of `Work.ShafarevichKoch.ProTwoClosed` at general `p`.
* `closedNormalGenerates_of_spanningModulo` (**proved**): the *engine* of the dictionary in this
  normalisation — a spanning statement modulo `K^p[K,F]` *at every finite `p`-quotient* produces a
  closed normal generating set.  Its proof is the finite engine of this chapter
  (`le_normalClosure_of_le_sup_relFrattini`) applied at each finite quotient; it needs no completed
  group algebra and no free pro-`p` group.
* `ProPHopfCohomologicalInput p d gen` (**the one classical input**, named): the identification
  `dim_{𝔽_p} H²_cont(Γ,𝔽_p) = dim_{𝔽_p} K ⧸ K^p[K,Γ]` for `K = ker (FreeGroup.lift gen)`, in the
  form that a bound `dim H² ≤ r` produces `r` elements spanning `K` modulo `K^p[K,F]` at every
  finite `p`-quotient.

Combining the two gives the closed dictionary: `dim_{𝔽_p} H²_cont(Γ,𝔽_p) ≤ r` implies that `Γ` has a
*closed* presentation on the given generators with `r` relators — the statement the arithmetic
chapters produce, and the classical theorem rather than the open efficiency question.  Passing from
there to the *discrete* presentation used by `Work.TameArithmetic.TamePro2Presentation` is the
additional residual-`p`-finiteness step (ShafarevichKoch's `hasProTwoPresentation_iff_closed`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.HopfGaschutz

variable {α : Type*} [Fintype α]

/-- **Closed normal generation, finite-quotient encoding.**  A finite `S ⊆ FreeGroup α` generates the
subgroup `K` as a *closed* normal subgroup iff every finite `p`-group quotient of `FreeGroup α` that
kills `S` kills `K` (the closed normal closure of `S` is the intersection of the kernels of the
finite `p`-quotients killing `S`).

This is the second clause of `Work.ShafarevichKoch.ClosedRelationData`, at a general prime `p`. -/
def ClosedNormalGenerates (p : ℕ) (K : Subgroup (FreeGroup α))
    (S : Finset (FreeGroup α)) : Prop :=
  ∀ (Q : Type*) [Group Q] [Fintype Q], IsPGroup p Q → ∀ φ : FreeGroup α →* Q,
    (∀ s ∈ S, φ s = 1) → K ≤ MonoidHom.ker φ

/-- **The engine of the closed dictionary.**  If a finite `S ⊆ FreeGroup α` spans a normal `K` modulo
`K^p[K,F]` at every finite `p`-group quotient (i.e. modulo the kernel of the quotient), then `S`
closed-normally generates `K`.

In particular the *natural* spanning condition `K ≤ ⟪S⟫ · K^p[K,F]` (no quotient kernel) implies the
hypothesis, so `K ≤ ⟪S⟫·K^p[K,F]` will never be enough to produce relations — but its *closed*
avatar, imposed at every finite quotient, does, because at each finite quotient the defect is a
finite `p`-group and the finite engine of this chapter applies. -/
theorem closedNormalGenerates_of_spanningModulo {p : ℕ} [Fact p.Prime]
    {K : Subgroup (FreeGroup α)} [K.Normal] {S : Finset (FreeGroup α)}
    (hspan : ∀ (Q : Type*) [Group Q] [Fintype Q], IsPGroup p Q → ∀ φ : FreeGroup α →* Q,
      K ≤ Subgroup.normalClosure (S : Set (FreeGroup α)) ⊔ relFrattini p K ⊔ MonoidHom.ker φ) :
    ClosedNormalGenerates p K S :=
  closedRelationData_of_spanningModulo hspan

/-- **The one classical input of the closed dictionary** (Gaschütz 1953; Koch Ch. 11;
Neukirch--Schmidt--Wingberg I §4.3): for a pro-`p` group `Γ` presented on the generating family
`gen : Fin d → Γ`, a bound `dim_{𝔽_p} H²_cont(Γ,𝔽_p) ≤ r` produces `r` elements of
`FreeGroup (Fin d)` whose images lie in the relation kernel `K = ker (FreeGroup.lift gen)` and which
span it modulo `K^p[K,F]` at every finite `p`-group quotient.

Stated in terms of `Work.RelatorRank.ContH2DimLe Γ r` (the finite-dimension form of
`dim_{𝔽_p} H²(Γ,𝔽_p) ≤ r`).  This is a *theorem* in the literature (not the open efficiency
question of `README.md` §3): it is the pro-`p` transgression
`H²_cont(Γ,𝔽_p) ≅ H¹_cont(K)^Γ/im(H¹_cont(F̂))` together with Nakayama for the compact
`𝔽_p[[Γ]]`-module `K ⧸ K^p[K,F]`. -/
def ProPHopfCohomologicalInput (p : ℕ) (d : ℕ) (Γ : Type*) [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] (gen : Fin d → Γ) : Prop :=
  ∀ r : ℕ, Work.RelatorRank.ContH2DimLe Γ r →
    ∃ S : Finset (FreeGroup (Fin d)), S.card ≤ r ∧
      (∀ s ∈ S, FreeGroup.lift gen s = 1) ∧
      (∀ (Q : Type*) [Group Q] [Fintype Q], IsPGroup p Q → ∀ φ : FreeGroup (Fin d) →* Q,
        MonoidHom.ker (FreeGroup.lift gen) ≤
          Subgroup.normalClosure (S : Set (FreeGroup (Fin d))) ⊔ relFrattini p (MonoidHom.ker (FreeGroup.lift gen))
            ⊔ MonoidHom.ker φ)

/-- **The closed relation-rank dictionary.**  From the classical cohomological input, a bound
`dim_{𝔽_p} H²_cont(Γ,𝔽_p) ≤ r` on a pro-`p` group with generating family `gen : Fin d → Γ` gives a
*closed* presentation of `Γ` on those `d` generators with `r` relators: there are `r` words in
`FreeGroup (Fin d)` that die in `Γ` and whose closed normal closure is the relation kernel.

This is the statement the arithmetic chapters produce (Salle/Shafarevich/Koch); the only input is
the classical `ProPHopfCohomologicalInput`. -/
theorem closedPresentation_of_contH2DimLe {p d r : ℕ} [Fact p.Prime] {Γ : Type*} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] (gen : Fin d → Γ)
    (h : ProPHopfCohomologicalInput p d Γ gen) (hr : Work.RelatorRank.ContH2DimLe Γ r) :
    ∃ S : Finset (FreeGroup (Fin d)), S.card ≤ r ∧
      (∀ s ∈ S, FreeGroup.lift gen s = 1) ∧
      ClosedNormalGenerates p (MonoidHom.ker (FreeGroup.lift gen)) S :=
  let ⟨S, hScard, himg, hspan⟩ := h r hr
  ⟨S, hScard, himg, closedNormalGenerates_of_spanningModulo hspan⟩

/-- **The first bridge of `Profinite.lean` is a theorem**, not merely a named `Prop`: for a compact,
Hausdorff, totally disconnected `Γ`, every locally constant `2`-cochain on `Γ × Γ` factors through
a finite quotient (`cochainFactorization`). -/
theorem cochainFactorization_holds (Γ : Type*) [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] :
    CochainFactorization Γ :=
  cochainFactorization Γ

end Work.HopfGaschutz
