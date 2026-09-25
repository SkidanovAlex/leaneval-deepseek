import Mathlib
import Submission.Work.HopfGaschutz.All
import Submission.Work.RelatorRank.CohomologyH2
import Submission.Work.ProPDeficiency.Basic

/-!
# `Work.ProPGS` -- the Golod--Shafarevich theorem in its pro-`p` / cohomological form

**Namespace** `Work.ProPGS`; module `Submission.Work.ProPGS.Defs`.

This is the area requested by `fundmath3-martinet_totally_real_towers`.  It supplies the
*pro-`p`* Golod--Shafarevich inequality -- pure group theory, no number theory --

> a finite `p`-group `Q` with a **minimal** generating family of size `d` satisfies
> `4 · dim_{𝔽_p} H²(Q,𝔽_p) > d²`

in the form the endgame of `Submission.exists_totallyReal_discr_le` consumes, i.e.

* `Work.ProPGS.subsingleton_of_card_contH2_le_sixtyfour` -- no nontrivial finite `2`-group has
  five minimal generators and `#H²(·,𝔽₂) ≤ 64`, so the arithmetic bound `dim_{𝔽₂} H²(Γ,𝔽₂) ≤ 6`
  on the maximal tame pro-`2` group forces `Γ` to be infinite;
* `Work.ProPGS.four_mul_dim_contH2_lt_card_sq` -- the general inequality.

## Why the *pro-`p`* form is a theorem while the *discrete* form is not

For a finite `p`-group the number `dim_{𝔽_p} H²(Q,𝔽_p)` is realised as a **pro-`p`** relation rank:
the kernel of a continuous surjection `F̂_d ↠ Q` (the free pro-`p` group) is generated as a *closed
normal* subgroup by exactly `dim_{𝔽_p} H²(Q,𝔽_p)` elements, and there is **no efficiency gap** in the
pro-`p` category -- Nakayama over `𝔽_p[[Q]]` closes it.  This is why `4 · dim H² > d²` holds.

The temptation is to prove the same inequality from the *discrete* free group: the kernel
`K = ker (FreeGroup (Fin d) → Q)` satisfies `#(K ⧸ K^p[K,F]) = #H²(Q,𝔽_p)`, and if one could find
`K ⧸ K^p[K,F]`-many relators whose *normal closure* is `K` one would be done.  That last step is
exactly *efficiency* of finite `p`-groups (Mann's Question 18, Gardam arXiv:1705.02040), which is
**open**; `Work.HopfGaschutz.gaschutzDictionary_iff_minimalRelatorSet` records the equivalence and
`Work.ProPGS.gaschutzDictionary_two_implies_proPGolodShafarevich` below records that the open
statement is *strictly stronger* than the theorem of this chapter.  Nothing in this directory
assumes it.

## Vocabulary

* `IsMinimalGeneratingFamily gen` -- `gen` generates and cannot be thinned;
* `ProPGolodShafarevich p` -- the inequality, in the `h2DimOf` language of
  `Work.HopfGaschutz` (which is `dim_{𝔽_p} H²` for a minimal generating family of a finite
  `p`-group, by the transgression theorem
  `Work.HopfGaschutz.h2DimOf_eq_log_card_contH2`).

Everything is stated with the arithmetic side's vocabulary: `Work.RelatorRank.contH2` is the
continuous cohomology `H²(Γ,𝔽₂)`, and for a finite group with the discrete topology it is ordinary
group cohomology.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Work.ProPGS

open Work.HopfGaschutz

/-- **A minimal generating family.**  `gen : α → Q` generates `Q`, and no `Finset` of *fewer* than
`Fintype.card α` elements generates `Q`; i.e. `Fintype.card α = d(Q)`.

The minimality is essential: without it the Golod--Shafarevich inequality is false, see
`Work.ProPGS.not_minimal_generating_family_gs_fails`. -/
def IsMinimalGeneratingFamily {α : Type*} [Fintype α] {Q : Type*} [Group Q]
    (gen : α → Q) : Prop :=
  Subgroup.closure (Set.range gen) = ⊤ ∧
    ∀ S : Finset Q, Subgroup.closure (S : Set Q) = ⊤ → Fintype.card α ≤ S.card

theorem isMinimalGeneratingFamily_iff {α : Type*} [Fintype α] {Q : Type*} [Group Q]
    {gen : α → Q} :
    IsMinimalGeneratingFamily gen ↔
      (Subgroup.closure (Set.range gen) = ⊤ ∧
        ∀ S : Finset Q, Subgroup.closure (S : Set Q) = ⊤ → Fintype.card α ≤ S.card) :=
  Iff.rfl

/-- The generating clause of a minimal generating family. -/
theorem IsMinimalGeneratingFamily.closure {α : Type*} [Fintype α] {Q : Type*} [Group Q]
    {gen : α → Q} (h : IsMinimalGeneratingFamily gen) :
    Subgroup.closure (Set.range gen) = ⊤ := h.1

/-- The minimality clause of a minimal generating family. -/
theorem IsMinimalGeneratingFamily.card_le {α : Type*} [Fintype α] {Q : Type*} [Group Q]
    {gen : α → Q} (h : IsMinimalGeneratingFamily gen) {S : Finset Q}
    (hS : Subgroup.closure (S : Set Q) = ⊤) : Fintype.card α ≤ S.card := h.2 S hS

/-- **The pro-`p` Golod--Shafarevich inequality.**

For every nontrivial finite `p`-group `Q` and every *minimal* generating family `gen : α → Q`,

  `4 · dim_{𝔽_p} H²(Q,𝔽_p) > |α|²`,

where `dim_{𝔽_p} H²(Q,𝔽_p)` is expressed as `Work.HopfGaschutz.h2DimOf p α Q gen` -- the
`𝔽_p`-dimension of `K ⧸ K^p[K,F]`, `K = ker (FreeGroup.lift gen)`, which for a *minimal* generating
family of a finite `p`-group equals `log_p #H²(Q,𝔽_p)` by the transgression theorem
(`Work.HopfGaschutz.h2DimOf_eq_log_card_contH2`).

This is the single named target of the chapter; `Work.ProPGS.ProPGS.lean` proves it, and the
headline corollaries below only need it. -/
def ProPGolodShafarevich (p : ℕ) : Prop :=
  ∀ (α : Type) [Fintype α] (Q : Type) [Group Q] [Fintype Q] [Nontrivial Q],
    IsPGroup p Q → ∀ gen : α → Q, IsMinimalGeneratingFamily gen →
      4 * h2DimOf p α Q gen > Fintype.card α ^ 2

/-- The inequality in the product form `d(Q) · d(Q)`. -/
theorem ProPGolodShafarevich.four_mul_gt_sq {p : ℕ} (h : ProPGolodShafarevich p)
    {α : Type} [Fintype α] {Q : Type} [Group Q] [Fintype Q] [Nontrivial Q]
    (hQ : IsPGroup p Q) (gen : α → Q) (hmin : IsMinimalGeneratingFamily gen) :
    4 * h2DimOf p α Q gen > Fintype.card α * Fintype.card α := by
  have h' := h α Q hQ gen hmin
  have hsq : (Fintype.card α) ^ 2 = Fintype.card α * Fintype.card α := pow_two _
  omega

/-- `dim_{𝔽_p} H²` is monotone under a bound on `#H²`.  For a finite `2`-group with a minimal
generating family this is the conversion `#H²(Q,𝔽₂) ≤ 2^k → dim_{𝔽_p} H² ≤ k`. -/
theorem h2DimOf_le_of_card_contH2_le {α Q : Type*} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [DiscreteTopology Q] [TopologicalSpace (FreeGroup α)]
    [DiscreteTopology (FreeGroup α)] [Fintype α] [Fintype Q]
    (gen : α → Q) (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hmin : presKernel gen ≤ relFrattini 2 ⊤)
    {N : ℕ} (h : Nat.card (Work.RelatorRank.contH2 Q) ≤ N) :
    h2DimOf 2 α Q gen ≤ Nat.log 2 N := by
  have hbr := h2DimOf_eq_log_card_contH2 gen hgen hmin
  have hmono : Nat.log 2 (Nat.card (Work.RelatorRank.contH2 Q)) ≤ Nat.log 2 N :=
    Nat.log_mono_right h
  omega

end Work.ProPGS
