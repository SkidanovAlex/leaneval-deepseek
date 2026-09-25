import Mathlib
import Submission.GroupTheory.GolodShafarevichFromCommons
import Submission.Work.HopfGaschutz.Defs
import Submission.Work.HopfGaschutz.le_normalClosure_of_le_sup_relFrattini
import Submission.Work.HopfGaschutz.relFrattiniDim_le_card_of_normalGenerates
import Submission.Work.HopfGaschutz.h2DimOf_le_card_of_presentation
import Submission.Work.HopfGaschutz.le_normalClosure_of_finite_pgroup_defect
import Submission.Work.HopfGaschutz.normalGeneratorNumber_eq_relFrattiniDim_of_finite_pgroup

/-!
# `Work.HopfGaschutz.Dictionary` -- the relation-rank dictionary

**Namespace** `Work.HopfGaschutz`; module `Submission.Work.HopfGaschutz.Dictionary`.

This file assembles the relation-rank dictionary out of the pieces of the chapter:

* **downward** (`dim H² ≤ r` for every presentation with `r` relators) -- the *easy* direction,
  `RelationRankLowerBound`, whose proof for a genuinely finite presentation is
  `relFrattiniDim_le_card_of_normalGenerates`;
* **upward** (`dim H² ≤ r` produces a presentation with `≤ r` relators) -- the single named
  classical input `GaschutzDictionary p`;
* **the finite `p`-group case, unconditionally**: for `K ⊴ G` with `G` a finite `p`-group,
  `normalGeneratorNumber K = relFrattiniDim p K`
  (`normalGeneratorNumber_eq_relFrattiniDim_of_finite_pgroup`) -- the generalised Burnside basis
  theorem for normal subgroups, and the case of the dictionary in which the *engine*
  (`K = ⟨S⟩^G · K^p[K,G] → ⟨S⟩^G = K`, `le_normalClosure_of_le_sup_relFrattini`) is available
  because the defect is automatically a `p`-group;
* **the `p`-group-internal consequence** consumed by the endgame: for a finite `p`-group `Q` with a
  minimal generating family `gen : Fin 5 → Q` and `dim H² ≤ 6`, a presentation with five generators
  and at most six relators exists.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped commutatorElement

namespace Work.HopfGaschutz

variable {p : ℕ}

/-! ## The two directions of the dictionary -/

/-- **The upward direction of the dictionary**, unpacked from `GaschutzDictionary`: a bound on the
relation rank of a presentation of a finite `p`-group `G` on a minimal generating family `gen`
produces a presentation on that same family with at most that many relators. -/
theorem exists_relatorSet_of_le_h2DimOf (hdict : GaschutzDictionary p)
    {α : Type} [Fintype α] [DecidableEq α] {G : Type} [Group G] [Fintype G]
    (hG : IsPGroup p G) (gen : α → G) (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hmin : ∀ S : Finset G, Subgroup.closure (S : Set G) = ⊤ → Fintype.card α ≤ S.card)
    {r : ℕ} (h : h2DimOf p α G gen ≤ r) :
    ∃ rel : Finset (FreeGroup α), rel.card ≤ r ∧
      MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (rel : Set (FreeGroup α)) :=
  hdict G hG gen hgen hmin r h

/-- **The downward direction of the dictionary**, in the form supplied by
`RelationRankLowerBound`: every relator set of a presentation has at least
`dim_{𝔽_p} H²` elements. -/
theorem card_rel_le_of_presentation {α : Type} [Fintype α] [DecidableEq α] {G : Type}
    [Group G] (hlow : RelationRankLowerBound p α G)
    (gen : α → G) (rel : Finset (FreeGroup α))
    (h : MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (rel : Set (FreeGroup α))) :
    h2DimOf p α G gen ≤ rel.card :=
  hlow gen rel h

/-! ## The finite `p`-group case, unconditionally -/

/-- **The dictionary in the finite `p`-group case.**  For `K ⊴ G` with `G` a finite `p`-group, the
minimal number of normal generators of `K` equals the `𝔽_p`-dimension of
`K ⧸ K^p[K,G]` -- i.e. the number of relators of the corresponding presentation of a quotient is
the relation rank, in the one case in which the engine is a theorem rather than an input.

(Here the ambient group is finite, so no defect can occur: `K ⧸ ⟨S⟩^G` is a finite `p`-group and
`M = M^p[M,G]` forces `M = ⊥`.) -/
theorem normalGeneratorNumber_finite_pgroup {G : Type} [Group G] [Fintype G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) {K : Subgroup G} [K.Normal] :
    normalGeneratorNumber K = relFrattiniDim p K :=
  normalGeneratorNumber_eq_relFrattiniDim_of_finite_pgroup hG

/-- **The upward direction, proved, in the finite `p`-group case**: a bound on the relation rank of
`K ⊴ G` (`G` a finite `p`-group) produces a normal generating set of that size. -/
theorem exists_normalGenerates_card_le_of_relFrattiniDim_le {G : Type} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) {K : Subgroup G} [K.Normal] {r : ℕ}
    (h : relFrattiniDim p K ≤ r) :
    ∃ S : Finset G, S.card ≤ r ∧ NormalGenerates K S := by
  classical
  have hle : normalGeneratorNumber K ≤ r := by
    rw [normalGeneratorNumber_eq_relFrattiniDim_of_finite_pgroup hG]; exact h
  have hne : ∃ S : Finset G, S.card = normalGeneratorNumber K ∧ NormalGenerates K S := by
    have hmem := Nat.sInf_mem
      (s := {r : ℕ | ∃ S : Finset G, S.card = r ∧ NormalGenerates K S})
      ⟨((Finset.univ : Finset K).image K.subtype).card,
        (Finset.univ : Finset K).image K.subtype, rfl, by
        have hcoe : (↑((Finset.univ : Finset K).image K.subtype) : Set G) = K := by
          ext x
          constructor
          · intro hx
            obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
            exact y.2
          · intro hx
            exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
        rw [NormalGenerates, hcoe]
        exact Subgroup.normalClosure_eq_self K⟩
    simpa [normalGeneratorNumber] using hmem
  obtain ⟨S, hScard, hSgen⟩ := hne
  exact ⟨S, hScard ▸ hle, hSgen⟩

/-! ## The `p`-group-internal consequence for the endgame -/

/-- **The `p`-group-internal consequence of the dictionary** (the form the endgame consumes):
a finite `p`-group with a minimal generating family of size five and relation rank at most six
admits a presentation with five generators and at most six relators.

This is `GaschutzDictionary p` at `α = Fin 5`, `r = 6`.  No continuous cohomology is involved: the
hypothesis `h2DimOf` is the *presentation-theoretic* relation rank. -/
theorem exists_relatorSet_five_six (hdict : GaschutzDictionary 2)
    {Q : Type} [Group Q] [Fintype Q] (hQ : IsPGroup 2 Q) (gen : Fin 5 → Q)
    (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hmin : ∀ S : Finset Q, Subgroup.closure (S : Set Q) = ⊤ → 5 ≤ S.card)
    (h : h2DimOf 2 (Fin 5) Q gen ≤ 6) :
    ∃ rel : Finset (FreeGroup (Fin 5)), rel.card ≤ 6 ∧
      MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (rel : Set (FreeGroup (Fin 5))) :=
  exists_relatorSet_of_le_h2DimOf hdict hQ gen hgen (by simpa using hmin) h

/-- The same consequence with the generating family only required to be *minimal* in the sense that
no four elements generate (the shape in which the arithmetic certificate `d(Γ) = 5` arrives). -/
theorem exists_relatorSet_five_six_of_no_smaller (hdict : GaschutzDictionary 2)
    {Q : Type} [Group Q] [Fintype Q] (hQ : IsPGroup 2 Q) (gen : Fin 5 → Q)
    (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hmin : ∀ S : Finset Q, Subgroup.closure (S : Set Q) = ⊤ → 5 ≤ S.card)
    (h : h2DimOf 2 (Fin 5) Q gen ≤ 6) :
    ∃ rel : Finset (FreeGroup (Fin 5)), rel.card ≤ 6 ∧
      MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (rel : Set (FreeGroup (Fin 5))) :=
  exists_relatorSet_five_six hdict hQ gen hgen hmin h

/-! ## The engine under the hypothesis that the defect is a finite `p`-group -/

/-- **The sharpened engine**: the naive criterion `K = ⟨S⟩^F · K^p[K,F] → ⟨S⟩^F = K` becomes a
theorem as soon as the *defect* `K ⧸ ⟨S⟩^F` is a finite `p`-group and `F ⧸ K` is a `p`-group.  This
is the hypothesis that the pro-`p` category supplies automatically (there the defect is compact
pro-`p`, and Nakayama over `𝔽_p[[Γ]]` applies), and it is exactly what the discrete counterexample
`Counterexample.lean` violates (`Ktwo ⧸ ⟪x₁⁶⟫ ≅ ℤ/3`).  Consequently *a* presentation with
`h2DimOf` relators exists whenever a spanning set of that size can be chosen with a finite
`p`-group defect. -/
theorem normalGenerates_of_finite_pgroup_defect {F : Type*} [Group F] {p : ℕ} [Fact p.Prime]
    {K : Subgroup F} [K.Normal] (hquot : IsPGroup p (F ⧸ K)) {S : Finset F}
    (hS : (S : Set F) ⊆ K)
    (hspan : K ≤ Subgroup.normalClosure (S : Set F) ⊔ relFrattini p K)
    (hfin : Finite (K ⧸ (Subgroup.normalClosure (S : Set F)).subgroupOf K))
    (hdef : IsPGroup p (K ⧸ (Subgroup.normalClosure (S : Set F)).subgroupOf K)) :
    NormalGenerates K S :=
  le_antisymm
    (Subgroup.normalClosure_le_normal (fun y hy => hS hy))
    (le_normalClosure_of_finite_pgroup_defect hS hquot hspan hfin hdef)

/-! ## The single input, characterised -/

/-- **`GaschutzDictionary p` is exactly the statement that a minimal presentation of a finite
`p`-group has `dim_{𝔽_p} H²` relators.**  Both directions are proved here, using
`h2DimOf_le_card_of_presentation` (the easy direction) for the `≥` half.

Consequently the input is not bookkeeping: by Rapaport's theorem every finite nilpotent group —
in particular every finite `p`-group — admits a *minimal* presentation (with `d(G)` generators), and
the question whether its relator count is the minimal possible one, `d(H₁) + d(H₂) = dim H²`, is
exactly *efficiency* of `G`.  **No non-efficient finite `p`-group is known**: this is Mann's
Question 18 (*Some questions about `p`-groups*, J. Austral. Math. Soc. Ser. A 67 (1999)), restated as
the question "is every finite `p`-group an element of `𝒢_p`?" in Gardam, *Finite groups of arbitrary
deficiency*, arXiv:1705.02040, which records "there is no known example of a non-efficient finite
`p`-group".  So the discrete, free-kernel form of the dictionary **cannot be a theorem of this
workspace**: it is an open problem.  What is proved here is the pro-`p`-shaped finite case
(`normalGeneratorNumber_eq_relFrattiniDim_of_finite_pgroup`) and the easy direction in full
generality. -/
theorem gaschutzDictionary_iff_minimalRelatorSet {p : ℕ} [Fact p.Prime] :
    GaschutzDictionary p ↔
      ∀ {α : Type} [Fintype α] [DecidableEq α] (Q : Type) [Group Q] [Fintype Q],
        IsPGroup p Q → ∀ (gen : α → Q),
        Subgroup.closure (Set.range gen) = ⊤ →
        (∀ S : Finset Q, Subgroup.closure (S : Set Q) = ⊤ → Fintype.card α ≤ S.card) →
        ∃ rel : Finset (FreeGroup α), rel.card = h2DimOf p α Q gen ∧
          MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (rel : Set (FreeGroup α)) := by
  constructor
  · intro hdict α _ _ Q _ _ hQ gen hgen hmin
    obtain ⟨rel, hcard, hker⟩ := hdict Q hQ gen hgen hmin (h2DimOf p α Q gen) le_rfl
    exact ⟨rel, le_antisymm hcard (h2DimOf_le_card_of_presentation p gen hgen rel hker), hker⟩
  · intro h α _ _ Q _ _ hQ gen hgen hmin r hr
    obtain ⟨rel, hcard, hker⟩ := h Q hQ gen hgen hmin
    exact ⟨rel, hcard ▸ hr, hker⟩

/-! ## The finite case of the endgame is *vacuous* -- an important sanity check -/

/-- **No nontrivial finite `2`-group has `d = 5` and `dim H² ≤ 6`.**  Combining the dictionary with
the finite `p`-group Golod--Shafarevich inequality
(`Submission.GroupTheory.finitePGroupGolodShafarevich_of_commons`): a presentation with five
generators and at most six relators would give `4·6 = 24 ≤ 25 = 5²`, against
`4 · rel.card > 5²`.  Hence a finite `2`-group with `h2DimOf 2 (Fin 5) Q gen ≤ 6` on a minimal
generating family must be **trivial**.

This is worth recording because it shows that the `p`-group-internal consequence
`exists_relatorSet_five_six` can *never* be applied to a nontrivial finite group with these numbers:
the arithmetic bound `dim H² ≤ 6` with `d = 5` is a statement about the *infinite* pro-`2` group `Γ`
(whose finite quotients have at most four generators, that being the whole point of the tower), and
the finite-level dictionary is a tool for the finite quotients, not a route to a five-generator finite
group. -/
theorem subsingleton_of_h2DimOf_le_six (hdict : GaschutzDictionary 2)
    (hGS : Submission.GroupTheory.FinitePGroupGolodShafarevich 2)
    {Q : Type} [Group Q] [Fintype Q] (hQ : IsPGroup 2 Q) (gen : Fin 5 → Q)
    (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hmin : ∀ S : Finset Q, Subgroup.closure (S : Set Q) = ⊤ → 5 ≤ S.card)
    (h : h2DimOf 2 (Fin 5) Q gen ≤ 6) : Subsingleton Q := by
  classical
  by_contra hnt
  haveI : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hnt
  obtain ⟨rel, hcard, hker⟩ := exists_relatorSet_five_six hdict hQ gen hgen hmin h
  have hsurj : Function.Surjective (FreeGroup.lift gen) := by
    rw [← MonoidHom.range_eq_top, FreeGroup.range_lift_eq_closure, hgen]
  have hpres : Nonempty (Q ≃* FreeGroup (Fin 5) ⧸ Subgroup.normalClosure (rel : Set (FreeGroup (Fin 5)))) := by
    refine ⟨?_⟩
    have h := QuotientGroup.quotientKerEquivOfSurjective (FreeGroup.lift gen) hsurj
    have e2 : FreeGroup (Fin 5) ⧸ MonoidHom.ker (FreeGroup.lift gen) ≃*
        FreeGroup (Fin 5) ⧸ Subgroup.normalClosure (rel : Set (FreeGroup (Fin 5))) :=
      QuotientGroup.quotientMulEquivOfEq hker
    exact h.symm.trans e2
  have hineq : 4 * rel.card > Fintype.card (Fin 5) * Fintype.card (Fin 5) :=
    hGS Q rel hQ hpres (by intro S hS; simpa using hmin S hS)
  simp only [Fintype.card_fin] at hineq
  omega

/-! ## The deficiency diagnosis

For a *finite* `p`-group `Q` with a minimal generating family of size `α`, the two bounds available
without the engine are

* `r ≥ dim_{𝔽_p} H²(Q, 𝔽_p)` -- the easy direction, i.e. the cohomological Euler characteristic of
  the two-step resolution, `relFrattiniDim_le_card_of_normalGenerates` here;
* `r ≥ α + d(H₂(Q,ℤ))`, which is the same inequality (`dim H² = dim H¹ + d(H₂) = α + d(H₂)` for a
  finite `p`-group), i.e. the classical "the Schur multiplicator can be generated by `-def`" bound
  (Johnson--Robertson).

The upward direction `r ≤ dim H²` is the assertion that the bound is *attained*, which for finite
groups is the statement that `Q` is **efficient**; the naive proof route (`K = ⟨S⟩^G·K^p[K,G]`
implies `K = ⟨S⟩^G`) is *false* in the discrete setting, as `Counterexample.lean` records.  In the
pro-`p` setting the defect is a pro-`p` group, Nakayama applies, and the bound is attained: that is
the classical theorem (Gaschütz 1953; Koch Ch. 11; Neukirch--Schmidt--Wingberg I §4.3;
Hajir--Maire--Ramakrishna, arXiv:2103.09508, where `r(G) := dim H²(G,ℤ/p)`). -/

end Work.HopfGaschutz
