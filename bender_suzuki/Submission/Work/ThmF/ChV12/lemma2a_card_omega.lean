import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.RankOneUniqueness.qPt_surjective
import Submission.Work.RankOneUniqueness.qPt_injective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.lemma2a_card_omega` — Peterfalvi II, Ch. V §2, Lemma 2 (a) (cardinality)

In the split rank-one situation `IsSplitRankOne H Q t`, the set `Ω = G ⧸ H` of conjugates of
`H` has exactly `|Q| + 1` elements.

Mathematically this is the classical `|P¹(F_q)| = q + 1` of a split BN-pair of rank one: the
canonical point `∞ = pt H` is fixed by `H`, `Q` is sharply transitive on the complement, and
`Q` is transitive on `Ω ∖ {∞}` (`RankOneUniqueness.qPt_surjective`), so the map

`x ↦ qPt H t x = x • (t • ∞) : Q → Ω ∖ {∞}`

is injective (`RankOneUniqueness.qPt_injective`) and surjective
(`RankOneUniqueness.qPt_surjective`), hence a bijection. It follows that
`|Ω| = |Ω ∖ {∞}| + 1 = |Q| + 1`.

This is exactly the cardinality hypothesis `hcard` that `lemma2a_Q_regular` takes as input.
-/

set_option autoImplicit false

namespace Work.ThmF.ChV12

open Submission.Blueprint

/-- Removing one point `a` from a finite type lowers its cardinality by one:
`|{x // x ≠ a}| + 1 = |α|`. -/
private lemma card_subtype_ne_add_one (α : Type) [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} + 1 = Nat.card α := by
  have h1 : Nat.card {x : α // x ≠ a} = Nat.card α - 1 := by
    rw [show Nat.card {x : α // x ≠ a} = ({a}ᶜ : Set α).ncard from by
      rw [show ({a}ᶜ : Set α).ncard = Nat.card ↥({a}ᶜ : Set α) from rfl]
      exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => by simp))]
    rw [Set.ncard_compl, Set.ncard_singleton]
  have h2 : 1 ≤ Nat.card α := Nat.card_pos_iff.mpr ⟨⟨a⟩, inferInstance⟩
  omega

/-- The point labelling `x ↦ x • (t • ∞)`: a bijection between `Q` and the set
`Ω ∖ {∞}` of points of `Ω = G ⧸ H` different from the canonical point. -/
private noncomputable def qPtEquiv {G : Type} [Group G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) :
    Q ≃ {ω : Work.DoubleTransitivity.Omega H // ω ≠ Work.DoubleTransitivity.pt H} :=
  Equiv.ofBijective
    (fun x : Q =>
      ⟨Work.RankOneUniqueness.qPt H t (x : G), Work.RankOneUniqueness.qPt_ne_pt h x.2⟩)
    (by
      constructor
      · intro x y hxy
        apply Subtype.ext
        exact Work.RankOneUniqueness.qPt_injective h x.2 y.2 (Subtype.ext_iff.mp hxy)
      · intro ω
        obtain ⟨x, hx, hxq⟩ := Work.RankOneUniqueness.qPt_surjective h ω.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxq⟩)

theorem lemma2a_card_omega {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} (h : Submission.Blueprint.IsSplitRankOne H Q t) : Nat.card (Work.DoubleTransitivity.Omega H) = Nat.card Q + 1 := by
  have hb : Nat.card Q =
      Nat.card {ω : Work.DoubleTransitivity.Omega H //
        ω ≠ Work.DoubleTransitivity.pt H} :=
    Nat.card_congr (qPtEquiv h)
  rw [hb]
  exact (card_subtype_ne_add_one (Work.DoubleTransitivity.Omega H)
    (Work.DoubleTransitivity.pt H)).symm

end Work.ThmF.ChV12
