import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.RankOneUniqueness.qPt_injective
import Submission.Work.RankOneUniqueness.qPt_surjective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausTwoGroup.card_quotient_eq` — `Q` is regular on `Ω ∖ {∞}`

Let `H = Q ⋊ D` be the rank-one datum of a split BN-pair of rank one
(`IsSplitRankOne H Q t`, with `D = H ∩ Hᵗ` the two-point stabiliser, `Q ≤ H`, `H ≤ N(Q)`,
`Q ⊓ D = ⊥`, `Q ⊔ D = H`) and let `Ω = G ⧸ H` be the set of cosets, with base point
`∞ = pt H = H` and `t • ∞ ≠ ∞` (`t ∉ H`).

The points `qPt H t x = x·t·H` for `x ∈ Q` are then exactly the points of `Ω ∖ {∞}`:

* `RankOneUniqueness.qPt_ne_pt`: no `qPt H t x` (`x ∈ Q`) is `∞`;
* `RankOneUniqueness.qPt_injective`: `x ↦ qPt H t x` is injective on `Q`, because
  `x·t·H = y·t·H` forces `x⁻¹y ∈ H ∩ Hᵗ = D`, and `x⁻¹y ∈ Q` with `Q ⊓ D = ⊥`;
* `RankOneUniqueness.qPt_surjective`: every `ω ≠ ∞` is `qPt H t x` for some `x ∈ Q`
  (`H` is transitive on `Ω ∖ {∞}` by 2-transitivity, and `H = Q·D` with `D` fixing `t • ∞`).

Hence the map `Q ⊕ Unit → Ω`, `inl x ↦ qPt H t x`, `inr _ ↦ ∞`, is a bijection, and
`|G : H| = |Ω| = |Q| + 1`.

`Subgroup.index H` is *definitionally* `Nat.card (G ⧸ H)`, so the statement is exactly
`|G : H| = |Q| + 1`.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

/-- In the split rank-one set-up `Q` is regular on the set of points different from the base
point of `Ω = G ⧸ H`: the map `x ↦ x·t·H` is a bijection from `Q` onto `Ω ∖ {H}`.  Hence
`|G : H| = |Ω| = |Q| + 1`. -/
theorem card_quotient_eq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) :
    Nat.card (G ⧸ H) = Nat.card Q + 1 := by
  classical
  -- the labelling of `Ω = G ⧸ H` by `Q ⊕ Unit`: `x ↦ x·t·H`, and `∞ = H` for the extra point
  have hbij : Function.Bijective
      (fun o : Q ⊕ Unit =>
        Sum.elim (fun x : Q => Work.RankOneUniqueness.qPt H t (x : G))
          (fun _ : Unit => Work.RankOneUniqueness.pt H) o) := by
    refine ⟨?_, ?_⟩
    · rintro (x | u) (y | v) hab
      · -- both points are `qPt H t _`, and the labelling is injective on `Q`
        have hxy : (x : G) = (y : G) :=
          Work.RankOneUniqueness.qPt_injective h x.2 y.2 (by simpa using hab)
        exact congrArg Sum.inl (Subtype.ext hxy)
      · -- `qPt H t x ≠ ∞`
        exact absurd (by simpa using hab) (Work.RankOneUniqueness.qPt_ne_pt h x.2)
      · -- `∞ ≠ qPt H t y`
        exact absurd (by simpa using hab.symm) (Work.RankOneUniqueness.qPt_ne_pt h y.2)
      · -- the two extra points agree
        cases u
        cases v
        rfl
    · -- every point is either `∞` or of the form `qPt H t x`, `x ∈ Q`
      intro ω
      rcases eq_or_ne ω (Work.RankOneUniqueness.pt H) with hω | hω
      · exact ⟨Sum.inr Unit.unit, by simp [hω]⟩
      · obtain ⟨x, hx, hxω⟩ := Work.RankOneUniqueness.qPt_surjective h hω
        exact ⟨Sum.inl ⟨x, hx⟩, by simpa using hxω⟩
  -- `|Ω| = |Q ⊕ Unit| = |Q| + 1`
  have hcard : Nat.card (Q ⊕ Unit) = Nat.card (G ⧸ H) :=
    Nat.card_congr (Equiv.ofBijective _ hbij)
  have hsplit : Nat.card (Q ⊕ Unit) = Nat.card Q + 1 := by
    rw [Nat.card_sum]
    congr 1
    exact Nat.card_unique
  exact hcard.symm.trans hsplit

end Work.ZassenhausTwoGroup
