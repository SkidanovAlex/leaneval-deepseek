/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area ZASS: step Z1 (two-point stabilizers)

`Work.ZASS.eq_one_of_fixes_three`: an element fixing three distinct points of a Zassenhaus
action is trivial.  Consequences: the stabilizers of `{x, ∞}` and `{y, ∞}` for `x ≠ y`
(`x, y ≠ ∞`) meet trivially, and the two-point stabilizer has order `(q-1)/2`.
-/
import Mathlib
import Submission.Work.ZASS.Defs

open scoped MatrixGroups

namespace Work.ZASS

open Work.GW2 (ZassHyps2)
open Work.Zassenhaus (borel pairStab fixesOnly fixesSome)

variable {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]

/-- **Z1.** In a Zassenhaus action every nonidentity element fixes at most two points; hence
an element fixing three pairwise distinct points is trivial.  (Cf.
`Work.Zassenhaus.zass_eq_one_of_fixes_three`, stated there for the older `ZassHyp`.) -/
theorem eq_one_of_fixes_three {q : ℕ} (h : ZassHyps2 G X q) {g : G} {x y z : X}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hx : g • x = x) (hy : g • y = y)
    (hz : g • z = z) : g = 1 := by
  by_contra hg
  have hle : ({a : X | g • a = a} : Set X).ncard ≤ 2 := h.2.2.2.1 g hg
  have hsub : ({x, y, z} : Set X) ⊆ {a : X | g • a = a} := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  have h3 : ({x, y, z} : Set X).ncard = 3 :=
    (Set.ncard_eq_three).2 ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hmono := Set.ncard_le_ncard hsub
  omega

/-- **Z1.** Membership form: an element of both `G_{∞x}` and `G_{∞y}` (`x ≠ y`, `x, y ≠ ∞`)
fixes three distinct points, hence is trivial. -/
theorem eq_one_of_mem_pairStab_pairStab {q : ℕ} (h : ZassHyps2 G X q) {inf x y : X}
    (hx : x ≠ inf) (hy : y ≠ inf) (hxy : x ≠ y) {g : G}
    (hgx : g ∈ pairStab G inf x) (hgy : g ∈ pairStab G inf y) : g = 1 :=
  eq_one_of_fixes_three h hxy hx hy (Work.Zassenhaus.mem_pairStab_iff.mp hgx).1
    (Work.Zassenhaus.mem_pairStab_iff.mp hgy).1 (Work.Zassenhaus.mem_pairStab_iff.mp hgx).2

/-- **Z1.** Subgroup form of the previous statement. -/
theorem pairStab_inf_pairStab_inf_eq_bot {q : ℕ} (h : ZassHyps2 G X q) {inf x y : X}
    (hx : x ≠ inf) (hy : y ≠ inf) (hxy : x ≠ y) :
    pairStab G inf x ⊓ pairStab G inf y = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  exact eq_one_of_mem_pairStab_pairStab h hx hy hxy hg.1 hg.2

/-- **Z1.** The order of the two-point stabilizer is `h = (q-1)/2`; this is arithmetic from
the clause `2 * |G_{xy}| = q - 1` of `ZassHyps2`. -/
theorem card_pairStab {q : ℕ} (h : ZassHyps2 G X q) {inf zero : X} (hne : inf ≠ zero) :
    Nat.card (pairStab G inf zero) = (q - 1) / 2 := by
  have h2 : 2 * Nat.card (MulAction.stabilizer G zero ⊓ MulAction.stabilizer G inf :
      Subgroup G) = q - 1 := h.2.2.2.2 zero inf (Ne.symm hne)
  have h3 : pairStab G inf zero =
      MulAction.stabilizer G zero ⊓ MulAction.stabilizer G inf := rfl
  rw [h3]
  omega

/-- **Z1.** The two-point stabilizer is nontrivial as soon as `q ≥ 4` (it has order
`(q-1)/2 ≥ 2`), in particular for the Zassenhaus values `q = p^k ≥ 5`. -/
theorem one_lt_card_pairStab {q : ℕ} (h : ZassHyps2 G X q) {inf zero : X} (hne : inf ≠ zero)
    (hq : 5 ≤ q) : 1 < Nat.card (pairStab G inf zero) := by
  rw [card_pairStab h hne]
  omega

end Work.ZASS
