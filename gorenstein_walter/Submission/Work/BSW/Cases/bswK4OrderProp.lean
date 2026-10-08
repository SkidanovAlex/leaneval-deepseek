/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, the `|K| = 4` case)

# The `|K| = 4` case of the Brauer–Suzuki–Wall theorem: the order of `G`

This file assembles the proof that in a finite group `G` in which the centralizer of every
involution is dihedral of order `8` and all involutions are conjugate, `|G| = 168` or `|G| = 360`
(Bender, *Finite groups with large subgroups*, Illinois J. Math. **18** (1974) 223–228, §3).

The work is split into four lemmas:

* `Work.BSW.Cases.K4.countingFacts` — Bender's §2 coset/involution count (truncated form);
* `Work.BSW.Cases.K4.fourGroupNormalizer` — for a Klein four-group `V`, `C_G(V) = V`, `N_G(V)` has
  order `24` and contains `9` involutions;
* `Work.BSW.Cases.K4.benderCase2` — Bender's Case 2 (`C_G(X) ≤ N_G(V)`), `|G| = 168`;
* `Work.BSW.Cases.K4.benderOrder360` — Bender's Case 1 (`C_G(X) ≰ N_G(V)`), `|G| = 360`.

The main theorem of this file is `Work.BSW.Cases.bswK4OrderProp`, i.e.
`Work.BSW.BSWK4OrderProp`, obtained by reducing `BSWHyps2` with `|K| = 4` to the `K4Hyp` setting
(`Work.BSW.Cases.K4.k4Hyp_of_hyps`) and applying the case analysis.
-/
import Mathlib
import Submission.Work.BSW.Concl
import Submission.Work.BSW.Cases.K4.K4Hyp
import Submission.Work.BSW.Cases.K4.countingFacts
import Submission.Work.BSW.Cases.K4.fourGroupNormalizer
import Submission.Work.BSW.Cases.K4.benderCase2
import Submission.Work.BSW.Cases.K4.benderOrder360

namespace Work.BSW.Cases

open Subgroup Work.GW2

/-- **Bender, `Finite groups with large subgroups` §3.**  Let `G` be a finite group in which all
involutions are conjugate and the centralizer of every involution is dihedral of order `8`.  Fix a
Klein four-group `V` and a subgroup `X` of order `3` in `N_G(V)`.  Then

* `C_G(X) ≤ N_G(V)` forces `|G| = 168` (`Work.BSW.Cases.K4.benderCase2`), and
* `C_G(X) ≰ N_G(V)` forces `|G| = 360` (`Work.BSW.Cases.K4.benderOrder360`). -/
theorem benderK4Order {G : Type} [Group G] [Finite G] (h : K4.K4Hyp G) :
    Nat.card G = 168 ∨ Nat.card G = 360 := by
  have hK4 : K4.K4Hyp G := h
  obtain ⟨⟨t, ht⟩, _h8, _hnc, hfour, _hconj⟩ := hK4
  obtain ⟨V, _hVle, hV4⟩ := hfour t ht
  have hN24 : Nat.card ↥(Subgroup.normalizer (V : Set G)) = 24 :=
    (K4.fourGroupNormalizer h V hV4).2.1
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.normalizer (V : Set G))) 3
    (by rw [hN24]; norm_num)
  let X : Subgroup G := Subgroup.zpowers (g : G)
  have hXle : X ≤ Subgroup.normalizer (V : Set G) := Subgroup.zpowers_le.mpr g.2
  have hgG : orderOf (g : G) = 3 := by
    rw [Subgroup.orderOf_coe g]; exact hg
  have hX3 : Nat.card ↥X = 3 := by
    rw [Nat.card_zpowers]; exact hgG
  by_cases hCX : Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (V : Set G)
  · exact Or.inl (K4.benderCase2 h V X hV4 hXle hX3 hCX)
  · exact Or.inr (K4.benderOrder360 h V X hV4 hXle hX3 hCX)

/-- **Bender, *Finite groups with large subgroups*, §3** (`REFS/bender1974_large.txt`), the
`|K| = 4` case.

Then `|C_G(t)| = |K ⊔ ⟨s⟩| = 8`, and `K` is cyclic (it is abelian with the unique involution `t`,
and `s` inverts it), so `C_G(t) ≅ D₈` is dihedral and — all involutions being conjugate — every
involution has dihedral centralizer of order `8`.  Bender's Lemma 1 (coset/involution count,
`REFS/bender1974_large.txt` pp. 223–224) applied as in §3 gives `|G| = 9·8·5 = 360` in Case 1 and
`|G| = 7·8·3 = 168` in Case 2. -/
theorem bswK4OrderProp : Work.BSW.BSWK4OrderProp := by
  intro G _ _ _hS _hnab t s K h hk
  exact benderK4Order (K4.k4Hyp_of_hyps h hk)

end Work.BSW.Cases
