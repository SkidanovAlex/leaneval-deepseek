import Mathlib
import Submission.Work.FeitSibley.GroupTheory.D_dvd_card_sub_one
import Submission.Work.FeitSibley.GroupTheory.S_Q1
import Submission.Work.FeitSibley.Coherence.Q1_isNilpotent_of_D_ne_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `|D| + 1 ≤ |Z(Q₁)|` for the Feit–Sibley data

`D` acts fixed point freely by conjugation on `Q₁` (`h.D_fpf_Q1`), and `Q₁ ≠ ⊥` is not a
`2`-group.  Since `D ≠ ⊥` (here `2 ≤ |D|`), Thompson's theorem
(`Q1_isNilpotent_of_D_ne_bot`) makes `Q₁` nilpotent, so its centre is nontrivial; the centre is
characteristic, hence `D`-invariant, so `D` acts fixed point freely on `Z(Q₁)` as well and
Burnside's lemma (`D_dvd_card_sub_one`) gives `|D| ∣ |Z(Q₁)| - 1`.

As `Z(Q₁) ≠ ⊥` we have `|Z(Q₁)| ≥ 2`, so `|Z(Q₁)| - 1` is a *positive* multiple of `|D|`, and
therefore `|Z(Q₁)| - 1 ≥ |D|`, i.e. `|D| + 1 ≤ |Z(Q₁)|`.

This is the numerical input used in Peterfalvi II, Appendice XII, step (2) (the degree bound for
`𝒮(Q')`).
-/

set_option linter.style.haveILetI false

namespace Work.FeitSibley.Coherence

theorem card_centerQ1_ge_card_D_add_one {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) (hd : 2 ≤ Nat.card h.D) :
    Nat.card h.D + 1 ≤ Nat.card h.centerQ1 := by
  -- `|D| ≥ 2` forces `D ≠ ⊥`.
  have hDne : h.D ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hd
    omega
  -- `Q₁` is nilpotent (Thompson), and nontrivial, hence its centre is nontrivial.
  haveI : Group.IsNilpotent ↥h.Q1 := Work.FeitSibley.Coherence.Q1_isNilpotent_of_D_ne_bot h hDne
  haveI : Nontrivial ↥h.Q1 := (Subgroup.nontrivial_iff_ne_bot h.Q1).mpr h.Q1_ne_bot
  have hZne : h.centerQ1 ≠ ⊥ := by
    have hc : Subgroup.center ↥h.Q1 ≠ ⊥ := Group.IsNilpotent.center_ne_bot ↥h.Q1
    have hmap : (Subgroup.center ↥h.Q1).map h.Q1.subtype ≠ ⊥ :=
      fun hb =>
        hc ((Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥h.Q1)
          h.Q1.subtype_injective).mp hb)
    exact hmap
  -- `D` normalises `Z(Q₁)` and acts fixed point freely on it, so `|D| ∣ |Z(Q₁)| - 1`.
  have hAn : h.D ≤ Subgroup.normalizer (h.centerQ1 : Set G) :=
    le_trans h.D_le_H h.centerQ1_normal_in_H
  have hdvd : Nat.card h.D ∣ Nat.card ↥h.centerQ1 - 1 :=
    Work.FeitSibley.GroupTheory.D_dvd_card_sub_one h h.centerQ1 h.centerQ1_le_Q1 hAn
  -- `Z(Q₁) ≠ ⊥` gives `|Z(Q₁)| ≥ 2`, so the multiple `|Z(Q₁)| - 1` is positive.
  have h2 : 2 ≤ Nat.card ↥h.centerQ1 :=
    Work.FeitSibley.FSData.two_le_card_of_ne_bot h.centerQ1 hZne
  have hle : Nat.card h.D ≤ Nat.card ↥h.centerQ1 - 1 :=
    Nat.le_of_dvd (by omega) hdvd
  omega

end Work.FeitSibley.Coherence
