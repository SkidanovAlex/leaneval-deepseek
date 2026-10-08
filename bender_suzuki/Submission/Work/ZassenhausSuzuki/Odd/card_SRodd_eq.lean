import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ZassenhausSuzuki.Odd.OddCore
import Submission.Work.ZassenhausSuzuki.Odd.card_twoElements_ne_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.Odd.card_SRodd_eq`

The number of odd-order elements of the Suzuki rank-one configuration
`H = Q ⋊ D` (with `q = |Z Q| = |Q₀sub H|`, `|G| = q²(q-1)(q²+1)`), in the form used by the
numerical endgame of `Work.ZassenhausSuzuki.Odd.odd_isStronglyReal_of_suzuki`:

`#{x : x strongly real of odd order} + #{x : x of odd order, not strongly real} + q⁴
   = |G| + 1`.

The proof is the partition of `G` by the order of its elements:

* `SRodd` and `BadOdd` are disjoint (`BadOdd` carries the negation of `IsStronglyReal`) and
  their union is the set of elements of odd order: `1` is strongly real, and every other
  odd-order element either is strongly real or lies in `BadOdd`;
* by `Odd.no_mixed_order`, every non-identity element is of odd order or of `2`-power order,
  and these two classes are disjoint (a non-identity element of `2`-power order has even
  order).  So `#{odd order} + #{x ≠ 1, 2-power order} = |G|`;
* `Odd.card_twoElements_ne_one` computes `#{x ≠ 1, 2-power order} = q⁴ - 1`.

Hence `#{odd order} = |G| - (q⁴ - 1)`, which is the stated identity.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ZassenhausSuzuki.Odd

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- The identity is a product of two involutions. -/
private lemma isStronglyReal_one : Work.ZassenhausSuzuki.IsStronglyReal (1 : G) :=
  ⟨1, 1, by simp, by simp, by simp⟩

theorem card_SRodd_eq (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t) :
    Nat.card {x : G // Work.ZassenhausSuzuki.Odd.SRodd x}
      + Nat.card {x : G // Work.ZassenhausSuzuki.Odd.BadOdd x}
      + (Work.ZassenhausSuzuki.Odd.q H) ^ 4 = Nat.card G + 1 := by
  classical
  -- ## (1) The odd-order elements split into the strongly real ones and the bad ones.
  have hAB : Set.ncard {x : G | SRodd x} + Set.ncard {x : G | BadOdd x}
      = Set.ncard {x : G | Odd (orderOf x)} := by
    -- the two sets are disjoint
    have hd : Disjoint ({x : G | SRodd x} : Set G) {x : G | BadOdd x} := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact hx'.2.2 hx.1
    -- and their union is the set of odd-order elements
    have hu : ({x : G | SRodd x} : Set G) ∪ {x : G | BadOdd x}
        = {x : G | Odd (orderOf x)} := by
      ext x
      constructor
      · rintro (⟨_hsr, hodd⟩ | ⟨hodd, _hx1, _hnsr⟩)
        · exact hodd
        · exact hodd
      · intro hodd
        by_cases hsr : Work.ZassenhausSuzuki.IsStronglyReal x
        · exact Or.inl ⟨hsr, hodd⟩
        · by_cases hx1 : x = 1
          · subst hx1
            exact Or.inl ⟨isStronglyReal_one, hodd⟩
          · exact Or.inr ⟨hodd, hx1, hsr⟩
    have hc := Set.ncard_union_eq hd
    rw [hu] at hc
    exact hc.symm
  -- ## (2) `G` splits into the odd-order elements and the non-identity `2`-elements.
  have hOP : Set.ncard {x : G | Odd (orderOf x)}
      + Set.ncard {x : G | x ≠ 1 ∧ PowTwoOrder x} = Nat.card G := by
    -- disjointness: a non-identity element of `2`-power order has even order
    have hd : Disjoint ({x : G | Odd (orderOf x)} : Set G)
        {x : G | x ≠ 1 ∧ PowTwoOrder x} := by
      rw [Set.disjoint_left]
      intro x hx hx'
      obtain ⟨hx1, k, hk⟩ := hx'
      have hodd' : Odd (2 ^ k) := hk ▸ hx
      have hk0 : k = 0 := by
        by_contra hk0
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        have h2 : 2 ∣ 2 ^ (j + 1) := ⟨2 ^ j, by ring⟩
        exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr h2)
      exact hx1 (orderOf_eq_one_iff.mp (by rw [hk, hk0, pow_zero]))
    -- covering: every element is odd-order, or is `1`, or is of `2`-power order
    have hu : ({x : G | Odd (orderOf x)} : Set G) ∪ {x : G | x ≠ 1 ∧ PowTwoOrder x}
        = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro x
      rw [Set.mem_union]
      by_cases hx1 : x = 1
      · left
        show Odd (orderOf x)
        rw [hx1, orderOf_one]
        norm_num
      · rcases no_mixed_order h hx1 with hk | hodd
        · exact Or.inr ⟨hx1, hk⟩
        · exact Or.inl hodd
    have hc := Set.ncard_union_eq hd
    rw [hu, Set.ncard_univ] at hc
    exact hc.symm
  -- ## (3) There are `q⁴ - 1` non-identity elements of `2`-power order.
  have hP : Set.ncard {x : G | x ≠ 1 ∧ PowTwoOrder x} + 1 = (q H) ^ 4 := by
    have hc := card_twoElements_ne_one (G := G) (H := H) (Q := Q) (t := t) h
    exact hc
  -- ## (4) Assemble.
  have hA : Nat.card {x : G // SRodd x} = Set.ncard {x : G | SRodd x} :=
    Nat.card_coe_set_eq _
  have hB : Nat.card {x : G // BadOdd x} = Set.ncard {x : G | BadOdd x} :=
    Nat.card_coe_set_eq _
  omega

end Work.ZassenhausSuzuki.Odd
