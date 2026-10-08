/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.

# An involution fixing a point forces `q ≡ 1 (mod 4)`

Let `G` act on `X` under the Zassenhaus hypotheses `Work.GW2.ZassHyps2 G X q` with `q` odd.
The action is faithful and 2-transitive on `q + 1` points (`Nat.card X = q + 1`), every
nonidentity element fixes at most two points, and every two-point stabilizer has order
`(q - 1) / 2`.

**Claim.** If an involution `s` (`orderOf s = 2`) fixes a point `x`, then `(q - 1) / 2` is
even, i.e. `q ≡ 1 (mod 4)`.

This is the classical dichotomy for Zassenhaus groups: for `q odd` the number of fixed points
of an involution is even (a fixed-point-free involution permutes the remaining points in
2-cycles, so it moves an even number of them — `Equiv.Perm.two_dvd_card_support`).  Since
`Nat.card X = q + 1` is even and the number of fixed points of a nonidentity element is at most
two, an involution which fixes `x` must fix *exactly two* points `x, y`.  Hence `s` lies in the
two-point stabilizer `G_x ⊓ G_y`, whose order is `(q - 1) / 2`; by Cauchy/Lagrange (an element
of order `2` divides the order of the group containing it) `2 ∣ (q - 1) / 2`.
-/
import Mathlib
import Submission.Work.ZASS.Leaf9
import Submission.Work.ZASS.card_G

-- `Fintype.ofFinite` has to be introduced with `letI`/`haveI`: a local `Fintype` instance
-- genuinely changes what `Finset.univ` (and hence `Equiv.Perm.support`) elaborates to.
set_option linter.style.haveILetI false

namespace Work.ZASS2

/-! ## Parity of the number of moved points -/

/-- **An involution of a finite set moves an even number of points.**

Equivalently, its number of fixed points has the same parity as the ambient set.  This is
`Equiv.Perm.two_dvd_card_support`, transported along `MulAction.toPermHom`. -/
lemma two_dvd_ncard_movedBy {G X : Type} [Group G] [MulAction G X] [Finite X]
    (s : G) (hs : s * s = 1) : 2 ∣ ({x : X | s • x ≠ x} : Set X).ncard := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  have hset : ((MulAction.toPermHom G X s).support : Set X) = {x : X | s • x ≠ x} := by
    rw [Equiv.Perm.coe_support_eq_set_support]
    ext x
    simp [MulAction.toPermHom_apply]
  rw [← hset, Set.ncard_coe_finset]
  exact Equiv.Perm.two_dvd_card_support (by rw [← map_pow, pow_two, hs, map_one])

/-- **Parity of the fixed points of an involution.**  If `s` is an involution of the finite
`G`-set `X` and `Nat.card X` is even, then `s` fixes an even number of points.

(The moved points and the fixed points partition `X`, and the moved points are even in number by
`two_dvd_ncard_movedBy`.) -/
lemma even_ncard_fixedBy_of_involution {G X : Type} [Group G] [MulAction G X] [Finite X]
    (s : G) (hs : s * s = 1) (hX : Even (Nat.card X)) :
    Even (({x : X | s • x = x} : Set X).ncard) := by
  have hmoved : 2 ∣ ({x : X | s • x ≠ x} : Set X).ncard := two_dvd_ncard_movedBy s hs
  have hcompl : ({x : X | s • x = x} : Set X) = ({x : X | s • x ≠ x} : Set X)ᶜ := by
    ext y; simp
  have hsum : ({x : X | s • x = x} : Set X).ncard + ({x : X | s • x ≠ x} : Set X).ncard
      = Nat.card X := by
    rw [hcompl, add_comm]
    exact Set.ncard_add_ncard_compl _
  rw [Nat.eq_sub_of_add_eq hsum]
  exact even_iff_two_dvd.mpr (Nat.dvd_sub (even_iff_two_dvd.mp hX) hmoved)

/-! ## The main statement -/

/-- **An involution fixing a point forces `(q - 1) / 2` to be even.**

Under the Zassenhaus hypotheses `Work.GW2.ZassHyps2 G X q` with `q` odd, the existence of an
involution `s` with a fixed point `x` implies `2 ∣ (q - 1) / 2`.  The involution then fixes
exactly two points `x ≠ y`, so it lies in the two-point stabilizer `G_x ⊓ G_y` of order
`(q - 1) / 2`, which is therefore even. -/
theorem two_dvd_of_involution_fixing {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    {q : ℕ} (hZ : Work.GW2.ZassHyps2 G X q) (hodd : Odd q) {s : G} (hs : orderOf s = 2)
    {x : X} (hx : s • x = x) : 2 ∣ (q - 1) / 2 := by
  obtain ⟨hfai, hXcard, hpre, hfix2, hstab⟩ := hZ
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hss : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rwa [hs, pow_two] at h
  -- `Nat.card X = q + 1` is even (`q` is odd)
  have hXeven : Even (Nat.card X) := by
    rw [hXcard]
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + 1, by omega⟩
  -- the fixed points of `s` are even in number: `0` or `2`
  have hFeven : Even (({y : X | s • y = y} : Set X).ncard) :=
    even_ncard_fixedBy_of_involution s hss hXeven
  have hFle : ({y : X | s • y = y} : Set X).ncard ≤ 2 := hfix2 s hs1
  have hFpos : 0 < ({y : X | s • y = y} : Set X).ncard := (Set.ncard_pos).mpr ⟨x, hx⟩
  have hFcard : ({y : X | s • y = y} : Set X).ncard = 2 := by
    obtain ⟨m, hm⟩ := hFeven
    omega
  -- so there is a second fixed point `y ≠ x`
  have hlt : 1 < ({y : X | s • y = y} : Set X).ncard := by rw [hFcard]; norm_num
  obtain ⟨y, hy, hyx⟩ := Set.exists_ne_of_one_lt_ncard hlt x
  have hxy : x ≠ y := fun h => hyx h.symm
  -- `s` lies in the two-point stabilizer `G_x ⊓ G_y`, of order `(q - 1) / 2`
  have hmem : s ∈ (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y : Subgroup G) :=
    ⟨MulAction.mem_stabilizer_iff.mpr hx, MulAction.mem_stabilizer_iff.mpr hy⟩
  have hcard : Nat.card (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y : Subgroup G)
      = (q - 1) / 2 := by
    have h2 := hstab x y hxy
    rw [← h2]
    exact (Nat.mul_div_cancel_left _ (by norm_num : (0 : ℕ) < 2)).symm
  have hdvd := Subgroup.orderOf_dvd_natCard
    (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y : Subgroup G) hmem
  rwa [hs, hcard] at hdvd

end Work.ZASS2
