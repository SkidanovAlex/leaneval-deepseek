import Mathlib
import Submission.Work.CORE3.CosetInvCountAPI

/-!
# CORE3: `|S|` divides the number of involutions whose coset contains exactly one involution

Bender 1981 §3, p. 224: "since `|S| = 8` divides `b₁` (`S` is fixed-point-free on `J₁`)".
This file proves the group-theoretic input in the generality needed here.

`J = J₁ = {y : G | orderOf y = 2 ∧ y ∉ Hh ∧ cosetInvCount Hh y = 1}` is the set of involutions
outside `Hh` whose coset `y Hh` contains exactly one involution.  If `S ≤ Hh` is a `2`-subgroup
containing an involution `t` with `C_G(t) ≤ Hh` (in the application `S = B.S` is the Sylow
`2`-subgroup of order `8`, `t = B.t` and `Hh = B.Hhat ⊇ C(t) = B.H`), then `S` acts on `J` by
conjugation (`s • y = s y s⁻¹` — well defined because `S ≤ Hh` normalizes `Hh`, so that
`Work.CORE3.cosetInvCount_conj` applies) and the action is free:

* if `y ∈ J` and `1 ≠ s ∈ S` commute, then `S` being a `2`-group gives a power `w ∈ ⟨s⟩ ≤ S` of
  order `2` commuting with `y` (`Work.CORE3.exists_mem_zpowers_orderOf_eq_two`);
* `w = t` puts `y ∈ C_G(t) ≤ Hh`, contradicting `y ∉ Hh`;
* `w ≠ t` makes `y * w` a second involution of the coset `y Hh`, contradicting
  `cosetInvCount Hh y = 1` (`Work.CORE3.two_le_cosetInvCount_of`).

A free action has orbits of size `|S|`, so `|S|` divides `|J|`
(`MulAction.selfEquivOrbitsQuotientProd`).
-/

namespace Work.CORE3

open Subgroup
open Work.GW2

set_option linter.style.haveILetI false

/-- A `2`-subgroup `S ≤ Hh` containing an involution `t` whose centralizer lies in `Hh` acts
freely by conjugation on the involutions `y ∉ Hh` whose coset contains exactly one involution;
hence the order of `S` divides their number. -/
theorem FreeActionDvdJ {G : Type} [Group G] [Finite G] (Hh S : Subgroup G) (t : G)
    (hSHh : S ≤ Hh) (hS2 : IsPGroup 2 ↥S) (htS : t ∈ S) (ht2 : orderOf t = 2)
    (hCt : Subgroup.centralizer ({t} : Set G) ≤ Hh) :
    Nat.card ↥S ∣
      {y : G | orderOf y = 2 ∧ y ∉ Hh ∧ cosetInvCount Hh y = 1}.ncard := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let J : Set G := {y : G | orderOf y = 2 ∧ y ∉ Hh ∧ cosetInvCount Hh y = 1}
  -- the members of `J`, unfolded
  have hJmem : ∀ y : G, y ∈ J ↔ orderOf y = 2 ∧ y ∉ Hh ∧ cosetInvCount Hh y = 1 :=
    fun y => Iff.rfl
  -- every element of `S` lies in the normalizer of `Hh`, because `S ≤ Hh`
  have hSN : S ≤ Subgroup.normalizer (Hh : Set G) :=
    Subgroup.le_normalizer_iff.mpr fun h hh k hk =>
      Hh.mul_mem (Hh.mul_mem (hSHh hh) hk) (Hh.inv_mem (hSHh hh))
  -- the conjugation action of `S` preserves `J`
  have hconj : ∀ (s : ↥S) (y : ↥J), (s : G) * (y : G) * (s : G)⁻¹ ∈ J := by
    intro s y
    obtain ⟨hy2, hyHh, hyc⟩ := (hJmem (y : G)).mp y.2
    refine (hJmem _).mpr ⟨?_, ?_, ?_⟩
    · change orderOf ((s : G) * (y : G) * (s : G)⁻¹) = 2
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hy2
    · intro hmem
      refine hyHh ?_
      have hconj' : (s : G)⁻¹ * ((s : G) * (y : G) * (s : G)⁻¹) * (s : G) = (y : G) := by
        group
      rw [← hconj']
      exact Hh.mul_mem (Hh.mul_mem (Hh.inv_mem (hSHh s.2)) hmem) (hSHh s.2)
    · rw [cosetInvCount_conj Hh (hSN s.2) (y : G)]
      exact hyc
  letI : SMul ↥S ↥J := ⟨fun s y => ⟨(s : G) * (y : G) * (s : G)⁻¹, hconj s y⟩⟩
  letI : MulAction ↥S ↥J :=
    { one_smul := fun y => Subtype.ext (by
        change (1 : G) * (y : G) * (1 : G)⁻¹ = (y : G)
        group)
      mul_smul := fun s s' y => Subtype.ext (by
        change ((s : G) * (s' : G)) * (y : G) * ((s : G) * (s' : G))⁻¹ =
          (s : G) * ((s' : G) * (y : G) * (s' : G)⁻¹) * (s : G)⁻¹
        group) }
  -- the action is free: no nontrivial `s ∈ S` commutes with an element of `J`
  have hstab : ∀ b : ↥J, MulAction.stabilizer ↥S b = ⊥ := by
    intro b
    rw [Subgroup.eq_bot_iff_forall]
    intro s hs
    have hfix : (s : G) * (b : G) * (s : G)⁻¹ = (b : G) :=
      congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hs)
    by_contra hs1
    have hsG1 : (s : G) ≠ 1 := fun h => hs1 (Subtype.ext h)
    have hbs : (b : G) * (s : G) = (s : G) * (b : G) := by
      have h1 := congrArg (fun z : G => z * (s : G)) hfix
      rw [show (s : G) * (b : G) * (s : G)⁻¹ * (s : G) = (s : G) * (b : G) from by group] at h1
      exact h1.symm
    -- `s` has even order, so `⟨s⟩ ≤ S` contains an involution `w` commuting with `b`
    have heven : 2 ∣ orderOf (s : G) := by
      rw [Subgroup.orderOf_coe]
      exact hS2.dvd_orderOf hs1
    obtain ⟨w, hwz, hw2⟩ := exists_mem_zpowers_orderOf_eq_two hsG1 heven
    have hwS : w ∈ S := Subgroup.zpowers_le.mpr s.2 hwz
    have hwHh : w ∈ Hh := hSHh hwS
    have hcomm : (b : G) * w = w * (b : G) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwz
      have hcs : Commute (b : G) (s : G) := hbs
      have hck := hcs.zpow_right k
      rwa [hk] at hck
    by_cases hwt : w = t
    · -- `w = t`: then `b` centralizes `t`, so `b ∈ C_G(t) ≤ Hh`
      have hmem : (b : G) ∈ Subgroup.centralizer ({t} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        rw [← hwt]
        exact hcomm.symm
      exact ((hJmem (b : G)).mp b.2).2.1 (hCt hmem)
    · -- `w ≠ t`: `b` and `b * w` are two involutions of the coset `b Hh`
      obtain ⟨hb2, hbHh, hbc⟩ := (hJmem (b : G)).mp b.2
      have hsq : ((b : G) * w) ^ 2 = 1 := by
        rw [Commute.mul_pow hcomm]
        have hb2' : (b : G) ^ 2 = 1 := by
          have h := pow_orderOf_eq_one (b : G)
          rwa [hb2] at h
        have hw2' : w ^ 2 = 1 := by
          have h := pow_orderOf_eq_one w
          rwa [hw2] at h
        rw [hb2', hw2', mul_one]
      have h1 : orderOf ((b : G) * w) = 2 := by
        refine orderOf_eq_prime hsq ?_
        intro h1eq
        have hw_eq : w = (b : G)⁻¹ := by
          have h := congrArg (fun z : G => (b : G)⁻¹ * z) h1eq
          simpa using h
        have hcontra : (b : G) ∈ Hh := by
          have := Hh.inv_mem (hw_eq ▸ hwHh)
          simpa using this
        exact hbHh hcontra
      have hne : (b : G) * w ≠ (b : G) := by
        intro heq
        have hw1 : w = 1 := by
          have h := congrArg (fun z : G => (b : G)⁻¹ * z) heq
          simpa using h
        rw [hw1, orderOf_one] at hw2
        exact absurd hw2 (by norm_num)
      have h2 : (b : G)⁻¹ * ((b : G) * w) ∈ Hh := by
        rw [inv_mul_cancel_left]
        exact hwHh
      have h3 : (b : G)⁻¹ * (b : G) ∈ Hh := by
        rw [inv_mul_cancel]
        exact Hh.one_mem
      have hle := two_le_cosetInvCount_of Hh hb2 h3 h1 h2 hne.symm
      omega
  -- a free action has orbits of size `|S|`
  have hcard : Nat.card ↥J = Nat.card (Quotient (MulAction.orbitRel ↥S ↥J)) * Nat.card ↥S := by
    rw [Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd (G := ↥S) (X := ↥J) hstab),
      Nat.card_prod]
  have hdvd : Nat.card ↥S ∣ Nat.card ↥J := ⟨_, by rw [hcard, Nat.mul_comm]⟩
  rw [Nat.card_coe_set_eq] at hdvd
  exact hdvd

end Work.CORE3
