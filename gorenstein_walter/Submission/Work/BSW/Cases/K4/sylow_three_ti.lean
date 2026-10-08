import Mathlib
import Submission.Work.BSW.Defs
import Submission.Work.BSW.Basic
import Submission.Work.BSW.Cases.K4.Setup
import Submission.Work.BSW.Cases.K4.CardSup
import Submission.Work.BSW.Cases.K4.exists_not_mem_centralizer_of_isPGroup

namespace Work.BSW.Cases.K4

open Subgroup Work.GW2

open scoped Pointwise

/-! ## Auxiliary lemmas for `sylow_three_ti`

The Sylow `3`-subgroups of a group of order `360` have order `9`, so two distinct of them
intersect trivially unless the intersection has order `3`.  The latter cannot happen: if `x ≠ 1`
lies in `Q ⊓ Q^g` then `orderOf x` is `3` or `9`; in the second case `⟨x⟩ = Q = Q^g`, and in the
first case `C_G(x) = Q`, so `Q^g ≤ C_G(x) = Q` and `Q^g = Q`.  Either way `g ∈ N_G(Q)`.

The key input is that `C_G(x) = Q` for `x ∈ Q` of order `3`, which uses that `G` has no element of
order `15`. -/

/-- `n₅ = 36` and `|G| = 360` give `|N_G(P)| = 360 / 36 = 10` for a Sylow `5`-subgroup `P`: the
number of Sylow `5`-subgroups is the index of `N_G(P)`. -/
theorem card_normalizer_sylow_five {G : Type} [Group G] [Finite G]
    (hG : Nat.card G = 360)
    (h5 : Nat.card (Sylow 5 G) = 36) (P : Sylow 5 G) :
    Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G)) = 10 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Finite (Sylow 5 G) := inferInstance
  have hidx : (Subgroup.normalizer ((P : Subgroup G) : Set G)).index = 36 := by
    have h := Sylow.card_eq_index_normalizer P
    rw [h5] at h
    exact h.symm
  have hmul := Subgroup.card_mul_index (Subgroup.normalizer ((P : Subgroup G) : Set G))
  rw [hidx, hG] at hmul
  omega

/-- In a group `G` of order `360` in which every Sylow `5`-subgroup has normalizer of order `10`,
there is no element of order `15`.

Indeed if `orderOf z = 15` then `y = z ^ 3` has order `5`, so `H = ⟨y⟩` has order `5 = |G|₅` and
is a Sylow `5`-subgroup of `G`; `z` commutes with `y`, hence with every element of `H`, so
`z ∈ C_G(H) ≤ N_G(H)`, whose order is `10`.  But then `orderOf z = 15` divides `10`. -/
theorem orderOf_ne_fifteen {G : Type} [Group G] [Finite G]
    (hG : Nat.card G = 360)
    (hN5 : ∀ P : Sylow 5 G, Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G)) = 10) :
    ∀ z : G, orderOf z ≠ 15 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro z hz
  have hy : orderOf (z ^ 3) = 5 := by
    rw [orderOf_pow, hz]
    norm_num
  have hcard : Nat.card ↥(Subgroup.zpowers (z ^ 3)) = 5 := by
    rw [Nat.card_zpowers, hy]
  -- `⟨z ^ 3⟩` is a Sylow `5`-subgroup
  have hp : IsPGroup 5 ↥(Subgroup.zpowers (z ^ 3)) :=
    IsPGroup.of_card (p := 5) (n := 1) (by rw [hcard]; norm_num)
  have hidx : ¬ 5 ∣ (Subgroup.zpowers (z ^ 3)).index := by
    have hmul := Subgroup.card_mul_index (Subgroup.zpowers (z ^ 3))
    rw [hcard, hG] at hmul
    rintro ⟨k, hk⟩
    omega
  let P : Sylow 5 G := hp.toSylow hidx
  -- `z` centralizes `⟨z ^ 3⟩ = P`
  have hcent : z ∈ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
    have hPcoe : ((P : Subgroup G) : Set G) = ((Subgroup.zpowers (z ^ 3)) : Set G) := rfl
    rw [hPcoe, Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (((Commute.refl z).pow_right 3).zpow_right n).symm
  have hN : z ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ hcent
  have hdvd : orderOf z ∣ Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G)) :=
    orderOf_dvd_natCard_of_mem hN
  rw [hN5 P, hz] at hdvd
  norm_num at hdvd

/-- In the `|K| = 4` case of `BSW` with `|G| = 360`, an element `x` of order `3` of a Sylow
`3`-subgroup `Q` of `G` has centralizer `Q`.

`Q` is abelian of order `9`, so `9 ∣ |C_G(x)|`, and `|C_G(x)| ∣ |G| = 360`, so `|C_G(x)| = 9m`
with `m ∣ 40`.  `m` is odd: an involution `w ∈ C_G(x)` would make `x` an element of `C_G(w)`, and
in the `|K| = 4` case every involution centralizer has order `8`, so `3 = orderOf x` would divide
`8`.  And `m ≠ 5`: an element `y` of order `5` in `C_G(x)` commutes with `x`, so `x * y` has order
`15`, excluded by `h15`.  Hence `m = 1`, `|C_G(x)| = 9 = |Q|`, and `Q ≤ C_G(x)` gives
`C_G(x) = Q`. -/
theorem centralizer_of_orderOf_eq_three {G : Type} [Group G] [Finite G]
    {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hK4 : Nat.card ↥K = 4) (hG : Nat.card G = 360)
    (h15 : ∀ z : G, orderOf z ≠ 15)
    (Q : Sylow 3 G) {x : G} (hxQ : x ∈ (Q : Subgroup G)) (hx3 : orderOf x = 3) :
    Subgroup.centralizer ({x} : Set G) = (Q : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hQcard : Nat.card ↥(Q : Subgroup G) = 9 := by
    rw [Sylow.card_eq_multiplicity, hG]
    norm_num [Nat.factorization]
  haveI : IsMulCommutative ↥(Q : Subgroup G) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := ↥(Q : Subgroup G))
      (by rw [hQcard]; norm_num)
  -- `Q` is abelian and contains `x`, so `Q ≤ C_G(x)`
  have hQle : (Q : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := ↥(Q : Subgroup G))).comm ⟨y, hy⟩ ⟨x, hxQ⟩)
  have h9dvd : 9 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set G)) := by
    rw [← hQcard]
    exact Subgroup.card_dvd_of_le hQle
  have hdvd360 : Nat.card ↥(Subgroup.centralizer ({x} : Set G)) ∣ 360 := by
    have hh := Subgroup.card_dvd_of_le (H := Subgroup.centralizer ({x} : Set G)) (K := ⊤) le_top
    rwa [Subgroup.card_top, hG] at hh
  obtain ⟨m, hm⟩ := h9dvd
  have hm0 : 0 < m := by
    have hpos : 0 < 9 * m := by rw [← hm]; exact Nat.card_pos
    exact Nat.pos_of_mul_pos_left hpos
  have hmdvd : m ∣ 40 := by
    obtain ⟨k, hk⟩ := hdvd360
    rw [hm] at hk
    have h : 9 * (m * k) = 9 * 40 := by
      rw [← mul_assoc, ← hk]
    exact ⟨k, (Nat.eq_of_mul_eq_mul_left (by norm_num) h).symm⟩
  -- `m` is odd: `C_G(x)` contains no involution
  have hmnot2 : ¬ 2 ∣ m := by
    rintro ⟨m', hm'⟩
    have h2C : 2 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set G)) :=
      ⟨9 * m', by rw [hm, hm']; ring⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fintype ↥(Subgroup.centralizer ({x} : Set G)) := Fintype.ofFinite _
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card
      (G := ↥(Subgroup.centralizer ({x} : Set G))) 2 (by simpa using h2C)
    have hwG : orderOf (w : G) = 2 := by rw [Subgroup.orderOf_coe, hw]
    have hxmem : x ∈ Subgroup.centralizer ({(w : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp w.2).symm
    have h3d8 := orderOf_dvd_natCard_of_mem hxmem
    rw [card_centralizer_of_orderOf_eq_two h hK4 hwG, hx3] at h3d8
    norm_num at h3d8
  -- `m ≠ 5`: an element of order `5` in `C_G(x)` would give an element of order `15`
  have hmne5 : m ≠ 5 := by
    intro hm5
    have h5C : 5 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set G)) := by
      rw [hm, hm5]
      norm_num
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    haveI : Fintype ↥(Subgroup.centralizer ({x} : Set G)) := Fintype.ofFinite _
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card
      (G := ↥(Subgroup.centralizer ({x} : Set G))) 5 (by simpa using h5C)
    have hyG : orderOf (y : G) = 5 := by rw [Subgroup.orderOf_coe, hy]
    have hcomm : Commute x (y : G) := (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm
    have h15' : orderOf (x * (y : G)) = 15 := by
      have hh := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx3, hyG]; norm_num)
      rw [hx3, hyG] at hh
      norm_num at hh
      exact hh
    exact h15 _ h15'
  have hm1 : m = 1 := by
    have hm40 : m ≤ 40 := Nat.le_of_dvd (by norm_num) hmdvd
    interval_cases m <;> norm_num at *
  have hCcard : Nat.card ↥(Subgroup.centralizer ({x} : Set G)) = 9 := by
    rw [hm, hm1, mul_one]
  refine (Subgroup.eq_of_le_of_card_ge hQle ?_).symm
  rw [hCcard, hQcard]

/-- In the `|K| = 4`, `|G| = 360` case of BSW, the Sylow `3`-subgroup is TI with respect to its
normalizer: `Q ⊓ Q^g = 1` for `g ∉ N_G(Q)` (Bender 3.7).  The extra hypothesis
`h5 : Nat.card (Sylow 5 G) = 36` is proved in
`Work.BSW.Cases.K4.natCard_sylow_five_eq_thirtysix`.

Strategy (`Work.BSW.Cases.K4.Setup` has the `|K| = 4` API; `hN` gives `n₃ = 10`):

* `n₅ = 36` gives `|N_G(P)| = 10` for a Sylow `5`-subgroup `P`; `C_G(P) ≤ N_G(P)` has order
  divisible by `5` and is not all of `N_G(P)` (otherwise `P ≤ Z(N_G(P))` and Burnside's
  normal-`p`-complement result, e.g. `Work.BSW.Cases.K4.exists_not_mem_centralizer_of_isPGroup`,
  contradicts simplicity), so `|C_G(P)| = 5`.  Hence there is **no element of order `15`** (such an
  `x` has `⟨x³⟩` a Sylow `5`-subgroup and `x ∈ C_G(⟨x³⟩)`).
* For `u ∈ Q` of order `3`: `Q` is abelian of order `9`, so `Q ≤ C_G(u)` and `9 ∣ |C_G(u)|`; also
  `|C_G(u)| ∣ 360`, so `|C_G(u)| = 9m` with `m ∣ 40`.  `m` is odd: an involution `w ∈ C_G(u)` would
  give `u ∈ C_G(w)`, of order `8`, and `3 ∤ 8`.  `m ≠ 5`: `|C_G(u)| = 45` would contain a Sylow
  `5`-subgroup `P` of `G` with `u ∈ C_G(P)`, but `|C_G(P)| = 5`.  Hence `m = 1` and
  **`C_G(u) = Q`**.
* If `x ∈ Q ⊓ Q^g` is not `1`, then `x ∈ Q` has order `3` or `9`.  In the first case `C_G(x) = Q`,
  and `Q^g` (abelian of order `9`, containing `x`) lies in `C_G(x) = Q`, so `Q^g = Q`, a
  contradiction.  In the second case `⟨x⟩ = Q` and `C_G(x) = C_G(⟨x⟩) = C_G(Q) = Q` (`hC`), and the
  same argument applies. -/
theorem sylow_three_ti {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hK4 : Nat.card ↥K = 4) (hG : Nat.card G = 360)
    (h5 : Nat.card (Sylow 5 G) = 36)
    (Q : Sylow 3 G) (hN : Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G)) = 36)
    (hC : Subgroup.centralizer ((Q : Subgroup G) : Set G) = (Q : Subgroup G))
    (g : G) (hg : g ∉ Subgroup.normalizer ((Q : Subgroup G) : Set G)) :
    (Q : Subgroup G) ⊓ Work.GW2.conjSub g (Q : Subgroup G) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h15 : ∀ z : G, orderOf z ≠ 15 :=
    orderOf_ne_fifteen hG (card_normalizer_sylow_five hG h5)
  by_contra hne
  have hQcard : Nat.card ↥(Q : Subgroup G) = 9 := by
    rw [Sylow.card_eq_multiplicity, hG]
    norm_num [Nat.factorization]
  haveI : IsMulCommutative ↥(Q : Subgroup G) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := ↥(Q : Subgroup G))
      (by rw [hQcard]; norm_num)
  have hconjcard : Nat.card ↥(Work.GW2.conjSub g (Q : Subgroup G)) = 9 := by
    rw [Work.GW2.conjSub,
      Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective, hQcard]
  obtain ⟨x, hxQ, hxconj, hx1⟩ :
      ∃ x : G, x ∈ (Q : Subgroup G) ∧ x ∈ Work.GW2.conjSub g (Q : Subgroup G) ∧ x ≠ 1 := by
    haveI : Nontrivial ↥((Q : Subgroup G) ⊓ Work.GW2.conjSub g (Q : Subgroup G)) := by
      rw [Subgroup.nontrivial_iff_ne_bot]
      exact hne
    obtain ⟨y, hy1⟩ := exists_ne (1 : ↥((Q : Subgroup G) ⊓ Work.GW2.conjSub g (Q : Subgroup G)))
    exact ⟨(y : G), y.2.1, y.2.2, fun h1 => hy1 (Subtype.ext h1)⟩
  have hx9 : orderOf x ∣ 9 := by
    have hh := orderOf_dvd_natCard_of_mem hxQ
    rwa [hQcard] at hh
  have hcases : orderOf x = 3 ∨ orderOf x = 9 := by
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 2)).mp (by simpa using hx9)
    interval_cases k
    · exfalso
      exact hx1 (orderOf_eq_one_iff.mp (by simpa using hk))
    · exact Or.inl (by simpa using hk)
    · exact Or.inr (by simpa using hk)
  have hconj_eq : Work.GW2.conjSub g (Q : Subgroup G) = (Q : Subgroup G) := by
    rcases hcases with hx3 | hx9'
    · -- `x` has order `3`: `C_G(x) = Q` and `Q^g` is abelian of order `9`, so `Q^g ≤ Q`
      have hcent := centralizer_of_orderOf_eq_three h hK4 hG h15 Q hxQ hx3
      have h0 : Work.GW2.conjSub g (Q : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
        haveI : IsMulCommutative ↥(Work.GW2.conjSub g (Q : Subgroup G)) :=
          IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
            (G := ↥(Work.GW2.conjSub g (Q : Subgroup G))) (by rw [hconjcard]; norm_num)
        intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := ↥(Work.GW2.conjSub g (Q : Subgroup G)))).comm
            ⟨z, hz⟩ ⟨x, hxconj⟩)
      have hle : Work.GW2.conjSub g (Q : Subgroup G) ≤ (Q : Subgroup G) := by
        rw [hcent] at h0
        exact h0
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [hconjcard, hQcard])
    · -- `x` has order `9`: `⟨x⟩ = Q` and `x ∈ Q^g`, so `Q^g = ⟨x⟩ = Q`
      have hzpx : Subgroup.zpowers x = (Q : Subgroup G) := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxQ) ?_
        rw [Nat.card_zpowers, hx9', hQcard]
      have hzpc : Subgroup.zpowers x = Work.GW2.conjSub g (Q : Subgroup G) := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxconj) ?_
        rw [Nat.card_zpowers, hx9', hconjcard]
      rw [← hzpc, hzpx]
  have hsmul : g • Q = Q := Sylow.ext (by
    have hbridge : ((g • Q : Sylow 3 G) : Subgroup G) = Work.GW2.conjSub g (Q : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      rfl
    rw [hbridge, hconj_eq])
  exact hg ((Sylow.smul_eq_iff_mem_normalizer).mp hsmul)

end Work.BSW.Cases.K4
