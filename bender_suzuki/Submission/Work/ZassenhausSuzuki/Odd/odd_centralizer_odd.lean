import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs
import Submission.Work.ThmF.Bender.involutionMemConj
import Submission.Work.ZassenhausSuzuki.centralizer_abelian_of_strongly_real

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.Odd.odd_centralizer_odd`

The centraliser of an element of odd order is odd in a group with a split rank-one Zassenhaus
datum `H = Q ⋊ D` whose root group `Q` is a `2`-group.

This follows from Suzuki's Proposition 1, available in the workspace as
`Work.ZassenhausSuzuki.centralizer_le_Q_of_mem_involutions` (the centraliser of an involution of
`H` lies in the `2`-group `Q`), together with `Work.ThmF.Bender.involutionMemConj` (every
involution of `G` lies in a conjugate of `H`): hence the centraliser of *every* involution of `G`
is a `2`-group.

If `y` had odd order and `C_G(y)` contained an involution `z`, then `y ∈ C_G(z)` would have
`2`-power order, so `orderOf y = 1`, i.e. `y = 1`.  Thus `C_G(y)` has no element of order `2`,
and a finite group without an element of order `2` has odd order (Cauchy's theorem).
-/

namespace Work.ZassenhausSuzuki.Odd

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

theorem odd_centralizer_odd (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t) {y : G} (hy1 : y ≠ 1)
    (hodd : Odd (orderOf y)) :
    Odd (Nat.card ↥(Subgroup.centralizer ({y} : Set G))) := by
  classical
  -- Suppose `C_G(y)` has even order; then (Cauchy) it contains an involution.
  refine Nat.not_even_iff_odd.mp fun heven => ?_
  have h2dvd : 2 ∣ Nat.card ↥(Subgroup.centralizer ({y} : Set G)) := even_iff_two_dvd.mp heven
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz2⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer ({y} : Set G))) 2 h2dvd
  -- `z` is an involution commuting with `y`.
  have hz2G : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe, hz2]
  have hzy : (z : G) * y = y * (z : G) := Subgroup.mem_centralizer_singleton_iff.mp z.2
  -- Carry the involution into `H`: `z = g * u * g⁻¹` with `u ∈ H` an involution.
  obtain ⟨g, hg⟩ := Work.ThmF.Bender.involutionMemConj h.hsplit.stronglyEmbedded hz2G
  rw [Submission.Blueprint.conj, Subgroup.mem_map] at hg
  obtain ⟨u, huH, huconj⟩ := hg
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at huconj
  have hu2 : orderOf u = 2 := by
    rw [← Work.ThmF.Bender.orderOf_conj_eq g u, huconj, hz2G]
  -- Suzuki's Proposition 1: the centraliser of an involution of `H` lies in the `2`-group `Q`.
  have hle := Work.ZassenhausSuzuki.centralizer_le_Q_of_mem_involutions h.hsplit h.hzass h.h2
    (u := u) ⟨huH, hu2⟩
  have hgu : g⁻¹ * (z : G) * g = u := by rw [← huconj]; group
  -- `g⁻¹ * y * g` commutes with `u`.
  have hcomm : (g⁻¹ * y * g) * u = u * (g⁻¹ * y * g) := by
    rw [← hgu]
    calc (g⁻¹ * y * g) * (g⁻¹ * (z : G) * g)
        = g⁻¹ * (y * (z : G)) * g := by group
      _ = g⁻¹ * ((z : G) * y) * g := by rw [hzy]
      _ = (g⁻¹ * (z : G) * g) * (g⁻¹ * y * g) := by group
  have hyQ : g⁻¹ * y * g ∈ Q := hle (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
  -- So `orderOf y` divides a power of `2`; being odd, it is `1`.
  obtain ⟨k, hk⟩ := h.h2.exists_orderOf_dvd_pow ⟨g⁻¹ * y * g, hyQ⟩
  rw [Subgroup.orderOf_mk] at hk
  have hperm : orderOf (g⁻¹ * y * g) = orderOf y := by
    simpa using Work.ThmF.Bender.orderOf_conj_eq g⁻¹ y
  have hodd' : Odd (orderOf (g⁻¹ * y * g)) := by rw [hperm]; exact hodd
  have hone : orderOf (g⁻¹ * y * g) = 1 :=
    Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_left.mpr hodd').pow_left k) hk dvd_rfl
  have hg1 : g⁻¹ * y * g = 1 := orderOf_eq_one_iff.mp hone
  exact hy1 (by calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
                  _ = g * 1 * g⁻¹ := by rw [hg1]
                  _ = 1 := by group)

end Work.ZassenhausSuzuki.Odd
