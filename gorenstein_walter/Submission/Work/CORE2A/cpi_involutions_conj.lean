/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE2A)
-/
import Mathlib
import Submission.Work.FUS.thompson_transfer
import Submission.Work.FUS.DihedralFacts.rot_involutions
import Submission.Work.FUS.Dihedral

/-!
# All involutions of `G` are conjugate (Gorenstein–Walter, dihedral Sylow 2-subgroup)

Main result: `Work.CORE2A.cpi_involutions_conj`.

Let `G` be a finite group with a Sylow `2`-subgroup `S` isomorphic to `DihedralGroup n`
(`n ≥ 2`, so `|S| = 2n ≥ 4`), and suppose that `G` has no normal subgroup of index `2`.
Then all involutions of `G` are conjugate.

The mathematical content is the standard "fusion" statement proved with **Thompson's transfer
lemma** (`Work.FUS.thompson_transfer`):

* The reflection sign `Work.FUS.reflSign n : DihedralGroup n →* Multiplicative (ZMod 2)`
  (kernel the rotation subgroup `Work.Dihedral.rot n`) composed with the isomorphism of `S`
  with `DihedralGroup n` is a character `σ` of `S` whose kernel is cyclic.
* If an involution `v ∈ S` had no `G`-conjugate inside `ker σ`, then `σ` evaluated on every
  `S`-conjugate of `v` would be nontrivial, and Thompson's transfer lemma would produce a
  normal subgroup of `G` of index `2`, contradicting the hypothesis.
* Hence some conjugate of `v` lies in `ker σ`, i.e. in the cyclic rotation part. The only
  involutions there are `1` and the central rotation `r (n/2)` (`rot_involutions`, using that
  `n` is even: `|S| = 2^k`); as `v ≠ 1`, that conjugate must be `r (n/2)`.
* Every involution of `G` lies in some Sylow `2`-subgroup, which is conjugate to `S`
  (Sylow's theorem), and conjugation preserves the order, so every involution of `G` is
  conjugate to `e.symm (r (n/2))`.
-/

namespace Work.CORE2A

open Subgroup
open scoped Pointwise

/-- For an involution `x`, the cyclic subgroup `⟨x⟩` is a `2`-group. -/
private lemma isPGroup_zpowers_of_orderOf_eq_two {G : Type*} [Group G] [Finite G] {x : G}
    (hx : orderOf x = 2) : IsPGroup 2 (Subgroup.zpowers x) :=
  IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, hx, pow_one]⟩

/-- Thompson's transfer lemma applied to a Sylow `2`-subgroup `S ≃* DihedralGroup n`: if `G` has
no normal subgroup of index `2`, then every involution of `S` is conjugate to the involution
`e.symm (r (n / 2))` lying in the "rotation" part of `S`. -/
private theorem conj_center_of_sylow {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (n : ℕ)
    (hn2 : 2 ≤ n) (e : (S : Subgroup G) ≃* DihedralGroup n)
    (hnoN : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) :
    ∀ u : (S : Subgroup G), orderOf u = 2 →
      IsConj (u : G) (e.symm (DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) : G) := by
  have hcardS : Nat.card (S : Subgroup G) = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hEven : Even n := Work.FUS.even_of_two_mul_eq_two_pow hn2 (by rw [← hcardS, hk])
  haveI : NeZero n := ⟨by omega⟩
  have hodd : Odd (S : Subgroup G).index := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact S.not_dvd_index
  have hcadd : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
    obtain ⟨c, hc⟩ := hEven
    rw [← Nat.cast_add, show (n / 2 + n / 2 : ℕ) = n from by omega, ZMod.natCast_self]
  have hr2 : (DihedralGroup.r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) ^ 2 = 1 := by
    rw [sq, DihedralGroup.r_mul_r, hcadd, DihedralGroup.r_zero]
  let σ : (S : Subgroup G) →* Multiplicative (ZMod 2) := (Work.FUS.reflSign n).comp e.toMonoidHom
  have hσker : σ.ker = (Work.Dihedral.rot n).comap e.toMonoidHom := by
    ext v
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, σ, MonoidHom.comp_apply]
    rw [← Work.FUS.ker_reflSign n, MonoidHom.mem_ker]
  intro u hu2
  set z : (S : Subgroup G) := e.symm (DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) with hz
  have hzapply : e z = DihedralGroup.r ((n / 2 : ℕ) : ZMod n) := by
    rw [hz, MulEquiv.apply_symm_apply]
  have hkey : ∀ v : (S : Subgroup G), orderOf v = 2 → IsConj (v : G) (z : G) := by
    intro v hv2
    have hv2' : v ^ 2 = 1 := by simpa [hv2] using pow_orderOf_eq_one v
    -- the order of a conjugate of `v`, computed inside `S`
    have hconj_ord : ∀ (g : G) (hh : g * (v : G) * g⁻¹ ∈ (S : Subgroup G)),
        orderOf (⟨g * (v : G) * g⁻¹, hh⟩ : (S : Subgroup G)) = 2 := by
      intro g hh
      rw [Subgroup.orderOf_mk]
      have h5 : orderOf (g * (v : G) * g⁻¹) = orderOf (v : G) :=
        MulEquiv.orderOf_eq (MulAut.conj g) (v : G)
      rw [h5, Subgroup.orderOf_coe, hv2]
    -- a conjugate of `v` inside the rotation part is conjugate to `z`
    have hstep : ∀ (g : G) (hh : g * (v : G) * g⁻¹ ∈ (S : Subgroup G)),
        σ ⟨g * (v : G) * g⁻¹, hh⟩ = 1 → IsConj (v : G) (z : G) := by
      intro g hh h1
      have hrot : e ⟨g * (v : G) * g⁻¹, hh⟩ ∈ Work.Dihedral.rot n := by
        have hmem : (⟨g * (v : G) * g⁻¹, hh⟩ : (S : Subgroup G)) ∈ σ.ker := h1
        rwa [hσker, Subgroup.mem_comap] at hmem
      have hsq : (e ⟨g * (v : G) * g⁻¹, hh⟩) ^ 2 = 1 := by
        rw [← map_pow,
          show (⟨g * (v : G) * g⁻¹, hh⟩ : (S : Subgroup G)) ^ 2 = 1 by
            simpa [hconj_ord g hh] using
              pow_orderOf_eq_one (⟨g * (v : G) * g⁻¹, hh⟩ : (S : Subgroup G)),
          map_one]
      rcases Work.FUS.DihedralFacts.rot_involutions n hEven _ hrot hsq with h2 | h2
      · exfalso
        have h3 : (⟨g * (v : G) * g⁻¹, hh⟩ : (S : Subgroup G)) = 1 := by
          have : e ⟨g * (v : G) * g⁻¹, hh⟩ = e 1 := by rw [h2, map_one]
          exact e.injective this
        have h4 := hconj_ord g hh
        rw [h3, orderOf_one] at h4
        exact absurd h4 (by norm_num)
      · refine isConj_iff.mpr ⟨g, ?_⟩
        have h3 : (⟨g * (v : G) * g⁻¹, hh⟩ : (S : Subgroup G)) = z :=
          e.injective (by rw [h2, hzapply])
        exact congrArg Subtype.val h3
    by_cases hv : e v ∈ Work.Dihedral.rot n
    · have hsq : (e v) ^ 2 = 1 := by rw [← map_pow, hv2', map_one]
      rcases Work.FUS.DihedralFacts.rot_involutions n hEven (e v) hv hsq with h1 | h1
      · exfalso
        have h0 : v = 1 := by
          have : e v = e 1 := by rw [h1, map_one]
          exact e.injective this
        rw [h0, orderOf_one] at hv2
        exact absurd hv2 (by norm_num)
      · have : v = z := by
          rw [hz]
          exact e.injective (by rw [h1, hzapply])
        rw [this]
    · have hσv : σ v ≠ 1 := by
        intro h1
        refine hv ?_
        have h2 : v ∈ σ.ker := h1
        rwa [hσker, Subgroup.mem_comap] at h2
      -- if no conjugate of `v` lay in the rotation part, Thompson transfer would produce a normal
      -- subgroup of index 2, which is excluded
      have hexists : ∃ g : G, ∃ (hh : g * (v : G) * g⁻¹ ∈ (S : Subgroup G)),
          σ ⟨g * (v : G) * g⁻¹, hh⟩ = 1 := by
        by_contra hno
        push_neg at hno
        obtain ⟨N, hN, hidx, -⟩ :=
          Work.FUS.thompson_transfer (S : Subgroup G) hodd σ v hv2 hσv hno
        exact hnoN N hN hidx
      obtain ⟨g, hh, h1⟩ := hexists
      exact hstep g hh h1
  exact hkey u hu2

theorem cpi_involutions_conj {G : Type} [Group G] [Finite G] (S : Sylow 2 G) (n : ℕ)
    (hn : 2 ≤ n) (hiso : Nonempty ((S : Subgroup G) ≃* DihedralGroup n))
    (hnoN : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) :
    ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y := by
  obtain ⟨e⟩ := hiso
  haveI : Finite (Sylow 2 G) := Sylow.finite_of_finiteIndex S
  intro x y hx hy
  have key : ∀ w : G, orderOf w = 2 →
      IsConj w (e.symm (DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) : G) := by
    intro w hw
    obtain ⟨Q, hwQ⟩ : ∃ Q : Sylow 2 G, w ∈ (Q : Subgroup G) := by
      obtain ⟨Q, hQ⟩ := (isPGroup_zpowers_of_orderOf_eq_two hw).exists_le_sylow
      exact ⟨Q, hQ (Subgroup.mem_zpowers w)⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
    have hmem : g⁻¹ * w * g ∈ (S : Subgroup G) := by
      have h1 : w ∈ (MulAut.conj g) • (S : Subgroup G) := by
        rw [← Sylow.coe_subgroup_smul]
        show w ∈ (g • S : Sylow 2 G)
        rw [hg]
        exact hwQ
      have h2 : (MulAut.conj g).symm w ∈ (S : Subgroup G) :=
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp h1
      have h3 : (MulAut.conj g).symm w = g⁻¹ * w * g := by
        have h4 : (MulAut.conj g) ((MulAut.conj g).symm w) = (MulAut.conj g) (g⁻¹ * w * g) := by
          rw [MulEquiv.apply_symm_apply, MulAut.conj_apply]
          group
        exact (MulAut.conj g).injective h4
      rwa [h3] at h2
    have hw2 : orderOf (⟨g⁻¹ * w * g, hmem⟩ : (S : Subgroup G)) = 2 := by
      rw [Subgroup.orderOf_mk]
      have h5 : orderOf (g⁻¹ * w * g) = orderOf w := by
        simpa only [MulAut.conj_apply, inv_inv] using MulEquiv.orderOf_eq (MulAut.conj g⁻¹) w
      rw [h5, hw]
    have hconj1 : IsConj (g⁻¹ * w * g) w := by
      refine isConj_iff.mpr ⟨g, ?_⟩
      group
    have hconj2 : IsConj (g⁻¹ * w * g)
        (e.symm (DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) : G) := by
      simpa using conj_center_of_sylow S n hn e hnoN ⟨g⁻¹ * w * g, hmem⟩ hw2
    exact hconj1.symm.trans hconj2
  exact (key x hx).trans (key y hy).symm

end Work.CORE2A
