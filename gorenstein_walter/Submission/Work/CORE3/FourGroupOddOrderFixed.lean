import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.FourGroupOrderThreeFixed

/-!
# CORE3: an element of odd order normalising a four-group acts fixed-point-freely

`Work.CORE3.FourGroupOddOrderFixed`: if `V ≤ G` is a Klein four-group (`|V| = 4` with every
element an involution), `x ∈ N_G(V)` has **odd** order and `x` does *not* centralize `V`,
then `C_V(x) = V ⊓ C_G(x) = ⊥`.

Informal proof.  Suppose `w ∈ V`, `w ≠ 1`, is centralized by `x`.  Since `x ∉ C_G(V)` there is
`z ∈ V` with `x z x⁻¹ ≠ z`; automatically `z ≠ 1` and `z ≠ w`, so the four-group is
`V = {1, w, z, w z}` (see `Work.CORE3.fourGroup_eq_four`).  As `x` normalizes `V`, the element
`x z x⁻¹` lies in `V`, and it is not `1` (else `z = 1`) and not `w` (else `z = w`), hence it is
`z` — impossible — or `w z`.  Therefore `x z x⁻¹ = w z`, so
`x² z x⁻² = (x w x⁻¹)(x z x⁻¹) = w · (w z) = z`, while `x² w x⁻² = w` and
`x² (w z) x⁻² = (w z)` by multiplicativity.  Thus `x²` centralizes every element of `V`, i.e.
`x² ∈ C_G(V)`.  Finally `orderOf x` is odd, say `orderOf x = 2k + 1`; then
`x = x ^ (2k + 2) = (x²)^(k+1)`, a power of `x²`, so `x ∈ C_G(V)`, contradicting `x ∉ C_G(V)`.

Hence `C_V(x)` is trivial.

Note that this *cannot* be reduced to the order-`3` case `Work.CORE3.FourGroupOrderThreeFixed`:
when `9 ∣ orderOf x` an element of order `3` in `⟨x⟩` may well centralize `V`.
-/

namespace Work.CORE3

open Subgroup

theorem FourGroupOddOrderFixed {G : Type} [Group G] [Finite G] {V : Subgroup G} {x : G}
    (hV4 : Work.GW2.IsFourGroup V)
    (hxN : x ∈ Subgroup.normalizer (V : Set G))
    (hxo : Odd (orderOf x))
    (hxnc : x ∉ Subgroup.centralizer (V : Set G)) :
    V ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro w hw
  rw [Subgroup.mem_inf] at hw
  obtain ⟨hwV, hwC⟩ := hw
  by_contra hw1
  -- `x` commutes with `w`
  have hwx : x * w = w * x := (Subgroup.mem_centralizer_iff.mp hwC) x (by simp)
  have hxw : x * w * x⁻¹ = w := by rw [hwx, mul_assoc, mul_inv_cancel, mul_one]
  have hw2 : w * w = 1 := by simpa [pow_two] using hV4.2 w hwV
  -- some `z ∈ V` is moved by conjugation by `x`
  have hxnc' : ∃ v ∈ V, x * v * x⁻¹ ≠ v := by
    by_contra h
    apply hxnc
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : x * v * x⁻¹ = v := by
      by_contra hc
      exact h ⟨v, hv, hc⟩
    calc v * x = (x * v * x⁻¹) * x := by rw [hv']
      _ = x * v := by group
  obtain ⟨z, hzV, hxz⟩ := hxnc'
  have hz1 : z ≠ 1 := by
    intro h
    exact hxz (by rw [h]; simp)
  have hzw : z ≠ w := by
    intro h
    exact hxz (by rw [h]; exact hxw)
  have hVset : (V : Set G) = {1, w, z, w * z} :=
    fourGroup_eq_four hV4.1 hV4.2 hwV hzV hw1 hz1 hzw.symm
  have hzmem : x * z * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxN z).mp hzV
  -- as `x z x⁻¹ ∈ V ∖ {1, w}` and `x z x⁻¹ ≠ z`, we must have `x z x⁻¹ = w * z`
  have hz_eq : x * z * x⁻¹ = w * z := by
    have hm : x * z * x⁻¹ ∈ ({1, w, z, w * z} : Set G) := hVset ▸ hzmem
    rcases (Set.mem_insert_iff.mp hm) with h | h
    · exfalso
      apply hz1
      have hxzeq : x * z = x * 1 := by
        calc x * z = x * z * x⁻¹ * x := by group
          _ = 1 * x := by rw [h]
          _ = x * 1 := by rw [one_mul, mul_one]
      exact mul_left_cancel hxzeq
    · rcases (Set.mem_insert_iff.mp h) with h | h
      · exfalso
        apply hzw
        have hxzeq : x * z = x * w := by
          calc x * z = x * z * x⁻¹ * x := by group
            _ = w * x := by rw [h]
            _ = x * w := hwx.symm
        exact mul_left_cancel hxzeq
      · rcases (Set.mem_insert_iff.mp h) with h | h
        · exact absurd h hxz
        · exact Set.mem_singleton_iff.mp h
  -- `x * x` centralizes all of `V`
  have hx2w : (x * x) * w * (x * x)⁻¹ = w := by
    have e : (x * x) * w * (x * x)⁻¹ = x * (x * w * x⁻¹) * x⁻¹ := by group
    rw [e, hxw, hxw]
  have hx2z : (x * x) * z * (x * x)⁻¹ = z := by
    calc (x * x) * z * (x * x)⁻¹ = x * (x * z * x⁻¹) * x⁻¹ := by group
      _ = x * (w * z) * x⁻¹ := by rw [hz_eq]
      _ = (x * w * x⁻¹) * (x * z * x⁻¹) := by group
      _ = w * (w * z) := by rw [hxw, hz_eq]
      _ = z := by rw [← mul_assoc, hw2, one_mul]
  have hx2c : ∀ y ∈ V, (x * x) * y * (x * x)⁻¹ = y := by
    intro y hy
    have hy' : y ∈ ({1, w, z, w * z} : Set G) := hVset ▸ hy
    rcases (Set.mem_insert_iff.mp hy') with h | h
    · rw [h]; group
    · rcases (Set.mem_insert_iff.mp h) with h | h
      · rw [h]; exact hx2w
      · rcases (Set.mem_insert_iff.mp h) with h | h
        · rw [h]; exact hx2z
        · rw [Set.mem_singleton_iff.mp h]
          have e1 : (x * x) * (w * z) * (x * x)⁻¹ =
              ((x * x) * w * (x * x)⁻¹) * ((x * x) * z * (x * x)⁻¹) := by group
          rw [e1, hx2w, hx2z]
  have hx2C : x * x ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := hx2c y hy
    calc y * (x * x) = ((x * x) * y * (x * x)⁻¹) * (x * x) := by rw [h]
      _ = (x * x) * y := by group
  -- `x` is a power of `x * x`, so `x ∈ C_G(V)`: contradiction
  obtain ⟨k, hk⟩ := hxo
  have h1 : x ^ orderOf x = 1 := pow_orderOf_eq_one x
  rw [hk] at h1
  have hpow : x ^ (2 * k + 2) = x := by
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring, pow_succ, h1, one_mul]
  have hx_eq : x = (x * x) ^ (k + 1) := by
    calc x = x ^ (2 * k + 2) := hpow.symm
      _ = x ^ (2 * (k + 1)) := by rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
      _ = (x * x) ^ (k + 1) := by rw [pow_mul, pow_two]
  have hxC : x ∈ Subgroup.centralizer (V : Set G) := by
    rw [hx_eq]
    exact Subgroup.pow_mem _ hx2C (k + 1)
  exact hxnc hxC

end Work.CORE3
