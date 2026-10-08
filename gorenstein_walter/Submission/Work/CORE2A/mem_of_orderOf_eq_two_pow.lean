import Mathlib
import Submission.Work.CORE2A.Defs

namespace Work.CORE2A

/-!
# CORE2A: a `2`-element of `K` inside a `K`-normal subgroup containing a Sylow `2`-subgroup

Let `S` be a Sylow `2`-subgroup of a finite group `G`, let `S ≤ K` be a subgroup, and let
`E ≤ G` be such that `E ∩ K` is normal in `K` and `S ≤ E`.  Then every element of `K` whose
order is a power of `2` already lies in `E`.

The point is that `S ≤ K` makes `S` a Sylow `2`-subgroup of `K` (`Sylow.subtype`), and since
`E ∩ K` is normal in `K` and contains `S`, its index in `K` is odd; equivalently the quotient
`K ⧸ (E ∩ K)` is a group of odd order.  Hence the image of a `2`-element of `K` in that
quotient has order dividing both a power of `2` and an odd number, so is trivial.
-/

theorem mem_of_orderOf_eq_two_pow {G : Type} [Group G] [Finite G] (S : Sylow 2 G) {K E : Subgroup G}
    (hSK : (S : Subgroup G) ≤ K) (hEnorm : (E.subgroupOf K).Normal) (hSE : (S : Subgroup G) ≤ E)
    {x : G} (hx : x ∈ K) {n : ℕ} (hxord : orderOf x = 2 ^ n) : x ∈ E := by
  classical
  -- `S`, viewed inside `K`, is a Sylow `2`-subgroup of `K`.
  let S' : Sylow 2 K := S.subtype hSK
  have hS'co : (S' : Subgroup K) = (S : Subgroup G).subgroupOf K := Sylow.coe_subtype S hSK
  -- `S' ≤ E ∩ K`.
  have hS'le : (S' : Subgroup K) ≤ E.subgroupOf K := by
    intro s hs
    rw [hS'co, Subgroup.mem_subgroupOf] at hs
    rw [Subgroup.mem_subgroupOf]
    exact hSE hs
  -- The index of a Sylow `2`-subgroup is odd, and it is a multiple of the index of `E ∩ K`.
  have hS'index : ¬ 2 ∣ (S' : Subgroup K).index := Sylow.not_dvd_index S'
  have hNindex : ¬ 2 ∣ (E.subgroupOf K).index :=
    fun h => hS'index (h.trans (Subgroup.index_dvd_of_le hS'le))
  -- The image of `x` in `K ⧸ (E ∩ K)`.
  let xK : K := ⟨x, hx⟩
  have hxKord : orderOf xK = 2 ^ n := by
    rw [← Subgroup.orderOf_coe xK]
    exact hxord
  let y : K ⧸ (E.subgroupOf K) := QuotientGroup.mk' (E.subgroupOf K) xK
  -- Its order divides both `2 ^ n` and the odd number `[K : E ∩ K]`.
  have hydvd2 : orderOf y ∣ 2 ^ n := by
    rw [← hxKord]
    exact orderOf_map_dvd (QuotientGroup.mk' (E.subgroupOf K)) xK
  have hydvdidx : orderOf y ∣ (E.subgroupOf K).index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard y
  have hodd : Odd (orderOf y) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact fun h => hNindex (h.trans hydvdidx)
  -- Hence the image is trivial, i.e. `x ∈ E ∩ K`.
  have hy1 : y = 1 := by
    rw [← orderOf_eq_one_iff]
    exact ((hodd.coprime_two_right).pow_right n).eq_one_of_dvd hydvd2
  have hxKN : xK ∈ E.subgroupOf K := by
    rw [← QuotientGroup.ker_mk' (E.subgroupOf K), MonoidHom.mem_ker]
    exact hy1
  have : ((xK : K) : G) ∈ E := Subgroup.mem_subgroupOf.mp hxKN
  simpa using this

end Work.CORE2A
