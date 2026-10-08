import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic

/-!
# `I_K(s) = {1}` when `s` centralizes `K` of odd order

`Work.GW2.invSet K s = {x ∈ K | x^s = x⁻¹}` is Bender's set `I_K(s)`.  If `s` centralizes `K`,
then for every `x ∈ K` the defining relation `s * x * s⁻¹ = x⁻¹` collapses to `x = x⁻¹`, i.e.
`x ^ 2 = 1`.  Since `|K|` is odd, `orderOf x ∣ 2` and `orderOf x ∣ |K|` force `orderOf x = 1`,
so the only member of `I_K(s)` is the identity.
-/

namespace Work.CORE3

/-- If `s` centralizes a subgroup `K` of odd order, then `I_K(s)` is the trivial set `{1}`. -/
theorem ncard_invSet_eq_one_of_le_centralizer {G : Type} [Group G] (K : Subgroup G) (s : G)
    (hs : s ∈ Subgroup.centralizer (K : Set G)) (hK : Odd (Nat.card K)) :
    (Work.GW2.invSet K s).ncard = 1 := by
  have hset : Work.GW2.invSet K s = {1} := by
    rw [Set.eq_singleton_iff_unique_mem]
    refine ⟨Work.CORE2A.one_mem_invSet K.one_mem, ?_⟩
    intro x hx
    obtain ⟨hxK, hxinv⟩ := hx
    -- `s` commutes with `x`, so `s * x * s⁻¹ = x`
    have hcomm : x * s = s * x := (Subgroup.mem_centralizer_iff.mp hs) x hxK
    have hx1 : s * x * s⁻¹ = x := by rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    -- hence `x = x⁻¹`, i.e. `x ^ 2 = 1`
    have hxeq : x = x⁻¹ := hx1.symm.trans hxinv
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      exact eq_inv_iff_mul_eq_one.mp hxeq
    -- `orderOf x` divides both `2` and the odd number `Nat.card K`, hence is `1`
    have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
    have hdvdK : orderOf x ∣ Nat.card K := K.orderOf_dvd_natCard hxK
    have hcop : Nat.Coprime 2 (Nat.card K) := Nat.coprime_two_left.mpr hK
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvdK)
  rw [hset, Set.ncard_singleton]

end Work.CORE3
