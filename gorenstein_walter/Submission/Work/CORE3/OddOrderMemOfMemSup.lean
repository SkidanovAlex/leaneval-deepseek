import Mathlib
import Submission.Work.CORE3.Defs

namespace Work.CORE3

open Pointwise

/-- If `V` is a four-group, `U` has odd order, `V` and `U` intersect trivially and `V`
centralizes `U`, then every element of odd order in `V ⊔ U` already lies in `U`.

Indeed `V` commutes with `U`, so `V ⊔ U = V * U` and any `x ∈ V ⊔ U` can be written
`x = v * u` with `v ∈ V`, `u ∈ U`.  For `m = orderOf x` odd we get `v ^ m = v` (as `v ^ 2 = 1`),
hence `1 = x ^ m = v * u ^ m`, so `v = (u ^ m)⁻¹ ∈ U`, and `v ∈ V ⊓ U = ⊥` forces `v = 1`. -/
theorem OddOrderMemOfMemSup {G : Type} [Group G] [Finite G] {V U : Subgroup G} {x : G}
    (hV4 : Work.GW2.IsFourGroup V) (hUodd : Odd (Nat.card U))
    (hdisj : V ⊓ U = ⊥) (hVU : V ≤ Subgroup.centralizer (U : Set G))
    (hx : x ∈ V ⊔ U) (hxo : Odd (orderOf x)) : x ∈ U := by
  -- `V` centralizes `U`, hence `V ≤ N_G(U)` and `V ⊔ U = V * U`.
  have hcoe : (↑(V ⊔ U) : Set G) = (V : Set G) * (U : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right V U
      (hVU.trans (Subgroup.centralizer_le_normalizer _))
  have hx' : x ∈ (V : Set G) * (U : Set G) := by rw [← hcoe]; exact hx
  rw [Set.mem_mul] at hx'
  obtain ⟨v, hv, u, hu, rfl⟩ := hx'
  -- `v` and `u` commute, and `v ^ 2 = 1`.
  have hcomm : Commute v u := ((Subgroup.mem_centralizer_iff.mp (hVU hv)) u hu).symm
  have hv2 : v ^ 2 = 1 := hV4.2 v hv
  obtain ⟨k, hk⟩ := hxo
  -- `v ^ orderOf (v * u) = v`, since `v ^ 2 = 1` and the order is odd.
  have hvn : v ^ orderOf (v * u) = v := by
    rw [hk, pow_succ, pow_mul, hv2, one_pow, one_mul]
  have h1 : (v * u) ^ orderOf (v * u) = v ^ orderOf (v * u) * u ^ orderOf (v * u) :=
    hcomm.mul_pow _
  -- `1 = (v * u) ^ orderOf (v * u) = v * u ^ orderOf (v * u)`.
  have hprod : v * u ^ orderOf (v * u) = 1 := by
    have hm : v ^ orderOf (v * u) * u ^ orderOf (v * u) = 1 := by
      rw [← h1]; exact pow_orderOf_eq_one _
    rwa [hvn] at hm
  -- Thus `v = (u ^ orderOf (v * u))⁻¹ ∈ U`, and `v ∈ V ⊓ U = ⊥`.
  have hvU : v ∈ U := by
    rw [eq_inv_of_mul_eq_one_left hprod]
    exact U.inv_mem (U.pow_mem hu _)
  have hv1 : v = 1 := by
    have hmem : v ∈ V ⊓ U := ⟨hv, hvU⟩
    rw [hdisj] at hmem
    exact Subgroup.mem_bot.mp hmem
  rw [hv1, one_mul]
  exact hu

end Work.CORE3
