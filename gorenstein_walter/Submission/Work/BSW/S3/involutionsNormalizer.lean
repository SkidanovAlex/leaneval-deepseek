import Mathlib
import Submission.Work.BSW.S3.S31setup

/-!
# Bender §3.1 (c): the involutions of `N_G(C_G(x))` are the coset `t · C_G(x)`

Setting: `G` finite with `BSWHyps2 G t s K`, `x ∉ H^G` inverted by `t`, `F = C_G(x)`,
`M = N_G(F)`.  Every involution of `M` inverts `F` (`involution_mem_normalizer_inverts`), so for
an involution `u ∈ M` the product `u * t` centralizes `F`, i.e. lies in `F`; hence
`u = t * (u*t)⁻¹ ∈ tF`.  Conversely `t * c` is an involution of `M` for every `c ∈ F`.
-/

namespace Work.BSW.S3

open Subgroup Work.GW2

/-- The involutions of the normalizer of `F = C_G(x)` form exactly the coset `t * F`.
This is part of Bender's §3.1 (c) (`Work.BSW.BSWS31Prop`). -/
theorem involutionsNormalizer {G : Type} [Group G] [Finite G] {t s x : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hx : x ∉ Work.BSW.HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    {u : G | orderOf u = 2 ∧
        u ∈ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)} =
      {u : G | ∃ c ∈ Subgroup.centralizer ({x} : Set G), u = t * c} := by
  ext u
  constructor
  · rintro ⟨hu2, huN⟩
    -- Every involution `u ∈ M` inverts `F`.
    have huinv := (involution_mem_normalizer_inverts h hx hinv huN hu2).1
    -- Hence `u * t` centralizes `F`, i.e. `u * t ∈ F`.
    have hwF : u * t ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [← centralizer_centralizer_eq_self h hx hinv, Subgroup.mem_centralizer_iff]
      intro c hc
      have key : (u * t) * c * (u * t)⁻¹ = c := by
        rw [mul_inv_rev, Work.BSW.t_inv h]
        calc u * t * c * (t * u⁻¹) = u * (t * c * t) * u⁻¹ := by group
          _ = u * c⁻¹ * u⁻¹ := by rw [inverts_centralizer h hx hinv c hc]
          _ = (u * c * u⁻¹)⁻¹ := by group
          _ = c := by rw [huinv c hc, inv_inv]
      calc c * (u * t) = ((u * t) * c * (u * t)⁻¹) * (u * t) := by rw [key]
        _ = (u * t) * c := by group
    -- `u = t * (u * t)⁻¹`.
    refine ⟨(u * t)⁻¹, (Subgroup.centralizer ({x} : Set G)).inv_mem hwF, ?_⟩
    have hu_inv : u⁻¹ = u :=
      inv_eq_of_mul_eq_one_left (Work.BSW.mul_self_eq_one_of_orderOf_eq_two hu2)
    have hcalc : t * (u * t)⁻¹ = u := by
      rw [mul_inv_rev, Work.BSW.t_inv h, hu_inv, ← mul_assoc, Work.BSW.t_mul_self h, one_mul]
    exact hcalc.symm
  · rintro ⟨c, hc, rfl⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨?_, ?_⟩
    · -- `t * c` is an involution since `t` inverts `F`.
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two]
        calc (t * c) * (t * c) = (t * c * t) * c := by group
          _ = c⁻¹ * c := by rw [inverts_centralizer h hx hinv c hc]
          _ = 1 := inv_mul_cancel c
      · intro h1
        refine t_notMem_centralizer h hx ?_
        have : t = c⁻¹ := by
          calc t = t * c * c⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
            _ = 1 * c⁻¹ := by rw [h1]
            _ = c⁻¹ := one_mul _
        rw [this]
        exact (Subgroup.centralizer ({x} : Set G)).inv_mem hc
    · -- `t * c ∈ M` since `t ∈ M` and `F ≤ M`.
      exact (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)).mul_mem
        (t_mem_normalizer_centralizer h hx hinv)
        ((Subgroup.centralizer ({x} : Set G)).le_normalizer hc)

end Work.BSW.S3
