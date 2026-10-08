import Mathlib
import Submission.Work.ThreePoints.FourGroupCoprimeDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.ThreePoints

/-- The centraliser of `v` in `G` maps onto the centraliser of `v` in `G ⧸ N`.

If `x ∈ G ⧸ N` is fixed by the (involutive) automorphism `v` and `g : G` lifts `x`, then
`c := (v • g)⁻¹ * g ∈ N` measures the failure of `g` to be fixed.  As `v • c = c⁻¹`, the map
`n ↦ c⁻¹ * (v • n)` is an involution of the finite set `N`; this involution has odd cardinality
(`|N|` divides the odd number `|G|`), so it has a fixed point `n`, and then `g * n` is fixed by
`v` and still lifts `x`. -/
theorem elemCent_map_mk {V G : Type*} [Group V] [Group G] [Finite G]
    [MulDistribMulAction V G] (v : V) (hv2 : v * v = 1) (N : Subgroup G) [N.Normal]
    [FT.IsInvariant V N] (hodd : Odd (Nat.card G)) :
    (Work.ThreePoints.elemCent (G := G) v).map (QuotientGroup.mk' N) =
      Work.ThreePoints.elemCent (G := G ⧸ N) v := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype ↥N := Fintype.ofFinite ↥N
  refine le_antisymm ?_ ?_
  · rintro _ ⟨c, hc, rfl⟩
    show v • (QuotientGroup.mk' N c) = QuotientGroup.mk' N c
    rw [QuotientGroup.mk'_apply, FT.quotient_smul_mk, show v • c = c from hc]
  · intro x hx
    rw [Work.ThreePoints.mem_elemCent] at hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    -- `g` is a lift of `x`, and `g` is fixed modulo `N`.
    have hxg : ((v • g : G) : G ⧸ N) = (g : G ⧸ N) := by
      have h := hx
      rw [QuotientGroup.mk'_apply, FT.quotient_smul_mk] at h
      exact h
    -- The obstruction to `g` being fixed.
    set c : G := (v • g)⁻¹ * g with hc_def
    have hcN : c ∈ N := by rw [hc_def]; exact QuotientGroup.eq.mp hxg
    -- `v` inverts the obstruction.
    have hvc : v • c = c⁻¹ := by
      rw [hc_def]
      rw [smul_mul', smul_inv', ← mul_smul, hv2, one_smul]
      group
    -- The affine involution `n ↦ c⁻¹ * (v • n)` of `N`.
    have hθmem : ∀ n : ↥N, c⁻¹ * (v • (n : G)) ∈ N := fun n =>
      N.mul_mem (N.inv_mem hcN)
        (FT.IsInvariant.smul_mem (inferInstance : FT.IsInvariant V N) v n.2)
    let θ : ↥N → ↥N := fun n => ⟨c⁻¹ * (v • (n : G)), hθmem n⟩
    have hθval : ∀ n : ↥N, (θ n : G) = c⁻¹ * (v • (n : G)) := fun n => rfl
    have hθ : Function.Involutive θ := by
      intro n
      apply Subtype.ext
      rw [hθval, hθval]
      rw [smul_mul', smul_inv', ← mul_smul, hv2, one_smul, hvc, inv_inv]
      group
    let σ : Equiv.Perm ↥N := { toFun := θ, invFun := θ, left_inv := hθ, right_inv := hθ }
    have hσ2 : σ * σ = 1 := by
      apply Equiv.Perm.ext
      intro n
      rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      exact hθ n
    -- `|N|` is odd, so the involution `σ` has a fixed point.
    have hα : ¬ 2 ∣ Fintype.card ↥N := by
      rw [← Nat.card_eq_fintype_card]
      intro h2
      exact (Nat.not_even_iff_odd.mpr hodd)
        (even_iff_two_dvd.mpr (dvd_trans h2 (Subgroup.card_subgroup_dvd_card N)))
    have hσ : σ ^ 2 ^ 1 = 1 := by simpa [pow_two] using hσ2
    obtain ⟨n, hn⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hα hσ
    -- A fixed point `n` satisfies `v • n = c * n`.
    have hn' : v • (n : G) = c * (n : G) := by
      have h1 : (σ n : G) = (n : G) := congrArg Subtype.val hn
      have h1' : c⁻¹ * (v • (n : G)) = (n : G) := by rw [← hθval n]; exact h1
      have h2 : c * (c⁻¹ * (v • (n : G))) = c * (n : G) := congrArg (fun z => c * z) h1'
      rw [← mul_assoc, mul_inv_cancel, one_mul] at h2
      exact h2
    -- `g * n` is fixed by `v` and still lifts `x`.
    refine Subgroup.mem_map.mpr ⟨g * (n : G), ?_, ?_⟩
    · show v • (g * (n : G)) = g * (n : G)
      have hgc : (v • g) * c = g := by rw [hc_def]; group
      rw [smul_mul', hn', ← mul_assoc, hgc]
    · show (QuotientGroup.mk' N) (g * (n : G)) = (QuotientGroup.mk' N) g
      have hnN : (QuotientGroup.mk' N) (n : G) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact n.2
      rw [map_mul, hnN, mul_one]

end Work.ThreePoints
