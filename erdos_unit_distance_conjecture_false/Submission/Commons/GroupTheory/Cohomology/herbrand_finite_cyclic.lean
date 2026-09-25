import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Torsor.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option linter.unusedVariables false

open scoped BigOperators

namespace Commons.GroupTheory.Cohomology

/-- For a finite group `G` acting on a commutative monoid `M`, the product
`∏ g, g • m` is fixed by the action. -/
lemma herbrand_smul_prod_univ {G M : Type*} [Group G] [CommGroup M]
    [MulDistribMulAction G M] [Fintype G] (τ : G) (m : M) :
    τ • (∏ g : G, g • m) = ∏ g : G, g • m := by
  have h1 : τ • (∏ g : G, g • m) = ∏ g : G, τ • (g • m) := by
    rw [← MulDistribMulAction.toMonoidHom_apply M τ (∏ g : G, g • m)]
    rw [map_prod]
    simp [MulDistribMulAction.toMonoidHom_apply]
  rw [h1]
  refine Fintype.prod_equiv (Equiv.mulLeft τ)
    (fun g : G => τ • (g • m)) (fun g : G => g • m) ?_
  intro g
  simp [mul_smul]

/-- **Herbrand's lemma for a finite cyclic group.**
For a finite group `G` acting on a finite commutative group `M`, and `σ : G`,
setting `d m = σ • m * m⁻¹` and `Nm m = ∏ g, g • m`, the two Tate cohomology
groups `H¹ = ker d / im Nm` and `H⁻¹ = ker Nm / im d` have the same order. -/
theorem herbrand_finite_cyclic {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]
    [Fintype G] [Fintype M] (σ : G) (hσ : Subgroup.zpowers σ = ⊤) (d Nm : M →* M)
    (hd : ∀ m : M, d m = σ • m * m⁻¹)
    (hN : ∀ m : M, Nm m = ∏ g : G, g • m) :
    Nat.card (d.ker ⧸ (Nm.range.subgroupOf d.ker)) =
      Nat.card (Nm.ker ⧸ (d.range.subgroupOf Nm.ker)) := by
  -- `Nm` is invariant under the action.
  have hNm_smul : ∀ m : M, Nm (σ • m) = Nm m := by
    intro m
    rw [hN (σ • m), hN m]
    refine Fintype.prod_equiv (Equiv.mulRight σ)
      (fun g : G => g • (σ • m)) (fun g : G => g • m) ?_
    intro g
    simp [mul_smul]
  have hNm_fix : ∀ m : M, σ • Nm m = Nm m := by
    intro m
    rw [hN m]
    exact herbrand_smul_prod_univ σ m
  -- The relevant subgroup inclusions.
  have hNm_range_le : Nm.range ≤ d.ker := by
    intro x hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨m, rfl⟩ := hx
    rw [MonoidHom.mem_ker, hd (Nm m), hNm_fix m, mul_inv_cancel]
  have hd_range_le : d.range ≤ Nm.ker := by
    intro x hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨m, rfl⟩ := hx
    rw [MonoidHom.mem_ker, hd m, map_mul, map_inv, hNm_smul m, mul_inv_cancel]
  -- Cardinality comparison.
  have hcard_Nmr : Nat.card ↥(Nm.range.subgroupOf d.ker) = Nat.card ↥Nm.range :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNm_range_le).toEquiv
  have hcard_dr : Nat.card ↥(d.range.subgroupOf Nm.ker) = Nat.card ↥d.range :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hd_range_le).toEquiv
  have hM_d : Nat.card M = Nat.card ↥d.ker * Nat.card ↥d.range := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup d.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange d).toEquiv] at h
    rw [h]
    exact Nat.mul_comm _ _
  have hM_N : Nat.card M = Nat.card ↥Nm.ker * Nat.card ↥Nm.range := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Nm.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange Nm).toEquiv] at h
    rw [h]
    exact Nat.mul_comm _ _
  have hI1 : Nat.card ↥d.ker =
      Nat.card (d.ker ⧸ (Nm.range.subgroupOf d.ker)) * Nat.card ↥Nm.range := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Nm.range.subgroupOf d.ker)
    rw [hcard_Nmr] at h
    exact h
  have hI2 : Nat.card ↥Nm.ker =
      Nat.card (Nm.ker ⧸ (d.range.subgroupOf Nm.ker)) * Nat.card ↥d.range := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (d.range.subgroupOf Nm.ker)
    rw [hcard_dr] at h
    exact h
  have hEpos : 0 < Nat.card ↥Nm.range := Nat.card_pos
  have hBpos : 0 < Nat.card ↥d.range := Nat.card_pos
  have hpos : 0 < Nat.card ↥Nm.range * Nat.card ↥d.range := Nat.mul_pos hEpos hBpos
  have key :
      Nat.card (d.ker ⧸ (Nm.range.subgroupOf d.ker)) *
          (Nat.card ↥Nm.range * Nat.card ↥d.range) =
      Nat.card (Nm.ker ⧸ (d.range.subgroupOf Nm.ker)) *
          (Nat.card ↥Nm.range * Nat.card ↥d.range) := by
    calc
      Nat.card (d.ker ⧸ (Nm.range.subgroupOf d.ker)) *
          (Nat.card ↥Nm.range * Nat.card ↥d.range)
          = (Nat.card (d.ker ⧸ (Nm.range.subgroupOf d.ker)) * Nat.card ↥Nm.range) *
              Nat.card ↥d.range := (Nat.mul_assoc _ _ _).symm
      _ = Nat.card ↥d.ker * Nat.card ↥d.range := by rw [← hI1]
      _ = Nat.card M := by rw [← hM_d]
      _ = Nat.card ↥Nm.ker * Nat.card ↥Nm.range := hM_N
      _ = (Nat.card (Nm.ker ⧸ (d.range.subgroupOf Nm.ker)) * Nat.card ↥d.range) *
              Nat.card ↥Nm.range := by rw [← hI2]
      _ = Nat.card (Nm.ker ⧸ (d.range.subgroupOf Nm.ker)) *
              (Nat.card ↥d.range * Nat.card ↥Nm.range) := Nat.mul_assoc _ _ _
      _ = Nat.card (Nm.ker ⧸ (d.range.subgroupOf Nm.ker)) *
              (Nat.card ↥Nm.range * Nat.card ↥d.range) := by
            rw [Nat.mul_comm (Nat.card ↥d.range) (Nat.card ↥Nm.range)]
  exact Nat.mul_right_cancel hpos key

end Commons.GroupTheory.Cohomology