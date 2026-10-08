import Mathlib
import Submission.Work.PSU3.StageB.NotFpfStep4.WTorusLift
import Submission.Work.Models.ModelData.psu3ModelData_data
import Submission.Work.Models.Port.PSU3.WeylQuotient
import Submission.Work.Models.Port.PSU3.Centralizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.ModelCentralizer

/-- An element of the maximal torus `psu3T n = T̄ ≤ PSU(3,2ⁿ)` (the image of `suTS n`) which
commutes with the Weyl involution `psu3Weyl n = psu3Hom (suSgM n)` is the image of `suTgSU n a`
for a unit `a ∈ (GF(2^{2n}))ˣ` with `a^(2ⁿ+1) = 1`. -/
theorem exists_suTgSU_of_mem_psu3T_centralizes_weyl {n : ℕ}
    {x : LeanEval.GroupTheory.Defs.PSU3Model n}
    (hxT : x ∈ Submission.PSU3.psu3T n)
    (hxc : x * Submission.PSU3.psu3Weyl n = Submission.PSU3.psu3Weyl n * x) :
    ∃ a : (Submission.PSU3.F n)ˣ,
      x = Submission.PSU3.psu3Hom n (Submission.PSU3.suTgSU n a) ∧
        (a : Submission.PSU3.F n) ^ (2 ^ n + 1) = 1 := by
  -- Lift `x ∈ T̄` to the maximal torus `T = suTS n` of `SU(3,2ⁿ)`.
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxT
  obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.mp hy
  have hya : y = Submission.PSU3.suTgSU n a := by
    apply Subtype.ext
    rw [Submission.PSU3.suTgSU_val]
    exact ha
  have hxeq : x = Submission.PSU3.psu3Hom n (Submission.PSU3.suTgSU n a) := by
    rw [← hyx, hya]
  -- The commutator of the lift with the Weyl element lies in the kernel of `SU(3,2ⁿ) → PSU(3,2ⁿ)`.
  have hker : y * Submission.PSU3.suSgM n * y⁻¹ * (Submission.PSU3.suSgM n)⁻¹ ∈
      (Submission.PSU3.psu3Hom n).ker := by
    rw [MonoidHom.mem_ker]
    have hc : Submission.PSU3.psu3Hom n
        (y * Submission.PSU3.suSgM n * y⁻¹ * (Submission.PSU3.suSgM n)⁻¹) =
        x * Submission.PSU3.psu3Weyl n * x⁻¹ * (Submission.PSU3.psu3Weyl n)⁻¹ := by
      rw [show Submission.PSU3.psu3Weyl n =
        Submission.PSU3.psu3Hom n (Submission.PSU3.suSgM n) from rfl]
      simp only [map_mul, map_inv]
      rw [← hyx]
    have hconj : x * Submission.PSU3.psu3Weyl n * x⁻¹ = Submission.PSU3.psu3Weyl n := by
      rw [hxc, mul_assoc, mul_inv_cancel, mul_one]
    rw [hc, hconj, mul_inv_cancel]
  -- Since the Weyl element inverts the torus, that commutator is `suTgSU (a ^ (q+1))`; so
  -- `suTgSU (a ^ (q+1))` is a scalar matrix, i.e. `(a^(q+1))^(q+1) = (a^(q+1))^3 = 1`.
  have hbker : Submission.PSU3.suTgSU n (a ^ (2 ^ n + 1)) ∈
      (Submission.PSU3.psu3Hom n).ker := by
    rw [← Work.PSU3.StageB.NotFpfStep4.wtl_suTgSU_conj_suSgM n a]
    simpa [hya] using hker
  obtain ⟨hbq1, hb3⟩ :=
    (Work.PSU3.StageB.NotFpfStep4.wtl_suTgSU_mem_ker_iff n (a ^ (2 ^ n + 1))).mp hbker
  have hbodd : (a ^ (2 ^ n + 1)) ^ (2 ^ n - 1) = 1 := by
    rw [← pow_mul, Work.PSU3.StageB.NotFpfStep4.wtl_mul_pow_sub n,
      Work.PSU3.StageB.NotFpfStep4.wtl_pow_card_sub_one_units n a]
  have hb2 : (a ^ (2 ^ n + 1)) ^ 2 = 1 := by
    have hsum : (2 ^ n - 1) + 2 = 2 ^ n + 1 := by
      have := Nat.one_le_two_pow (n := n); omega
    have hsplit : (a ^ (2 ^ n + 1)) ^ (2 ^ n + 1)
        = (a ^ (2 ^ n + 1)) ^ (2 ^ n - 1) * (a ^ (2 ^ n + 1)) ^ 2 := by
      rw [← pow_add, hsum]
    rw [hbq1, hbodd, one_mul] at hsplit
    exact hsplit.symm
  have hbone : a ^ (2 ^ n + 1) = 1 := by
    have h3 : (a ^ (2 ^ n + 1)) ^ 3 = a ^ (2 ^ n + 1) := by
      rw [pow_three, ← pow_two, hb2]
      simp
    rw [h3] at hb3
    exact hb3
  refine ⟨a, hxeq, ?_⟩
  have hfield := congrArg (fun u : (Submission.PSU3.F n)ˣ => (u : Submission.PSU3.F n)) hbone
  simpa using hfield

end Work.PSU3.ModelCentralizer
