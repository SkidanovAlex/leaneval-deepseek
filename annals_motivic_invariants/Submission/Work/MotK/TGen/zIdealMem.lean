import Mathlib
import Submission.Work.MotK.TGen.ZPlaneDefs
import Submission.Work.MotK.TGen.zG3Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Membership of `zB` and `zg` in the chart ideal `ZI`

The two easy membership facts of node K5's saturation computation, separated from
`Work.MotK.TGen.ker_zPsi_le_radical_aux` (which contains the *hole* `radical_zA_saturation`)
so that the consumers that only need these (`Work.MotK.TGen.ZRingIsDomainAll` and its K5
descendants) do not import the hole.
-/

set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-- `zB ∈ ZI`. -/
theorem zB_mem_ZI (a b h : K) (hb : b ≠ 0) : zB K a b h ∈ Work.MotK.TwCensus.ZI a b h := by
  have h3 : Work.MotK.TwCensus.Zcub a b h 3 = -(C b) * zB K a b h := by
    rw [Work.MotK.TwCensus.Zcub_three, zB, zA, zC]
  have hmem : Work.MotK.TwCensus.Zcub a b h 3 ∈ Work.MotK.TwCensus.ZI a b h :=
    Ideal.subset_span ⟨3, rfl⟩
  have hb1 : (C (b⁻¹) : MvPolynomial (Fin 3) K) * C b = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hb, C_1]
  have h2 : -(C (b⁻¹) : MvPolynomial (Fin 3) K) * Work.MotK.TwCensus.Zcub a b h 3
      = zB K a b h := by
    rw [h3]
    rw [show -(C (b⁻¹) : MvPolynomial (Fin 3) K) * (-(C b) * zB K a b h)
          = ((C (b⁻¹) : MvPolynomial (Fin 3) K) * C b) * zB K a b h from by ring]
    rw [hb1, one_mul]
  rw [← h2]
  exact Ideal.mul_mem_left _ _ hmem

/-- `g = zg ∈ ZI`. -/
theorem zg_mem_ZI (a b h : K) (ha : a ≠ 0) : zg K a b h ∈ Work.MotK.TwCensus.ZI a b h := by
  have hc := Work.MotK.TwCensus.eliminant_cert (K := K) a b h
  have ha1 : (C a⁻¹ : MvPolynomial (Fin 3) K) * C a = 1 := by
    rw [← C_mul, inv_mul_cancel₀ ha, C_1]
  have hmem : C a * (Work.MotK.TwCensus.ZElim a b h) ∈ Work.MotK.TwCensus.ZI a b h := by
    rw [hc]
    exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨0, rfl⟩))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨1, rfl⟩)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨3, rfl⟩)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨4, rfl⟩))
  have hthis := Ideal.mul_mem_left _ (C a⁻¹ : MvPolynomial (Fin 3) K) hmem
  rw [← mul_assoc, ha1, one_mul] at hthis
  rw [zg_eq_ZElim]
  exact hthis

end Work.MotK.TGen
