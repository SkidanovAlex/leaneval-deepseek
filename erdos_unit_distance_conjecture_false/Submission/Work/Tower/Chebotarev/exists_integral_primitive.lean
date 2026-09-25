import Mathlib
import Submission.Work.Tower.Chebotarev.Defs

namespace Work.Tower.Chebotarev

open NumberField
open scoped Classical nonZeroDivisors NumberField

/-- Every number field has a primitive element which is an algebraic integer: there is
`θ : 𝓞 K` with `ℚ⟮θ⟯ = ⊤`. -/
theorem exists_integral_primitive (K : Type) [Field K] [NumberField K] :
    ∃ θ : 𝓞 K, Algebra.adjoin ℚ ({(θ : K)} : Set K) = ⊤ := by
  classical
  -- A primitive element `α` of `K` over `ℚ`, by the primitive element theorem.
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ K
  -- Clearing denominators: some nonzero integer multiple of `α` is integral over `ℤ`.
  obtain ⟨⟨d, hd⟩, hdint⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (R := ℤ) (Rₘ := ℚ) (S := K)
      (nonZeroDivisors ℤ) α (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  rw [Submonoid.smul_def] at hdint
  have hd0 : (d : K) ≠ 0 := by
    have hd0' : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
    exact_mod_cast hd0'
  -- `θ = d • α` is an algebraic integer and still generates `K` over `ℚ`.
  refine ⟨⟨d • α, hdint⟩, ?_⟩
  show Algebra.adjoin ℚ ({d • α} : Set K) = ⊤
  have hθalg : IsAlgebraic ℚ (d • α) := Algebra.IsAlgebraic.isAlgebraic _
  have hgen : IntermediateField.adjoin ℚ ({d • α} : Set K) = ⊤ := by
    rw [eq_top_iff, ← hα, IntermediateField.adjoin_le_iff]
    simp only [Set.singleton_subset_iff]
    have hmem : d • α ∈ IntermediateField.adjoin ℚ ({d • α} : Set K) :=
      IntermediateField.mem_adjoin_simple_self ℚ (d • α)
    have hd_mem : (d : K) ∈ IntermediateField.adjoin ℚ ({d • α} : Set K) := by
      simp
    have hαeq : α = (d : K)⁻¹ * (d • α) := by
      rw [zsmul_eq_mul, inv_mul_cancel_left₀ hd0]
    have key : (d : K)⁻¹ * (d • α) ∈ IntermediateField.adjoin ℚ ({d • α} : Set K) :=
      mul_mem (inv_mem hd_mem) hmem
    nth_rewrite 2 [hαeq]
    exact key
  exact (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic hθalg).mp hgen

end Work.Tower.Chebotarev
