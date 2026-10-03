import Mathlib
import Submission.Work.ORTorsion.Defs

namespace Work.ORTorsion.Support

open scoped TensorProduct
open Work.ORTorsion
open Work.ORTorsion.LaurentBase

/-- The support of the degree-`b` coefficient of `x : K[H]` is covered by the maps
`h' ↦ h' * s ^ b` from the support of `x`: every `h` occurring in `degCoeff Lb b x` arises
from some `h' ∈ x.coeff.support` as `h' = h * s ^ b` in `G`. -/
theorem degCoeff_support_subset {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*}
    [Ring U] [Algebra K U] (L : TorsionData K G U) {H : Subgroup G}
    {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ) (b : ℤ)
    (x : MonoidAlgebra K H) :
    ∀ h ∈ (LaurentBase.degCoeff Lb b x).coeff.support,
      ∃ h' ∈ x.coeff.support, (h' : G) = (h : G) * (Lb.s : G) ^ b := by
  intro h hh
  -- `degCoeff` is `ofCoeff` of a finite sum of `single`s, whose support is covered by the union
  -- of the supports of the summands.
  have hmem : h ∈ (∑ a ∈ x.coeff.support,
      (if ha : φ a = Multiplicative.ofAdd b then
        Finsupp.single ⟨(a * Lb.s ^ (-b) : H), Lb.mem_N_of_mem_ker (Lb.mem_ker_mul_zpow ha)⟩
          (x.coeff a)
      else 0 : ↥Lb.N →₀ K)).support := by
    simpa only [LaurentBase.degCoeff] using hh
  obtain ⟨a, ha_supp, ha_mem⟩ := Finsupp.mem_support_finsetSum h hmem
  refine ⟨a, ha_supp, ?_⟩
  -- the summand indexed by `a` is nonzero at `h`, so the `if` must have taken the `then` branch
  have hcoe : (if ha : φ a = Multiplicative.ofAdd b then
        Finsupp.single ⟨(a * Lb.s ^ (-b) : H), Lb.mem_N_of_mem_ker (Lb.mem_ker_mul_zpow ha)⟩
          (x.coeff a)
      else 0 : ↥Lb.N →₀ K) h ≠ 0 := Finsupp.mem_support_iff.mp ha_mem
  by_cases hφa : φ a = Multiplicative.ofAdd b
  · rw [dif_pos hφa] at hcoe
    have hs : h ∈ (Finsupp.single ⟨(a * Lb.s ^ (-b) : H),
        Lb.mem_N_of_mem_ker (Lb.mem_ker_mul_zpow hφa)⟩ (x.coeff a) : ↥Lb.N →₀ K).support := by
      rw [Finsupp.mem_support_iff]
      exact hcoe
    rw [Finsupp.mem_support_single] at hs
    obtain ⟨heq, -⟩ := hs
    -- hence `h = a * s ^ (-b)` in `N`, and the claim follows from `s ^ b * s ^ (-b) = 1`
    have hG : (h : G) = (a : G) * (Lb.s : G) ^ (-b) := by
      have hcongr := congrArg (fun z : ↥Lb.N => (z : G)) heq
      simpa using hcongr
    rw [hG]
    group
  · rw [dif_neg hφa] at hcoe
    simp at hcoe

end Work.ORTorsion.Support
