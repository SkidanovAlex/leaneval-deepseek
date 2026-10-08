import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

/-- Membership in the centralizer of the section `K/H`: an element `x` centralizes `K/H`
exactly when all its commutators with elements of `K` lie in `H`. -/
theorem mem_sectionCentralizer_iff_commutator {G : Type*} [Group G] {H K : Subgroup G} [H.Normal]
    {x : G} : x ∈ Work.Fitting.sectionCentralizer H K ↔ ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ H := by
  rw [Work.Fitting.mem_sectionCentralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    have h1 : (↑k : G ⧸ H) * ↑x = ↑x * ↑k := by
      simpa only [QuotientGroup.mk'_apply] using
        h _ (Subgroup.mem_map_of_mem (QuotientGroup.mk' H) hk)
    rw [← QuotientGroup.eq_one_iff (x * k * x⁻¹ * k⁻¹)]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact commutatorElement_eq_one_iff_mul_comm.mpr h1.symm
  · intro h y hy
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
    have h2 : (↑(x * k * x⁻¹ * k⁻¹) : G ⧸ H) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (h k hk)
    have h2' : (↑x : G ⧸ H) * ↑k * (↑x)⁻¹ * (↑k)⁻¹ = 1 := by
      simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using h2
    exact (commutatorElement_eq_one_iff_mul_comm.mp h2').symm

end Work.Fitting
