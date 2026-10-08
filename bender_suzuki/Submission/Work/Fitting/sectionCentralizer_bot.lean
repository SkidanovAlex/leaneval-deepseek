import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.mem_sectionCentralizer_iff_commutator

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Fitting

/-- For `H = ⊥` the section `K/H` is just `K`, so `C_G(K/1) = C_G(K)`. -/
theorem sectionCentralizer_bot {G : Type*} [Group G] (K : Subgroup G) :
    Work.Fitting.sectionCentralizer (⊥ : Subgroup G) K = Subgroup.centralizer (K : Set G) := by
  ext x
  rw [Work.Fitting.mem_sectionCentralizer_iff_commutator, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    have h1 : x * k * x⁻¹ * k⁻¹ = 1 := by simpa using h k hk
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  · intro h k hk
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (h k hk).symm

end Work.Fitting
