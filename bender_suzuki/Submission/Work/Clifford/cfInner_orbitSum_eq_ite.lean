import Mathlib
import Submission.Work.Clifford.cfInner_eq_ite_of_mem_Irr
import Submission.Work.Clifford.conjFun_mem_Irr
import Submission.Work.Clifford.Orbit

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Clifford

/-- The orbit of an irreducible character consists of irreducible characters. -/
theorem charOrbit_subset_Irr {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    {θ : N → ℂ} (hθ : θ ∈ Work.Clifford.Irr N) :
    ∀ ψ ∈ Work.Clifford.charOrbit N θ, ψ ∈ Work.Clifford.Irr N := by
  intro ψ hψ
  obtain ⟨g, rfl⟩ := mem_charOrbit.mp hψ
  exact conjFun_mem_Irr g hθ

/-- The orbit sum is the sum of the members of the orbit. -/
theorem orbitSum_eq_sum {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    (θ : N → ℂ) :
    Work.Clifford.orbitSum N θ = ∑ ψ ∈ Work.Clifford.charOrbit N θ, ψ := by
  ext n
  rw [orbitSum_apply, Finset.sum_apply]

theorem cfInner_orbitSum_eq_ite {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    [Fintype N] {θ φ : N → ℂ} (hθ : θ ∈ Work.Clifford.Irr N) (hφ : φ ∈ Work.Clifford.Irr N) :
    Work.Clifford.cfInner (Work.Clifford.orbitSum N θ) φ =
      if φ ∈ Work.Clifford.charOrbit N θ then 1 else 0 := by
  rw [orbitSum_eq_sum, cfInner_sum_left (charOrbit N θ) (fun ψ : N → ℂ => ψ) φ]
  trans ∑ ψ ∈ charOrbit N θ, (if ψ = φ then (1 : ℂ) else 0)
  · exact Finset.sum_congr rfl fun ψ hψ =>
      cfInner_eq_ite_of_mem_Irr (charOrbit_subset_Irr hθ ψ hψ) hφ
  · exact Finset.sum_ite_eq' _ _ _

end Work.Clifford
