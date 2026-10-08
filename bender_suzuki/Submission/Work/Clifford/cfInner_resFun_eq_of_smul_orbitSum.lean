import Mathlib
import Submission.Work.Clifford.cfInner_orbitSum_self
import Submission.Work.Clifford.CFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Clifford

theorem cfInner_resFun_eq_of_smul_orbitSum {G : Type*} [Group G] [Fintype G] {N : Subgroup G}
    [N.Normal] [Fintype N] {θ : N → ℂ} (hθ : θ ∈ Work.Clifford.Irr N) {χ : G → ℂ} {e : ℕ}
    (h : Work.Clifford.resFun N χ = (e : ℂ) • Work.Clifford.orbitSum N θ) :
    Work.Clifford.cfInner (Work.Clifford.resFun N χ) θ = (e : ℂ) := by
  rw [h, cfInner_smul_left, cfInner_orbitSum_self hθ, mul_one]

end Work.Clifford
