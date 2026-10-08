import Mathlib
import Submission.Work.Higman.PowSub

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.Higman.RedAux

open scoped commutatorElement

/-- The commutator subgroup of `zpowers x` with `C` lies in a normal subgroup `A`
if and only if every commutator `x * c * x⁻¹ * c⁻¹` with `c ∈ C` lies in `A`. -/
theorem c4_phi_equiv {P : Type} [Group P] {A C : Subgroup P} (hA : A.Normal) {x : P} :
    ⁅Subgroup.zpowers x, C⁆ ≤ A ↔ ∀ c : P, c ∈ C → x * c * x⁻¹ * c⁻¹ ∈ A := by
  constructor
  · intro hh c hc
    have h1 := Subgroup.commutator_le.mp hh x (Subgroup.mem_zpowers x) c hc
    rwa [commutatorElement_def] at h1
  · intro h
    haveI : A.Normal := hA
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_zpowers_iff] at hg₁
    obtain ⟨n, rfl⟩ := hg₁
    have hcomm : ⁅x, g₂⁆ ∈ A := by
      rw [commutatorElement_def]; exact h g₂ hg₂
    -- In the quotient `P ⧸ A` the image of `x` commutes with the image of `g₂`.
    have hxq : Commute ((QuotientGroup.mk' A) x) ((QuotientGroup.mk' A) g₂) :=
      commutatorElement_eq_one_iff_commute.mp (by
        rw [← map_commutatorElement (QuotientGroup.mk' A) x g₂]
        exact (QuotientGroup.eq_one_iff ⁅x, g₂⁆).mpr hcomm)
    have hq1 : ⁅(QuotientGroup.mk' A) (x ^ n), (QuotientGroup.mk' A) g₂⁆ = 1 := by
      rw [map_zpow]
      exact commutatorElement_eq_one_iff_commute.mpr (hxq.zpow_left n)
    have hq2 : (QuotientGroup.mk' A) ⁅x ^ n, g₂⁆ = 1 := by
      rw [map_commutatorElement]; exact hq1
    exact (QuotientGroup.eq_one_iff ⁅x ^ n, g₂⁆).mp hq2

end Work.Higman.RedAux
