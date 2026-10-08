import Mathlib
import Submission.Work.Fitting.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.Tools

/-- If `D` is a finite solvable group whose Fitting subgroup `F(D)` is cyclic, then `F(D)`
contains the derived subgroup of `D`: every commutator `x * y * x⁻¹ * y⁻¹` lies in `F(D)`.

Indeed `F(D)` is characteristic, hence normal, so conjugation gives a homomorphism
`MulAut.conjNormal : D →* MulAut F(D)`.  As `F(D)` is cyclic, its automorphism group is
commutative (`IsCyclic.mulAutMulEquiv` identifies it with `(ZMod n)ˣ`), so the homomorphism
kills every commutator.  Its kernel consists of the elements of `D` centralising `F(D)`, and
`Work.Fitting.centralizer_fitting_le` (self-centralizing Fitting subgroup of a finite solvable
group) places that centralizer inside `F(D)`. -/
theorem appX_commutator_le_fitting {D : Type} [Group D] [Finite D] [Group.IsSolvable D]
    (hcyc : IsCyclic ↥(Work.Fitting.fitting D)) :
    ∀ x y : D, x * y * x⁻¹ * y⁻¹ ∈ Work.Fitting.fitting D := by
  intro x y
  -- The automorphism group of the cyclic group `F(D)` is commutative.
  have hcomm : ∀ a b : MulAut ↥(Work.Fitting.fitting D), a * b = b * a := by
    intro a b
    apply (IsCyclic.mulAutMulEquiv (G := ↥(Work.Fitting.fitting D))).injective
    simp only [map_mul]
    exact mul_comm _ _
  -- Therefore conjugation by `D` kills the commutator.
  have hφ1 : MulAut.conjNormal (x * y * x⁻¹ * y⁻¹) =
      (1 : MulAut ↥(Work.Fitting.fitting D)) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [hcomm (MulAut.conjNormal x) (MulAut.conjNormal y)]
    group
  -- Evaluating at an arbitrary `a ∈ F(D)` shows the commutator centralises `F(D)`.
  have hmem : x * y * x⁻¹ * y⁻¹ ∈
      Subgroup.centralizer (Work.Fitting.fitting D : Set D) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hval : (MulAut.conjNormal (x * y * x⁻¹ * y⁻¹)) ⟨a, ha⟩ = ⟨a, ha⟩ := by
      rw [hφ1]; rfl
    have h3 : (x * y * x⁻¹ * y⁻¹) * a * (x * y * x⁻¹ * y⁻¹)⁻¹ = a := by
      have hval2 := congrArg Subtype.val hval
      simpa only [MulAut.conjNormal_apply, Subtype.coe_mk] using hval2
    have h4 : a * (x * y * x⁻¹ * y⁻¹) = (x * y * x⁻¹ * y⁻¹) * a := by
      have hh := congrArg (· * (x * y * x⁻¹ * y⁻¹)) h3
      simp only [mul_assoc, inv_mul_cancel, mul_one] at hh
      simpa only [mul_assoc] using hh.symm
    exact h4
  -- `C_D(F(D)) ≤ F(D)` by self-centralization of the Fitting subgroup.
  exact Work.Fitting.centralizer_fitting_le D hmem

end Work.ThmF.Tools
