import Mathlib
import Submission.Work.Whitney.RankTwo.Basic
import Submission.Work.Cohomology.MVcapSquares

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.Whitney.RankTwo
open Work.Thom
open Work.Cohomology

noncomputable section

variable (Y : Type) [TopologicalSpace Y]

/-- A `1`-cochain of the `A+C` complex vanishes on each arc of the hexagon. -/
theorem genEval_pdABKern_arcSimp (y : Y) (k : ℕ) (hk : k < 6)
    (u : ↥(pdABKernR (R := ℤ) (TopCat.of (X Y)) (tcmA Y 1 1) (tcmC Y 1 1) 1)) :
    genEval ℤ (ssX Y) (u.1) (arcSimp Y y k) = 0 := by
  have hA : ∀ k ∈ ({0, 2, 3, 5} : Finset ℕ),
      Set.range (fun q : stdSimplex ℝ (Fin (1 + 1)) => (sEquiv Y 1) (arcSimp Y y k) q)
        ⊆ tcmA Y 1 1 := fun k hk => arcSimp_image_subset_A Y y hk
  have hC : ∀ k ∈ ({1, 4} : Finset ℕ),
      Set.range (fun q : stdSimplex ℝ (Fin (1 + 1)) => (sEquiv Y 1) (arcSimp Y y k) q)
        ⊆ tcmC Y 1 1 := fun k hk => arcSimp_image_subset_C Y y hk
  have key : ∀ (A : Set (X Y)) (h : Set.range (fun q : stdSimplex ℝ (Fin (1 + 1)) =>
        (sEquiv Y 1) (arcSimp Y y k) q) ⊆ A)
      (hu : (u.1 : Cochain ℤ (ssX Y) 1) ∈ relKern ℤ (TopCat.of (X Y)) A 1),
      genEval ℤ (ssX Y) (u.1) (arcSimp Y y k) = 0 := by
    intro A h hu
    obtain ⟨τ, hτ⟩ := exists_lift_of_range_subset A (arcSimp Y y k)
      (by rw [← TopCat.range_toSSetObjEquivOld]; exact h)
    rw [← hτ]
    exact genEval_eq_zero_of_mem_relKern ℤ (TopCat.of (X Y)) A u.1 hu τ
  interval_cases k
  · exact key (tcmA Y 1 1) (hA 0 (by decide)) (Submodule.mem_inf.mp u.2).1
  · exact key (tcmC Y 1 1) (hC 1 (by decide)) (Submodule.mem_inf.mp u.2).2
  · exact key (tcmA Y 1 1) (hA 2 (by decide)) (Submodule.mem_inf.mp u.2).1
  · exact key (tcmA Y 1 1) (hA 3 (by decide)) (Submodule.mem_inf.mp u.2).1
  · exact key (tcmC Y 1 1) (hC 4 (by decide)) (Submodule.mem_inf.mp u.2).2
  · exact key (tcmA Y 1 1) (hA 5 (by decide)) (Submodule.mem_inf.mp u.2).1

/-- The evaluation of a degree `1` cochain on the arc cycle. -/
theorem kronecker_c_apply (y : Y) (γ : Cochain ℤ (ssX Y) 1) :
    kronecker ℤ (ssX Y) γ (c Y y)
      = ∑ k ∈ Finset.range 6, genEval ℤ (ssX Y) γ (arcSimp Y y k) := by
  show γ (c Y y) = _
  rw [c, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show γ (((ssX Y).ιChainComplex (R := zR) (arcSimp Y y k)).hom 1) = _
  exact kronecker_gen ℤ (ssX Y) γ (arcSimp Y y k)

/-- **A `1`-cochain of the `A+C` complex pairs trivially with the boundary of the cone.** -/
theorem kronecker_dZ_eq_zero (y : Y)
    (u : ↥(pdABKernR (R := ℤ) (TopCat.of (X Y)) (tcmA Y 1 1) (tcmC Y 1 1) 1)) :
    kronecker ℤ (ssX Y) (u.1) ((((ssX Y).chainComplex zR).d 2 1) (Z Y y)) = 0 := by
  rw [d_Z, kronecker_c_apply]
  exact Finset.sum_eq_zero fun k hk =>
    genEval_pdABKern_arcSimp Y y k (Finset.mem_range.mp hk) u

/-- The evaluation of a degree `2` cochain on the cone. -/
theorem kronecker_Z_apply (y : Y) (γ : Cochain ℤ (ssX Y) 2) :
    kronecker ℤ (ssX Y) γ (Z Y y)
      = ∑ k ∈ Finset.range 6, genEval ℤ (ssX Y) γ (secSimp Y y k) := by
  show γ (Z Y y) = _
  rw [Z, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show γ (((ssX Y).ιChainComplex (R := zR) (secSimp Y y k)).hom 1) = _
  exact kronecker_gen ℤ (ssX Y) γ (secSimp Y y k)

/-- **The number `1`: the Alexander–Whitney product of the two sign cocycles on the cone.** -/
theorem kronecker_cup_Z (y : Y) :
    kronecker ℤ (ssX Y) (cup ℤ (ssX Y) (alpha Y) (beta Y)) (Z Y y) = 1 := by
  rw [kronecker_Z_apply, ← cupSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [genEval_cup_secSimp, coordA_vtx, coordB_vtx]

end
end Work.Whitney.RankTwo
