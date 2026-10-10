import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Submission.Work.Shrinking.PCentral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open scoped commutatorElement

/-- If every commutator in `G` is central and of order two, then the square of every element of
`G` is central. -/
theorem sq_mem_center_of_central_commutators {G : Type*} [Group G]
    (hcen : ∀ x y z : G, ⁅⁅x, y⁆, z⁆ = 1)
    (hcomm : ∀ x y : G, ⁅x, y⁆ ^ 2 = 1) (x : G) :
    x ^ 2 ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro y
  refine (commutatorElement_eq_one_iff_mul_comm.mp ?_).symm
  have hc : ∀ z : G, ⁅x, y⁆ * z = z * ⁅x, y⁆ :=
    fun z => commutatorElement_eq_one_iff_mul_comm.mp (hcen x y z)
  calc ⁅x ^ 2, y⁆ = ⁅x * x, y⁆ := by rw [sq]
    _ = x * ⁅x, y⁆ * x⁻¹ * ⁅x, y⁆ := commutatorElement_mul_left_eq_conj_mul x x y
    _ = ⁅x, y⁆ * x * x⁻¹ * ⁅x, y⁆ := by rw [hc x]
    _ = ⁅x, y⁆ * ⁅x, y⁆ := by group
    _ = (⁅x, y⁆) ^ 2 := by rw [sq]
    _ = 1 := hcomm x y

/-- In a group of exponent dividing four whose commutators are central of order two, the second
term of the descending `2`-central series is already trivial. -/
theorem pCentralSeries_two_eq_bot_of_exponent_four {G : Type*} [Group G]
    (hpow : ∀ x : G, x ^ 4 = 1)
    (hcen : ∀ x y z : G, ⁅⁅x, y⁆, z⁆ = 1)
    (hcomm : ∀ x y : G, ⁅x, y⁆ ^ 2 = 1) :
    Work.Shrinking.pCentralSeries 2 G 2 = ⊥ := by
  set S : Set G := Set.range (fun x : G => x ^ 2) ∪ {g : G | ∃ x y : G, ⁅x, y⁆ = g} with hS
  -- Every generator in `S` is central of order two.
  have hgen : ∀ z ∈ S, z ∈ Subgroup.center G ∧ z ^ 2 = 1 := by
    intro z hz
    rcases hz with ⟨x, rfl⟩ | ⟨a, b, rfl⟩
    · refine ⟨sq_mem_center_of_central_commutators hcen hcomm x, ?_⟩
      have h4 : (x ^ 2) ^ 2 = x ^ 4 := by rw [← pow_mul]
      rw [h4, hpow x]
    · refine ⟨?_, hcomm a b⟩
      rw [Subgroup.mem_center_iff]
      intro g
      exact (commutatorElement_eq_one_iff_mul_comm.mp (hcen a b g)).symm
  -- The property propagates through the closure.
  have hP : ∀ z ∈ Subgroup.closure S, z ∈ Subgroup.center G ∧ z ^ 2 = 1 := by
    intro z hz
    refine Subgroup.closure_induction (p := fun w _ => w ∈ Subgroup.center G ∧ w ^ 2 = 1)
      (fun w hw => hgen w hw) ?_ ?_ ?_ hz
    · exact ⟨Subgroup.one_mem _, by simp⟩
    · intro a b ha hb haP hbP
      obtain ⟨hac, ha2⟩ := haP
      obtain ⟨hbc, hb2⟩ := hbP
      refine ⟨Subgroup.mul_mem _ hac hbc, ?_⟩
      have hcab : Commute a b := (Subgroup.mem_center_iff.mp hac b).symm
      rw [hcab.mul_pow 2, ha2, hb2, one_mul]
    · intro a ha haP
      obtain ⟨hac, ha2⟩ := haP
      refine ⟨Subgroup.inv_mem _ hac, ?_⟩
      rw [inv_pow, ha2, inv_one]
  -- The whole of `pCentralSeries 2 G 1` is contained in `S`'s closure.
  have hle : Work.Shrinking.pCentralSeries 2 G 1 ≤ Subgroup.closure S := by
    have hA : Work.Shrinking.powSubgroup 2 (⊤ : Subgroup G) ≤ Subgroup.closure S := by
      rw [Work.Shrinking.powSubgroup, Subgroup.closure_le]
      rintro z ⟨x, -, rfl⟩
      exact Subgroup.subset_closure (Or.inl ⟨x, rfl⟩)
    have hB : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ Subgroup.closure S := by
      rw [Subgroup.commutator_def, Subgroup.closure_le]
      rintro z ⟨a, -, b, -, rfl⟩
      exact Subgroup.subset_closure (Or.inr ⟨a, b, rfl⟩)
    exact sup_le hA hB
  have hcenter : Work.Shrinking.pCentralSeries 2 G 1 ≤ Subgroup.center G :=
    fun z hz => (hP z (hle hz)).1
  have hsq : ∀ z ∈ Work.Shrinking.pCentralSeries 2 G 1, z ^ 2 = 1 :=
    fun z hz => (hP z (hle hz)).2
  have hpw : Work.Shrinking.powSubgroup 2 (Work.Shrinking.pCentralSeries 2 G 1) = ⊥ := by
    rw [Work.Shrinking.powSubgroup]
    refine le_antisymm ?_ bot_le
    rw [Subgroup.closure_le]
    rintro z ⟨h, hh, rfl⟩
    exact Subgroup.mem_bot.mpr (hsq h hh)
  have hcm : ⁅Work.Shrinking.pCentralSeries 2 G 1, (⊤ : Subgroup G)⁆ = ⊥ :=
    Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr hcenter
  rw [Work.Shrinking.pCentralSeries_succ 2 G 1, Work.Shrinking.pCentralStep, hpw, hcm,
    bot_sup_eq]

end Work.SSGRoute
