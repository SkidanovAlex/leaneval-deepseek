/-
# The two sides of a Jordan curve: component structure, uniqueness, path-connectedness

Given the two sides `I`, `O` of a Jordan curve `C` (`Work.Top.Sides C`), every point of `Cᶜ`
lies in one of the two sides and its connected component in `Cᶜ` *is* that side.  Consequently
the two sides are unique -- any two `Work.Top.Sides C` have the same `I` and `O` -- and, since
open connected subsets of the plane are path connected, each side is path connected.

The main user-facing definitions of the area are in `Submission/Work/TopJordan/Sides.lean`
(`sidesOf`, `sidesOfCurve`) and `Submission/Work/TopJordan/Jordan.lean` (`jordanForm`).
-/
import Mathlib
import Submission.Work.Top.Jordan
import Submission.Work.TopJordan.Sides
import Submission.Work.TopJordan.Jordan
import Submission.Commons.Topology.Connected.isPreconnected_compl_closedBall
import Submission.Work.TopJordan.CurveModel
import Submission.Commons.Topology.PathConnected.isPathConnected_of_isConnected_of_open_pathConnected_nhds

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open Set

namespace Work.TopJordan

noncomputable section

/-! ## Nonemptiness of the two sides -/

/-- The bounded side of a Jordan curve is nonempty (it has the nonempty curve as frontier). -/
theorem sides_I_nonempty {C : Set ℂ} (hC : Work.Top.IsJordanCurve C)
    (S : Work.Top.Sides C) : S.I.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  obtain ⟨z, hz⟩ := nonempty_of_isJordanCurve hC
  have hzf : z ∈ frontier S.I := by rw [S.frontier_I]; exact hz
  rw [h, frontier_empty] at hzf
  exact hzf

/-- The unbounded side of a Jordan curve is nonempty (it is unbounded). -/
theorem sides_O_nonempty {C : Set ℂ} (S : Work.Top.Sides C) : S.O.Nonempty := by
  obtain ⟨z, hz, -⟩ := S.unbounded_O 0
  exact ⟨z, hz⟩

/-! ## A side is the connected component of each of its points -/

/-- The bounded side is the connected component of each of its points. -/
theorem sides_I_eq_connectedComponentIn {C : Set ℂ} (S : Work.Top.Sides C) {z : ℂ}
    (hz : z ∈ S.I) : S.I = connectedComponentIn Cᶜ z := by
  refine Set.Subset.antisymm ?_ ?_
  · exact IsPreconnected.subset_connectedComponentIn S.preconnected_I hz S.subset_compl_I
  · have h1 : connectedComponentIn Cᶜ z ⊆ S.I ∪ S.O := fun w hw => by
      rw [S.union_eq]
      exact connectedComponentIn_subset Cᶜ z hw
    have h2 : connectedComponentIn Cᶜ z ∩ (S.I ∩ S.O) = ∅ := by
      rw [Set.disjoint_iff_inter_eq_empty.mp S.disjoint, Set.inter_empty]
    rcases (isPreconnected_iff_subset_of_disjoint.mp isPreconnected_connectedComponentIn)
      S.I S.O S.isOpen_I S.isOpen_O h1 h2 with h | h
    · exact h
    · exact absurd (h (mem_connectedComponentIn (S.subset_compl_I hz))) (S.notMem_O_of_mem_I hz)

/-- The unbounded side is the connected component of each of its points. -/
theorem sides_O_eq_connectedComponentIn {C : Set ℂ} (S : Work.Top.Sides C) {z : ℂ}
    (hz : z ∈ S.O) : S.O = connectedComponentIn Cᶜ z := by
  refine Set.Subset.antisymm ?_ ?_
  · exact IsPreconnected.subset_connectedComponentIn S.preconnected_O hz S.subset_compl_O
  · have h1 : connectedComponentIn Cᶜ z ⊆ S.I ∪ S.O := fun w hw => by
      rw [S.union_eq]
      exact connectedComponentIn_subset Cᶜ z hw
    have h2 : connectedComponentIn Cᶜ z ∩ (S.I ∩ S.O) = ∅ := by
      rw [Set.disjoint_iff_inter_eq_empty.mp S.disjoint, Set.inter_empty]
    rcases (isPreconnected_iff_subset_of_disjoint.mp isPreconnected_connectedComponentIn)
      S.I S.O S.isOpen_I S.isOpen_O h1 h2 with h | h
    · exact absurd (h (mem_connectedComponentIn (S.subset_compl_O hz))) (S.notMem_I_of_mem_O hz)
    · exact h

/-- **Every connected component of the complement of a Jordan curve is one of the two sides.** -/
theorem connectedComponentIn_eq_sides {C : Set ℂ} (S : Work.Top.Sides C) {x : ℂ}
    (hx : x ∈ Cᶜ) : connectedComponentIn Cᶜ x = S.I ∨ connectedComponentIn Cᶜ x = S.O := by
  rcases S.subset_of_preconnected isPreconnected_connectedComponentIn
    (connectedComponentIn_subset Cᶜ x) with h | h
  · left
    have hxI : x ∈ S.I := h (mem_connectedComponentIn hx)
    rw [sides_I_eq_connectedComponentIn S hxI]
  · right
    have hxO : x ∈ S.O := h (mem_connectedComponentIn hx)
    rw [sides_O_eq_connectedComponentIn S hxO]

/-! ## Uniqueness of the two sides -/

/-- **The two sides of a Jordan curve are unique.**  Any two decompositions of the complement of
a Jordan curve into a bounded and an unbounded component have the same two pieces. -/
theorem sides_ext {C : Set ℂ} (hC : Work.Top.IsJordanCurve C) {S S' : Work.Top.Sides C} :
    S.I = S'.I ∧ S.O = S'.O := by
  have hIeq : S.I = S'.I := by
    obtain ⟨x, hx⟩ := sides_I_nonempty hC S
    have hxcc : x ∈ Cᶜ := S.subset_compl_I hx
    rcases S'.subset_of_preconnected isPreconnected_connectedComponentIn
      (connectedComponentIn_subset Cᶜ x) with h | h
    · have hxI : x ∈ S'.I := h (mem_connectedComponentIn hxcc)
      rw [sides_I_eq_connectedComponentIn S hx, sides_I_eq_connectedComponentIn S' hxI]
    · -- impossible: the unbounded side would be bounded
      exfalso
      have hxO : x ∈ S'.O := h (mem_connectedComponentIn hxcc)
      have hSO : S'.O = connectedComponentIn Cᶜ x := sides_O_eq_connectedComponentIn S' hxO
      have hbdd : Bornology.IsBounded S'.O := by
        rw [hSO, ← sides_I_eq_connectedComponentIn S hx]
        exact S.bounded_I
      obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbdd
      obtain ⟨z, hzO, hz⟩ := S'.unbounded_O (Nat.ceil (R + 1))
      have hzR : ‖z‖ ≤ R := hR z hzO
      have h2 : R < (Nat.ceil (R + 1) : ℝ) :=
        lt_of_lt_of_le (lt_add_one R) (Nat.le_ceil (R + 1))
      linarith
  have hOeq : S.O = S'.O := by
    refine Set.Subset.antisymm ?_ ?_
    · intro w hw
      have hwC : w ∈ Cᶜ := S.subset_compl_O hw
      have hw' : w ∈ S'.I ∪ S'.O := by rw [S'.union_eq]; exact hwC
      rcases hw' with h | h
      · exact absurd (hIeq ▸ h) (S.notMem_I_of_mem_O hw)
      · exact h
    · intro w hw
      have hwC : w ∈ Cᶜ := S'.subset_compl_O hw
      have hw' : w ∈ S.I ∪ S.O := by rw [S.union_eq]; exact hwC
      rcases hw' with h | h
      · exact absurd (hIeq ▸ h) (S'.notMem_I_of_mem_O hw)
      · exact h
  exact ⟨hIeq, hOeq⟩

/-! ## The sides are path connected -/

/-- **The bounded side of a Jordan curve is path connected.** -/
theorem isPathConnected_sidesOf_I {C : Set ℂ} (hC : Work.Top.IsJordanCurve C) :
    IsPathConnected (sidesOf hC).I := by
  refine Commons.Topology.PathConnected.isPathConnected_of_isConnected_of_open_pathConnected_nhds
    ⟨sides_I_nonempty hC (sidesOf hC), (sidesOf hC).preconnected_I⟩ ?_
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (sidesOf hC).isOpen_I x hx
  exact ⟨Metric.ball x ε, Metric.isOpen_ball, Metric.mem_ball_self hε,
    (convex_ball x ε).isPathConnected ⟨x, Metric.mem_ball_self hε⟩, hball⟩

/-- **The unbounded side of a Jordan curve is path connected.** -/
theorem isPathConnected_sidesOf_O {C : Set ℂ} (hC : Work.Top.IsJordanCurve C) :
    IsPathConnected (sidesOf hC).O := by
  refine Commons.Topology.PathConnected.isPathConnected_of_isConnected_of_open_pathConnected_nhds
    ⟨sides_O_nonempty (sidesOf hC), (sidesOf hC).preconnected_O⟩ ?_
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (sidesOf hC).isOpen_O x hx
  exact ⟨Metric.ball x ε, Metric.isOpen_ball, Metric.mem_ball_self hε,
    (convex_ball x ε).isPathConnected ⟨x, Metric.mem_ball_self hε⟩, hball⟩

/-! ## Closure of a side, and paths in the complement -/

/-- The closure of the bounded side is the bounded side together with the curve. -/
theorem closure_sides_I {C : Set ℂ} (S : Work.Top.Sides C) : closure S.I = S.I ∪ C := by
  rw [closure_eq_self_union_frontier, S.frontier_I]

/-- The closure of the unbounded side is the unbounded side together with the curve. -/
theorem closure_sides_O {C : Set ℂ} (S : Work.Top.Sides C) : closure S.O = S.O ∪ C := by
  rw [closure_eq_self_union_frontier, S.frontier_O]

/-- A point of the closure of the bounded side which is not on the curve lies in the bounded
side. -/
theorem mem_sides_I_of_mem_closure {C : Set ℂ} (S : Work.Top.Sides C) {x : ℂ}
    (hx : x ∈ closure S.I) (hxC : x ∉ C) : x ∈ S.I := by
  have h : x ∈ S.I ∪ C := by rw [← closure_sides_I S]; exact hx
  rcases h with h | h
  · exact h
  · exact absurd h hxC

/-- A point of the closure of the unbounded side which is not on the curve lies in the unbounded
side. -/
theorem mem_sides_O_of_mem_closure {C : Set ℂ} (S : Work.Top.Sides C) {x : ℂ}
    (hx : x ∈ closure S.O) (hxC : x ∉ C) : x ∈ S.O := by
  have h : x ∈ S.O ∪ C := by rw [← closure_sides_O S]; exact hx
  rcases h with h | h
  · exact h
  · exact absurd h hxC

/-- **Two points of the complement of a Jordan curve are joined in it exactly when they lie on
the same side.** -/
theorem joinedIn_iff_same_side {C : Set ℂ} (hC : Work.Top.IsJordanCurve C) {x y : ℂ}
    (hx : x ∈ Cᶜ) (hy : y ∈ Cᶜ) :
    JoinedIn Cᶜ x y ↔
      (x ∈ (sidesOf hC).I ∧ y ∈ (sidesOf hC).I) ∨
      (x ∈ (sidesOf hC).O ∧ y ∈ (sidesOf hC).O) := by
  have hx' : x ∈ (sidesOf hC).I ∪ (sidesOf hC).O := by
    rw [(sidesOf hC).union_eq]; exact hx
  have hy' : y ∈ (sidesOf hC).I ∪ (sidesOf hC).O := by
    rw [(sidesOf hC).union_eq]; exact hy
  constructor
  · intro hjoin
    rcases hx' with hxI | hxO
    · refine Or.inl ⟨hxI, ?_⟩
      rcases hy' with hyI | hyO
      · exact hyI
      · exact absurd hjoin ((sidesOf hC).not_joinedIn hxI hyO)
    · refine Or.inr ⟨hxO, ?_⟩
      rcases hy' with hyI | hyO
      · exact absurd (JoinedIn.symm hjoin) ((sidesOf hC).not_joinedIn hyI hxO)
      · exact hyO
  · rintro (⟨hxI, hyI⟩ | ⟨hxO, hyO⟩)
    · exact JoinedIn.mono ((isPathConnected_sidesOf_I hC).joinedIn x hxI y hyI)
        (sidesOf hC).subset_compl_I
    · exact JoinedIn.mono ((isPathConnected_sidesOf_O hC).joinedIn x hxO y hyO)
        (sidesOf hC).subset_compl_O

/-! ## Agreement with the sides extracted from `Work.Top.JordanForm` -/

/-- The sides constructed here agree with those extracted from `Work.Top.JordanForm` (now that
`jordanForm` proves it): the sides of a Jordan curve are unique. -/
theorem sidesOf_eq_JordanForm_sides {C : Set ℂ} (hC : Work.Top.IsJordanCurve C) :
    (sidesOf hC).I = (Work.Top.JordanForm.sides jordanForm C hC).I ∧
      (sidesOf hC).O = (Work.Top.JordanForm.sides jordanForm C hC).O :=
  sides_ext hC

/-! ## Sides and balls, and the first crossing of a curve -/

/-- **The exterior of a ball containing the curve lies in the unbounded side.** -/
theorem exterior_subset_sides_O {C : Set ℂ} (S : Work.Top.Sides C) {R : ℝ}
    (hR : C ⊆ Metric.closedBall (0 : ℂ) R) : {z : ℂ | R < ‖z‖} ⊆ S.O := by
  refine S.subset_O_of_unbounded ?_ ?_ ?_
  · simpa using Commons.Topology.Connected.isPreconnected_compl_closedBall (0 : ℂ) R
  · intro z hz
    simp only [Set.mem_compl_iff]
    intro hzC
    have h1 : ‖z‖ ≤ R := by
      have h2 := hR hzC
      simpa [Metric.mem_closedBall, dist_zero_right] using h2
    exact absurd hz (not_lt.mpr h1)
  · intro n
    have h0 : (0 : ℝ) ≤ max R 0 + (n : ℝ) + 1 := by
      have h1 := le_max_right R 0
      have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    refine ⟨((max R 0 + (n : ℝ) + 1 : ℝ) : ℂ), ?_, ?_⟩
    · show R < ‖((max R 0 + (n : ℝ) + 1 : ℝ) : ℂ)‖
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
      have h1 := le_max_left R 0
      have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    · show (n : ℝ) ≤ ‖((max R 0 + (n : ℝ) + 1 : ℝ) : ℂ)‖
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
      have h1 := le_max_right R 0
      linarith

/-- A point far enough outside the curve (beyond any ball containing it) lies in the unbounded
side. -/
theorem sides_O_of_norm_gt {C : Set ℂ} (S : Work.Top.Sides C) {R : ℝ}
    (hR : C ⊆ Metric.closedBall (0 : ℂ) R) {z : ℂ} (hz : R < ‖z‖) : z ∈ S.O :=
  exterior_subset_sides_O S hR hz

/-- **Any closed ball about the origin containing the curve contains the bounded side.** -/
theorem sides_I_subset_closedBall {C : Set ℂ} (S : Work.Top.Sides C) {R : ℝ}
    (hR : C ⊆ Metric.closedBall (0 : ℂ) R) : S.I ⊆ Metric.closedBall (0 : ℂ) R := by
  intro z hz
  have hzO : z ∉ S.O := S.notMem_O_of_mem_I hz
  by_contra hzR
  refine hzO (exterior_subset_sides_O S hR ?_)
  show R < ‖z‖
  have h : R < dist z 0 := not_le.mp (by simpa [Metric.mem_closedBall] using hzR)
  rwa [dist_zero_right] at h

/-- **First crossing.**  A path from the bounded side of a Jordan curve to the unbounded side
meets the curve, and there is a first time at which it does so. -/
theorem exists_min_crossing {C : Set ℂ} (hC : Work.Top.IsJordanCurve C) (S : Work.Top.Sides C)
    {f : C(unitInterval, ℂ)} (h0 : f 0 ∈ S.I) (h1 : f 1 ∈ S.O) :
    ∃ t : unitInterval, f t ∈ C ∧ ∀ s : unitInterval, f s ∈ C → t ≤ s := by
  have hne : (f ⁻¹' C).Nonempty := S.path_meets h0 h1
  obtain ⟨t, htC, htmin⟩ :=
    ((isClosed_of_isJordanCurve hC).preimage f.continuous).isCompact.exists_isMinOn hne
      (continuous_subtype_val.continuousOn)
  exact ⟨t, htC, fun s hs => Subtype.coe_le_coe.mpr (htmin hs)⟩

end

end Work.TopJordan
