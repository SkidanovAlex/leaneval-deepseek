import Mathlib
import Submission.Work.RatHurewicz.coneSphereContractible
import Submission.Work.RatHurewicz.AttachCells

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The orthant cover of the model sphere

For `Γ = cellSphere k = S^{k+1} ⊆ EuclideanSpace ℝ (Fin (k+2))`, the pieces

  `cvPiece k (Sum.inl j) = {x | 0 < x j}`  (`j : Fin (k+2)`) and
  `cvPiece k (Sum.inr ()) = {x | ∑ j, x j < 0}`

form an open cover of `Γ` whose finite intersections are the unit spheres of convex cones, hence
contractible whenever nonempty.
-/

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-- The covering pieces of the model sphere `cellSphere k`. -/
def cvPiece (k : ℕ) : (Fin (k + 2) ⊕ Unit) → Set (cellSphere k)
  | Sum.inl j => {x | 0 < (x : EuclideanSpace ℝ (Fin (k + 2))) j}
  | Sum.inr _ => {x | ∑ j : Fin (k + 2), (x : EuclideanSpace ℝ (Fin (k + 2))) j < 0}

/-- The convex cone underlying a finite intersection of pieces. -/
def cvCone (k : ℕ) (T : Finset (Fin (k + 2) ⊕ Unit)) :
    Set (EuclideanSpace ℝ (Fin (k + 2))) :=
  {x | (∀ j : Fin (k + 2), Sum.inl j ∈ T → 0 < x.ofLp j) ∧
    (Sum.inr () ∈ T → ∑ j : Fin (k + 2), x.ofLp j < 0)}

theorem mem_cvCone_iff (k : ℕ) (T : Finset (Fin (k + 2) ⊕ Unit))
    (x : EuclideanSpace ℝ (Fin (k + 2))) :
    x ∈ cvCone k T ↔
      (∀ j : Fin (k + 2), Sum.inl j ∈ T → 0 < x.ofLp j) ∧
        (Sum.inr () ∈ T → ∑ j : Fin (k + 2), x.ofLp j < 0) :=
  Iff.rfl

theorem isOpen_cvPiece (k : ℕ) (i : Fin (k + 2) ⊕ Unit) : IsOpen (cvPiece k i) := by
  rcases i with j | u
  · exact isOpen_lt continuous_const (by fun_prop)
  · exact isOpen_lt (by fun_prop) continuous_const

theorem mem_iInter_cvPiece_iff (k : ℕ) (T : Finset (Fin (k + 2) ⊕ Unit)) (x : cellSphere k) :
    x ∈ ⋂ i ∈ T, cvPiece k i ↔ (x : EuclideanSpace ℝ (Fin (k + 2))) ∈ cvCone k T := by
  rw [Set.mem_iInter₂]
  constructor
  · intro hx
    refine ⟨fun j hj => ?_, fun hT => ?_⟩
    · exact hx (Sum.inl j) hj
    · exact hx (Sum.inr ()) hT
  · rintro ⟨h1, h2⟩ i hi
    rcases i with j | u
    · exact h1 j hi
    · exact h2 hi

theorem iUnion_cvPiece (k : ℕ) (hk : 1 ≤ k) :
    (⋃ i : Fin (k + 2) ⊕ Unit, cvPiece k i) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_contra h
  have hmem : ∀ i, x ∉ cvPiece k i := fun i hi => h ⟨i, hi⟩
  have hle : ∀ j : Fin (k + 2), (x : EuclideanSpace ℝ (Fin (k + 2))) j ≤ 0 := by
    intro j
    have h' := hmem (Sum.inl j)
    simpa only [cvPiece, Set.mem_setOf_eq, not_lt] using h'
  have hlt : ∃ j : Fin (k + 2), (x : EuclideanSpace ℝ (Fin (k + 2))) j < 0 := by
    by_contra hc
    push_neg at hc
    have hnn : ∀ j, (x : EuclideanSpace ℝ (Fin (k + 2))) j = 0 := fun j =>
      le_antisymm (hle j) (hc j)
    have hnorm : ‖(x : EuclideanSpace ℝ (Fin (k + 2)))‖ = 0 := by
      rw [← sq_eq_zero_iff, EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hnn j]
      norm_num
    have h1 := x.2
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, hnorm] at h1
    norm_num at h1
  obtain ⟨j, hj⟩ := hlt
  have h' := hmem (Sum.inr ())
  have hsum : (∑ i : Fin (k + 2), (x : EuclideanSpace ℝ (Fin (k + 2))) i) < 0 := by
    have hsplit : (∑ i : Fin (k + 2), (x : EuclideanSpace ℝ (Fin (k + 2))) i)
        = (x : EuclideanSpace ℝ (Fin (k + 2))) j
          + ∑ i ∈ (Finset.univ : Finset (Fin (k + 2))).erase j,
              (x : EuclideanSpace ℝ (Fin (k + 2))) i :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
    rw [hsplit]
    have h2 : (∑ i ∈ (Finset.univ : Finset (Fin (k + 2))).erase j,
        (x : EuclideanSpace ℝ (Fin (k + 2))) i) ≤ 0 :=
      Finset.sum_nonpos fun i _ => hle i
    linarith
  simp only [cvPiece, Set.mem_setOf_eq, not_lt] at h'
  linarith

theorem convex_cvCone (k : ℕ) (T : Finset (Fin (k + 2) ⊕ Unit)) : Convex ℝ (cvCone k T) := by
  intro x hx y hy a b ha hb hab
  rw [mem_cvCone_iff] at hx hy
  rw [mem_cvCone_iff]
  refine ⟨fun j hj => ?_, fun hT => ?_⟩
  · have hx' := hx.1 j hj
    have hy' := hy.1 j hj
    have h : (a • x + b • y).ofLp j = a * x.ofLp j + b * y.ofLp j := by simp
    rw [h]
    rcases eq_or_lt_of_le ha with h0 | h0
    · rw [← h0, zero_mul, zero_add]
      have hb1 : b = 1 := by linarith
      rw [hb1, one_mul]
      exact hy'
    · exact add_pos_of_pos_of_nonneg (mul_pos h0 hx') (mul_nonneg hb (le_of_lt hy'))
  · have hx' := hx.2 hT
    have hy' := hy.2 hT
    have h : (∑ j : Fin (k + 2), (a • x + b • y).ofLp j)
        = a * ∑ j : Fin (k + 2), x.ofLp j + b * ∑ j : Fin (k + 2), y.ofLp j := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp
    rw [h]
    rcases eq_or_lt_of_le ha with h0 | h0
    · rw [← h0, zero_mul, zero_add]
      have hb1 : b = 1 := by linarith
      rw [hb1, one_mul]
      exact hy'
    · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg h0 hx')
        (mul_nonpos_of_nonneg_of_nonpos hb (le_of_lt hy'))

theorem smul_mem_cvCone (k : ℕ) (T : Finset (Fin (k + 2) ⊕ Unit))
    {x : EuclideanSpace ℝ (Fin (k + 2))} (hx : x ∈ cvCone k T) {t : ℝ} (ht : 0 < t) :
    t • x ∈ cvCone k T := by
  rw [mem_cvCone_iff] at hx
  rw [mem_cvCone_iff]
  refine ⟨fun j hj => ?_, fun hT => ?_⟩
  · have h := hx.1 j hj
    simpa using mul_pos ht h
  · have h := hx.2 hT
    have : (∑ j : Fin (k + 2), (t • x).ofLp j) = t * ∑ j : Fin (k + 2), x.ofLp j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by simp
    rw [this]
    exact mul_neg_of_pos_of_neg ht h

theorem zero_notMem_cvCone (k : ℕ) (T : Finset (Fin (k + 2) ⊕ Unit)) (hT : T.Nonempty) :
    (0 : EuclideanSpace ℝ (Fin (k + 2))) ∉ cvCone k T := by
  intro h
  rw [mem_cvCone_iff] at h
  obtain ⟨i, hi⟩ := hT
  rcases i with j | u
  · have := h.1 j hi
    simp at this
  · have := h.2 hi
    simp at this

/-- The `iInter` of the pieces is the unit sphere of the cone `cvCone`. -/
theorem iInter_cvPiece_eq (k : ℕ) (T : Finset (Fin (k + 2) ⊕ Unit)) :
    (⋂ i ∈ T, cvPiece k i)
      = ((Subtype.val : cellSphere k → EuclideanSpace ℝ (Fin (k + 2))) ⁻¹'
          (cvCone k T ∩ Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1)) := by
  ext x
  rw [mem_iInter_cvPiece_iff, Set.mem_preimage, Set.mem_inter_iff]
  exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩

/-- The finite intersections of the covering pieces are contractible when nonempty. -/
theorem contractibleSpace_cvInter (k : ℕ) (T : Finset (Fin (k + 2) ⊕ Unit)) (hT : T.Nonempty)
    (hne : (⋂ i ∈ T, cvPiece k i).Nonempty) : ContractibleSpace ↥(⋂ i ∈ T, cvPiece k i) := by
  have hmem : ∀ x : cellSphere k, x ∈ ⋂ i ∈ T, cvPiece k i ↔
      (x : EuclideanSpace ℝ (Fin (k + 2))) ∈ cvCone k T := mem_iInter_cvPiece_iff k T
  haveI : ContractibleSpace
      ↥(cvCone k T ∩ Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :=
    coneSphereContractible (k + 1) (cvCone k T) (convex_cvCone k T)
      (fun x hx t ht => smul_mem_cvCone k T hx ht) (zero_notMem_cvCone k T hT)
      (by
        obtain ⟨x, hx⟩ := hne
        exact ⟨(x : EuclideanSpace ℝ (Fin (k + 2))), (hmem x).mp hx, x.2⟩)
  let e : ↥(⋂ i ∈ T, cvPiece k i) ≃ₜ
      ↥(cvCone k T ∩ Metric.sphere (0 : EuclideanSpace ℝ (Fin (k + 2))) 1) :=
    { toFun := fun x => ⟨x.1, (hmem x.1).mp x.2, x.1.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.2⟩, (hmem ⟨y.1, y.2.2⟩).mpr y.2.1⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact Homeomorph.contractibleSpace e

end

end Work.RatHurewicz
