import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.ModelBall

open Metric
open scoped Topology

/-- The standard closed half-ball `{u : ℝⁿ | 0 ≤ u 0 ∧ ‖u‖ ≤ 1}` is convex. -/
private theorem convex_stdHalfBall (n : ℕ) [NeZero n] :
    Convex ℝ {u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0 ∧ ‖u‖ ≤ 1} := by
  have h : {u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0 ∧ ‖u‖ ≤ 1}
      = {u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0} ∩ closedBall 0 1 := by
    ext u
    simp [mem_closedBall]
  rw [h]
  exact (convex_halfSpace_ge (f := fun u : EuclideanSpace ℝ (Fin n) => u 0)
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩ 0).inter (convex_closedBall 0 1)

/-- The standard closed half-ball is closed. -/
private theorem isClosed_stdHalfBall (n : ℕ) [NeZero n] :
    IsClosed {u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0 ∧ ‖u‖ ≤ 1} := by
  have h1 : IsClosed {u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0} :=
    isClosed_Ici.preimage (f := fun u : EuclideanSpace ℝ (Fin n) => u 0)
      (by simpa using (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)).continuous)
  have h2 : {u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0 ∧ ‖u‖ ≤ 1}
      = {u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0} ∩ closedBall 0 1 := by
    ext u
    simp [mem_closedBall]
  rw [h2]
  exact h1.inter isClosed_closedBall

/-- The standard closed half-ball is bounded. -/
private theorem isBounded_stdHalfBall (n : ℕ) [NeZero n] :
    Bornology.IsBounded {u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0 ∧ ‖u‖ ≤ 1} := by
  refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin n))) (r := 1)).subset ?_
  intro u hu
  simpa [Metric.mem_closedBall] using hu.2

/-- The interior of the standard closed half-ball is the open half-ball. -/
private theorem interior_stdHalfBall (n : ℕ) [NeZero n] :
    interior {u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0 ∧ ‖u‖ ≤ 1}
      = {u : EuclideanSpace ℝ (Fin n) | 0 < u 0 ∧ ‖u‖ < 1} := by
  apply Set.Subset.antisymm
  · intro u hu
    have huH : u ∈ {u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0 ∧ ‖u‖ ≤ 1} := interior_subset hu
    refine ⟨?_, ?_⟩
    · by_contra hcon
      have h0 : u 0 = 0 := le_antisymm (not_lt.mp hcon) huH.1
      obtain ⟨ε, hε, hball⟩ :=
        Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hu)
      have hmem : u - (ε / 2) • EuclideanSpace.single (0 : Fin n) (1 : ℝ) ∈ ball u ε := by
        rw [mem_ball, dist_eq_norm]
        have hdiff : u - (ε / 2) • EuclideanSpace.single (0 : Fin n) (1 : ℝ) - u
            = -((ε / 2) • EuclideanSpace.single (0 : Fin n) (1 : ℝ)) := by abel
        rw [hdiff]
        simp [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
        linarith
      have hgt := (hball hmem).1
      have hval : (u - (ε / 2) • EuclideanSpace.single (0 : Fin n) (1 : ℝ)
          : EuclideanSpace ℝ (Fin n)) 0 = -(ε / 2) := by
        simp [h0]
      rw [hval] at hgt
      linarith
    · have hmem : u ∈ interior (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
        interior_mono (fun _ hv => by simpa [mem_closedBall] using hv.2) hu
      rw [interior_closedBall _ one_ne_zero, mem_ball, dist_zero_right] at hmem
      exact hmem
  · intro u hu
    have hopen : IsOpen {u : EuclideanSpace ℝ (Fin n) | 0 < u 0 ∧ ‖u‖ < 1} := by
      have h1 : IsOpen {u : EuclideanSpace ℝ (Fin n) | 0 < u 0} :=
        isOpen_lt continuous_const
          (by simpa using (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin n)).continuous)
      have h2 : {u : EuclideanSpace ℝ (Fin n) | 0 < u 0 ∧ ‖u‖ < 1}
          = {u : EuclideanSpace ℝ (Fin n) | 0 < u 0} ∩ ball 0 1 := by
        ext u
        simp [mem_ball]
      rw [h2]
      exact h1.inter isOpen_ball
    have hsub : {u : EuclideanSpace ℝ (Fin n) | 0 < u 0 ∧ ‖u‖ < 1}
        ⊆ {u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0 ∧ ‖u‖ ≤ 1} :=
      fun _ hv => ⟨le_of_lt hv.1, le_of_lt hv.2⟩
    rw [← hopen.interior_eq] at hu
    exact interior_mono hsub hu

/-- The standard closed half-ball of `ℝⁿ` is homeomorphic to the closed unit ball,
carrying the relative boundary onto the unit sphere. -/
theorem stdHalfBallHomeoBall (n : ℕ) [NeZero n] :
    ∃ e : ↥{u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0 ∧ ‖u‖ ≤ 1} ≃ₜ
            ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1),
      ∀ u : ↥{u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0 ∧ ‖u‖ ≤ 1},
        ((u : EuclideanSpace ℝ (Fin n)) 0 = 0 ∨ ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1) ↔
          ((e u : EuclideanSpace ℝ (Fin n)) ∈ Metric.sphere 0 1) := by
  classical
  have hne : (interior {u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0 ∧ ‖u‖ ≤ 1}).Nonempty := by
    refine ⟨(1 / 2 : ℝ) • EuclideanSpace.single (0 : Fin n) (1 : ℝ), ?_⟩
    rw [interior_stdHalfBall n]
    constructor
    · simp
    · rw [norm_smul, PiLp.norm_single, Real.norm_eq_abs]
      norm_num
  obtain ⟨h, h1, h2, h3⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (convex_stdHalfBall n) hne (isBounded_stdHalfBall n)
  have hcl : closure {u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0 ∧ ‖u‖ ≤ 1}
      = {u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0 ∧ ‖u‖ ≤ 1} :=
    (isClosed_stdHalfBall n).closure_eq
  rw [hcl] at h2
  have hex : ∃ e : ↥{u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0 ∧ ‖u‖ ≤ 1} ≃ₜ
        ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1),
      ∀ v, ((e v : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
        : EuclideanSpace ℝ (Fin n)) = h (v : EuclideanSpace ℝ (Fin n)) := by
    have hmem_to : ∀ v : ↥{u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0 ∧ ‖u‖ ≤ 1},
        h (v : EuclideanSpace ℝ (Fin n)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      intro v
      rw [← h2]
      exact ⟨(v : EuclideanSpace ℝ (Fin n)), v.2, rfl⟩
    have hmem_inv : ∀ y : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1),
        h.symm (y : EuclideanSpace ℝ (Fin n)) ∈ {u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0 ∧ ‖u‖ ≤ 1} := by
      intro y
      have hy : (y : EuclideanSpace ℝ (Fin n))
          ∈ h '' {u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0 ∧ ‖u‖ ≤ 1} := by
        rw [h2]
        exact y.2
      obtain ⟨v, hv, hvy⟩ := hy
      rwa [← hvy, h.symm_apply_apply]
    refine ⟨{ toFun := fun v => ⟨h v, hmem_to v⟩
              invFun := fun y => ⟨h.symm y, hmem_inv y⟩
              left_inv := fun v => Subtype.ext (h.symm_apply_apply _)
              right_inv := fun y => Subtype.ext (h.apply_symm_apply _)
              continuous_toFun := Continuous.subtype_mk
                (h.continuous.comp continuous_subtype_val) hmem_to
              continuous_invFun := Continuous.subtype_mk
                (h.symm.continuous.comp continuous_subtype_val) hmem_inv },
            fun v => rfl⟩
  obtain ⟨e, he⟩ := hex
  refine ⟨e, ?_⟩
  intro u
  rw [he u]
  have hu : (u : EuclideanSpace ℝ (Fin n))
      ∈ {u : EuclideanSpace ℝ (Fin n) | 0 ≤ u 0 ∧ ‖u‖ ≤ 1} := u.2
  have hkey : h (u : EuclideanSpace ℝ (Fin n)) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↔
      ((u : EuclideanSpace ℝ (Fin n)) 0 = 0 ∨ ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1) := by
    rw [← h3, h.injective.mem_set_image, frontier, hcl, Set.mem_sdiff]
    constructor
    · rintro ⟨-, hni⟩
      rw [interior_stdHalfBall n] at hni
      simp only [Set.mem_ofPred_eq, not_and_or, not_lt] at hni
      rcases hni with hle | hle
      · exact Or.inl (le_antisymm hle hu.1)
      · exact Or.inr (le_antisymm hu.2 hle)
    · rintro (h0 | h1)
      · refine ⟨hu, ?_⟩
        rw [interior_stdHalfBall n]
        simp [h0]
      · refine ⟨hu, ?_⟩
        rw [interior_stdHalfBall n]
        simp [h1]
  exact hkey.symm

end Work.ThomBordism.ModelBall
