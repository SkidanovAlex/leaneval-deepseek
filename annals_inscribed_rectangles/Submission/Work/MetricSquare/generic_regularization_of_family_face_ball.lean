import Mathlib
import Submission.Work.MetricSquare.generic_regularization_of_family_face

/-!
# Generic regularization on the faces of the box, with a small parameter

`Work.MetricSquare.generic_regularization_of_family_face` produces a parameter `p` at which the
`z`-derivative of `Φ (p, ·)` is surjective at every zero inside the unit box, and at every zero on a
face `z i = 0` or `z i = 1` the restriction of the `z`-derivative to the coordinate hyperplane
`{v // v i = 0}` is surjective.

Here we record the *localized* version: the parameter can be chosen inside the ball `‖p‖ < ε` for
any prescribed `ε > 0`.  This is what allows the perturbation to be taken small.

The argument is the one of the parent file, with the last step changed: the bad set is a countable
union of closed sets with empty interior, so its interior is empty; hence it cannot contain the
nonempty open ball of radius `ε`, and we may pick `p` in that ball outside the bad set.
-/

set_option maxHeartbeats 2000000

namespace Work.MetricSquare

open scoped ContDiff Topology
open Set Metric

noncomputable section

/-- **A set of empty interior misses some point of every ball around the origin.**  The complement
of a set with empty interior is dense, hence meets the nonempty open ball of radius `ε`. -/
lemma exists_norm_lt_notMem_of_interior_eq_empty {E : Type*} [NormedAddCommGroup E]
    (S : Set E) (hS : interior S = ∅) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : E, ‖p‖ < ε ∧ p ∉ S := by
  have hdense : Dense (Sᶜ) := by
    rw [dense_iff_closure_eq, closure_compl, hS, compl_empty]
  have hne : (Metric.ball (0 : E) ε).Nonempty :=
    ⟨0, by rw [Metric.mem_ball]; simpa using hε⟩
  obtain ⟨p, hpS, hpball⟩ := hdense.exists_mem_open isOpen_ball hne
  refine ⟨p, ?_, hpS⟩
  rwa [Metric.mem_ball, dist_zero_right] at hpball

/-- **The union of the bad sets is meagre.**  The union over the (finite) family of auxiliary maps
`mapFam Φ` of their bad parameter sets has empty interior. -/
lemma interior_iUnion_badSet_mapFam_eq_empty (m : ℕ)
    (Φ : Pm m × Cz → Tw)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hsurj : ∀ (p : Pm m) (z : Cz), z ∈ Submission.Drive.unitBox 6 → Φ (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : Pm m => Φ (p', z)) p)) :
    interior (⋃ o : Option (Fin 7 × Bool), badSet m (mapFam Φ o)) = ∅ := by
  classical
  have hmap_smooth : ∀ o : Option (Fin 7 × Bool),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mapFam Φ o) := by
    intro o
    cases o with
    | none => exact hΦ
    | some jb =>
      obtain ⟨i, b⟩ := jb
      exact PhiIc_contDiff Φ hΦ i (cval b)
  have hmap_hsurj : ∀ o : Option (Fin 7 × Bool),
      ∀ (p : Pm m) (z : Cz), z ∈ Submission.Drive.unitBox 6 → mapFam Φ o (p, z) = 0 →
        Function.Surjective (fderiv ℝ (fun p' : Pm m => mapFam Φ o (p', z)) p) := by
    intro o
    cases o with
    | none => exact hsurj
    | some jb =>
      obtain ⟨i, b⟩ := jb
      exact PhiIc_hsurj Φ i (cval b) (cval_nonneg b) (cval_le_one b) hsurj
  have hFclosed : ∀ k : Option (Fin 7 × Bool) × ℕ,
      IsClosed (badSet m (mapFam Φ k.1) ∩ Metric.closedBall (0 : Pm m) k.2) :=
    fun k => (isCompact_badSet_inter_closedBall m (mapFam Φ k.1) (hmap_smooth k.1) k.2).isClosed
  have hFempty : ∀ k : Option (Fin 7 × Bool) × ℕ,
      interior (badSet m (mapFam Φ k.1) ∩ Metric.closedBall (0 : Pm m) k.2) = ∅ := by
    intro k
    exact subset_eq_empty (interior_mono Set.inter_subset_left)
      (interior_badSet_eq_empty m (mapFam Φ k.1) (hmap_smooth k.1) (hmap_hsurj k.1))
  have hBaire := Work.Sard.wp.interior_eq_empty_iUnion_isClosed hFclosed hFempty
  have hunion : (⋃ k : Option (Fin 7 × Bool) × ℕ,
        badSet m (mapFam Φ k.1) ∩ Metric.closedBall (0 : Pm m) k.2)
      = ⋃ o : Option (Fin 7 × Bool), badSet m (mapFam Φ o) := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, badSet]
    constructor
    · rintro ⟨k, ⟨z, hz, hz0, hz1⟩, -⟩
      exact ⟨k.1, z, hz, hz0, hz1⟩
    · rintro ⟨o, z, hz, hz0, hz1⟩
      obtain ⟨n, hn⟩ := exists_nat_ge ‖p‖
      exact ⟨(o, n), ⟨z, hz, hz0, hz1⟩,
        Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hn)⟩
  rw [← hunion]
  exact hBaire

/-- **Generic regularization on the faces of the box, with an arbitrarily small parameter.** -/
theorem generic_regularization_of_family_face_ball (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (Φ : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 6 → Work.Drive.Tgt 6)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hsurj : ∀ (p : EuclideanSpace ℝ (Fin m)) (z : Work.Drive.Amb 6),
      z ∈ Submission.Drive.unitBox 6 → Φ (p, z) = 0 →
      Function.Surjective (fderiv ℝ (fun p' : EuclideanSpace ℝ (Fin m) => Φ (p', z)) p)) :
    ∃ p : EuclideanSpace ℝ (Fin m), ‖p‖ < ε ∧
      (∀ z ∈ Submission.Drive.unitBox 6, Φ (p, z) = 0 →
        Function.Surjective (fderiv ℝ (fun z' : Work.Drive.Amb 6 => Φ (p, z')) z)) ∧
      (∀ (i : Fin 7) (z : Work.Drive.Amb 6), z ∈ Submission.Drive.unitBox 6 → Φ (p, z) = 0 →
        (z i = 0 ∨ z i = 1) →
        Function.Surjective (fun v : {v : Work.Drive.Amb 6 // v i = 0} =>
          fderiv ℝ (fun z' : Work.Drive.Amb 6 => Φ (p, z')) z v.1)) := by
  classical
  have hBempty : interior (⋃ o : Option (Fin 7 × Bool), badSet m (mapFam Φ o)) = ∅ :=
    interior_iUnion_badSet_mapFam_eq_empty m Φ hΦ hsurj
  obtain ⟨p, hpball, hp⟩ :=
    exists_norm_lt_notMem_of_interior_eq_empty _ hBempty hε
  refine ⟨p, hpball, ?_, ?_⟩
  · intro z hz h0
    by_contra hbad
    refine hp (Set.mem_iUnion.mpr ⟨none, ?_⟩)
    show p ∈ badSet m Φ
    exact ⟨z, hz, h0, hbad⟩
  · intro i z hz h0 hzi
    by_contra hbad
    have hpface : p ∈ badSet m (PhiIc Φ i (z i)) := by
      refine ⟨z, hz, ?_, ?_⟩
      · show PhiIc Φ i (z i) (p, z) = 0
        rw [PhiIc, faceMap_self i z]
        exact h0
      · intro hD
        have hD' : Function.Surjective
            ((fderiv ℝ (fun w : Cz => Φ (p, w)) z).comp (faceLin i)) := by
          have h1 := fderiv_PhiIc Φ hΦ i (z i) p z
          rw [faceMap_self i z] at h1
          rw [← h1]
          exact hD
        exact hbad ((surjective_comp_faceLin_iff _ i).mp hD')
    refine hp (Set.mem_iUnion.mpr ⟨some (i, boolOf (z i)), ?_⟩)
    have hval : cval (boolOf (z i)) = z i := cval_boolOf hzi
    show p ∈ badSet m (PhiIc Φ i (cval (boolOf (z i))))
    rw [hval]
    exact hpface

end

end Work.MetricSquare
