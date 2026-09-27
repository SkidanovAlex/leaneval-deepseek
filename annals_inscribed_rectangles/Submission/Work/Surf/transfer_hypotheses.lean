import Mathlib
import Submission.Work.Surf.defs
import Submission.Work.Surf.exists_smooth_approx_C1
import Submission.Work.Surf.transfer_defs
import Submission.Work.Surf.zeros_finite_euc
import Submission.Work.Surf.Trans.face_cluster
import Submission.Work.Surf.Trans.face_persist
import Submission.Work.Surf.Trans.zeros_regular_persist

/-!
# Stability of the cut/ray hypotheses under a small `C¹` perturbation

The proof of `Work.Surf.transfer_hypotheses` is assembled here from three lemmas proved in sibling
files, all of them stated in the vocabulary of `Work.Surf.Trans`
(`Submission/Work/Surf/transfer_defs.lean`):

* `Work.Surf.Trans.face_cluster` -- compactness of the boundary near the ray-meeting parameters;
* `Work.Surf.Trans.face_persist` -- the per-face persistence of the ray-meeting parameters
  (finiteness, avoidance of the corners, transversality);
* `Work.Surf.Trans.zeros_regular_persist` -- the zeros of a `C¹`-small perturbation of `F` in the
  square remain regular points.

The hypotheses `hcorner` and `htrans_bdry`, transported to each face, supply the hypotheses of
`face_persist`, and `Work.Surf.Trans.rayMeet_inter_sqBdry_eq_iUnion` turns the finiteness of the four
per-face sets into the finiteness of the boundary ray-meeting set of `G`.  The last clause (the
finiteness of the boundary ray-meeting set of `G`) does *not* use `Work.Surf.ncard_rayMeet_persist`:
`face_persist` already shows that each face carries only finitely many ray-meeting parameters, and the
boundary is the union of the four faces.
-/

namespace Work.Surf.Trans

open Set Metric

lemma isCompact_sqBdry : IsCompact sqBdry := by
  have h : sqBdry = ⋃ i : Fin 4, facePt i '' Icc 0 1 :=
    Subset.antisymm sqBdry_subset_iUnion_face
      (iUnion_subset fun i => image_subset_iff.mpr fun t ht => facePt_mem_sqBdry i ht)
  rw [h]
  exact isCompact_iUnion fun i => isCompact_Icc.image (continuous_facePt i)

lemma sqBdry_nonempty : sqBdry.Nonempty :=
  ⟨facePt 0 0, facePt_mem_sqBdry 0 ⟨le_refl 0, zero_le_one⟩⟩

lemma exists_pos_le_norm_sqBdry (F : E2 → E2) (hF : ContDiff ℝ 1 F)
    (hbdry : ∀ x ∈ sqBdry, F x ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ sqBdry, m ≤ ‖F x‖ :=
  exists_pos_le_of_isCompact_of_pos (hF.continuous.norm) isCompact_sqBdry
    (fun x hx => norm_pos_iff.mpr (hbdry x hx))

lemma exists_max_norm_sqBdry (F : E2 → E2) (hF : ContDiff ℝ 1 F) :
    ∃ x ∈ sqBdry, ∀ y ∈ sqBdry, ‖F y‖ ≤ ‖F x‖ := by
  obtain ⟨x, hx, hmax⟩ := isCompact_sqBdry.exists_isMaxOn sqBdry_nonempty
    (hF.continuous.norm.continuousOn)
  exact ⟨x, hx, fun y hy => hmax hy⟩

lemma faceRaySet_finite_of_fin {H : E2 → E2} {v : E2}
    (hfin : (rayMeet H v ∩ sqBdry).Finite) (i : Fin 4) : (FaceRaySet H v i).Finite := by
  have hinj : Set.InjOn (facePt i) (facePt i ⁻¹' (rayMeet H v ∩ sqBdry)) :=
    fun a _ b _ h => facePt_inj i h
  have hpre : (facePt i ⁻¹' (rayMeet H v ∩ sqBdry)).Finite :=
    Set.Finite.preimage hinj hfin
  refine hpre.subset fun t ht => ?_
  exact facePt_mem_rayMeet_of_mem H v ht

end Work.Surf.Trans

namespace Work.Surf

open Set Metric Work.Surf.Trans

/-- **The hypotheses of the cut/ray statement are stable under a small `C¹` perturbation.**  Let
`F : 𝔼² → 𝔼²` be `C¹`, nonzero on the boundary of the unit square, with every zero in the square a
regular point, and let `v ≠ 0` satisfy `‖F x‖ < ‖v‖` on the boundary, with the boundary ray-meeting
set finite, transverse (in the face direction) and avoiding the corners.  Then there is `δ > 0` such
that every `C¹` map `G` with `‖G x - F x‖ < δ` and `‖fderiv ℝ G x - fderiv ℝ F x‖ < δ` on the square
satisfies all the same hypotheses:

* `G x ≠ 0` on the boundary;
* every zero of `G` in the square is a regular point of `G`;
* `‖G x‖ < ‖v‖` on the boundary;
* the corners of the square are not ray-meeting points of `G`;
* the boundary ray-meeting points of `G` are transverse in the face direction;
* the boundary ray-meeting set of `G` is finite.

This is the last (elementary) ingredient of the reduction `Work.Surf.smooth_reduction`: combined with
`Work.Surf.exists_smooth_approx_C1` (approximation), `Work.Surf.ncard_zeros_persist` and
`Work.Surf.ncard_rayMeet_persist` (the two counts), it produces a smooth map with the same data.

Proof sketch.  All the clauses except the regularity of the zeros of `G` are *open conditions*
satisfied by `F`, so they persist for a small enough perturbation; the finiteness of the ray-meeting
set of `G` is `Work.Surf.ncard_rayMeet_persist`.  For the regularity: the zeros of `G` are the
finitely many points `x̃ᵢ`, one near each zero `pᵢ` of `F` (the argument of
`Work.Surf.ncard_zeros_persist`: no zeros outside small balls around the `pᵢ` because `‖F‖` is bounded
below there, and exactly one zero inside each such ball by the contraction argument); at such `x̃ᵢ`
one has `fderiv ℝ G x̃ᵢ - fderiv ℝ F pᵢ = (fderiv ℝ G x̃ᵢ - fderiv ℝ F x̃ᵢ) + (fderiv ℝ F x̃ᵢ - fderiv ℝ F pᵢ)`,
a sum of two terms of norm `< δ` and small (by continuity of `fderiv ℝ F`), so `fderiv ℝ G x̃ᵢ` is a
small perturbation of the invertible `fderiv ℝ F pᵢ` and hence surjective (the set of invertible
endomorphisms is open). -/

theorem transfer_hypotheses
    (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : ContDiff ℝ 1 F)
    (hbdry : ∀ x ∈ Work.Surf.sqBdry, F x ≠ 0)
    (hreg : ∀ x ∈ Work.Surf.sqBox, F x = 0 → Function.Surjective (fderiv ℝ F x))
    {v : EuclideanSpace ℝ (Fin 2)} (hv : v ≠ 0)
    (hbig : ∀ x ∈ Work.Surf.sqBdry, ‖F x‖ < ‖v‖)
    (hcorner : ∀ x ∈ Work.Surf.sqBdry, (∃ r : ℝ, 0 < r ∧ F x = r • v) →
      ¬ ((x 0 = 0 ∨ x 0 = 1) ∧ (x 1 = 0 ∨ x 1 = 1)))
    (htrans_bdry : ∀ x ∈ Work.Surf.sqBdry, (∃ r : ℝ, 0 < r ∧ F x = r • v) →
      ((x 1 = 0 ∨ x 1 = 1) →
        Work.Drive.det2 (fderiv ℝ F x (EuclideanSpace.single 0 1)) v ≠ 0) ∧
      ((x 0 = 0 ∨ x 0 = 1) →
        Work.Drive.det2 (fderiv ℝ F x (EuclideanSpace.single 1 1)) v ≠ 0))
    (hfin : (Work.Surf.rayMeet F v ∩ Work.Surf.sqBdry).Finite) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      ContDiff ℝ 1 G → (∀ x ∈ Work.Surf.sqBox, ‖G x - F x‖ < δ) →
      (∀ x ∈ Work.Surf.sqBox, ‖fderiv ℝ G x - fderiv ℝ F x‖ < δ) →
      (∀ x ∈ Work.Surf.sqBdry, G x ≠ 0) ∧
      (∀ x ∈ Work.Surf.sqBox, G x = 0 → Function.Surjective (fderiv ℝ G x)) ∧
      (∀ x ∈ Work.Surf.sqBdry, ‖G x‖ < ‖v‖) ∧
      (∀ x ∈ Work.Surf.sqBdry, (∃ r : ℝ, 0 < r ∧ G x = r • v) →
        ¬ ((x 0 = 0 ∨ x 0 = 1) ∧ (x 1 = 0 ∨ x 1 = 1))) ∧
      (∀ x ∈ Work.Surf.sqBdry, (∃ r : ℝ, 0 < r ∧ G x = r • v) →
        ((x 1 = 0 ∨ x 1 = 1) →
          Work.Drive.det2 (fderiv ℝ G x (EuclideanSpace.single 0 1)) v ≠ 0) ∧
        ((x 0 = 0 ∨ x 0 = 1) →
          Work.Drive.det2 (fderiv ℝ G x (EuclideanSpace.single 1 1)) v ≠ 0)) ∧
      (Work.Surf.rayMeet G v ∩ Work.Surf.sqBdry).Finite := by
  classical
  obtain ⟨mF, hmFpos, hmF⟩ := exists_pos_le_norm_sqBdry F hF hbdry
  obtain ⟨x₀, hx₀, hx₀max⟩ := exists_max_norm_sqBdry F hF
  have hMv : ‖F x₀‖ < ‖v‖ := hbig x₀ hx₀
  obtain ⟨δz, hδzpos, hδz⟩ := zeros_regular_persist F hF hbdry hreg
  have hfaces : ∀ i : Fin 4, ∃ δ : ℝ, 0 < δ ∧ ∀ G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      ContDiff ℝ 1 G → (∀ x ∈ sqBox, ‖G x - F x‖ < δ) →
      (∀ x ∈ sqBox, ‖fderiv ℝ G x - fderiv ℝ F x‖ < δ) →
      (FaceRaySet G v i).Finite ∧ FaceRaySet G v i ⊆ Ioo 0 1 ∧
        ∀ t ∈ FaceRaySet G v i, deriv (faceDet G v i) t ≠ 0 := by
    intro i
    have hSfin : (FaceRaySet F v i).Finite := faceRaySet_finite_of_fin hfin i
    have hSint : FaceRaySet F v i ⊆ Ioo 0 1 := by
      intro t ht
      have htIcc : t ∈ Icc 0 1 := ht.1
      have hx : facePt i t ∈ sqBdry := facePt_mem_sqBdry i htIcc
      have hnc : ¬ (((facePt i t) 0 = 0 ∨ (facePt i t) 0 = 1) ∧
          ((facePt i t) 1 = 0 ∨ (facePt i t) 1 = 1)) := hcorner (facePt i t) hx ht.2
      have hne : ¬ (t = 0 ∨ t = 1) := fun h => hnc ((facePt_corner_iff (i := i) (t := t)).mpr h)
      exact ⟨lt_of_le_of_ne htIcc.1 (fun h => hne (Or.inl h.symm)),
        lt_of_le_of_ne htIcc.2 (fun h => hne (Or.inr h))⟩
    refine face_persist F hF hv i hSfin hSint ?_ ?_
    · intro p hp
      have hpIoo : p ∈ Ioo 0 1 := hSint hp
      have hx : facePt i p ∈ sqBdry := facePt_mem_sqBdry i hp.1
      have ht := htrans_bdry (facePt i p) hx hp.2
      rw [deriv_faceDet F hF v i p]
      by_cases hle : i.val ≤ 1
      · have h1 : (facePt i p) 1 = 0 ∨ (facePt i p) 1 = 1 :=
          (facePt_coord_one_iff i hpIoo).mpr hle
        have h := ht.1 h1
        simpa [faceDirN, hle, e0] using h
      · have h0 : (facePt i p) 0 = 0 ∨ (facePt i p) 0 = 1 :=
          (facePt_coord_zero_iff i hpIoo).mpr hle
        have h := ht.2 h0
        simpa [faceDirN, hle, e1] using h
    · exact face_cluster F hF hbdry hv i hSfin
  choose δf hδfpos hδf using hfaces
  obtain ⟨δface, hδfacepos, hδfacele⟩ :=
    exists_pos_le_of_finite (Finite.of_fintype (Fin 4)) δf hδfpos
  set δ : ℝ := min (min δz δface) (min (mF / 2) ((‖v‖ - ‖F x₀‖) / 2)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min hδzpos hδfacepos) (lt_min (by linarith) (by linarith))
  refine ⟨δ, hδpos, ?_⟩
  intro G hG hG0 hG1
  have hδ_le_z : δ ≤ δz := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ_le_face0 : δ ≤ δface := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ_le_face : ∀ i : Fin 4, δ ≤ δf i := fun i => le_trans hδ_le_face0 (hδfacele i)
  have hδ_le_mF : δ ≤ mF / 2 := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_le_M : δ ≤ (‖v‖ - ‖F x₀‖) / 2 := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hG0z : ∀ x ∈ sqBox, ‖G x - F x‖ < δz :=
    fun x hx => lt_of_lt_of_le (hG0 x hx) hδ_le_z
  have hG1z : ∀ x ∈ sqBox, ‖fderiv ℝ G x - fderiv ℝ F x‖ < δz :=
    fun x hx => lt_of_lt_of_le (hG1 x hx) hδ_le_z
  have hzeros := hδz G hG hG0z hG1z
  have hfacesG : ∀ i : Fin 4, (FaceRaySet G v i).Finite ∧ FaceRaySet G v i ⊆ Ioo 0 1 ∧
      ∀ t ∈ FaceRaySet G v i, deriv (faceDet G v i) t ≠ 0 := by
    intro i
    exact hδf i G hG (fun x hx => lt_of_lt_of_le (hG0 x hx) (hδ_le_face i))
      (fun x hx => lt_of_lt_of_le (hG1 x hx) (hδ_le_face i))
  have hface_decomp : ∀ x ∈ sqBdry, (∃ r : ℝ, 0 < r ∧ G x = r • v) →
      ∃ i : Fin 4, ∃ t : ℝ, t ∈ Ioo 0 1 ∧ x = facePt i t ∧
        deriv (faceDet G v i) t ≠ 0 := by
    intro x hx hray
    obtain ⟨i, t, ht, htx⟩ := mem_iUnion.mp (sqBdry_subset_iUnion_face hx)
    have htS : t ∈ FaceRaySet G v i := ⟨ht, by rw [htx]; exact hray⟩
    obtain ⟨-, htIoo, htr⟩ := hfacesG i
    exact ⟨i, t, htIoo htS, htx.symm, htr t htS⟩
  refine ⟨?_, hzeros, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have h1 : mF ≤ ‖F x‖ := hmF x hx
    have h2 : ‖G x - F x‖ < mF / 2 := lt_of_lt_of_le (hG0 x hx.1) hδ_le_mF
    have h3 : ‖F x‖ ≤ ‖G x - F x‖ + ‖G x‖ := by
      have h := norm_add_le (F x - G x) (G x)
      rw [sub_add_cancel] at h
      simpa [norm_sub_rev] using h
    have h4 : 0 < ‖G x‖ := by linarith
    exact norm_ne_zero_iff.mp (ne_of_gt h4)
  · intro x hx
    have h1 : ‖F x‖ ≤ ‖F x₀‖ := hx₀max x hx
    have h2 : ‖G x - F x‖ < (‖v‖ - ‖F x₀‖) / 2 := lt_of_lt_of_le (hG0 x hx.1) hδ_le_M
    have h3 : ‖G x‖ ≤ ‖F x‖ + ‖G x - F x‖ := by
      have h := norm_add_le (F x) (G x - F x)
      rw [show F x + (G x - F x) = G x from by abel] at h
      exact h
    linarith
  · intro x hx hray hcornerx
    obtain ⟨i, t, htIoo, htx, -⟩ := hface_decomp x hx hray
    rw [htx] at hcornerx
    have hc := (facePt_corner_iff (i := i) (t := t)).mp hcornerx
    rcases hc with h | h <;> linarith [htIoo.1, htIoo.2]
  · intro x hx hray
    obtain ⟨i, t, htIoo, htx, htr⟩ := hface_decomp x hx hray
    have hdet : Work.Drive.det2 (fderiv ℝ G x (faceDirN i)) v ≠ 0 := by
      rw [htx, ← deriv_faceDet G hG v i t]
      exact htr
    constructor
    · intro h1
      have hle : i.val ≤ 1 := by
        refine (facePt_coord_one_iff i htIoo).mp ?_
        rw [htx] at h1
        exact h1
      have hdir : faceDirN i = EuclideanSpace.single 0 1 := by
        simp [faceDirN, hle, e0]
      rw [← hdir]
      exact hdet
    · intro h0
      have hle : ¬ (i.val ≤ 1) := by
        refine (facePt_coord_zero_iff i htIoo).mp ?_
        rw [htx] at h0
        exact h0
      have hdir : faceDirN i = EuclideanSpace.single 1 1 := by
        simp [faceDirN, hle, e1]
      rw [← hdir]
      exact hdet
  · rw [rayMeet_inter_sqBdry_eq_iUnion G v]
    exact Set.finite_iUnion fun i => (hfacesG i).1.image (facePt i)


end Work.Surf
