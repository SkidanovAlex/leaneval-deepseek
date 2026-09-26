import Mathlib
import Submission.Work.Drive.Mono.JunctionGenC
import Submission.Work.Drive.Mono.traceLocallyEuclidean_of_junctionGenB
import Submission.Work.Drive.Mono.trace_locallyEuclidean_of_junctionGen

/-!
# The local models of the sweep trace from the repaired junction bundle `JunctionGenC`

This is the assembly of `Submission/Work/Drive/Mono/traceLocallyEuclidean_of_junctionGenB.lean` with
the *repaired* bundle `Work.Drive.Mono.JunctionGenC` (clause (c) restricted to the closed slab,
`Mono/JunctionGenC.lean`).  Only one step changes: the unique-active-face lemma now needs the slab
condition at the point, which its unique call site has (there the point lies strictly inside the
slab).
-/



namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-! ## 1. The corrected unique-active-face lemma (clause (c) of `JunctionGenC`) -/

/-- **The active face of the box sphere at a point of the surface at a non-exceptional level is
unique**, by clause (c) of `JunctionGenC`. -/
theorem unique_activeFace_of_junctionGenC {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 lam : ℝ}
    {z : R3}
    (hJ : JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1) (hlam : lam ∈ Set.Icc lam0 lam1)
    (hne : lam ∉ (exc : Set ℝ)) (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzS : Submission.boxNorm c σ z = s) (hslab : |inner ℝ v z - (inner ℝ v c + u)| ≤ h)
    (hzl : ℓ z = lam) :
    ∃ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧
      Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε z ∧
      ∀ j : Fin 3, j ≠ i → Work.Smooth.BoxGeneric.faceNorm c σ j z < s := by
  obtain ⟨i, hi⟩ := Work.Smooth.BoxGeneric.exists_faceNorm_eq_boxNorm c σ z
  have hi' : Work.Smooth.BoxGeneric.faceNorm c σ i z = s := by rw [hi, hzS]
  refine ⟨i, faceSign c σ z i, faceSign_eq_one_or_neg_one c σ z i, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [faceLin_faceSign, hi']
    · intro j
      have h1 := Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ j z
      rwa [hzS] at h1
  · intro j hj
    by_contra hcon
    push_neg at hcon
    have hj' : Work.Smooth.BoxGeneric.faceNorm c σ j z = s :=
      le_antisymm (by
        have h1 := Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ j z
        rwa [hzS] at h1) hcon
    have hext : ∃ i' j' : Fin 3, i' ≠ j' ∧ |z (σ i') - c (σ i')| = Submission.boxSide i' * s ∧
        |z (σ j') - c (σ j')| = Submission.boxSide j' * s := by
      refine ⟨i, j, hj.symm, ?_, ?_⟩
      · have h2 := hi'
        rw [Work.Smooth.BoxGeneric.faceNorm_apply, div_eq_iff (ne_of_gt (Submission.boxSide_pos i))]
          at h2
        simpa [mul_comm] using h2
      · have h2 := hj'
        rw [Work.Smooth.BoxGeneric.faceNorm_apply, div_eq_iff (ne_of_gt (Submission.boxSide_pos j))]
          at h2
        simpa [mul_comm] using h2
    have := hJ.2.2.1 z hz hzS hslab hext
    rw [hzl] at this
    exact hne this

/-! ## 2. The assembly -/
/-- **Every trace point is locally Euclidean, from the corrected junction bundle.**

This is verbatim the assembly `Work.Drive.Mono.trace_locallyEuclidean_of_junctionGen`
(`Submission/Work/Drive/Mono/trace_locallyEuclidean_of_junctionGen.lean`) with the hypothesis
`Work.Drive.Mono.JunctionGen` replaced by the corrected bundle `Work.Drive.Mono.JunctionGenC`
(whose clause (c) is restricted to points *on the box sphere*). -/
theorem traceLocallyEuclidean_of_junctionGenC {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ}
    {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 lam : ℝ}
    (hs : 0 < s)
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      (Work.BoxShrink.Core.sphereSet c σ s)))
    (hfaceReg : ∀ z : R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → z ∈ Submission.PBox s c σ →
      |inner ℝ v z - (inner ℝ v c + u)| = h →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0)
    (hT : Work.Drive.Mono.TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (hJ : Work.Drive.Mono.JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1)
    (hlam : lam ∈ Set.Icc lam0 lam1) (hne : lam ∉ (exc : Set ℝ)) :
    ∀ z : R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) →
      ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
        Work.Smooth.OneManoifold.IsLocallyEuclidean
          (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
            frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  intro z hz
  obtain ⟨hgen, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, hexc⟩ := hT
  have hv : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv1
    exact one_ne_zero hv1.symm
  have hzc : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier := hz.1
  have hzfr : z ∈ frontier (tiltedLevelRemoved s c σ u v h ℓ lam) := hz.2
  have hface_or : ∀ w : R3, |inner ℝ v w - (inner ℝ v c + u)| = h →
      inner ℝ v w = inner ℝ v c + u + h ∨ inner ℝ v w = inner ℝ v c + u - h := by
    intro w hw
    rcases (abs_eq (le_of_lt hh)).mp hw with h2 | h2
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hb_le : Submission.boxNorm c σ z ≤ s :=
    boxNorm_le_of_mem_frontier_tiltedLevelRemoved hzfr
  rcases lt_or_ge (Submission.boxNorm c σ z) s with hlt | hge
  · -- ### the point is inside the box
    have hzP : z ∈ Submission.PBox s c σ := (Submission.mem_PBox_iff s c σ z).mpr hlt
    rcases lt_trichotomy |inner ℝ v z - (inner ℝ v c + u)| h with hslab | hslab | hslab
    · -- strictly inside the slab
      rcases lt_trichotomy (ℓ z) lam with hzlam | hzlam | hzlam
      · exact absurd (frontier_subset_closure hzfr)
          (notMem_closure_tiltedLevelRemoved_of_slab_below hslab hzlam)
      · -- the interior of the wall
        refine Work.Drive.Mono.isLocallyEuclidean_trace_of_wallPoint hℓne hzc hzP hslab hzlam ?_
        intro p hp
        refine hgen.1 lam hne p (by rwa [hp]) ?_ (by rw [hp]; exact hzlam)
        simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq, hp]
        exact le_of_lt hslab
      · exact absurd hzfr (notMem_frontier_of_mem_interior
          (mem_interior_tiltedLevelRemoved_of_lt hzP hzlam))
    · -- on a face of the slab
      rcases hface_or z hslab with hf | hf
      · -- upper face
        rcases lt_trichotomy (ℓ z) lam with hzlam | hzlam | hzlam
        · -- interior of a face
          exact Work.Drive.Mono.isLocallyEuclidean_trace_of_facePoint hv hh hzc hzP hf hzlam
            (faceReg_forall_of_exists (hfaceReg z hzc hzP hslab))
        · -- wall ∩ face
          refine Work.Drive.Mono.isLocallyEuclidean_trace_of_faceWallJunction hv hh hℓne hzc hzP
            hf hzlam ?_ ?_ ?_
          · intro p hp
            refine hgen.1 lam hne p (by rwa [hp]) ?_ (by rw [hp]; exact hzlam)
            simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq, hp, hf]
            rw [show inner ℝ v c + u + h - (inner ℝ v c + u) = h from by ring, abs_of_pos hh]
          · exact faceReg_forall_of_exists (hfaceReg z hzc hzP hslab)
          · intro p hp t
            have h2 := hgen.2.1 lam hne p (by rwa [hp])
              (by rw [hp, hf]
                  rw [show inner ℝ v c + u + h - (inner ℝ v c + u) = h from by ring,
                    abs_of_pos hh])
              (by rw [hp]; exact hzlam) t
            rw [Work.Drive.EpsForm.sweepHeight_innerSL ψ v]
            exact h2
        · exact absurd hzfr (notMem_frontier_of_mem_interior
            (mem_interior_tiltedLevelRemoved_of_lt hzP hzlam))
      · -- lower face
        rcases lt_trichotomy (ℓ z) lam with hzlam | hzlam | hzlam
        · -- interior of a face
          refine localModel_of_neg (ψ := ψ) (s := s) (u := u) (c := c) (v := v) (σ := σ)
            (h := h) (ℓ := ℓ) (lam := lam) (z := z) ?_
          refine Work.Drive.Mono.isLocallyEuclidean_trace_of_facePoint (ψ := ψ) (s := s) (u := -u)
            (c := c) (σ := σ) (v := -v) (h := h) (ℓ := ℓ) (lam := lam) (z := z)
            (by simpa using hv) hh hzc hzP ?_ hzlam ?_
          · rw [inner_neg_left, inner_neg_left]
            linarith [hf]
          · intro p hp
            exact faceReg_neg (faceReg_forall_of_exists (hfaceReg z hzc hzP hslab) p hp)
        · -- wall ∩ face
          refine localModel_of_neg (ψ := ψ) (s := s) (u := u) (c := c) (v := v) (σ := σ)
            (h := h) (ℓ := ℓ) (lam := lam) (z := z) ?_
          refine Work.Drive.Mono.isLocallyEuclidean_trace_of_faceWallJunction (ψ := ψ) (s := s)
            (u := -u) (c := c) (σ := σ) (v := -v) (h := h) (ℓ := ℓ) (lam := lam) (z := z)
            (by simpa using hv) hh hℓne hzc hzP ?_ hzlam ?_ ?_ ?_
          · rw [inner_neg_left, inner_neg_left]
            linarith [hf]
          · intro p hp
            refine hgen.1 lam hne p (by rwa [hp]) ?_ (by rw [hp]; exact hzlam)
            simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq, hp, hf]
            rw [show inner ℝ v c + u - h - (inner ℝ v c + u) = -h from by ring, abs_neg,
              abs_of_pos hh]
          · intro p hp
            exact faceReg_neg (faceReg_forall_of_exists (hfaceReg z hzc hzP hslab) p hp)
          · intro p hp t
            refine faceTrans_neg2 ?_ t
            intro t'
            have h2 := hgen.2.1 lam hne p (by rwa [hp])
              (by rw [hp, hf]
                  rw [show inner ℝ v c + u - h - (inner ℝ v c + u) = -h from by ring, abs_neg,
                    abs_of_pos hh])
              (by rw [hp]; exact hzlam) t'
            rw [Work.Drive.EpsForm.sweepHeight_innerSL ψ v]
            exact h2
        · exact absurd hzfr (notMem_frontier_of_mem_interior
            (mem_interior_tiltedLevelRemoved_of_lt hzP hzlam))
    · -- outside the slab
      exact absurd hzfr (notMem_frontier_of_mem_interior
        (mem_interior_tiltedLevelRemoved_of_slab_lt hzP hslab))
  · -- ### the point is on the box sphere
    have hbS : Submission.boxNorm c σ z = s := le_antisymm hb_le hge
    rcases lt_trichotomy |inner ℝ v z - (inner ℝ v c + u)| h with hslab | hslab | hslab
    · -- strictly inside the slab
      rcases lt_trichotomy (ℓ z) lam with hzlam | hzlam | hzlam
      · exact absurd (frontier_subset_closure hzfr)
          (notMem_closure_tiltedLevelRemoved_of_slab_below hslab hzlam)
      · -- wall ∩ box sphere: the "V" of the wall and the box sphere
        obtain ⟨p, hp, hF, hB, hind⟩ := hJ.1 lam hlam hne z hzc hbS (le_of_lt hslab) hzlam
        obtain ⟨i, ε, hε, hact, huniq⟩ :=
          unique_activeFace_of_junctionGenC hJ hlam hne hzc hbS (le_of_lt hslab) hzlam
        exact localModel_wallSphere hs hℓne hε hzc hbS hslab hzlam hact huniq
          ⟨p, hp, hF, hB, hind⟩
      · -- above the wall: the trace is the box sphere
        exact localModel_spherePoint_of_lt_level hs hslice hzc hbS hzlam
    · -- on a face of the slab
      rcases hface_or z hslab with hf | hf
      · -- upper face
        rcases lt_trichotomy (ℓ z) lam with hzlam | hzlam | hzlam
        · -- box sphere ∩ face
          obtain ⟨p, hp, hd1, hd2, hd3⟩ := hJ.2.1 lam hlam hne z hzc hbS hslab hzlam
          exact Work.Drive.Mono.isLocallyEuclidean_trace_of_sphereFaceJunction hs hv hh hzc hbS
            hf hzlam ⟨p, hp, hd1, hd2, hd3⟩
        · -- triple point: forbidden by the genericity of the levels of the face points
          exact absurd (by rw [← hzlam]; exact hJ.2.2.2 z hzc hbS hslab) hne
        · exact localModel_spherePoint_of_lt_level hs hslice hzc hbS hzlam
      · -- lower face
        rcases lt_trichotomy (ℓ z) lam with hzlam | hzlam | hzlam
        · -- box sphere ∩ face
          refine localModel_of_neg (ψ := ψ) (s := s) (u := u) (c := c) (v := v) (σ := σ)
            (h := h) (ℓ := ℓ) (lam := lam) (z := z) ?_
          obtain ⟨p, hp, hd1, hd2, hd3⟩ := hJ.2.1 lam hlam hne z hzc hbS hslab hzlam
          refine Work.Drive.Mono.isLocallyEuclidean_trace_of_sphereFaceJunction (ψ := ψ) (s := s)
            (u := -u) (c := c) (σ := σ) (v := -v) (h := h) (ℓ := ℓ) (lam := lam) (z := z)
            hs (by simpa using hv) hh hzc hbS ?_ hzlam ?_
          · rw [inner_neg_left, inner_neg_left]
            linarith [hf]
          · exact ⟨p, hp, fderiv_inner_neg_ne_zero hd1, hd2, fderiv_inner_neg_ne_smul hd3⟩
        · -- triple point
          exact absurd (by rw [← hzlam]; exact hJ.2.2.2 z hzc hbS hslab) hne
        · exact localModel_spherePoint_of_lt_level hs hslice hzc hbS hzlam
    · -- outside the slab: the trace is the box sphere
      exact localModel_spherePoint_outsideSlab hs hslice hzc hbS hslab

end

end Work.Drive.Mono
