import Mathlib
import Submission.Work.Drive.Mono.trace_locallyEuclidean_at_of_noEventAt
import Submission.Work.Drive.Mono.SweepGeom3

/-!
# The local model of the trace at a point whose *level* fibre carries no event

`Work.Drive.Mono.trace_locallyEuclidean_at_of_noEventAt` proves the local model of the trace at a
point `z` whose whole fibre over `Pinch.par ψ` is event-free.  The (L) route consumes only the
*level-restricted* version: `z` may well be the image of an event of the sweep, as long as no event
of the sweep that is an event **at the level `lam`** maps to `z`.

This module proves that restricted statement.  The proof is the assembly
`Work.Drive.Mono.trace_localModel_at_of_localData` with its hypothesis `hnoev` weakened to
`hnoevLam`: every use of `hnoev` in that assembly occurs at a point `p` with
`ℓ (Pinch.par ψ p) = lam` (in the two genericity clauses of the sweep height, where the level
equation is a hypothesis, and in the two corner-event contradictions, where the branch carries
`ℓ z = lam` and `Pinch.par ψ p = z`), so the restricted hypothesis suffices verbatim.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

theorem trace_localModel_at_of_localData_lam {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 lam : ℝ}
    {z : R3}
    (hs : 0 < s)
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      (Work.BoxShrink.Core.sphereSet c σ s)))
    (hfaceReg : ∀ y : R3,
      y ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → y ∈ Submission.PBox s c σ →
      |inner ℝ v y - (inner ℝ v c + u)| = h →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = y ∧
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0)
    (hv : v ≠ 0) (hℓne : ℓ ≠ 0) (hh : 0 < h)
    (hJ : JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1)
    (hEF : EdgeFree ψ s c σ u v h)
    (hΓ : ∀ p : ℝ × ℝ, Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| ≤ h →
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ
          (Work.BoxShrink.Pinch.par ψ q)) p)
    (hlam : lam ∈ Set.Icc lam0 lam1) (hl01 : lam0 < lam1)
    (hnoevLam : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
      ℓ (Work.BoxShrink.Pinch.par ψ p) = lam →
      ¬ Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p)
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) :
    ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  -- clause (i) of `TiltedGenericity` at the preimages of `z`, from `hnoev`
  have hgen1 : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
      Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      Work.BoxShrink.Pinch.par ψ p ∈
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
      ℓ (Work.BoxShrink.Pinch.par ψ p) = lam →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0 := by
    intro p hp hP hS hℓ h0
    exact hnoevLam p hp hℓ (Or.inl ⟨hP, hS, h0⟩)
  -- clause (ii) of `TiltedGenericity` at the preimages of `z`, from `hnoev`
  have hgen2 : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
      Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| = h →
      ℓ (Work.BoxShrink.Pinch.par ψ p) = lam →
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p := by
    intro p hp hP hf hℓ t ht
    exact hnoevLam p hp hℓ (Or.inr (Or.inl ⟨hP, by rw [Work.Drive.Final.slabFn_apply]; exact hf,
      ⟨t, by rw [fderiv_slabFnPar_eq_aux]; exact ht⟩⟩))
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
        refine hgen1 p hp (by rwa [hp]) ?_ (by rw [hp]; exact hzlam)
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
            refine hgen1 p hp (by rwa [hp]) ?_ (by rw [hp]; exact hzlam)
            simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq, hp, hf]
            rw [show inner ℝ v c + u + h - (inner ℝ v c + u) = h from by ring, abs_of_pos hh]
          · exact faceReg_forall_of_exists (hfaceReg z hzc hzP hslab)
          · intro p hp t
            have h2 := hgen2 p hp (by rwa [hp])
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
            refine hgen1 p hp (by rwa [hp]) ?_ (by rw [hp]; exact hzlam)
            simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq, hp, hf]
            rw [show inner ℝ v c + u - h - (inner ℝ v c + u) = -h from by ring, abs_neg,
              abs_of_pos hh]
          · intro p hp
            exact faceReg_neg (faceReg_forall_of_exists (hfaceReg z hzc hzP hslab) p hp)
          · intro p hp t
            refine faceTrans_neg2 ?_ t
            intro t'
            have h2 := hgen2 p hp (by rwa [hp])
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
        obtain ⟨p, hp, hF, hB, hind⟩ := junctionClauseA_of_gammaTransverse hΓ hzc hbS (le_of_lt hslab)
        obtain ⟨i, ε, hε, hact, huniq⟩ :=
          unique_activeFace_of_edgeFree hEF hzc hbS (le_of_lt hslab)
        exact localModel_wallSphere hs hℓne hε hzc hbS hslab hzlam hact huniq
          ⟨p, hp, hF, hB, hind⟩
      · -- above the wall: the trace is the box sphere
        exact localModel_spherePoint_of_lt_level hs hslice hzc hbS hzlam
    · -- on a face of the slab
      rcases hface_or z hslab with hf | hf
      · -- upper face
        rcases lt_trichotomy (ℓ z) lam with hzlam | hzlam | hzlam
        · -- box sphere ∩ face
          obtain ⟨p, hp, hd1, hd2, hd3⟩ := junctionClauseB_at hJ hl01 hzc hbS hslab (lt_of_lt_of_le hzlam hlam.2)
          exact Work.Drive.Mono.isLocallyEuclidean_trace_of_sphereFaceJunction hs hv hh hzc hbS
            hf hzlam ⟨p, hp, hd1, hd2, hd3⟩
        · -- triple point: forbidden by the genericity of the levels of the face points
          obtain ⟨p, hp⟩ : ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z := hzc
          exact absurd (Or.inr (Or.inr (show Work.Drive.Final.IsCornerEvent ψ s c σ u v h p from
            ⟨by rw [hp]; exact mem_closure_PBox_of_boxNorm_eq hs hbS, by rw [hp]; exact hbS,
             by rw [hp, Work.Drive.Final.slabFn_apply]; exact hslab⟩)) :
            Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p) (hnoevLam p hp (by rw [hp]; exact hzlam))
        · exact localModel_spherePoint_of_lt_level hs hslice hzc hbS hzlam
      · -- lower face
        rcases lt_trichotomy (ℓ z) lam with hzlam | hzlam | hzlam
        · -- box sphere ∩ face
          refine localModel_of_neg (ψ := ψ) (s := s) (u := u) (c := c) (v := v) (σ := σ)
            (h := h) (ℓ := ℓ) (lam := lam) (z := z) ?_
          obtain ⟨p, hp, hd1, hd2, hd3⟩ := junctionClauseB_at hJ hl01 hzc hbS hslab (lt_of_lt_of_le hzlam hlam.2)
          refine Work.Drive.Mono.isLocallyEuclidean_trace_of_sphereFaceJunction (ψ := ψ) (s := s)
            (u := -u) (c := c) (σ := σ) (v := -v) (h := h) (ℓ := ℓ) (lam := lam) (z := z)
            hs (by simpa using hv) hh hzc hbS ?_ hzlam ?_
          · rw [inner_neg_left, inner_neg_left]
            linarith [hf]
          · exact ⟨p, hp, fderiv_inner_neg_ne_zero hd1, hd2, fderiv_inner_neg_ne_smul hd3⟩
        · -- triple point
          obtain ⟨p, hp⟩ : ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z := hzc
          exact absurd (Or.inr (Or.inr (show Work.Drive.Final.IsCornerEvent ψ s c σ u v h p from
            ⟨by rw [hp]; exact mem_closure_PBox_of_boxNorm_eq hs hbS, by rw [hp]; exact hbS,
             by rw [hp, Work.Drive.Final.slabFn_apply]; exact hslab⟩)) :
            Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p) (hnoevLam p hp (by rw [hp]; exact hzlam))
        · exact localModel_spherePoint_of_lt_level hs hslice hzc hbS hzlam
    · -- outside the slab: the trace is the box sphere
      exact localModel_spherePoint_outsideSlab hs hslice hzc hbS hslab

end

end Work.Drive.Mono

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

theorem trace_localModel_of_event_off
    {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s u : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h R : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    {p q : ℕ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {lam : ℝ} (hlam : lam ∈ Set.Icc lam0 lam1)
    {z : LeanEval.KnotTheory.PardonDistortion.R3}
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))
    (hnoevLam : ∀ qq : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ qq = z →
      ℓ (Work.BoxShrink.Pinch.par ψ qq) = lam →
      ¬ Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ qq) :
    ∃ O : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  obtain ⟨hData, hG3, -⟩ := hDP
  obtain ⟨-, hEF, -, -, hΓ, -, -, -, -, -⟩ := hG3
  obtain ⟨hT, hJ, hfaceReg, hslabCuts, hslice, -, -⟩ := hData
  obtain ⟨-, hv1, hℓne, -, -, hh, -, -, -, hl01, -⟩ := hT
  have hv : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv1
    exact one_ne_zero hv1.symm
  have hs : 0 < s := by
    obtain ⟨y, hyP, -⟩ := hslabCuts.1
    have h1 : Submission.boxNorm c σ y < s := (Submission.mem_PBox_iff s c σ y).mp hyP
    have h2 : 0 ≤ Submission.boxNorm c σ y := Submission.boxNorm_nonneg c σ y
    linarith
  exact Work.Drive.Mono.trace_localModel_at_of_localData_lam hs hslice hfaceReg hv hℓne hh hJ hEF hΓ hlam hl01 hnoevLam hz

end

end Work.Drive.Final
