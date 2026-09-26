import Mathlib
import Submission.Work.Drive.Mono.SweepGeom3
import Submission.Work.Drive.Mono.traceLocallyEuclidean_of_junctionGenC
import Submission.Work.Drive.Mono.JunctionGenC
import Submission.Work.Drive.Mono.frontier_tiltedLevelRemoved_sphereFace
import Submission.Work.Drive.Mono.trace_localModel_of_not_event

/-!
# The local model of the trace at a point carrying no event

`Work.Drive.Mono.traceLocallyEuclidean_of_junctionGenC` proves the local models of the trace at
every point of a level which is **not exceptional** (`lam ∉ exc`): the erasure device
(`Work.Drive.Mono.trace_localModel_of_not_event`) even removes the level from `exc` when no event
of the sweep (`Work.Drive.Final.IsAnyEvent`) lies *at* that level.

The present module is the pointwise version of that statement, which is the one the (L) route
consumes: at a level which *does* carry an event somewhere else, a point `z` of the trace whose
**fibre** carries no event is still a regular point of the sweep, and has a neighbourhood in which
the trace is locally Euclidean of dimension one.

Everything the assembly of `traceLocallyEuclidean_of_junctionGenC` uses of the bundles `TiltData`
and `JunctionGenC` is used

* at the level `lam` only,
* at the points `p` of the parameter plane with `Pinch.par ψ p = z` (the genericity clauses of the
  sweep height — clauses (i) and (ii) of `TiltedGenericity`, applied to preimages of `z`), and
* at the point `z` itself (the junction clauses (a), (b), (d) of `JunctionGenC`).

Each of those instances is available from the raw data together with the pointwise hypothesis
`¬ IsAnyEvent` at the fibre of `z`:

* clause (i) is the refusal of `IsEvent` (`IsEvent` is exactly `PBox ∧ slabClosed ∧ fderiv = 0`);
* clause (ii) is the refusal of `IsFaceEvent` (`IsFaceEvent` is exactly `PBox ∧ |slab| = h` and the
  tangency of the two differentials, the two forms of which are `fderiv_slabFnPar_eq_aux`);
* clause (a) is the *universal* `GammaTransverse` of `GoodSweepData3`, which mentions no level;
* clause (b) is level-independent in its conclusion and is read off at an auxiliary level above
  `max lam0 (ℓ z)` avoiding `exc`;
* clause (c) is vacuous by `EdgeFree` (a point of the closed slab with two extremal box coordinates
  contradicts it), which also gives the uniqueness of the active box face;
* clause (d) is the refusal of `IsCornerEvent` (`IsCornerEvent` is exactly `closure PBox`,
  `boxNorm = s` and `|slab| = h`).

The target `Work.Drive.Mono.trace_locallyEuclidean_at_of_noEventAt` is the instance of the local
assembly at the fields of `Work.Drive.Mono.GoodDataPackage3`.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-! ## 1. The uniqueness of the active box face, from `EdgeFree` -/

/-- **The active face of the box sphere at a point of the surface in the closed slab is unique**,
with clause (c) of `JunctionGenC` replaced by `EdgeFree`: under `EdgeFree` a point of the surface
with two extremal box coordinates lies strictly outside the closed slab, so the hypothesis of
clause (c) is empty.  This is `Work.Drive.Mono.unique_activeFace_of_junctionGenC` with that
substitution at its last step. -/
theorem unique_activeFace_of_edgeFree {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {h : ℝ} {z : R3}
    (hEF : EdgeFree ψ s c σ u v h) (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzS : Submission.boxNorm c σ z = s)
    (hslab : |inner ℝ v z - (inner ℝ v c + u)| ≤ h) :
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
    exact absurd (hEF z hz hzS hext) (not_lt.mpr hslab)

/-! ## 2. The two junction clauses at a point of the box sphere -/

/-- **Clause (a) of `JunctionGenC` at a point of the surface on the box sphere inside the closed
slab**, from the universal `GammaTransverse` of `GoodSweepData3`.  The non-vanishing of the
derivative of the sweep height is the case `t = 0` of the transversality. -/
theorem junctionClauseA_of_gammaTransverse {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {z : R3}
    (hΓ : ∀ p : ℝ × ℝ, Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| ≤ h →
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ
          (Work.BoxShrink.Pinch.par ψ q)) p)
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzS : Submission.boxNorm c σ z = s)
    (hslab : |inner ℝ v z - (inner ℝ v c + u)| ≤ h) :
    ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0 ∧
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ
          (Work.BoxShrink.Pinch.par ψ q)) p := by
  obtain ⟨p, hp⟩ := (show z ∈ Set.range (Work.BoxShrink.Pinch.par ψ) from hz)
  obtain ⟨hd, hind⟩ := hΓ p (by rw [hp]; exact hzS)
    (by rw [hp, Work.Drive.Final.slabFn_apply]; exact hslab)
  exact ⟨p, hp, (fun h0 => hind 0 (by rw [h0, zero_smul])), hd, hind⟩

/-- **Clause (b) of `JunctionGenC` at a box-sphere point of a slab face, at an arbitrary level of
the window**: the clause is level-independent in its conclusion (its hypothesis is `ℓ z < β` and
its conclusion does not mention `β`), so it is read off at an auxiliary non-exceptional level above
`max lam0 (ℓ z)`, which exists because `exc` is finite and `lam0 < lam1`. -/
theorem junctionClauseB_at {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ} {z : R3}
    (hJ : JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1) (h01 : lam0 < lam1)
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzS : Submission.boxNorm c σ z = s)
    (hslab : |inner ℝ v z - (inner ℝ v c + u)| = h) (hlt : ℓ z < lam1) :
    ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ
          (Work.BoxShrink.Pinch.par ψ q)) p := by
  have hmax : max lam0 (ℓ z) < lam1 := max_lt h01 hlt
  obtain ⟨β, hβ1, hβ2, hβ3⟩ := exists_level_gt_finset exc hmax
  exact hJ.2.1 β ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hβ1), le_of_lt hβ2⟩ hβ3 z hz hzS hslab
    (lt_of_le_of_lt (le_max_right _ _) hβ1)

/-! ## 3. The local assembly at a point carrying no event -/

/-- **The local models of the trace at a point whose fibre carries no event**, from the raw
pieces of `Work.Drive.Mono.GoodDataPackage3`.  This is the assembly
`Work.Drive.Mono.traceLocallyEuclidean_of_junctionGenC` with every instance of the bundles
`TiltData` and `JunctionGenC` replaced by the pointwise derivation described in the header: the
genericity clauses of the sweep height at the preimages of `z` (`hnoev`), and the junction clauses of
`JunctionGenC` at `z` (from `GammaTransverse`, the auxiliary level, `EdgeFree`, and `hnoev`). -/
theorem trace_localModel_at_of_localData {ψ : Submission.Diffeo} {s u : ℝ} {c v : R3}
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
    (hnoev : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
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
    exact hnoev p hp (Or.inl ⟨hP, hS, h0⟩)
  -- clause (ii) of `TiltedGenericity` at the preimages of `z`, from `hnoev`
  have hgen2 : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
      Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      |inner ℝ v (Work.BoxShrink.Pinch.par ψ p) - (inner ℝ v c + u)| = h →
      ℓ (Work.BoxShrink.Pinch.par ψ p) = lam →
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p := by
    intro p hp hP hf hℓ t ht
    exact hnoev p hp (Or.inr (Or.inl ⟨hP, by rw [Work.Drive.Final.slabFn_apply]; exact hf,
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
            Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p) (hnoev p hp)
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
            Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p) (hnoev p hp)
        · exact localModel_spherePoint_of_lt_level hs hslice hzc hbS hzlam
    · -- outside the slab: the trace is the box sphere
      exact localModel_spherePoint_outsideSlab hs hslice hzc hbS hslab

/-! ## 4. The requested lemma -/

/-- **A trace point whose fibre carries no event is locally Euclidean**, at the data of
`Work.Drive.Mono.GoodDataPackage3`.

The hypothesis `hnoev` is pointwise at `z`: no lift of `z` to the parameter plane is an event of the
sweep (of any of the three types `IsEvent`, `IsFaceEvent`, `IsCornerEvent`).  The conclusion is the
local model of the trace at `z`: `z` has an open neighbourhood in which the trace
`carrier ∩ frontier (tiltedLevelRemoved … lam)` is locally Euclidean of dimension one. -/
theorem trace_locallyEuclidean_at_of_noEventAt
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
    (hnoev : ∀ qq : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ qq = z →
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
  exact trace_localModel_at_of_localData hs hslice hfaceReg hv hℓne hh hJ hEF hΓ hlam hl01 hnoev hz

end

end Work.Drive.Mono
