import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Mono.TraceLocalModels
import Submission.Work.Drive.Mono.isLocallyEuclidean_trace_of_faceWallJunction
import Submission.Work.Drive.Mono.WallInert
import Submission.Work.Drive.Final.trace_localModel_of_event_off
import Submission.Work.Drive.Mono.trace_locallyEuclidean_of_junctionGen

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-- The derivative of the pulled-back slab functional is the derivative of the pulled-back normal
functional: the shift `⟪v,c⟫ + u` is constant. -/
theorem fderiv_slabFnPar_eq_par (ψ : Submission.Diffeo) (c v : R3) (u : ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p =
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p := by
  have h1 : Work.Drive.Final.slabFnPar ψ c u v =
      fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q) - (inner ℝ v c + u) := rfl
  rw [h1]
  exact fderiv_sub_const _

open LeanEval.KnotTheory.PardonDistortion in
/-- **The local model of the trace at a point of the surface strictly inside the box**, at an
arbitrary (possibly exceptional) level: given the two pointwise regularity clauses of the sweep at
the fibre of `z` (`hgen1`: the sweep height is regular at the level `lam`; `hgen2`: the level is
transverse to the slab faces at the level `lam`) and the face regularity of the slab functional at
`z` (`hfaceReg`), the trace `carrier ∩ frontier (tiltedLevelRemoved s c σ u v h ℓ lam)` is locally
Euclidean of dimension one near `z`.

No hypothesis on the level (regularity of `lam`, membership in a window, absence of events) is used:
the point is deep inside the box (`hzP`), so only the wall and the two slab faces of the frontier
occur, and the three local models `isLocallyEuclidean_trace_of_wallPoint`,
`isLocallyEuclidean_trace_of_facePoint` and `isLocallyEuclidean_trace_of_faceWallJunction` dispatch
on the position of `z`.  The lower slab face is handled by the flip `(u,v) ↦ (-u,-v)` (under which
`tiltedLevelRemoved` is invariant), exactly as in the already-proved
`Work.Drive.Mono.trace_localModel_at_of_localData_lam`
(`Submission/Work/Drive/Final/trace_localModel_of_event_off.lean`), whose *box-interior branch*
is this statement verbatim; the private helpers it uses (`notMem_closure_tiltedLevelRemoved_of_slab_below`,
`mem_interior_tiltedLevelRemoved_of_lt`, `mem_interior_tiltedLevelRemoved_of_slab_lt`,
`notMem_frontier_of_mem_interior`, `boxNorm_le_of_mem_frontier_tiltedLevelRemoved`,
`localModel_of_neg`, `faceReg_neg`, `faceTrans_neg2`, `fderiv_pullback_eq_of_par_eq`,
`faceReg_forall_of_exists` as well as `fderiv_inner_neg_ne_zero`, `fderiv_inner_neg_ne_smul`,
`tiltedLevelRemoved_neg`, `tiltedSlabClosed_neg`, `sweepHeight_neg`, `fderiv_sweepHeight_neg_ne_zero`
and `faceTrans_neg`) live in `Submission/Work/Drive/Mono/TraceLocalModelsJunction.lean` and may be
copied (they are `private` there, so copying is necessary). -/
theorem trace_localModel_inBox {ψ : Submission.Diffeo} {s u h : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {z : R3}
    (hs : 0 < s) (hv : v ≠ 0) (hh : 0 < h) (hℓne : ℓ ≠ 0)
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))
    (hzP : z ∈ Submission.PBox s c σ)
    (hgen1 : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
      Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      Work.BoxShrink.Pinch.par ψ p ∈
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
      ℓ (Work.BoxShrink.Pinch.par ψ p) = lam →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0)
    (hgen2 : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
      Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| = h →
      ℓ (Work.BoxShrink.Pinch.par ψ p) = lam →
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p)
    (hfaceReg : |Work.Drive.Final.slabFn c u v z| = h → ∃ p : ℝ × ℝ,
      Work.BoxShrink.Pinch.par ψ p = z ∧
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ((innerSL ℝ) v)) p ≠ 0) :
    ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  have hzc : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier := hz.1
  have hzfr : z ∈ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) := hz.2
  -- the two faces of the slab, in the form of the normal functional
  have hface_or : ∀ w : R3, |inner ℝ v w - (inner ℝ v c + u)| = h →
      inner ℝ v w = inner ℝ v c + u + h ∨ inner ℝ v w = inner ℝ v c + u - h := by
    intro w hw
    rcases (abs_eq (le_of_lt hh)).mp hw with h2 | h2
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  -- `hfaceReg` in the form of the slab functional
  have hfaceReg' : |inner ℝ v z - (inner ℝ v c + u)| = h →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ (innerSL ℝ v)) p ≠ 0 := by
    intro hzface
    exact hfaceReg (by rw [Work.Drive.Final.slabFn_apply]; exact hzface)
  rcases lt_trichotomy |inner ℝ v z - (inner ℝ v c + u)| h with hslab | hslab | hslab
  · -- ### strictly inside the slab
    rcases lt_trichotomy (ℓ z) lam with hzlam | hzlam | hzlam
    · exact absurd (frontier_subset_closure hzfr)
        (Work.Drive.Mono.notMem_closure_tiltedLevelRemoved_of_slab_below hslab hzlam)
    · -- the interior of the wall
      refine Work.Drive.Mono.isLocallyEuclidean_trace_of_wallPoint hℓne hzc hzP hslab hzlam ?_
      intro p hp
      refine hgen1 p hp (by rwa [hp]) ?_ (by rw [hp]; exact hzlam)
      simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq, hp]
      exact le_of_lt hslab
    · exact absurd hzfr (Work.Drive.Mono.notMem_frontier_of_mem_interior
        (Work.Drive.Mono.mem_interior_tiltedLevelRemoved_of_lt hzP hzlam))
  · -- ### on a face of the slab
    rcases hface_or z hslab with hf | hf
    · -- the upper face
      rcases lt_trichotomy (ℓ z) lam with hzlam | hzlam | hzlam
      · -- the interior of the face
        refine Work.Drive.Mono.isLocallyEuclidean_trace_of_facePoint hv hh hzc hzP hf hzlam ?_
        exact Work.Drive.Mono.fderiv_sweepHeight_forall_of_exists (hfaceReg' hslab)
      · -- the wall meets the face
        refine Work.Drive.Mono.isLocallyEuclidean_trace_of_faceWallJunction hv hh hℓne hzc hzP
          hf hzlam ?_ ?_ ?_
        · intro p hp
          refine hgen1 p hp (by rwa [hp]) ?_ (by rw [hp]; exact hzlam)
          simp only [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq, hp, hf]
          rw [show inner ℝ v c + u + h - (inner ℝ v c + u) = h from by ring, abs_of_pos hh]
        · exact Work.Drive.Mono.fderiv_sweepHeight_forall_of_exists (hfaceReg' hslab)
        · intro p hp t hcon
          refine hgen2 p hp (by rwa [hp]) (by rw [hp, Work.Drive.Final.slabFn_apply]; exact hslab)
            (by rw [hp]; exact hzlam) t ?_
          rw [hcon, Work.Drive.EpsForm.sweepHeight_innerSL ψ v,
            fderiv_slabFnPar_eq_par ψ c v u p]
      · exact absurd hzfr (Work.Drive.Mono.notMem_frontier_of_mem_interior
          (Work.Drive.Mono.mem_interior_tiltedLevelRemoved_of_lt hzP hzlam))
    · -- the lower face: flip `(u,v) ↦ (-u,-v)`
      rcases lt_trichotomy (ℓ z) lam with hzlam | hzlam | hzlam
      · -- the interior of the face
        refine Work.Drive.Mono.localModel_of_neg ?_
        refine Work.Drive.Mono.isLocallyEuclidean_trace_of_facePoint (ψ := ψ) (s := s) (u := -u)
          (c := c) (σ := σ) (v := -v) (h := h) (ℓ := ℓ) (lam := lam) (z := z)
          (by simpa using hv) hh hzc hzP ?_ hzlam ?_
        · rw [inner_neg_left, inner_neg_left]
          linarith [hf]
        · intro p hp
          exact Work.Drive.Mono.faceReg_neg
            (Work.Drive.Mono.fderiv_sweepHeight_forall_of_exists (hfaceReg' hslab) p hp)
      · -- the wall meets the face
        refine Work.Drive.Mono.localModel_of_neg ?_
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
          exact Work.Drive.Mono.faceReg_neg
            (Work.Drive.Mono.fderiv_sweepHeight_forall_of_exists (hfaceReg' hslab) p hp)
        · intro p hp t
          refine Work.Drive.Mono.faceTrans_neg2 ?_ t
          intro t'
          have h2 := hgen2 p hp (by rwa [hp])
            (by rw [hp, Work.Drive.Final.slabFn_apply]; exact hslab) (by rw [hp]; exact hzlam) t'
          rw [Work.Drive.EpsForm.sweepHeight_innerSL ψ v]
          rwa [fderiv_slabFnPar_eq_par ψ c v u p] at h2
      · exact absurd hzfr (Work.Drive.Mono.notMem_frontier_of_mem_interior
          (Work.Drive.Mono.mem_interior_tiltedLevelRemoved_of_lt hzP hzlam))
  · -- ### outside the slab
    exact absurd hzfr (Work.Drive.Mono.notMem_frontier_of_mem_interior
      (Work.Drive.Mono.mem_interior_tiltedLevelRemoved_of_slab_lt hzP hslab))

end

end Work.Drive.Final
