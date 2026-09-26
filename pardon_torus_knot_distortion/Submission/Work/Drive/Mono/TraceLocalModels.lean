import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.Drive.Mono.LevelSetLocallyEuclidean_holds
import Submission.Work.Drive.Mono.Trace_eq_levelSet_near_wallPoint_holds
import Submission.Work.Drive.Mono.Trace_eq_planeNear_facePoint_holds

/-!
# The local models of the trace of the tilted sweep (lower module)

The pointwise local models of the trace at the *non-junction* point types are self-contained: a point
of the level wall (inside the box, strictly inside the slab, at the level, with the sweep height
regular there) and a point of a slab face (inside the box, strictly below the level).  They consume
only the two proved coincidence statements `Trace_eq_levelSet_near_wallPoint_holds` /
`Trace_eq_planeNear_facePoint_holds` and the regularity of the level set
(`LevelSetLocallyEuclidean_holds`), so they are kept in this *lower* module: the junction assembly
(`Submission/Work/Drive/Mono/trace_locallyEuclidean_of_junctionGen.lean`) and the deliverable both
need them, and keeping them here breaks the import cycle between the two.

Also kept here: the compactness of the trace of a level (`isCompact_trace_torusOf`), the compactness
input of clause 1.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

noncomputable section

/-- **(P1)(a), wall type: the trace is locally Euclidean at a point of the level wall.**

Let `z` be a point of the surface in the box, strictly inside the closed slab and at the level `lam`,
with the sweep height regular at `z` (clause (i) of `TiltedGenericity` at the level `lam`, away from
`exc`).  Then the trace of the level — the surface's part of the frontier of the level's removed set —
coincides near `z` with the level set `carrier ∩ {ℓ = lam}` (delegated as
`Work.Drive.Mono.Trace_eq_levelSet_near_wallPoint_holds`) and that level set is locally Euclidean of
dimension one at `z` (delegated as `Work.Drive.Mono.LevelSetLocallyEuclidean_holds`); hence so is the
trace.

This is one of the local models of clause 1 of the trace data.  The remaining point types of the trace
are the slab faces, the box sphere, and the junctions between them. -/
theorem isLocallyEuclidean_trace_of_wallPoint {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {z : R3}
    (hℓne : ℓ ≠ 0) (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzb : z ∈ Submission.PBox s c σ)
    (hzslab : |inner ℝ v z - (inner ℝ v c + u)| < h) (hzl : ℓ z = lam)
    (hreg : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0) :
    ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  obtain ⟨O₁, hO₁open, hzO₁, hO₁⟩ :=
    Work.Drive.Mono.Trace_eq_levelSet_near_wallPoint_holds
      (P := Work.Drive.EpsSphere.torusOf ψ) hℓne hz hzb hzslab hzl
  obtain ⟨O₂, hO₂open, hzO₂, hO₂⟩ :=
    Work.Drive.Mono.LevelSetLocallyEuclidean_holds ψ ℓ hz hzl hreg
  refine ⟨O₁ ∩ O₂, hO₁open.inter hO₂open, ⟨hzO₁, hzO₂⟩, ?_⟩
  have hEq : (O₁ ∩ O₂) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) =
      (O₁ ∩ O₂) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ {y : R3 | ℓ y = lam}) := by
    ext x
    constructor
    · rintro ⟨hxO, hxtrace⟩
      have hx : x ∈ O₁ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) := ⟨hxO.1, hxtrace⟩
      rw [hO₁] at hx
      exact ⟨hxO, ⟨hx.1.2, hx.2⟩⟩
    · rintro ⟨hxO, hxmem⟩
      have hx : x ∈ (O₁ ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) ∩
          {y : R3 | ℓ y = lam} := ⟨⟨hxO.1, hxmem.1⟩, hxmem.2⟩
      rw [← hO₁] at hx
      exact ⟨hxO, hx.2⟩
  rw [hEq]
  have hO₂' : Work.Smooth.OneManifold.IsLocallyEuclidean
      (O₂ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ {y : R3 | ℓ y = lam})) :=
    Work.Smooth.OneManifold.isLocallyEuclidean_of_eq
      (by ext x; simp only [Set.mem_inter_iff]; tauto) hO₂
  refine Work.Smooth.OneManifold.IsLocallyEuclidean.of_isOpenIn
    (Z := O₂ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ {y : R3 | ℓ y = lam}))
    (V := (O₁ ∩ O₂) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ {y : R3 | ℓ y = lam}))
    ?_ ?_ hO₂'
  · rintro x ⟨hxO, hxmem⟩
    exact ⟨hxO.2, hxmem⟩
  · show IsOpen (((Subtype.val ⁻¹' ((O₁ ∩ O₂) ∩
        ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ {y : R3 | ℓ y = lam}))) :
      Set ↥(O₂ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ {y : R3 | ℓ y = lam}))))
    have hVeq : ((Subtype.val ⁻¹' ((O₁ ∩ O₂) ∩
          ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ {y : R3 | ℓ y = lam}))) :
        Set ↥(O₂ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ {y : R3 | ℓ y = lam})))
        = (Subtype.val ⁻¹' O₁ :
            Set ↥(O₂ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ {y : R3 | ℓ y = lam}))) := by
      ext z
      constructor
      · intro hz
        exact hz.1.1
      · intro hz
        exact ⟨⟨hz, z.2.1⟩, z.2.2⟩
    rw [hVeq]
    exact hO₁open.preimage continuous_subtype_val



/-- **(P1)(a), face type: the trace is locally Euclidean at a point of a slab face.**

Let `z` be a point of the surface in the box, on the *upper* slab face (`⟪v,z⟫ = ⟪v,c⟫ + u + h`) and
strictly below the level (`ℓ z < lam`).  Then the trace of the level coincides near `z` with the
surface's intersection with the face plane (delegated as
`Work.Drive.Mono.Trace_eq_planeNear_facePoint_holds`), and that intersection is locally Euclidean of
dimension one at `z` provided the plane crosses the surface transversally there — which is the
regularity hypothesis of `Work.Drive.Mono.LevelSetLocallyEuclidean_holds` applied to the functional
`⟪v,·⟫` (clause (ii) of `TiltedGenericity`, the height regular on the slab faces). -/
theorem isLocallyEuclidean_trace_of_facePoint {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {z : R3}
    (hv : v ≠ 0) (hh : 0 < h) (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzb : z ∈ Submission.PBox s c σ)
    (hzface : inner ℝ v z = inner ℝ v c + u + h) (hzl : ℓ z < lam)
    (hreg : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ (innerSL ℝ v)) p ≠ 0) :
    ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  obtain ⟨O₁, hO₁open, hzO₁, hO₁⟩ :=
    Work.Drive.Mono.Trace_eq_planeNear_facePoint_holds
      (P := Work.Drive.EpsSphere.torusOf ψ) hv hh hz hzb hzface hzl
  have hzlvl : (innerSL ℝ v) z = inner ℝ v c + u + h := by
    rw [innerSL_apply_apply]
    exact hzface
  obtain ⟨O₂, hO₂open, hzO₂, hO₂⟩ :=
    Work.Drive.Mono.LevelSetLocallyEuclidean_holds ψ (innerSL ℝ v) hz hzlvl hreg
  -- rewrite the level set of `⟪v,·⟫` as the face plane
  have hO₂' : Work.Smooth.OneManifold.IsLocallyEuclidean
      (O₂ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        {y : R3 | inner ℝ v y = inner ℝ v c + u + h})) :=
    Work.Smooth.OneManifold.isLocallyEuclidean_of_eq
      (by ext y; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]; tauto) hO₂
  refine ⟨O₁ ∩ O₂, hO₁open.inter hO₂open, ⟨hzO₁, hzO₂⟩, ?_⟩
  have hEq : (O₁ ∩ O₂) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) =
      (O₁ ∩ O₂) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        {y : R3 | inner ℝ v y = inner ℝ v c + u + h}) := by
    ext x
    constructor
    · rintro ⟨hxO, hxtrace⟩
      have hx : x ∈ O₁ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) := ⟨hxO.1, hxtrace⟩
      rw [hO₁] at hx
      exact ⟨hxO, ⟨hx.1.2, hx.2⟩⟩
    · rintro ⟨hxO, hxmem⟩
      have hx : x ∈ (O₁ ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) ∩
          {y : R3 | inner ℝ v y = inner ℝ v c + u + h} := ⟨⟨hxO.1, hxmem.1⟩, hxmem.2⟩
      rw [← hO₁] at hx
      exact ⟨hxO, hx.2⟩
  rw [hEq]
  have hO₂'' : Work.Smooth.OneManifold.IsLocallyEuclidean
      (O₂ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        {y : R3 | inner ℝ v y = inner ℝ v c + u + h})) := hO₂'
  refine Work.Smooth.OneManifold.IsLocallyEuclidean.of_isOpenIn
    (Z := O₂ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      {y : R3 | inner ℝ v y = inner ℝ v c + u + h}))
    (V := (O₁ ∩ O₂) ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      {y : R3 | inner ℝ v y = inner ℝ v c + u + h}))
    ?_ ?_ hO₂''
  · rintro x ⟨hxO, hxmem⟩
    exact ⟨hxO.2, hxmem⟩
  · show IsOpen (((Subtype.val ⁻¹' ((O₁ ∩ O₂) ∩
        ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          {y : R3 | inner ℝ v y = inner ℝ v c + u + h}))) :
      Set ↥(O₂ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        {y : R3 | inner ℝ v y = inner ℝ v c + u + h}))))
    have hVeq : ((Subtype.val ⁻¹' ((O₁ ∩ O₂) ∩
          ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
            {y : R3 | inner ℝ v y = inner ℝ v c + u + h}))) :
        Set ↥(O₂ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          {y : R3 | inner ℝ v y = inner ℝ v c + u + h})))
        = (Subtype.val ⁻¹' O₁ :
            Set ↥(O₂ ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
              {y : R3 | inner ℝ v y = inner ℝ v c + u + h}))) := by
      ext w
      constructor
      · intro hw
        exact hw.1.1
      · intro hw
        exact ⟨⟨hw, w.2.1⟩, w.2.2⟩
    rw [hVeq]
    exact hO₁open.preimage continuous_subtype_val


/-! ## Compactness of the trace -/

/-- **The trace of a level is compact** (for the torus of a diffeomorphism, whose carrier is compact):
it is the intersection of the carrier with the frontier of the level's removed set, and a frontier is
closed.  This is the compactness input of `traceCurvesAt_of_isLocallyEuclidean`. -/
theorem isCompact_trace_torusOf (ψ : Submission.Diffeo) (s u : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (v : R3) (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam : ℝ) :
    IsCompact ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) :=
  (Work.Smooth.Morse.Surface.isCompact_torus ψ).of_isClosed_subset
    ((Work.Smooth.Morse.Surface.isCompact_torus ψ).isClosed.inter isClosed_frontier)
    (fun y hy => hy.1)


end

end Work.Drive.Mono
