import Mathlib
import Submission.Work.Smooth.OneManifold.levelSet_isLocallyEuclidean_of_regularValue
import Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_uniqueActiveFace

/-!
# The box-norm level set is locally Euclidean at a point with a unique active face

If a single signed face `(i, ε)` of the box sphere of level `s > 0` is tight at `y` and the two
other faces are strictly inactive, then the box norm agrees with the smooth function
`faceLin c σ i ε = ε * signedFace c σ i` on a neighbourhood of `y`
(`Work.Smooth.BoxGeneric.LocalSurface.eventually_boxNorm_eq_faceLin`).  Hence, near `y`, the
box-norm level set coincides with the level set `F ∩ {signedFace c σ i = ε * s}` — a level set of a
smooth function at a *regular* value (`ε * s` is a regular value of `signedFace c σ i`, which is the
a.e. hypothesis of the box chapter) — and such a level set is locally Euclidean of dimension one
(`Work.Smooth.OneManifold.levelSet_isLocallyEuclidean_of_regularValue`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.OneManifold

noncomputable section

open scoped Topology

/-- **The box-norm level set is locally Euclidean at a point with a unique active face.** -/
theorem isLocallyEuclideanAt_of_uniqueActiveFace {ψ : Submission.Diffeo} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {s : ℝ} {y : R3} {i : Fin 3} {ε : ℝ} (hs : 0 < s)
    (hε : ε = 1 ∨ ε = -1) (hy : y ∈ (Work.Smooth.Morse.torus ψ).carrier)
    (hact : Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε y)
    (huniq : ∀ j : Fin 3, j ≠ i → Work.Smooth.BoxGeneric.faceNorm c σ j y < s)
    (hreg : Work.Smooth.Morse.IsRegularValue ψ (Work.Smooth.BoxGeneric.signedFace c σ i)
      (ε * s)) :
    ∃ U : Set R3, Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) U ∧ y ∈ U ∧
      IsLocallyEuclidean (U ∩ Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) := by
  -- the box norm is the active face near `y`
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.mem_nhds_iff.mp
    (Work.Smooth.BoxGeneric.LocalSurface.eventually_boxNorm_eq_faceLin hs hε hact huniq)
  -- the regular level set of the signed face
  have hloc : IsLocallyEuclidean
      (Work.Smooth.Morse.levelSet ψ (Work.Smooth.BoxGeneric.signedFace c σ i) (ε * s)) :=
    levelSet_isLocallyEuclidean_of_regularValue ψ
      ((Work.Smooth.BoxGeneric.contDiff_signedFace c σ i).of_le (by simp)) hreg
  -- the open neighbourhood of `y`
  set U : Set R3 := (Work.Smooth.Morse.torus ψ).carrier ∩ Metric.ball y δ₀ with hUdef
  have hUopen : Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) U := by
    have h1 : (Subtype.val ⁻¹' U : Set (Work.Smooth.Morse.torus ψ).carrier)
        = Subtype.val ⁻¹' Metric.ball y δ₀ := by
      ext z
      rw [hUdef]
      exact ⟨fun h => h.2, fun h => ⟨z.2, h⟩⟩
    rw [Work.SurgeryInvariance.IsOpenInCarrier, h1]
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  have hyU : y ∈ U := ⟨hy, Metric.mem_ball_self hδ₀pos⟩
  refine ⟨U, hUopen, hyU, ?_⟩
  -- identify the box-norm level set with the signed-face level set on `U`
  have hUsub : U ∩ Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s
      = U ∩ Work.Smooth.Morse.levelSet ψ (Work.Smooth.BoxGeneric.signedFace c σ i) (ε * s) := by
    ext x
    constructor
    · rintro ⟨hxU, hxZ⟩
      obtain ⟨hxcar, hxbox⟩ := Work.Smooth.Morse.mem_levelSet.mp hxZ
      have hxball : x ∈ Metric.ball y δ₀ := by
        rw [hUdef] at hxU
        exact hxU.2
      refine ⟨hxU, Work.Smooth.Morse.mem_levelSet.mpr ⟨hxcar, ?_⟩⟩
      have h1 : Work.Smooth.BoxGeneric.faceLin c σ i ε x = s := by
        rw [← hδ₀ hxball, hxbox]
      rcases hε with hε1 | hε1
      · rw [hε1, Work.Smooth.BoxGeneric.faceLin_one] at h1
        rw [hε1, one_mul]
        exact h1
      · rw [hε1, Work.Smooth.BoxGeneric.faceLin_neg_one] at h1
        rw [hε1]
        linarith
    · rintro ⟨hxU, hxZ⟩
      obtain ⟨hxcar, hxface⟩ := Work.Smooth.Morse.mem_levelSet.mp hxZ
      have hxball : x ∈ Metric.ball y δ₀ := by
        rw [hUdef] at hxU
        exact hxU.2
      refine ⟨hxU, Work.Smooth.Morse.mem_levelSet.mpr ⟨hxcar, ?_⟩⟩
      rw [hδ₀ hxball]
      rcases hε with hε1 | hε1
      · rw [hε1, one_mul] at hxface
        rw [hε1, Work.Smooth.BoxGeneric.faceLin_one]
        exact hxface
      · rw [hε1] at hxface
        rw [hε1, Work.Smooth.BoxGeneric.faceLin_neg_one]
        linarith
  rw [hUsub]
  -- restrict the regular level set to the (relatively) open set `U`
  have hZsub : Work.Smooth.Morse.levelSet ψ (Work.Smooth.BoxGeneric.signedFace c σ i) (ε * s)
      ⊆ (Work.Smooth.Morse.torus ψ).carrier :=
    Work.Smooth.Morse.levelSet_subset_carrier _ _ _
  have hVopen : IsOpenInSet
      (Work.Smooth.Morse.levelSet ψ (Work.Smooth.BoxGeneric.signedFace c σ i) (ε * s))
      (U ∩ Work.Smooth.Morse.levelSet ψ (Work.Smooth.BoxGeneric.signedFace c σ i) (ε * s)) :=
    isOpenInSet_inter_of_isOpenInCarrier hZsub hUopen
  exact IsLocallyEuclidean.of_isOpenIn inter_subset_right hVopen hloc

end

end Work.Smooth.OneManifold
