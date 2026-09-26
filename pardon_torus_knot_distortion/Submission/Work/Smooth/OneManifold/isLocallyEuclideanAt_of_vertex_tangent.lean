import Mathlib
import Submission.Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param
import Submission.Work.Smooth.OneManifold.Plane.Vertex
import Submission.Work.Smooth.BoxGeneric.LocalSurface.boxNorm_param_eq_max
import Submission.Work.Smooth.BoxGeneric.LocalSurface.fderiv_pullback_faceLin_apply_vertexDir
import Submission.Work.Smooth.BoxGeneric.AeVertex

/-!
# The box-norm level set is locally Euclidean at a tangential vertex

This is the fourth and last local model of the box-norm level set, complementing
`isLocallyEuclideanAt_of_uniqueActiveFace`, `isLocallyEuclideanAt_of_corner` and
`isLocallyEuclideanAt_of_tangentialCorner`.

Let `y = boxVertex c σ ε s` be a vertex of the box (all three faces tight, sign pattern
`ε i = ±1`) lying on the surface `F = ψ(standard torus)`, and suppose that the vertex-ray direction
`vertexDir σ ε` — in which all three face functions increase at unit speed — is **tangent** to `F`
at `y`.  Then the three pulled-back signed faces, shifted to vanish at a parameter `p` over `y`,
have derivative `1` in the direction `r` with `fderiv (param ψ) p r = vertexDir σ ε`; by
`Work.Smooth.OneManifold.isLocallyArc_max_three` the zero set of their maximum is locally an arc,
and since near the vertex the box norm is that maximum
(`Work.Smooth.BoxGeneric.LocalSurface.boxNorm_param_eq_max`) the box-norm level set is described by
a plane model, which is transported to the surface by
`Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Filter

namespace Work.Smooth.OneManifold

noncomputable section

open scoped Topology

/-- **The box-norm level set is locally Euclidean at a tangential vertex.** -/
theorem isLocallyEuclideanAt_of_vertex_tangent {ψ : Submission.Diffeo} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {s : ℝ} {ε : Fin 3 → ℝ} (hs : 0 < s)
    (hε : ∀ i : Fin 3, ε i = 1 ∨ ε i = -1)
    (hy : Work.Smooth.BoxGeneric.boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier)
    (htan : ∃ p : ℝ × ℝ,
      Work.Smooth.Morse.param ψ p = Work.Smooth.BoxGeneric.boxVertex c σ ε s ∧
      ∃ r : ℝ × ℝ, fderiv ℝ (Work.Smooth.Morse.param ψ) p r =
        Work.Smooth.BoxGeneric.Vertex.vertexDir σ ε) :
    ∃ U : Set R3, Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) U ∧
      Work.Smooth.BoxGeneric.boxVertex c σ ε s ∈ U ∧
      IsLocallyEuclidean (U ∩ Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) := by
  classical
  obtain ⟨p, hp, r, hr⟩ := htan
  have hrne : r ≠ 0 := by
    intro h0
    have h1 : Work.Smooth.BoxGeneric.Vertex.vertexDir σ ε = 0 := by
      rw [← hr, h0, map_zero]
    have h2 : Work.Smooth.BoxGeneric.Vertex.vertexDir σ ε (σ 0) = 0 := by
      rw [h1]
      rfl
    rw [Work.Smooth.BoxGeneric.Vertex.vertexDir_apply] at h2
    simp only [Equiv.symm_apply_apply] at h2
    rcases hε 0 with h | h <;> rw [h] at h2 <;> nlinarith [Submission.boxSide_pos 0]
  -- the three pulled-back faces, shifted to vanish at `p`
  set F : Fin 3 → ℝ × ℝ → ℝ := fun i q =>
    Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i (ε i)) q - s with hFdef
  have hFcd : ∀ i : Fin 3, ContDiff ℝ 1 (F i) := fun i =>
    ((Work.Smooth.BoxGeneric.pullback_faceLin_contDiff ψ c σ i (ε i)).sub contDiff_const).of_le
      (by simp)
  have hFp : ∀ i : Fin 3, F i p = 0 := fun i => by
    show Work.Smooth.BoxGeneric.faceLin c σ i (ε i) (Work.Smooth.Morse.param ψ p) - s = 0
    rw [hp, (Work.Smooth.BoxGeneric.isActiveSignedFace_boxVertex (le_of_lt hs) hε i).1,
      sub_self]
  have hFd : ∀ i : Fin 3, fderiv ℝ (F i) p r = 1 := fun i => by
    have h := Work.Smooth.BoxGeneric.LocalSurface.fderiv_pullback_faceLin_apply_vertexDir
      (ψ := ψ) (c := c) (σ := σ) (ε := ε) (s := s) hp hr i (hε i)
    show fderiv ℝ (fun q => Work.Smooth.Morse.pullback ψ
      (Work.Smooth.BoxGeneric.faceLin c σ i (ε i)) q - s) p r = 1
    rw [fderiv_sub_const, h]
  -- the plane model
  obtain ⟨V, hVopen, hpV, hVloc⟩ :=
    isLocallyArc_max_three (hFcd 0) (hFcd 1) (hFcd 2) (hFp 0) (hFp 1) (hFp 2) hrne
      (by rw [hFd 0]; norm_num) (by rw [hFd 1]; norm_num) (by rw [hFd 2]; norm_num)
  -- near the vertex the box norm is the maximum of the three signed faces
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.mem_nhds_iff.mp
    (Work.Smooth.BoxGeneric.LocalSurface.boxNorm_param_eq_max
      (ψ := ψ) (c := c) (σ := σ) (ε := ε) (s := s) hs hε hp)
  -- a ball around `p`, inside `V`, inside the ball of validity of the box-norm identity
  obtain ⟨δ₂, hδ₂pos, hδ₂inj⟩ := Work.Smooth.Morse.Surface.param_local_injective ψ p
  obtain ⟨δ₃, hδ₃pos, hδ₃⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds hpV)
  set δ : ℝ := min (min δ₀ δ₂) δ₃ with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hδ₀pos hδ₂pos) hδ₃pos
  have hδ₀' : δ ≤ δ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₂' : δ ≤ δ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₃' : δ ≤ δ₃ := min_le_right _ _
  set B : Set (ℝ × ℝ) := Metric.ball p δ with hBdef
  set P : Set (ℝ × ℝ) := B ∩ {q : ℝ × ℝ | max (max (F 0 q) (F 1 q)) (F 2 q) = 0} with hPdef
  have hBopen : IsOpen B := by rw [hBdef]; exact Metric.isOpen_ball
  have hPB : P ⊆ B := by rw [hPdef]; exact inter_subset_left
  have hBV : B ⊆ V := by
    rintro q hq
    rw [hBdef] at hq
    exact hδ₃ (Metric.ball_subset_ball hδ₃' hq)
  have hloc : IsLocallyArcP P := by
    have h1 : Work.Smooth.SphereJordan.IsLocallyArc
        ↥((V ∩ {q : ℝ × ℝ | max (max (F 0 q) (F 1 q)) (F 2 q) = 0}) ∩ B) :=
      isLocallyArc_inter_of_isOpen hVloc hBopen
    refine isLocallyArc_of_eq ?_ h1
    ext q
    constructor
    · rintro ⟨⟨-, hq⟩, hqB⟩
      exact ⟨hqB, hq⟩
    · rintro ⟨hqB, hq⟩
      exact ⟨⟨hBV hqB, hq⟩, hqB⟩
  -- the key equivalence on the ball
  have hkey : ∀ q : ℝ × ℝ, q ∈ B →
      (Submission.boxNorm c σ (Work.Smooth.Morse.param ψ q) = s ↔
        max (max (F 0 q) (F 1 q)) (F 2 q) = 0) := by
    intro q hqB
    have hqδ : q ∈ Metric.ball p δ₀ := by
      rw [hBdef] at hqB
      exact Metric.ball_subset_ball hδ₀' hqB
    rw [hδ₀ hqδ]
    have e0 : Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 0 (ε 0)) q
        = F 0 q + s := by
      show Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 0 (ε 0)) q
        = Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 0 (ε 0)) q - s + s
      ring
    have e1 : Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 1 (ε 1)) q
        = F 1 q + s := by
      show Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 1 (ε 1)) q
        = Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 1 (ε 1)) q - s + s
      ring
    have e2 : Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 2 (ε 2)) q
        = F 2 q + s := by
      show Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 2 (ε 2)) q
        = Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 2 (ε 2)) q - s + s
      ring
    rw [e0, e1, e2, max_add_add_right, max_add_add_right]
    constructor <;> intro h <;> linarith
  -- the identification of the surface level set with the plane model
  have hident : ∀ B' : Set (ℝ × ℝ), IsOpen B' → B' ⊆ B →
      Work.Smooth.Morse.param ψ '' (B' ∩ P)
        = Work.Smooth.Morse.param ψ '' B' ∩
          Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s := by
    intro B' _ hB'sub
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨hqB', hqP⟩ := hq
      have hqB : q ∈ B := hB'sub hqB'
      refine ⟨⟨q, hqB', rfl⟩, ?_⟩
      rw [Work.Smooth.Morse.mem_levelSet]
      exact ⟨Work.Smooth.Morse.param_mem ψ q, (hkey q hqB).mpr hqP.2⟩
    · rintro ⟨⟨q, hqB', rfl⟩, hz⟩
      obtain ⟨-, hzbox⟩ := Work.Smooth.Morse.mem_levelSet.mp hz
      have hqB : q ∈ B := hB'sub hqB'
      refine ⟨q, ⟨hqB', ?_⟩, rfl⟩
      rw [hPdef]
      exact ⟨hqB, (hkey q hqB).mp hzbox⟩
  have hinj : Set.InjOn (Work.Smooth.Morse.param ψ) B := fun a ha b hb hab =>
    hδ₂inj (Metric.ball_subset_ball hδ₂' (by rwa [hBdef] at ha))
      (Metric.ball_subset_ball hδ₂' (by rwa [hBdef] at hb)) hab
  refine ⟨Work.Smooth.Morse.param ψ '' B,
    Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ hBopen,
    ⟨p, by rw [hBdef]; exact Metric.mem_ball_self hδpos, hp⟩, ?_⟩
  have hyl : Work.Smooth.BoxGeneric.boxVertex c σ ε s
      ∈ Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s := by
    rw [Work.Smooth.Morse.mem_levelSet]
    refine ⟨hy, ?_⟩
    have hpB : p ∈ B := by rw [hBdef]; exact Metric.mem_ball_self hδpos
    rw [← hp]
    exact (hkey p hpB).mpr (by
      rw [hFp 0, hFp 1, hFp 2]
      norm_num)
  exact isLocallyEuclidean_image_of_param
    (Work.Smooth.Morse.levelSet_subset_carrier ψ (Submission.boxNorm c σ) s)
    hBopen hPB hident hinj
    (isLocallyArc_of_eq (by
      ext q
      constructor
      · intro h
        exact ⟨hPB h, h⟩
      · rintro ⟨-, h⟩
        exact h) hloc)

end

end Work.Smooth.OneManifold
