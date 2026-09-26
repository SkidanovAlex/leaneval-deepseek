import Mathlib
import Submission.Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param
import Submission.Work.Smooth.OneManifold.Plane.Corner
import Submission.Work.Smooth.OneManifold.boxNorm_eq_max_of_corner

/-!
# The box-norm level set is locally Euclidean at a transverse corner

At a corner point `y` of the box sphere of level `s > 0` at which the two tight signed faces
`(i, ε)`, `(j, ε')` are *transverse* — the pair of derivatives of their pull-backs, read in the
parameter plane, is invertible (`Work.Smooth.BoxGeneric.CornerTransverseAt`) — the box norm agrees
near `y` with `max (faceLin c σ i ε) (faceLin c σ j ε')`
(`Work.Smooth.OneManifold.eventually_boxNorm_eq_max_of_corner`), and the plane model
`{q | max (f q) (g q) = 0}` of the two shifted pull-backs is locally an arc
(`Work.Smooth.OneManifold.isLocallyArc_max_of_isInvertible`).  Transporting the plane model to the
surface along the parametrisation (`Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param`)
gives the local `1`-manifold structure of the box-norm level set at `y`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Filter

namespace Work.Smooth.OneManifold

noncomputable section

open scoped Topology

/-- **The box-norm level set is locally Euclidean at a transverse corner.** -/
theorem isLocallyEuclideanAt_of_corner {ψ : Submission.Diffeo} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {s : ℝ} {y : R3} {i j : Fin 3} {ε ε' : ℝ} (hs : 0 < s)
    (hij : i ≠ j) (hε : ε = 1 ∨ ε = -1) (hε' : ε' = 1 ∨ ε' = -1)
    (hy : y ∈ (Work.Smooth.Morse.torus ψ).carrier)
    (hacti : Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε y)
    (hactj : Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s j ε' y)
    (huniq : ∀ k : Fin 3, k ≠ i → k ≠ j → Work.Smooth.BoxGeneric.faceNorm c σ k y < s)
    (htrans : Work.Smooth.BoxGeneric.CornerTransverseAt ψ c σ i j ε ε' y) :
    ∃ U : Set R3, Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) U ∧ y ∈ U ∧
      IsLocallyEuclidean (U ∩ Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) := by
  obtain ⟨p, hp, hinv⟩ := htrans
  set f : ℝ × ℝ → ℝ := fun q => Work.Smooth.Morse.pullback ψ
    (Work.Smooth.BoxGeneric.faceLin c σ i ε) q - s with hfdef
  set g : ℝ × ℝ → ℝ := fun q => Work.Smooth.Morse.pullback ψ
    (Work.Smooth.BoxGeneric.faceLin c σ j ε') q - s with hgdef
  have hfcd : ContDiffAt ℝ 1 f p :=
    (((Work.Smooth.BoxGeneric.pullback_faceLin_contDiff ψ c σ i ε).sub
      contDiff_const).of_le (by simp)).contDiffAt
  have hgcd : ContDiffAt ℝ 1 g p :=
    (((Work.Smooth.BoxGeneric.pullback_faceLin_contDiff ψ c σ j ε').sub
      contDiff_const).of_le (by simp)).contDiffAt
  have hfp : f p = 0 := by
    have h1 : Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) p = s := by
      show Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ p) = s
      rw [hp]
      exact hacti.1
    rw [hfdef]
    change Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) p - s = 0
    rw [h1, sub_self]
  have hgp : g p = 0 := by
    have h1 : Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε') p = s := by
      show Work.Smooth.BoxGeneric.faceLin c σ j ε' (Work.Smooth.Morse.param ψ p) = s
      rw [hp]
      exact hactj.1
    rw [hgdef]
    change Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε') p - s = 0
    rw [h1, sub_self]
  have hinv' : ((fderiv ℝ f p).prod (fderiv ℝ g p)).IsInvertible := by
    have hf' : fderiv ℝ f p = fderiv ℝ (Work.Smooth.Morse.pullback ψ
        (Work.Smooth.BoxGeneric.faceLin c σ i ε)) p := by
      rw [hfdef]
      exact fderiv_sub_const s
    have hg' : fderiv ℝ g p = fderiv ℝ (Work.Smooth.Morse.pullback ψ
        (Work.Smooth.BoxGeneric.faceLin c σ j ε')) p := by
      rw [hgdef]
      exact fderiv_sub_const s
    rw [hf', hg']
    exact hinv
  -- the plane model
  obtain ⟨V, hVopen, hpV, hVloc⟩ := isLocallyArc_max_of_isInvertible hfcd hgcd hfp hgp hinv'
  -- the box norm is the maximum of the two tight faces near `y`
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.mem_nhds_iff.mp
    (eventually_boxNorm_eq_max_of_corner hs hij hε hε' hacti hactj huniq)
  -- a ball around `p`: inside `V`, inside the preimage of the ball around `y`, injective
  have hnhds : {q : ℝ × ℝ | Work.Smooth.Morse.param ψ q ∈ Metric.ball y δ₀} ∈ nhds p := by
    have hmem : Metric.ball y δ₀ ∈ nhds (Work.Smooth.Morse.param ψ p) := by
      rw [hp]
      exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ₀pos)
    exact (Work.Smooth.Morse.param_continuous ψ).continuousAt hmem
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhds_iff.mp hnhds
  obtain ⟨δ₂, hδ₂pos, hδ₂inj⟩ := Work.Smooth.Morse.Surface.param_local_injective ψ p
  obtain ⟨δ₃, hδ₃pos, hδ₃⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds hpV)
  set δ : ℝ := min (min δ₁ δ₂) δ₃ with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hδ₁pos hδ₂pos) hδ₃pos
  have hδ₁' : δ ≤ δ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₂' : δ ≤ δ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₃' : δ ≤ δ₃ := min_le_right _ _
  set B : Set (ℝ × ℝ) := Metric.ball p δ with hBdef
  set P : Set (ℝ × ℝ) := B ∩ {q : ℝ × ℝ | max (f q) (g q) = 0} with hPdef
  have hBopen : IsOpen B := by rw [hBdef]; exact Metric.isOpen_ball
  have hBV : B ⊆ V := by
    rintro q hq
    rw [hBdef] at hq
    exact hδ₃ (Metric.ball_subset_ball hδ₃' hq)
  have hPB : P ⊆ B := by rw [hPdef]; exact inter_subset_left
  -- the plane model is locally an arc
  have hloc : IsLocallyArcP P := by
    have h1 : Work.Smooth.SphereJordan.IsLocallyArc
        ↥((V ∩ {q : ℝ × ℝ | max (f q) (g q) = 0}) ∩ B) :=
      isLocallyArc_inter_of_isOpen hVloc hBopen
    refine isLocallyArc_of_eq ?_ h1
    ext q
    constructor
    · rintro ⟨⟨-, hq⟩, hqB⟩
      exact ⟨hqB, hq⟩
    · rintro ⟨hqB, hq⟩
      exact ⟨⟨hBV hqB, hq⟩, hqB⟩
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
      have hqball : q ∈ Metric.ball p δ := by rwa [hBdef] at hqB
      have hqy : Work.Smooth.Morse.param ψ q ∈ Metric.ball y δ₀ :=
        hδ₁ (Metric.ball_subset_ball hδ₁' hqball)
      refine ⟨⟨q, hqB', rfl⟩, ?_⟩
      rw [Work.Smooth.Morse.mem_levelSet]
      refine ⟨Work.Smooth.Morse.param_mem ψ q, ?_⟩
      rw [hδ₀ hqy]
      have hmax : max (f q) (g q) = 0 := hqP.2
      rw [hfdef, hgdef] at hmax
      have hmax' : max (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) q)
          (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε') q) - s = 0 := by
        rw [← max_sub_sub_right]
        exact hmax
      rw [sub_eq_zero] at hmax'
      exact hmax'
    · rintro ⟨⟨q, hqB', rfl⟩, hz⟩
      obtain ⟨-, hzbox⟩ := Work.Smooth.Morse.mem_levelSet.mp hz
      have hqB : q ∈ B := hB'sub hqB'
      have hqball : q ∈ Metric.ball p δ := by rwa [hBdef] at hqB
      have hqy : Work.Smooth.Morse.param ψ q ∈ Metric.ball y δ₀ :=
        hδ₁ (Metric.ball_subset_ball hδ₁' hqball)
      refine ⟨q, ⟨hqB', ?_⟩, rfl⟩
      have hmax : max (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) q)
          (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε') q) = s := by
        have h1 : Submission.boxNorm c σ (Work.Smooth.Morse.param ψ q) =
            max (Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ q))
              (Work.Smooth.BoxGeneric.faceLin c σ j ε' (Work.Smooth.Morse.param ψ q)) :=
          hδ₀ hqy
        rw [show max (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) q)
              (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε') q)
            = max (Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ q))
              (Work.Smooth.BoxGeneric.faceLin c σ j ε' (Work.Smooth.Morse.param ψ q)) from rfl,
          ← h1, hzbox]
      rw [hPdef]
      refine ⟨hqB, ?_⟩
      change max (f q) (g q) = 0
      rw [hfdef, hgdef]
      change max (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) q - s)
        (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ j ε') q - s) = 0
      rw [max_sub_sub_right, hmax, sub_self]
  have hinj : Set.InjOn (Work.Smooth.Morse.param ψ) B := fun a ha b hb hab =>
    hδ₂inj (Metric.ball_subset_ball hδ₂' (by rwa [hBdef] at ha))
      (Metric.ball_subset_ball hδ₂' (by rwa [hBdef] at hb)) hab
  refine ⟨Work.Smooth.Morse.param ψ '' B,
    Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ hBopen,
    ⟨p, by rw [hBdef]; exact Metric.mem_ball_self hδpos, hp⟩, ?_⟩
  have hyl : y ∈ Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s := by
    rw [Work.Smooth.Morse.mem_levelSet]
    refine ⟨hy, le_antisymm ((Work.Smooth.BoxGeneric.boxNorm_le_iff c σ s y).mpr hacti.2) ?_⟩
    calc s = Work.Smooth.BoxGeneric.faceLin c σ i ε y := hacti.1.symm
      _ = Work.Smooth.BoxGeneric.faceNorm c σ i y :=
          (faceNorm_eq_faceLin_of_nonneg hε (by rw [hacti.1]; exact le_of_lt hs)).symm
      _ ≤ Submission.boxNorm c σ y := Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ i y
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
