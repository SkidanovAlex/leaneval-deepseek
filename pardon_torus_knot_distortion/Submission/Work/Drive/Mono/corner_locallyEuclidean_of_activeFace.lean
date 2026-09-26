import Mathlib
import Submission.Work.Drive.Mono.Residual
import Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_uniqueActiveFace
import Submission.Work.Smooth.OneManifold.Basic
import Submission.Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param
import Submission.Work.Smooth.OneManifold.Plane.Corner
import Submission.Work.Drive.Mono.SphereFaceDefs
import Submission.Work.SliceArcs.Components
import Submission.Work.Smooth.Morse.Surface.param_local_injective
import Submission.Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen

/-!
# The box-sphere/tilted-plane corner: the local `1`-manifold structure

Let `F = torus ψ` be the embedded torus of the challenge, `z ∈ F` a point at which a *single*
signed face `(i, ε)` of Pardon's box of level `s > 0` is tight (`faceLin c σ i ε z = s`, all face
norms `≤ s` at `z`) and the two other face norms are strictly below `s`, and let `φ` be a linear
functional with `φ z = k`.  The *corner set*

`Z = F ∩ {y | max (boxNorm c σ y - s) (k - φ y) = 0}`

is the part of the box sphere `{boxNorm = s}` on which `φ ≥ k`, together with the part of the
plane `{φ = k}` inside the box.  This file proves that on a small neighbourhood `O` of `z` the set
`O ∩ Z` is locally Euclidean of dimension one (`Work.Smooth.OneManifold.IsLocallyEuclidean`), i.e.
a topological `1`-manifold, provided the two cutting functions are *transverse on the surface* at
some parameter `p` over `z`: both derivatives of `φ ∘ par` and of `boxNorm c σ ∘ par` at `p` are
nonzero and are not proportional (`hreg`).

## The argument

On a ball around `z` the box norm agrees with the active face `faceLin c σ i ε`
(`Work.Smooth.BoxGeneric.LocalSurface.eventually_boxNorm_eq_faceLin`), so it suffices to treat the
corner in the parameter plane: with

`F q = faceLin c σ i ε (param ψ q) - s`, `G q = k - φ (param ψ q)`

the plane model is `{q | max (F q) (G q) = 0}`.  The transversality hypothesis identifies
`fderiv F p` with the derivative of `boxNorm c σ ∘ par` at `p` (the two functions agree near `p`)
and `fderiv G p` with `- fderiv (φ ∘ par) p`, so the pair `(fderiv F p).prod (fderiv G p)` is
invertible (`Work.Drive.Mono.isInvertible_prod_of_forall_ne_smul`); then
`isLocallyArc_max_of_isInvertible` (the plane model of a transverse corner: the pair `(F, G)` is a
local homeomorphism at `p`, so the corner is the homeomorphic image of the standard corner
`{max a b = 0}`, itself an arc) gives an open `V ∋ p` with `V ∩ {max F G = 0}` locally an arc.
Cutting by a small ball `B ∋ p` on which `param ψ` is injective and maps into the ball around `z`
gives the plane model `P = B ∩ {max F G = 0}`, and the identification
`param ψ '' (B' ∩ P) = param ψ '' B' ∩ Z` for every open `B' ⊆ B`; transporting along the
parametrisation (`Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param`) yields the
`1`-manifold structure of `param ψ '' B ∩ Z`, which is a trace on the surface of the required
ambient open set (`Work.SliceArcs.exists_isOpen_inter_carrier`).
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped _root_.Topology

theorem corner_locallyEuclidean_of_activeFace {ψ : Submission.Diffeo} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {s : ℝ} {φ : R3 →L[ℝ] ℝ} {k : ℝ} {z : R3} {i : Fin 3} {ε : ℝ}
    (hs : 0 < s) (hε : ε = 1 ∨ ε = -1)
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hact : Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε z)
    (huniq : ∀ j : Fin 3, j ≠ i → Work.Smooth.BoxGeneric.faceNorm c σ j z < s)
    (hk : φ z = k)
    (hreg : ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
      fderiv ℝ (fun q : ℝ × ℝ => φ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (fun q : ℝ × ℝ => φ (Work.BoxShrink.Pinch.par ψ q)) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) :
    ∃ O : Set R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          {y : R3 | max (Submission.boxNorm c σ y - s) (k - φ y) = 0})) := by
  classical
  obtain ⟨p, hp, hdφ, hdbox, hprop⟩ := hreg
  rw [Work.BoxShrink.Pinch.par_def] at hp hdφ hdbox hprop
  -- the two functions whose maximum cuts the corner, read in the parameter plane
  set F : ℝ × ℝ → ℝ := Work.Drive.Mono.faceW ψ s c σ i ε with hFdef
  set G : ℝ × ℝ → ℝ := fun q => k - φ (Work.Smooth.Morse.param ψ q) with hGdef
  -- smoothness and values at `p`
  have hFcd : ContDiff ℝ 1 F := by
    rw [hFdef]
    exact (Work.Drive.Mono.contDiff_faceW ψ s c σ i ε).of_le (by norm_num)
  have hGcd : ContDiff ℝ 1 G := by
    rw [hGdef]
    exact contDiff_const.sub (φ.contDiff.comp ((Work.Smooth.Morse.param_contDiff ψ).of_le (by simp)))
  have hFp : F p = 0 := by
    rw [hFdef]
    show Work.Smooth.BoxGeneric.faceLin c σ i ε (Work.Smooth.Morse.param ψ p) - s = 0
    rw [hp, hact.1, sub_self]
  have hGp : G p = 0 := by
    rw [hGdef]
    show k - φ (Work.Smooth.Morse.param ψ p) = 0
    rw [hp, hk, sub_self]
  -- the ball around `z` on which the box norm is the active face
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.mem_nhds_iff.mp
    (Work.Smooth.BoxGeneric.LocalSurface.eventually_boxNorm_eq_faceLin hs hε hact huniq)
  -- the derivative of `F` is that of `boxNorm c σ ∘ param ψ` (the two agree near `p`)
  have hev : F =ᶠ[𝓝 p]
      (fun q => Submission.boxNorm c σ (Work.Smooth.Morse.param ψ q) - s) := by
    have hmem : Metric.ball z δ₀ ∈ 𝓝 (Work.Smooth.Morse.param ψ p) := by
      rw [hp]
      exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ₀pos)
    filter_upwards [((Work.Smooth.Morse.param_continuous ψ).continuousAt).preimage_mem_nhds hmem]
      with q hq
    rw [hFdef, Work.Drive.Mono.faceW_apply]
    rw [hδ₀ hq]
    simp only [Work.BoxShrink.Pinch.par_def]
  have hdF : fderiv ℝ F p
      = fderiv ℝ (fun q => Submission.boxNorm c σ (Work.Smooth.Morse.param ψ q)) p := by
    rw [hev.fderiv_eq, fderiv_sub_const]
  have hdG : fderiv ℝ G p
      = - fderiv ℝ (fun q => φ (Work.Smooth.Morse.param ψ q)) p := by
    rw [hGdef, fderiv_const_sub]
  have hdGne : fderiv ℝ G p ≠ 0 := by
    rw [hdG]
    exact neg_ne_zero.mpr hdφ
  -- the two derivatives are not proportional: otherwise the pair `(d phi, d boxNorm)` would not
  -- be surjective, contradicting Cramer's rule for the non-proportional pair
  have hprop' : ∀ t : ℝ, fderiv ℝ F p ≠ t • fderiv ℝ G p := by
    intro t ht
    rw [hdF, hdG] at ht
    have hpoint : ∀ v : ℝ × ℝ,
        fderiv ℝ (fun q => Submission.boxNorm c σ (Work.Smooth.Morse.param ψ q)) p v
          = -(t * (fderiv ℝ (fun q => φ (Work.Smooth.Morse.param ψ q)) p v)) := by
      intro v
      have h1 := congrArg (fun f : (ℝ × ℝ) →L[ℝ] ℝ => f v) ht
      simpa using h1
    obtain ⟨r, hr1, hr2⟩ :=
      Work.Drive.Mono.exists_apply_eq_pair_of_forall_ne_smul hdbox hprop 0 1
    rw [hpoint r, hr1] at hr2
    norm_num at hr2
  have hinv : ((fderiv ℝ F p).prod (fderiv ℝ G p)).IsInvertible :=
    Work.Drive.Mono.isInvertible_prod_of_forall_ne_smul hdGne hprop'
  -- the plane model of the corner is locally an arc
  obtain ⟨V, hVopen, hpV, hVloc⟩ :=
    Work.Smooth.OneManifold.isLocallyArc_max_of_isInvertible
      (f := F) (g := G) (p := p) hFcd.contDiffAt hGcd.contDiffAt hFp hGp hinv
  -- the neighbourhood data around `p` and around `z`
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhds_iff.mp (by
    have hmem : Metric.ball z δ₀ ∈ 𝓝 (Work.Smooth.Morse.param ψ p) := by
      rw [hp]
      exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ₀pos)
    exact ((Work.Smooth.Morse.param_continuous ψ).continuousAt).preimage_mem_nhds hmem)
  obtain ⟨δ₂, hδ₂pos, hδ₂inj⟩ := Work.Smooth.Morse.Surface.param_local_injective ψ p
  obtain ⟨δ₃, hδ₃pos, hδ₃⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds hpV)
  set δ : ℝ := min (min δ₁ δ₂) δ₃ with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min (lt_min hδ₁pos hδ₂pos) hδ₃pos
  have hδ₁' : δ ≤ δ₁ := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₂' : δ ≤ δ₂ := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₃' : δ ≤ δ₃ := by rw [hδdef]; exact min_le_right _ _
  set B : Set (ℝ × ℝ) := Metric.ball p δ with hBdef
  have hBopen : IsOpen B := by rw [hBdef]; exact Metric.isOpen_ball
  have hpB : p ∈ B := by rw [hBdef]; exact Metric.mem_ball_self hδpos
  have hBV : B ⊆ V := by
    rintro q hq
    rw [hBdef] at hq
    exact hδ₃ (Metric.ball_subset_ball hδ₃' hq)
  set P : Set (ℝ × ℝ) := B ∩ {q : ℝ × ℝ | max (F q) (G q) = 0} with hPdef
  have hPB : P ⊆ B := by rw [hPdef]; exact inter_subset_left
  have hinj : Set.InjOn (Work.Smooth.Morse.param ψ) B := by
    intro a ha b hb hab
    rw [hBdef] at ha hb
    exact hδ₂inj (Metric.ball_subset_ball hδ₂' ha) (Metric.ball_subset_ball hδ₂' hb) hab
  -- the plane model inside the ball is locally an arc
  have hloc : Work.Smooth.OneManifold.IsLocallyArcP (B ∩ P) := by
    have h1 : Work.Smooth.SphereJordan.IsLocallyArc
        ↥((V ∩ {q : ℝ × ℝ | max (F q) (G q) = 0}) ∩ B) :=
      Work.Smooth.OneManifold.isLocallyArc_inter_of_isOpen hVloc hBopen
    refine Work.Smooth.OneManifold.isLocallyArc_of_eq ?_ h1
    ext q
    constructor
    · rintro ⟨⟨-, hq⟩, hqB⟩
      exact ⟨hqB, ⟨hqB, hq⟩⟩
    · rintro ⟨hqB, -, hq⟩
      exact ⟨⟨hBV hqB, hq⟩, hqB⟩
  -- on the ball, the box norm is the active face
  have hkey : ∀ q : ℝ × ℝ, q ∈ B →
      max (F q) (G q) = max (Submission.boxNorm c σ (Work.Smooth.Morse.param ψ q) - s)
        (k - φ (Work.Smooth.Morse.param ψ q)) := by
    intro q hq
    have hqball : q ∈ Metric.ball p δ := by rw [hBdef] at hq; exact hq
    have hqy : Work.Smooth.Morse.param ψ q ∈ Metric.ball z δ₀ :=
      hδ₁ (Metric.ball_subset_ball hδ₁' hqball)
    rw [hδ₀ hqy]
    simp only [hFdef, hGdef, Work.Drive.Mono.faceW_apply, Work.BoxShrink.Pinch.par_def]
  -- the target set of the statement
  set Z : Set R3 := (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
    {y : R3 | max (Submission.boxNorm c σ y - s) (k - φ y) = 0} with hZdef
  -- the plane model represents the target set
  have hident : ∀ B' : Set (ℝ × ℝ), IsOpen B' → B' ⊆ B →
      Work.Smooth.Morse.param ψ '' (B' ∩ P) = Work.Smooth.Morse.param ψ '' B' ∩ Z := by
    intro B' _ hB'sub
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨hqB', hqP⟩ := hq
      have hqB : q ∈ B := hB'sub hqB'
      have hmax : max (F q) (G q) = 0 := by
        have h := hqP
        rw [hPdef] at h
        exact h.2
      refine ⟨⟨q, hqB', rfl⟩, ?_⟩
      rw [hZdef]
      refine ⟨Work.Smooth.Morse.param_mem ψ q, ?_⟩
      show max (Submission.boxNorm c σ (Work.Smooth.Morse.param ψ q) - s)
        (k - φ (Work.Smooth.Morse.param ψ q)) = 0
      rw [← hkey q hqB]
      exact hmax
    · rintro ⟨⟨q, hqB', rfl⟩, hyZ⟩
      have hqB : q ∈ B := hB'sub hqB'
      refine ⟨q, ⟨hqB', ?_⟩, rfl⟩
      rw [hPdef]
      refine ⟨hqB, ?_⟩
      show max (F q) (G q) = 0
      rw [hkey q hqB]
      rw [hZdef] at hyZ
      exact hyZ.2
  have hlocZ : Work.Smooth.OneManifold.IsLocallyEuclidean
      (Work.Smooth.Morse.param ψ '' B ∩ Z) :=
    Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param
      (Z := Z) (B := B) (P := P) (hZc := inter_subset_left) hBopen hPB hident hinj hloc
  -- an ambient open set whose trace on the surface is the chart image
  have hVopenC : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
      (Work.Smooth.Morse.param ψ '' B) :=
    Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ hBopen
  obtain ⟨W, hWopen, hWeq⟩ :=
    Work.SliceArcs.exists_isOpen_inter_carrier (P := Work.Drive.EpsSphere.torusOf ψ) hVopenC
  refine ⟨W, hWopen, ?_, ?_⟩
  · -- `z ∈ W`
    have hzcar : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier := by
      rw [← hp]; exact Work.Smooth.Morse.param_mem ψ p
    have hzmem : z ∈ Work.Smooth.Morse.param ψ '' B
        ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier := ⟨⟨p, hpB, hp⟩, hz⟩
    rw [hWeq] at hzmem
    exact hzmem.1
  · -- the trace is locally Euclidean
    have hsub : Work.Smooth.Morse.param ψ '' B ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier := by
      rw [show (Work.Drive.EpsSphere.torusOf ψ).carrier
          = Set.range (Work.Smooth.Morse.param ψ) from Work.Smooth.Morse.torus_carrier ψ]
      exact Set.image_subset_range _ _
    have hWc : W ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier
        = Work.Smooth.Morse.param ψ '' B := by
      rw [← hWeq]
      exact Set.inter_eq_left.mpr hsub
    have hZc : Z ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier := fun y hy => hy.1
    have e1 : (W ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) ∩ Z = W ∩ Z := by
      rw [Set.inter_assoc, Set.inter_eq_right.mpr hZc]
    have e2 : (W ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) ∩ Z
        = Work.Smooth.Morse.param ψ '' B ∩ Z := by rw [hWc]
    refine Work.Smooth.OneManifold.isLocallyEuclidean_of_eq (Z' := W ∩ Z) ?_ hlocZ
    exact e2.symm.trans e1

end Work.Drive.Mono
