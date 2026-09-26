import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs

/-!
# The box-norm level set is locally an arc at a point with a unique active face

`Submission.boxNorm c σ` is the gauge of Pardon's box `Submission.PBox s c σ`; it is only
piecewise smooth, being the maximum of the three face norms `faceNorm c σ i = |signedFace c σ i|`.
At a point `y` of the surface `F = ψ(standard torus)` at which a *single* face is tight — that is,
`faceLin c σ i ε y = s` for the level `s` while `faceNorm c σ j y < s` for the two other faces — the
box norm agrees with the smooth function `faceLin c σ i ε` on a whole neighbourhood of `y` in `ℝ³`
(no other face can overtake the active one there; `eventually_boxNorm_eq_faceLin` below).

Consequently the level set `F ∩ {boxNorm c σ = s}` is, near such a `y`, the level set of the smooth
function `faceLin c σ i ε` restricted to `F`.  If moreover the derivative of that restriction is
nonzero at some parameter `p` over `y`, the implicit function theorem
(`Work.Smooth.Morse.Regular.pullback_local_arc`) exhibits the level set of the pull-back as a local
arc in the parameter plane, and pushing it forward along the locally injective parametrisation
`param ψ` gives the local arc of the surface level set: this is the statement proved here,
`isLocalArcAt_of_uniqueActiveFace`.

This is the face-interior half of the local model of a good box level (the corner half is governed
by the transversality input `Work.Smooth.BoxGeneric.CornerTransverseAt`), and it feeds the
`Work.Smooth.Morse.CompactOneManifoldInput` step producing
`Work.Smooth.BoxGeneric.AeTransverseBox`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped Topology

namespace Work.Smooth.BoxGeneric.LocalSurface

noncomputable section

/-- **Near a point at which a single signed face is tight, the box norm is that face function.**

If `faceLin c σ i ε y = s`, all face norms are `≤ s` at `y`, the two other face norms are
*strictly* less than `s` at `y`, and `ε = ±1`, then for every `x` close enough to `y` the box norm
`Submission.boxNorm c σ x` equals the (smooth) function `faceLin c σ i ε x`.

Indeed, on a neighbourhood of `y` the active signed face is positive,
`0 < faceLin c σ i ε`, hence equal to the absolute value `faceNorm c σ i`, and it dominates the two
other face norms, so it is their maximum. -/
lemma eventually_boxNorm_eq_faceLin {c : R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ}
    {i : Fin 3} {ε : ℝ} {y : R3} (hs : 0 < s) (hε : ε = 1 ∨ ε = -1)
    (hact : IsActiveSignedFace c σ s i ε y)
    (huniq : ∀ j : Fin 3, j ≠ i → faceNorm c σ j y < s) :
    ∀ᶠ x in 𝓝 y, Submission.boxNorm c σ x = faceLin c σ i ε x := by
  have hface : faceLin c σ i ε y = s := hact.1
  -- the active signed face stays positive
  have hpos : ∀ᶠ x in 𝓝 y, (0 : ℝ) < faceLin c σ i ε x :=
    (isOpen_lt continuous_const (contDiff_faceLin c σ i ε).continuous).mem_nhds
      (by show (0 : ℝ) < faceLin c σ i ε y; rw [hface]; exact hs)
  -- it also stays bigger than the two other face norms
  have hlt : ∀ᶠ x in 𝓝 y, ∀ j : Fin 3, j ≠ i → faceNorm c σ j x < faceLin c σ i ε x := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = i
    · subst hj
      exact Filter.Eventually.of_forall fun x h => absurd rfl h
    · filter_upwards [show {b : R3 | faceNorm c σ j b < faceLin c σ i ε b} ∈ 𝓝 y from
        (isOpen_lt (continuous_faceNorm c σ j) (contDiff_faceLin c σ i ε).continuous).mem_nhds
          (by show faceNorm c σ j y < faceLin c σ i ε y; rw [hface]; exact huniq j hj)] with x hx
      intro _
      exact hx
  filter_upwards [hpos, hlt] with x hxpos hxlt
  -- on the positive part of a signed face, that signed face *is* the face norm
  have hnorm : faceNorm c σ i x = faceLin c σ i ε x := by
    have hsgn : signedFace c σ i x = ε * faceLin c σ i ε x := by
      rcases hε with h | h
      · rw [h, faceLin_one]; ring
      · rw [h, faceLin_neg_one]; ring
    rw [faceNorm_eq_abs_signedFace, hsgn, abs_mul]
    have habs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
    rw [habs, one_mul, abs_of_pos hxpos]
  refine le_antisymm ?_ ?_
  · exact (boxNorm_le_iff c σ (faceLin c σ i ε x) x).mpr fun j => by
      by_cases hj : j = i
      · rw [hj, hnorm]
      · exact le_of_lt (hxlt j hj)
  · rw [← hnorm]
    exact faceNorm_le_boxNorm c σ i x

/-- **The box-norm level set is locally an arc at a point with a unique active face.**

Let `y` be a point of the surface `F = ψ(standard torus)` lying on the box sphere of level `s > 0`,
at which the single signed face `(i, ε)` (`ε = ±1`) is tight — `faceLin c σ i ε y = s` and all face
norms `≤ s` — while the two other face norms are *strictly* below `s`.  If the signed face function
restricted to the surface has a nonvanishing derivative at some parameter `p` over `y`, then the
level set `F ∩ {boxNorm c σ = s}` is, in a neighbourhood of `y` which is open in the surface,
exactly the image of an injective continuous arc through `y`; in other words, it is locally an arc
at `y` in the sense of the local model `Work.Smooth.Morse.IsLocalArc`.

The neighbourhood is the image under `param ψ` of a sufficiently small ball of parameters around
`p`, small enough that (a) `param ψ` is injective on it, (b) on its image the box norm agrees with
`faceLin c σ i ε`, and (c) the arc of the level set of the pull-back
(`Work.Smooth.Morse.Regular.pullback_local_arc`) exhausts all level points in it. -/
theorem isLocalArcAt_of_uniqueActiveFace {ψ : Submission.Diffeo} {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ} {y : LeanEval.KnotTheory.PardonDistortion.R3} {i : Fin 3} {ε : ℝ} (hs : 0 < s) (hε : ε = 1 ∨ ε = -1) (hy : y ∈ (Work.Smooth.Morse.torus ψ).carrier) (hact : Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε y) (huniq : ∀ j : Fin 3, j ≠ i → Work.Smooth.BoxGeneric.faceNorm c σ j y < s) (hreg : ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = y ∧ fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε)) p ≠ 0) : ∃ U : Set LeanEval.KnotTheory.PardonDistortion.R3, Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) U ∧ y ∈ U ∧ ∃ (I : Set ℝ) (s₀ : ℝ) (ρ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3), IsOpen I ∧ s₀ ∈ I ∧ ContinuousOn ρ I ∧ ρ s₀ = y ∧ Set.InjOn ρ I ∧ (∀ t ∈ I, ρ t ∈ Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) ∧ (∀ z, z ∈ Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s → z ∈ U → ∃ t ∈ I, ρ t = z) := by
  classical
  -- a parameter over `y` at which the active face restricted to the surface is regular
  obtain ⟨p, hp, hd⟩ := hreg
  -- a ball on which the box norm is the active face function
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.mem_nhds_iff.mp
    (eventually_boxNorm_eq_faceLin hs hε hact huniq)
  -- the level of the active face function, in the parameter plane
  have hgp : Work.Smooth.Morse.pullback ψ (faceLin c σ i ε) p = s := by
    show faceLin c σ i ε (Work.Smooth.Morse.param ψ p) = s
    rw [hp]
    exact hact.1
  -- the arc of the level set of the pull-back through `p`
  obtain ⟨εa, hεapos, σa, hσa0, hσacont, hσainj, hσalev, hσacov⟩ :=
    Work.Smooth.Morse.Regular.pullback_local_arc ψ
      ((contDiff_faceLin c σ i ε).of_le (by simp)) s p hgp hd
  -- a ball on which the parametrisation of the surface is injective
  obtain ⟨εp, hεppos, hεpinj⟩ := Work.Smooth.Morse.Surface.param_local_injective ψ p
  -- a ball whose image under `param ψ` stays inside the region of agreement
  have hnhds : {q : ℝ × ℝ | Work.Smooth.Morse.param ψ q ∈ Metric.ball y δ₀} ∈ 𝓝 p := by
    have hmem : Metric.ball y δ₀ ∈ 𝓝 (Work.Smooth.Morse.param ψ p) := by
      rw [hp]
      exact (Metric.isOpen_ball).mem_nhds (Metric.mem_ball_self hδ₀pos)
    exact (Work.Smooth.Morse.param_continuous ψ).continuousAt (x := p) hmem
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhds_iff.mp hnhds
  set δ : ℝ := min (min εa εp) δ₁ with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hεapos hεppos) hδ₁pos
  have hδεa : δ ≤ εa := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδεp : δ ≤ εp := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδδ₁ : δ ≤ δ₁ := min_le_right _ _
  -- the interval of arc parameters whose image lies in the small ball
  set I : Set ℝ := Set.Ioo (-1 : ℝ) 1 ∩ σa ⁻¹' Metric.ball p δ with hIdef
  have hIopen : IsOpen I := hσacont.isOpen_inter_preimage isOpen_Ioo Metric.isOpen_ball
  have h0I : (0 : ℝ) ∈ I := by
    rw [hIdef]
    refine ⟨by norm_num, ?_⟩
    show σa 0 ∈ Metric.ball p δ
    rw [hσa0]
    exact Metric.mem_ball_self hδpos
  refine ⟨Work.Smooth.Morse.param ψ '' Metric.ball p δ,
    Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ Metric.isOpen_ball,
    ⟨p, Metric.mem_ball_self hδpos, hp⟩, I, 0, fun t => Work.Smooth.Morse.param ψ (σa t),
    hIopen, h0I, ?_, ?_, ?_, ?_, ?_⟩
  · -- the arc of the surface is continuous
    refine (Work.Smooth.Morse.param_continuous ψ).continuousOn.comp ?_ (Set.mapsTo_univ _ _)
    exact hσacont.mono (by rw [hIdef]; exact inter_subset_left)
  · -- it passes through `y`
    show Work.Smooth.Morse.param ψ (σa 0) = y
    rw [hσa0, hp]
  · -- and it is injective, because both `σa` and `param ψ` are injective there
    intro t ht t' ht' heq
    rw [hIdef] at ht ht'
    have htB : σa t ∈ Metric.ball p εp := Metric.ball_subset_ball hδεp ht.2
    have htB' : σa t' ∈ Metric.ball p εp := Metric.ball_subset_ball hδεp ht'.2
    exact hσainj ht.1 ht'.1 (hεpinj htB htB' heq)
  · -- the arc lies in the box-norm level set, where the box norm is the active face
    intro t ht
    rw [Work.Smooth.Morse.mem_levelSet]
    rw [hIdef] at ht
    refine ⟨Work.Smooth.Morse.param_mem ψ (σa t), ?_⟩
    have hmem : Work.Smooth.Morse.param ψ (σa t) ∈ Metric.ball y δ₀ :=
      hδ₁ (Metric.ball_subset_ball hδδ₁ ht.2)
    rw [hδ₀ hmem]
    show faceLin c σ i ε (Work.Smooth.Morse.param ψ (σa t)) = s
    exact hσalev t ht.1
  · -- and it exhausts the level set in the neighbourhood
    intro z hz hzU
    rw [Work.Smooth.Morse.mem_levelSet] at hz
    obtain ⟨hzcar, hzbox⟩ := hz
    obtain ⟨q, hqB, hqq⟩ := hzU
    have hqδa : ‖q - p‖ < εa := by
      rw [Metric.mem_ball, dist_eq_norm] at hqB
      exact lt_of_lt_of_le hqB hδεa
    have hzg : faceLin c σ i ε z = s := by
      have hmem : z ∈ Metric.ball y δ₀ := by
        rw [← hqq]
        exact hδ₁ (Metric.ball_subset_ball hδδ₁ hqB)
      exact (hδ₀ hmem).symm.trans hzbox
    have hpq : Work.Smooth.Morse.pullback ψ (faceLin c σ i ε) q = s := by
      show faceLin c σ i ε (Work.Smooth.Morse.param ψ q) = s
      rw [hqq]
      exact hzg
    obtain ⟨t, ht, hta⟩ := hσacov q hpq hqδa
    refine ⟨t, ?_, ?_⟩
    · rw [hIdef]
      refine ⟨ht, ?_⟩
      show σa t ∈ Metric.ball p δ
      rw [hta]
      exact hqB
    · show Work.Smooth.Morse.param ψ (σa t) = z
      rw [hta, hqq]

end

end Work.Smooth.BoxGeneric.LocalSurface
