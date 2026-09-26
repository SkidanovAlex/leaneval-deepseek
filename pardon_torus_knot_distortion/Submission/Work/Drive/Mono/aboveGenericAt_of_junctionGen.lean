import Mathlib
import Submission.Work.Drive.Mono.JunctionGen
import Submission.Work.Drive.Mono.Residual
import Submission.Work.Drive.Mono.Split

/-!
# Clause 2 of the trace data from the interior genericity and the junction genericity

This module proves `Work.Drive.Mono.aboveGenericAt_of_junctionGen`: from the tilt data `TiltData`
(the four clauses of `Work.Drive.Final.TiltedGenericity`, the size and window conditions) and the
junction genericity `Work.Drive.Mono.JunctionGen` (the stratified general position of the sweep at
the points of the box sphere, the slab faces, the triple points and the box edges and corners), the
second clause of the trace data

  `Work.Drive.Mono.AboveGenericAt (torusOf ψ) s c σ u v h ℓ lam`

holds at every non-exceptional level `lam` of the window.

## The two regimes

Let `z` be a point of the surface in the closed box and the closed slab at the level `lam`.

* **`z` in the open box.**  Then `z` lies in the open box *and* in the closed slab, so clause (i) of
  `TiltedGenericity` gives `fderiv (sweepHeight ψ ℓ) p ≠ 0` at *every* lift `p` of `z`: the sweep
  height takes values strictly above `lam` arbitrarily close to `z`, and the points of the surface
  obtained are in the open box (a neighbourhood of `z` is, by openness of the box) and have
  `ℓ > lam`, hence lie in the region `openTiltedSweepRegion … lam` whatever their slab status.  So
  `z ∈ closure X`.

* **`z` on the box sphere** (`boxNorm c σ z = s`: this is exactly what `z ∈ closure (PBox)` together
  with `z ∉ PBox` means, since `PBox = {boxNorm < s}`).  Here clause (i) of `TiltedGenericity` is
  not available, and this is precisely the regime in which clause 2 is *false* for arbitrary data
  (`Work.Drive.Mono.NOTES_STATE.md` records three machine-checked refutations: a box-sphere local
  maximiser of `ℓ` at a non-exceptional level, a corner of the box at which the level function is
  not stationary along the faces, and a level that does not cut the box at all).  What rescues it is
  clause (a) of `JunctionGen`: the level curve of the sweep height crosses the box sphere
  *transversally* at `z`.  Concretely, at the lift `p` of `z` supplied by `JunctionGen` the two
  differentials

    `A = d(sweepHeight ψ ℓ)_p`,   `B = d(boxNorm c σ ∘ par ψ)_p`

  are both nonzero and not parallel, so the pair of functions
  `q ↦ (sweepHeight ψ ℓ q, boxNorm c σ (par ψ q))` has *surjective* differential at `p`; hence for
  every `ε > 0` there is `q` with `‖q - p‖ < ε`, `lam < sweepHeight ψ ℓ q` and
  `boxNorm c σ (par ψ q) < s`.  The image `par ψ q` is then a point of the surface in the open box
  at a level strictly above `lam`, i.e. a point of the region, arbitrarily close to `z` (by
  continuity of `par ψ`).  So `z ∈ closure X` in this regime as well.

## The analytic bricks

* `exists_pos_near_lt_of_pair`: a `C¹` function of one variable with positive derivative at `0` and
  another with negative derivative at `0` satisfy both one-sided inequalities at a *common* small
  positive parameter (the slopes converge to the derivative values, so each inequality holds
  eventually in `𝓝[≠] 0`, and one takes the intersection).
* `exists_near_lt_of_fderiv_indep`, `exists_near_gt_of_fderiv_ne_zero`: the two-variable forms,
  obtained by restricting to the line `t ↦ p + t • w` along a direction `w` in which the relevant
  differential is positive (`exists_dir_neg_of_indep`, `exists_dir_pos_of_ne_zero`).
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-! ## Directions of positive and of negative value for functionals on the plane -/

/-- **A nonzero functional on `ℝ × ℝ` has a vector on which it is positive.** -/
lemma exists_dir_pos_of_ne_zero {A : (ℝ × ℝ) →L[ℝ] ℝ} (hA : A ≠ 0) :
    ∃ w : ℝ × ℝ, 0 < A w := by
  by_contra h
  push_neg at h
  refine hA (ContinuousLinearMap.ext fun x => ?_)
  have h1 : A x ≤ 0 := h x
  have h2 : (0 : ℝ) ≤ A x := by
    have := h (-x)
    simpa using this
  simp only [ContinuousLinearMap.zero_apply]
  linarith

/-- **Two nonzero, non-parallel functionals on `ℝ × ℝ` have a direction on which the first is
positive and the second negative.**  If `u` is a vector with `A u ≠ 0` (scaled so that `A u = 1`)
and `z` is a vector of `ker A` on which `B` does not vanish — which exists precisely because `B` is
not a multiple of `A` — then `u + s • z` has `A`-value `1` for every `s` and `B`-value
`B u + s * B z`, which is made negative by the choice `s = -(B u + 1)/B z`. -/
lemma exists_dir_neg_of_indep {A B : (ℝ × ℝ) →L[ℝ] ℝ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hind : ∀ t : ℝ, A ≠ t • B) : ∃ w : ℝ × ℝ, 0 < A w ∧ B w < 0 := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ × ℝ, A u ≠ 0 := by
    by_contra h
    push_neg at h
    exact hA (ContinuousLinearMap.ext h)
  set u' : ℝ × ℝ := (A u)⁻¹ • u with hu'def
  have hAu' : A u' = 1 := by
    rw [hu'def, map_smul, smul_eq_mul, inv_mul_cancel₀ hu]
  -- a vector of `ker A` on which `B` does not vanish
  have hnot : ¬ (∀ z : ℝ × ℝ, A z = 0 → B z = 0) := by
    intro hsub
    have hpoint : ∀ x : ℝ × ℝ, B x = B u' * A x := by
      intro x
      have hker : A (x - (A x) • u') = 0 := by
        rw [map_sub, map_smul, hAu', smul_eq_mul, mul_one, sub_self]
      have h0 : B (x - (A x) • u') = 0 := hsub _ hker
      rw [map_sub, map_smul, smul_eq_mul] at h0
      nlinarith [h0]
    have hBu' : B u' ≠ 0 := by
      intro h0
      apply hB
      refine ContinuousLinearMap.ext fun x => ?_
      rw [hpoint x, h0, zero_mul]
      rfl
    have hAeq : A = (B u')⁻¹ • B := by
      refine ContinuousLinearMap.ext fun x => ?_
      simp only [smul_apply, smul_eq_mul]
      rw [hpoint x]
      rw [← mul_assoc, inv_mul_cancel₀ hBu', one_mul]
    exact hind (B u')⁻¹ hAeq
  push_neg at hnot
  obtain ⟨z, hzA, hzB⟩ := hnot
  set s : ℝ := -(B u' + 1) / B z with hsdef
  have hs : s * B z = -(B u' + 1) := by
    rw [hsdef]
    exact div_mul_cancel₀ _ hzB
  have hAz : A (s • z) = 0 := by rw [map_smul, hzA, smul_eq_mul, mul_zero]
  have hBz : B (s • z) = -(B u' + 1) := by rw [map_smul, smul_eq_mul, hs]
  refine ⟨u' + s • z, ?_, ?_⟩
  · have h : A (u' + s • z) = 1 := by
      rw [map_add, hAu', hAz, add_zero]
    rw [h]; norm_num
  · have h : B (u' + s • z) = -1 := by
      rw [map_add, hBz]
      ring
    rw [h]; norm_num

/-! ## The one-dimensional pair lemma -/

/-- **A `C¹` function of one variable with positive derivative at `0` and another with negative
derivative at `0` satisfy both one-sided inequalities at a *common* small positive parameter.** -/
lemma exists_pos_near_lt_of_pair {φ ψ : ℝ → ℝ} {c d : ℝ} (hφ : HasDerivAt φ c 0)
    (hψ : HasDerivAt ψ d 0) (hc : 0 < c) (hd : d < 0) :
    ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 < t ∧ t < ε ∧ φ 0 < φ t ∧ ψ t < ψ 0 := by
  intro ε hε
  have hev1 : ∀ᶠ t in nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ),
      c / 2 < t⁻¹ * (φ (0 + t) - φ 0) := by
    have h := hφ.tendsto_slope_zero.eventually
      (isOpen_Ioi.mem_nhds (show c / 2 < c by linarith))
    simpa [smul_eq_mul] using h
  have hev2 : ∀ᶠ t in nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ),
      t⁻¹ * (ψ (0 + t) - ψ 0) < d / 2 := by
    have h := hψ.tendsto_slope_zero.eventually
      (isOpen_Iio.mem_nhds (show d < d / 2 by linarith))
    simpa [smul_eq_mul] using h
  have hev := hev1.and hev2
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhdsWithin_iff.mp hev
  set t : ℝ := min δ ε / 2 with ht
  have htpos : 0 < t := by
    have h : 0 < min δ ε := lt_min hδpos hε
    rw [ht]; linarith
  have htδ : t < δ := by
    have h : min δ ε ≤ δ := min_le_left _ _
    rw [ht]; linarith
  have htε : t < ε := by
    have h : min δ ε ≤ ε := min_le_right _ _
    rw [ht]; linarith
  have htne : t ≠ 0 := ne_of_gt htpos
  have hmem : t ∈ Metric.ball (0 : ℝ) δ ∩ ({0}ᶜ : Set ℝ) := by
    refine ⟨?_, htne⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact htδ
  have h1 : c / 2 < t⁻¹ * (φ (0 + t) - φ 0) := (hδ hmem).1
  have h2 : t⁻¹ * (ψ (0 + t) - ψ 0) < d / 2 := (hδ hmem).2
  refine ⟨t, htpos, htε, ?_, ?_⟩
  · have h3 : t * (c / 2) < φ (0 + t) - φ 0 := by
      have h4 := mul_lt_mul_of_pos_left h1 htpos
      rw [← mul_assoc, mul_inv_cancel₀ htne, one_mul] at h4
      exact h4
    simp only [zero_add] at h3
    linarith [mul_pos htpos (by linarith : (0 : ℝ) < c / 2)]
  · have h3 : ψ (0 + t) - ψ 0 < t * (d / 2) := by
      have h4 := mul_lt_mul_of_pos_left h2 htpos
      rw [← mul_assoc, mul_inv_cancel₀ htne, one_mul] at h4
      exact h4
    simp only [zero_add] at h3
    linarith [mul_neg_of_pos_of_neg htpos (by linarith : d / 2 < 0)]

/-- **A `C¹` function of one variable with positive derivative at `0` takes values strictly above
its value at `0` arbitrarily close to `0` on the right.** -/
lemma exists_pos_near_gt_of_hasDerivAt {φ : ℝ → ℝ} {c : ℝ} (hφ : HasDerivAt φ c 0)
    (hc : 0 < c) : ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 < t ∧ t < ε ∧ φ 0 < φ t := by
  intro ε hε
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) ({0}ᶜ : Set ℝ),
      c / 2 < t⁻¹ * (φ (0 + t) - φ 0) := by
    have h := hφ.tendsto_slope_zero.eventually
      (isOpen_Ioi.mem_nhds (show c / 2 < c by linarith))
    simpa [smul_eq_mul] using h
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhdsWithin_iff.mp hev
  set t : ℝ := min δ ε / 2 with ht
  have htpos : 0 < t := by
    have h : 0 < min δ ε := lt_min hδpos hε
    rw [ht]; linarith
  have htδ : t < δ := by
    have h : min δ ε ≤ δ := min_le_left _ _
    rw [ht]; linarith
  have htε : t < ε := by
    have h : min δ ε ≤ ε := min_le_right _ _
    rw [ht]; linarith
  have htne : t ≠ 0 := ne_of_gt htpos
  have hmem : t ∈ Metric.ball (0 : ℝ) δ ∩ ({0}ᶜ : Set ℝ) := by
    refine ⟨?_, htne⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos htpos]
    exact htδ
  have h1 : c / 2 < t⁻¹ * (φ (0 + t) - φ 0) := hδ hmem
  refine ⟨t, htpos, htε, ?_⟩
  have h3 : t * (c / 2) < φ (0 + t) - φ 0 := by
    have h4 := mul_lt_mul_of_pos_left h1 htpos
    rw [← mul_assoc, mul_inv_cancel₀ htne, one_mul] at h4
    exact h4
  simp only [zero_add] at h3
  linarith [mul_pos htpos (by linarith : (0 : ℝ) < c / 2)]

/-! ## The two-variable lemmas, along a direction of positive derivative -/

/-- **A `C¹` function of two variables whose differential does not vanish at `p` takes values
strictly above its value at `p` arbitrarily close to `p`.**  The direction `w` with `A w > 0`
(`A = df_p`) is produced by `exists_dir_pos_of_ne_zero`, and
`exists_pos_near_gt_of_hasDerivAt` is applied to the one-variable function
`t ↦ f (p + t • w)`. -/
lemma exists_near_gt_of_fderiv_ne_zero {f : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : HasFDerivAt f (fderiv ℝ f p) p) (hne : fderiv ℝ f p ≠ 0) :
    ∀ ε : ℝ, 0 < ε → ∃ q : ℝ × ℝ, ‖q - p‖ < ε ∧ f p < f q := by
  obtain ⟨w, hAw⟩ := exists_dir_pos_of_ne_zero hne
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr (fun h0 => by
    rw [h0] at hAw
    simp at hAw)
  have hpath : HasDerivAt (fun t : ℝ => p + t • w) w 0 := by
    have h : HasDerivAt (fun y : ℝ => y • w) ((1 : ℝ) • w) 0 :=
      (hasDerivAt_id (0 : ℝ)).smul_const w
    have h'' : HasDerivAt (fun t : ℝ => p + t • w) ((1 : ℝ) • w) 0 := h.const_add p
    simpa using h''
  have hf' : HasFDerivAt f (fderiv ℝ f p) (p + (0 : ℝ) • w) := by simpa using hf
  have hφ : HasDerivAt (f ∘ fun t : ℝ => p + t • w) (fderiv ℝ f p w) 0 := by
    have := hf'.comp_hasDerivAt (0 : ℝ) hpath
    simpa using this
  intro ε hε
  obtain ⟨t, htpos, htlt, hφlt⟩ :=
    exists_pos_near_gt_of_hasDerivAt hφ hAw (ε / (‖w‖ + 1)) (div_pos hε (by linarith))
  refine ⟨p + t • w, ?_, ?_⟩
  · have hlen : ‖(p + t • w) - p‖ = t * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    rw [hlen]
    have ha : t * ‖w‖ < (ε / (‖w‖ + 1)) * ‖w‖ := mul_lt_mul_of_pos_right htlt hwn
    have hb : (ε / (‖w‖ + 1)) * ‖w‖ < (ε / (‖w‖ + 1)) * (‖w‖ + 1) :=
      mul_lt_mul_of_pos_left (by linarith) (div_pos hε (by linarith))
    have hc : (ε / (‖w‖ + 1)) * (‖w‖ + 1) = ε := div_mul_cancel₀ ε (by linarith)
    linarith [ha, hb, hc.le, hc.ge]
  · simpa using hφlt

/-- **Two `C¹` functions of two variables whose differentials at `p` are nonzero and not parallel
satisfy, at a point arbitrarily close to `p`, the strict inequalities `f p < f ·` and
`· < g p` simultaneously.**  The direction `w` with `A w > 0` and `B w < 0` (`A = df_p`,
`B = dg_p`) is produced by `exists_dir_neg_of_indep`, and `exists_pos_near_lt_of_pair` is applied to
`t ↦ f (p + t • w)` and `t ↦ g (p + t • w)`. -/
lemma exists_near_lt_of_fderiv_indep {f g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hf : HasFDerivAt f (fderiv ℝ f p) p) (hg : HasFDerivAt g (fderiv ℝ g p) p)
    (hfne : fderiv ℝ f p ≠ 0) (hgne : fderiv ℝ g p ≠ 0)
    (hind : ∀ t : ℝ, fderiv ℝ f p ≠ t • fderiv ℝ g p) :
    ∀ ε : ℝ, 0 < ε → ∃ q : ℝ × ℝ, ‖q - p‖ < ε ∧ f p < f q ∧ g q < g p := by
  obtain ⟨w, hAw, hBw⟩ := exists_dir_neg_of_indep hfne hgne hind
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr (fun h0 => by
    rw [h0] at hAw
    simp at hAw)
  have hpath : HasDerivAt (fun t : ℝ => p + t • w) w 0 := by
    have h : HasDerivAt (fun y : ℝ => y • w) ((1 : ℝ) • w) 0 :=
      (hasDerivAt_id (0 : ℝ)).smul_const w
    have h'' : HasDerivAt (fun t : ℝ => p + t • w) ((1 : ℝ) • w) 0 := h.const_add p
    simpa using h''
  have hf' : HasFDerivAt f (fderiv ℝ f p) (p + (0 : ℝ) • w) := by simpa using hf
  have hg' : HasFDerivAt g (fderiv ℝ g p) (p + (0 : ℝ) • w) := by simpa using hg
  have hφ : HasDerivAt (f ∘ fun t : ℝ => p + t • w) (fderiv ℝ f p w) 0 := by
    have := hf'.comp_hasDerivAt (0 : ℝ) hpath
    simpa using this
  have hψ : HasDerivAt (g ∘ fun t : ℝ => p + t • w) (fderiv ℝ g p w) 0 := by
    have := hg'.comp_hasDerivAt (0 : ℝ) hpath
    simpa using this
  intro ε hε
  obtain ⟨t, htpos, htlt, hφlt, hψlt⟩ :=
    exists_pos_near_lt_of_pair hφ hψ hAw hBw (ε / (‖w‖ + 1))
      (div_pos hε (by linarith))
  refine ⟨p + t • w, ?_, ?_, ?_⟩
  · have hlen : ‖(p + t • w) - p‖ = t * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    rw [hlen]
    have ha : t * ‖w‖ < (ε / (‖w‖ + 1)) * ‖w‖ := mul_lt_mul_of_pos_right htlt hwn
    have hb : (ε / (‖w‖ + 1)) * ‖w‖ < (ε / (‖w‖ + 1)) * (‖w‖ + 1) :=
      mul_lt_mul_of_pos_left (by linarith) (div_pos hε (by linarith))
    have hc : (ε / (‖w‖ + 1)) * (‖w‖ + 1) = ε := div_mul_cancel₀ ε (by linarith)
    linarith [ha, hb, hc.le, hc.ge]
  · simpa using hφlt
  · simpa using hψlt

/-! ## The box-sphere regime -/

/-- **Clause 2 at a point of the surface on the box sphere**, from the junction genericity: the
level curve of the sweep height crosses the box sphere transversally there, so the surface, inside
the box, is at levels strictly above `lam` arbitrarily close to `z`; such points lie in the region
`openTiltedSweepRegion … lam`. -/
theorem aboveGenericAt_of_boxSphere {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 lam : ℝ}
    (hJ : JunctionGen ψ s c σ u v h ℓ exc lam0 lam1) (hlam : lam ∈ Set.Icc lam0 lam1)
    (hne : lam ∉ (exc : Set ℝ)) :
    ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → z ∉ Submission.PBox s c σ →
      z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lam →
      z ∈ closure (Work.Drive.EpsFormSphere.openTiltedSweepRegion
            (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) ∪
        ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) := by
  intro z hzc hznb hzcl hslab hzl
  -- `z ∈ closure PBox` together with `z ∉ PBox` forces `boxNorm c σ z = s`
  have hnorm_le : Submission.boxNorm c σ z ≤ s :=
    closure_minimal (fun _ hy => le_of_lt ((Submission.mem_PBox_iff s c σ _).mp hy))
      (isClosed_le (Work.Topology.SphereSlicing.boxNorm_continuous c σ) continuous_const) hzcl
  have hnorm : Submission.boxNorm c σ z = s := by
    refine le_antisymm hnorm_le ?_
    by_contra hlt
    exact hznb ((Submission.mem_PBox_iff s c σ z).mpr (lt_of_not_ge hlt))
  obtain ⟨p, hpar, hfne, hgne, hind⟩ := hJ.1 lam hlam hne z hzc hnorm hslab hzl
  refine Or.inl (Metric.mem_closure_iff.mpr fun ε hε => ?_)
  have hf : HasFDerivAt (Work.Drive.EpsForm.sweepHeight ψ ℓ)
      (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p) p :=
    (((Work.Smooth.Morse.pullback_contDiff_one ψ
        (ℓ.contDiff : ContDiff ℝ 1 (fun y : R3 => ℓ y))).contDiffAt.differentiableAt
      one_ne_zero)).hasFDerivAt
  have hg : HasFDerivAt (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q))
      (fderiv ℝ (fun q : ℝ × ℝ =>
        Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) p := by
    have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ =>
        Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p := by
      by_contra h
      rw [fderiv_zero_of_not_differentiableAt h] at hgne
      exact hgne rfl
    exact hd.hasFDerivAt
  have hfp : Work.Drive.EpsForm.sweepHeight ψ ℓ p = lam := by
    show ℓ (Work.BoxShrink.Pinch.par ψ p) = lam
    rw [hpar, hzl]
  have hgp : Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s := by
    rw [hpar, hnorm]
  have hcont : ContinuousAt (Work.BoxShrink.Pinch.par ψ) p := by
    rw [Work.BoxShrink.Pinch.par_def]
    exact (Work.Smooth.Morse.param_continuous ψ).continuousAt
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont ε hε
  obtain ⟨q, hq, hqf, hqg⟩ := exists_near_lt_of_fderiv_indep hf hg hfne hgne hind δ hδpos
  -- the point `par ψ q` is in the open box and at a level strictly above `lam`
  have hbox : Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) < s := by
    have h1 := hqg
    rw [hgp] at h1
    exact h1
  have hlvl : lam < ℓ (Work.BoxShrink.Pinch.par ψ q) := by
    have h1 := hqf
    rw [hfp] at h1
    exact h1
  refine ⟨Work.BoxShrink.Pinch.par ψ q, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Work.BoxShrink.Pinch.par_mem_carrier ψ q
  · exact (Submission.mem_PBox_iff s c σ _).mpr hbox
  · rintro ⟨-, hle⟩
    exact absurd hle (not_le.mpr hlvl)
  · have hd : dist (Work.BoxShrink.Pinch.par ψ q) z < ε := by
      have h1 : dist (Work.BoxShrink.Pinch.par ψ q) (Work.BoxShrink.Pinch.par ψ p) < ε :=
        hδ (by simpa [dist_eq_norm] using hq)
      rwa [hpar] at h1
    rwa [dist_comm] at hd

/-! ## The main theorem -/

/-- **Clause 2 of the trace data from the tilt data and the junction genericity.**  At every
non-exceptional level of the window, a point of the surface in the closed box and the closed slab at
the level lies in the closure of the level's region or on the level's trace: in the open box by
clause (i) of `TiltedGenericity` (a direction of increase of the sweep height at any lift, see
`exists_near_gt_of_fderiv_ne_zero`), on the box sphere by clause (a) of `JunctionGen` (the
transversal crossing of the level curve with the box sphere, see `aboveGenericAt_of_boxSphere`). -/
theorem aboveGenericAt_of_junctionGen {ψ : Submission.Diffeo} {s u : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {v : LeanEval.KnotTheory.PardonDistortion.R3} {h R : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 lam : ℝ}
    (hs : 0 < s)
    (hT : Work.Drive.Mono.TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (hJ : Work.Drive.Mono.JunctionGen ψ s c σ u v h ℓ exc lam0 lam1)
    (hlam : lam ∈ Set.Icc lam0 lam1) (hne : lam ∉ (exc : Set ℝ)) :
    Work.Drive.Mono.AboveGenericAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  obtain ⟨hgen, _hv1, _hℓne, _hℓv, _hsize, _hh, _hRbox, _hlow, _hhigh, _hl, _hexc⟩ := hT
  have _ := hs
  intro z hzc hzcl hslab hzl
  by_cases hzb : z ∈ Submission.PBox s c σ
  · -- the open box: clause (i) of the genericity of the sweep height
    refine Or.inl (Metric.mem_closure_iff.mpr fun ε hε => ?_)
    obtain ⟨p₀, hp₀⟩ : ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z := hzc
    have hreg : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p₀ ≠ 0 :=
      hgen.1 lam hne p₀ (by rw [hp₀]; exact hzb) (by rw [hp₀]; exact hslab)
        (by rw [hp₀]; exact hzl)
    have hsw : ContDiff ℝ 1 (Work.Drive.EpsForm.sweepHeight ψ ℓ) :=
      Work.Smooth.Morse.pullback_contDiff_one ψ
        (ℓ.contDiff : ContDiff ℝ 1 (fun y : R3 => ℓ y))
    have hF : HasFDerivAt (Work.Drive.EpsForm.sweepHeight ψ ℓ)
        (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p₀) p₀ :=
      (hsw.contDiffAt.differentiableAt one_ne_zero).hasFDerivAt
    have hswv : Work.Drive.EpsForm.sweepHeight ψ ℓ p₀ = lam := by
      show ℓ (Work.BoxShrink.Pinch.par ψ p₀) = lam
      rw [hp₀, hzl]
    have hboxopen : IsOpen (Submission.PBox s c σ) :=
      Work.Topology.SphereSlicing.isOpen_PBox s c σ
    obtain ⟨ρ, hρpos, hρ⟩ := Metric.isOpen_iff.mp hboxopen z hzb
    have hcont : ContinuousAt (Work.BoxShrink.Pinch.par ψ) p₀ := by
      rw [Work.BoxShrink.Pinch.par_def]
      exact (Work.Smooth.Morse.param_continuous ψ).continuousAt
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont (min ε ρ) (lt_min hε hρpos)
    obtain ⟨q, hq, hqval⟩ := exists_near_gt_of_fderiv_ne_zero hF hreg δ hδpos
    have hdistz : dist (Work.BoxShrink.Pinch.par ψ q) z < min ε ρ := by
      have h1 : dist (Work.BoxShrink.Pinch.par ψ q) (Work.BoxShrink.Pinch.par ψ p₀) < min ε ρ :=
        hδ (by simpa [dist_eq_norm] using hq)
      rwa [hp₀] at h1
    have hlvl : lam < ℓ (Work.BoxShrink.Pinch.par ψ q) := by
      have h1 := hqval
      rw [hswv] at h1
      exact h1
    refine ⟨Work.BoxShrink.Pinch.par ψ q, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact Work.BoxShrink.Pinch.par_mem_carrier ψ q
    · exact hρ (Metric.mem_ball.mpr (lt_of_lt_of_le hdistz (min_le_right _ _)))
    · rintro ⟨-, hle⟩
      exact absurd hle (not_le.mpr hlvl)
    · rw [dist_comm]
      exact lt_of_lt_of_le hdistz (min_le_left _ _)
  · -- on the box sphere: the junction genericity
    exact aboveGenericAt_of_boxSphere hJ hlam hne z hzc hzb hzcl hslab hzl

end

end Work.Drive.Mono
