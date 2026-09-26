import Mathlib
import Submission.Work.Drive.Mono.SweepGeom3
import Submission.Work.Drive.Mono.Split
import Submission.Work.Drive.Mono.wallSideDefs
import Submission.Work.Drive.Mono.aboveGenericAt_of_junctionGen
import Submission.Work.Drive.Final.noJumpBelow_of_region
import Submission.Work.Drive.Final.sweep_mono

/-!
# Tools for the no-jump at an *event* level of the tilted sweep

This module contains two new bricks for `Work.Drive.Mono.noJumpBelowAt_of_anyEventAt`.

* **`Work.Drive.Mono.aboveGenericAt_at_any_level`** — clause 2 of the trace data (`AboveGenericAt`) at
  an *arbitrary* level, with **no** genericity hypothesis.  The resident proof
  `Work.Drive.Mono.aboveGenericAt_of_junctionGenC` needs the level to be *non-exceptional* (it uses
  clause (i) of the tilt data at points of the *open* box); here the open-box points are handled by
  the geometry of the box and of the removed set alone, and the box-sphere points by the
  *unrestricted* transversality clause `GammaTransverse` of `GoodSweepData3`, which holds at every
  point of the surface on the box sphere inside the closed slab, with no exceptional set.

* **`Work.Drive.Mono.noJumpBelowAt_of_wallSide_ne_bot`** — the reduction of the target to a single
  *per-level* statement: if the far side of the wall at the level `lam` has non-vanishing winding
  span, then no level of a left-neighbourhood of `lam` carries the full span.  The proof is the
  "strip" argument of `Work.Drive.Final.noJumpBelow_of_region`.

Consequently the residual of the (L) field at an event level is the single statement

  `WindingSpan P (wallSide P s c σ u v h ℓ lam) ≠ ⊥`  at a level with `WindingSpan P (sweep … lam) = ⊥`,

which is equivalent — via `Work.SurgeryInvariance.Span.union_eq_sup` applied to the cover
`carrier = sweep ∪ wall ∪ wallSide` — to Pardon's counting input at that level, namely the
non-`⊤`-ness of the wall's own span.
-/

open LeanEval.KnotTheory.PardonDistortion Set

set_option maxHeartbeats 1000000

namespace Work.Drive.Mono

noncomputable section

variable {ψ : Submission.Diffeo} {s u h : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ}

/-! ## 0. Elementary ingredients -/

theorem convex_PBox' : Convex ℝ (Submission.PBox s c σ) :=
  Work.Topology.SphereSlicing.convex_PBox s c σ

theorem interior_PBox' : interior (Submission.PBox s c σ) = Submission.PBox s c σ :=
  (Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq

/-- A direction on which `ℓ` decreases. -/
theorem exists_dir_ell_neg (hℓne : ℓ ≠ 0) : ∃ w : R3, ℓ w < 0 := by
  by_contra hcon
  push_neg at hcon
  refine hℓne (ContinuousLinearMap.ext fun y => ?_)
  have h1 : 0 ≤ ℓ y := hcon y
  have h2 : 0 ≤ ℓ (-y) := hcon (-y)
  rw [map_neg] at h2
  simp only [ContinuousLinearMap.zero_apply]
  exact le_antisymm (by linarith) h1

/-- A direction decreasing `ℓ` and pushing the slab functional `⟪v,·⟫ - a` towards (or past) zero. -/
theorem exists_dir_neg_slab (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) (b : ℝ) :
    ∃ d : R3, ℓ d < 0 ∧ (0 < b → inner ℝ v d < 0) ∧ (b < 0 → 0 < inner ℝ v d) := by
  obtain ⟨w, hw⟩ := exists_dir_ell_neg (ℓ := ℓ) hℓne
  have hnormv : 0 < ‖v‖ ^ 2 := by positivity
  have hne : (‖v‖ ^ 2) ≠ 0 := ne_of_gt hnormv
  have hkey : ∀ s : ℝ, inner ℝ v (w - s • v) = inner ℝ v w - s * ‖v‖ ^ 2 := by
    intro s
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
  have hℓkey : ∀ s : ℝ, ℓ (w - s • v) = ℓ w := by
    intro s
    rw [map_sub, map_smul, hℓv, smul_eq_mul, mul_zero, sub_zero]
  rcases lt_trichotomy b 0 with hb | hb | hb
  · -- `b < 0`: move in the direction where the slab value increases
    have hval : inner ℝ v (w - (inner ℝ v w / ‖v‖ ^ 2 - 1) • v)
        = inner ℝ v w - inner ℝ v w + ‖v‖ ^ 2 := by
      rw [hkey]
      have : (inner ℝ v w / ‖v‖ ^ 2 - 1) * ‖v‖ ^ 2 = inner ℝ v w - ‖v‖ ^ 2 := by
        rw [sub_mul, div_mul_cancel₀ _ hne, one_mul]
      rw [this]; ring
    refine ⟨w - (inner ℝ v w / ‖v‖ ^ 2 - 1) • v, ?_, ?_, ?_⟩
    · have : ℓ (w - (inner ℝ v w / ‖v‖ ^ 2 - 1) • v) = ℓ w := hℓkey _
      rw [this]; exact hw
    · intro hcon; exact absurd hcon.le (not_le.mpr hb)
    · intro _
      rw [hval]
      linarith
  · -- `b = 0`: any direction decreasing `ℓ` keeps the slab value small
    refine ⟨w, ?_, ?_, ?_⟩
    · have : ℓ (w - (0:ℝ) • v) = ℓ w := hℓkey 0
      simpa using hw
    · intro hcon; exact absurd hb (ne_of_gt hcon)
    · intro hcon; exact absurd hb (ne_of_lt hcon)
  · -- `b > 0`: move in the direction where the slab value decreases
    have hval : inner ℝ v (w - (inner ℝ v w / ‖v‖ ^ 2 + 1) • v)
        = inner ℝ v w - inner ℝ v w - ‖v‖ ^ 2 := by
      rw [hkey]
      have : (inner ℝ v w / ‖v‖ ^ 2 + 1) * ‖v‖ ^ 2 = inner ℝ v w + ‖v‖ ^ 2 := by
        rw [add_mul, div_mul_cancel₀ _ hne, one_mul]
      rw [this]; ring
    refine ⟨w - (inner ℝ v w / ‖v‖ ^ 2 + 1) • v, ?_, ?_, ?_⟩
    · have : ℓ (w - (inner ℝ v w / ‖v‖ ^ 2 + 1) • v) = ℓ w := hℓkey _
      rw [this]; exact hw
    · intro _
      rw [hval]
      linarith
    · intro hcon; exact absurd hcon.le (not_le.mpr hb)

/-! ## 1. A surface point on a slab face of the box sphere -/

/-- **A surface point on the box sphere whose slab value is exactly `±h` is in the closure of the
level's removed set.**  Starting from `z` we walk along the segment towards a point of the open box
that lies strictly outside the closed slab on the *same* side: the segment stays in the open box (the
box is convex and `z` is in its closure) and its slab value increases beyond `h` in absolute value. -/
theorem mem_closure_removed_of_slab_eq
    {lam : ℝ} (hh : 0 < h)
    (hslabP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y)
    (hslabM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h)
    {z : R3} (hzcl : z ∈ closure (Submission.PBox s c σ)) (hznb : z ∉ Submission.PBox s c σ)
    (hslabz : |inner ℝ v z - (inner ℝ v c + u)| = h) :
    z ∈ closure (tiltedLevelRemoved s c σ u v h ℓ lam) := by
  have hsplit : inner ℝ v z - (inner ℝ v c + u) = h ∨
      inner ℝ v z - (inner ℝ v c + u) = -h := by
    rcases lt_trichotomy (inner ℝ v z - (inner ℝ v c + u)) 0 with h' | h' | h'
    · right; rw [abs_of_neg h'] at hslabz; linarith
    · rw [h'] at hslabz
      simp only [abs_zero] at hslabz
      exact absurd hslabz.symm (ne_of_gt hh)
    · left; rw [abs_of_pos h'] at hslabz; exact hslabz
  obtain ⟨y, hyP, hySlab⟩ : ∃ y : R3, y ∈ Submission.PBox s c σ ∧
      h < inner ℝ v y - (inner ℝ v c + u) := by
    obtain ⟨y, hyP, hy⟩ := hslabP
    exact ⟨y, hyP, by linarith⟩
  obtain ⟨y', hy'P, hy'Slab⟩ : ∃ y' : R3, y' ∈ Submission.PBox s c σ ∧
      inner ℝ v y' - (inner ℝ v c + u) < -h := by
    obtain ⟨y, hyP, hy⟩ := hslabM
    exact ⟨y, hyP, by linarith⟩
  rcases hsplit with hz | hz
  · -- `z` on the upper face of the slab
    refine Metric.mem_closure_iff.mpr fun ε hε => ?_
    have hyz : 0 < ‖y - z‖ + 1 := by positivity
    set t : ℝ := min 1 (ε / (2 * (‖y - z‖ + 1))) with htdef
    have htpos : 0 < t := lt_min one_pos (by positivity)
    have htle : t ≤ 1 := min_le_left _ _
    have htbal : t * ‖y - z‖ < ε := by
      have h1 : t ≤ ε / (2 * (‖y - z‖ + 1)) := min_le_right _ _
      have h2 : t * ‖y - z‖ ≤ (ε / (2 * (‖y - z‖ + 1))) * ‖y - z‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      have h3 : (ε / (2 * (‖y - z‖ + 1))) * ‖y - z‖ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg (y - z), hε]
      linarith
    refine ⟨z + t • (y - z), ⟨?_, ?_⟩, ?_⟩
    · exact interior_PBox' ▸ (convex_PBox' (s := s) (c := c) (σ := σ)).add_smul_sub_mem_interior'
        hzcl (by rw [interior_PBox']; exact hyP) ⟨htpos, htle⟩
    · rintro ⟨hc, -⟩
      have hlin : inner ℝ v (z + t • (y - z)) =
          (1 - t) * inner ℝ v z + t * inner ℝ v y := by
        simp only [inner_add_right, inner_sub_right, inner_smul_right]
        ring
      have hval : h < inner ℝ v (z + t • (y - z)) - (inner ℝ v c + u) := by
        rw [hlin]
        nlinarith [hz, hySlab, htpos, htle]
      have hle : |inner ℝ v (z + t • (y - z)) - (inner ℝ v c + u)| ≤ h := hc
      rw [abs_of_pos (by linarith)] at hle
      linarith
    · rw [dist_eq_norm]
      have hsub : z - (z + t • (y - z)) = -(t • (y - z)) := by abel
      rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      exact htbal
  · -- `z` on the lower face of the slab
    refine Metric.mem_closure_iff.mpr fun ε hε => ?_
    have hyz : 0 < ‖y' - z‖ + 1 := by positivity
    set t : ℝ := min 1 (ε / (2 * (‖y' - z‖ + 1))) with htdef
    have htpos : 0 < t := lt_min one_pos (by positivity)
    have htle : t ≤ 1 := min_le_left _ _
    have htbal : t * ‖y' - z‖ < ε := by
      have h1 : t ≤ ε / (2 * (‖y' - z‖ + 1)) := min_le_right _ _
      have h2 : t * ‖y' - z‖ ≤ (ε / (2 * (‖y' - z‖ + 1))) * ‖y' - z‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      have h3 : (ε / (2 * (‖y' - z‖ + 1))) * ‖y' - z‖ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg (y' - z), hε]
      linarith
    refine ⟨z + t • (y' - z), ⟨?_, ?_⟩, ?_⟩
    · exact interior_PBox' ▸ (convex_PBox' (s := s) (c := c) (σ := σ)).add_smul_sub_mem_interior'
        hzcl (by rw [interior_PBox']; exact hy'P) ⟨htpos, htle⟩
    · rintro ⟨hc, -⟩
      have hlin : inner ℝ v (z + t • (y' - z)) =
          (1 - t) * inner ℝ v z + t * inner ℝ v y' := by
        simp only [inner_add_right, inner_sub_right, inner_smul_right]
        ring
      have hval : inner ℝ v (z + t • (y' - z)) - (inner ℝ v c + u) < -h := by
        rw [hlin]
        nlinarith [hz, hy'Slab, htpos, htle]
      have hle : |inner ℝ v (z + t • (y' - z)) - (inner ℝ v c + u)| ≤ h := hc
      rw [abs_of_neg (by linarith)] at hle
      linarith
    · rw [dist_eq_norm]
      have hsub : z - (z + t • (y' - z)) = -(t • (y' - z)) := by abel
      rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      exact htbal

/-! ## 2. The closed region and its trace -/

/-- **The surface points in the closure of the level's region are in the region or on the level's
trace.**  A point of the surface in `closure X` is in `closure R` for the removed set `R`, and if it
were in the interior of `R` it would be in `X`, since the interior of `R` is contained in
`PBox \ (slab ∩ {ℓ ≤ lam})` and `X` is the part of that set lying in the surface. -/
theorem carrier_inter_closure_sweep_subset {P : Work.CoreTopology.ParamTorus} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (hdesc : ∃ w : R3, inner ℝ v w = 0 ∧ ℓ w < 0) :
    P.carrier ∩ closure (Work.Drive.Final.sweep P s c σ u v h ℓ lam) ⊆
      Work.Drive.Final.sweep P s c σ u v h ℓ lam ∪ wall P s c σ u v h ℓ lam := by
  rintro z ⟨hzc, hzcl⟩
  by_cases hzX : z ∈ Work.Drive.Final.sweep P s c σ u v h ℓ lam
  · exact Or.inl hzX
  · refine Or.inr ⟨hzc, closure_mono ?_ hzcl, fun hint => hzX ?_⟩
    · intro y hy
      rw [Work.Drive.Mono.mem_openTiltedSweepRegion_iff] at hy
      obtain ⟨hyc, hyP, hyrem⟩ := hy
      exact ⟨hyP, fun hc => hyrem ⟨hc.1, le_of_lt hc.2⟩⟩
    · have h1 := Work.Drive.Final.interior_tiltedLevelRemoved_subset_sweepRegion
        (s := s) (u := u) (c := c) (v := v) (σ := σ) (h := h) (lam := lam) (ℓ := ℓ) hdesc hint
      exact Work.Drive.Mono.mem_openTiltedSweepRegion_iff.mpr ⟨hzc, h1.1, h1.2⟩

/-! ## 3. The box-sphere case at an arbitrary level -/

/-- **Clause 2 of the trace data at a surface point of the box sphere**, from the *unrestricted*
transversality clause of `GoodSweepData3`: at every point of the surface on the box sphere inside the
closed slab, the box-norm functional is a submersion and no multiple of its differential is the
differential of the sweep height.  This is
`Work.Drive.Mono.aboveGenericAt_of_boxSphere_of_junctionGenC` with the exceptional-set restriction
removed, so that it applies at *every* level. -/
theorem aboveGenericAt_of_boxSphere_of_transverse
    {ψ : Submission.Diffeo} {s u h lam : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ}
    (hGT : ∀ p : ℝ × ℝ, Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| ≤ h →
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) :
    ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → z ∉ Submission.PBox s c σ →
      z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lam →
      z ∈ closure (Work.Drive.EpsFormSphere.openTiltedSweepRegion
            (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) ∪
        ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) := by
  intro z hzc hznb hzcl hslab hzl
  have hnorm_le : Submission.boxNorm c σ z ≤ s :=
    closure_minimal (fun _ hy => le_of_lt ((Submission.mem_PBox_iff s c σ _).mp hy))
      (isClosed_le (Work.Topology.SphereSlicing.boxNorm_continuous c σ) continuous_const) hzcl
  have hnorm : Submission.boxNorm c σ z = s := by
    refine le_antisymm hnorm_le ?_
    by_contra hlt
    exact hznb ((Submission.mem_PBox_iff s c σ z).mpr (lt_of_not_ge hlt))
  obtain ⟨p, hpar⟩ : ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z := hzc
  have hnorm' : Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s := by rw [hpar]; exact hnorm
  have hslab' : |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| ≤ h := by
    rw [hpar]; exact hslab
  obtain ⟨hgne, hind⟩ := hGT p hnorm' hslab'
  have hfne : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0 := by
    intro h0
    exact hind 0 (by rw [h0, zero_smul])
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
  obtain ⟨q, hq, hqf, hqg⟩ :=
    Work.Drive.Mono.exists_near_lt_of_fderiv_indep hf hg hfne hgne hind δ hδpos
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

/-! ## 4. The level-genericity of the sweep at an arbitrary level -/

/-- **The level-genericity of the sweep at an arbitrary level.**  Every surface point in the closed
box and the closed slab at the level `lam` lies in the closure of the level's region or on the
level's trace:

* in the open box, a point at the level is either strictly outside the closed slab — hence in the
  region — or at slab value at most `h`, in which case it is in the removed set but not in its
  interior (the interior of the removed set is contained in `PBox \ (slab ∩ {ℓ ≤ lam})`), hence on
  the trace;
* on the box sphere, a point on a slab face is in the closure of the removed set (walk towards a
  point of the box strictly outside the slab, on the same side), and a point strictly inside the slab
  is handled by the unrestricted transversality clause.

No genericity of the height at the level is used. -/
theorem aboveGenericAt_at_any_level
    {ψ : Submission.Diffeo} {s u h : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ}
    (hGT : ∀ p : ℝ × ℝ, Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| ≤ h →
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p)
    (hslabP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y)
    (hslabM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h)
    (hh : 0 < h) (hv : v ≠ 0) (hℓne : ℓ ≠ 0) (hℓv : ℓ v = 0) (lam : ℝ) :
    Work.Drive.Mono.AboveGenericAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  intro z hzc hzcl hslab hzl
  by_cases hzP : z ∈ Submission.PBox s c σ
  · by_cases hslabz : |inner ℝ v z - (inner ℝ v c + u)| ≤ h
    · -- in the open box, in the closed slab: on the trace
      refine Or.inr ⟨hzc, subset_closure ?_, ?_⟩
      · refine ⟨hzP, ?_⟩
        rintro ⟨-, hlt⟩
        simp only [Set.mem_setOf_eq] at hlt
        rw [hzl] at hlt
        exact lt_irrefl lam hlt
      · intro hint
        have h1 := Work.Drive.Final.interior_tiltedLevelRemoved_subset_sweepRegion
          (s := s) (u := u) (c := c) (v := v) (σ := σ) (h := h) (lam := lam) (ℓ := ℓ)
          (Work.Drive.Final.exists_descend_of_inner_eq_zero hv hℓne hℓv) hint
        refine h1.2 ⟨hslabz, ?_⟩
        simp only [Set.mem_setOf_eq]
        rw [hzl]
    · -- in the open box, strictly outside the closed slab: in the region
      refine Or.inl (subset_closure (Work.Drive.Mono.mem_openTiltedSweepRegion_iff.mpr
        ⟨hzc, hzP, fun hcon => hslabz hcon.1⟩))
  · by_cases hslabz : |inner ℝ v z - (inner ℝ v c + u)| = h
    · -- on the box sphere, on a slab face: in the closure of the removed set
      refine Or.inr ⟨hzc, Work.Drive.Mono.mem_closure_removed_of_slab_eq hh hslabP hslabM hzcl hzP
        hslabz, ?_⟩
      intro hint
      exact hzP (Work.Drive.Final.interior_tiltedLevelRemoved_subset_sweepRegion
        (s := s) (u := u) (c := c) (v := v) (σ := σ) (h := h) (lam := lam) (ℓ := ℓ)
        (Work.Drive.Final.exists_descend_of_inner_eq_zero hv hℓne hℓv) hint).1
    · -- on the box sphere, strictly inside the slab: transversality
      exact Work.Drive.Mono.aboveGenericAt_of_boxSphere_of_transverse hGT z hzc hzP hzcl hslab hzl

/-! ## 5. The reduction of the target to the far side at the level -/

/-- **The no-jump below a level, from the non-vanishing of the far side's span at that level.**

Assume `W (sweep lam) = ⊥` and take an essential loop `ζ` of the far side `wallSide lam`.  The far
side is disjoint from the region and from the wall, and the surface points of the closure of the
region are in the region or on the wall (`carrier_inter_closure_sweep_subset`), so `ζ` avoids the
closure of the region.  By the level-genericity (`aboveGenericAt_at_any_level`) and the strip lemma
`Work.Drive.Final.exists_levelStrip_disjoint_of_gen`, `ζ` then also avoids the strips below `lam`; and
every level region just below `lam` is contained in the closure of the region together with that strip
(`Work.Drive.Mono.levelRegion_subset_closure_union_levelStrip`).  So `ζ` avoids every level region of
a left-neighbourhood of `lam`, and `Work.PinchLemma3.ClosedDiscA.ne_top_of_disjoint_essential`
concludes. -/
theorem noJumpBelowAt_of_wallSide_ne_bot
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h R : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {lam : ℝ} (hlam : lam ∈ Set.Icc lam0 lam1)
    (hfar : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
      (wallSide (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) ≠ ⊥) :
    ∃ mu0 : ℝ, mu0 < lam ∧ ∀ mu ∈ Set.Ico mu0 lam,
      Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ mu) ≠ ⊤ := by
  obtain ⟨hdata, hG3, -⟩ := hDP
  obtain ⟨hgen0, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, hexc⟩ := hdata.tilt
  have hv : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv1
    exact one_ne_zero hv1.symm
  obtain ⟨hGS2, hEF, hBelt, hSBCR, hGT, hFRC, hCorner, hOffK, hOne, hSph⟩ := hG3
  obtain ⟨hslabP, hslabM⟩ := hdata.slabCuts
  set P := Work.Drive.EpsSphere.torusOf ψ with hP
  have hdesc : ∃ w : R3, inner ℝ v w = 0 ∧ ℓ w < 0 :=
    Work.Drive.Final.exists_descend_of_inner_eq_zero hv hℓne hℓv
  have hAG := Work.Drive.Mono.aboveGenericAt_at_any_level (ψ := ψ) hGT hslabP hslabM hh hv hℓne hℓv
    lam
  have hcl_sub := Work.Drive.Mono.carrier_inter_closure_sweep_subset (P := P)
    (s := s) (u := u) (c := c) (σ := σ) (v := v) (h := h) (ℓ := ℓ) (lam := lam) hdesc
  -- the essential loop of the far side
  obtain ⟨ζ, hζess, hζmem⟩ := (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hfar
  have hζav : ∀ t : ℝ, ζ.γ t ∉ closure (Work.Drive.Final.sweep P s c σ u v h ℓ lam) ∪
      (P.carrier ∩ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) := by
    intro t
    rintro (h1 | h2)
    · have h3 : ζ.γ t ∈ P.carrier ∩ closure (Work.Drive.Final.sweep P s c σ u v h ℓ lam) :=
        ⟨ζ.mem t, h1⟩
      rcases hcl_sub h3 with h | h
      · exact (Work.Drive.Mono.mem_wallSide_iff.mp (hζmem t)).2.1 h
      · exact (Work.Drive.Mono.mem_wallSide_iff.mp (hζmem t)).2.2 h
    · exact (Work.Drive.Mono.mem_wallSide_iff.mp (hζmem t)).2.2 h2
  -- the strips below `lam` miss the loop
  obtain ⟨mu0, hmu0lt, hstrip'⟩ :=
    Work.Drive.Final.exists_levelStrip_disjoint_of_gen (P := P) (s := s) (u := u) (c := c)
      (σ := σ) (v := v) (h := h) (ℓ := ℓ) (lamstar := lam) (δ := ζ)
      (Z := closure (Work.Drive.Final.sweep P s c σ u v h ℓ lam) ∪
        (P.carrier ∩ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)))
      hAG (by
        rw [Set.disjoint_left]
        rintro z hz hzZ
        obtain ⟨t, rfl⟩ := hz
        exact hζav t hzZ)
  refine ⟨mu0, hmu0lt, fun mu hmu => ?_⟩
  refine Work.PinchLemma3.ClosedDiscA.ne_top_of_disjoint_essential P
    (X := Work.Drive.Final.sweep P s c σ u v h ℓ mu)
    (fun z hz => (Work.Drive.Mono.mem_openTiltedSweepRegion_iff.mp hz).1) (fun t hcon => ?_)
    ((Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P ζ).mp hζess)
  have hsub := Work.Drive.Mono.levelRegion_subset_closure_union_levelStrip (P := P)
    (s := s) (c := c) (σ := σ) (u := u) (v := v) (h := h) (ℓ := ℓ) (mu := mu) (lamstar := lam)
    hcon
  rcases hsub with h | h
  · exact hζav t (Or.inl h)
  · exact (Set.disjoint_left.mp (hstrip' mu hmu)) ⟨t, rfl⟩ h

end

end Work.Drive.Mono
