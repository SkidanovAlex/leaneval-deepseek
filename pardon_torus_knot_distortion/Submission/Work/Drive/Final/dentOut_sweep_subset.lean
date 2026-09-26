import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.openTiltedSweepRegion_subset_dentOutRegion
import Submission.Work.Drive.Final.dentOut_trace
import Submission.Work.Drive.Mono.TiltedTraceData

/-!
# L5's geometric core: `Ω₁` is the sweep region at the shifted level, up to the ball of the dent

(Project lead, `Final/NOTES_LEAD_L4_L1.md` §4, L5.)

The preimage region `Ω₁` of the dent differs from the *undeformed* sweep region at the event's level
only inside the ball of the dent:

  `Ω₁ ⊆ X (ℓ D.centre) ∪ closedBall D.centre D.r`.

The proof is the observation that the deformation is the identity off its ball: a point of `Ω₁`
outside the ball is a point of the *interior* of the removed set, and the interior of the removed set
is contained in the open sweep region — the wall `{ℓ = lam*}` is removed from the interior by the
descent direction `w` (tangent to the slab, `⟪v,w⟫ = 0`, along which `ℓ` decreases), which exists
whenever `⟪v,·⟫` and `ℓ` are not proportional (`TiltData`'s `ℓ v = 0`, `ℓ ≠ 0`, `v ≠ 0`).

The interval of the sweep between the shifted level `ℓ D.centre - a'·ℓ d` and `ℓ D.centre` is where
Pardon's counting has to be spent; this module only isolates the *point-set* content of L5.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped Topology

namespace Work.Drive.Final

noncomputable section

/-- **The interior of the removed set is contained in the open sweep region.**  A point of the
interior of `tiltedLevelRemoved … lam` which lay in the closed slab would be on the wall `{ℓ = lam}`
(any point of the slab below the level is *not* in the removed set, and points of the slab just below
the level below the wall are still in the slab) — but the descent direction `w` (tangent to the slab,
decreasing `ℓ`) produces points of the slab strictly below the level arbitrarily close to it, which
excludes the interior.  Hence such a point is outside the closed slab, which is exactly membership in
the open sweep region. -/
theorem interior_tiltedLevelRemoved_subset_sweepRegion {s u : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {h lam : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    (hdesc : ∃ w : R3, inner ℝ v w = 0 ∧ ℓ w < 0) :
    interior (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) ⊆
      Submission.PBox s c σ \
        (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∩ {y : R3 | ℓ y ≤ lam}) := by
  rintro z hz
  have hzR : z ∈ Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam := interior_subset hz
  refine ⟨hzR.1, fun hc => ?_⟩
  -- a point of the interior of the slab at the level of the wall is excluded by the descent
  have hzℓ : ℓ z = lam := by
    rcases lt_trichotomy (ℓ z) lam with hlt | heq | hgt
    · exact absurd ⟨hc.1, hlt⟩ hzR.2
    · exact heq
    · exact absurd hc.2 (not_le.mpr hgt)
  obtain ⟨w, hwv, hwℓ⟩ := hdesc
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  set t : ℝ := min (ε / 2) (ε / (2 * (‖w‖ + 1))) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have hlt : t * ‖w‖ < ε := by
    have h1 : t ≤ ε / (2 * (‖w‖ + 1)) := by rw [ht]; exact min_le_right _ _
    have h2 : (0 : ℝ) < 2 * (‖w‖ + 1) := by positivity
    have h3 : t * ‖w‖ ≤ (ε / (2 * (‖w‖ + 1))) * ‖w‖ :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg w)
    have h4 : (ε / (2 * (‖w‖ + 1))) * ‖w‖ ≤ ε / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ h2]
      nlinarith [norm_nonneg w, hε]
    linarith
  have hdist : dist (z + t • w) z < ε := by
    rw [dist_eq_norm]
    have : z + t • w - z = t • w := by abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    exact hlt
  have hslab : z + t • w ∈ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h := by
    have h1 : z ∈ Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h := hc.1
    rw [Work.Drive.EpsForm.tiltedSlabClosed, Set.mem_ofPred_eq] at h1 ⊢
    have h2 : inner ℝ v (z + t • w) = inner ℝ v z := by
      rw [inner_add_right, inner_smul_right, hwv, mul_zero, add_zero]
    rw [h2]; exact h1
  have hltℓ : ℓ (z + t • w) < lam := by
    rw [map_add, map_smul, smul_eq_mul, hzℓ]
    have := mul_neg_of_pos_of_neg htpos hwℓ
    linarith
  exact (hball hdist).2 ⟨hslab, hltℓ⟩

/-- **The descent direction of a tilted sweep** (`TiltData`'s standing hypotheses): if `v ≠ 0`,
`ℓ ≠ 0` and `ℓ v = 0`, then `ℓ` does not vanish on `v^⊥`, so some `w ⟂ v` has `ℓ w < 0`. -/
theorem exists_descend_of_inner_eq_zero {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓ : ℓ ≠ 0)
    (hℓv : ℓ v = 0) :
    ∃ w : R3, inner ℝ v w = 0 ∧ ℓ w < 0 := by
  by_contra hcon
  push Not at hcon
  have hvv : inner ℝ v v ≠ 0 := inner_self_ne_zero.mpr hv
  have hker : ∀ y : R3, ℓ y = (inner ℝ v y / inner ℝ v v) * ℓ v := by
    intro y
    set p : R3 := y - (inner ℝ v y / inner ℝ v v) • v with hp
    have hperp : inner ℝ v p = 0 := by
      rw [hp, inner_sub_right, inner_smul_right]
      rw [div_mul_cancel₀ _ hvv, sub_self]
    have h0 : ℓ p = 0 := le_antisymm (by
      have h := hcon (-p) (by simp [hperp])
      simpa using h) (hcon p hperp)
    have hy : (inner ℝ v y / inner ℝ v v) • v + p = y := by rw [hp]; abel
    calc ℓ y = ℓ ((inner ℝ v y / inner ℝ v v) • v + p) := by rw [hy]
      _ = ℓ ((inner ℝ v y / inner ℝ v v) • v) + ℓ p := by rw [map_add]
      _ = (inner ℝ v y / inner ℝ v v) * ℓ v := by rw [map_smul, smul_eq_mul, h0, add_zero]
  have hzero : ℓ v = 0 := hℓv
  refine hℓ (ContinuousLinearMap.ext fun y => ?_)
  rw [hker y, hzero, mul_zero, zero_apply]

/-- **L5's geometric core**: the preimage region of the dent is contained in the sweep region at the
event's level together with the *ball* of the dent.  (Off the ball the deformation is the identity, so
membership of `Ω₁` is membership of the interior of the removed set, which the previous lemma places
in the open sweep region.) -/
theorem dentOutRegion_subset_sweepRegion_union_ball
    {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U)
    (hdesc : ∃ w : R3, inner ℝ v w = 0 ∧ ℓ w < 0) :
    dentOutRegion ψ s c σ u v h R ℓ D ⊆
      Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
          (ℓ D.centre) ∪ Metric.closedBall D.centre D.r := by
  rintro z ⟨hzc, hzint⟩
  by_cases hzball : z ∈ Metric.closedBall D.centre D.r
  · exact Or.inr hzball
  · refine Or.inl ⟨hzc, ?_⟩
    -- off the ball the deformation is the identity, so `z` is an interior point of the removed set
    have hzout : D.r < ‖z - D.centre‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hzball
      exact not_le.mp hzball
    have hnb : ∀ᶠ y in 𝓝 z, D.r < ‖y - D.centre‖ :=
      (isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))).mem_nhds
        hzout
    have hid : ∀ᶠ y in 𝓝 z, D.deform y = y := by
      filter_upwards [hnb] with y hy
      exact dentDeform_eq_self_of_le D.r_pos D.χ_eq_zero (le_of_lt hy)
    have hR : z ∈ interior (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) := by
      rw [mem_interior_iff_mem_nhds] at hzint ⊢
      refine Filter.mem_of_superset (Filter.inter_mem hzint hid) ?_
      intro y ⟨hy1, hy2⟩
      rwa [Set.mem_preimage, hy2] at hy1
    exact interior_tiltedLevelRemoved_subset_sweepRegion (s := s) (u := u) (c := c) (v := v)
      (σ := σ) (h := h) (lam := ℓ D.centre) hdesc hR


/-- **The preimage region of the dent lies in the open box.**  Off the ball of the deformation the
image of a point of the region is the point itself (hence in the box, as the removed set is contained
in the box); inside the ball the box is preserved by the deformation (`box_pres`). -/
theorem dentOutRegion_subset_PBox {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U) :
    dentOutRegion ψ s c σ u v h R ℓ D ⊆ Submission.PBox s c σ := by
  rintro z ⟨-, hzint⟩
  have hzR : D.deform z ∈ Submission.PBox s c σ := by
    have h1 : z ∈ D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre) :=
      interior_subset hzint
    exact h1.1
  by_cases hb : ‖z - D.centre‖ ≤ D.r
  · exact (D.box_pres z hb).mpr hzR
  · have h2 : D.r ≤ ‖z - D.centre‖ := le_of_lt (not_le.mp hb)
    have h3 : D.deform z = z := by
      simpa only [AnyDentDatum.deform] using
        dentDeform_eq_self_of_le D.r_pos D.χ_eq_zero h2
    rwa [h3] at hzR

end

end Work.Drive.Final
