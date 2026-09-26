import Mathlib
import Submission.Work.Drive.Final.DentDatum
import Submission.Work.Drive.Mono.Split

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion

open scoped Topology

noncomputable section

/-- Membership in the open region of the tilted sweep, as a pure formula. -/
private theorem mem_openTiltedSweepRegion_aux {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {y : R3} :
    y ∈ Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam ↔
      y ∈ P.carrier ∧ y ∈ Submission.PBox s c σ ∧
        ¬ (|inner ℝ v y - (inner ℝ v c + u)| ≤ h ∧ ℓ y ≤ lam) := by
  simp only [Work.Drive.EpsFormSphere.openTiltedSweepRegion, Set.mem_inter_iff, Set.mem_sdiff,
    Set.mem_setOf_eq, Work.Drive.EpsForm.tiltedSlabClosed]

/-- Membership in the removed set of a level of the tilted sweep, as a pure formula. -/
private theorem mem_tiltedLevelRemoved_aux {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ} {y : R3} :
    y ∈ Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam ↔
      y ∈ Submission.PBox s c σ ∧
        ¬ (|inner ℝ v y - (inner ℝ v c + u)| ≤ h ∧ ℓ y < lam) := by
  simp only [Work.Drive.Mono.tiltedLevelRemoved, Set.mem_sdiff, Set.mem_inter_iff,
    Set.mem_setOf_eq, Work.Drive.EpsForm.tiltedSlabClosed]

/-- **Interior of an image, from the identity on a neighbourhood.**  If `T` is a neighbourhood of
`y` on which `f` is the identity and `T ⊆ S`, then `y` lies in the interior of `f '' S`. -/
private theorem mem_interior_image_of_eqOn_nhds {f : R3 → R3} {S T : Set R3} {y : R3}
    (hT : T ∈ nhds y) (hsub : T ⊆ S) (hid : ∀ z ∈ T, f z = z) : y ∈ interior (f '' S) :=
  mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset hT fun z hz => ⟨z, hsub hz, hid z hz⟩)

/-- The dent is the identity outside the ball of radius `D.r` around its centre: there the cutoff
vanishes. -/
private theorem deform_eq_self_of_r_lt {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    (D : DentDatum ψ s c σ u v h R ℓ) {z : R3} (hz : D.r < ‖z - D.centre‖) : D.deform z = z := by
  have h1 : 1 ≤ ‖z - D.centre‖ / D.r := by
    rw [one_le_div D.r_pos]
    exact le_of_lt hz
  simp only [DentDatum.deform, dentDeform, D.χ_eq_zero _ h1, mul_zero, zero_smul, add_zero]

open LeanEval.KnotTheory.PardonDistortion in
theorem dentRegion_union_strip {P : Work.CoreTopology.ParamTorus} {ψ : Submission.Diffeo}
    {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    (D : Work.Drive.Final.DentDatum ψ s c σ u v h R ℓ) {mu : ℝ} :
    Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ mu ⊆
      (closure (P.carrier ∩ interior (D.deform ''
          Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)))
        ∪ Work.Drive.Mono.levelStrip P s c σ u v h ℓ mu (ℓ D.centre))
      ∪ (P.carrier ∩ Metric.closedBall D.centre D.r) := by
  intro y hy
  rw [mem_openTiltedSweepRegion_aux] at hy
  obtain ⟨hyc, hyb, hyrem⟩ := hy
  have hPBox_open : IsOpen (Submission.PBox s c σ) :=
    Work.Topology.SphereSlicing.isOpen_PBox s c σ
  have hslabClosed : IsClosed
      (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h) :=
    Work.Drive.EpsForm.isClosed_tiltedSlabClosed _ _ _
  by_cases hball : y ∈ Metric.closedBall D.centre D.r
  · exact Or.inr ⟨hyc, hball⟩
  · have hfar : D.r < ‖y - D.centre‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hball
      exact not_le.mp hball
    have hopen_far : IsOpen {z : R3 | D.r < ‖z - D.centre‖} := by
      exact isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
    have hfar_nhds : {z : R3 | D.r < ‖z - D.centre‖} ∈ nhds y := hopen_far.mem_nhds hfar
    by_cases hslab : |inner ℝ v y - (inner ℝ v c + u)| ≤ h
    · have hmu_lt : mu < ℓ y := by
        by_contra hcon
        exact hyrem ⟨hslab, not_lt.mp hcon⟩
      by_cases hle : ℓ y ≤ ℓ D.centre
      · -- `y` lies in the closed slab between the two levels: it is in the strip.
        refine Or.inl (Or.inr ?_)
        rw [Work.Drive.Mono.levelStrip]
        exact ⟨subset_closure hyb, hslab, le_of_lt hmu_lt, hle⟩
      · -- `y` lies in the closed slab above the level of the centre: it is in the closed region.
        push_neg at hle
        refine Or.inl (Or.inl (subset_closure ⟨hyc, ?_⟩))
        refine mem_interior_image_of_eqOn_nhds
          (T := ({z : R3 | D.r < ‖z - D.centre‖} ∩ Submission.PBox s c σ) ∩
            {z : R3 | ℓ D.centre < ℓ z}) ?_ ?_ ?_
        · exact Filter.inter_mem
            (Filter.inter_mem hfar_nhds (hPBox_open.mem_nhds hyb))
            ((isOpen_lt continuous_const ℓ.continuous).mem_nhds hle)
        · rintro z ⟨⟨hzf, hzb⟩, hzl⟩
          rw [mem_tiltedLevelRemoved_aux]
          exact ⟨hzb, fun ⟨_, hzlt⟩ => absurd hzl (not_lt.mpr (le_of_lt hzlt))⟩
        · rintro z ⟨⟨hzf, _⟩, _⟩
          exact deform_eq_self_of_r_lt D hzf
    · -- `y` is outside the closed slab: it is in the closed region after all.
      refine Or.inl (Or.inl (subset_closure ⟨hyc, ?_⟩))
      refine mem_interior_image_of_eqOn_nhds
        (T := ({z : R3 | D.r < ‖z - D.centre‖} ∩ Submission.PBox s c σ) ∩
          (Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h)ᶜ) ?_ ?_ ?_
      · exact Filter.inter_mem (Filter.inter_mem hfar_nhds (hPBox_open.mem_nhds hyb))
          (hslabClosed.isOpen_compl.mem_nhds (by
            simpa only [Set.mem_compl_iff, Work.Drive.EpsForm.tiltedSlabClosed,
              Set.mem_setOf_eq] using hslab))
      · rintro z ⟨⟨_, hzb⟩, hzn⟩
        rw [mem_tiltedLevelRemoved_aux]
        exact ⟨hzb, fun ⟨hzs, _⟩ => hzn hzs⟩
      · rintro z ⟨⟨hzf, _⟩, _⟩
        exact deform_eq_self_of_r_lt D hzf

end

end Work.Drive.Final
