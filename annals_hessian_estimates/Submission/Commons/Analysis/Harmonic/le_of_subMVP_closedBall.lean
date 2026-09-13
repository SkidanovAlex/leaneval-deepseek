import Mathlib
import Submission.Commons.Analysis.Harmonic.integral_laplacian_nonneg_of_ball_meanValue_cs
import Submission.Commons.Analysis.Harmonic.laplacian_nonneg_of_le_setAverage_ball

noncomputable section

open MeasureTheory Metric Filter Topology
open scoped ENNReal Topology

namespace Commons.Analysis.Harmonic

/-- Monotonicity of the set average of real-valued functions. -/
private lemma setAverage_mono' {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f g : α → ℝ} (hfs : IntegrableOn f s μ) (hgs : IntegrableOn g s μ)
    (hs : MeasurableSet s) (h : ∀ x ∈ s, f x ≤ g x) :
    ⨍ x in s, f x ∂μ ≤ ⨍ x in s, g x ∂μ := by
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
  refine smul_le_smul_of_nonneg_left (MeasureTheory.setIntegral_mono_on hfs hgs hs h) ?_
  rw [inv_nonneg]
  exact MeasureTheory.measureReal_nonneg

/-- A closed metric ball of radius `(R - dist x c)/2` around an interior point `x` of `ball c R`
is contained in `ball c R`. -/
private lemma closedBall_subset_ball_of_lt {n : ℕ} {c x : EuclideanSpace ℝ (Fin n)} {R : ℝ}
    (hx : dist x c < R) :
    Metric.closedBall x ((R - dist x c) / 2) ⊆ Metric.ball c R := by
  intro y hy
  rw [Metric.mem_closedBall] at hy
  rw [Metric.mem_ball]
  have h2 : dist y c ≤ dist y x + dist x c := dist_triangle y x c
  linarith

/-- **Propagation step.** If `f` is continuous on the closed ball `closedBall x r`, is bounded
above by `M` on the open ball `ball x r`, and its average over `ball x r` equals `M`, then `f`
equals `M` on the whole open ball.  (Apply the nonnegative-continuous-with-zero-average
principle to `M - f`.) -/
private lemma eqOn_ball_of_le_of_setAverage_eq {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)} {r M : ℝ} (hr : 0 < r)
    (hfcont : ContinuousOn f (Metric.closedBall x r))
    (hle : ∀ y ∈ Metric.ball x r, f y ≤ M)
    (havg : ⨍ y in Metric.ball x r, f y = M) :
    ∀ y ∈ Metric.ball x r, f y = M := by
  have hfin : (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball x r) ≠ ⊤ := by
    have hK : IsCompact (Metric.closedBall x r) := isCompact_closedBall x r
    exact (lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall) hK.measure_lt_top).ne
  have hpos : (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball x r) ≠ 0 :=
    (measure_ball_pos volume x hr).ne'
  have hfint : IntegrableOn f (Metric.ball x r) :=
    (hfcont.integrableOn_compact (isCompact_closedBall x r)).mono_set Metric.ball_subset_closedBall
  have hcint : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => M) (Metric.ball x r) :=
    integrableOn_const hfin (by simp)
  have hgavg : ⨍ y in Metric.ball x r, (M - f y) = 0 := by
    rw [Commons.Analysis.Harmonic.setAverage_sub_real (f := fun _ => M) (g := f) hcint hfint,
      MeasureTheory.setAverage_const hpos hfin M, havg, sub_self]
  have hgint0 : ∫ y in Metric.ball x r, (M - f y) = 0 := by
    have h2 := MeasureTheory.measure_smul_setAverage (fun y => M - f y)
      (s := Metric.ball x r) hfin
    rw [hgavg, smul_zero] at h2
    exact h2.symm
  have hgcont : ContinuousOn (fun y : EuclideanSpace ℝ (Fin n) => M - f y) (Metric.closedBall x r) :=
    (continuousOn_const (c := M)).sub hfcont
  have hgnnae : 0 ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x r)]
      (fun y => M - f y) :=
    (MeasureTheory.ae_restrict_iff' Metric.isOpen_ball.measurableSet).mpr
      (Eventually.of_forall (fun y hy => sub_nonneg.mpr (hle y hy)))
  have hgint : Integrable (fun y => M - f y)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.ball x r)) :=
    (hgcont.integrableOn_compact (isCompact_closedBall x r)).mono_set Metric.ball_subset_closedBall
  have hge : (fun y => M - f y) =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
      (Metric.ball x r)] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hgnnae hgint).mp hgint0
  have hgz : Set.EqOn (fun y => M - f y) 0 (Metric.ball x r) :=
    Measure.eqOn_open_of_ae_eq hge Metric.isOpen_ball
      (hgcont.mono Metric.ball_subset_closedBall) continuousOn_const
  intro y hy
  have hzero : M - f y = 0 := hgz hy
  linarith

theorem le_of_subMVP_closedBall {n : ℕ} (hn : 0 < n) {c : EuclideanSpace ℝ (Fin n)} {R A : ℝ} (hR : 0 < R)
    {w : EuclideanSpace ℝ (Fin n) → ℝ} (hwc : ContinuousOn w (Metric.closedBall c R))
    (hsub : ∀ x ∈ Metric.ball c R, ∀ r : ℝ, 0 < r → Metric.closedBall x r ⊆ Metric.ball c R →
      w x ≤ ⨍ y in Metric.ball x r, w y)
    (hbd : ∀ y ∈ Metric.sphere c R, w y ≤ A) :
    ∀ x ∈ Metric.closedBall c R, w x ≤ A := by
  obtain ⟨x0, hx0mem, hx0max⟩ :=
    (isCompact_closedBall c R).exists_isMaxOn ⟨c, Metric.mem_closedBall_self hR.le⟩ hwc
  have hMA : w x0 ≤ A := by
    by_contra hcon
    have hlt : A < w x0 := lt_of_not_ge hcon
    have hx0ball : x0 ∈ Metric.ball c R := by
      rw [Metric.mem_ball]
      have hle : dist x0 c ≤ R := Metric.mem_closedBall.mp hx0mem
      have hne : dist x0 c ≠ R := by
        intro heq
        exact absurd (hbd x0 (Metric.mem_sphere.mpr heq)) (not_le.mpr hlt)
      exact lt_of_le_of_ne hle hne
    have hball_eq : ∀ y ∈ Metric.ball c R, w y = w x0 := by
      let S : Set (EuclideanSpace ℝ (Fin n)) := {z | z ∈ Metric.ball c R ∧ w z = w x0}
      have hS_open : IsOpen S := by
        rw [Metric.isOpen_iff]
        intro z hzS
        rcases hzS with ⟨hzball, hzM⟩
        have hzd : dist z c < R := Metric.mem_ball.mp hzball
        refine ⟨(R - dist z c) / 2, by linarith, ?_⟩
        intro y hy
        have hyc : y ∈ Metric.ball c R :=
          (Metric.ball_subset_closedBall.trans (closedBall_subset_ball_of_lt hzd)) hy
        refine ⟨hyc, ?_⟩
        have hδ : 0 < (R - dist z c) / 2 := by linarith
        have hclosed : Metric.closedBall z ((R - dist z c) / 2) ⊆ Metric.ball c R :=
          closedBall_subset_ball_of_lt hzd
        have hfcont : ContinuousOn w (Metric.closedBall z ((R - dist z c) / 2)) :=
          hwc.mono (hclosed.trans Metric.ball_subset_closedBall)
        have hleM : ∀ y ∈ Metric.ball z ((R - dist z c) / 2), w y ≤ w x0 := fun y hy =>
          hx0max (Metric.ball_subset_closedBall
            ((Metric.ball_subset_closedBall.trans hclosed) hy))
        have hballcR : Metric.ball z ((R - dist z c) / 2) ⊆ Metric.ball c R :=
          Metric.ball_subset_closedBall.trans hclosed
        have hfin : (volume : Measure (EuclideanSpace ℝ (Fin n)))
            (Metric.ball z ((R - dist z c) / 2)) ≠ ⊤ := by
          have hK : IsCompact (Metric.closedBall z ((R - dist z c) / 2)) :=
            isCompact_closedBall z _
          exact (lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
            hK.measure_lt_top).ne
        have hfi : IntegrableOn w (Metric.ball z ((R - dist z c) / 2)) :=
          (hfcont.integrableOn_compact (isCompact_closedBall z _)).mono_set
            Metric.ball_subset_closedBall
        have hci : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => w x0)
            (Metric.ball z ((R - dist z c) / 2)) := integrableOn_const hfin (by simp)
        have havg_le : ⨍ y in Metric.ball z ((R - dist z c) / 2), w y ≤ w x0 := by
          have h := setAverage_mono' hfi hci Metric.isOpen_ball.measurableSet
            (fun y hy => hleM y hy)
          have hc : ⨍ y in Metric.ball z ((R - dist z c) / 2), (fun _ => w x0) y = w x0 :=
            MeasureTheory.setAverage_const (measure_ball_pos volume z hδ).ne' hfin (w x0)
          rwa [hc] at h
        have hle_avg : w x0 ≤ ⨍ y in Metric.ball z ((R - dist z c) / 2), w y := by
          rw [← hzM]
          exact hsub z hzball _ hδ hclosed
        have havg : ⨍ y in Metric.ball z ((R - dist z c) / 2), w y = w x0 :=
          le_antisymm havg_le hle_avg
        exact eqOn_ball_of_le_of_setAverage_eq hδ hfcont hleM havg y hy
      have hT_open : IsOpen (Metric.ball c R \ S) := by
        rw [Metric.isOpen_iff]
        intro z hzT
        rcases hzT with ⟨hzball, hznotS⟩
        have hzM : w z ≠ w x0 := by
          intro heq
          exact hznotS ⟨hzball, heq⟩
        have hzlt : w z < w x0 := lt_of_le_of_ne
          (hx0max (Metric.ball_subset_closedBall hzball)) hzM
        have hnbhd : Metric.closedBall c R ∈ 𝓝 z := by
          rcases Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hzball) with ⟨ε, hε, hsub⟩
          exact mem_of_superset (Metric.ball_mem_nhds z hε)
            (hsub.trans Metric.ball_subset_closedBall)
        have hcontAt : ContinuousAt w z := hwc.continuousAt hnbhd
        have hevent : ∀ᶠ y in 𝓝 z, w y < w x0 :=
          ContinuousAt.eventually_lt hcontAt continuousAt_const hzlt
        rcases Metric.eventually_nhds_iff.mp hevent with ⟨ε₂, hε₂pos, hε₂⟩
        rcases Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hzball) with ⟨ε₁, hε₁pos, hε₁⟩
        refine ⟨min ε₁ ε₂, lt_min hε₁pos hε₂pos, ?_⟩
        intro y hy
        have hy₁ : y ∈ Metric.ball z ε₁ := (Metric.ball_subset_ball (min_le_left ε₁ ε₂)) hy
        have hy₂ : y ∈ Metric.ball z ε₂ := (Metric.ball_subset_ball (min_le_right ε₁ ε₂)) hy
        exact ⟨hε₁ hy₁, fun hyS => (ne_of_lt (hε₂ hy₂)) hyS.2⟩
      have hdisj : Disjoint S (Metric.ball c R \ S) := by
        rw [Set.disjoint_left]
        intro z hzS hzT
        exact hzT.2 hzS
      have hcover : Metric.ball c R ⊆ S ∪ (Metric.ball c R \ S) := by
        intro z hz
        by_cases hzS : z ∈ S
        · exact Or.inl hzS
        · exact Or.inr ⟨hz, hzS⟩
      have hnonempty : (Metric.ball c R ∩ S).Nonempty := ⟨x0, hx0ball, hx0ball, rfl⟩
      have hsubS : Metric.ball c R ⊆ S :=
        IsPreconnected.subset_left_of_subset_union hS_open hT_open hdisj hcover hnonempty
          isPreconnected_ball
      intro y hy
      exact (hsubS hy).2
    have hclosed_eq : ∀ y ∈ Metric.closedBall c R, w y = w x0 := by
      have hSclosed : IsClosed (Metric.closedBall c R ∩ w ⁻¹' {w x0}) :=
        hwc.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
      have hball_sub : Metric.ball c R ⊆ Metric.closedBall c R ∩ w ⁻¹' {w x0} := by
        intro y hy
        exact ⟨Metric.ball_subset_closedBall hy, Set.mem_singleton_iff.mpr (hball_eq y hy)⟩
      have hcl : closure (Metric.ball c R) ⊆ Metric.closedBall c R ∩ w ⁻¹' {w x0} :=
        closure_minimal hball_sub hSclosed
      rw [closure_ball c hR.ne'] at hcl
      intro y hy
      exact Set.mem_singleton_iff.mp (hcl hy).2
    obtain ⟨y0, hy0⟩ : ∃ y0, y0 ∈ Metric.sphere c R := by
      refine ⟨c + R • EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ), ?_⟩
      rw [Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left]
      rw [norm_smul, PiLp.norm_single 2 (fun _ : Fin n => ℝ) ⟨0, hn⟩ (1:ℝ), Real.norm_eq_abs, abs_of_nonneg hR.le]
      simp
    have hfin_le : w x0 ≤ A := by
      rw [← hclosed_eq y0 (Metric.sphere_subset_closedBall hy0)]
      exact hbd y0 hy0
    exact absurd hfin_le (not_le.mpr hlt)
  intro x hx
  exact le_trans (hx0max hx) hMA

end Commons.Analysis.Harmonic
