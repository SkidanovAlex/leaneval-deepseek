import Mathlib
import Submission.Commons.Analysis.Harmonic.le_setAverage_ball_of_laplacian_nonneg_of_isOpen
import Submission.Commons.Analysis.MeasureTheory.polar_integral
import Submission.Commons.Analysis.MeasureTheory.integral_radial_mul_homogeneous
import Submission.Commons.Analysis.MeasureTheory.continuous_integrable_sphere

noncomputable section
open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

set_option linter.style.haveILetI false

namespace Commons.Analysis.Harmonic

/-- **Translation of a ball integral.** -/
private lemma integral_ball_add_left {n : ℕ} (c : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (H : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ y in Metric.ball c r, H y
      = ∫ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, H (c + w) := by
  have hiff : ∀ w : EuclideanSpace ℝ (Fin n),
      c + w ∈ Metric.ball c r ↔ w ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := by
    intro w
    rw [Metric.mem_ball, Metric.mem_ball, dist_eq_norm, dist_eq_norm]
    rw [add_sub_cancel_left, sub_zero]
  have hcomp : ∀ w : EuclideanSpace ℝ (Fin n),
      (Metric.ball c r).indicator H (c + w)
        = (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r).indicator (fun w => H (c + w)) w := by
    intro w
    by_cases hw : w ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
    · simp only [Set.indicator_of_mem, hw, (hiff w).mpr hw]
    · simp only [Set.indicator_of_notMem, hw, not_false_eq_true, (hiff w).not.mpr hw]
  rw [← integral_indicator measurableSet_ball,
    ← integral_indicator (s := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)
      (f := fun w => H (c + w)) measurableSet_ball]
  calc ∫ y, (Metric.ball c r).indicator H y
      = ∫ w, (Metric.ball c r).indicator H (c + w) :=
        (integral_add_left_eq_self (fun y => (Metric.ball c r).indicator H y) c).symm
    _ = ∫ w, (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r).indicator
          (fun w => H (c + w)) w := by
        apply integral_congr_ae
        filter_upwards with w
        exact hcomp w

/-- **Polar-coordinate formula for a ball integral.** -/
private theorem integral_ball_eq_integral_sphere_radial {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (G : EuclideanSpace ℝ (Fin n) → ℝ) (hG : ContinuousOn G (closedBall 0 r)) :
    (∫ u in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, G u)
      = ∫ t in (0:ℝ)..r, t ^ (n - 1) *
          (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              G (t • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere) := by
  classical
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
    infer_instance
  set F : EuclideanSpace ℝ (Fin n) → ℝ :=
    (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r).indicator G with hFdef
  have hGint : IntegrableOn G (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) volume :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) r)
      hG).mono_set ball_subset_closedBall
  have hFint : Integrable F volume := by
    rw [hFdef]
    rw [integrable_indicator_iff measurableSet_ball]
    exact hGint
  have hpolar := Commons.Analysis.MeasureTheory.polar_integral_prod
    (EuclideanSpace ℝ (Fin n)) F
  let g : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    fun p => F (p.2.1 • (p.1 : EuclideanSpace ℝ (Fin n)))
  have hgi : Integrable g ((MeasureTheory.volume.toSphere).prod
      (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1))) := by
    let hh : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) ≃ₜ
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0 : ℝ)) :=
      homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin n))
    have hmp : MeasurePreserving (hh) (volume.comap
        (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) → EuclideanSpace ℝ (Fin n)))
        ((volume.toSphere).prod (Measure.volumeIoiPow
          (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1))) := by
      simpa [hh] using (Measure.measurePreserving_homeomorphUnitSphereProd
        (μ := volume) (E := EuclideanSpace ℝ (Fin n)))
    rw [← (hmp.integrable_comp_emb hh.measurableEmbedding (g := g))]
    have hgh : ∀ x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))),
        g (hh x) = F (x : EuclideanSpace ℝ (Fin n)) := by
      intro x
      change F (((hh x).2 : Set.Ioi (0:ℝ)).1 • ((hh x).1 : EuclideanSpace ℝ (Fin n))) = F (x : _)
      congr 1
      calc ((hh x).2 : Set.Ioi (0 : ℝ)).1 • ((hh x).1 : EuclideanSpace ℝ (Fin n))
          = ((hh.symm (hh x) : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) :
              EuclideanSpace ℝ (Fin n)) := by
            rw [homeomorphUnitSphereProd_symm_apply_coe]
        _ = (x : EuclideanSpace ℝ (Fin n)) := by
            congr 1
            exact hh.left_inv x
    have hgval : Integrable (fun x : ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ : Set _) =>
        F (x : EuclideanSpace ℝ (Fin n)))
        (volume.comap (Subtype.val : ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ : Set _) →
          EuclideanSpace ℝ (Fin n))) := by
      have hFo : IntegrableOn F ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ : Set _) volume := by
        dsimp [MeasureTheory.IntegrableOn]
        rw [restrict_compl_singleton (0 : EuclideanSpace ℝ (Fin n))]
        exact hFint
      exact (integrableOn_iff_comap_subtypeVal
        (measurableSet_singleton (0 : EuclideanSpace ℝ (Fin n))).compl).mp hFo
    exact hgval.congr (ae_of_all _ (fun x => (hgh x).symm))
  have hmem : ∀ (t : Set.Ioi (0:ℝ)) (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
      (t.1 • (θ : EuclideanSpace ℝ (Fin n))) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
        ↔ (t:ℝ) < r := by
    intro t θ
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_pos t.2, mem_sphere_zero_iff_norm.mp θ.2, mul_one]
  have hinner : ∀ t : Set.Ioi (0:ℝ),
      ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, g (θ, t)
        ∂MeasureTheory.volume.toSphere =
      (if (t:ℝ) < r then (1:ℝ) else 0) *
        ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          G (t.1 • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere := by
    intro t
    have hpt : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        g (θ,t) = (if (t:ℝ) < r then G (t.1 • (θ : EuclideanSpace ℝ (Fin n))) else 0) := by
      intro θ
      simp only [g, hFdef, Set.indicator_apply]
      rw [if_congr (hmem t θ) rfl rfl]
    rw [show (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, g (θ, t)
          ∂MeasureTheory.volume.toSphere)
        = ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            (if (t:ℝ) < r then G (t.1 • (θ : EuclideanSpace ℝ (Fin n))) else 0)
            ∂MeasureTheory.volume.toSphere from by
        apply integral_congr_ae
        filter_upwards with θ
        exact hpt θ]
    by_cases hc : (t:ℝ) < r
    · simp only [if_pos hc, one_mul]
    · simp only [if_neg hc, integral_zero, zero_mul]
  have hstep5 : (∫ t : Set.Ioi (0:ℝ),
        (if (t:ℝ) < r then (1:ℝ) else 0) *
          (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            G (t.1 • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere)
        ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)))
      = ∫ t in (0:ℝ)..r, t ^ (n - 1) *
          (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            G (t • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere) := by
    rw [Commons.Analysis.MeasureTheory.integral_volumeIoiPow_eq_integral_Ioi_mul_pow
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)
      (fun t : ℝ => (if t < r then (1:ℝ) else 0) *
        (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          G (t • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere))]
    rw [finrank_euclideanSpace_fin]
    have hcongr : Set.EqOn
        (fun t : ℝ => t ^ (n - 1) * ((if t < r then (1:ℝ) else 0) *
          (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            G (t • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere)))
        (fun t : ℝ => (Set.Ioo (0:ℝ) r).indicator
          (fun t => t ^ (n - 1) *
            (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              G (t • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere)) t)
        (Set.Ioi 0) := by
      intro t ht
      change t ^ (n - 1) * ((if t < r then (1:ℝ) else 0) *
          (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            G (t • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere)) =
        (Set.Ioo (0:ℝ) r).indicator
          (fun t => t ^ (n - 1) *
            (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              G (t • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere)) t
      rw [mem_Ioi] at ht
      by_cases htr : t < r
      · rw [if_pos htr, Set.indicator_of_mem (show t ∈ Set.Ioo (0:ℝ) r from ⟨ht, htr⟩)]
        ring
      · rw [if_neg htr]
        have hnot : t ∉ Set.Ioo (0:ℝ) r := fun h => htr h.2
        rw [Set.indicator_of_notMem hnot]
        ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
    rw [setIntegral_indicator measurableSet_Ioo]
    rw [inter_eq_right.mpr Set.Ioo_subset_Ioi_self]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
  calc (∫ u in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, G u)
      = ∫ u, F u := by
        rw [hFdef]
        exact (integral_indicator measurableSet_ball).symm
    _ = ∫ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0:ℝ), g p
          ∂((MeasureTheory.volume.toSphere).prod
            (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1))) := by
        simpa [g] using hpolar
    _ = ∫ t : Set.Ioi (0:ℝ),
          ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, g (θ, t)
            ∂MeasureTheory.volume.toSphere
          ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)) :=
        integral_prod_symm g hgi
    _ = ∫ t : Set.Ioi (0:ℝ),
          (if (t:ℝ) < r then (1:ℝ) else 0) *
            (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              G (t.1 • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)) := by
        apply integral_congr_ae
        filter_upwards with t
        exact hinner t
    _ = _ := hstep5

/-- **Polar-coordinate formula for a ball integral, general centre.** -/
private theorem integral_ball_center_eq_integral_sphere_radial {n : ℕ} (hn : 0 < n)
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (G : EuclideanSpace ℝ (Fin n) → ℝ) (hG : ContinuousOn G (closedBall c r)) :
    (∫ y in Metric.ball c r, G y)
      = ∫ t in (0:ℝ)..r, t ^ (n - 1) *
          (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              G (c + t • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere) := by
  have hG' : ContinuousOn (fun u : EuclideanSpace ℝ (Fin n) => G (c + u))
      (closedBall (0 : EuclideanSpace ℝ (Fin n)) r) := by
    have hc : Continuous (fun u : EuclideanSpace ℝ (Fin n) => c + u) :=
      continuous_const.add continuous_id
    have hmaps : MapsTo (fun u : EuclideanSpace ℝ (Fin n) => c + u)
        (closedBall (0 : EuclideanSpace ℝ (Fin n)) r) (closedBall c r) := by
      intro u hu
      rw [mem_closedBall, dist_eq_norm] at hu ⊢
      simpa using hu
    exact hG.comp hc.continuousOn hmaps
  have hA := integral_ball_eq_integral_sphere_radial hn hr (fun u => G (c + u)) hG'
  rw [← integral_ball_add_left c r G] at hA
  simpa using hA

/-- **Continuity of the spherical average.** -/
private theorem continuousOn_sphereAverage {n : ℕ} (hn : 0 < n)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {c : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    (hcont : ContinuousOn h (closedBall c R)) :
    ContinuousOn (fun t : ℝ =>
      ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        h (c + t • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere) (Icc 0 R) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hf : ContinuousOn (Function.uncurry (fun t : ℝ =>
      fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      h (c + t • (θ : EuclideanSpace ℝ (Fin n)))))
      (Set.Icc 0 R ×ˢ (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))) := by
    have hΨcont : Continuous (fun p : ℝ × Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        c + p.1 • (p.2 : EuclideanSpace ℝ (Fin n))) := by fun_prop
    have hmaps : MapsTo (fun p : ℝ × Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        c + p.1 • (p.2 : EuclideanSpace ℝ (Fin n)))
        (Set.Icc 0 R ×ˢ (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)))
        (closedBall c R) := by
      rintro ⟨t, θ⟩ ⟨ht, -⟩
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        mem_sphere_zero_iff_norm.mp θ.2, mul_one]
      exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    have hcomp := hcont.comp hΨcont.continuousOn hmaps
    convert hcomp using 1
    ext p
    simp [Function.uncurry]
  have := continuousOn_integral_of_compact_support
    (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
    (s := Set.Icc 0 R) (k := (Set.univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)))
    isCompact_univ hf (fun p x _ hx => (hx trivial).elim)
  simpa using this

/-- **Ball mean value property, integral form.** -/
private theorem integral_ball_eq_of_harmonic {n : ℕ} (hn : 0 < n)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {c : EuclideanSpace ℝ (Fin n)} {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hrR : r < R)
    (hh : ContDiffOn ℝ 2 h (ball c R))
    (hΔ : ∀ x ∈ ball c R, Laplacian.laplacian h x = 0) :
    (∫ y in ball c r, h y) = (volume.real (ball c r)) * h c := by
  have hsub : closedBall c r ⊆ ball c R := closedBall_subset_ball hrR
  have hle := le_setAverage_ball_of_laplacian_nonneg_of_isOpen isOpen_ball hh
      (fun x hx => by rw [hΔ x hx]) hr hsub
  have hV : 0 < volume.real (ball c r) := by
    rw [MeasureTheory.Measure.real]
    exact ENNReal.toReal_pos (measure_ball_pos volume c hr).ne' (measure_ball_ne_top)
  rw [setAverage_eq, smul_eq_mul] at hle
  have hle' : volume.real (ball c r) * h c ≤ ∫ y in ball c r, h y := by
    have h := mul_le_mul_of_nonneg_left hle hV.le
    rwa [← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul] at h
  have hge := le_setAverage_ball_of_laplacian_nonneg_of_isOpen isOpen_ball hh.neg
      (fun x hx => by
        have hneg : Laplacian.laplacian (fun x : EuclideanSpace ℝ (Fin n) => -h x) x
            = - Laplacian.laplacian h x := by
          have h1 : (fun x : EuclideanSpace ℝ (Fin n) => -h x) = -h := by
            funext x; rfl
          rw [h1]
          exact congrFun (InnerProductSpace.laplacian_neg (f := h)) x
        rw [hneg, hΔ x hx, neg_zero]) hr hsub
  rw [setAverage_eq, smul_eq_mul] at hge
  rw [integral_neg] at hge
  have hge' : (∫ y in ball c r, h y) ≤ volume.real (ball c r) * h c := by
    have h := mul_le_mul_of_nonneg_left hge hV.le
    rw [← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul] at h
    linarith
  linarith

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace in
theorem sphereAverage_harmonic_C2 {n : ℕ} (hn : 0 < n) {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    (hh : ContDiffOn ℝ 2 h (ball c R))
    (hΔ : ∀ x ∈ ball c R, Laplacian.laplacian h x = 0)
    (hcont : ContinuousOn h (closedBall c R)) :
    (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        h (c + R • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere)
      = (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, (1 : ℝ)
          ∂MeasureTheory.volume.toSphere) * h c := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let A : ℝ → ℝ := fun t =>
    ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      h (c + t • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere
  let Area : ℝ := ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      (1 : ℝ) ∂MeasureTheory.volume.toSphere
  have hAcont : ContinuousOn A (Icc 0 R) := continuousOn_sphereAverage hn hR hcont
  have hinner_eq : ∀ t ∈ Set.Icc (0:ℝ) R,
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (h (c + t • (θ : EuclideanSpace ℝ (Fin n))) - h c)
        ∂MeasureTheory.volume.toSphere) = A t - Area * h c := by
    intro t ht
    have hint1 : Integrable (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        h (c + t • (θ : EuclideanSpace ℝ (Fin n)))) MeasureTheory.volume.toSphere := by
      refine Commons.Analysis.MeasureTheory.continuous_integrable_sphere _ ?_
      have hcontc : Continuous (fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          c + t • (θ : EuclideanSpace ℝ (Fin n))) := by fun_prop
      have hmaps : ∀ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          c + t • (θ : EuclideanSpace ℝ (Fin n)) ∈ closedBall c R := by
        intro θ
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          mem_sphere_zero_iff_norm.mp θ.2, mul_one]
        exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      simpa [Function.comp_def] using hcont.comp_continuous hcontc hmaps
    rw [integral_sub hint1 (integrable_const (h c)), integral_const]
    dsimp only [A, Area]
    rw [integral_const]
    simp only [smul_eq_mul, mul_one]
  have hkey : ∀ r : ℝ, 0 < r → r < R →
      ∫ t in (0:ℝ)..r, t ^ (n - 1) * (A t - Area * h c) = 0 := by
    intro r hr hrR
    have hcr : ContinuousOn h (closedBall c r) := hcont.mono (closedBall_subset_closedBall hrR.le)
    have hpol := integral_ball_center_eq_integral_sphere_radial hn hr
      (fun y : EuclideanSpace ℝ (Fin n) => h y - h c) (hcr.sub continuousOn_const)
    have hhint : IntegrableOn h (ball c r) volume :=
      (ContinuousOn.integrableOn_compact (isCompact_closedBall c r) hcr).mono_set
        ball_subset_closedBall
    have hcint : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => h c) (ball c r) volume :=
      integrableOn_const (C := h c) (measure_ball_ne_top)
    have hmvp := integral_ball_eq_of_harmonic hn hR hr hrR hh hΔ
    have hLHS : (∫ y in ball c r, (h y - h c)) = 0 := by
      rw [integral_sub hhint hcint, hmvp, setIntegral_const, smul_eq_mul]
      ring
    have hRHS : (∫ t in (0:ℝ)..r, t ^ (n - 1) *
          (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            (h (c + t • (θ : EuclideanSpace ℝ (Fin n))) - h c)
            ∂MeasureTheory.volume.toSphere))
        = ∫ t in (0:ℝ)..r, t ^ (n - 1) * (A t - Area * h c) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Set.Icc (0:ℝ) R := by
        rw [Set.uIcc_of_le hr.le] at ht
        exact ⟨ht.1, ht.2.trans hrR.le⟩
      dsimp only
      rw [hinner_eq t ht']
    rw [← hRHS, ← hpol]
    exact hLHS
  have hAz : ∀ r ∈ Set.Ioo (0:ℝ) R, A r = Area * h c := by
    intro r hr
    have hψcont : ContinuousOn (fun t : ℝ => t ^ (n - 1) * (A t - Area * h c))
        (Set.uIcc 0 r) := by
      have hA' : ContinuousOn A (Set.uIcc 0 r) := hAcont.mono (by
        intro x hx
        rw [Set.uIcc_of_le hr.1.le] at hx
        exact ⟨hx.1, hx.2.trans hr.2.le⟩)
      exact (continuous_id.continuousOn.pow _).mul (hA'.sub continuousOn_const)
    have hAcAt : ContinuousAt A r := hAcont.continuousAt (Icc_mem_nhds hr.1 hr.2)
    have hψcAt : ContinuousAt (fun t : ℝ => t ^ (n - 1) * (A t - Area * h c)) r :=
      (continuousAt_id.pow _).mul (hAcAt.sub continuousAt_const)
    have hψcontOpen : ContinuousOn (fun t : ℝ => t ^ (n - 1) * (A t - Area * h c))
        (Set.Ioo (0:ℝ) R) :=
      (continuous_id.continuousOn.pow _).mul
        ((hAcont.mono Set.Ioo_subset_Icc_self).sub continuousOn_const)
    have hψmeas : StronglyMeasurableAtFilter
        (fun t : ℝ => t ^ (n - 1) * (A t - Area * h c)) (𝓝 r) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hψcontOpen r hr
    have hψint : IntervalIntegrable (fun t : ℝ => t ^ (n - 1) * (A t - Area * h c))
        volume 0 r := hψcont.intervalIntegrable
    have hFderiv : HasDerivAt
        (fun s => ∫ t in (0:ℝ)..s, t ^ (n - 1) * (A t - Area * h c))
        (r ^ (n - 1) * (A r - Area * h c)) r :=
      intervalIntegral.integral_hasDerivAt_right hψint hψmeas hψcAt
    have hFzero : HasDerivAt
        (fun s => ∫ t in (0:ℝ)..s, t ^ (n - 1) * (A t - Area * h c)) 0 r := by
      have heq : (fun s => ∫ t in (0:ℝ)..s, t ^ (n - 1) * (A t - Area * h c))
          =ᶠ[𝓝 r] (fun _ => (0:ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
        exact hkey s hs.1 hs.2
      exact (hasDerivAt_const (c := (0:ℝ)) (x := r)).congr_of_eventuallyEq heq
    have hzero : 0 = r ^ (n - 1) * (A r - Area * h c) := hFzero.unique hFderiv
    have hrpow : r ^ (n - 1) ≠ 0 := pow_ne_zero _ hr.1.ne'
    have : A r - Area * h c = 0 := (mul_eq_zero.mp hzero.symm).resolve_left hrpow
    exact sub_eq_zero.mp this
  have hAtend : Tendsto A (𝓝[Set.Ioo (0:ℝ) R] R) (𝓝 (Area * h c)) := by
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with r hr'
    exact (hAz r hr').symm
  haveI hneBot : (𝓝[Set.Ioo (0:ℝ) R] R).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (ne_of_lt hR)]
    exact ⟨hR.le, le_refl R⟩
  have hAatR : Tendsto A (𝓝[Set.Ioo (0:ℝ) R] R) (𝓝 (A R)) :=
    ((hAcont.continuousWithinAt ⟨hR.le, le_refl R⟩).mono
      (Set.Ioo_subset_Icc_self)).tendsto
  have hAR : A R = Area * h c := tendsto_nhds_unique hAatR hAtend
  change A R = Area * h c
  exact hAR

end Commons.Analysis.Harmonic
