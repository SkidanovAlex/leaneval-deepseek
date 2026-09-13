import Mathlib
import Submission.Commons.Analysis.MeasureTheory.polar_integral_prod
import Submission.Commons.Analysis.MeasureTheory.integral_radial_mul_homogeneous
import Submission.Commons.Measure.Integral.integral_ball_transfer_small_radius

noncomputable section
open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

namespace Commons.Analysis.Harmonic

set_option maxHeartbeats 1600000

/-- Integrability transfers through the polar homeomorphism: an integrable `F` on
`EuclideanSpace ℝ (Fin n)` gives an integrable function `(θ, r) ↦ F (r • θ)` on the
product of the unit sphere and the positive ray. -/
private lemma integrable_polar_comp {n : ℕ} [Nonempty (Fin n)]
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : Integrable F volume) :
    Integrable (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0:ℝ) =>
        F (p.2.1 • (p.1 : EuclideanSpace ℝ (Fin n))))
      ((volume.toSphere).prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1))) := by
  let hh : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) ≃ₜ
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0 : ℝ)) :=
    homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin n))
  have hmp : MeasurePreserving hh
      (volume.comap (Subtype.val : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) →
        EuclideanSpace ℝ (Fin n)))
      ((volume.toSphere).prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1))) := by
    simpa [hh] using (Measure.measurePreserving_homeomorphUnitSphereProd
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))))
  rw [← (hmp.integrable_comp_emb hh.measurableEmbedding
    (g := fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0:ℝ) =>
        F (p.2.1 • (p.1 : EuclideanSpace ℝ (Fin n)))))]
  have hgh : ∀ x : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))),
      F (((hh x).2 : Set.Ioi (0:ℝ)).1 • (((hh x).1 :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
          EuclideanSpace ℝ (Fin n))) = F (x : EuclideanSpace ℝ (Fin n)) := by
    intro x
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
      exact hF
    exact (integrableOn_iff_comap_subtypeVal
      (measurableSet_singleton (0 : EuclideanSpace ℝ (Fin n))).compl).mp hFo
  exact hgval.congr (ae_of_all _ (fun x => (hgh x).symm))

/-- **Radial (polar-coordinate) decomposition of a ball integral.**
For a function integrable on the ball of radius `R` about the origin,
`∫_{B(0,R)} F = ∫_{(0,R)} r^{n-1} (∫_{‖θ‖=1} F (r θ) dθ) dr`. -/
private lemma integral_ball_zero_eq_integral_sphere_radial {n : ℕ} [Nonempty (Fin n)]
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {R : ℝ} (hR : 0 < R)
    (hF : IntegrableOn F (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) volume) :
    (∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R, F y)
      = ∫ r in Set.Ioo (0:ℝ) R, r ^ (n - 1) *
          (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            F (r • (θ : EuclideanSpace ℝ (Fin n))) ∂volume.toSphere) := by
  classical
  set Find : EuclideanSpace ℝ (Fin n) → ℝ :=
    (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R).indicator F with hFinddef
  have hFind : Integrable Find volume := by
    rw [hFinddef]
    exact (integrable_indicator_iff measurableSet_ball).mpr hF
  have hGint : Integrable
      (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0:ℝ) =>
        Find (p.2.1 • (p.1 : EuclideanSpace ℝ (Fin n))))
      ((volume.toSphere).prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1))) :=
    integrable_polar_comp hFind
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hinner : ∀ r : Set.Ioi (0:ℝ),
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          Find (r.1 • (θ : EuclideanSpace ℝ (Fin n))) ∂volume.toSphere)
        = (Set.Ioo (0:ℝ) R).indicator
            (fun x : ℝ => ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              F (x • (θ : EuclideanSpace ℝ (Fin n))) ∂volume.toSphere) r.1 := by
    intro r
    have hr : (0:ℝ) < r.1 := r.2
    have hmem : r.1 ∈ Set.Ioo (0:ℝ) R ↔ r.1 < R := ⟨fun h => h.2, fun h => ⟨hr, h⟩⟩
    by_cases hlt : r.1 < R
    · rw [Set.indicator_of_mem (hmem.mpr hlt)]
      apply integral_congr_ae
      filter_upwards with θ
      have hball : r.1 • (θ : EuclideanSpace ℝ (Fin n)) ∈
          Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := by
        rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
          (mem_sphere_zero_iff_norm).mp θ.2, mul_one]
        exact hlt
      rw [hFinddef]
      simp only [Set.indicator_of_mem hball]
    · rw [Set.indicator_of_notMem (fun h => hlt (hmem.mp h))]
      have : (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          Find (r.1 • (θ : EuclideanSpace ℝ (Fin n))) ∂volume.toSphere)
          = ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, (0:ℝ)
              ∂volume.toSphere := by
        apply integral_congr_ae
        filter_upwards with θ
        have hnot : r.1 • (θ : EuclideanSpace ℝ (Fin n)) ∉
            Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := by
          rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
            (mem_sphere_zero_iff_norm).mp θ.2, mul_one]
          exact not_lt.mpr (le_of_not_gt hlt)
        rw [hFinddef]
        simp only [Set.indicator_of_notMem hnot]
      rw [this, integral_zero]
  have h1 : (∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R, F y) = ∫ y, Find y := by
    rw [hFinddef, integral_indicator measurableSet_ball]
  have h2 : (∫ y, Find y)
      = ∫ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0:ℝ),
          Find (p.2.1 • (p.1 : EuclideanSpace ℝ (Fin n)))
          ∂((volume.toSphere).prod
            (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1))) :=
    Commons.Analysis.MeasureTheory.polar_integral_prod (EuclideanSpace ℝ (Fin n)) Find
  have h3 : (∫ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0:ℝ),
        Find (p.2.1 • (p.1 : EuclideanSpace ℝ (Fin n)))
        ∂((volume.toSphere).prod
          (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1))))
      = ∫ r : Set.Ioi (0:ℝ),
          ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            Find (r.1 • (θ : EuclideanSpace ℝ (Fin n))) ∂volume.toSphere
          ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)) :=
    integral_prod_symm _ hGint
  have h4 : (∫ r : Set.Ioi (0:ℝ),
        ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          Find (r.1 • (θ : EuclideanSpace ℝ (Fin n))) ∂volume.toSphere
        ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)))
      = ∫ r : Set.Ioi (0:ℝ),
          (Set.Ioo (0:ℝ) R).indicator
            (fun x : ℝ => ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              F (x • (θ : EuclideanSpace ℝ (Fin n))) ∂volume.toSphere) r.1
          ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)) := by
    apply integral_congr_ae
    filter_upwards with r
    exact hinner r
  have h5 : (∫ r : Set.Ioi (0:ℝ),
          (Set.Ioo (0:ℝ) R).indicator
            (fun x : ℝ => ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              F (x • (θ : EuclideanSpace ℝ (Fin n))) ∂volume.toSphere) r.1
          ∂(Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)))
      = ∫ r in Set.Ioi (0:ℝ), r ^ (n - 1) *
          (Set.Ioo (0:ℝ) R).indicator
            (fun x : ℝ => ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              F (x • (θ : EuclideanSpace ℝ (Fin n))) ∂volume.toSphere) r := by
    rw [Commons.Analysis.MeasureTheory.integral_volumeIoiPow_eq_integral_Ioi_mul_pow
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)]
    rw [hdim]
  have h6 : (∫ r in Set.Ioi (0:ℝ), r ^ (n - 1) *
          (Set.Ioo (0:ℝ) R).indicator
            (fun x : ℝ => ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              F (x • (θ : EuclideanSpace ℝ (Fin n))) ∂volume.toSphere) r)
      = ∫ r in Set.Ioo (0:ℝ) R, r ^ (n - 1) *
          (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            F (r • (θ : EuclideanSpace ℝ (Fin n))) ∂volume.toSphere) := by
    have hc : (∫ r in Set.Ioi (0:ℝ), r ^ (n - 1) *
          (Set.Ioo (0:ℝ) R).indicator
            (fun x : ℝ => ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              F (x • (θ : EuclideanSpace ℝ (Fin n))) ∂volume.toSphere) r)
        = ∫ r in Set.Ioi (0:ℝ),
            (Set.Ioo (0:ℝ) R).indicator
              (fun x : ℝ => x ^ (n - 1) *
                (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
                  F (x • (θ : EuclideanSpace ℝ (Fin n))) ∂volume.toSphere)) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r _
      by_cases hmem : r ∈ Set.Ioo (0:ℝ) R
      · simp only [Set.indicator_of_mem hmem]
      · simp only [Set.indicator_of_notMem hmem, mul_zero]
    rw [hc, setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr Set.Ioo_subset_Ioi_self]
  rw [h1, h2, h3, h4, h5, h6]

/-- A ball has finite Lebesgue measure. -/
private lemma ball_measure_ne_top {n : ℕ} (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (Metric.ball c r) ≠ ∞ :=
  ne_top_of_le_ne_top (isCompact_closedBall c r).measure_lt_top.ne
    (measure_mono Metric.ball_subset_closedBall)

/-- The Lebesgue measure of a ball of positive radius is positive. -/
private lemma ball_measureReal_pos {n : ℕ} (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    0 < (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball c r) := by
  have hpos : 0 < volume (Metric.ball c r) :=
    MeasureTheory.Measure.measure_pos_of_nonempty_interior volume
      ⟨c, by rw [Metric.isOpen_ball.interior_eq]; exact Metric.mem_ball_self hr⟩
  have hne : volume.real (Metric.ball c r) ≠ 0 :=
    (MeasureTheory.measureReal_ne_zero_iff (ball_measure_ne_top c r)).mpr hpos.ne'
  exact lt_of_le_of_ne MeasureTheory.measureReal_nonneg hne.symm

/-- If `∫ g ≤ ∫ f` and `g` is integrable then `0 ≤ ∫ (f - g)`.  No integrability of `f` is
required: when `f` is not integrable the integral of `f - g` is `0` by definition. -/
private lemma integral_sub_nonneg_of_le_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hg : Integrable g μ) (h : ∫ x, g x ∂μ ≤ ∫ x, f x ∂μ) :
    0 ≤ ∫ x, (f x - g x) ∂μ := by
  by_cases hf : Integrable f μ
  · rw [integral_sub hf hg]; linarith
  · have hfg : ¬ Integrable (fun x => f x - g x) μ := by
      intro hsub
      exact hf ((hsub.add hg).congr (Filter.Eventually.of_forall (fun x => by
        simp only [Pi.add_apply, sub_add_cancel])))
    rw [integral_undef hfg]

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace in
theorem le_setAverage_ball_of_forall_sphere {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    (hu : IntegrableOn u (ball c R) volume)
    (h : ∀ r : ℝ, 0 < r → r ≤ R →
      (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, (1 : ℝ)
          ∂MeasureTheory.volume.toSphere) * u c ≤
      ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        u (c + r • (θ : EuclideanSpace ℝ (Fin n))) ∂MeasureTheory.volume.toSphere) :
    u c ≤ ⨍ y in ball c R, u y := by
  rcases isEmpty_or_nonempty (Fin n) with hem | hne
  · -- degenerate case: the space is a single point
    haveI : IsEmpty (Fin n) := hem
    haveI : Subsingleton (EuclideanSpace ℝ (Fin n)) := inferInstance
    have hball : Metric.ball c R = Set.univ := by
      ext y
      rw [Metric.mem_ball]
      constructor
      · intro _; trivial
      · intro _
        rw [dist_eq_norm]
        have : y - c = 0 := Subsingleton.elim _ _
        rw [this, norm_zero]; exact hR
    have hvol0 : (volume : Measure (EuclideanSpace ℝ (Fin n))) Set.univ ≠ 0 := by
      rw [volume_euclideanSpace_eq_dirac (Fin n)]; simp
    have hvoltop : (volume : Measure (EuclideanSpace ℝ (Fin n))) Set.univ ≠ ⊤ := by
      rw [volume_euclideanSpace_eq_dirac (Fin n)]; simp
    have h1 : ⨍ y in Metric.ball c R, u y
        = ⨍ y in Metric.ball c R, (fun _ : EuclideanSpace ℝ (Fin n) => u c) y := by
      apply setAverage_congr_fun measurableSet_ball
      exact Filter.Eventually.of_forall (fun y _ => congrArg u (Subsingleton.elim y c))
    rw [h1, hball]
    exact le_of_eq (setAverage_const hvol0 hvoltop (u c)).symm
  · haveI := hne
    set w : EuclideanSpace ℝ (Fin n) → ℝ := fun y => u (c + y) - u c with hwdef
    -- integrability of `y ↦ u (c + y)` on the ball at the origin
    have hucomp : IntegrableOn (fun y : EuclideanSpace ℝ (Fin n) => u (c + y))
        (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) volume := by
      have hmp : MeasurePreserving (MeasurableEquiv.addLeft c)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) volume := by
        refine ⟨(MeasurableEquiv.addLeft c).measurable, ?_⟩
        simpa only [MeasurableEquiv.coe_addLeft] using
          (Measure.IsAddLeftInvariant.map_add_left_eq_self
            (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) c)
      have hh := (MeasurePreserving.integrableOn_comp_preimage hmp
        (MeasurableEquiv.addLeft c).measurableEmbedding (f := u) (s := Metric.ball c R)).mpr hu
      have hpre : (MeasurableEquiv.addLeft c) ⁻¹' (Metric.ball c R) =
          Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := by
        ext y
        simp only [Set.mem_preimage, MeasurableEquiv.coe_addLeft, Metric.mem_ball, dist_eq_norm,
          add_sub_cancel_left, sub_zero]
      rw [hpre] at hh
      simpa only [Function.comp_def, MeasurableEquiv.coe_addLeft] using hh
    have hw_int : IntegrableOn w (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) volume := by
      rw [hwdef]
      exact hucomp.sub (integrableOn_const (C := u c)
        (ball_measure_ne_top (0 : EuclideanSpace ℝ (Fin n)) R) (by simp))
    -- the sphere average of `w` is nonnegative
    have hAW_nonneg : ∀ r : ℝ, 0 < r → r ≤ R →
        0 ≤ ∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            w (r • (θ : EuclideanSpace ℝ (Fin n))) ∂volume.toSphere := by
      intro r hr hrR
      have hgint : Integrable (fun _ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => u c)
          volume.toSphere := integrable_const (u c)
      have hgeq : (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, u c ∂volume.toSphere)
          = (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, (1:ℝ)
              ∂volume.toSphere) * u c := by
        rw [integral_const, integral_const, smul_eq_mul, smul_eq_mul, mul_one]
      simp only [hwdef]
      exact integral_sub_nonneg_of_le_integral hgint (by rw [hgeq]; exact h r hr hrR)
    -- hence the ball integral of `w` is nonnegative
    have hnonneg_int : 0 ≤ ∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R, w y := by
      rw [integral_ball_zero_eq_integral_sphere_radial (n := n) (F := w) hR hw_int]
      apply setIntegral_nonneg measurableSet_Ioo
      intro r hr
      exact mul_nonneg (pow_nonneg hr.1.le _) (hAW_nonneg r hr.1 hr.2.le)
    -- translate back to the ball at `c`
    have htrans : (∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R, w y)
        = ∫ y in Metric.ball c R, (u y - u c) := by
      rw [← Commons.Measure.Integral.setIntegral_ball_sub_translate w c R]
      apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
      intro x _
      rw [hwdef]
      simp only [add_sub_cancel]
    have hkey : (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball c R) * u c
        ≤ ∫ y in Metric.ball c R, u y := by
      have huc_int : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => u c)
          (Metric.ball c R) volume :=
        integrableOn_const (C := u c) (ball_measure_ne_top c R) (by simp)
      have hsplit : (∫ y in Metric.ball c R, (u y - u c))
          = (∫ y in Metric.ball c R, u y) - (volume.real (Metric.ball c R)) * u c := by
        rw [integral_sub hu huc_int, setIntegral_const (u c), smul_eq_mul]
      have hh := hnonneg_int
      rw [htrans, hsplit] at hh
      linarith
    rw [setAverage_eq, smul_eq_mul]
    have hV : 0 < (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball c R) :=
      ball_measureReal_pos c hR
    calc u c = ((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball c R))⁻¹ *
            (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball c R)) * u c) := by
          rw [← mul_assoc, inv_mul_cancel₀ hV.ne', one_mul]
      _ ≤ ((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball c R))⁻¹ *
            ∫ y in Metric.ball c R, u y :=
          mul_le_mul_of_nonneg_left hkey (inv_nonneg.mpr hV.le)

end Commons.Analysis.Harmonic
