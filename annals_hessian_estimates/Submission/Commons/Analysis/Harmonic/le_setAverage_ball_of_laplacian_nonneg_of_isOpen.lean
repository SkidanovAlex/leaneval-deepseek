import Mathlib
import Submission.Commons.Analysis.Harmonic.integral_fderiv_sub_eq_half_integral_laplacian

namespace Commons.Analysis.Harmonic

open _root_.MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

noncomputable section

/-- Translation of a ball integral. -/
private lemma integral_ball_add_left {n : ℕ}
    (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) (H : EuclideanSpace ℝ (Fin n) → ℝ) :
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
    · simp only [Set.indicator_of_notMem, hw, not_false_eq_true,
        (hiff w).not.mpr hw]
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

/-- Scaling of a ball integral centred at the origin. -/
private lemma integral_ball_smul_origin {n : ℕ} {s : ℝ} (hs : 0 < s) (r : ℝ)
    (G : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r, G (s • w)
      = (s ^ n)⁻¹ * ∫ u in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (s*r), G u := by
  have h := Measure.setIntegral_comp_smul_of_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) G
    (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) hs
  rw [smul_ball (x := (0 : EuclideanSpace ℝ (Fin n))) hs.ne' r,
    smul_zero, Real.norm_eq_abs, abs_of_pos hs] at h
  rw [h]
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  rw [hfr, smul_eq_mul]

/-- Rescaling the ball in the inner radial integral. -/
private lemma radial_integral_subst {n : ℕ} (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n)) {r s : ℝ} (hs : 0 < s) :
    (∫ y in Metric.ball c r, (fderiv ℝ v (c + s • (y - c))) (y - c))
      = (s ^ (n+1))⁻¹ *
          ∫ u in Metric.ball c (s*r), (fderiv ℝ v u) (u - c) := by
  have h1 : (∫ y in Metric.ball c r, (fderiv ℝ v (c + s • (y - c))) (y - c))
      = s⁻¹ * ∫ y in Metric.ball c r,
          (fderiv ℝ v (c + s • (y - c))) (s • (y - c)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    dsimp only
    rw [map_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  have h2 : (∫ y in Metric.ball c r, (fderiv ℝ v (c + s • (y - c))) (s • (y - c)))
      = ∫ y in Metric.ball c r,
          (fderiv ℝ v (c + s • (y - c))) ((c + s • (y - c)) - c) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    dsimp only
    rw [add_sub_cancel_left]
  have h3 : (∫ y in Metric.ball c r,
          (fderiv ℝ v (c + s • (y - c))) ((c + s • (y - c)) - c))
      = ∫ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          (fderiv ℝ v (c + s • w)) ((c + s • w) - c) := by
    rw [integral_ball_add_left]
    apply setIntegral_congr_fun measurableSet_ball
    intro w hw
    dsimp only
    rw [add_sub_cancel_left]
  have h4 : (∫ w in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r,
          (fderiv ℝ v (c + s • w)) ((c + s • w) - c))
      = (s^n)⁻¹ * ∫ u in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (s*r),
          (fderiv ℝ v (c + u)) ((c + u) - c) := by
    have h := integral_ball_smul_origin (n := n) hs r
      (fun w => (fderiv ℝ v (c + w)) ((c + w) - c))
    simpa using h
  have h5 : (∫ u in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (s*r),
          (fderiv ℝ v (c + u)) ((c + u) - c))
      = ∫ y in Metric.ball c (s*r), (fderiv ℝ v y) (y - c) :=
    (integral_ball_add_left (n := n) c (s*r) (fun y => (fderiv ℝ v y) (y - c))).symm
  rw [h1, h2, h3, h4, h5]
  have : s⁻¹ * (s ^ n)⁻¹ = (s ^ (n+1))⁻¹ := by
    rw [mul_comm s⁻¹ (s ^ n)⁻¹, ← mul_inv, ← pow_succ]
  rw [← this, mul_assoc]

/-- A ball has finite Lebesgue measure. -/
private lemma ball_measure_ne_top {n : ℕ} (c : EuclideanSpace ℝ (Fin n)) {r : ℝ}
    (hr : 0 < r) : volume (Metric.ball c r) ≠ ∞ := by
  have h1 : volume (Metric.ball c r) ≤ volume (Metric.closedBall c r) :=
    measure_mono Metric.ball_subset_closedBall
  have h2 : volume (Metric.closedBall c r) < ∞ := (isCompact_closedBall c r).measure_lt_top
  exact ne_top_of_le_ne_top h2.ne h1

/-- The Lebesgue measure of a ball is positive. -/
private lemma ball_measureReal_pos {n : ℕ} (c : EuclideanSpace ℝ (Fin n)) {r : ℝ}
    (hr : 0 < r) : (0:ℝ) < volume.real (Metric.ball c r) := by
  have hpos : 0 < volume (Metric.ball c r) :=
    Measure.measure_pos_of_nonempty_interior volume
      ⟨c, by rw [Metric.isOpen_ball.interior_eq]; exact Metric.mem_ball_self hr⟩
  have hne : volume.real (Metric.ball c r) ≠ 0 :=
    (measureReal_ne_zero_iff (ball_measure_ne_top c hr)).mpr hpos.ne'
  exact lt_of_le_of_ne measureReal_nonneg hne.symm

/-- The ball average of `v` minus the centre is the radial integral of the pairing
`⟪∇v, y - c⟫`, rescaled. -/
private lemma integral_ball_sub_center_eq_radial {n : ℕ} [Nonempty (Fin n)]
    (v : EuclideanSpace ℝ (Fin n) → ℝ) (hv : ContDiff ℝ 2 v)
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    (∫ y in Metric.ball c r, (v y - v c))
      = ∫ t in (0:ℝ)..1, (t ^ (n+1))⁻¹ *
          (∫ y in Metric.ball c (t*r), (fderiv ℝ v y) (y - c)) := by
  have hfd_cont : Continuous (fun z : EuclideanSpace ℝ (Fin n) => fderiv ℝ v z) :=
    hv.continuous_fderiv (by simp)
  have hpt : ∀ y : EuclideanSpace ℝ (Fin n),
      v y - v c = ∫ s in (0:ℝ)..1, (fderiv ℝ v (c + s • (y - c))) (y - c) := by
    intro y
    have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => v (c + s • (y - c)))
        ((fderiv ℝ v (c + s • (y - c))) (y - c)) s := by
      intro s
      have h1 : HasDerivAt (fun s : ℝ => c + s • (y - c)) (y - c) s := by
        simpa using ((hasDerivAt_id s).smul_const (y - c)).const_add c
      exact (((hv.differentiable (by simp)).differentiableAt.hasFDerivAt)).comp_hasDerivAt s h1
    have hint : IntervalIntegrable (fun s : ℝ => (fderiv ℝ v (c + s • (y - c))) (y - c))
        volume 0 1 := by
      apply Continuous.intervalIntegrable
      have hc : Continuous (fun s : ℝ => c + s • (y - c)) := by fun_prop
      exact (hfd_cont.comp hc).clm_apply continuous_const
    have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0:ℝ)) (b := 1)
      (f := fun s : ℝ => v (c + s • (y - c)))
      (f' := fun s : ℝ => (fderiv ℝ v (c + s • (y - c))) (y - c))
      (fun s _ => hderiv s) hint
    rw [H]
    simp
  have hcongr : (∫ y in Metric.ball c r, (v y - v c))
      = ∫ y in Metric.ball c r,
          ∫ s in (0:ℝ)..1, (fderiv ℝ v (c + s • (y - c))) (y - c) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    exact hpt y
  rw [hcongr]
  have hint : Integrable (Function.uncurry fun s y =>
        (fderiv ℝ v (c + s • (y - c))) (y - c))
      ((volume.restrict (Set.uIoc (0:ℝ) 1)).prod (volume.restrict (Metric.ball c r))) := by
    rw [Measure.prod_restrict]
    have hcont : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ v (c + p.1 • (p.2 - c))) (p.2 - c)) := by
      have h1 : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin n) => c + p.1 • (p.2 - c)) := by
        fun_prop
      exact (hfd_cont.comp h1).clm_apply (by fun_prop)
    have hsub : Set.uIoc (0:ℝ) 1 ×ˢ Metric.ball c r ⊆
        Set.Icc (0:ℝ) 1 ×ˢ Metric.closedBall c r :=
      Set.prod_mono (by
        rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        intro x hx
        exact ⟨le_of_lt hx.1, hx.2⟩) Metric.ball_subset_closedBall
    exact (ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_closedBall c r)) hcont.continuousOn).mono_set hsub
  have hfub : (∫ y in Metric.ball c r,
        ∫ s in (0:ℝ)..1, (fderiv ℝ v (c + s • (y - c))) (y - c))
      = ∫ s in (0:ℝ)..1, ∫ y in Metric.ball c r,
          (fderiv ℝ v (c + s • (y - c))) (y - c) :=
    (intervalIntegral_integral_swap (μ := volume.restrict (Metric.ball c r)) hint).symm
  rw [hfub]
  apply intervalIntegral.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t ht
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
  exact radial_integral_subst v c ht.1

/-!
## The local mean value inequality

The global statement `Commons.Analysis.Harmonic.le_setAverage_ball_of_laplacian_nonneg` assumes
that `v` is `C²` on the whole space and that `Δ v ≥ 0` everywhere.  Here we only assume this on an
open set `s` containing the closed ball `closedBall c r`.

The reduction to the global statement is by multiplying `v` with a smooth cutoff `φ` which equals
`1` on a neighbourhood of `closedBall c r` and whose support is contained in `s`.  The resulting
function `w = fun x => φ x * v x` is globally `C²`, agrees with `v` on `ball c r`, and its
Laplacian agrees with that of `v` there (in particular it is `≥ 0`, since `closedBall c r ⊆ s`).
The two integral identities used in the proof of the global statement
(`integral_ball_sub_center_eq_radial` and `integral_fderiv_sub_eq_half_integral_laplacian`) are
pure identities valid for any globally `C²` function, so they apply to `w`.
-/

/-- If `φ` is `C²` with `tsupport φ ⊆ s`, `s` is open, and `v` is `C²` on `s`, then the product
`fun x => φ x * v x` is (globally) `C²`. -/
private lemma aux_contDiff_mul_of_contDiffOn_of_tsupport_subset
    {n : ℕ} {v : EuclideanSpace ℝ (Fin n) → ℝ} {s : Set (EuclideanSpace ℝ (Fin n))}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hs : IsOpen s) (hφ : ContDiff ℝ 2 φ)
    (hφs : tsupport φ ⊆ s) (hv : ContDiffOn ℝ 2 v s) :
    ContDiff ℝ 2 (fun x => φ x * v x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ s
  · exact hφ.contDiffAt.mul (hv.contDiffAt (hs.mem_nhds hx))
  · have hx' : x ∉ tsupport φ := fun h => hx (hφs h)
    have hev : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx'
    have hev2 : (fun y => φ y * v y) =ᶠ[𝓝 x]
        (fun _ : EuclideanSpace ℝ (Fin n) => (0:ℝ)) := by
      filter_upwards [hev] with y hy
      simp [hy]
    have hconst : ContDiffAt ℝ 2 (fun _ : EuclideanSpace ℝ (Fin n) => (0:ℝ)) x :=
      contDiffAt_const
    have hval : (fun y => φ y * v y) x = (fun _ : EuclideanSpace ℝ (Fin n) => (0:ℝ)) x := by
      simp [hev.eq_of_nhds]
    exact (Filter.EventuallyEq.congr_contDiffWithinAt (s := Set.univ)
      (by simpa [nhdsWithin_univ] using hev2) hval).mpr hconst

/-- From `0 ≤ ∫_{B(c,r)} (v - v c)` (and integrability of `v` on the ball) one gets the
mean value inequality `v c ≤ ⨍_{B(c,r)} v`. -/
private lemma aux_le_setAverage_of_integral_sub_center_nonneg {n : ℕ}
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {c : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hr : 0 < r) (hvint : IntegrableOn v (Metric.ball c r) volume)
    (hmain : 0 ≤ ∫ y in Metric.ball c r, (v y - v c)) :
    v c ≤ ⨍ y in Metric.ball c r, v y := by
  have hV : 0 < volume.real (Metric.ball c r) := ball_measureReal_pos c hr
  have hIntc : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => v c) (Metric.ball c r) volume :=
    integrableOn_const (ball_measure_ne_top c hr) (by simp)
  have hsub : (∫ y in Metric.ball c r, (v y - v c))
      = (∫ y in Metric.ball c r, v y) - (volume.real (Metric.ball c r)) * v c := by
    rw [integral_sub hvint hIntc, setIntegral_const, smul_eq_mul]
  have hkey : (volume.real (Metric.ball c r)) * v c ≤ ∫ y in Metric.ball c r, v y := by
    linarith
  rw [setAverage_eq, smul_eq_mul]
  calc v c = (volume.real (Metric.ball c r))⁻¹ * ((volume.real (Metric.ball c r)) * v c) := by
        rw [← mul_assoc, inv_mul_cancel₀ hV.ne', one_mul]
    _ ≤ (volume.real (Metric.ball c r))⁻¹ * (∫ y in Metric.ball c r, v y) :=
        mul_le_mul_of_nonneg_left hkey (inv_nonneg.mpr hV.le)

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace in
theorem le_setAverage_ball_of_laplacian_nonneg_of_isOpen {n : ℕ}
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsOpen s)
    (hv : ContDiffOn ℝ 2 v s) (hΔ : ∀ x ∈ s, 0 ≤ Laplacian.laplacian v x)
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (hsub : closedBall c r ⊆ s) :
    v c ≤ ⨍ y in ball c r, v y := by
  have hvcont : ContinuousOn v (closedBall c r) := (hv.mono hsub).continuousOn
  have hvint : IntegrableOn v (ball c r) volume :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall c r) hvcont).mono_set
      ball_subset_closedBall
  rcases isEmpty_or_nonempty (Fin n) with hem | hne
  · -- degenerate case `n = 0`: the ball is a single point and the average is `v c`
    refine aux_le_setAverage_of_integral_sub_center_nonneg hr hvint ?_
    have hzero : (∫ y in ball c r, (v y - v c)) = ∫ y in ball c r, (0:ℝ) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro y hy
      have hyc : y = c := Subsingleton.elim y c
      simp [hyc]
    rw [hzero, integral_zero]
  · haveI : Nonempty (Fin n) := hne
    -- a closed ball slightly larger than `closedBall c r` and still contained in `s`
    obtain ⟨d, hdpos, hdsub⟩ :=
      (isCompact_closedBall c r).exists_thickening_subset_open hs hsub
    have hball_sub : ball c (d + r) ⊆ s := by
      rw [← thickening_closedBall hdpos hr.le c]
      exact hdsub
    set R : ℝ := r + d / 2 with hRdef
    have hRd : R < d + r := by rw [hRdef]; linarith
    let b : ContDiffBump c :=
      { rIn := r, rOut := R, rIn_pos := hr, rIn_lt_rOut := by rw [hRdef]; linarith }
    have hb_supp : tsupport (b : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ s := by
      rw [b.tsupport_eq]
      exact (closedBall_subset_ball hRd).trans hball_sub
    set w : EuclideanSpace ℝ (Fin n) → ℝ := fun x => b x * v x with hwdef
    have hb_cont : ContDiff ℝ 2 (b : EuclideanSpace ℝ (Fin n) → ℝ) := b.contDiff (n := 2)
    have hw : ContDiff ℝ 2 w :=
      aux_contDiff_mul_of_contDiffOn_of_tsupport_subset hs hb_cont hb_supp hv
    -- `w` agrees with `v` on `closedBall c r`
    have hw_eq : ∀ x ∈ closedBall c r, w x = v x := by
      intro x hx
      have hbx : (b : EuclideanSpace ℝ (Fin n) → ℝ) x = 1 := by
        apply b.one_of_mem_closedBall
        simpa only [b] using hx
      simp only [hwdef, hbx, one_mul]
    have hc_mem : c ∈ closedBall c r := by
      rw [Metric.mem_closedBall, dist_self]; exact hr.le
    have hmain : 0 ≤ ∫ y in ball c r, (v y - v c) := by
      have h1 : (∫ y in ball c r, (v y - v c)) = ∫ y in ball c r, (w y - w c) := by
        apply setIntegral_congr_fun measurableSet_ball
        intro y hy
        change v y - v c = w y - w c
        rw [hw_eq y (ball_subset_closedBall hy), hw_eq c hc_mem]
      rw [h1, integral_ball_sub_center_eq_radial w hw c hr]
      apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      refine mul_nonneg (inv_nonneg.mpr (pow_nonneg ht0 _)) ?_
      rcases eq_or_lt_of_le ht0 with h | h
      · rw [← h]; simp
      · rw [integral_fderiv_sub_eq_half_integral_laplacian w hw c (by positivity : 0 < t * r)]
        apply mul_nonneg (by norm_num)
        apply setIntegral_nonneg measurableSet_ball
        intro y hy
        have hytr : y ∈ ball c (t * r) := hy
        have hyr : y ∈ ball c r := by
          rw [Metric.mem_ball, dist_eq_norm] at hytr ⊢
          nlinarith [hytr, ht.2, hr.le, norm_nonneg (y - c)]
        refine mul_nonneg ?_ ?_
        · rw [Metric.mem_ball, dist_eq_norm] at hytr
          nlinarith [norm_nonneg (y - c), sq_nonneg (t * r - ‖y - c‖)]
        · have hys : y ∈ s := hsub (ball_subset_closedBall hyr)
          have hb1 : (b : EuclideanSpace ℝ (Fin n) → ℝ) =ᶠ[𝓝 y] (fun _ => (1:ℝ)) := by
            apply b.eventuallyEq_one_of_mem_ball
            simpa only [b, mem_ball, dist_eq_norm] using hyr
          have hev : w =ᶠ[𝓝 y] v := by
            filter_upwards [hb1] with z hz
            simp only [hwdef, hz, one_mul]
          have hlap : Laplacian.laplacian w y = Laplacian.laplacian v y :=
            (InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds
          rw [hlap]
          exact hΔ y hys
    exact aux_le_setAverage_of_integral_sub_center_nonneg hr hvint hmain

end

end Commons.Analysis.Harmonic
