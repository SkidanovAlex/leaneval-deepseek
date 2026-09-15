import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Commons.Analysis.Complex.norm_sq_le_average_norm_sq_of_analyticOn_ball

open MeasureTheory Metric
open scoped ENNReal

namespace Commons.Analysis.Complex

/-- **Volume of a polydisc** in `Fin d → ℂ` (sup-norm): `(π r²)^d`. -/
theorem polydisc_volume {d : ℕ} (z : Fin d → ℂ) {r : ℝ} (hr : 0 < r) :
    ENNReal.toReal (MeasureTheory.volume (Metric.closedBall z r)) = (Real.pi * r ^ 2) ^ d := by
  have hclosed : Metric.closedBall z r = Set.pi Set.univ (fun i => Metric.closedBall (z i) r) := by
    ext w
    simp only [Set.mem_pi, Set.mem_univ, true_implies, mem_closedBall]
    exact dist_pi_le_iff hr.le
  rw [hclosed,
    show (volume : Measure (Fin d → ℂ)) = Measure.pi (fun _ : Fin d => (volume : Measure ℂ)) from rfl]
  rw [Measure.pi_pi]
  have hbase : ∀ i : Fin d, (volume : Measure ℂ) (Metric.closedBall (z i) r)
      = ENNReal.ofReal (Real.pi * r ^ 2) := by
    intro i
    rw [Complex.volume_closedBall]
    rw [← ENNReal.ofReal_coe_nnreal (p := NNReal.pi), ← ENNReal.ofReal_pow (le_of_lt hr),
      ← ENNReal.ofReal_mul (by positivity), NNReal.coe_real_pi, mul_comm]
  simp_rw [hbase]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity)]

/-- Membership in the polydisc `closedBall z r ⊆ Fin (n+1) → ℂ`, transported to
`ℂ × (Fin n → ℂ)` via `Fin.cons`. -/
theorem closedBall_fin_cons_iff {n : ℕ} (z : Fin (n + 1) → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (p : ℂ × (Fin n → ℂ)) :
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).symm p ∈ Metric.closedBall z r)
      ↔ p ∈ Metric.closedBall (z 0) r ×ˢ Metric.closedBall (Fin.tail z) r := by
  obtain ⟨u, w'⟩ := p
  rw [show ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).symm (u, w'))
      = (Fin.cons u w' : Fin (n + 1) → ℂ) from by
    ext i; simp [MeasurableEquiv.piFinSuccAbove_symm_apply]]
  simp only [mem_closedBall, Set.mem_prod]
  rw [dist_pi_le_iff hr, dist_pi_le_iff hr]
  constructor
  · intro h; exact ⟨h 0, fun j => h (Fin.succ j)⟩
  · rintro ⟨h0, hsucc⟩ i
    induction i using Fin.cases with
    | zero => simpa using h0
    | succ j => exact hsucc j

/-- **Fubini/Tonelli along `Fin.cons`** for the polydisc. -/
theorem lintegral_closedBall_fin_cons {n : ℕ} (z : Fin (n + 1) → ℂ) (r : ℝ)
    (A : (Fin (n + 1) → ℂ) → ℝ≥0∞)
    (hA : AEMeasurable A (MeasureTheory.volume.restrict (Metric.closedBall z r))) :
    ∫⁻ w in Metric.closedBall z r, A w =
      ∫⁻ w' in Metric.closedBall (Fin.tail z) r,
        ∫⁻ u in Metric.closedBall (z 0) r, A (Fin.cons u w' : Fin (n + 1) → ℂ) := by
  classical
  by_cases hr : r < 0
  · rw [Metric.closedBall_eq_empty.mpr hr, Metric.closedBall_eq_empty.mpr hr]
    simp
  push Not at hr
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0 with he
  have hesymm : ∀ (p : ℂ × (Fin n → ℂ)), e.symm p = (Fin.cons p.1 p.2 : Fin (n + 1) → ℂ) := by
    rintro ⟨u, w'⟩
    rw [he]
    ext i
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
  have hmp : MeasurePreserving e.symm (volume.prod volume) (volume : Measure (Fin (n + 1) → ℂ)) := by
    rw [he]; exact (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0).symm
  have hpre : e.symm ⁻¹' (Metric.closedBall z r)
      = Metric.closedBall (z 0) r ×ˢ Metric.closedBall (Fin.tail z) r := by
    ext p
    rw [Set.mem_preimage, closedBall_fin_cons_iff z r hr p]
  have hmap : Measure.map e.symm
        ((volume.prod volume).restrict (Metric.closedBall (z 0) r ×ˢ Metric.closedBall (Fin.tail z) r))
      = volume.restrict (Metric.closedBall z r) := by
    rw [← hpre]
    exact (Measure.restrict_map e.symm.measurable measurableSet_closedBall).symm.trans
      (by rw [hmp.map_eq])
  have hAcomp : AEMeasurable (fun p : ℂ × (Fin n → ℂ) => A (e.symm p))
      ((volume.prod volume).restrict (Metric.closedBall (z 0) r ×ˢ Metric.closedBall (Fin.tail z) r)) := by
    change AEMeasurable (A ∘ e.symm) ((volume.prod volume).restrict
      (Metric.closedBall (z 0) r ×ˢ Metric.closedBall (Fin.tail z) r))
    rw [← (MeasurableEquiv.measurableEmbedding e.symm).aemeasurable_map_iff (g := A)
      (μ := (volume.prod volume).restrict
        (Metric.closedBall (z 0) r ×ˢ Metric.closedBall (Fin.tail z) r)), hmap]
    exact hA
  have hstep : ∫⁻ w in Metric.closedBall z r, A w
      = ∫⁻ p, (Metric.closedBall z r).indicator A (e.symm p) ∂(volume.prod volume) := by
    rw [← lintegral_indicator measurableSet_closedBall A]
    exact (hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding e.symm)
      (fun w => (Metric.closedBall z r).indicator A w)).symm
  rw [hstep]
  have hcongr : (fun p : ℂ × (Fin n → ℂ) => (Metric.closedBall z r).indicator A (e.symm p))
      = (Metric.closedBall (z 0) r ×ˢ Metric.closedBall (Fin.tail z) r).indicator
          (fun p => A (e.symm p)) := by
    funext p
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hp : p ∈ Metric.closedBall (z 0) r ×ˢ Metric.closedBall (Fin.tail z) r
    · rw [if_pos hp, if_pos ((closedBall_fin_cons_iff z r hr p).mpr hp)]
    · rw [if_neg hp, if_neg (fun h => hp ((closedBall_fin_cons_iff z r hr p).mp h))]
  rw [hcongr, lintegral_indicator (measurableSet_closedBall.prod measurableSet_closedBall)]
  rw [setLIntegral_prod_symm (f := fun a : ℂ × (Fin n → ℂ) => A (e.symm a)) hAcomp]
  apply lintegral_congr; intro w'
  apply lintegral_congr; intro u
  rw [hesymm]

/-- The slice `w' ↦ Fin.cons u w'` is analytic everywhere. -/
theorem analyticAt_fin_cons_tail {n : ℕ} (z₀ : ℂ) (x : Fin n → ℂ) :
    AnalyticAt ℂ (fun w' : Fin n → ℂ => (Fin.cons z₀ w' : Fin (n + 1) → ℂ)) x := by
  refine AnalyticAt.pi (f := fun (i : Fin (n + 1)) (w' : Fin n → ℂ) =>
    (Fin.cons z₀ w' : Fin (n + 1) → ℂ) i) ?_
  intro i
  induction i using Fin.cases with
  | zero => simpa [Fin.cons_zero] using analyticAt_const (v := z₀) (x := x)
  | succ j => exact (ContinuousLinearMap.proj (R := ℂ) j).analyticAt x

/-- The slice `u ↦ Fin.cons u w'` is analytic everywhere. -/
theorem analyticAt_fin_cons_head {n : ℕ} (w' : Fin n → ℂ) (u : ℂ) :
    AnalyticAt ℂ (fun u : ℂ => (Fin.cons u w' : Fin (n + 1) → ℂ)) u := by
  refine AnalyticAt.pi (f := fun (i : Fin (n + 1)) (u : ℂ) =>
    (Fin.cons u w' : Fin (n + 1) → ℂ) i) ?_
  intro i
  induction i using Fin.cases with
  | zero => (simp only [Fin.cons_zero]; exact analyticAt_id)
  | succ j => simpa [Fin.cons_succ] using analyticAt_const (v := w' j) (x := u)

/-- Restriction of an analytic function of `n+1` variables to the last `n` variables
(fixing the first to `z 0`) is analytic on the smaller polydisc. -/
theorem analyticOnNhd_fin_cons_tail {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℂ} {z : Fin (n + 1) → ℂ}
    {r : ℝ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall z r)) :
    AnalyticOnNhd ℂ (fun w' : Fin n → ℂ => f (Fin.cons (z 0) w' : Fin (n + 1) → ℂ))
      (Metric.closedBall (Fin.tail z) r) := by
  rcases lt_or_ge r 0 with hr | hr
  · rw [Metric.closedBall_eq_empty.mpr hr]
    exact fun x hx => absurd hx (by simp)
  refine AnalyticOnNhd.comp hf (fun x _ => analyticAt_fin_cons_tail (z 0) x) ?_
  intro w' hw'
  have hz : (Fin.cons (z 0) (Fin.tail z) : Fin (n + 1) → ℂ) = z := Fin.cons_self_tail z
  rw [← hz]
  rw [mem_closedBall, dist_pi_le_iff hr]
  rw [mem_closedBall, dist_pi_le_iff hr] at hw'
  intro i
  induction i using Fin.cases with
  | zero => simpa using hr
  | succ j => simpa [Fin.cons_succ] using hw' j

/-- Restriction of an analytic function of `n+1` variables to one variable (fixing the
remaining ones to `w' ∈ closedBall (Fin.tail z) r`) is analytic on `closedBall (z 0) r`. -/
theorem analyticOnNhd_fin_cons_head {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℂ} {z : Fin (n + 1) → ℂ}
    {r : ℝ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall z r)) {w' : Fin n → ℂ}
    (hw' : w' ∈ Metric.closedBall (Fin.tail z) r) :
    AnalyticOnNhd ℂ (fun u : ℂ => f (Fin.cons u w' : Fin (n + 1) → ℂ))
      (Metric.closedBall (z 0) r) := by
  rcases lt_or_ge r 0 with hr | hr
  · rw [Metric.closedBall_eq_empty.mpr hr] at hw' ⊢
    exact fun x hx => absurd hx (by simp)
  refine AnalyticOnNhd.comp hf (fun x _ => analyticAt_fin_cons_head w' x) ?_
  intro u hu
  have hz : (Fin.cons (z 0) (Fin.tail z) : Fin (n + 1) → ℂ) = z := Fin.cons_self_tail z
  rw [← hz]
  rw [mem_closedBall, dist_pi_le_iff hr]
  rw [mem_closedBall, dist_pi_le_iff hr] at hw'
  intro i
  induction i using Fin.cases with
  | zero => exact hu
  | succ j => exact hw' j

/-- For a nonnegative real function, `ofReal` of the (Bochner) integral is bounded by the
`ℝ≥0∞`-integral of `ofReal` of the function. -/
theorem ofReal_integral_le_lintegral_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : 0 ≤ f) (hfm : AEStronglyMeasurable f μ) :
    ENNReal.ofReal (∫ a, f a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (f a) ∂μ := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf) hfm]
  exact ENNReal.ofReal_toReal_le

/-- The main inductive step, in `ℝ≥0∞` form. -/
private theorem key (d : ℕ) : ∀ (f : (Fin d → ℂ) → ℂ) (z : Fin d → ℂ) (r : ℝ),
    0 < r → AnalyticOnNhd ℂ f (Metric.closedBall z r) →
    ENNReal.ofReal (‖f z‖ ^ 2) ≤
      (ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall z r))))⁻¹ *
        ∫⁻ w in Metric.closedBall z r, ENNReal.ofReal (‖f w‖ ^ 2) := by
  induction d with
  | zero =>
    intro f z r hr hf
    have hmem : z ∈ Metric.closedBall z r := mem_closedBall_self hr.le
    have hvol : (volume : Measure (Fin 0 → ℂ)) = Measure.dirac z :=
      Measure.volume_pi_eq_dirac (α := fun _ : Fin 0 => ℂ) z
    rw [hvol]
    have h1 : Measure.dirac z (Metric.closedBall z r) = 1 := Measure.dirac_apply_of_mem hmem
    have h2 : ∫⁻ w in Metric.closedBall z r, ENNReal.ofReal (‖f w‖ ^ 2) ∂(Measure.dirac z)
        = ENNReal.ofReal (‖f z‖ ^ 2) := by
      rw [← lintegral_indicator measurableSet_closedBall (fun w => ENNReal.ofReal (‖f w‖ ^ 2)),
        lintegral_dirac, Set.indicator_of_mem hmem]
    rw [h1, h2]
    simp
  | succ n ih =>
    intro f z r hr hf
    -- boundedness of `f` on the polydisc
    have hcont : ContinuousOn f (Metric.closedBall z r) :=
      fun x hx => (hf x hx).continuousAt.continuousWithinAt
    obtain ⟨M, hM⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn hcont
    have hM0 : 0 ≤ M := le_trans (norm_nonneg (f z)) (hM z (mem_closedBall_self hr.le))
    -- volume computations
    have hdV : ENNReal.toReal (volume (Metric.closedBall z r)) = (Real.pi * r ^ 2) ^ (n + 1) :=
      polydisc_volume z hr
    have hdV' : ENNReal.toReal (volume (Metric.closedBall (Fin.tail z) r)) = (Real.pi * r ^ 2) ^ n :=
      polydisc_volume (Fin.tail z) hr
    have hdW : ENNReal.toReal (volume (Metric.closedBall (z 0) r)) = Real.pi * r ^ 2 := by
      rw [Complex.volume_closedBall, ← ENNReal.ofReal_coe_nnreal (p := NNReal.pi),
        ← ENNReal.ofReal_pow (le_of_lt hr), ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ r ^ 2),
        NNReal.coe_real_pi, ENNReal.toReal_ofReal (by positivity)]
      ring
    have hA0 : ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall (Fin.tail z) r))) ≠ 0 := by
      rw [hdV']; exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity) n)).ne'
    have hB0 : ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall (z 0) r))) ≠ 0 := by
      rw [hdW]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hVW : ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall z r)))
        = ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall (Fin.tail z) r)))
          * ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall (z 0) r))) := by
      rw [hdV, hdV', hdW, pow_succ, ENNReal.ofReal_mul (by positivity)]
    have hVWinv : (ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall z r))))⁻¹
        = (ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall (Fin.tail z) r))))⁻¹
          * (ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall (z 0) r))))⁻¹ := by
      rw [hVW, ENNReal.mul_inv (Or.inl hA0) (Or.inr hB0)]
    have hBne : (ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall (z 0) r))))⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.mpr hB0
    -- the induction hypothesis
    have hslice : AnalyticOnNhd ℂ (fun w' : Fin n → ℂ => f (Fin.cons (z 0) w' : Fin (n + 1) → ℂ))
        (Metric.closedBall (Fin.tail z) r) := analyticOnNhd_fin_cons_tail hf
    have hIH := ih (fun w' : Fin n → ℂ => f (Fin.cons (z 0) w' : Fin (n + 1) → ℂ))
      (Fin.tail z) r hr hslice
    rw [Fin.cons_self_tail z] at hIH
    -- the pointwise one-dimensional sub-mean value inequality
    have hone : ∀ w' ∈ Metric.closedBall (Fin.tail z) r,
        ENNReal.ofReal (‖f (Fin.cons (z 0) w' : Fin (n + 1) → ℂ)‖ ^ 2) ≤
          (ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall (z 0) r))))⁻¹ *
            ∫⁻ u in Metric.closedBall (z 0) r,
              ENNReal.ofReal (‖f (Fin.cons u w' : Fin (n + 1) → ℂ)‖ ^ 2) := by
      intro w' hw'
      have hgN : AnalyticOnNhd ℂ (fun u : ℂ => f (Fin.cons u w' : Fin (n + 1) → ℂ))
          (Metric.closedBall (z 0) r) := analyticOnNhd_fin_cons_head hf hw'
      have hgA : AnalyticOn ℂ (fun u : ℂ => f (Fin.cons u w' : Fin (n + 1) → ℂ))
          (Metric.closedBall (z 0) r) := hgN.analyticOn
      have h1dlaw := norm_sq_le_average_norm_sq_of_analyticOn_ball hr hgA
      beta_reduce at h1dlaw
      have hcb : ContinuousOn (fun u : ℂ => f (Fin.cons u w' : Fin (n + 1) → ℂ))
          (Metric.ball (z 0) r) :=
        (fun u hu => (hgN u (Metric.ball_subset_closedBall hu)).continuousAt.continuousWithinAt)
      have hmeas : AEStronglyMeasurable
          (fun u : ℂ => ‖f (Fin.cons u w' : Fin (n + 1) → ℂ)‖ ^ 2)
          (volume.restrict (Metric.ball (z 0) r)) :=
        ((hcb.aestronglyMeasurable measurableSet_ball).norm).pow 2
      have hlint := ofReal_integral_le_lintegral_of_nonneg
        (μ := volume.restrict (Metric.ball (z 0) r))
        (f := fun u : ℂ => ‖f (Fin.cons u w' : Fin (n + 1) → ℂ)‖ ^ 2)
        (fun u => by positivity) hmeas
      calc ENNReal.ofReal (‖f (Fin.cons (z 0) w' : Fin (n + 1) → ℂ)‖ ^ 2)
          ≤ ENNReal.ofReal (1 / (Real.pi * r ^ 2)) *
              ENNReal.ofReal (∫ u in Metric.ball (z 0) r,
                ‖f (Fin.cons u w' : Fin (n + 1) → ℂ)‖ ^ 2) := by
            rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (Real.pi * r ^ 2))]
            exact ENNReal.ofReal_le_ofReal h1dlaw
        _ ≤ ENNReal.ofReal (1 / (Real.pi * r ^ 2)) *
              ∫⁻ u in Metric.ball (z 0) r,
                ENNReal.ofReal (‖f (Fin.cons u w' : Fin (n + 1) → ℂ)‖ ^ 2) := by
            gcongr
        _ ≤ ENNReal.ofReal (1 / (Real.pi * r ^ 2)) *
              ∫⁻ u in Metric.closedBall (z 0) r,
                ENNReal.ofReal (‖f (Fin.cons u w' : Fin (n + 1) → ℂ)‖ ^ 2) := by
            gcongr
            exact Metric.ball_subset_closedBall
        _ = (ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall (z 0) r))))⁻¹ *
              ∫⁻ u in Metric.closedBall (z 0) r,
                ENNReal.ofReal (‖f (Fin.cons u w' : Fin (n + 1) → ℂ)‖ ^ 2) := by
            rw [show ENNReal.ofReal (1 / (Real.pi * r ^ 2))
                = (ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall (z 0) r))))⁻¹ from by
              rw [hdW, one_div, ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < Real.pi * r ^ 2)]]
    -- monotonicity
    have hmono : (∫⁻ w' in Metric.closedBall (Fin.tail z) r,
            ENNReal.ofReal (‖f (Fin.cons (z 0) w' : Fin (n + 1) → ℂ)‖ ^ 2))
        ≤ (ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall (z 0) r))))⁻¹ *
            ∫⁻ w' in Metric.closedBall (Fin.tail z) r,
              ∫⁻ u in Metric.closedBall (z 0) r,
                ENNReal.ofReal (‖f (Fin.cons u w' : Fin (n + 1) → ℂ)‖ ^ 2) := by
      rw [← lintegral_const_mul' _ _ hBne]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with w' hw'
      exact hone w' hw'
    -- Fubini / Tonelli
    have hbridge : (∫⁻ w in Metric.closedBall z r, ENNReal.ofReal (‖f w‖ ^ 2))
        = (∫⁻ w' in Metric.closedBall (Fin.tail z) r,
            ∫⁻ u in Metric.closedBall (z 0) r,
              ENNReal.ofReal (‖f (Fin.cons u w' : Fin (n + 1) → ℂ)‖ ^ 2)) :=
      lintegral_closedBall_fin_cons z r (fun w => ENNReal.ofReal (‖f w‖ ^ 2))
        ((ENNReal.continuous_ofReal.comp_continuousOn (hcont.norm.pow 2)).aemeasurable
          measurableSet_closedBall)
    calc ENNReal.ofReal (‖f z‖ ^ 2)
        ≤ (ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall (Fin.tail z) r))))⁻¹ *
            ∫⁻ w' in Metric.closedBall (Fin.tail z) r,
              ENNReal.ofReal (‖f (Fin.cons (z 0) w' : Fin (n + 1) → ℂ)‖ ^ 2) := hIH
      _ ≤ (ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall (Fin.tail z) r))))⁻¹ *
            ((ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall (z 0) r))))⁻¹ *
              ∫⁻ w' in Metric.closedBall (Fin.tail z) r,
                ∫⁻ u in Metric.closedBall (z 0) r,
                  ENNReal.ofReal (‖f (Fin.cons u w' : Fin (n + 1) → ℂ)‖ ^ 2)) := by
            gcongr
      _ = ((ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall (Fin.tail z) r))))⁻¹ *
            (ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall (z 0) r))))⁻¹) *
              ∫⁻ w' in Metric.closedBall (Fin.tail z) r,
                ∫⁻ u in Metric.closedBall (z 0) r,
                  ENNReal.ofReal (‖f (Fin.cons u w' : Fin (n + 1) → ℂ)‖ ^ 2) := by
            rw [mul_assoc]
      _ = (ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall z r))))⁻¹ *
              ∫⁻ w in Metric.closedBall z r, ENNReal.ofReal (‖f w‖ ^ 2) := by
            rw [← hVWinv, ← hbridge]

/-- **Mean value inequality over a polydisc** for analytic functions of several complex
variables. -/
theorem meanValue_polydisc {d : ℕ}
    {f : (Fin d → ℂ) → ℂ} {z : Fin d → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall z r)) :
    ‖f z‖ ^ 2 ≤ (ENNReal.toReal (MeasureTheory.volume (Metric.closedBall z r)))⁻¹ *
      ∫ w in Metric.closedBall z r, ‖f w‖ ^ 2 := by
  have hkey := key d f z r hr hf
  have hcont : ContinuousOn f (Metric.closedBall z r) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (f z)) (hM z (mem_closedBall_self hr.le))
  have hmeas : AEStronglyMeasurable (fun w : Fin d → ℂ => ‖f w‖ ^ 2)
      (volume.restrict (Metric.closedBall z r)) :=
    ((hcont.aestronglyMeasurable measurableSet_closedBall).norm).pow 2
  have hfin : ∫⁻ w in Metric.closedBall z r, ENNReal.ofReal (‖f w‖ ^ 2) ≠ ⊤ := by
    have hle : ∫⁻ w in Metric.closedBall z r, ENNReal.ofReal (‖f w‖ ^ 2)
        ≤ ∫⁻ w in Metric.closedBall z r, ENNReal.ofReal (M ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with w hw
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg (f w)) (hM w hw) 2)
    have hc : ∫⁻ w in Metric.closedBall z r, ENNReal.ofReal (M ^ 2)
        = ENNReal.ofReal (M ^ 2) * volume (Metric.closedBall z r) := setLIntegral_const _ _
    rw [hc] at hle
    exact ne_of_lt (lt_of_le_of_lt hle
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (isCompact_closedBall z r).measure_lt_top))
  have hdVpos : 0 < ENNReal.toReal (volume (Metric.closedBall z r)) := by
    rw [polydisc_volume z hr]; positivity
  have hne : (ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall z r))))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hdVpos).ne'
  calc ‖f z‖ ^ 2 = (ENNReal.ofReal (‖f z‖ ^ 2)).toReal :=
        (ENNReal.toReal_ofReal (by positivity)).symm
    _ ≤ ((ENNReal.ofReal (ENNReal.toReal (volume (Metric.closedBall z r))))⁻¹ *
          ∫⁻ w in Metric.closedBall z r, ENNReal.ofReal (‖f w‖ ^ 2)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hne hfin) hkey
    _ = (ENNReal.toReal (volume (Metric.closedBall z r)))⁻¹ *
          ∫ w in Metric.closedBall z r, ‖f w‖ ^ 2 := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hdVpos.le]
        rw [← integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun w => by positivity)) hmeas]

end Commons.Analysis.Complex