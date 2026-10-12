import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.aliasImageDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imageW_lens_bound` — the image weight is `tsum`-finite

Backup (independent of the delegated `tsum_lintegral_aliasKernel_imageW_ne_top`) proof of the
analytic estimate underpinning `aliasImageIdentity`:

    ∑'_m ∫⁻_u ENNReal.ofReal (‖𝒢(u)‖ · imgW ℓ m u) ≠ ⊤ ,   𝒢 = aliasKernel g .

Route (strict support gap): `tsupport g` is a *compact* subset of the *open* ball `B(0, ℓ/2)`,
hence contained in a *closed* ball `B(0,R)` with `2R < ℓ`.  Then `autocorr g` vanishes for
`‖u‖ > 2R` (the two points `x`, `x − u` would both have norm `≤ R`), so the integrand is
supported in `B(0,2R)`, where `‖u − ℓ • latVec m‖ ≥ ℓ‖latVec m‖ − 2R` for every `m ≠ 0`.  Since
`|𝒢| ≤ ∫‖g‖²`, the `m`-th term is bounded by `(∫‖g‖²)·(ℓ‖latVec m‖ − 2R)^{-4}·|B(0,2R)|`, and
`Σ_{m ≠ 0}(ℓ‖latVec m‖ − 2R)^{-4} < ∞` (dominated by `(1 + ‖latVec m‖²)^{-2}`, summable by the
lattice decay `Work.BoseK15.sum_inv_one_add_norm_le`).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `‖latVec m‖ ≥ 1` for `m ≠ 0` (local copy of the helper of `aliasImageIdentity`). -/
private lemma one_le_norm_latVec' {m : Fin 3 → ℤ} (hm : m ≠ 0) : 1 ≤ ‖latVec m‖ := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hm (funext h)
  have h1 : (1 : ℝ) ≤ |((m i : ℤ) : ℝ)| := by
    have h2 : (1 : ℤ) ≤ |m i| := Int.one_le_abs hi
    exact_mod_cast h2
  have h2 : ‖(latVec m).ofLp i‖ = |((m i : ℤ) : ℝ)| := by
    have h3 : (latVec m).ofLp i = ((m i : ℤ) : ℝ) := by
      simp [latVec, WithLp.ofLp_toLp]
    rw [h3, Real.norm_eq_abs]
  calc (1 : ℝ) ≤ ‖(latVec m).ofLp i‖ := by rw [h2]; exact h1
    _ ≤ ‖latVec m‖ := PiLp.norm_apply_le (latVec m) i

private lemma vec_eq_smul_latVec (n : Fin 3 → ℤ) :
    Work.BoseB4.vec n = (2 * Real.pi) • latVec n := by
  have h : (fun i : Fin 3 => 2 * Real.pi * (n i : ℝ))
      = (2 * Real.pi) • (fun i : Fin 3 => (n i : ℝ)) := by
    funext i
    simp [Pi.smul_apply, smul_eq_mul]
  rw [Work.BoseB4.vec, latVec, h, WithLp.toLp_smul]

private lemma norm_vec_eq' (n : Fin 3 → ℤ) :
    ‖Work.BoseB4.vec n‖ = 2 * Real.pi * ‖latVec n‖ := by
  rw [vec_eq_smul_latVec, norm_smul, Real.norm_of_nonneg (by positivity)]

/-- **The lattice decay of `(1 + ‖latVec m‖²)^{-2}`.** -/
private lemma summable_inv_one_add_norm_latVec_sq :
    Summable (fun m : Fin 3 → ℤ => (((1 : ℝ) + ‖latVec m‖ ^ 2) ^ 2)⁻¹) := by
  have hS : Summable (fun n : Fin 3 → ℤ => (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 2)⁻¹) :=
    summable_of_sum_le (f := fun n : Fin 3 → ℤ => (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 2)⁻¹)
      (fun n => by positivity)
      (fun u => (Work.BoseK15.sum_inv_one_add_norm_le 2 (by norm_num)).choose_spec.2 u)
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    (hS.mul_left ((4 * Real.pi ^ 2) ^ 2))
  set x : ℝ := ‖latVec m‖ with hx
  have hCpos : (0 : ℝ) < (4 * Real.pi ^ 2) ^ 2 := by positivity
  have hA : 0 < (1 + (2 * Real.pi * x) ^ 2) ^ 2 := by positivity
  have hB : 0 < (1 + x ^ 2) ^ 2 := by positivity
  have h1 : 1 + (2 * Real.pi * x) ^ 2 ≤ (4 * Real.pi ^ 2) * (1 + x ^ 2) := by
    nlinarith [Real.pi_gt_three, sq_nonneg x]
  have h2 : (1 + (2 * Real.pi * x) ^ 2) ^ 2
      ≤ (4 * Real.pi ^ 2) ^ 2 * (1 + x ^ 2) ^ 2 := by
    calc (1 + (2 * Real.pi * x) ^ 2) ^ 2 ≤ ((4 * Real.pi ^ 2) * (1 + x ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = (4 * Real.pi ^ 2) ^ 2 * (1 + x ^ 2) ^ 2 := mul_pow _ _ _
  have hAC : 0 < (1 + (2 * Real.pi * x) ^ 2) ^ 2 / (4 * Real.pi ^ 2) ^ 2 := div_pos hA hCpos
  have hAC2 : (1 + (2 * Real.pi * x) ^ 2) ^ 2 / (4 * Real.pi ^ 2) ^ 2 ≤ (1 + x ^ 2) ^ 2 := by
    rw [div_le_iff₀ hCpos]
    calc (1 + (2 * Real.pi * x) ^ 2) ^ 2 ≤ (4 * Real.pi ^ 2) ^ 2 * (1 + x ^ 2) ^ 2 := h2
      _ = (1 + x ^ 2) ^ 2 * (4 * Real.pi ^ 2) ^ 2 := by ring
  have hkey : ((1 + x ^ 2) ^ 2)⁻¹
      ≤ (4 * Real.pi ^ 2) ^ 2 * (((1 + (2 * Real.pi * x) ^ 2) ^ 2)⁻¹) := by
    calc ((1 + x ^ 2) ^ 2)⁻¹
        ≤ (((1 + (2 * Real.pi * x) ^ 2) ^ 2 / (4 * Real.pi ^ 2) ^ 2))⁻¹ :=
          (inv_le_inv₀ hB hAC).mpr hAC2
      _ = (4 * Real.pi ^ 2) ^ 2 * (((1 + (2 * Real.pi * x) ^ 2) ^ 2)⁻¹) := by
          rw [inv_div]
          ring
  rw [norm_vec_eq', ← hx]
  exact hkey

/-- The autocorrelation vanishes outside the ball of radius `2R` when `tsupport g ⊆ B(0,R)`. -/
theorem autocorr_eq_zero_of_two_mul_lt_norm {R : ℝ} {g : E3 → ℂ}
    (hsupp : tsupport g ⊆ Metric.closedBall (0 : E3) R) {u : E3} (hu : 2 * R < ‖u‖) :
    autocorr g u = 0 := by
  have hzero : ∀ x, g x * starRingEnd ℂ (g (x - u)) = 0 := by
    intro x
    by_contra h
    have hx : g x ≠ 0 := fun hx0 => h (by simp [hx0])
    have hy : g (x - u) ≠ 0 := fun hy0 => h (by simp [hy0])
    have hxmem : x ∈ Metric.closedBall (0 : E3) R :=
      hsupp (subset_closure (Function.mem_support.mpr hx))
    have hymem : x - u ∈ Metric.closedBall (0 : E3) R :=
      hsupp (subset_closure (Function.mem_support.mpr hy))
    rw [Metric.mem_closedBall, dist_zero_right] at hxmem hymem
    have h1 : ‖u‖ ≤ ‖x - u‖ + ‖x‖ := by
      have h2 : ‖u‖ ≤ ‖u - x‖ + ‖x‖ := by
        have := norm_add_le (u - x) x
        simpa using this
      simpa [norm_sub_rev u x] using h2
    linarith
  rw [autocorr,
    show (fun x : E3 => g x * starRingEnd ℂ (g (x - u))) = fun _ => 0 from funext hzero]
  simp

/-- `tsupport g` lies in a closed ball of radius `R` with `2R < ℓ` whenever it lies in the open
ball `B(0, ℓ/2)`. -/
theorem exists_tsupport_subset_closedBall {ℓ : ℝ} (hℓ : 0 < ℓ) {g : E3 → ℂ}
    (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2)) :
    ∃ R : ℝ, 0 ≤ R ∧ 2 * R < ℓ ∧ tsupport g ⊆ Metric.closedBall 0 R := by
  have hK : IsCompact (tsupport g) :=
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_tsupport g, Metric.isBounded_ball.subset hgsupp⟩
  by_cases hne : (tsupport g).Nonempty
  · obtain ⟨x₀, hx₀, hmax⟩ :=
      hK.exists_isMaxOn hne continuous_norm.continuousOn
    refine ⟨‖x₀‖, norm_nonneg _, ?_, ?_⟩
    · have h1 : ‖x₀‖ < ℓ / 2 := by
        have := hgsupp hx₀
        rwa [Metric.mem_ball, dist_zero_right] at this
      linarith
    · intro x hx
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hmax hx
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨0, le_refl 0, by linarith, by rw [hne]; exact Set.empty_subset _⟩

/-- **The image weight is `tsum`-finite** (`ℝ≥0∞` form). -/
theorem tsum_lintegral_aliasKernel_imageW_lens {ℓ : ℝ} (hℓ : 0 < ℓ) {g : E3 → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g) (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2)) :
    (∑' m : Fin 3 → ℤ, ∫⁻ u : E3, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u)) ≠ ⊤ := by
  obtain ⟨R, hR0, hR2, hsuppR⟩ := exists_tsupport_subset_closedBall hℓ hgsupp
  have hgc : HasCompactSupport g := by
    rw [HasCompactSupport, Metric.isCompact_iff_isClosed_bounded]
    exact ⟨isClosed_tsupport g, Metric.isBounded_ball.subset hgsupp⟩
  set M : ℝ := ∫ x : E3, ‖g x‖ ^ 2 with hMdef
  have hM0 : 0 ≤ M := integral_nonneg (fun x => by positivity)
  have hBfin : (volume : Measure E3) (Metric.closedBall (0 : E3) (2 * R)) ≠ ⊤ :=
    (isCompact_closedBall (0 : E3) (2 * R)).measure_lt_top.ne
  set V : ℝ := (volume : Measure E3).real (Metric.closedBall (0 : E3) (2 * R)) with hVdef
  have hVB : (volume : Measure E3) (Metric.closedBall (0 : E3) (2 * R)) = ENNReal.ofReal V := by
    rw [hVdef, Measure.real_def, ENNReal.ofReal_toReal hBfin]
  -- pointwise bounds
  have hvan : ∀ u : E3, 2 * R < ‖u‖ → aliasKernel g u = 0 := fun u hu => by
    simp only [aliasKernel, autocorr_eq_zero_of_two_mul_lt_norm hsuppR hu, Complex.zero_re]
  have hMbound : ∀ u : E3, ‖aliasKernel g u‖ ≤ M := fun u =>
    le_trans (Complex.abs_re_le_norm _) (autocorr_norm_le hg hgc u)
  -- the lattice weight
  set a : (Fin 3 → ℤ) → ℝ := fun m =>
    if m = 0 then 0 else ((ℓ * ‖latVec m‖ - 2 * R) ^ 4)⁻¹ with hadef
  have ha0 : ∀ m, 0 ≤ a m := by
    intro m
    show 0 ≤ (if m = 0 then 0 else ((ℓ * ‖latVec m‖ - 2 * R) ^ 4)⁻¹)
    split
    · exact le_refl 0
    · positivity
  have hpos : ∀ m : Fin 3 → ℤ, m ≠ 0 → 0 < ℓ * ‖latVec m‖ - 2 * R := by
    intro m hm
    have h1 : ℓ ≤ ℓ * ‖latVec m‖ := by
      nth_rewrite 1 [← mul_one ℓ]
      exact mul_le_mul_of_nonneg_left (one_le_norm_latVec' hm) hℓ.le
    linarith
  -- the strict distance bound
  have hdist : ∀ m : Fin 3 → ℤ, m ≠ 0 → ∀ u : E3, ‖u‖ ≤ 2 * R →
      ℓ * ‖latVec m‖ - 2 * R ≤ ‖u - ℓ • latVec m‖ := by
    intro m hm u hu
    have h1 : ‖ℓ • latVec m‖ ≤ ‖ℓ • latVec m - u‖ + ‖u‖ := by
      have := norm_add_le (ℓ • latVec m - u) u
      simpa using this
    rw [norm_smul, Real.norm_of_nonneg hℓ.le, norm_sub_rev] at h1
    linarith
  -- the `m`-th bound
  have hm_bound : ∀ m : Fin 3 → ℤ,
      (∫⁻ u : E3, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u))
        ≤ ENNReal.ofReal (M * a m * V) := by
    intro m
    by_cases hm : m = 0
    · have haz : a 0 = 0 := by
        show (if (0 : Fin 3 → ℤ) = 0 then 0 else ((ℓ * ‖latVec 0‖ - 2 * R) ^ 4)⁻¹) = 0
        rw [if_pos rfl]
      rw [hm, haz, mul_zero, zero_mul, ENNReal.ofReal_zero]
      rw [show (fun u : E3 => ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ 0 u)) = fun _ => 0 from
        funext (fun u => by simp), lintegral_zero]
    · have hpt : ∀ u : E3, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u)
          ≤ ENNReal.ofReal (M * a m)
            * (Metric.closedBall (0 : E3) (2 * R)).indicator (fun _ => (1 : ENNReal)) u := by
        intro u
        rw [imgW_ne_zero hm]
        by_cases hu : u ∈ Metric.closedBall (0 : E3) (2 * R)
        · rw [Set.indicator_of_mem hu]
          simp only [Pi.one_apply, mul_one]
          refine ENNReal.ofReal_le_ofReal ?_
          have ham : a m = ((ℓ * ‖latVec m‖ - 2 * R) ^ 4)⁻¹ := by
            show (if m = 0 then 0 else ((ℓ * ‖latVec m‖ - 2 * R) ^ 4)⁻¹) = _
            rw [if_neg hm]
          have h1 : ℓ * ‖latVec m‖ - 2 * R ≤ ‖u - ℓ • latVec m‖ :=
            hdist m hm u (by simpa [Metric.mem_closedBall, dist_zero_right] using hu)
          have h2 : 0 < ℓ * ‖latVec m‖ - 2 * R := hpos m hm
          have h3 : (‖u - ℓ • latVec m‖ ^ 4)⁻¹ ≤ ((ℓ * ‖latVec m‖ - 2 * R) ^ 4)⁻¹ :=
            (inv_le_inv₀ (pow_pos (lt_of_lt_of_le h2 h1) 4) (pow_pos h2 4)).mpr
              (pow_le_pow_left₀ h2.le h1 4)
          calc ‖aliasKernel g u‖ * (‖u - ℓ • latVec m‖ ^ 4)⁻¹
              ≤ M * ((ℓ * ‖latVec m‖ - 2 * R) ^ 4)⁻¹ :=
                mul_le_mul (hMbound u) h3 (by positivity) hM0
            _ = M * a m := by rw [ham]
        · rw [Set.indicator_of_notMem hu, mul_zero]
          have hu' : 2 * R < ‖u‖ := by
            rw [Metric.mem_closedBall, dist_zero_right, not_le] at hu
            linarith
          simp [hvan u hu']
      calc (∫⁻ u : E3, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u))
          ≤ ∫⁻ u : E3, ENNReal.ofReal (M * a m)
              * (Metric.closedBall (0 : E3) (2 * R)).indicator (fun _ => (1 : ENNReal)) u :=
            lintegral_mono hpt
        _ = ENNReal.ofReal (M * a m)
              * ∫⁻ u : E3,
                  (Metric.closedBall (0 : E3) (2 * R)).indicator (fun _ => (1 : ENNReal)) u := by
            rw [lintegral_const_mul _ (measurable_const.indicator measurableSet_closedBall)]
        _ = ENNReal.ofReal (M * a m) * (volume : Measure E3) (Metric.closedBall (0 : E3) (2 * R)) := by
            rw [lintegral_indicator measurableSet_closedBall, setLIntegral_one]
        _ = ENNReal.ofReal (M * a m * V) := by
            rw [hVB, ← ENNReal.ofReal_mul (by positivity)]
  -- summability of the lattice weights
  have ha_summ : Summable a := by
    set C₀ : ℝ := 25 * ((ℓ ^ 4)⁻¹ + ((ℓ - 2 * R) ^ 4)⁻¹) with hC0def
    have hC0 : 0 ≤ C₀ := by
      rw [hC0def]
      exact mul_nonneg (by norm_num) (add_nonneg (by positivity) (by positivity))
    refine Summable.of_nonneg_of_le ha0 (fun m => ?_)
      (summable_inv_one_add_norm_latVec_sq.mul_left C₀)
    by_cases hm : m = 0
    · have haz : a m = 0 := by
        show (if m = 0 then 0 else ((ℓ * ‖latVec m‖ - 2 * R) ^ 4)⁻¹) = 0
        rw [if_pos hm]
      rw [haz]
      exact mul_nonneg hC0 (by positivity)
    · have ham : a m = ((ℓ * ‖latVec m‖ - 2 * R) ^ 4)⁻¹ := by
        show (if m = 0 then 0 else ((ℓ * ‖latVec m‖ - 2 * R) ^ 4)⁻¹) = _
        rw [if_neg hm]
      rw [ham]
      set x : ℝ := ‖latVec m‖ with hx
      have hx1 : 1 ≤ x := by rw [hx]; exact one_le_norm_latVec' hm
      have hx0 : 0 ≤ x := by linarith
      have hD : 0 < ℓ * x - 2 * R := by rw [hx]; exact hpos m hm
      have hkey : ((ℓ * x - 2 * R) ^ 4)⁻¹ ≤ C₀ * ((1 + x ^ 2) ^ 2)⁻¹ := by
        rcases le_total x 2 with hx2 | hx2
        · -- `x ≤ 2`: the distance is at least `ℓ - 2R`
          have hP : 0 < ℓ - 2 * R := by linarith
          have hDge : ℓ - 2 * R ≤ ℓ * x - 2 * R := by nlinarith [hℓ, hx1]
          have h1 : ((ℓ * x - 2 * R) ^ 4)⁻¹ ≤ ((ℓ - 2 * R) ^ 4)⁻¹ :=
            (inv_le_inv₀ (pow_pos hD 4) (pow_pos hP 4)).mpr (pow_le_pow_left₀ hP.le hDge 4)
          have h2 : (1 : ℝ) ≤ 25 * ((1 + x ^ 2) ^ 2)⁻¹ := by
            have h3 : (1 + x ^ 2) ^ 2 ≤ 25 := by
              have h6 : x ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ hx0 hx2 2
              nlinarith
            have h4 : (0 : ℝ) < (1 + x ^ 2) ^ 2 := by positivity
            have h5 : (1 : ℝ) * ((1 + x ^ 2) ^ 2)
                ≤ (25 * ((1 + x ^ 2) ^ 2)⁻¹) * ((1 + x ^ 2) ^ 2) := by
              rw [one_mul, mul_assoc, inv_mul_cancel₀ h4.ne', mul_one]
              exact h3
            exact (mul_le_mul_iff_of_pos_right h4).mp h5
          have h3 : 25 * ((ℓ - 2 * R) ^ 4)⁻¹ ≤ C₀ := by
            rw [hC0def]
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact le_add_of_nonneg_left (by positivity)
          calc ((ℓ * x - 2 * R) ^ 4)⁻¹ ≤ ((ℓ - 2 * R) ^ 4)⁻¹ := h1
            _ ≤ ((ℓ - 2 * R) ^ 4)⁻¹ * (25 * ((1 + x ^ 2) ^ 2)⁻¹) := by
                nth_rewrite 1 [← mul_one ((ℓ - 2 * R) ^ 4)⁻¹]
                exact mul_le_mul_of_nonneg_left h2 (by positivity)
            _ = 25 * ((ℓ - 2 * R) ^ 4)⁻¹ * ((1 + x ^ 2) ^ 2)⁻¹ := by ring
            _ ≤ C₀ * ((1 + x ^ 2) ^ 2)⁻¹ := mul_le_mul_of_nonneg_right h3 (by positivity)
        · -- `x ≥ 2`: the distance is at least `ℓ x / 2`
          have hDge : ℓ * x / 2 ≤ ℓ * x - 2 * R := by nlinarith [hR2, hℓ, hx2]
          have h1 : ((ℓ * x - 2 * R) ^ 4)⁻¹ ≤ (16 * (ℓ ^ 4)⁻¹) * (x ^ 4)⁻¹ := by
            have h5 : ((ℓ * x - 2 * R) ^ 4)⁻¹ ≤ (((ℓ * x) / 2) ^ 4)⁻¹ :=
              (inv_le_inv₀ (pow_pos hD 4) (by positivity)).mpr
                (pow_le_pow_left₀ (by positivity) hDge 4)
            have h6 : (((ℓ * x) / 2) ^ 4)⁻¹ = 16 * (ℓ ^ 4)⁻¹ * (x ^ 4)⁻¹ := by
              rw [div_pow, mul_pow]
              field_simp
              ring
            rwa [h6] at h5
          have h2 : (x ^ 4)⁻¹ ≤ 25 / 16 * ((1 + x ^ 2) ^ 2)⁻¹ := by
            have h10 : (1 + x ^ 2) ≤ (5 / 4) * x ^ 2 := by nlinarith
            have h11 : (1 + x ^ 2) ^ 2 ≤ ((5 / 4) * x ^ 2) ^ 2 :=
              pow_le_pow_left₀ (by positivity) h10 2
            have hA : 0 < ((5 / 4) * x ^ 2) ^ 2 := by positivity
            have hB : 0 < (1 + x ^ 2) ^ 2 := by positivity
            have h12 : (((5 / 4) * x ^ 2) ^ 2)⁻¹ = 16 / 25 * (x ^ 4)⁻¹ := by
              rw [mul_pow, ← pow_mul]
              field_simp
              ring
            have h13 : (((5 / 4) * x ^ 2) ^ 2)⁻¹ ≤ ((1 + x ^ 2) ^ 2)⁻¹ :=
              (inv_le_inv₀ hA hB).mpr h11
            rw [h12] at h13
            calc (x ^ 4)⁻¹ = 25 / 16 * (16 / 25 * (x ^ 4)⁻¹) := by ring
              _ ≤ 25 / 16 * ((1 + x ^ 2) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h13 (by norm_num)
          have h3 : 25 * (ℓ ^ 4)⁻¹ ≤ C₀ := by
            rw [hC0def]
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact le_add_of_nonneg_right (by positivity)
          calc ((ℓ * x - 2 * R) ^ 4)⁻¹ ≤ (16 * (ℓ ^ 4)⁻¹) * (x ^ 4)⁻¹ := h1
            _ ≤ (16 * (ℓ ^ 4)⁻¹) * (25 / 16 * ((1 + x ^ 2) ^ 2)⁻¹) :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
            _ = 25 * (ℓ ^ 4)⁻¹ * ((1 + x ^ 2) ^ 2)⁻¹ := by ring
            _ ≤ C₀ * ((1 + x ^ 2) ^ 2)⁻¹ := mul_le_mul_of_nonneg_right h3 (by positivity)
      rw [hx] at hkey
      simpa only [hx] using hkey
  -- assembly
  intro htop
  have hle : (⊤ : ENNReal) ≤ ENNReal.ofReal (M * V * ∑' m : Fin 3 → ℤ, a m) := by
    rw [← htop]
    calc (∑' m : Fin 3 → ℤ, ∫⁻ u : E3, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u))
        ≤ ∑' m : Fin 3 → ℤ, ENNReal.ofReal (M * a m * V) := ENNReal.tsum_le_tsum hm_bound
      _ = ENNReal.ofReal (∑' m : Fin 3 → ℤ, M * a m * V) :=
          (ENNReal.ofReal_tsum_of_nonneg (f := fun m : Fin 3 → ℤ => M * a m * V)
            (fun m => by positivity)
            (((ha_summ.mul_left M).mul_left V).congr (fun m => by ring))).symm
      _ = ENNReal.ofReal (V * ∑' m : Fin 3 → ℤ, M * a m) := by
          congr 1
          rw [← Summable.tsum_mul_left V (ha_summ.mul_left M)]
          exact tsum_congr (fun m => by ring)
      _ = ENNReal.ofReal (V * (M * ∑' m : Fin 3 → ℤ, a m)) := by
          rw [Summable.tsum_mul_left M ha_summ]
      _ = ENNReal.ofReal (M * V * ∑' m : Fin 3 → ℤ, a m) := by
          congr 1
          ring
  exact ENNReal.ofReal_ne_top (top_unique hle)

end Work.BoseBoxFock
