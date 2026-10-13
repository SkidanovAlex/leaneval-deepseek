/-
  WilG4c / `SliceC1Real` — the `ε`-`δ` (ℓ²) predicate `C1Pred` is exactly `ContDiffAt ℝ 1`.

  `C1Pred g u` (see `SliceC1Defs`) says: on a ball around `u` every point `y` carries an
  `ε`-`δ` Fréchet derivative `HasFDerivEps g y c` (given by a coefficient vector `c`, so that
  the derivative is `linMap c`), and the coefficient vector depends continuously on `y` in the
  ℓ² sense.  This file proves the equivalence with Mathlib's `ContDiffAt ℝ 1 g u`, using the
  already-proved bridge `c1RealFD : HasFDerivEps g y c ↔ HasFDerivAt g (linMap c) y`.

  The only content is bookkeeping between the ℓ² ("sum of squares") balls used by `C1Pred` and
  Mathlib's sup norm, and between the coefficient vector of `linMap c` and the operator norm on
  `(Fin M → ℝ) →L[ℝ] ℝ`.  The constant `scK M = √M + 1` (always `≥ 1`, with `M < scK M ^ 2`)
  keeps all the estimates uniform in `M`, in particular covering `M = 0`.

  Everything here is `sorry`-free.
-/
import Mathlib
import Submission.Work.WilG4c.SliceC1Defs
import Submission.Work.WilG4c.c1RealFD

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilG4c

/-! ## 0. A uniform positive constant -/

/-- `scK M = √M + 1`: positive, `≥ 1`, and with `M < scK M ^ 2`. -/
private def scK (M : ℕ) : ℝ := Real.sqrt (M : ℝ) + 1

private lemma scK_pos (M : ℕ) : 0 < scK M := by
  have h := Real.sqrt_nonneg (M : ℝ)
  unfold scK
  linarith

private lemma natCast_lt_scK_sq (M : ℕ) : (M : ℝ) < scK M ^ 2 := by
  have hsq : Real.sqrt (M : ℝ) ^ 2 = (M : ℝ) := Real.sq_sqrt (Nat.cast_nonneg M)
  have hnn : 0 ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg _
  have h2 : (Real.sqrt (M : ℝ) + 1) ^ 2 = (M : ℝ) + 2 * Real.sqrt (M : ℝ) + 1 := by
    rw [add_sq, hsq]
    ring
  unfold scK
  rw [h2]
  linarith

/-! ## 1. Sup norm versus sum of squares -/

/-- The sup norm is dominated by the Euclidean (`ℓ²`) norm. -/
private lemma sc_norm_le_sqrt_sumSq {M : ℕ} (d : Fin M → ℝ) :
    ‖d‖ ≤ Real.sqrt (∑ j, (d j) ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg d)]
  exact Real.sqrt_le_sqrt (sq_norm_le_sum_sq d)

/-- A point within the sup distance `δ / scK M` lies in the sum-of-squares ball of radius `δ`. -/
private lemma sc_sumSq_lt_of_dist_lt {M : ℕ} {a y : Fin M → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h : dist y a < δ / scK M) : ∑ j, (y j - a j) ^ 2 < δ ^ 2 := by
  have hK := scK_pos M
  have hnorm : ‖y - a‖ < δ / scK M := by rwa [dist_eq_norm] at h
  have h2 : (∑ j, ((y - a) j) ^ 2) = ∑ j, (y j - a j) ^ 2 := by
    exact Finset.sum_congr rfl fun j _ => by simp
  rw [← h2]
  calc ∑ j, ((y - a) j) ^ 2
      ≤ (M : ℝ) * ‖y - a‖ ^ 2 := sum_sq_le_card_mul_sq_norm (y - a)
    _ ≤ (M : ℝ) * (δ / scK M) ^ 2 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hnorm) 2) (Nat.cast_nonneg M)
    _ = (M : ℝ) * (δ ^ 2 / scK M ^ 2) := by rw [div_pow]
    _ = ((M : ℝ) * δ ^ 2) / scK M ^ 2 := by ring
    _ < δ ^ 2 := by
        rw [div_lt_iff₀ (pow_pos hK 2)]
        nlinarith [mul_lt_mul_of_pos_right (natCast_lt_scK_sq M) (pow_pos hδ 2)]

/-! ## 2. Coefficient vectors of linear functionals -/

/-- The `j`-th coefficient of a functional is bounded by its operator norm. -/
private lemma sc_abs_linCoeff_le_opNorm {M : ℕ} (φ : (Fin M → ℝ) →L[ℝ] ℝ) (j : Fin M) :
    |linCoeff φ j| ≤ ‖φ‖ := by
  have h := ContinuousLinearMap.le_opNorm φ (Pi.single j (1 : ℝ) : Fin M → ℝ)
  have hnorm : ‖(Pi.single j (1 : ℝ) : Fin M → ℝ)‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs]
    by_cases hi : i = j
    · subst hi; simp
    · simp [Pi.single_eq_of_ne, Ne.symm hi]
  change |φ (Pi.single j (1 : ℝ))| ≤ ‖φ‖
  rw [← Real.norm_eq_abs]
  calc ‖φ (Pi.single j (1 : ℝ))‖ ≤ ‖φ‖ * ‖(Pi.single j (1 : ℝ) : Fin M → ℝ)‖ := h
    _ ≤ ‖φ‖ * 1 := mul_le_mul_of_nonneg_left hnorm (norm_nonneg φ)
    _ = ‖φ‖ := mul_one _

/-- The sum of squares of the coefficients of a functional is bounded by its operator norm. -/
private lemma sc_sumSq_linCoeff_le {M : ℕ} (φ : (Fin M → ℝ) →L[ℝ] ℝ) :
    ∑ j, (linCoeff φ j) ^ 2 ≤ (M : ℝ) * ‖φ‖ ^ 2 := by
  calc ∑ j, (linCoeff φ j) ^ 2 ≤ ∑ _j : Fin M, ‖φ‖ ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h := sc_abs_linCoeff_le_opNorm φ j
        have h2 : |linCoeff φ j| ≤ |‖φ‖| := by rwa [abs_of_nonneg (norm_nonneg φ)]
        exact sq_le_sq.mpr h2
    _ = (M : ℝ) * ‖φ‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The operator norm of `linMap c` is bounded by `scK M` times the `ℓ²` norm of `c`. -/
private lemma sc_linMap_norm_le {M : ℕ} (d : Fin M → ℝ) :
    ‖linMap d‖ ≤ scK M * Real.sqrt (∑ j, (d j) ^ 2) := by
  have h1 : ‖linMap d‖ ≤ ∑ j, |d j| := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun j _ => abs_nonneg _)
      fun v => ?_
    rw [linMap_apply, Real.norm_eq_abs]
    calc |∑ j, d j * v j| ≤ ∑ j, |d j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |d j| * |v j| := Finset.sum_congr rfl fun j _ => abs_mul _ _
      _ ≤ ∑ j, |d j| * ‖v‖ := Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left
              (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v j) (abs_nonneg _)
      _ = (∑ j, |d j|) * ‖v‖ := (Finset.sum_mul _ _ _).symm
  have hCS : (∑ j, |d j|) ^ 2 ≤ (∑ j, (d j) ^ 2) * (M : ℝ) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin M)) (fun j => |d j|)
      (fun _ => (1 : ℝ))
    have h1 : (∑ j, |d j| * (1 : ℝ)) = ∑ j, |d j| :=
      Finset.sum_congr rfl fun j _ => mul_one _
    have h2 : (∑ j, |d j| ^ 2) = ∑ j, (d j) ^ 2 :=
      Finset.sum_congr rfl fun j _ => sq_abs (d j)
    have h3 : (∑ _j : Fin M, (1 : ℝ) ^ 2) = (M : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [h1, h2, h3] at h
    exact h
  have h2 : ∑ j, |d j| ≤ scK M * Real.sqrt (∑ j, (d j) ^ 2) := by
    have hnn : 0 ≤ ∑ j, |d j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have hsq : 0 ≤ ∑ j, (d j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have h3 : ∑ j, |d j| ≤ Real.sqrt (∑ j, (d j) ^ 2) * Real.sqrt (M : ℝ) := by
      have h4 : Real.sqrt ((∑ j, |d j|) ^ 2) ≤ Real.sqrt ((∑ j, (d j) ^ 2) * (M : ℝ)) :=
        Real.sqrt_le_sqrt hCS
      rwa [Real.sqrt_sq hnn, Real.sqrt_mul hsq] at h4
    calc ∑ j, |d j| ≤ Real.sqrt (∑ j, (d j) ^ 2) * Real.sqrt (M : ℝ) := h3
      _ ≤ Real.sqrt (∑ j, (d j) ^ 2) * scK M := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          have := Real.sqrt_nonneg (M : ℝ)
          unfold scK
          linarith
      _ = scK M * Real.sqrt (∑ j, (d j) ^ 2) := by ring
  linarith

/-- `linMap` is additive in its coefficient vector. -/
private lemma sc_linMap_sub {M : ℕ} (c c' : Fin M → ℝ) :
    linMap (c - c') = linMap c - linMap c' := by
  ext v
  simp only [linMap_apply, sub_apply, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- `linCoeff` is additive. -/
private lemma sc_linCoeff_sub {M : ℕ} (φ ψ : (Fin M → ℝ) →L[ℝ] ℝ) :
    linCoeff (φ - ψ) = linCoeff φ - linCoeff ψ := by
  funext j
  simp [linCoeff]

/-! ## 3. `C1Pred` implies `ContDiffAt ℝ 1` -/

/-- The forward direction of the equivalence. -/
theorem c1Pred_to_contDiffAt_slice {M : ℕ} (g : (Fin M → ℝ) → ℝ) (u : Fin M → ℝ)
    (h : C1Pred g u) : ContDiffAt ℝ 1 g u := by
  obtain ⟨δ₀, hδ₀, hclause⟩ := h
  refine contDiffAt_one_iff.mpr
    ⟨fun z => fderiv ℝ g z, {y | ∑ j, (y j - u j) ^ 2 < δ₀ ^ 2}, ?_, ?_, ?_⟩
  · rw [Metric.mem_nhds_iff]
    exact ⟨δ₀ / scK M, div_pos hδ₀ (scK_pos M),
      fun z hz => sc_sumSq_lt_of_dist_lt hδ₀ hz⟩
  · intro y hy
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨c, hc_eps, hc_cont⟩ := hclause y hy
    obtain ⟨δ, hδ, hδclause⟩ := hc_cont (ε / scK M) (div_pos hε (scK_pos M))
    refine ⟨δ / scK M, div_pos hδ (scK_pos M), fun y' _ hy'dist => ?_⟩
    have hQ : ∑ j, (y' j - y j) ^ 2 < δ ^ 2 := sc_sumSq_lt_of_dist_lt hδ hy'dist
    obtain ⟨c', hc'_eps, hc'_near⟩ := hδclause y' hQ
    have h1 : fderiv ℝ g y' = linMap c' := ((c1RealFD g y' c').mp hc'_eps).fderiv
    have h2 : fderiv ℝ g y = linMap c := ((c1RealFD g y c).mp hc_eps).fderiv
    rw [dist_eq_norm, h1, h2, ← sc_linMap_sub]
    calc ‖linMap (c' - c)‖ ≤ scK M * Real.sqrt (∑ j, ((c' - c) j) ^ 2) :=
          sc_linMap_norm_le (c' - c)
      _ = scK M * Real.sqrt (∑ j, (c' j - c j) ^ 2) := by simp only [Pi.sub_apply]
      _ < scK M * (ε / scK M) := by
          refine mul_lt_mul_of_pos_left ?_ (scK_pos M)
          rw [Real.sqrt_lt' (div_pos hε (scK_pos M))]
          exact hc'_near
      _ = ε := by
          have h : scK M ≠ 0 := ne_of_gt (scK_pos M)
          rw [show scK M * (ε / scK M) = ε * (scK M / scK M) by ring, div_self h, mul_one]
  · intro y hy
    obtain ⟨c, hc_eps, -⟩ := hclause y hy
    have hf : fderiv ℝ g y = linMap c := ((c1RealFD g y c).mp hc_eps).fderiv
    change HasFDerivAt g (fderiv ℝ g y) y
    rw [hf]
    exact (c1RealFD g y c).mp hc_eps

/-! ## 4. `ContDiffAt ℝ 1` implies `C1Pred` -/

/-- The backward direction of the equivalence. -/
theorem contDiffAt_to_c1Pred_slice {M : ℕ} (g : (Fin M → ℝ) → ℝ) (u : Fin M → ℝ)
    (h : ContDiffAt ℝ 1 g u) : C1Pred g u := by
  obtain ⟨f', u', hu', hcont, hderiv⟩ := contDiffAt_one_iff.mp h
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hu'
  refine ⟨r / 2, by linarith, fun y hy => ?_⟩
  have hy_norm : ‖y - u‖ < r / 2 := by
    have h1 : ‖y - u‖ ≤ Real.sqrt (∑ j, ((y - u) j) ^ 2) := sc_norm_le_sqrt_sumSq (y - u)
    have h2 : (∑ j, ((y - u) j) ^ 2) = ∑ j, (y j - u j) ^ 2 := by
      exact Finset.sum_congr rfl fun j _ => by simp
    rw [h2] at h1
    have h3 : Real.sqrt (∑ j, (y j - u j) ^ 2) < r / 2 := by
      rw [Real.sqrt_lt' (by linarith : (0 : ℝ) < r / 2)]
      exact hy
    linarith
  have hyu' : y ∈ u' := hball (Metric.mem_ball.mpr (by rw [dist_eq_norm]; linarith))
  refine ⟨linCoeff (f' y), ?_, ?_⟩
  · rw [c1RealFD, linMap_linCoeff]
    exact hderiv y hyu'
  · intro ε hε
    obtain ⟨δ₁, hδ₁, hδ₁c⟩ := Metric.continuousWithinAt_iff.mp (hcont y hyu')
      (ε / scK M) (div_pos hε (scK_pos M))
    refine ⟨min δ₁ (r / 2), lt_min hδ₁ (by linarith), fun y' hy' => ?_⟩
    have hmin : (0 : ℝ) < min δ₁ (r / 2) := lt_min hδ₁ (by linarith)
    have hy'_norm : ‖y' - y‖ < min δ₁ (r / 2) := by
      have h1 : ‖y' - y‖ ≤ Real.sqrt (∑ j, ((y' - y) j) ^ 2) := sc_norm_le_sqrt_sumSq (y' - y)
      have h2 : (∑ j, ((y' - y) j) ^ 2) = ∑ j, (y' j - y j) ^ 2 := by
        exact Finset.sum_congr rfl fun j _ => by simp
      rw [h2] at h1
      have h3 : Real.sqrt (∑ j, (y' j - y j) ^ 2) < min δ₁ (r / 2) := by
        rw [Real.sqrt_lt' hmin]
        exact hy'
      linarith
    have hdyu : dist y u < r / 2 := by rw [dist_eq_norm]; exact hy_norm
    have hdy'y : dist y' y < min δ₁ (r / 2) := by rw [dist_eq_norm]; exact hy'_norm
    have hy'u' : y' ∈ u' := hball (Metric.mem_ball.mpr (by
      calc dist y' u ≤ dist y' y + dist y u := dist_triangle _ _ _
        _ < min δ₁ (r / 2) + r / 2 := add_lt_add hdy'y hdyu
        _ ≤ r := by linarith [min_le_right δ₁ (r / 2)]))
    refine ⟨linCoeff (f' y'), ?_, ?_⟩
    · rw [c1RealFD, linMap_linCoeff]
      exact hderiv y' hy'u'
    · have hlt : dist y' y < δ₁ := by
        rw [dist_eq_norm]
        exact lt_of_lt_of_le hy'_norm (min_le_left δ₁ (r / 2))
      have hdist : dist (f' y') (f' y) < ε / scK M := hδ₁c hy'u' hlt
      have hnorm : ‖f' y' - f' y‖ < ε / scK M := by rwa [dist_eq_norm] at hdist
      have hK := scK_pos M
      calc ∑ j, (linCoeff (f' y') j - linCoeff (f' y) j) ^ 2
          = ∑ j, (linCoeff (f' y' - f' y) j) ^ 2 := by rw [sc_linCoeff_sub]; simp
        _ ≤ (M : ℝ) * ‖f' y' - f' y‖ ^ 2 := sc_sumSq_linCoeff_le (f' y' - f' y)
        _ ≤ (M : ℝ) * (ε / scK M) ^ 2 := mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hnorm) 2) (Nat.cast_nonneg M)
        _ = (M : ℝ) * (ε ^ 2 / scK M ^ 2) := by rw [div_pow]
        _ = ((M : ℝ) * ε ^ 2) / scK M ^ 2 := by ring
        _ < ε ^ 2 := by
            rw [div_lt_iff₀ (pow_pos hK 2)]
            nlinarith [mul_lt_mul_of_pos_right (natCast_lt_scK_sq M) (pow_pos hε 2)]

/-! ## 5. The equivalence -/

theorem c1RealPred_slice {M : ℕ} (g : (Fin M → ℝ) → ℝ) (u : Fin M → ℝ) :
    C1Pred g u ↔ ContDiffAt ℝ 1 g u :=
  ⟨c1Pred_to_contDiffAt_slice g u, contDiffAt_to_c1Pred_slice g u⟩

end Work.WilG4c
