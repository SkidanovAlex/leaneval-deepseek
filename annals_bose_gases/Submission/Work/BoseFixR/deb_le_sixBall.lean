import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.deb_cover
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.deb_le_sixBall` — the six-ball debit comparison

The target compares the integral over the *crescent* `C = {u | dist(u, ℓℤ³) < ‖u‖/3}` of the
autocorrelation `u ↦ ∫ x, W x W (x+u)` divided by the nearest-lattice distance, against the same
autocorrelation integrated over the six balls `ball (±ℓ eᵢ) ℓ/2` against the distance to the
respective centre.

The mechanism (with `W ≥ 0`, `W` supported in `ball 0 R`, `2R < ℓ`):

* the autocorrelation `g(u) = ∫ x, W x W (x+u)` vanishes for `‖u‖ ≥ 2R`;
* if `u` is in the crescent and `‖u‖ < 2R` then the nearby lattice point `lat ℓ n` has label
  `n = ±eᵢ` (because `‖lat ℓ n‖ < 4ℓ/3` forces `‖lat1 n‖ < 4/3`, and a nonzero label shorter than
  `4/3` must be `±eᵢ`) — this is the proved `Work.BoseFixR.deb_cover`;
* on `ball (lat ℓ n) (ℓ/2)` the nearest lattice point *is* the centre (`debLatD_ball`), so the
  crescent integrand `g(u)/dist(u, ℓℤ³)` coincides there with the corresponding term on the
  right-hand side, which is therefore pointwise dominated by the sum of the six terms;
* both sides are nonnegative, and each of the six terms is integrable, so `integral_mono_of_nonneg`
  finishes.

The two helper lemmas about the lattice ball (`debLatD_ball`, `debLatD_ball_neg`) and the
integrability of the six terms (`deb_pair_integrableOn`) are proved below.
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory Metric Filter

namespace Work.BoseFixR

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. The nearest lattice point on the ball of radius `ℓ/2` -/

/-- On `ball (lat ℓ n) (ℓ/2)` the nearest lattice point is the centre. -/
theorem debLatD_ball {ℓ : ℝ} (hℓ : 0 < ℓ) {n : Fin 3 → ℤ} {u : E3}
    (hu : u ∈ Metric.ball (lat ℓ n) (ℓ / 2)) : debLatD ℓ u = ‖u - lat ℓ n‖ := by
  have hmem : (Set.range (fun m : Fin 3 → ℤ => lat ℓ m)).Nonempty :=
    ⟨lat ℓ 0, Set.mem_range_self 0⟩
  refine le_antisymm (Metric.infDist_le_dist_of_mem (y := lat ℓ n) ⟨n, rfl⟩) ?_
  refine (Metric.le_infDist (x := u) (s := Set.range (fun m : Fin 3 → ℤ => lat ℓ m))
    hmem).mpr ?_
  rintro y ⟨m, rfl⟩
  rw [dist_eq_norm]
  by_cases hmn : m = n
  · subst hmn; exact le_rfl
  · have hden : ‖u - lat ℓ n‖ < ℓ / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hu
    have h1 : ℓ ≤ ‖lat ℓ m - lat ℓ n‖ := by
      rw [← deb_lat_sub, deb_norm_lat hℓ.le]
      have hne : m - n ≠ 0 := sub_ne_zero.mpr hmn
      nlinarith [deb_one_le_norm_lat1 hne, hℓ]
    have h2 : ‖lat ℓ m - lat ℓ n‖ ≤ ‖lat ℓ m - u‖ + ‖u - lat ℓ n‖ := by
      have h := norm_add_le (lat ℓ m - u) (u - lat ℓ n)
      simpa [sub_add_sub_cancel] using h
    rw [norm_sub_rev (lat ℓ m) u] at h2
    linarith

/-- The mirror form of `debLatD_ball`: on `ball (-(lat ℓ n)) (ℓ/2)` the nearest lattice point is
`-(lat ℓ n)`, so the distance to the lattice is `‖u + lat ℓ n‖`. -/
theorem debLatD_ball_neg {ℓ : ℝ} (hℓ : 0 < ℓ) {n : Fin 3 → ℤ} {u : E3}
    (hu : u ∈ Metric.ball (-(lat ℓ n)) (ℓ / 2)) : debLatD ℓ u = ‖u + lat ℓ n‖ := by
  have hmem : u ∈ Metric.ball (lat ℓ (-n)) (ℓ / 2) := by
    rw [deb_lat_neg]; simpa using hu
  rw [debLatD_ball hℓ hmem, deb_lat_neg, sub_neg_eq_add]

/-! ## 1. The six indicator terms -/

/-- The `i`-th positive-centre term of the six-ball comparison, as a function on `ℝ³`. -/
noncomputable def debTermP (ℓ : ℝ) (W : E3 → ℝ) (i : Fin 3) : E3 → ℝ :=
  (Metric.ball (debLC ℓ i) (ℓ / 2)).indicator (fun u => debPair W u / ‖u - debLC ℓ i‖)

/-- The `i`-th negative-centre term of the six-ball comparison, as a function on `ℝ³`. -/
noncomputable def debTermN (ℓ : ℝ) (W : E3 → ℝ) (i : Fin 3) : E3 → ℝ :=
  (Metric.ball (-(debLC ℓ i)) (ℓ / 2)).indicator (fun u => debPair W u / ‖u + debLC ℓ i‖)

lemma debTermP_eq (ℓ : ℝ) (W : E3 → ℝ) (i : Fin 3) :
    debTermP ℓ W i
      = (Metric.ball (debLC ℓ i) (ℓ / 2)).indicator
          (fun u => debPair W u / ‖u - debLC ℓ i‖) := rfl

lemma debTermN_eq (ℓ : ℝ) (W : E3 → ℝ) (i : Fin 3) :
    debTermN ℓ W i
      = (Metric.ball (-(debLC ℓ i)) (ℓ / 2)).indicator
          (fun u => debPair W u / ‖u + debLC ℓ i‖) := rfl

lemma debTermP_nonneg {ℓ : ℝ} {W : E3 → ℝ} (hWnn : 0 ≤ W) (i : Fin 3) (u : E3) :
    0 ≤ debTermP ℓ W i u := by
  rw [debTermP_eq]
  by_cases h : u ∈ Metric.ball (debLC ℓ i) (ℓ / 2)
  · rw [Set.indicator_of_mem h]
    exact div_nonneg (debPair_nonneg hWnn u) (norm_nonneg _)
  · rw [Set.indicator_of_notMem h]

lemma debTermN_nonneg {ℓ : ℝ} {W : E3 → ℝ} (hWnn : 0 ≤ W) (i : Fin 3) (u : E3) :
    0 ≤ debTermN ℓ W i u := by
  rw [debTermN_eq]
  by_cases h : u ∈ Metric.ball (-(debLC ℓ i)) (ℓ / 2)
  · rw [Set.indicator_of_mem h]
    exact div_nonneg (debPair_nonneg hWnn u) (norm_nonneg _)
  · rw [Set.indicator_of_notMem h]

lemma debTermP_of_mem {ℓ : ℝ} {W : E3 → ℝ} {i : Fin 3} {u : E3}
    (h : u ∈ Metric.ball (debLC ℓ i) (ℓ / 2)) :
    debTermP ℓ W i u = debPair W u / ‖u - debLC ℓ i‖ := by
  rw [debTermP_eq, Set.indicator_of_mem h]

lemma debTermN_of_mem {ℓ : ℝ} {W : E3 → ℝ} {i : Fin 3} {u : E3}
    (h : u ∈ Metric.ball (-(debLC ℓ i)) (ℓ / 2)) :
    debTermN ℓ W i u = debPair W u / ‖u + debLC ℓ i‖ := by
  rw [debTermN_eq, Set.indicator_of_mem h]

/-! ## 2. Integrability of the six terms -/

/-- **Integrability of the autocorrelation divided by the distance to a lattice point of norm
`ℓ`.**  On `ball v (ℓ/2)` with `‖v‖ = ℓ > 2R` the only singularity of `1/‖u - v‖` sits in the
region `‖u‖ > 2R` where the autocorrelation vanishes; elsewhere both numerator (`≤ C ∫‖W‖`) and
denominator (`≥ ℓ - 2R > 0`) are bounded. -/
theorem deb_pair_integrableOn {ℓ R : ℝ} (h2R : 2 * R < ℓ)
    {W : E3 → ℝ} (hW1 : Integrable W) (hWb : ∃ C, ∀ x, |W x| ≤ C)
    (hsupp : tsupport W ⊆ Metric.ball 0 R)
    {v : E3} (hv : ‖v‖ = ℓ) :
    IntegrableOn (fun u => debPair W u / ‖u - v‖) (Metric.ball v (ℓ / 2)) volume := by
  obtain ⟨C, hC⟩ := hWb
  set M : ℝ := max C 0 * ∫ x, ‖W x‖ with hM
  have hMnn : 0 ≤ M :=
    mul_nonneg (le_max_right _ _) (integral_nonneg fun x => norm_nonneg (W x))
  -- the autocorrelation is bounded by `M`
  have hbdd : ∀ u, |debPair W u| ≤ M := by
    intro u
    have h1 : ‖debPair W u‖ ≤ ∫ x, ‖W x * W (x + u)‖ := norm_integral_le_integral_norm _
    have h2 : ∫ x, ‖W x * W (x + u)‖ ≤ ∫ x, max C 0 * ‖W x‖ := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
        ((hW1.norm).const_mul (max C 0)) (Eventually.of_forall fun x => ?_)
      show ‖W x * W (x + u)‖ ≤ max C 0 * ‖W x‖
      rw [norm_mul]
      have hx : ‖W (x + u)‖ ≤ max C 0 :=
        le_trans (by simpa [Real.norm_eq_abs] using hC (x + u)) (le_max_left _ _)
      calc ‖W x‖ * ‖W (x + u)‖ ≤ ‖W x‖ * max C 0 := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
        _ = max C 0 * ‖W x‖ := by ring
    calc |debPair W u| = ‖debPair W u‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x, ‖W x * W (x + u)‖ := h1
      _ ≤ ∫ x, max C 0 * ‖W x‖ := h2
      _ = M := by rw [hM, integral_const_mul]
  -- the autocorrelation vanishes where `2R ≤ ‖u‖`
  have hzero : ∀ u, 2 * R ≤ ‖u‖ → debPair W u = 0 := fun u hu =>
    debPair_eq_zero_of_norm_ge hsupp hu
  have hden_pos : 0 < ℓ - 2 * R := by linarith
  refine IntegrableOn.of_bound (Metric.isBounded_ball.measure_lt_top) ?_ (M / (ℓ - 2 * R)) ?_
  · have hnorm : AEMeasurable (fun u : E3 => ‖u - v‖) volume :=
      (continuous_norm.comp (continuous_id.sub continuous_const)).aemeasurable
    have hg : AEStronglyMeasurable (fun u : E3 => (‖u - v‖)⁻¹) volume :=
      (measurable_inv.comp_aemeasurable hnorm).aestronglyMeasurable
    have hfg : AEStronglyMeasurable (fun u : E3 => debPair W u * (‖u - v‖)⁻¹) volume :=
      (debPair_aestronglyMeasurable hW1).mul hg
    simpa [div_eq_mul_inv] using hfg.mono_measure Measure.restrict_le_self
  · filter_upwards with u
    by_cases hcase : 2 * R ≤ ‖u‖
    · rw [hzero u hcase, zero_div, norm_zero]
      positivity
    · push Not at hcase
      have hden : ℓ - 2 * R ≤ ‖u - v‖ := by
        have h := abs_norm_sub_norm_le v u
        rw [norm_sub_rev] at h
        have h1 : ℓ - ‖u‖ ≤ ‖u - v‖ := by
          calc ℓ - ‖u‖ = ‖v‖ - ‖u‖ := by rw [hv]
            _ ≤ |‖v‖ - ‖u‖| := le_abs_self _
            _ ≤ ‖u - v‖ := h
        linarith
      have hdiv : ‖debPair W u / ‖u - v‖‖ = |debPair W u| / ‖u - v‖ := by
        rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (norm_nonneg _)]
      rw [hdiv]
      exact div_le_div₀ hMnn (hbdd u) hden_pos hden

/-! ## 3. The target -/

theorem deb_le_sixBall {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) (h2R : 2 * R < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW1 : MeasureTheory.Integrable W) (hWb : ∃ C, ∀ x, |W x| ≤ C)
    (hWnn : 0 ≤ W) (hsupp : tsupport W ⊆ Metric.ball 0 R) :
    (∫ u in {u : EuclideanSpace ℝ (Fin 3) | Metric.infDist u (Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n))
            < ‖u‖ / 3},
        (∫ x, W x * W (x + u))
          / Metric.infDist u (Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n)))
      ≤ (∑ i : Fin 3, ∫ u in Metric.ball (Work.BoseFixR.lat ℓ (Pi.single i (1 : ℤ))) (ℓ / 2),
            (∫ x, W x * W (x + u)) / ‖u - Work.BoseFixR.lat ℓ (Pi.single i (1 : ℤ))‖)
        + (∑ i : Fin 3, ∫ u in Metric.ball (-(Work.BoseFixR.lat ℓ (Pi.single i (1 : ℤ)))) (ℓ / 2),
            (∫ x, W x * W (x + u)) / ‖u + Work.BoseFixR.lat ℓ (Pi.single i (1 : ℤ))‖) := by
  change (∫ u in debSet ℓ, debPair W u / debLatD ℓ u)
      ≤ (∑ i : Fin 3, ∫ u in Metric.ball (debLC ℓ i) (ℓ / 2), debPair W u / ‖u - debLC ℓ i‖)
        + (∑ i : Fin 3, ∫ u in Metric.ball (-(debLC ℓ i)) (ℓ / 2), debPair W u / ‖u + debLC ℓ i‖)
  -- integrability of the six terms
  have hPint : ∀ i : Fin 3, Integrable (debTermP ℓ W i) volume := by
    intro i
    refine (integrable_indicator_iff measurableSet_ball).mpr ?_
    exact deb_pair_integrableOn h2R hW1 hWb hsupp (deb_norm_lc hℓ.le i)
  have hNint : ∀ i : Fin 3, Integrable (debTermN ℓ W i) volume := by
    intro i
    refine (integrable_indicator_iff measurableSet_ball).mpr ?_
    have hv : ‖-(debLC ℓ i)‖ = ℓ := by rw [norm_neg, deb_norm_lc hℓ.le i]
    rw [show (fun u : E3 => debPair W u / ‖u + debLC ℓ i‖)
        = (fun u : E3 => debPair W u / ‖u - (-(debLC ℓ i))‖) from by
      funext u; rw [sub_neg_eq_add]]
    exact deb_pair_integrableOn h2R hW1 hWb hsupp hv
  have hPsum : Integrable (fun u => ∑ i : Fin 3, debTermP ℓ W i u) volume :=
    integrable_finsetSum Finset.univ fun i _ => hPint i
  have hNsum : Integrable (fun u => ∑ i : Fin 3, debTermN ℓ W i u) volume :=
    integrable_finsetSum Finset.univ fun i _ => hNint i
  -- the pointwise comparison
  have hpoint : ∀ u : E3,
      (debSet ℓ).indicator (fun u => debPair W u / debLatD ℓ u) u
        ≤ (∑ i : Fin 3, debTermP ℓ W i u) + (∑ i : Fin 3, debTermN ℓ W i u) := by
    intro u
    have hnonneg : 0 ≤ (∑ i : Fin 3, debTermP ℓ W i u) + (∑ i : Fin 3, debTermN ℓ W i u) :=
      add_nonneg (Finset.sum_nonneg fun i _ => debTermP_nonneg hWnn i u)
        (Finset.sum_nonneg fun i _ => debTermN_nonneg hWnn i u)
    by_cases hu : u ∈ debSet ℓ
    · rw [Set.indicator_of_mem hu]
      by_cases h2u : ‖u‖ < 2 * R
      · obtain ⟨i, hi | hi⟩ := deb_cover hℓ h2R hu h2u
        · have hQi : debLatD ℓ u = ‖u - debLC ℓ i‖ := by
            have h := debLatD_ball (ℓ := ℓ) hℓ (n := Pi.single i (1 : ℤ)) hi
            simpa [debLC] using h
          have hval : debTermP ℓ W i u = debPair W u / debLatD ℓ u := by
            rw [debTermP_of_mem hi, hQi]
          calc debPair W u / debLatD ℓ u = debTermP ℓ W i u := hval.symm
            _ ≤ ∑ j : Fin 3, debTermP ℓ W j u :=
                Finset.single_le_sum (fun j _ => debTermP_nonneg hWnn j u) (Finset.mem_univ i)
            _ ≤ (∑ j : Fin 3, debTermP ℓ W j u) + (∑ j : Fin 3, debTermN ℓ W j u) :=
                le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => debTermN_nonneg hWnn j u)
        · have hQi : debLatD ℓ u = ‖u + debLC ℓ i‖ := by
            have h := debLatD_ball_neg (ℓ := ℓ) hℓ (n := Pi.single i (1 : ℤ)) hi
            simpa [debLC] using h
          have hval : debTermN ℓ W i u = debPair W u / debLatD ℓ u := by
            rw [debTermN_of_mem hi, hQi]
          calc debPair W u / debLatD ℓ u = debTermN ℓ W i u := hval.symm
            _ ≤ ∑ j : Fin 3, debTermN ℓ W j u :=
                Finset.single_le_sum (fun j _ => debTermN_nonneg hWnn j u) (Finset.mem_univ i)
            _ ≤ (∑ j : Fin 3, debTermP ℓ W j u) + (∑ j : Fin 3, debTermN ℓ W j u) :=
                le_add_of_nonneg_left (Finset.sum_nonneg fun j _ => debTermP_nonneg hWnn j u)
      · have hz : debPair W u = 0 := debPair_eq_zero_of_norm_ge hsupp (le_of_not_gt h2u)
        rw [hz, zero_div]
        exact hnonneg
    · rw [Set.indicator_of_notMem hu]
      exact hnonneg
  -- the two sides as integrals
  have hleft : (∫ u, (debSet ℓ).indicator (fun u => debPair W u / debLatD ℓ u) u)
      = ∫ u in debSet ℓ, debPair W u / debLatD ℓ u :=
    integral_indicator (debSet_measurable ℓ)
  have hPeq : ∀ i : Fin 3, (∫ u, debTermP ℓ W i u)
      = ∫ u in Metric.ball (debLC ℓ i) (ℓ / 2), debPair W u / ‖u - debLC ℓ i‖ := by
    intro i
    rw [debTermP_eq ℓ W i]
    exact integral_indicator measurableSet_ball
  have hNeq : ∀ i : Fin 3, (∫ u, debTermN ℓ W i u)
      = ∫ u in Metric.ball (-(debLC ℓ i)) (ℓ / 2), debPair W u / ‖u + debLC ℓ i‖ := by
    intro i
    rw [debTermN_eq ℓ W i]
    exact integral_indicator measurableSet_ball
  have hmono : (∫ u, (debSet ℓ).indicator (fun u => debPair W u / debLatD ℓ u) u)
      ≤ ∫ u, (∑ i : Fin 3, debTermP ℓ W i u) + (∑ i : Fin 3, debTermN ℓ W i u) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun u => ?_) (hPsum.add hNsum)
      (Eventually.of_forall hpoint)
    by_cases h : u ∈ debSet ℓ
    · rw [Set.indicator_of_mem h]
      exact div_nonneg (debPair_nonneg hWnn u) (debLatD_nonneg ℓ u)
    · rw [Set.indicator_of_notMem h]
      exact le_refl 0
  have hright : (∫ u, (∑ i : Fin 3, debTermP ℓ W i u) + (∑ i : Fin 3, debTermN ℓ W i u))
      = (∑ i : Fin 3, ∫ u in Metric.ball (debLC ℓ i) (ℓ / 2), debPair W u / ‖u - debLC ℓ i‖)
        + (∑ i : Fin 3, ∫ u in Metric.ball (-(debLC ℓ i)) (ℓ / 2),
            debPair W u / ‖u + debLC ℓ i‖) := by
    have hstep : (∫ u, (∑ i : Fin 3, debTermP ℓ W i u) + (∑ i : Fin 3, debTermN ℓ W i u))
        = (∫ u, ∑ i : Fin 3, debTermP ℓ W i u)
          + (∫ u, ∑ i : Fin 3, debTermN ℓ W i u) :=
      integral_add hPsum hNsum
    have hA : (∑ i : Fin 3, ∫ u, debTermP ℓ W i u)
        = ∑ i : Fin 3, ∫ u in Metric.ball (debLC ℓ i) (ℓ / 2),
            debPair W u / ‖u - debLC ℓ i‖ :=
      Finset.sum_congr rfl fun i _ => hPeq i
    have hB : (∑ i : Fin 3, ∫ u, debTermN ℓ W i u)
        = ∑ i : Fin 3, ∫ u in Metric.ball (-(debLC ℓ i)) (ℓ / 2),
            debPair W u / ‖u + debLC ℓ i‖ :=
      Finset.sum_congr rfl fun i _ => hNeq i
    rw [hstep, integral_finsetSum Finset.univ (fun i _ => hPint i), hA,
      integral_finsetSum Finset.univ (fun i _ => hNint i), hB]
  rw [hleft, hright] at hmono
  exact hmono

end Work.BoseFixR
