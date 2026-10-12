import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Defs
import Submission.Work.BoseFixB1S.chiSmallCorrDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.chiSmallB_autocorr_aux` — the geometric half of the `χ_B`-autocorrelation bound

This module contains the *geometric* (scaling + plateau) lemmas that turn the
three-dimensional correlation estimates about `chiSmall` into the correlation bound
for the sliding cutoff `chiSmallB M ℓ d 0 x = χ(x/ℓ)·χ_M(x/(ℓd))`:

* `chiMass_le_massB1S` — the mass bound
  `chiMass M ℓ d 0 ≤ chiSupAbs²·(ℓd)³·∫_{|y_j| ≤ 1/(2d)} χ_M(y)² dy`
  (`χ(x/ℓ) ≤ chiSupAbs` pointwise and `χ(x/ℓ)` vanishes off `‖x‖ ≤ ℓ/2`, which after
  `x = (ℓd)·y` sits inside the polydisc of half-side `1/(2d)`).
* `autocorr_ge_cubeB1S` — the lower bound
  `chiSupAbs²·(ℓd)³·∫_{cube b (s/2)} χ_M(y)χ_M(y−s) dy ≤ ∫_x χ_B(x)χ_B(x−z) dx`
  for `s = (ℓd)⁻¹·z`, `b = 7/(32√3·d)` and `‖z‖ ≤ min(ℓd, ℓ)/16`: on the cube both
  `χ`-factors are at their plateau value `chiSupAbs` (`chiBase = 1` on `‖·‖ ≤ 1/4`).
* `corr1D_big` — the `b ≥ 1/2` degenerate case of the per-coordinate correlation
  inequality: there the shift is irrelevant (`∫_{[-b,b]} f = ∫_ℝ f`) and the ratio
  `b/T ≤ 1` makes the inequality trivial.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The polydisc (coordinate cube) of half-side `T` centred at the origin. -/
def polydisc3 (T : ℝ) : Set E3 := {y : E3 | ∀ j : Fin 3, |y.ofLp j| ≤ T}

/-- The cube of half-side `b` centred at `s/2`. -/
def cubeHalf (s : E3) (b : ℝ) : Set E3 :=
  {y : E3 | ∀ j : Fin 3, |y.ofLp j - s.ofLp j / 2| ≤ b}

lemma isClosed_polydisc3 (T : ℝ) : IsClosed (polydisc3 T) := by
  have h : polydisc3 T = ⋂ j : Fin 3, {y : E3 | |y.ofLp j| ≤ T} := by
    ext y
    simp [polydisc3]
  rw [h]
  refine isClosed_iInter (fun j => ?_)
  exact isClosed_Iic.preimage
    (continuous_abs.comp (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) j))

lemma measurableSet_polydisc3 (T : ℝ) : MeasurableSet (polydisc3 T) :=
  (isClosed_polydisc3 T).measurableSet

lemma isClosed_cubeHalf (s : E3) (b : ℝ) : IsClosed (cubeHalf s b) := by
  have h : cubeHalf s b = ⋂ j : Fin 3, {y : E3 | |y.ofLp j - s.ofLp j / 2| ≤ b} := by
    ext y
    simp [cubeHalf]
  rw [h]
  refine isClosed_iInter (fun j => ?_)
  exact isClosed_Iic.preimage (continuous_abs.comp
    ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) j).sub continuous_const))

lemma measurableSet_cubeHalf (s : E3) (b : ℝ) : MeasurableSet (cubeHalf s b) :=
  (isClosed_cubeHalf s b).measurableSet

/-- **Coordinatewise bound implies the norm bound**: `‖y‖ ≤ √3·r` if every coordinate
of `y` is bounded by `r ≥ 0`. -/
lemma norm_le_sqrt3_mul {y : E3} {r : ℝ} (hr : 0 ≤ r) (h : ∀ j : Fin 3, |y.ofLp j| ≤ r) :
    ‖y‖ ≤ Real.sqrt 3 * r := by
  have hsq : ‖y‖ ^ 2 = ∑ j : Fin 3, |y.ofLp j| ^ 2 := by
    simpa using (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin 3 => ℝ) y)
  have hsum : (∑ j : Fin 3, |y.ofLp j| ^ 2) ≤ 3 * r ^ 2 := by
    calc
      (∑ j : Fin 3, |y.ofLp j| ^ 2) ≤ ∑ _j : Fin 3, r ^ 2 :=
        Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (abs_nonneg _) (h j) 2)
      _ = 3 * r ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have h2 : ‖y‖ ^ 2 ≤ 3 * r ^ 2 := by rw [hsq]; exact hsum
  have h3 : Real.sqrt (‖y‖ ^ 2) ≤ Real.sqrt (3 * r ^ 2) := Real.sqrt_le_sqrt h2
  rw [Real.sqrt_sq (norm_nonneg y), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3) (r ^ 2),
    Real.sqrt_sq_eq_abs, abs_of_nonneg hr] at h3
  exact h3

/-- The plateau value of the corpus bump: on `‖x‖ ≤ 1/4`, `χ(x) = chiSupAbs`. -/
lemma chi_eq_chiSupAbs_of_norm_le {x : E3} (hx : ‖x‖ ≤ 1 / 4) : chi x = chiSupAbs := by
  have hs : 0 < Real.sqrt chiNormSq := Real.sqrt_pos.mpr chiNormSq_pos
  rw [chi, chiBase_eq_one_of_norm_le hx, chiSupAbs, one_div]

/-- **The `ℓ`-factors are at their plateau on the core cube.**  For `b = 7/(32√3·d)`,
`s = (ℓd)⁻¹·z` and `y` in the cube `|y_j − s_j/2| ≤ b`, both `χ_ℓ((ℓd)·y)` and
`χ_ℓ((ℓd)·y − z)` take the plateau value `chiSupAbs`, as soon as `‖z‖/ℓ ≤ 1/16`
(i.e. `‖d·s‖ ≤ 1/16`). -/
lemma chiScale_plateau_cube {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {z : E3}
    (hz2 : ‖z‖ ≤ ℓ / 16) {y : E3}
    (hy : y ∈ cubeHalf ((ℓ * d)⁻¹ • z) (7 / (32 * Real.sqrt 3 * d))) :
    chiScale ℓ ((ℓ * d) • y) = chiSupAbs ∧
      chiScale ℓ ((ℓ * d) • y - z) = chiSupAbs := by
  have hL : 0 < ℓ * d := mul_pos hℓ hd
  set s : E3 := (ℓ * d)⁻¹ • z with hsdef
  set c : E3 := (2 : ℝ)⁻¹ • s with hcdef
  have hds_eq : d • s = ℓ⁻¹ • z := by
    rw [hsdef, smul_smul]
    congr 1
    field_simp
  have hds : ‖d • s‖ ≤ 1 / 16 := by
    rw [hds_eq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
    calc ℓ⁻¹ * ‖z‖ ≤ ℓ⁻¹ * (ℓ / 16) :=
          mul_le_mul_of_nonneg_left hz2 (le_of_lt (inv_pos.mpr hℓ))
      _ = 1 / 16 := by field_simp
  have hcs : ‖c‖ = ‖s‖ / 2 := by
    rw [hcdef, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
    ring
  -- the cube's coordinate bound gives `‖y − c‖ ≤ 7/(32d)`
  have hcj : ∀ j : Fin 3, c.ofLp j = s.ofLp j / 2 := by
    intro j
    rw [hcdef, PiLp.smul_apply, smul_eq_mul, div_eq_inv_mul]
  have hcoord : ∀ j : Fin 3, |(y - c).ofLp j| ≤ 7 / (32 * Real.sqrt 3 * d) := by
    intro j
    have hsub : (y - c).ofLp j = y.ofLp j - s.ofLp j / 2 := by
      rw [PiLp.sub_apply, hcj j]
    rw [hsub]
    exact hy j
  have hdist : ‖y - c‖ ≤ 7 / (32 * d) := by
    have hbnd := norm_le_sqrt3_mul (y := y - c) (r := 7 / (32 * Real.sqrt 3 * d))
      (by positivity) hcoord
    have hval : Real.sqrt 3 * (7 / (32 * Real.sqrt 3 * d)) = 7 / (32 * d) := by
      field_simp
    rwa [hval] at hbnd
  have hA : ‖d • (y - c)‖ ≤ 7 / 32 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd]
    calc d * ‖y - c‖ ≤ d * (7 / (32 * d)) := mul_le_mul_of_nonneg_left hdist (le_of_lt hd)
      _ = 7 / 32 := by field_simp
  have hB : ‖d • c‖ ≤ 1 / 32 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd, hcs]
    have h1 : ‖d • s‖ = d * ‖s‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd]
    calc d * (‖s‖ / 2) = d * ‖s‖ / 2 := by ring
      _ = ‖d • s‖ / 2 := by rw [h1]
      _ ≤ (1 / 16) / 2 := by linarith
      _ = 1 / 32 := by norm_num
  have hcc : c + c = s := by
    rw [hcdef, ← add_smul]
    norm_num
  have h1n : ‖d • y‖ ≤ 1 / 4 := by
    have hsplit : d • y = d • (y - c) + d • c := by rw [← smul_add]; congr 1; abel
    calc ‖d • y‖ = ‖d • (y - c) + d • c‖ := by rw [hsplit]
      _ ≤ ‖d • (y - c)‖ + ‖d • c‖ := norm_add_le _ _
      _ ≤ 7 / 32 + 1 / 32 := add_le_add hA hB
      _ = 1 / 4 := by norm_num
  have h2n : ‖d • (y - s)‖ ≤ 1 / 4 := by
    have hys : y - s = (y - c) - c := by
      rw [← hcc]
      abel
    have hsplit : d • (y - s) = d • (y - c) - d • c := by rw [hys, smul_sub]
    calc ‖d • (y - s)‖ = ‖d • (y - c) - d • c‖ := by rw [hsplit]
      _ ≤ ‖d • (y - c)‖ + ‖d • c‖ := norm_sub_le _ _
      _ ≤ 7 / 32 + 1 / 32 := add_le_add hA hB
      _ = 1 / 4 := by norm_num
  constructor
  · have hLy : (ℓ * d) • y = ℓ • (d • y) := by rw [smul_smul]
    rw [hLy, chiScale_apply_smul (ne_of_gt hℓ) (d • y)]
    exact chi_eq_chiSupAbs_of_norm_le h1n
  · have hz' : z = (ℓ * d) • s := by
      rw [hsdef, smul_smul, mul_inv_cancel₀ (ne_of_gt hL), one_smul]
    have harg : (ℓ * d) • y - z = ℓ • (d • (y - s)) := by
      rw [hz', ← smul_sub, smul_smul]
    rw [harg, chiScale_apply_smul (ne_of_gt hℓ) (d • (y - s))]
    exact chi_eq_chiSupAbs_of_norm_le h2n

/-! ## The mass bound -/

lemma chiSmallB_zero_nonneg (M : ℕ) (ℓ d : ℝ) (x : E3) :
    0 ≤ chiSmallB M ℓ d 0 x :=
  mul_nonneg (chiScale_nonneg ℓ x) (chiSmall_nonneg M _)

lemma chiSmallB_nonneg (M : ℕ) (ℓ d : ℝ) (x : E3) :
    0 ≤ chiSmallB M ℓ d 0 x := chiSmallB_zero_nonneg M ℓ d x

lemma cubeHalf_coord {s : E3} {b : ℝ} {y : E3} (hy : y ∈ cubeHalf s b) (j : Fin 3) :
    |y.ofLp j - s.ofLp j / 2| ≤ b := hy j

/-- The `(ℓd)·y` form of the sliding cutoff at `u = 0`. -/
lemma chiSmallB_smul_eq (M : ℕ) {ℓ d : ℝ} (hℓ : ℓ ≠ 0) (hd : d ≠ 0) (y : E3) :
    chiSmallB M ℓ d 0 ((ℓ * d) • y) = chi (d • y) * chiSmall M y := by
  have hL : (ℓ * d) ≠ 0 := mul_ne_zero hℓ hd
  have h1 : chiScale ℓ ((ℓ * d) • y) = chi (d • y) := by
    rw [show (ℓ * d) • y = ℓ • (d • y) by rw [smul_smul],
      chiScale_apply_smul hℓ]
  have h2 : chiSmall M ((ℓ * d)⁻¹ • ((ℓ * d) • y)) = chiSmall M y := by
    rw [smul_smul, inv_mul_cancel₀ hL, one_smul]
  rw [chiSmallB, sub_zero, h1, h2]

/-- **The mass bound for the sliding cutoff**: `chiMass M ℓ d 0` is at most
`chiSupAbs²·(ℓd)³` times the mass of `χ_M` over the polydisc of half-side `1/(2d)`. -/
lemma chiMass_le_massB1S {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    Work.SmallBoxSliding.chiMass M ℓ d 0
      ≤ chiSupAbs ^ 2 * (ℓ * d) ^ 3
          * ∫ y in polydisc3 (1 / (2 * d)), (chiSmall M y) ^ 2 := by
  have hL : 0 < ℓ * d := mul_pos hℓ hd
  have hχcs : HasCompactSupport (fun y : E3 => (chiSmall M y) ^ 2) := by
    refine (chiSmall_hasCompactSupport hM).mono ?_
    intro y hy
    rw [Function.mem_support] at hy ⊢
    intro hc
    exact hy (by rw [hc]; norm_num)
  have hχint : Integrable (fun y : E3 => (chiSmall M y) ^ 2) :=
    ((chiSmall_continuous hM).pow 2).integrable_of_hasCompactSupport hχcs
  rw [Work.SmallBoxSliding.chiMass_def]
  rw [integral_comp_smul_right (g := fun x : E3 => (chiSmallB M ℓ d 0 x) ^ 2) hL]
  have hkey : (∫ y : E3, (chiSmallB M ℓ d 0 ((ℓ * d) • y)) ^ 2)
      ≤ chiSupAbs ^ 2 * ∫ y in polydisc3 (1 / (2 * d)), (chiSmall M y) ^ 2 := by
    have hpt : ∀ y : E3, (chiSmallB M ℓ d 0 ((ℓ * d) • y)) ^ 2
        ≤ chiSupAbs ^ 2 * (polydisc3 (1 / (2 * d))).indicator
            (fun y => (chiSmall M y) ^ 2) y := by
      intro y
      by_cases hy : y ∈ polydisc3 (1 / (2 * d))
      · rw [Set.indicator_of_mem hy, chiSmallB_smul_eq M (ne_of_gt hℓ) (ne_of_gt hd) y,
          mul_pow]
        have hchi : chi (d • y) ^ 2 ≤ chiSupAbs ^ 2 := by
          have h1 : chi (d • y) ≤ chiSupAbs := by
            simpa [abs_of_nonneg (chi_nonneg _)] using chi_abs_le_sup (d • y)
          exact pow_le_pow_left₀ (chi_nonneg _) h1 2
        exact mul_le_mul_of_nonneg_right hchi (sq_nonneg _)
      · rw [Set.indicator_of_notMem hy, mul_zero]
        have hnorm : 1 / (2 * d) < ‖y‖ := by
          have hy' := hy
          simp only [polydisc3, Set.mem_ofPred_eq, not_forall] at hy'
          obtain ⟨j, hj⟩ := hy'
          have h1 : 1 / (2 * d) < |y.ofLp j| := lt_of_not_ge hj
          have h2 : |y.ofLp j| ≤ ‖y‖ := by
            simpa using PiLp.norm_apply_le (p := 2) (β := fun _ : Fin 3 => ℝ) y j
          linarith
        have hdy : 1 / 2 < ‖d • y‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd]
          calc 1 / 2 = d * (1 / (2 * d)) := by field_simp
            _ < d * ‖y‖ := mul_lt_mul_of_pos_left hnorm hd
        have hz : chi (d • y) = 0 := by
          rw [chi, chiBase_eq_zero_of_norm_gt (d • y) hdy]
          simp
        rw [chiSmallB_smul_eq M (ne_of_gt hℓ) (ne_of_gt hd) y, hz]
        ring_nf
        exact le_refl 0
    have hint : Integrable (fun y : E3 => chiSupAbs ^ 2 *
        (polydisc3 (1 / (2 * d))).indicator (fun y => (chiSmall M y) ^ 2) y) := by
      refine Integrable.const_mul ?_ _
      refine Integrable.mono' hχint
        (hχint.aestronglyMeasurable.indicator (measurableSet_polydisc3 _)) ?_
      filter_upwards with y
      by_cases hy : y ∈ polydisc3 (1 / (2 * d))
      · rw [Set.indicator_of_mem hy, Real.norm_of_nonneg (sq_nonneg _)]
      · rw [Set.indicator_of_notMem hy, norm_zero]
        exact sq_nonneg (chiSmall M y)
    calc (∫ y : E3, (chiSmallB M ℓ d 0 ((ℓ * d) • y)) ^ 2)
        ≤ ∫ y : E3, chiSupAbs ^ 2 * (polydisc3 (1 / (2 * d))).indicator
            (fun y => (chiSmall M y) ^ 2) y :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => sq_nonneg _)) hint
            (Filter.Eventually.of_forall hpt)
      _ = chiSupAbs ^ 2 * ∫ y in polydisc3 (1 / (2 * d)), (chiSmall M y) ^ 2 := by
          rw [integral_const_mul, integral_indicator (measurableSet_polydisc3 _)]
  calc (ℓ * d) ^ 3 * (∫ y : E3, (chiSmallB M ℓ d 0 ((ℓ * d) • y)) ^ 2)
      ≤ (ℓ * d) ^ 3 *
          (chiSupAbs ^ 2 * ∫ y in polydisc3 (1 / (2 * d)), (chiSmall M y) ^ 2) :=
        mul_le_mul_of_nonneg_left hkey (pow_nonneg (le_of_lt hL) 3)
    _ = chiSupAbs ^ 2 * (ℓ * d) ^ 3
          * ∫ y in polydisc3 (1 / (2 * d)), (chiSmall M y) ^ 2 := by ring

/-! ## The autocorrelation lower bound -/

/-- **The autocorrelation lower bound for the sliding cutoff.**  With `s = (ℓd)⁻¹·z` and
`b = 7/(32√3·d)`, on the cube `|y_j − s_j/2| ≤ b` both `χ`-factors of `chiSmallB` equal
`chiSupAbs`, so the scaled autocorrelation dominates `chiSupAbs²(ℓd)³` times the cube
integral of `χ_M(y)χ_M(y−s)`. -/
lemma autocorr_ge_cubeB1S {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {z : E3} (hz : ‖z‖ ≤ ℓ * d / 16) (hz2 : ‖z‖ ≤ ℓ / 16) :
    chiSupAbs ^ 2 * (ℓ * d) ^ 3
        * (∫ y in cubeHalf ((ℓ * d)⁻¹ • z) (7 / (32 * Real.sqrt 3 * d)),
            chiSmall M y * chiSmall M (y - (ℓ * d)⁻¹ • z))
      ≤ ∫ x : E3, chiSmallB M ℓ d 0 x * chiSmallB M ℓ d 0 (x - z) := by
  have hL : 0 < ℓ * d := mul_pos hℓ hd
  set s : E3 := (ℓ * d)⁻¹ • z with hsdef
  set b : ℝ := 7 / (32 * Real.sqrt 3 * d) with hbdef
  have hcont : Continuous fun y : E3 =>
      chiSmallB M ℓ d 0 ((ℓ * d) • y) * chiSmallB M ℓ d 0 ((ℓ * d) • y - z) :=
    ((chiSmallB_continuous hM hℓ hd 0).comp (continuous_const_smul _)).mul
      ((chiSmallB_continuous hM hℓ hd 0).comp
        ((continuous_const_smul _).sub continuous_const))
  have hcs : HasCompactSupport fun y : E3 =>
      chiSmallB M ℓ d 0 ((ℓ * d) • y) * chiSmallB M ℓ d 0 ((ℓ * d) • y - z) := by
    change IsCompact (closure (Function.support fun y : E3 =>
      chiSmallB M ℓ d 0 ((ℓ * d) • y) * chiSmallB M ℓ d 0 ((ℓ * d) • y - z)))
    have hsub : closure (Function.support fun y : E3 =>
        chiSmallB M ℓ d 0 ((ℓ * d) • y) * chiSmallB M ℓ d 0 ((ℓ * d) • y - z))
        ⊆ Metric.closedBall (0 : E3) (1 / (2 * d)) := by
      refine closure_minimal ?_ Metric.isClosed_closedBall
      intro y hy
      rw [Function.mem_support] at hy
      rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hcon
      rw [not_le] at hcon
      have hdy : 1 / 2 < ‖d • y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd]
        calc 1 / 2 = d * (1 / (2 * d)) := by field_simp
          _ < d * ‖y‖ := mul_lt_mul_of_pos_left hcon hd
      have hz0 : chi (d • y) = 0 := by
        rw [chi, chiBase_eq_zero_of_norm_gt (d • y) hdy]
        simp
      exact hy (by
        rw [chiSmallB_smul_eq M (ne_of_gt hℓ) (ne_of_gt hd) y, hz0]
        ring)
    exact IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E3) (1 / (2 * d)))
      isClosed_closure hsub
  have hint : Integrable fun y : E3 =>
      chiSmallB M ℓ d 0 ((ℓ * d) • y) * chiSmallB M ℓ d 0 ((ℓ * d) • y - z) :=
    hcont.integrable_of_hasCompactSupport hcs
  -- the pointwise identity on the cube
  have hpt : ∀ y ∈ cubeHalf s b,
      chiSmallB M ℓ d 0 ((ℓ * d) • y) * chiSmallB M ℓ d 0 ((ℓ * d) • y - z)
        = chiSupAbs ^ 2 * (chiSmall M y * chiSmall M (y - s)) := by
    intro y hy
    obtain ⟨h1, h2⟩ := chiScale_plateau_cube hℓ hd hz2 (y := y) (by simpa [s, b] using hy)
    have harg1 : (ℓ * d)⁻¹ • ((ℓ * d) • y) = y := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hL), one_smul]
    have harg2 : (ℓ * d)⁻¹ • ((ℓ * d) • y - z) = y - s := by
      rw [smul_sub, harg1, hsdef]
    simp only [chiSmallB, sub_zero]
    rw [harg1, harg2, h1, h2]
    ring
  have hnn : ∀ y : E3, 0 ≤ chiSmallB M ℓ d 0 ((ℓ * d) • y)
      * chiSmallB M ℓ d 0 ((ℓ * d) • y - z) :=
    fun y => mul_nonneg (chiSmallB_zero_nonneg M ℓ d _) (chiSmallB_zero_nonneg M ℓ d _)
  have hle : (∫ y in cubeHalf s b, chiSmallB M ℓ d 0 ((ℓ * d) • y)
        * chiSmallB M ℓ d 0 ((ℓ * d) • y - z))
      ≤ ∫ y : E3, chiSmallB M ℓ d 0 ((ℓ * d) • y)
          * chiSmallB M ℓ d 0 ((ℓ * d) • y - z) :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
  have hcongr : (∫ y in cubeHalf s b, chiSmallB M ℓ d 0 ((ℓ * d) • y)
        * chiSmallB M ℓ d 0 ((ℓ * d) • y - z))
      = chiSupAbs ^ 2 * ∫ y in cubeHalf s b, chiSmall M y * chiSmall M (y - s) := by
    rw [← integral_indicator (measurableSet_cubeHalf s b),
      ← integral_indicator (measurableSet_cubeHalf s b)]
    rw [show (∫ y : E3, (cubeHalf s b).indicator (fun y => chiSmallB M ℓ d 0 ((ℓ * d) • y)
            * chiSmallB M ℓ d 0 ((ℓ * d) • y - z)) y)
        = ∫ y : E3, chiSupAbs ^ 2 * (cubeHalf s b).indicator
            (fun y => chiSmall M y * chiSmall M (y - s)) y from ?_]
    · rw [integral_const_mul]
    · apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y ∈ cubeHalf s b
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hpt y hy]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  rw [integral_comp_smul_right (g := fun x : E3 =>
    chiSmallB M ℓ d 0 x * chiSmallB M ℓ d 0 (x - z)) hL]
  calc chiSupAbs ^ 2 * (ℓ * d) ^ 3
        * (∫ y in cubeHalf s b, chiSmall M y * chiSmall M (y - s))
      = (ℓ * d) ^ 3 * (chiSupAbs ^ 2 * ∫ y in cubeHalf s b,
          chiSmall M y * chiSmall M (y - s)) := by ring
    _ = (ℓ * d) ^ 3 * (∫ y in cubeHalf s b, chiSmallB M ℓ d 0 ((ℓ * d) • y)
          * chiSmallB M ℓ d 0 ((ℓ * d) • y - z)) := by rw [hcongr]
    _ ≤ (ℓ * d) ^ 3 * ∫ y : E3, chiSmallB M ℓ d 0 ((ℓ * d) • y)
          * chiSmallB M ℓ d 0 ((ℓ * d) • y - z) :=
        mul_le_mul_of_nonneg_left hle (pow_nonneg (le_of_lt hL) 3)

/-! ## The degenerate case `b ≥ 1/2` of the per-coordinate inequality -/

/-- The two-factor product `u ↦ gM(u+s/2)·gM(u−s/2)` vanishes for `|u| > 1/2`. -/
lemma gM_shift_eq_zero {M : ℕ} (hM : 1 ≤ M) {s u : ℝ} (h : 1 / 2 < |u|) :
    gM M (u + s / 2) * gM M (u - s / 2) = 0 := by
  have hpos : ∀ v : ℝ, 1 / 2 < |v| → gM M v = 0 := fun v hv => gM_eq_zero_of_one_half_lt hM hv
  rcases le_or_gt 0 s with hs | hs
  · rcases le_or_gt 0 u with hu | hu
    · have hu' : 1 / 2 < u := by rwa [abs_of_nonneg hu] at h
      have h1 : 1 / 2 < |u + s / 2| := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      rw [hpos _ h1, zero_mul]
    · have hu' : 1 / 2 < -u := by rwa [abs_of_neg hu] at h
      have h1 : 1 / 2 < |u - s / 2| := by
        have hneg : u - s / 2 < 0 := by linarith
        rw [abs_of_neg hneg]
        linarith
      rw [hpos _ h1, mul_zero]
  · rcases le_or_gt 0 u with hu | hu
    · have hu' : 1 / 2 < u := by rwa [abs_of_nonneg hu] at h
      have h1 : 1 / 2 < |u - s / 2| := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      rw [hpos _ h1, mul_zero]
    · have hu' : 1 / 2 < -u := by rwa [abs_of_neg hu] at h
      have h1 : 1 / 2 < |u + s / 2| := by
        have hneg : u + s / 2 < 0 := by linarith
        rw [abs_of_neg hneg]
        linarith
      rw [hpos _ h1, zero_mul]

/-- For `b ≥ 1/2` the correlation integral over `[-b,b]` is the full one, so the
per-coordinate inequality holds trivially (the ratio `b/T ≤ 1` and `∫g² ≤ 1`). -/
lemma corr1D_big {M : ℕ} (hM : 1 ≤ M) {s b T : ℝ} (hb : 1 / 2 ≤ b) (hbT : b ≤ T) :
    (b / T) * (∫ u in Set.Icc (-T) T, (gM M u) ^ 2)
        * (∫ u : ℝ, gM M (u + s / 2) * gM M (u - s / 2))
      ≤ ∫ u in Set.Icc (-b) b, gM M (u + s / 2) * gM M (u - s / 2) := by
  have hT : 0 < T := lt_of_lt_of_le (by linarith) hbT
  have hsup : ∫ u in Set.Icc (-b) b, gM M (u + s / 2) * gM M (u - s / 2)
      = ∫ u : ℝ, gM M (u + s / 2) * gM M (u - s / 2) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => ?_)
    have hu' : 1 / 2 < |u| := by
      by_contra hcon
      have hle : |u| ≤ 1 / 2 := le_of_not_gt hcon
      exact hu (Set.mem_Icc.mpr ⟨by linarith [(abs_le.mp hle).1],
        by linarith [(abs_le.mp hle).2]⟩)
    exact gM_shift_eq_zero hM hu'
  have hK : ∫ u in Set.Icc (-T) T, (gM M u) ^ 2 ≤ 1 := by
    have hint : Integrable fun u : ℝ => (gM M u) ^ 2 := by
      refine ((gM_continuous M).pow 2).integrable_of_hasCompactSupport ?_
      refine (gM_hasCompactSupport hM).mono ?_
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro hc
      exact hu (by rw [Pi.pow_apply, hc]; norm_num)
    calc ∫ u in Set.Icc (-T) T, (gM M u) ^ 2
        ≤ ∫ u : ℝ, (gM M u) ^ 2 :=
          setIntegral_le_integral hint (Filter.Eventually.of_forall (fun u => sq_nonneg _))
      _ = 1 := gM_sq_integral hM
  have hK0 : 0 ≤ ∫ u in Set.Icc (-T) T, (gM M u) ^ 2 :=
    setIntegral_nonneg measurableSet_Icc (fun u _ => sq_nonneg _)
  have hI : 0 ≤ ∫ u : ℝ, gM M (u + s / 2) * gM M (u - s / 2) :=
    integral_nonneg (fun u => mul_nonneg (gM_nonneg M _) (gM_nonneg M _))
  have hbT' : b / T ≤ 1 := (div_le_one hT).mpr hbT
  have h1 : (b / T) * (∫ u in Set.Icc (-T) T, (gM M u) ^ 2) ≤ 1 := by
    calc (b / T) * (∫ u in Set.Icc (-T) T, (gM M u) ^ 2)
        ≤ 1 * (∫ u in Set.Icc (-T) T, (gM M u) ^ 2) := mul_le_mul_of_nonneg_right hbT' hK0
      _ = ∫ u in Set.Icc (-T) T, (gM M u) ^ 2 := one_mul _
      _ ≤ 1 := hK
  rw [hsup]
  calc (b / T) * (∫ u in Set.Icc (-T) T, (gM M u) ^ 2)
        * (∫ u : ℝ, gM M (u + s / 2) * gM M (u - s / 2))
      ≤ 1 * (∫ u : ℝ, gM M (u + s / 2) * gM M (u - s / 2)) :=
        mul_le_mul_of_nonneg_right h1 hI
    _ = ∫ u : ℝ, gM M (u + s / 2) * gM M (u - s / 2) := one_mul _

end Work.BoseFixB1S
