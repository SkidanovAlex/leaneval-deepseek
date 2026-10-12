import Mathlib.Analysis.Convolution
import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.SqrtKin.norm_rpow_radial
import Submission.Work.BoseBoxFock.SqrtKinGradBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SqrtKin.riesz_pair_integrable`

The Riesz pair integrand `(x,y) ↦ ‖x - y‖^{-4}‖g x - g y‖²` of a smooth compactly supported
`g : ℝ³ → ℂ` is integrable for the product of Lebesgue measures on `ℝ³ × ℝ³`.

The proof combines the following ingredients:

* `lipschitz_bound_g` / `bounded_g` (from `SqrtKinGradBound`) bound `‖g x - g y‖ ≤ C‖x - y‖`
  and `‖g x‖ ≤ B`;
* the radial borderline integrability facts of `norm_rpow_radial`: `‖z‖^{-2}` on the unit ball
  (`α = 2 < 3`) and `‖z‖^{-4}` outside it (`α = 4 > 3`);
* the fact that `g` vanishes off `tsupport g`.

The integrand is dominated pointwise by the even radial kernel
`rieszDom C B (x - y) · (1_{tsupport g}(x) + 1_{tsupport g}(y))` (Lipschitz near the diagonal,
bounded far from it), and that dominating function is integrable by the convolution-integrand
lemma `Integrable.convolution_integrand` together with translation invariance of Lebesgue
measure. Integrability is then transferred by `Integrable.mono'`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.SqrtKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The manifestly even, nonnegative radial kernel dominating `‖z‖^{-4}‖g x - g y‖²`
for `z = x - y`: the Lipschitz bound `C‖z‖` is used on the unit ball, the sup bound `B` outside
(where the two contributions `‖z‖^{-2}·1_{‖z‖<1}` and `‖z‖^{-4}·1_{1≤‖z‖}` are the two borderline
radially integrable pieces in dimension `3`). -/
def rieszDom (C B : ℝ) (z : ℝ³) : ℝ :=
  C ^ 2 * (if ‖z‖ < 1 then ‖z‖ ^ (-(2 : ℝ)) else 0) +
    4 * B ^ 2 * (if 1 ≤ ‖z‖ then ‖z‖ ^ (-(4 : ℝ)) else 0)

lemma rieszDom_even (C B : ℝ) (z : ℝ³) : rieszDom C B (-z) = rieszDom C B z := by
  simp only [rieszDom, norm_neg]

lemma rieszDom_nonneg (C B : ℝ) (z : ℝ³) : 0 ≤ rieszDom C B z := by
  rw [rieszDom]
  have ha : 0 ≤ (if ‖z‖ < 1 then ‖z‖ ^ (-(2 : ℝ)) else 0) := by
    by_cases h : ‖z‖ < 1
    · rw [if_pos h]; exact Real.rpow_nonneg (norm_nonneg _) _
    · rw [if_neg h]
  have hb : 0 ≤ (if 1 ≤ ‖z‖ then ‖z‖ ^ (-(4 : ℝ)) else 0) := by
    by_cases h : 1 ≤ ‖z‖
    · rw [if_pos h]; exact Real.rpow_nonneg (norm_nonneg _) _
    · rw [if_neg h]
  exact add_nonneg (mul_nonneg (sq_nonneg C) ha)
    (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg B)) hb)

lemma integrable_rieszDom (C B : ℝ) : Integrable (rieszDom C B) volume := by
  have h1 : Integrable (fun z : ℝ³ => if ‖z‖ < 1 then ‖z‖ ^ (-(2 : ℝ)) else 0) volume := by
    have heq : (fun z : ℝ³ => if ‖z‖ < 1 then ‖z‖ ^ (-(2 : ℝ)) else 0)
        = (Metric.ball (0 : ℝ³) 1).indicator (fun z => ‖z‖ ^ (-(2 : ℝ))) := by
      funext z
      by_cases h : ‖z‖ < 1
      · rw [if_pos h, Set.indicator_of_mem (s := Metric.ball (0 : ℝ³) 1)
          (by simpa [Metric.mem_ball, dist_eq_norm] using h)
          (fun z : ℝ³ => ‖z‖ ^ (-(2 : ℝ)))]
      · rw [if_neg h, Set.indicator_of_notMem]
        intro hmem
        exact h (by simpa [Metric.mem_ball, dist_eq_norm] using hmem)
    rw [heq, integrable_indicator_iff Metric.isOpen_ball.measurableSet]
    exact integrableOn_norm_rpow_neg_two_ball
  have h2 : Integrable (fun z : ℝ³ => if 1 ≤ ‖z‖ then ‖z‖ ^ (-(4 : ℝ)) else 0) volume := by
    have heq : (fun z : ℝ³ => if 1 ≤ ‖z‖ then ‖z‖ ^ (-(4 : ℝ)) else 0)
        = ({z : ℝ³ | 1 ≤ ‖z‖}).indicator (fun z => ‖z‖ ^ (-(4 : ℝ))) := by
      funext z
      by_cases h : 1 ≤ ‖z‖
      · rw [if_pos h, Set.indicator_of_mem (s := {z : ℝ³ | 1 ≤ ‖z‖}) h
          (fun z : ℝ³ => ‖z‖ ^ (-(4 : ℝ)))]
      · rw [if_neg h, Set.indicator_of_notMem]
        exact fun hmem => h hmem
    rw [heq, integrable_indicator_iff (by measurability)]
    exact integrableOn_norm_rpow_neg_four_outer
  have h := (h1.const_mul (C ^ 2)).add (h2.const_mul (4 * B ^ 2))
  exact h

/-- The elementary `rpow` identity `z^{-4}z² = z^{-2}` for `z ≥ 0` (in dimension `3`). -/
lemma rpow_neg_four_mul_sq (x : ℝ) (hx : 0 ≤ x) : x ^ (-(4 : ℝ)) * x ^ 2 = x ^ (-(2 : ℝ)) := by
  by_cases h0 : x = 0
  · rw [h0, Real.zero_rpow (by norm_num : (-(4 : ℝ)) ≠ 0), zero_mul,
      Real.zero_rpow (by norm_num : (-(2 : ℝ)) ≠ 0)]
  · rw [← Real.rpow_natCast x 2, ← Real.rpow_add (lt_of_le_of_ne hx (Ne.symm h0))]
    norm_num

lemma indicator_one_nonneg {T : Set ℝ³} (x : ℝ³) : 0 ≤ T.indicator (fun _ => (1 : ℝ)) x := by
  by_cases h : x ∈ T
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]

/-- **Pointwise domination.**  If `‖g x - g y‖ ≤ C‖x - y‖`, `‖g x‖ ≤ B` and `g` vanishes off `T`,
then the Riesz integrand is dominated by `rieszDom C B (x - y)·(1_T x + 1_T y)`. -/
lemma rieszDom_pointwise_bound {g : ℝ³ → ℂ} {C B : ℝ}
    (hLip : ∀ x y : ℝ³, ‖g x - g y‖ ≤ C * ‖x - y‖) (hBd : ∀ x : ℝ³, ‖g x‖ ≤ B)
    {T : Set ℝ³} (hT : ∀ x, x ∉ T → g x = 0) (q : ℝ³ × ℝ³) :
    ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖g q.1 - g q.2‖ ^ 2
      ≤ rieszDom C B (q.1 - q.2)
        * ((T.indicator (fun _ => (1 : ℝ)) q.1) + (T.indicator (fun _ => (1 : ℝ)) q.2)) := by
  have hz0 : 0 ≤ ‖q.1 - q.2‖ := norm_nonneg _
  have hcore : ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖g q.1 - g q.2‖ ^ 2 ≤ rieszDom C B (q.1 - q.2) := by
    rw [rieszDom]
    by_cases hb : ‖q.1 - q.2‖ < 1
    · simp only [if_pos hb, if_neg (not_le.mpr hb), mul_zero, add_zero]
      have hle : ‖g q.1 - g q.2‖ ≤ C * ‖q.1 - q.2‖ := hLip _ _
      have hsq : ‖g q.1 - g q.2‖ ^ 2 ≤ (C * ‖q.1 - q.2‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hle 2
      calc ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖g q.1 - g q.2‖ ^ 2
          ≤ ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * (C * ‖q.1 - q.2‖) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hz0 _)
        _ = C ^ 2 * (‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖q.1 - q.2‖ ^ 2) := by ring
        _ = C ^ 2 * ‖q.1 - q.2‖ ^ (-(2 : ℝ)) := by rw [rpow_neg_four_mul_sq _ hz0]
    · have hb' : 1 ≤ ‖q.1 - q.2‖ := not_lt.mp hb
      simp only [if_neg hb, if_pos hb', mul_zero, zero_add]
      have hle : ‖g q.1 - g q.2‖ ≤ 2 * B := by
        calc ‖g q.1 - g q.2‖ ≤ ‖g q.1‖ + ‖g q.2‖ := norm_sub_le _ _
          _ ≤ B + B := add_le_add (hBd _) (hBd _)
          _ = 2 * B := by ring
      have hsq : ‖g q.1 - g q.2‖ ^ 2 ≤ (2 * B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
      calc ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖g q.1 - g q.2‖ ^ 2
          ≤ ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * (2 * B) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hz0 _)
        _ = 4 * B ^ 2 * ‖q.1 - q.2‖ ^ (-(4 : ℝ)) := by ring
  rcases em (q.1 ∈ T ∨ q.2 ∈ T) with hTm | hTm
  · have hfac : 1 ≤ (T.indicator (fun _ => (1 : ℝ)) q.1) +
        (T.indicator (fun _ => (1 : ℝ)) q.2) := by
      rcases hTm with h | h
      · rw [Set.indicator_of_mem h]
        linarith [indicator_one_nonneg (T := T) q.2]
      · rw [Set.indicator_of_mem h]
        linarith [indicator_one_nonneg (T := T) q.1]
    have hnn : 0 ≤ rieszDom C B (q.1 - q.2) := rieszDom_nonneg _ _ _
    calc ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖g q.1 - g q.2‖ ^ 2
        ≤ rieszDom C B (q.1 - q.2) := hcore
      _ ≤ rieszDom C B (q.1 - q.2)
            * ((T.indicator (fun _ => (1 : ℝ)) q.1) +
                (T.indicator (fun _ => (1 : ℝ)) q.2)) := by
          simpa using mul_le_mul_of_nonneg_left hfac hnn
  · rw [not_or] at hTm
    have h1 : g q.1 = 0 := hT q.1 hTm.1
    have h2 : g q.2 = 0 := hT q.2 hTm.2
    rw [Set.indicator_of_notMem hTm.1, Set.indicator_of_notMem hTm.2, add_zero, mul_zero,
      h1, h2]
    simp

/-- **Integrability of the dominating function.**  For an integrable (even) `Ψ` and a measurable
set `T` of finite Lebesgue measure, the function `(x,y) ↦ Ψ (x - y)(1_T x + 1_T y)` is integrable
for the product measure. -/
lemma integrable_sub_kernel_mul_indicator {Ψ : ℝ³ → ℝ} (hΨ : Integrable Ψ volume)
    (hΨeven : ∀ z, Ψ (-z) = Ψ z) {T : Set ℝ³} (hT : MeasurableSet T) (hfin : volume T ≠ ⊤) :
    Integrable (fun q : ℝ³ × ℝ³ =>
        Ψ (q.1 - q.2) * ((T.indicator (fun _ => (1 : ℝ)) q.1) +
          (T.indicator (fun _ => (1 : ℝ)) q.2))) (volume.prod volume) := by
  have hind : Integrable (T.indicator (fun _ => (1 : ℝ))) volume := by
    rw [integrable_indicator_iff hT]
    exact integrableOn_const hfin (by simp)
  -- the second summand, directly from the convolution integrand lemma
  have h2 : Integrable (fun p : ℝ³ × ℝ³ =>
      Ψ (p.1 - p.2) * (T.indicator (fun _ => (1 : ℝ)) p.2)) (volume.prod volume) := by
    have h := Integrable.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ)
      (f := T.indicator (fun _ => (1 : ℝ))) (g := Ψ) (μ := volume) (ν := volume) hind hΨ
    simpa only [ContinuousLinearMap.mul_apply', mul_comm] using h
  -- the first summand is the second one composed with the measure preserving swap
  have h1 : Integrable (fun q : ℝ³ × ℝ³ =>
      Ψ (q.1 - q.2) * (T.indicator (fun _ => (1 : ℝ)) q.1)) (volume.prod volume) := by
    have hswap := (Measure.measurePreserving_swap (μ := volume) (ν := volume)).integrable_comp
      h2.aestronglyMeasurable |>.mpr h2
    refine hswap.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap]
    rw [show q.2 - q.1 = -(q.1 - q.2) by abel, hΨeven]
  refine (h1.add h2).congr (Filter.Eventually.of_forall fun q => ?_)
  simp only [Pi.add_apply, mul_add]

theorem riesz_pair_integrable {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖g q.1 - g q.2‖ ^ 2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  obtain ⟨C, _, hLip⟩ := lipschitz_bound_g hg hgc
  obtain ⟨B, _, hBd⟩ := bounded_g hg hgc
  have hgcont : Continuous g := hg.continuous
  have hTmeas : MeasurableSet (tsupport g) := isClosed_tsupport g |>.measurableSet
  have hTfin : volume (tsupport g) ≠ ⊤ := (IsCompact.measure_lt_top hgc).ne
  have hG : Integrable (fun q : ℝ³ × ℝ³ => rieszDom C B (q.1 - q.2) *
      ((tsupport g).indicator (fun _ => (1 : ℝ)) q.1 +
        (tsupport g).indicator (fun _ => (1 : ℝ)) q.2)) (volume.prod volume) :=
    integrable_sub_kernel_mul_indicator (integrable_rieszDom C B) (rieszDom_even C B) hTmeas hTfin
  refine Integrable.mono' hG ?_ ?_
  · exact (by measurability :
      AEStronglyMeasurable (fun q : ℝ³ × ℝ³ =>
        ‖q.1 - q.2‖ ^ (-(4 : ℝ)) * ‖g q.1 - g q.2‖ ^ 2) (volume.prod volume))
  · filter_upwards with q
    rw [Real.norm_of_nonneg
      (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg _))]
    exact rieszDom_pointwise_bound hLip hBd
      (fun x hx => by
        by_contra h
        exact hx (subset_tsupport g h)) q

end Work.BoseBoxFock.SqrtKin
