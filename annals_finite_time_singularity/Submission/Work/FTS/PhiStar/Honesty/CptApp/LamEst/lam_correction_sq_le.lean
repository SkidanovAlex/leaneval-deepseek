/-
# `lam_correction_sq_le`: the cutoff correction is small

For a source `F` that is `C^∞` on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen`),
`F ∈ ℋ^k` (`Work.Spaces.HkMem`) and whose angular moment `F_* F = ∫_θ F z θ sinθcos²θ dθ`
vanishes for every `z > 0`, the truncated angular moment

  `lam n F z = ∫_θ zetaR n θ · F z θ · sinθcos²θ dθ`

of the cutoff approximation `CptApp.approx n F` of `Work.FTS.PhiStar.Honesty.exists_cptQ_approx`
satisfies, for almost every `z > 0` and every `s ≤ k`,

  `(D_z^s (lam n F) z)² · w(z)² ≤ C · (2/n)^{2+η} · ∫_θ (D_z^s F z θ · w(z)/sin(2θ)^{η/2})² dθ`,

with `C` a universal constant.  The factor `(2/n)^{2+η}` is what makes the correction term
`chiR n z · lam n F z · rho θ` of the approximation negligible as `n → ∞`.

## The argument

`Work.FTS.PhiStar.Honesty.CptApp.lamDzDeriv` pulls `D_z^s` through the angular integral:

  `D_z^s (lam n F) z = ∫_θ zetaR n θ · D_z^s F z θ · sinθcos²θ dθ`   (`z > 0`),

and `momentDzZero` says that the *uncut* moment of `D_z^s F` vanishes for a.e. `z > 0`.
Writing `X = D_z^s F z ·`, `sc = sinθcos²θ` and using the linearity of the integral
(`∫ zetaR·X·sc = ∫ X·sc + ∫ (zetaR - 1)·X·sc`, all three integrands being integrable because
`|X·sc| ≤ |X·w/sin^{η/2}|`) we get the **cancellation identity**

  `∫_θ zetaR n θ · X θ · sc θ dθ = ∫_θ (zetaR n θ - 1) · X θ · sc θ dθ`   (a.e. `z`).

Cauchy–Schwarz for the `L²` pairing
`X·sc = (X·w/sin^{η/2}) · ((zetaR - 1)·sin^{η/2}·sc/w)`
then bounds the square of the moment by
`(∫_θ (X w/sin^{η/2})²) · (∫_θ (zetaR - 1)²·sin^{η}·sc²)`, and the second factor is small
because `zetaR n - 1` is supported on the two boundary strips `[0, 2/n]` and
`[π/2 - 2/n, π/2]`, each of length `2/n`, where `sin(2θ)^{2+η} = O((2/n)^{2+η})`:

  `∫_θ (zetaR n θ - 1)²·sin(2θ)^{η}·sc² dθ ≤ 16·(2/n)^{2+η}`
  (`LamEst.angular_cutoff_bound`).

The two remaining ingredients are the analytic estimates, stated and proved separately:

* `LamEst.cs_cutoff` — the Cauchy–Schwarz step above (with the `w²` cancellation);
* `LamEst.integrable_mul_sinCos2` — the `L¹`-integrability of `X·sc` from the `L²` control.

Everything in this module is `sorry`-free.
-/
/- **Import hazard (project level).**  `CptApp.cutBasic` and `CptApp.lamDzDeriv` both declare
`zetaR_eq_zero_of_le` / `zetaR_eq_zero_of_ge`, so no module can import both: Lean rejects the
second import with "environment already contains ...".  Since `lamDzDeriv` is indispensable
here, the angular bound `LamEst.angular_cutoff_bound` (whose module imports `cutBasic`) is
*not* imported; its proof is reproduced below under the private name `angular_cutoff_bound_aux`,
together with local copies of the two `cutBasic` facts it uses (`zetaR_bounds`,
`zetaR_eq_one`).  The clash between `cutBasic` and `lamDzDeriv` must be resolved at the level of
those two files before any module wants both (e.g. the final assembly of `exists_cptQ_approx`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Defs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.lamDzDeriv
import Submission.Work.FTS.PhiStar.Honesty.CptApp.momentDzZero
import Submission.Work.FTS.PhiStar.Honesty.CptApp.LamEst.integrable_mul_sinCos2
import Submission.Work.FTS.PhiStar.Honesty.CptApp.LamEst.cs_cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.LamEst

set_option maxHeartbeats 1600000

/-- The angular cutoff takes values in `[0,1]` (local copy of
`CptApp.zetaR_bounds`; `CptApp.cutBasic` cannot be imported here, see the note below). -/
private lemma zetaR_bounds (n : ℕ) (θ : ℝ) : 0 ≤ zetaR n θ ∧ zetaR n θ ≤ 1 := by
  have hnn : 0 ≤ zetaR n θ := by
    simp only [zetaR, cut01]
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  refine ⟨hnn, ?_⟩
  simp only [zetaR, cut01]
  calc Real.smoothTransition ((n : ℝ) * θ - 1)
        * Real.smoothTransition ((n : ℝ) * (Real.pi / 2 - θ) - 1)
      ≤ 1 * 1 := mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
        (Real.smoothTransition.nonneg _) zero_le_one
    _ = 1 := by norm_num

/-- The angular cutoff equals `1` on its plateau (local copy of `CptApp.zetaR_eq_one`). -/
private lemma zetaR_eq_one {n : ℕ} (hn : 2 ≤ n) {θ : ℝ} (h1 : 2 / (n : ℝ) ≤ θ)
    (h2 : θ ≤ Real.pi / 2 - 2 / (n : ℝ)) : zetaR n θ = 1 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have ha : 1 ≤ (n : ℝ) * θ - 1 := by
    have := (div_le_iff₀ hnpos).mp h1
    nlinarith
  have hb : 1 ≤ (n : ℝ) * (Real.pi / 2 - θ) - 1 := by
    have h : 2 / (n : ℝ) ≤ Real.pi / 2 - θ := by linarith
    have := (div_le_iff₀ hnpos).mp h
    nlinarith
  simp only [zetaR, cut01, Real.smoothTransition.one_of_one_le ha,
    Real.smoothTransition.one_of_one_le hb]
  norm_num

private lemma sin_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h; simp
  · exact le_of_lt (Real.sin_lt h)

/-- On the support of `zetaR n - 1` the factor `(zetaR n θ - 1)²` is at most `1`. -/
private lemma zetaR_sub_one_sq_le_one (n : ℕ) (θ : ℝ) : (zetaR n θ - 1) ^ 2 ≤ 1 := by
  obtain ⟨h0, h1⟩ := zetaR_bounds n θ
  nlinarith

private lemma indicator_unit_nonneg (s : Set ℝ) (x : ℝ) :
    0 ≤ s.indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]; norm_num
  · rw [Set.indicator_of_notMem hx]

private lemma indicator_unit_le_one (s : Set ℝ) (x : ℝ) :
    s.indicator (fun _ => (1 : ℝ)) x ≤ 1 := by
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]; norm_num

/-- The two-strip majorant: the constant `C` on `[0,t]` and on `[π/2 - t, π/2]`. -/
private def majorant (t C : ℝ) : ℝ → ℝ := fun θ =>
  C * (Set.Icc 0 t).indicator (fun _ => (1 : ℝ)) θ
    + C * (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)).indicator (fun _ => (1 : ℝ)) θ

private lemma majorant_nonneg {t C : ℝ} (hC : 0 ≤ C) (θ : ℝ) : 0 ≤ majorant t C θ := by
  unfold majorant
  exact add_nonneg (mul_nonneg hC (indicator_unit_nonneg _ _))
    (mul_nonneg hC (indicator_unit_nonneg _ _))

private lemma majorant_le {t C : ℝ} (hC : 0 ≤ C) (θ : ℝ) : majorant t C θ ≤ 2 * C := by
  unfold majorant
  have h1 := indicator_unit_le_one (Set.Icc 0 t) θ
  have h2 := indicator_unit_le_one (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)) θ
  nlinarith [hC]

/-- On the strips the integrand is at most `4 t^{2+η}`. -/
private lemma pointwise_bound {n : ℕ} {t θ : ℝ} (ht : 0 < t)
    (hsin0 : 0 ≤ Real.sin (2 * θ)) (hsin : Real.sin (2 * θ) ≤ 2 * t)
    (hsc : (Work.Elliptic.sinCos2 θ) ^ 2 ≤ t ^ 2) :
    (zetaR n θ - 1) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
        * (Work.Elliptic.sinCos2 θ) ^ 2 ≤ 4 * t ^ (2 + Work.Spaces.eta) := by
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  have hz : (zetaR n θ - 1) ^ 2 ≤ 1 := zetaR_sub_one_sq_le_one n θ
  have h2 : (Real.sin (2 * θ)) ^ Work.Spaces.eta ≤ (2 * t) ^ Work.Spaces.eta :=
    Real.rpow_le_rpow hsin0 hsin Work.Spaces.eta_nonneg
  have h3 : (2 * t) ^ Work.Spaces.eta = 2 ^ Work.Spaces.eta * t ^ Work.Spaces.eta :=
    Real.mul_rpow (by norm_num) ht0
  have h4 : (2 : ℝ) ^ Work.Spaces.eta ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (le_of_lt Work.Spaces.eta_lt_one)
    simpa using h
  have h2t : (2 * t) ^ Work.Spaces.eta ≤ 2 * t ^ Work.Spaces.eta := by
    rw [h3]
    exact mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg ht0 _)
  have htp : t ^ Work.Spaces.eta * t ^ 2 = t ^ (2 + Work.Spaces.eta) := by
    rw [← Real.rpow_two t, ← Real.rpow_add ht, add_comm Work.Spaces.eta 2]
  have hsin_nn : 0 ≤ (Real.sin (2 * θ)) ^ Work.Spaces.eta :=
    Real.rpow_nonneg hsin0 _
  have h2t_nn : 0 ≤ (2 * t) ^ Work.Spaces.eta := Real.rpow_nonneg (by positivity) _
  calc (zetaR n θ - 1) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
        * (Work.Elliptic.sinCos2 θ) ^ 2
      ≤ 1 * (2 * t) ^ Work.Spaces.eta * t ^ 2 :=
        mul_le_mul (mul_le_mul hz h2 hsin_nn zero_le_one) hsc (sq_nonneg _)
          (mul_nonneg zero_le_one h2t_nn)
    _ ≤ 1 * (2 * t ^ Work.Spaces.eta) * t ^ 2 := by
        have h := mul_le_mul_of_nonneg_right h2t (sq_nonneg t)
        nlinarith [h]
    _ = 2 * (t ^ Work.Spaces.eta * t ^ 2) := by ring
    _ = 2 * t ^ (2 + Work.Spaces.eta) := by rw [htp]
    _ ≤ 4 * t ^ (2 + Work.Spaces.eta) := by
        linarith [Real.rpow_nonneg ht0 (2 + Work.Spaces.eta)]

private theorem angular_cutoff_bound_aux {n : ℕ} (hn : 2 ≤ n) :
    ∫ θ in Work.Spaces.Iθ, (Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) ^ 2
        * (Real.sin (2 * θ)) ^ Work.Spaces.eta * (Work.Elliptic.sinCos2 θ) ^ 2
      ≤ 16 * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) := by
  set t : ℝ := 2 / (n : ℝ) with ht
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one hnpos]
    exact_mod_cast hn
  set C : ℝ := 4 * t ^ (2 + Work.Spaces.eta) with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg ht0.le _)
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  have hIθ_fin : volume Work.Spaces.Iθ < ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  haveI hfin : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := by
    rw [isFiniteMeasure_restrict]
    exact hIθ_fin.ne
  -- basic pointwise facts on `Iθ`
  have hsin2_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    obtain ⟨h0, h1⟩ := hθ
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  -- the pointwise domination
  have hpoint : ∀ θ ∈ Work.Spaces.Iθ,
      (zetaR n θ - 1) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
          * (Work.Elliptic.sinCos2 θ) ^ 2 ≤ majorant t C θ := by
    intro θ hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    have hsinθ0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ0, by linarith [Real.pi_pos]⟩
    have hcosθ0 : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ0], by linarith [hθ1, Real.pi_pos]⟩
    have hcos2_le : Real.cos θ ^ 2 ≤ 1 := by
      nlinarith [abs_nonneg (Real.cos θ), Real.abs_cos_le_one θ, sq_abs (Real.cos θ)]
    have hsc0 : 0 ≤ Work.Elliptic.sinCos2 θ := by
      rw [Work.Elliptic.sinCos2]; exact mul_nonneg hsinθ0 (sq_nonneg _)
    by_cases hlt : θ < t
    · -- left strip `[0, t]`
      have hsinθ_le : Real.sin θ ≤ t := le_trans (sin_le_self_of_nonneg hθ0) (le_of_lt hlt)
      have hsin : Real.sin (2 * θ) ≤ 2 * t := by
        rw [Real.sin_two_mul]
        have h := mul_le_mul hsinθ_le (Real.cos_le_one θ) hcosθ0 ht0.le
        linarith [h]
      have hsct : Work.Elliptic.sinCos2 θ ≤ t := by
        rw [Work.Elliptic.sinCos2]
        nlinarith [hsinθ_le, hsinθ0, hcos2_le, sq_nonneg (Real.cos θ), ht0.le]
      have hsc : (Work.Elliptic.sinCos2 θ) ^ 2 ≤ t ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hsct) (add_nonneg ht0.le hsc0)]
      have hb := pointwise_bound (n := n) ht0 hsin0 hsin hsc
      rw [← hC] at hb
      have hind : (Set.Icc 0 t).indicator (fun _ => (1 : ℝ)) θ = 1 := by
        rw [Set.indicator_of_mem (show θ ∈ Set.Icc 0 t from ⟨hθ0, le_of_lt hlt⟩)]
      have hgm : C ≤ majorant t C θ := by
        simp only [majorant, hind]
        have h2n := mul_nonneg hC0 (indicator_unit_nonneg (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)) θ)
        linarith
      exact le_trans hb hgm
    · push_neg at hlt
      by_cases hple : θ ≤ Real.pi / 2 - t
      · -- the plateau: `zetaR n θ = 1`
        have hz : zetaR n θ = 1 := by
          refine zetaR_eq_one hn ?_ ?_
          · rw [← ht]; exact hlt
          · rw [← ht]; exact hple
        rw [hz]
        have hzero : (1 - 1 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
            * (Work.Elliptic.sinCos2 θ) ^ 2 = 0 := by ring
        rw [hzero]
        exact majorant_nonneg hC0 θ
      · -- right strip `[π/2 - t, π/2]`
        push_neg at hple
        have hsin : Real.sin (2 * θ) ≤ 2 * t := by
          have h1 : Real.sin (2 * θ) = Real.sin (Real.pi - 2 * θ) := by
            conv_lhs => rw [show 2 * θ = Real.pi - (Real.pi - 2 * θ) by ring]
            rw [Real.sin_pi_sub]
          rw [h1]
          have hx0 : 0 ≤ Real.pi - 2 * θ := by linarith [hθ1]
          have hxle : Real.pi - 2 * θ ≤ 2 * t := by linarith [hple]
          exact le_trans (sin_le_self_of_nonneg hx0) hxle
        have hcos_le : Real.cos θ ≤ t := by
          have h1 : Real.cos θ = Real.sin (Real.pi / 2 - θ) :=
            (Real.sin_pi_div_two_sub θ).symm
          rw [h1]
          exact le_trans (sin_le_self_of_nonneg (by linarith [hθ1])) (by linarith [hple])
        have hc2 : Real.cos θ ^ 2 ≤ t ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hcos_le) (add_nonneg ht0.le hcosθ0)]
        have hsc : (Work.Elliptic.sinCos2 θ) ^ 2 ≤ t ^ 2 := by
          have hst : Work.Elliptic.sinCos2 θ ≤ t ^ 2 := by
            rw [Work.Elliptic.sinCos2]
            have h := mul_le_mul (Real.sin_le_one θ) le_rfl (sq_nonneg (Real.cos θ)) zero_le_one
            nlinarith [h, hc2]
          have ht21 : t ^ 2 ≤ 1 := by nlinarith [ht0.le, ht1]
          have h1s : Work.Elliptic.sinCos2 θ ≤ 1 := le_trans hst ht21
          nlinarith [mul_nonneg hsc0 (sub_nonneg.mpr h1s), hst]
        have hb := pointwise_bound (n := n) ht0 hsin0 hsin hsc
        rw [← hC] at hb
        have hind : (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)).indicator (fun _ => (1 : ℝ)) θ = 1 := by
          rw [Set.indicator_of_mem (show θ ∈ Set.Icc (Real.pi / 2 - t) (Real.pi / 2)
            from ⟨le_of_lt hple, hθ1⟩)]
        have hgm : C ≤ majorant t C θ := by
          simp only [majorant, hind]
          have h2n := mul_nonneg hC0 (indicator_unit_nonneg (Set.Icc 0 t) θ)
          linarith
        exact le_trans hb hgm
  -- the majorant is integrable
  have hmaj_meas : AEStronglyMeasurable (majorant t C) (volume.restrict Work.Spaces.Iθ) := by
    have h1 : Measurable (fun θ : ℝ => C * (Set.Icc 0 t).indicator (fun _ => (1 : ℝ)) θ) :=
      measurable_const.mul (Measurable.indicator measurable_const measurableSet_Icc)
    have h2 : Measurable (fun θ : ℝ =>
        C * (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)).indicator (fun _ => (1 : ℝ)) θ) :=
      measurable_const.mul (Measurable.indicator measurable_const measurableSet_Icc)
    have h3 : Measurable (majorant t C) := by
      unfold majorant
      exact h1.add h2
    exact h3.aestronglyMeasurable
  have hmaj_int : Integrable (majorant t C) (volume.restrict Work.Spaces.Iθ) := by
    refine IntegrableOn.of_bound hIθ_fin hmaj_meas (2 * C) ?_
    filter_upwards with θ
    have h1 : 0 ≤ majorant t C θ := majorant_nonneg hC0 θ
    have h2 : majorant t C θ ≤ 2 * C := majorant_le hC0 θ
    calc ‖majorant t C θ‖ = |majorant t C θ| := Real.norm_eq_abs _
      _ = majorant t C θ := abs_of_nonneg h1
      _ ≤ 2 * C := h2
  -- the two strip integrals
  have hvol1 : (volume.restrict Work.Spaces.Iθ).real (Set.Icc 0 t) ≤ t := by
    have hm : (volume.restrict Work.Spaces.Iθ) (Set.Icc 0 t) ≤ ENNReal.ofReal t := by
      calc (volume.restrict Work.Spaces.Iθ) (Set.Icc 0 t)
          = volume (Set.Icc 0 t ∩ Work.Spaces.Iθ) := Measure.restrict_apply measurableSet_Icc
        _ ≤ volume (Set.Icc 0 t) := measure_mono (Set.inter_subset_left)
        _ = ENNReal.ofReal t := by rw [Real.volume_Icc]; norm_num
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    simpa [measureReal_def, ENNReal.toReal_ofReal ht0.le] using h
  have hvol2 : (volume.restrict Work.Spaces.Iθ).real
      (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)) ≤ t := by
    have hm : (volume.restrict Work.Spaces.Iθ)
        (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)) ≤ ENNReal.ofReal t := by
      calc (volume.restrict Work.Spaces.Iθ) (Set.Icc (Real.pi / 2 - t) (Real.pi / 2))
          = volume (Set.Icc (Real.pi / 2 - t) (Real.pi / 2) ∩ Work.Spaces.Iθ) :=
            Measure.restrict_apply measurableSet_Icc
        _ ≤ volume (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)) := measure_mono (Set.inter_subset_left)
        _ = ENNReal.ofReal t := by rw [Real.volume_Icc]; ring_nf
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
    simpa [measureReal_def, ENNReal.toReal_ofReal ht0.le] using h
  have hmaj_val : ∫ θ in Work.Spaces.Iθ, majorant t C θ
      = C * (volume.restrict Work.Spaces.Iθ).real (Set.Icc 0 t)
        + C * (volume.restrict Work.Spaces.Iθ).real
            (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)) := by
    have hi1 : Integrable (fun θ : ℝ => C * (Set.Icc 0 t).indicator (fun _ => (1 : ℝ)) θ)
        (volume.restrict Work.Spaces.Iθ) :=
      Integrable.const_mul (Integrable.indicator (integrable_const (1 : ℝ)) measurableSet_Icc) C
    have hi2 : Integrable (fun θ : ℝ =>
        C * (Set.Icc (Real.pi / 2 - t) (Real.pi / 2)).indicator (fun _ => (1 : ℝ)) θ)
        (volume.restrict Work.Spaces.Iθ) :=
      Integrable.const_mul (Integrable.indicator (integrable_const (1 : ℝ)) measurableSet_Icc) C
    simp only [majorant]
    rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul,
      integral_indicator_const (1 : ℝ) measurableSet_Icc,
      integral_indicator_const (1 : ℝ) measurableSet_Icc]
    simp
  have hmaj_le : ∫ θ in Work.Spaces.Iθ, majorant t C θ ≤ C * t + C * t := by
    rw [hmaj_val]
    have h1 := mul_le_mul_of_nonneg_left hvol1 hC0
    have h2 := mul_le_mul_of_nonneg_left hvol2 hC0
    linarith
  -- the final arithmetic
  have harith : C * t + C * t ≤ 16 * t ^ (2 + Work.Spaces.eta) := by
    have hnn : 0 ≤ t ^ (2 + Work.Spaces.eta) := Real.rpow_nonneg ht0.le _
    have hmul : t ^ (2 + Work.Spaces.eta) * t ≤ t ^ (2 + Work.Spaces.eta) := by
      nlinarith [hnn, ht1]
    calc C * t + C * t = 8 * (t ^ (2 + Work.Spaces.eta) * t) := by rw [hC]; ring
      _ ≤ 8 * t ^ (2 + Work.Spaces.eta) := by linarith
      _ ≤ 16 * t ^ (2 + Work.Spaces.eta) := by linarith
  have hf_nn : ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ (zetaR n θ - 1) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
          * (Work.Elliptic.sinCos2 θ) ^ 2 := by
    intro θ hθ
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin2_nn θ hθ) _)) (sq_nonneg _)
  calc ∫ θ in Work.Spaces.Iθ, (zetaR n θ - 1) ^ 2
          * (Real.sin (2 * θ)) ^ Work.Spaces.eta * (Work.Elliptic.sinCos2 θ) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, majorant t C θ :=
        integral_mono_of_nonneg
          (ae_restrict_of_forall_mem hIθ_meas hf_nn) hmaj_int
          (ae_restrict_of_forall_mem hIθ_meas hpoint)
    _ ≤ C * t + C * t := hmaj_le
    _ ≤ 16 * t ^ (2 + Work.Spaces.eta) := harith
    _ = 16 * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta) := by rw [ht]


/-- The angular cutoff factor `zetaR n θ - 1` is bounded by `1` (it lies in `[-1, 0]`). -/
theorem abs_zetaR_sub_one_le (n : ℕ) (θ : ℝ) : |zetaR n θ - 1| ≤ 1 := by
  have hnn : 0 ≤ zetaR n θ := by
    rw [zetaR, cut01]
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hle : zetaR n θ ≤ 1 := by
    rw [zetaR, cut01]
    calc Real.smoothTransition ((n : ℝ) * θ - 1)
          * Real.smoothTransition ((n : ℝ) * (Real.pi / 2 - θ) - 1)
        ≤ 1 * 1 := mul_le_mul (Real.smoothTransition.le_one _)
            (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) zero_le_one
      _ = 1 := by norm_num
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

theorem lam_correction_sq_le {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    ∃ Cmom : ℝ, 0 ≤ Cmom ∧
      ∀ (n : ℕ), 2 ≤ n → ∀ (s : ℕ), s ≤ k →
        ∀ᵐ z ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)),
          (Work.Spaces.DzIter s
              (fun z _ => Work.FTS.PhiStar.Honesty.CptApp.lam n F z) z 0)^2 * (Work.Spaces.w z)^2
            ≤ Cmom * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
              * (∫ θ in Work.Spaces.Iθ,
                  (Work.Spaces.DzIter s F z θ
                    * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))^2) := by
  refine ⟨16, by norm_num, ?_⟩
  intro n hn s hs
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  filter_upwards [momentDzZero hsm hF hFs s hs,
    MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hmom hz
  have hzpos : 0 < z := hz
  -- ## Integrability and measurability of the weighted `D_z^s F` slot
  have hX2 : MeasureTheory.Integrable
      (fun θ : ℝ => (Work.Spaces.DzIter s F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.integrableOn_zSummand α k hsm hF s hs
      (Set.mem_Ici.mpr hzpos.le)
  have hXm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.DzIter s F z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.DzIter s F p.1 p.2) ((hsm.DzIter s).continuousOn) hzpos
  have hAm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.DzIter s F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hsm.aesm_slice_summand s hzpos
  have hXsc : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.DzIter s F z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    integrable_mul_sinCos2 hzpos hXm hX2
  -- ## The cancellation identity: the uncut moment of `D_z^s F` vanishes
  have hγm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => zetaR n θ - 1)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ((continuous_zetaR n).aestronglyMeasurable).sub
      (continuous_const.aestronglyMeasurable)
  have hscm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    continuous_sinCos2.aestronglyMeasurable
  have hζint : MeasureTheory.Integrable
      (fun θ : ℝ => (zetaR n θ - 1) * Work.Spaces.DzIter s F z θ
        * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono hXsc ((hγm.mul hXm).mul hscm) ?_
    filter_upwards with θ
    have h3 : |zetaR n θ - 1| ≤ 1 := abs_zetaR_sub_one_le n θ
    calc ‖(zetaR n θ - 1) * Work.Spaces.DzIter s F z θ * Work.Elliptic.sinCos2 θ‖
        = |zetaR n θ - 1| * |Work.Spaces.DzIter s F z θ| * |Work.Elliptic.sinCos2 θ| := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
      _ ≤ 1 * |Work.Spaces.DzIter s F z θ| * |Work.Elliptic.sinCos2 θ| := by gcongr
      _ = |Work.Spaces.DzIter s F z θ| * |Work.Elliptic.sinCos2 θ| := by ring
      _ = ‖Work.Spaces.DzIter s F z θ * Work.Elliptic.sinCos2 θ‖ := by
          rw [Real.norm_eq_abs, abs_mul]
  have hId : (∫ θ in Work.Spaces.Iθ,
        zetaR n θ * Work.Spaces.DzIter s F z θ * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ,
        (zetaR n θ - 1) * Work.Spaces.DzIter s F z θ * Work.Elliptic.sinCos2 θ := by
    have hsum := MeasureTheory.integral_add hζint hXsc
    have hcongr : (∫ θ in Work.Spaces.Iθ,
          ((zetaR n θ - 1) * Work.Spaces.DzIter s F z θ * Work.Elliptic.sinCos2 θ)
            + (Work.Spaces.DzIter s F z θ * Work.Elliptic.sinCos2 θ))
        = ∫ θ in Work.Spaces.Iθ,
            zetaR n θ * Work.Spaces.DzIter s F z θ * Work.Elliptic.sinCos2 θ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with θ
      ring
    rw [hcongr, hmom, add_zero] at hsum
    exact hsum
  -- ## Cauchy–Schwarz against the `(s,0)`-slot, with the cutoff weight
  have hcs := cs_cutoff (X := fun θ : ℝ => Work.Spaces.DzIter s F z θ)
    (γ := fun θ : ℝ => zetaR n θ - 1) hzpos hγm (abs_zetaR_sub_one_le n) hAm hX2
  have hang := angular_cutoff_bound_aux hn
  have hΦnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter s F z θ * (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  -- ## Assembly
  rw [Work.FTS.PhiStar.Honesty.CptApp.lamDzDeriv hsm k n hn1 s hs z hzpos, hId]
  have hstep : (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter s F z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      * (∫ θ in Work.Spaces.Iθ,
        (zetaR n θ - 1) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
          * (Work.Elliptic.sinCos2 θ) ^ 2)
      ≤ 16 * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
        * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter s F z θ * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    calc (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter s F z θ * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        * (∫ θ in Work.Spaces.Iθ,
          (zetaR n θ - 1) ^ 2 * (Real.sin (2 * θ)) ^ Work.Spaces.eta
            * (Work.Elliptic.sinCos2 θ) ^ 2)
        ≤ (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter s F z θ * (Work.Spaces.w z
              / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          * (16 * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_left hang hΦnn
      _ = 16 * (2 / (n : ℝ)) ^ (2 + Work.Spaces.eta)
          * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter s F z θ * (Work.Spaces.w z
              / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by ring
  exact le_trans hcs hstep

end Work.FTS.PhiStar.Honesty.CptApp.LamEst
