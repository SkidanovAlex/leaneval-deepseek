import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseBoxFock.PCFU.aQ_aP_update_invariant
import Submission.Work.BoseBoxFock.PCFU.fibreMean_sq_integral_le
import Submission.Work.BoseFixB3.CS.Pieces.aP_sq_le_of_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.BoseGases

/-!
# `Work.BoseBoxFock.PCFU.chBimg_state_le`

The state-level bound behind the `chBimg` slot: for a continuous state `Φ` and distinct slots
`i ≠ j`, with `Θ = boxRestrictR ℓ Φ` (the box restriction of `Φ`) and `Ψ = Q_j P_i Θ`,

  `∫_x |Θ x| · (∫_{u ∈ acube ℓ} |Ψ (x[j↦u])| du) dx ≤ 8 ℓ³ ∫_x Θ(x)²  `,

and the left-hand integrand is integrable.

The proof is an elementary two-parameter Cauchy–Schwarz / AM–GM argument, carried in the *peeled*
coordinates `x = kcInsN m j (w, r)` of `abox (m+1) ℓ = acube ℓ × abox m ℓ`
(`BoseGases.abox_integral_peel`).  Writing `H x := |Θ x| · ∫_{u} |Ψ (x[j↦u])|`,

* peel the `j`-th slot: `∫_{abox} H = ∫_r (∫_w H (kcInsN j (w,r)) dw) dr`
  and `update (kcInsN j (w,r)) j u = kcInsN j (u,r)` (`BoseGases.update_kcInsN`) evaluates the
  inner integral, giving `∫_r A r · B r` with
  `A r = ∫_w |Θ (kcInsN j (w,r))|` and `B r = ∫_u |Ψ (kcInsN j (u,r))|`;
* AM–GM (`2 A B ≤ A² + B²`) turns this into `½(∫ A² + ∫ B²)`;
* each of `∫ A²`, `∫ B²` is bounded by `ℓ³ ∫_{abox} (·)²` by the fibre Cauchy–Schwarz on the cube
  (`Work.BoseBoxFock.PCFU.fibreMean_sq_integral_le`) followed by the peel;
* `∫_{abox} Ψ² ≤ 4 ∫_{abox} Θ²` because `P_i`, `P_j` are `L²`-contractions over the box
  (`Work.BoseFixB3.CS.Pieces.aP_sq_le_of_bound`) and `Ψ = P_iΘ − P_jP_iΘ` with
  `(a−b)² ≤ 2a² + 2b²`.

All functions occurring are bounded on the (finite-measure) box, so the integrability statements
follow from boundedness.
-/

/-- The fibre Cauchy–Schwarz bound used below is
`Work.BoseBoxFock.PCFU.fibreMean_sq_integral_le` (proved in the sibling module
`Submission/Work/BoseBoxFock/PCFU/fibreMean_sq_integral_le.lean`):

  `∫_r (∫_{w ∈ acube ℓ} |f (kcInsN m j (w,r))|)² ≤ ℓ³ ∫_{abox (m+1) ℓ} f²`. -/

theorem chBimg_state_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin n) (hij : i ≠ j)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
        |Work.BoseBoxFock.boxRestrictR ℓ Φ x|
          * (∫ u in Submission.BoseGases.acube ℓ,
              |Submission.BoseGases.aQ ℓ j
                (Submission.BoseGases.aP ℓ i (Work.BoseBoxFock.boxRestrictR ℓ Φ))
                (Function.update x j u)|))
      ∧ (∫ x : Submission.BoseGases.X n,
            |Work.BoseBoxFock.boxRestrictR ℓ Φ x|
              * (∫ u in Submission.BoseGases.acube ℓ,
                  |Submission.BoseGases.aQ ℓ j
                    (Submission.BoseGases.aP ℓ i (Work.BoseBoxFock.boxRestrictR ℓ Φ))
                    (Function.update x j u)|))
          ≤ 8 * ℓ ^ 3 * ∫ x : Submission.BoseGases.X n,
              (Work.BoseBoxFock.boxRestrictR ℓ Φ x) ^ 2 := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    set Θ : X (m + 1) → ℝ := boxRestrictR ℓ Φ with hΘdef
    set Ψ : X (m + 1) → ℝ := aQ ℓ j (aP ℓ i Θ) with hΨdef
    set H : X (m + 1) → ℝ :=
      fun x => |Θ x| * ∫ u in acube ℓ, |Ψ (Function.update x j u)| with hHdef
    -- ## basic facts about `Θ`
    have hΘm : Measurable Θ := by
      rw [hΘdef]
      unfold boxRestrictR
      exact hΦ.measurable.mul (measurable_const.indicator (abox_measurable (m + 1) ℓ))
    obtain ⟨C, hC0, hΘb⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |Θ x| ≤ C := by
      obtain ⟨C, hC⟩ := (abox_compact (m + 1) hℓ).exists_bound_of_continuousOn
        (s := abox (m + 1) ℓ) (f := Φ) hΦ.continuousOn
      refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
      rw [hΘdef]
      unfold boxRestrictR
      by_cases hx : x ∈ abox (m + 1) ℓ
      · rw [Set.indicator_of_mem hx, mul_one]
        exact le_trans (by simpa [Real.norm_eq_abs] using hC x hx) (le_max_left _ _)
      · rw [Set.indicator_of_notMem hx, mul_zero, abs_zero]
        exact le_max_right _ _
    have hΘsupp : ∀ x, x ∉ abox (m + 1) ℓ → Θ x = 0 := by
      intro x hx
      rw [hΘdef]
      unfold boxRestrictR
      rw [Set.indicator_of_notMem hx, mul_zero]
    -- ## basic facts about `Ψ`
    have hΨm : Measurable Ψ := by
      rw [hΨdef]
      exact Weak.aQ_measurable j (Weak.aP_measurable i hΘm)
    have hΨb : ∀ x, |Ψ x| ≤ 2 * C := by
      intro x
      rw [hΨdef]
      exact Weak.aQ_abs_le hℓ j hC0 (Weak.aP_abs_le hℓ i hC0 hΘb) x
    -- ## the measure on the `m`-particle box
    set ν : Measure (X m) := (volume : Measure (X m)).restrict (abox m ℓ) with hνdef
    haveI hνfin : IsFiniteMeasure ν :=
      ⟨by rw [hνdef, Measure.restrict_apply_univ]; exact abox_lt_top m ℓ hℓ.le⟩
    haveI hμcfin : IsFiniteMeasure ((volume : Measure Ω).restrict (acube ℓ)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top ℓ hℓ.le⟩
    -- ## the peeled coordinates `A`, `B`
    set Aa : X m → ℝ := fun r => ∫ w in acube ℓ, |Θ (kcInsN m j (w, r))| with hAadef
    set Bb : X m → ℝ := fun r => ∫ u in acube ℓ, |Ψ (kcInsN m j (u, r))| with hBbdef
    -- ## `H` vanishes off the box
    have hHsupp : ∀ x, x ∉ abox (m + 1) ℓ → H x = 0 := by
      intro x hx
      rw [hHdef]
      simp [hΘsupp x hx]
    -- ## integrability of `H` on the box
    have hHint : IntegrableOn H (abox (m + 1) ℓ) volume := by
      refine IntegrableOn.of_bound (abox_lt_top (m + 1) ℓ hℓ.le) ?_
        (C * (2 * C * ℓ ^ 3)) ?_
      · rw [hHdef]
        have h1 : AEStronglyMeasurable (fun x : X (m + 1) => |Θ x|) volume :=
          hΘm.abs.aestronglyMeasurable
        have h2 : AEStronglyMeasurable (fun x : X (m + 1) =>
            ∫ u in acube ℓ, |Ψ (Function.update x j u)|) volume := by
          have hjoint : AEStronglyMeasurable
              (fun p : X (m + 1) × Ω => |Ψ (Function.update p.1 j p.2)|)
              ((volume : Measure (X (m + 1))).prod
                ((volume : Measure Ω).restrict (acube ℓ))) :=
            (hΨm.comp (by fun_prop : Measurable fun p : X (m + 1) × Ω =>
              Function.update p.1 j p.2)).abs.aestronglyMeasurable
          simpa using AEStronglyMeasurable.integral_prod_right'
            (μ := (volume : Measure (X (m + 1))))
            (ν := (volume : Measure Ω).restrict (acube ℓ)) hjoint
        exact (h1.mul h2).restrict
      · rw [hHdef]
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_mul, abs_abs]
        refine mul_le_mul (hΘb x) ?_ (abs_nonneg _) hC0
        have h1 := norm_integral_le_integral_norm
          (μ := (volume : Measure Ω).restrict (acube ℓ))
          (fun u : Ω => |Ψ (Function.update x j u)|)
        simp only [Real.norm_eq_abs, abs_abs] at h1
        refine h1.trans ?_
        calc (∫ u in acube ℓ, |Ψ (Function.update x j u)|)
            ≤ ∫ u in acube ℓ, (2 * C) :=
              integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => abs_nonneg _)
                (integrable_const (2 * C)) (Filter.Eventually.of_forall fun u => hΨb _)
          _ = 2 * C * ℓ ^ 3 := Submission.BoseGases.integral_const_acube ℓ hℓ (2 * C)
    -- ## the peel of `H` at slot `j`
    have hpeel : ∫ x in abox (m + 1) ℓ, H x
        = ∫ r : X m, (∫ w in acube ℓ, H (kcInsN m j (w, r))) ∂ν :=
      abox_integral_peel (n := m) (ℓ := ℓ) (i := j) (F := H) hHint
    -- ## the pointwise evaluation of the peeled integrand
    have hpt : ∀ (w : Ω) (r : X m),
        H (kcInsN m j (w, r))
          = |Θ (kcInsN m j (w, r))| * (∫ u in acube ℓ, |Ψ (kcInsN m j (u, r))|) := by
      intro w r
      rw [hHdef]
      show |Θ (kcInsN m j (w, r))|
            * (∫ u in acube ℓ, |Ψ (Function.update (kcInsN m j (w, r)) j u)|)
          = |Θ (kcInsN m j (w, r))| * (∫ u in acube ℓ, |Ψ (kcInsN m j (u, r))|)
      congr 1
      apply integral_congr_ae
      filter_upwards with u
      rw [update_kcInsN]
    -- ## `∫_r ∫_w H = ∫_r A r * B r`
    have hstep1 : ∫ r : X m, (∫ w in acube ℓ, H (kcInsN m j (w, r))) ∂ν
        = ∫ r : X m, Aa r * Bb r ∂ν := by
      apply integral_congr_ae
      filter_upwards with r
      rw [show (∫ w in acube ℓ, H (kcInsN m j (w, r)))
            = ∫ w in acube ℓ, |Θ (kcInsN m j (w, r))| * Bb r from by
          apply integral_congr_ae
          filter_upwards with w
          rw [hpt w r]]
      rw [integral_mul_const]
    -- ## measurability and boundedness of `A`, `B`
    have hAam : AEStronglyMeasurable Aa ν := by
      rw [hAadef]
      refine AEStronglyMeasurable.integral_prod_right' (μ := ν)
        (ν := (volume : Measure Ω).restrict (acube ℓ))
        (f := fun p : X m × Ω => |Θ (kcInsN m j (p.2, p.1))|) ?_
      exact (hΘm.comp (by fun_prop : Measurable fun p : X m × Ω =>
        kcInsN m j (p.2, p.1))).abs.aestronglyMeasurable
    have hBbm : AEStronglyMeasurable Bb ν := by
      rw [hBbdef]
      refine AEStronglyMeasurable.integral_prod_right' (μ := ν)
        (ν := (volume : Measure Ω).restrict (acube ℓ))
        (f := fun p : X m × Ω => |Ψ (kcInsN m j (p.2, p.1))|) ?_
      exact (hΨm.comp (by fun_prop : Measurable fun p : X m × Ω =>
        kcInsN m j (p.2, p.1))).abs.aestronglyMeasurable
    have hAa_bd : ∀ r : X m, |Aa r| ≤ C * ℓ ^ 3 := by
      intro r
      have h1 := norm_integral_le_integral_norm
        (μ := (volume : Measure Ω).restrict (acube ℓ))
        (fun w : Ω => |Θ (kcInsN m j (w, r))|)
      simp only [Real.norm_eq_abs, abs_abs] at h1
      have h2 : (∫ w in acube ℓ, |Θ (kcInsN m j (w, r))|) ≤ ∫ w in acube ℓ, C :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => abs_nonneg _)
          (integrable_const C) (Filter.Eventually.of_forall fun w => hΘb _)
      rw [hAadef]
      exact h1.trans (h2.trans_eq (Submission.BoseGases.integral_const_acube ℓ hℓ C))
    have hBb_bd : ∀ r : X m, |Bb r| ≤ 2 * C * ℓ ^ 3 := by
      intro r
      have h1 := norm_integral_le_integral_norm
        (μ := (volume : Measure Ω).restrict (acube ℓ))
        (fun u : Ω => |Ψ (kcInsN m j (u, r))|)
      simp only [Real.norm_eq_abs, abs_abs] at h1
      have h2 : (∫ u in acube ℓ, |Ψ (kcInsN m j (u, r))|) ≤ ∫ u in acube ℓ, (2 * C) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => abs_nonneg _)
          (integrable_const (2 * C)) (Filter.Eventually.of_forall fun u => hΨb _)
      rw [hBbdef]
      exact h1.trans (h2.trans_eq (Submission.BoseGases.integral_const_acube ℓ hℓ (2 * C)))
    have hAa2int : Integrable (fun r : X m => (Aa r) ^ 2) ν := by
      refine Integrable.of_bound (hAam.pow 2) ((C * ℓ ^ 3) ^ 2) ?_
      filter_upwards with r
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (Aa r)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hAa_bd r) 2
    have hBb2int : Integrable (fun r : X m => (Bb r) ^ 2) ν := by
      refine Integrable.of_bound (hBbm.pow 2) ((2 * C * ℓ ^ 3) ^ 2) ?_
      filter_upwards with r
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (Bb r)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hBb_bd r) 2
    have hABint : Integrable (fun r : X m => Aa r * Bb r) ν := by
      refine Integrable.of_bound (hAam.mul hBbm) (C * ℓ ^ 3 * (2 * C * ℓ ^ 3)) ?_
      filter_upwards with r
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hAa_bd r) (hBb_bd r) (abs_nonneg _) (by positivity)
    -- ## AM–GM
    have hAB : ∫ r : X m, Aa r * Bb r ∂ν
        ≤ (1 / 2) * (∫ r : X m, (Aa r) ^ 2 ∂ν + ∫ r : X m, (Bb r) ^ 2 ∂ν) := by
      have hg : Integrable (fun r : X m => (1 / 2) * ((Aa r) ^ 2 + (Bb r) ^ 2)) ν :=
        (hAa2int.add hBb2int).const_mul (1 / 2)
      calc ∫ r : X m, Aa r * Bb r ∂ν
          ≤ ∫ r : X m, (1 / 2) * ((Aa r) ^ 2 + (Bb r) ^ 2) ∂ν := by
            apply integral_mono_ae hABint hg
            filter_upwards with r
            have h1 : 0 ≤ Aa r := by
              rw [hAadef]
              exact integral_nonneg (fun w => abs_nonneg _)
            have h2 : 0 ≤ Bb r := by
              rw [hBbdef]
              exact integral_nonneg (fun u => abs_nonneg _)
            nlinarith [two_mul_le_add_sq (Aa r) (Bb r)]
        _ = (1 / 2) * (∫ r : X m, (Aa r) ^ 2 ∂ν + ∫ r : X m, (Bb r) ^ 2 ∂ν) := by
            rw [integral_const_mul, integral_add hAa2int hBb2int]
    -- ## the two fibre bounds
    have hAa2_le : ∫ r : X m, (Aa r) ^ 2 ∂ν ≤ ℓ ^ 3 * ∫ x in abox (m + 1) ℓ, (Θ x) ^ 2 := by
      have h := fibreMean_sq_integral_le (m := m) (ℓ := ℓ) (f := Θ) (C := C)
        hℓ j hC0 hΘm hΘb
      simpa only [hAadef, hνdef] using h
    have hBb2_le : ∫ r : X m, (Bb r) ^ 2 ∂ν ≤ ℓ ^ 3 * ∫ x in abox (m + 1) ℓ, (Ψ x) ^ 2 := by
      have h := fibreMean_sq_integral_le (m := m) (ℓ := ℓ) (f := Ψ) (C := 2 * C)
        hℓ j (by positivity) hΨm hΨb
      simpa only [hBbdef, hνdef] using h
    -- ## `∫_{abox} Ψ² ≤ 4 ∫_{abox} Θ²`
    have hΨ2 : ∫ x in abox (m + 1) ℓ, (Ψ x) ^ 2
        ≤ 4 * ∫ x in abox (m + 1) ℓ, (Θ x) ^ 2 := by
      have hPim : Measurable (aP ℓ i Θ) := Weak.aP_measurable i hΘm
      have hPib : ∀ x, |aP ℓ i Θ x| ≤ C := Weak.aP_abs_le hℓ i hC0 hΘb
      have hPjm : Measurable (aP ℓ j (aP ℓ i Θ)) := Weak.aP_measurable j hPim
      have hPjb : ∀ x, |aP ℓ j (aP ℓ i Θ) x| ≤ C :=
        Weak.aP_abs_le hℓ j hC0 hPib
      have hX : ∫ x in abox (m + 1) ℓ, (aP ℓ i Θ x) ^ 2
          ≤ ∫ x in abox (m + 1) ℓ, (Θ x) ^ 2 :=
        Work.BoseFixB3.CS.Pieces.aP_sq_le_of_bound hℓ i hC0 hΘm (fun x _ => hΘb x)
      have hY : ∫ x in abox (m + 1) ℓ, (aP ℓ j (aP ℓ i Θ) x) ^ 2
          ≤ ∫ x in abox (m + 1) ℓ, (aP ℓ i Θ x) ^ 2 :=
        Work.BoseFixB3.CS.Pieces.aP_sq_le_of_bound hℓ j hC0 hPim (fun x _ => hPib x)
      have hpt2 : ∀ x, (Ψ x) ^ 2
          ≤ 2 * (aP ℓ i Θ x) ^ 2 + 2 * (aP ℓ j (aP ℓ i Θ) x) ^ 2 := by
        intro x
        rw [hΨdef]
        simp only [aQ]
        nlinarith [sq_nonneg (aP ℓ i Θ x + aP ℓ j (aP ℓ i Θ) x)]
      have hintΨ : IntegrableOn (fun x : X (m + 1) => (Ψ x) ^ 2) (abox (m + 1) ℓ) volume := by
        refine IntegrableOn.of_bound (abox_lt_top (m + 1) ℓ hℓ.le)
          ((hΨm.pow_const 2).aestronglyMeasurable.restrict) ((2 * C) ^ 2) ?_
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (Ψ x)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hΨb x) 2
      have hintPi : IntegrableOn (fun x : X (m + 1) => (aP ℓ i Θ x) ^ 2)
          (abox (m + 1) ℓ) volume := by
        refine IntegrableOn.of_bound (abox_lt_top (m + 1) ℓ hℓ.le)
          ((hPim.pow_const 2).aestronglyMeasurable.restrict) (C ^ 2) ?_
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (aP ℓ i Θ x)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hPib x) 2
      have hintPj : IntegrableOn (fun x : X (m + 1) => (aP ℓ j (aP ℓ i Θ) x) ^ 2)
          (abox (m + 1) ℓ) volume := by
        refine IntegrableOn.of_bound (abox_lt_top (m + 1) ℓ hℓ.le)
          ((hPjm.pow_const 2).aestronglyMeasurable.restrict) (C ^ 2) ?_
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (aP ℓ j (aP ℓ i Θ) x)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hPjb x) 2
      have hintA : IntegrableOn (fun x : X (m + 1) => (2 : ℝ) * (aP ℓ i Θ x) ^ 2)
          (abox (m + 1) ℓ) volume := hintPi.const_mul 2
      have hintB : IntegrableOn (fun x : X (m + 1) => (2 : ℝ) * (aP ℓ j (aP ℓ i Θ) x) ^ 2)
          (abox (m + 1) ℓ) volume := hintPj.const_mul 2
      have hint2 : IntegrableOn (fun x : X (m + 1) =>
            (2 : ℝ) * (aP ℓ i Θ x) ^ 2 + 2 * (aP ℓ j (aP ℓ i Θ) x) ^ 2)
          (abox (m + 1) ℓ) volume := hintA.add hintB
      calc ∫ x in abox (m + 1) ℓ, (Ψ x) ^ 2
          ≤ ∫ x in abox (m + 1) ℓ,
              ((2 : ℝ) * (aP ℓ i Θ x) ^ 2 + 2 * (aP ℓ j (aP ℓ i Θ) x) ^ 2) :=
            integral_mono_ae hintΨ hint2 (Filter.Eventually.of_forall hpt2)
        _ = 2 * (∫ x in abox (m + 1) ℓ, (aP ℓ i Θ x) ^ 2)
              + 2 * (∫ x in abox (m + 1) ℓ, (aP ℓ j (aP ℓ i Θ) x) ^ 2) := by
            rw [integral_add hintA hintB, integral_const_mul, integral_const_mul]
        _ ≤ 4 * ∫ x in abox (m + 1) ℓ, (Θ x) ^ 2 := by linarith
    -- ## the box integral of `H`
    have hmain : ∫ x in abox (m + 1) ℓ, H x
        ≤ (5 / 2) * ℓ ^ 3 * ∫ x in abox (m + 1) ℓ, (Θ x) ^ 2 := by
      have hI : (0 : ℝ) ≤ ∫ x in abox (m + 1) ℓ, (Θ x) ^ 2 :=
        integral_nonneg (fun x => sq_nonneg (Θ x))
      calc ∫ x in abox (m + 1) ℓ, H x
          = ∫ r : X m, (∫ w in acube ℓ, H (kcInsN m j (w, r))) ∂ν := hpeel
        _ = ∫ r : X m, Aa r * Bb r ∂ν := hstep1
        _ ≤ (1 / 2) * (∫ r : X m, (Aa r) ^ 2 ∂ν + ∫ r : X m, (Bb r) ^ 2 ∂ν) := hAB
        _ ≤ (5 / 2) * ℓ ^ 3 * ∫ x in abox (m + 1) ℓ, (Θ x) ^ 2 := by
            nlinarith [hAa2_le, hBb2_le, hΨ2, pow_pos hℓ 3, hI]
    have hH_eq_box : ∫ x : X (m + 1), H x = ∫ x in abox (m + 1) ℓ, H x :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hHsupp).symm
    have hΘ2_eq_box : ∫ x : X (m + 1), (Θ x) ^ 2 = ∫ x in abox (m + 1) ℓ, (Θ x) ^ 2 :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [hΘsupp x hx]; ring)).symm
    constructor
    · have hHind : H = (abox (m + 1) ℓ).indicator H := by
        funext x
        by_cases hx : x ∈ abox (m + 1) ℓ
        · rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx, hHsupp x hx]
      rw [hHind]
      exact (integrable_indicator_iff (abox_measurable (m + 1) ℓ)).mpr hHint
    · calc ∫ x : X (m + 1), H x
          = ∫ x in abox (m + 1) ℓ, H x := hH_eq_box
        _ ≤ (5 / 2) * ℓ ^ 3 * ∫ x in abox (m + 1) ℓ, (Θ x) ^ 2 := hmain
        _ = (5 / 2) * ℓ ^ 3 * ∫ x : X (m + 1), (Θ x) ^ 2 := by rw [hΘ2_eq_box]
        _ ≤ 8 * ℓ ^ 3 * ∫ x : X (m + 1), (Θ x) ^ 2 := by
            have hB : (0 : ℝ) ≤ ∫ x : X (m + 1), (Θ x) ^ 2 :=
              integral_nonneg (fun x => sq_nonneg (Θ x))
            nlinarith [hB, pow_pos hℓ 3]

end Work.BoseBoxFock.PCFU
