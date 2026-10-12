import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.RadialIntegral
import Submission.Work.ModeLatticeR3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The lattice model of the Bogoliubov integral — shared definitions

This module collects the objects that the proof of
`Work.BoseBox.lattice_sum_model_euclid` is phrased in:

* `lhyProfile c r` — the (radial) Bogoliubov model bracket
  `(r²+c) − √((r²+c)²−c²) − c²/(2r²)`, rewritten in the rationalised form
  `c²/((r²+c) + r√(r²+2c)) − c²/(2r²)` (the two agree for `r ≥ 0`; the
  rationalised form is the one that is algebraically controllable);
* `latticeCenter h N k` — the centre of the lattice cell of index
  `k : Fin 3 → Fin N` for the grid of mesh `h` straddling the origin as in the
  FS normalisation, i.e. `k ↦ h·(k − N/2)`;
* `latticeCell h N k` — the half-open cell of side `h` around that centre;
* `latticeBox h N` — the union of all cells (a cube of side `h·N`).

We also record the basic `eucNorm3` facts (the Euclidean norm on `Fin 3 → ℝ`,
realised as the norm on `EuclideanSpace ℝ (Fin 3)` transported along
`WithLp.toLp 2`), the unconditional radial-integration formula
`∫ x, g (eucNorm3 x) = 4π ∫₀^∞ r² g r dr`, and the volume of an
`eucNorm3`-ball.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBox

/-- The radial Bogoliubov model bracket, in rationalised form:
`c²/((r²+c) + r√(r²+2c)) − c²/(2r²)`.  For `r ≥ 0` this is
`(r²+c) − √((r²+c)²−c²) − c²/(2r²)`. -/
noncomputable def lhyProfile (c r : ℝ) : ℝ :=
  c ^ 2 / ((r ^ 2 + c) + r * Real.sqrt (r ^ 2 + 2 * c)) - c ^ 2 / (2 * r ^ 2)

/-- The centre `h·(k − N/2)` of the lattice cell with multi-index `k`. -/
noncomputable def latticeCenter (h : ℝ) (N : ℕ) (k : Fin 3 → Fin N) : Fin 3 → ℝ :=
  fun j => h * ((k j : ℝ) - (N : ℝ) / 2)

/-- The half-open cell of side `h` around `latticeCenter h N k`. -/
noncomputable def latticeCell (h : ℝ) (N : ℕ) (k : Fin 3 → Fin N) : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ
    (fun j : Fin 3 => Set.Ico (latticeCenter h N k j - h / 2) (latticeCenter h N k j + h / 2))

/-- The cube `[−hN/2 − h/2, hN/2 − h/2]³` covered by the lattice cells. -/
noncomputable def latticeBox (h : ℝ) (N : ℕ) : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ
    (fun _ : Fin 3 => Set.Ico (-(h * (N : ℝ) / 2 + h / 2)) (h * (N : ℝ) / 2 - h / 2))

/-- `eucNorm3` is continuous. -/
lemma continuous_eucNorm3 : Continuous (fun u : Fin 3 → ℝ => Submission.BoseGases.eucNorm3 u) := by
  simp only [Submission.BoseGases.eucNorm3]
  fun_prop

/-- `eucNorm3` is measurable. -/
lemma measurable_eucNorm3 : Measurable (fun u : Fin 3 → ℝ => Submission.BoseGases.eucNorm3 u) :=
  continuous_eucNorm3.measurable

/-- `eucNorm3` is the norm of the corresponding point of `EuclideanSpace ℝ (Fin 3)`. -/
lemma eucNorm3_eq_norm (u : Fin 3 → ℝ) :
    Submission.BoseGases.eucNorm3 u = ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 3))‖ := by
  rw [PiLp.norm_eq_sum (show (0 : ℝ) < (2 : ENNReal).toReal by norm_num)]
  have h1 : ∀ i : Fin 3,
      ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin 3)).ofLp i‖ ^ (2 : ENNReal).toReal
        = (u i) ^ 2 := by
    intro i
    rw [WithLp.ofLp_toLp, Real.norm_eq_abs]
    have h2 : (2 : ENNReal).toReal = 2 := by norm_num
    rw [h2, Real.rpow_two]
    exact sq_abs (u i)
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  simp only [Submission.BoseGases.eucNorm3]
  norm_num
  rw [Real.sqrt_eq_rpow]

/-- Triangle inequality for `eucNorm3`. -/
lemma eucNorm3_sub_le (u v : Fin 3 → ℝ) :
    Submission.BoseGases.eucNorm3 (u - v)
      ≤ Submission.BoseGases.eucNorm3 u + Submission.BoseGases.eucNorm3 v := by
  rw [eucNorm3_eq_norm u, eucNorm3_eq_norm v, eucNorm3_eq_norm (u - v), WithLp.toLp_sub]
  exact norm_sub_le _ _

/-- Reverse triangle inequality for `eucNorm3`. -/
lemma eucNorm3_abs_sub_le (u v : Fin 3 → ℝ) :
    |Submission.BoseGases.eucNorm3 u - Submission.BoseGases.eucNorm3 v|
      ≤ Submission.BoseGases.eucNorm3 (u - v) := by
  rw [eucNorm3_eq_norm u, eucNorm3_eq_norm v, eucNorm3_eq_norm (u - v), WithLp.toLp_sub]
  exact abs_norm_sub_norm_le _ _

/-- **Radial integration on `(Fin 3 → ℝ, eucNorm3)`** (unconditional form, on the
Pi-product Lebesgue measure): only the radius matters, and the 3-dimensional
Jacobian is `4π r²`. -/
theorem integral_eucNorm3_fun (g : ℝ → ℝ) :
    (∫ x : Fin 3 → ℝ, g (Submission.BoseGases.eucNorm3 x))
      = 4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r := by
  have hmp : MeasurePreserving
      (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  have h1 : (∫ x : Fin 3 → ℝ, g (Submission.BoseGases.eucNorm3 x))
      = ∫ y : EuclideanSpace ℝ (Fin 3), g ‖y‖ := by
    rw [← hmp.integral_comp (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
      (fun y : EuclideanSpace ℝ (Fin 3) => g ‖y‖)]
    apply integral_congr_ae
    filter_upwards with x
    rw [eucNorm3_eq_norm]
  rw [h1]
  exact Submission.BoseGases.integral_fun_norm_r3 (g := g)

/-- **Integrability criterion** for radial functions on `(Fin 3 → ℝ, eucNorm3)`. -/
theorem integrable_eucNorm3_fun_iff (g : ℝ → ℝ) :
    MeasureTheory.Integrable (fun x : Fin 3 → ℝ => g (Submission.BoseGases.eucNorm3 x))
        MeasureTheory.volume
      ↔ MeasureTheory.IntegrableOn (fun r : ℝ => r ^ 2 * g r) (Set.Ioi (0 : ℝ))
          MeasureTheory.volume := by
  have hmp : MeasurePreserving
      (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  have hfun : (fun x : Fin 3 → ℝ => g (Submission.BoseGases.eucNorm3 x))
      = ((fun y : EuclideanSpace ℝ (Fin 3) => g ‖y‖) ∘ (WithLp.toLp 2)) := by
    funext x
    simp only [Function.comp_apply, eucNorm3_eq_norm]
  rw [hfun, hmp.integrable_comp_emb (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
    (g := fun y : EuclideanSpace ℝ (Fin 3) => g ‖y‖)]
  exact Submission.BoseGases.integrable_radial_r3 (f := g)

/-- Every coordinate is bounded by `eucNorm3`. -/
lemma abs_apply_le_eucNorm3 (u : Fin 3 → ℝ) (j : Fin 3) :
    |u j| ≤ Submission.BoseGases.eucNorm3 u := by
  rw [show Submission.BoseGases.eucNorm3 u = Real.sqrt (∑ i : Fin 3, (u i) ^ 2) from rfl]
  rw [Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  calc (|u j|) ^ 2 = (u j) ^ 2 := sq_abs (u j)
    _ ≤ ∑ i : Fin 3, (u i) ^ 2 := Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ j)

/-- The `eucNorm3`-ball has finite volume. -/
lemma volume_eucNorm3_ball_lt_top {R : ℝ} :
    MeasureTheory.volume {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ≤ R} < ⊤ := by
  by_cases hR : 0 ≤ R
  · refine lt_of_le_of_lt (MeasureTheory.measure_mono (fun x hx => ?_))
      (isCompact_closedBall (0 : Fin 3 → ℝ) R).measure_lt_top
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hR).mpr
      (fun j => (abs_apply_le_eucNorm3 x j).trans hx)
  · have hE : {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ≤ R} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      have := Submission.BoseGases.eucNorm3_nonneg x
      linarith
    rw [hE]; simp

/-- The `eucNorm3`-ball of radius `R` has volume `4πR³/3`. -/
theorem volume_eucNorm3_ball_toReal {R : ℝ} (hR : 0 ≤ R) :
    (volume {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ≤ R}).toReal
      = 4 * Real.pi * R ^ 3 / 3 := by
  have h1d : (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * (if r ≤ R then (1 : ℝ) else 0))
      = R ^ 3 / 3 := by
    have hfun : ∀ r ∈ Set.Ioi (0 : ℝ), r ^ 2 * (if r ≤ R then (1 : ℝ) else 0)
        = (Set.Ioc (0 : ℝ) R).indicator (fun r => r ^ 2) r := by
      intro r hr
      by_cases hle : r ≤ R
      · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hr, hle⟩), if_pos hle, mul_one]
      · rw [Set.indicator_of_notMem (fun h => hle h.2), if_neg hle, mul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi hfun]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc]
    rw [show Set.Ioi (0 : ℝ) ∩ Set.Ioc (0 : ℝ) R = Set.Ioc (0 : ℝ) R by
      ext r; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]; tauto]
    rw [← intervalIntegral.integral_of_le hR, integral_pow]
    norm_num
  have h : (∫ x in {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ≤ R}, (1 : ℝ))
      = 4 * Real.pi * R ^ 3 / 3 := by
    rw [show (∫ x in {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ≤ R}, (1 : ℝ))
        = (∫ x : Fin 3 → ℝ,
            (fun x => if Submission.BoseGases.eucNorm3 x ≤ R then (1 : ℝ) else 0) x) from ?_]
    · rw [integral_eucNorm3_fun (g := fun r => if r ≤ R then (1 : ℝ) else 0), h1d]
      ring
    · rw [← integral_indicator
        (s := {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ≤ R})
        (measurableSet_le measurable_eucNorm3 measurable_const)]
      rfl
  rw [MeasureTheory.setIntegral_const] at h
  simpa [MeasureTheory.Measure.real] using h

end Work.BoseBox
