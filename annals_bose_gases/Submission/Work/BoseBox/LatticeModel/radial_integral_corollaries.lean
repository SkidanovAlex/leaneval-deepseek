import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Commons.Analysis.Integral.integral_Ioi_inv_sq_shift
import Submission.RadialIntegral
import Submission.Work.ModeLatticeR3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Radial-integral corollaries on `(Fin 3 → ℝ, eucNorm3)`

The spherical-coordinate evaluations used by the small-box Bogoliubov estimate,
together with the integrability criterion for a radial function on `ℝ³`, all on
the Pi-product Lebesgue measure of `Fin 3 → ℝ` with the Euclidean norm
`Submission.BoseGases.eucNorm3`:

* `∫ x, g (eucNorm3 x)` is integrable iff `r ↦ r² g r` is integrable on `(0,∞)`;
* `∫_{eucNorm3 ≤ R} ‖x‖⁻² = 4π R`  (the Coulomb potential of a ball);
* `∫_{A ≤ eucNorm3 ≤ B} ‖x‖⁻³ = 4π log(B/A)` (the annulus logarithm);
* `∫_{R ≤ eucNorm3} ‖x‖⁻⁴ = 4π/R`  (the `|p|⁻⁴`-type tail).

Everything is reduced to one-dimensional integrals in the radius by the
unconditional polar-coordinate identity `integral_eucNorm3_radial`,

    ∫ x, g (eucNorm3 x) = 4π ∫₀^∞ r² g r dr,

obtained from Mathlib's polar-coordinate change of variables
(`MeasureTheory.integral_fun_norm_addHaar`, instantiated on
`EuclideanSpace ℝ (Fin 3)` in `Submission.RadialIntegral`) transported along the
measure-preserving identification `WithLp.toLp 2 : (Fin 3 → ℝ) ≃ᵐ ℝ³`.
-/

namespace Work.BoseBox.LatticeModel

open MeasureTheory Set
open scoped Real

/-- `eucNorm3` is continuous (it is `u ↦ √(Σ uᵢ²)`). -/
lemma eucNorm3_continuous : Continuous (fun u : Fin 3 → ℝ => Submission.BoseGases.eucNorm3 u) := by
  simp only [Submission.BoseGases.eucNorm3]
  fun_prop

/-- `eucNorm3` is measurable. -/
lemma eucNorm3_measurable : Measurable (fun u : Fin 3 → ℝ => Submission.BoseGases.eucNorm3 u) :=
  eucNorm3_continuous.measurable

/-- `eucNorm3` is the Euclidean norm on `Fin 3 → ℝ`, i.e. the norm of the
corresponding point of `EuclideanSpace ℝ (Fin 3)`. -/
lemma eucNorm3_eq_euclidean_norm (u : Fin 3 → ℝ) :
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

/-- **Polar-coordinate reduction of a radial integral** (unconditional form, on
`Fin 3 → ℝ` with the Euclidean norm): only the radius matters and the
three-dimensional Jacobian is `4π r²`. -/
lemma integral_eucNorm3_radial (g : ℝ → ℝ) :
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
    rw [eucNorm3_eq_euclidean_norm]
  rw [h1]
  exact Submission.BoseGases.integral_fun_norm_r3 (g := g)

/-- **Integrability criterion for radial functions** on `(Fin 3 → ℝ, eucNorm3)`. -/
lemma integrable_eucNorm3_iff (g : ℝ → ℝ) :
    MeasureTheory.Integrable (fun x : Fin 3 → ℝ => g (Submission.BoseGases.eucNorm3 x))
        MeasureTheory.volume
      ↔ MeasureTheory.IntegrableOn (fun r : ℝ => r ^ 2 * g r) (Set.Ioi (0 : ℝ))
          MeasureTheory.volume := by
  have hmp : MeasurePreserving
      (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  have hemb : MeasurableEmbedding
      (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
  have htransfer : MeasureTheory.Integrable
      ((fun y : EuclideanSpace ℝ (Fin 3) => g ‖y‖) ∘
        (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3))) volume ↔
      MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) => g ‖y‖) volume :=
    hmp.integrable_comp_emb hemb
  have hfun : (fun x : Fin 3 → ℝ => g (Submission.BoseGases.eucNorm3 x))
      = (fun y : EuclideanSpace ℝ (Fin 3) => g ‖y‖) ∘
          (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)) := by
    funext x
    simp only [Function.comp_apply, eucNorm3_eq_euclidean_norm]
  rw [hfun]
  exact htransfer.trans Submission.BoseGases.integrable_radial_r3

/-- **Radial set integrals reduce to one-dimensional integrals.**  For a measurable
set `S ⊆ ℝ` of radii and any `F : ℝ → ℝ`,

    ∫_{eucNorm3 x ∈ S} F (eucNorm3 x) dx = 4π ∫₀^∞ r² · 1_S(r) F r dr . -/
lemma setIntegral_eucNorm3_eq (S : Set ℝ) (hS : MeasurableSet S) (F : ℝ → ℝ) :
    (∫ x in {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ∈ S},
        F (Submission.BoseGases.eucNorm3 x))
      = 4 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * S.indicator F r := by
  have hms : MeasurableSet {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ∈ S} :=
    eucNorm3_measurable hS
  rw [← MeasureTheory.integral_indicator hms]
  have hpt : ∀ x : Fin 3 → ℝ,
      {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ∈ S}.indicator
          (fun x => F (Submission.BoseGases.eucNorm3 x)) x
        = (S.indicator F) (Submission.BoseGases.eucNorm3 x) := by
    intro x
    by_cases hx : Submission.BoseGases.eucNorm3 x ∈ S
    · rw [Set.indicator_of_mem
            (show x ∈ {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ∈ S} from hx),
          Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem
            (show x ∉ {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ∈ S} from hx),
          Set.indicator_of_notMem hx]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_eucNorm3_radial]

/-- The one-dimensional radial integral of the `‖x‖⁻²` ball term:
`∫₀^∞ r² · 1_{r≤R} r⁻² dr = R` for `R ≥ 0`. -/
lemma radial_inv_sq_Iic (R : ℝ) (hR : 0 ≤ R) :
    (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * (Set.Iic R).indicator (fun r : ℝ => (1 : ℝ) / r ^ 2) r)
      = R := by
  have hpt : Set.EqOn
      (fun r : ℝ => r ^ 2 * (Set.Iic R).indicator (fun r : ℝ => (1 : ℝ) / r ^ 2) r)
      ((Set.Ioc (0 : ℝ) R).indicator (fun _ : ℝ => (1 : ℝ)))
      (Set.Ioi (0 : ℝ)) := by
    intro r hr
    show r ^ 2 * (Set.Iic R).indicator (fun r : ℝ => (1 : ℝ) / r ^ 2) r
      = (Set.Ioc (0 : ℝ) R).indicator (fun _ : ℝ => (1 : ℝ)) r
    by_cases hle : r ≤ R
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hle),
          Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hr, hle⟩)]
      have hr0 : r ≠ 0 := ne_of_gt hr
      field_simp
    · rw [Set.indicator_of_notMem (fun h => hle (Set.mem_Iic.mp h)),
          Set.indicator_of_notMem (fun h => hle h.2), mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
      setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.mpr (fun x hx => hx.1),
      setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hR)]
  simp

/-- The one-dimensional radial integral of the annulus term:
`∫₀^∞ r² · 1_{A≤r≤B} r⁻³ dr = log(B/A)` for `0 < A ≤ B`. -/
lemma radial_inv_cube_Icc (A B : ℝ) (hA : 0 < A) (hAB : A ≤ B) :
    (∫ r in Set.Ioi (0 : ℝ),
        r ^ 2 * (Set.Icc A B).indicator (fun r : ℝ => (1 : ℝ) / r ^ 3) r)
      = Real.log (B / A) := by
  have hpt : Set.EqOn
      (fun r : ℝ => r ^ 2 * (Set.Icc A B).indicator (fun r : ℝ => (1 : ℝ) / r ^ 3) r)
      ((Set.Icc A B).indicator (fun r : ℝ => r⁻¹))
      (Set.Ioi (0 : ℝ)) := by
    intro r _
    show r ^ 2 * (Set.Icc A B).indicator (fun r : ℝ => (1 : ℝ) / r ^ 3) r
      = (Set.Icc A B).indicator (fun r : ℝ => r⁻¹) r
    by_cases hmem : r ∈ Set.Icc A B
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le hA hmem.1)
      field_simp
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, mul_zero]
  have hinter : Set.Ioi (0 : ℝ) ∩ Set.Icc A B = Set.Icc A B :=
    Set.inter_eq_right.mpr fun x hx => lt_of_lt_of_le hA hx.1
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
      setIntegral_indicator measurableSet_Icc,
      hinter,
      MeasureTheory.integral_Icc_eq_integral_Ioo,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hAB,
      integral_inv_of_pos hA (lt_of_lt_of_le hA hAB)]

/-- The one-dimensional radial integral of the `|p|⁻⁴` tail:
`∫₀^∞ r² · 1_{R≤r} r⁻⁴ dr = 1/R` for `R > 0`. -/
lemma radial_inv_four_Ici (R : ℝ) (hR : 0 < R) :
    (∫ r in Set.Ioi (0 : ℝ),
        r ^ 2 * (Set.Ici R).indicator (fun r : ℝ => (1 : ℝ) / r ^ 4) r)
      = 1 / R := by
  have hpt : Set.EqOn
      (fun r : ℝ => r ^ 2 * (Set.Ici R).indicator (fun r : ℝ => (1 : ℝ) / r ^ 4) r)
      ((Set.Ici R).indicator (fun r : ℝ => (r⁻¹) ^ 2))
      (Set.Ioi (0 : ℝ)) := by
    intro r _
    show r ^ 2 * (Set.Ici R).indicator (fun r : ℝ => (1 : ℝ) / r ^ 4) r
      = (Set.Ici R).indicator (fun r : ℝ => (r⁻¹) ^ 2) r
    by_cases hmem : r ∈ Set.Ici R
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le hR (Set.mem_Ici.mp hmem))
      field_simp
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, mul_zero]
  have hinter : Set.Ioi (0 : ℝ) ∩ Set.Ici R = Set.Ici R :=
    Set.inter_eq_right.mpr fun x hx => lt_of_lt_of_le hR (Set.mem_Ici.mp hx)
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
      setIntegral_indicator measurableSet_Ici,
      hinter,
      MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hshift := Commons.Analysis.Integral.integral_Ioi_inv_sq_shift (c := 0) (T := R) hR
  simp only [sub_zero] at hshift
  have hcongr : (fun r : ℝ => (r⁻¹) ^ 2) = fun r : ℝ => r⁻¹ * r⁻¹ := by
    funext r
    rw [sq]
  rw [hcongr, hshift, one_div]

theorem radial_integral_corollaries :
    (∀ g : ℝ → ℝ, MeasureTheory.Integrable (fun x : Fin 3 → ℝ => g (Submission.BoseGases.eucNorm3 x)) MeasureTheory.volume ↔
        MeasureTheory.IntegrableOn (fun r : ℝ => r ^ 2 * g r) (Set.Ioi (0 : ℝ)) MeasureTheory.volume) ∧
    (∀ R : ℝ, 0 ≤ R →
      (∫ x in {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ≤ R},
          (1 : ℝ) / (Submission.BoseGases.eucNorm3 x) ^ 2) = 4 * Real.pi * R) ∧
    (∀ A B : ℝ, 0 < A → A ≤ B →
      (∫ x in {x : Fin 3 → ℝ | A ≤ Submission.BoseGases.eucNorm3 x ∧
          Submission.BoseGases.eucNorm3 x ≤ B},
          (1 : ℝ) / (Submission.BoseGases.eucNorm3 x) ^ 3)
        = 4 * Real.pi * Real.log (B / A)) ∧
    (∀ R : ℝ, 0 < R →
      (∫ x in {x : Fin 3 → ℝ | R ≤ Submission.BoseGases.eucNorm3 x},
          (1 : ℝ) / (Submission.BoseGases.eucNorm3 x) ^ 4) = 4 * Real.pi / R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) the integrability criterion
    intro g
    exact integrable_eucNorm3_iff g
  · -- (2) the `‖x‖⁻²` ball
    intro R hR
    show (∫ x in {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ∈ Set.Iic R},
        (fun r : ℝ => (1 : ℝ) / r ^ 2) (Submission.BoseGases.eucNorm3 x))
      = 4 * Real.pi * R
    rw [setIntegral_eucNorm3_eq (Set.Iic R) measurableSet_Iic (fun r : ℝ => (1 : ℝ) / r ^ 2),
        radial_inv_sq_Iic R hR]
  · -- (3) the `‖x‖⁻³` annulus
    intro A B hA hAB
    show (∫ x in {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ∈ Set.Icc A B},
        (fun r : ℝ => (1 : ℝ) / r ^ 3) (Submission.BoseGases.eucNorm3 x))
      = 4 * Real.pi * Real.log (B / A)
    rw [setIntegral_eucNorm3_eq (Set.Icc A B) measurableSet_Icc (fun r : ℝ => (1 : ℝ) / r ^ 3),
        radial_inv_cube_Icc A B hA hAB]
  · -- (4) the `‖x‖⁻⁴` tail
    intro R hR
    show (∫ x in {x : Fin 3 → ℝ | Submission.BoseGases.eucNorm3 x ∈ Set.Ici R},
        (fun r : ℝ => (1 : ℝ) / r ^ 4) (Submission.BoseGases.eucNorm3 x))
      = 4 * Real.pi / R
    rw [setIntegral_eucNorm3_eq (Set.Ici R) measurableSet_Ici (fun r : ℝ => (1 : ℝ) / r ^ 4),
        radial_inv_four_Ici R hR]
    ring

end Work.BoseBox.LatticeModel
