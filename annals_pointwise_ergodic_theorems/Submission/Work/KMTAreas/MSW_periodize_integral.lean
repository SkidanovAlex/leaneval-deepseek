/-
# The periodisation (de Leeuw transfer) integral identity

For a Schwartz function `φ : ℝ → ℂ`, a continuous function `X` on the frequency circle
`ℝ/ℤ` and a shift `c : ℝ`, the integral against Haar measure of the product of the
periodisation `periodize φ` (composed with the translation by `-c`) with `X` equals the
integral over `ℝ` of `φ(x) · X(x + c)`.

This is the "unfolding" of the periodisation used in the de Leeuw transfer argument: the
circle integral of the periodised symbol is the sum over the unit intervals tiling `ℝ`
(here shifted by `c`), where the circle-valued factor `X` only depends on the class of the
argument modulo `1`.

The proof reduces, by the invariance of Haar measure under translation, to the case `c = 0`,
rewrites the circle integral as an integral over the fundamental domain `(0,1]`, replaces
`periodize φ` by the sum of its integer shifts on `[0,1)`, exchanges the sum and the
integral (with the summable domination coming from the Schwartz decay), and reassembles the
unit intervals `(k, k+1]` into `ℝ`.
-/
import Mathlib
import Submission.Work.KMTAreas.MSW_defs
import Submission.Work.KMTAreas.schwartz_shift_summable
import Submission.Work.KMTAreas.summable_integral_shift_norm

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal
open MeasureTheory

namespace Work.KMTAreas

open Work.Analysis.IonescuWainger

/-- The frequency circle `ℝ/ℤ`. -/
local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## Elementary manipulations -/

/-- Adding an integer to a real number does not change its class in the circle. -/
private lemma circle_coe_add_int (x : ℝ) (k : ℤ) :
    (((x + (k : ℝ)) : ℝ) : Circ) = ((x : ℝ) : Circ) := by
  rw [AddCircle.coe_add]
  have hk : (((k : ℝ)) : Circ) = 0 := by
    rw [show (k : ℝ) = k • (1 : ℝ) by simp, AddCircle.coe_zsmul, AddCircle.coe_period,
      smul_zero]
  rw [hk, add_zero]

/-- The circle integral of a function is the integral over the fundamental domain `(0,1]`. -/
private lemma integral_circle_eq_Ioc (F : Circ → ℂ) :
    ∫ t : Circ, F t ∂circleMeasure = ∫ a in Set.Ioc (0 : ℝ) 1, F ((a : ℝ) : Circ) := by
  rw [circleMeasure, AddCircle.integral_haarAddCircle (T := 1)]
  rw [← AddCircle.integral_preimage (T := 1) (t := 0) F]
  simp only [zero_add]
  norm_num

/-- On the fundamental domain `[0,1)` the periodisation of a Schwartz function is the sum of its
integer shifts. -/
private lemma periodize_coe_Ico (φ : SchwartzMap ℝ ℂ) {a : ℝ} (ha : a ∈ Set.Ico (0 : ℝ) 1) :
    periodize (φ : ℝ → ℂ) ((a : ℝ) : Circ) = ∑' k : ℤ, (φ : ℝ → ℂ) (a + (k : ℝ)) := by
  rw [periodize]
  congr 1 with k
  congr 1
  have h := AddCircle.equivIco_coe_of_mem (p := (1 : ℝ)) (a := (0 : ℝ)) (y := a)
    (by simpa using ha)
  simpa using h

/-! ## The case `c = 0` -/

private theorem periodize_integral_zero (φ : SchwartzMap ℝ ℂ) (X : Circ → ℂ)
    (hX : Continuous X) :
    ∫ t : Circ, periodize (φ : ℝ → ℂ) t * X t ∂circleMeasure
      = ∫ x : ℝ, (φ : ℝ → ℂ) x * X ((x : ℝ) : Circ) := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn (s := Set.univ) hX.continuousOn
  set M' : ℝ := max M 0 with hM'def
  have hM' : ∀ t : Circ, ‖X t‖ ≤ M' := fun t => le_trans (hM t trivial) (le_max_left _ _)
  have hM'0 : 0 ≤ M' := le_max_right _ _
  rw [integral_circle_eq_Ioc (fun t : Circ => periodize (φ : ℝ → ℂ) t * X t)]
  let f : ℝ → ℂ := fun u => (φ : ℝ → ℂ) u * X ((u : ℝ) : Circ)
  have hfcont : Continuous f := by
    dsimp only [f]
    exact (SchwartzMap.continuous φ).mul (hX.comp (AddCircle.continuous_mk' (1 : ℝ)))
  -- the integrand is the sum of its shifts, almost everywhere on `(0,1]`
  have hcongr :
      (∫ a in Set.Ioc (0 : ℝ) 1,
          periodize (φ : ℝ → ℂ) ((a : ℝ) : Circ) * X ((a : ℝ) : Circ))
        = ∫ a in Set.Ioc (0 : ℝ) 1,
            ∑' k : ℤ, (φ : ℝ → ℂ) (a + (k : ℝ)) * X ((a : ℝ) : Circ) := by
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    have hnull : ∀ᵐ a ∂(volume : Measure ℝ), a ≠ 1 := by
      rw [ae_iff]
      simp
    filter_upwards [hnull] with a ha1 ha
    have haIoo : a ∈ Set.Ioo (0 : ℝ) 1 := ⟨ha.1, lt_of_le_of_ne ha.2 ha1⟩
    have hsum : Summable (fun k : ℤ => (φ : ℝ → ℂ) (a + (k : ℝ))) :=
      (schwartz_shift_summable φ a).of_norm
    rw [periodize_coe_Ico φ (Set.Ioo_subset_Ico_self haIoo),
      ← Summable.tsum_mul_right (X ((a : ℝ) : Circ)) hsum]
  -- integrability and summability of the shifted pieces
  have hφk_int : ∀ k : ℤ, Integrable (fun a : ℝ => (φ : ℝ → ℂ) (a + (k : ℝ)))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := fun k =>
    (φ.integrable.comp_add_right (k : ℝ)).integrableOn
  have hF_int : ∀ k : ℤ,
      Integrable (fun a : ℝ => (φ : ℝ → ℂ) (a + (k : ℝ)) * X ((a : ℝ) : Circ))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro k
    refine Integrable.mono' ((hφk_int k).norm.const_mul M') ?_ ?_
    · exact (((SchwartzMap.continuous φ).comp (continuous_id.add_const (k : ℝ))).mul
        (hX.comp (AddCircle.continuous_mk' (1 : ℝ)))).aestronglyMeasurable
    · filter_upwards with a
      calc ‖(φ : ℝ → ℂ) (a + (k : ℝ)) * X ((a : ℝ) : Circ)‖
          = ‖(φ : ℝ → ℂ) (a + (k : ℝ))‖ * ‖X ((a : ℝ) : Circ)‖ := norm_mul _ _
        _ ≤ ‖(φ : ℝ → ℂ) (a + (k : ℝ))‖ * M' :=
              mul_le_mul_of_nonneg_left (hM' _) (norm_nonneg _)
        _ = M' * ‖(φ : ℝ → ℂ) (a + (k : ℝ))‖ := by ring
  have hF_sum : Summable (fun k : ℤ =>
      ∫ a, ‖(φ : ℝ → ℂ) (a + (k : ℝ)) * X ((a : ℝ) : Circ)‖
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    have hB : Summable (fun k : ℤ =>
        M' * ∫ a, ‖(φ : ℝ → ℂ) (a + (k : ℝ))‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
      (summable_integral_shift_norm φ).mul_left M'
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (fun a => norm_nonneg _))
      (fun k => ?_) hB
    calc ∫ a, ‖(φ : ℝ → ℂ) (a + (k : ℝ)) * X ((a : ℝ) : Circ)‖
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))
        ≤ ∫ a, M' * ‖(φ : ℝ → ℂ) (a + (k : ℝ))‖
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
          refine integral_mono ((hF_int k).norm) ((hφk_int k).norm.const_mul M') ?_
          intro a
          calc ‖(φ : ℝ → ℂ) (a + (k : ℝ)) * X ((a : ℝ) : Circ)‖
              = ‖(φ : ℝ → ℂ) (a + (k : ℝ))‖ * ‖X ((a : ℝ) : Circ)‖ := norm_mul _ _
            _ ≤ ‖(φ : ℝ → ℂ) (a + (k : ℝ))‖ * M' :=
                  mul_le_mul_of_nonneg_left (hM' _) (norm_nonneg _)
            _ = M' * ‖(φ : ℝ → ℂ) (a + (k : ℝ))‖ := by ring
      _ = M' * ∫ a, ‖(φ : ℝ → ℂ) (a + (k : ℝ))‖
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := integral_const_mul M' _
  have hHS := hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) hF_int hF_sum
  have hf_int : Integrable f volume := by
    have hφint : Integrable (fun u : ℝ => (φ : ℝ → ℂ) u) volume := φ.integrable
    refine Integrable.mono' (hφint.norm.const_mul M') hfcont.aestronglyMeasurable ?_
    filter_upwards with u
    calc ‖f u‖ = ‖(φ : ℝ → ℂ) u‖ * ‖X ((u : ℝ) : Circ)‖ := by
          dsimp only [f]
          rw [norm_mul]
      _ ≤ ‖(φ : ℝ → ℂ) u‖ * M' := mul_le_mul_of_nonneg_left (hM' _) (norm_nonneg _)
      _ = M' * ‖(φ : ℝ → ℂ) u‖ := by ring
  have hterm : ∀ k : ℤ,
      (∫ a in Set.Ioc (0 : ℝ) 1, (φ : ℝ → ℂ) (a + (k : ℝ)) * X ((a : ℝ) : Circ))
        = ∫ x in (0 : ℝ)..1, f (x + (k : ℝ)) := by
    intro k
    rw [intervalIntegral.integral_of_le (zero_le_one)]
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    filter_upwards with a _
    dsimp only [f]
    rw [circle_coe_add_int a k]
  calc ∫ a in Set.Ioc (0 : ℝ) 1,
          periodize (φ : ℝ → ℂ) ((a : ℝ) : Circ) * X ((a : ℝ) : Circ)
      = ∫ a in Set.Ioc (0 : ℝ) 1,
          ∑' k : ℤ, (φ : ℝ → ℂ) (a + (k : ℝ)) * X ((a : ℝ) : Circ) := hcongr
    _ = ∑' k : ℤ, ∫ a in Set.Ioc (0 : ℝ) 1,
          (φ : ℝ → ℂ) (a + (k : ℝ)) * X ((a : ℝ) : Circ) := hHS.tsum_eq.symm
    _ = ∑' k : ℤ, ∫ x in (0 : ℝ)..1, f (x + (k : ℝ)) := tsum_congr (fun k => hterm k)
    _ = ∫ x : ℝ, f x := hf_int.hasSum_intervalIntegral_comp_add_int.tsum_eq
    _ = ∫ x : ℝ, (φ : ℝ → ℂ) x * X ((x : ℝ) : Circ) := by rfl

/-! ## The general shift -/

theorem MSW_periodize_integral (φ : SchwartzMap ℝ ℂ)
    (X : Work.Analysis.IonescuWainger.Circle → ℂ) (hX : Continuous X) (c : ℝ) :
    ∫ t : Work.Analysis.IonescuWainger.Circle,
        Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ)
          (t - (c : Work.Analysis.IonescuWainger.Circle)) * X t
        ∂Work.Analysis.IonescuWainger.circleMeasure
      = ∫ x : ℝ, (φ : ℝ → ℂ) x * X (((x : ℝ) : Work.Analysis.IonescuWainger.Circle)
          + (c : Work.Analysis.IonescuWainger.Circle)) := by
  have hshift : (∫ t : Circ, periodize (φ : ℝ → ℂ) (t - (c : Circ)) * X t ∂circleMeasure)
      = ∫ s : Circ, periodize (φ : ℝ → ℂ) s * X (s + (c : Circ)) ∂circleMeasure := by
    have h := integral_add_right_eq_self (μ := circleMeasure)
      (fun t : Circ => periodize (φ : ℝ → ℂ) (t - (c : Circ)) * X t) (c : Circ)
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h.symm
  rw [hshift]
  exact periodize_integral_zero φ (fun s : Circ => X (s + (c : Circ)))
    (hX.comp (continuous_add_const (c : Circ)))

end Work.KMTAreas
