import Mathlib
import Submission.Work.BourgainPlan.KPWW.bump_family
import Submission.Work.BourgainPlan.IonescuWainger.opArc_eq_tsum_kernel
import Submission.Work.BourgainPlan.IonescuWainger.norm_opMul_le_of_kernel
import Submission.Work.IonescuWainger.young_count_lp

/-!
# The `ℓᵖ` bound for the arc multiplier from a summable coefficient sequence

Let `φ ∈ L^∞(𝕋)` have summable Fourier coefficients
`c m = ∫ φ · conj e_m`, `Σ_m ‖c m‖ ≤ K`, and let `E` be a finite set of arcs.  The multiplier
`opArc φ hφ E` with symbol `Σ_{β ∈ E} φ(· - β)` then acts as the convolution with the kernel

`m ↦ (Σ_{β ∈ E} conj e_m(β)) · c m`,

whose `ℓ¹` norm is at most `E.card * K`.  Young's inequality for the counting measure on `ℤ`
(`Work.IonescuWainger.young_count_lp`) therefore gives the `ℓᵖ → ℓᵖ` bound with constant
`E.card * K`, **for every** `p ≥ 1`, uniformly in `φ`, `E`, `c` and the scale.

This is the discrete heart of the KMSZ/KPWW projection bounds: the operator
`Π = opArc φ hφ E` is a convolution with an explicitly summable kernel, so the abstract
`ℓᵖ` theory of convolutions applies with no restriction on the support of `f`.
-/

open MeasureTheory
open scoped ENNReal BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.KPWW

/-- `eLpNorm` against the counting measure on `ℤ` as a (possibly infinite) `ℓ^q` sum. -/
private lemma eLpNorm_count_eq_tsum_ofReal (f : ℤ → ℂ) {q : ℝ} (hq : 0 < q) :
    MeasureTheory.eLpNorm f (ENNReal.ofReal q) MeasureTheory.Measure.count
      = (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ q)) ^ (1 / q) := by
  rw [MeasureTheory.eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
    MeasureTheory.AEStronglyMeasurable.of_discrete,
    MeasureTheory.eLpNorm', ENNReal.toReal_ofReal hq.le, MeasureTheory.lintegral_count]
  congr 1
  apply tsum_congr
  intro n
  rw [show ‖f n‖ₑ = ENNReal.ofReal ‖f n‖ by simp [enorm_eq_nnnorm],
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le]

/-- The `ℝ≥0∞`-majorant of a `ℂ`-valued series: `ofReal ‖Σ x‖ ≤ Σ ofReal ‖x‖`. -/
private lemma ofReal_norm_tsum_le' (x : ℤ → ℂ) :
    ENNReal.ofReal ‖∑' i : ℤ, x i‖ ≤ ∑' i : ℤ, ENNReal.ofReal ‖x i‖ := by
  simpa using enorm_tsum_le_tsum_enorm (f := x)

theorem opArc_lp_bound_of_coeff {p : ℝ} (hp : 1 ≤ p)
    {φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ}
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {c : ℤ → ℂ}
    (hcsum : Summable fun n : ℤ => ‖c n‖)
    (hc : ∀ n : ℤ, ∫ θ, φ θ * star (fourier n θ) ∂(AddCircle.haarAddCircle (T := 1)) = c n)
    {K : ℝ} (hcK : (∑' n : ℤ, ‖c n‖) ≤ K) (E : Finset Work.BourgainPlan.IonescuWainger.Circle)
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    MeasureTheory.eLpNorm (fun n : ℤ =>
        Work.BourgainPlan.IonescuWainger.opArc φ hφ E f hf n)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((E.card : ℝ) * K)
        * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hcard : (0 : ℝ) ≤ (E.card : ℝ) := Nat.cast_nonneg _
  set w : ℤ → ENNReal := fun m => ENNReal.ofReal ‖(∑ β ∈ E, star (fourier m β)) * c m‖ with hwdef
  set g : ℤ → ENNReal := fun k => ENNReal.ofReal ‖f k‖ with hgdef
  -- ## The `ℓ¹` bound on the convolution kernel
  have hnorm_le : ∀ m : ℤ, w m ≤ ENNReal.ofReal (E.card : ℝ) * ENNReal.ofReal ‖c m‖ := by
    intro m
    have h1 : ‖(∑ β ∈ E, star (fourier m β)) * c m‖ ≤ (E.card : ℝ) * ‖c m‖ := by
      rw [norm_mul]
      have h2 : ‖∑ β ∈ E, star (fourier m β)‖ ≤ (E.card : ℝ) := by
        calc ‖∑ β ∈ E, star (fourier m β)‖ ≤ ∑ β ∈ E, ‖star (fourier m β)‖ := norm_sum_le _ _
          _ = ∑ _β ∈ E, (1 : ℝ) := Finset.sum_congr rfl (fun β _ => by
                rw [norm_star, Work.BourgainPlan.IonescuWainger.norm_fourier_apply'])
          _ = (E.card : ℝ) := by simp
      exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    calc w m = ENNReal.ofReal ‖(∑ β ∈ E, star (fourier m β)) * c m‖ := by simp only [hwdef]
      _ ≤ ENNReal.ofReal ((E.card : ℝ) * ‖c m‖) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (E.card : ℝ) * ENNReal.ofReal ‖c m‖ := ENNReal.ofReal_mul hcard
  have hsumw : (∑' m : ℤ, w m) ≤ ENNReal.ofReal ((E.card : ℝ) * K) := by
    calc ∑' m : ℤ, w m
        ≤ ∑' m : ℤ, (ENNReal.ofReal (E.card : ℝ) * ENNReal.ofReal ‖c m‖) :=
          ENNReal.tsum_le_tsum hnorm_le
      _ = ENNReal.ofReal (E.card : ℝ) * ∑' m : ℤ, ENNReal.ofReal ‖c m‖ :=
          ENNReal.tsum_mul_left
      _ = ENNReal.ofReal (E.card : ℝ) * ENNReal.ofReal (∑' m : ℤ, ‖c m‖) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun m : ℤ => ‖c m‖)
            (fun m => norm_nonneg _) hcsum]
      _ ≤ ENNReal.ofReal (E.card : ℝ) * ENNReal.ofReal K :=
          mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hcK)
      _ = ENNReal.ofReal ((E.card : ℝ) * K) := (ENNReal.ofReal_mul hcard).symm
  -- ## The pointwise domination by the convolution with `w`
  have hpoint : ∀ n : ℤ, ENNReal.ofReal
        (‖Work.BourgainPlan.IonescuWainger.opArc φ hφ E f hf n‖ ^ p)
      ≤ (∑' k : ℤ, w k * g (n - k)) ^ p := by
    intro n
    have h1 : ENNReal.ofReal ‖Work.BourgainPlan.IonescuWainger.opArc φ hφ E f hf n‖
        ≤ ∑' k : ℤ, g k * w (n - k) := by
      rw [Work.BourgainPlan.IonescuWainger.opArc_eq_tsum_kernel φ hφ hc E f hf n]
      calc ENNReal.ofReal ‖∑' k : ℤ, f k * ((∑ β ∈ E, star (fourier (n - k) β)) * c (n - k))‖
          ≤ ∑' k : ℤ, ENNReal.ofReal
              ‖f k * ((∑ β ∈ E, star (fourier (n - k) β)) * c (n - k))‖ :=
            ofReal_norm_tsum_le' _
        _ = ∑' k : ℤ, g k * w (n - k) := by
            refine tsum_congr fun k => ?_
            simp only [hwdef, hgdef]
            rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg (f k))]
    have hswap : (∑' k : ℤ, g k * w (n - k)) = ∑' k : ℤ, w k * g (n - k) := by
      rw [← Equiv.tsum_eq (Equiv.subLeft n) (fun j : ℤ => w j * g (n - j))]
      refine tsum_congr fun k => ?_
      rw [Equiv.subLeft_apply]
      have hnk : n - (n - k) = k := by ring
      rw [hnk, mul_comm]
    calc ENNReal.ofReal (‖Work.BourgainPlan.IonescuWainger.opArc φ hφ E f hf n‖ ^ p)
        = (ENNReal.ofReal ‖Work.BourgainPlan.IonescuWainger.opArc φ hφ E f hf n‖) ^ p :=
          (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le).symm
      _ ≤ (∑' k : ℤ, g k * w (n - k)) ^ p := ENNReal.rpow_le_rpow h1 hp0.le
      _ = (∑' k : ℤ, w k * g (n - k)) ^ p := by rw [hswap]
  -- ## Assembling: Young's inequality and the `eLpNorm` bookkeeping
  have hS1 : MeasureTheory.eLpNorm (fun n : ℤ =>
        Work.BourgainPlan.IonescuWainger.opArc φ hφ E f hf n)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      = (∑' n : ℤ, ENNReal.ofReal
          (‖Work.BourgainPlan.IonescuWainger.opArc φ hφ E f hf n‖ ^ p)) ^ (1 / p) :=
    eLpNorm_count_eq_tsum_ofReal _ hp0
  have hS2 : (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p)) = ∑' n : ℤ, g n ^ p := by
    refine tsum_congr fun n => ?_
    simp only [hgdef]
    exact (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le).symm
  have hstep : (∑' n : ℤ, ENNReal.ofReal
        (‖Work.BourgainPlan.IonescuWainger.opArc φ hφ E f hf n‖ ^ p))
      ≤ (∑' k : ℤ, w k) ^ p * ∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p) :=
    calc ∑' n : ℤ, ENNReal.ofReal
          (‖Work.BourgainPlan.IonescuWainger.opArc φ hφ E f hf n‖ ^ p)
        ≤ ∑' n : ℤ, (∑' k : ℤ, w k * g (n - k)) ^ p := ENNReal.tsum_le_tsum hpoint
      _ ≤ (∑' k : ℤ, w k) ^ p * ∑' n : ℤ, g n ^ p :=
          Work.IonescuWainger.young_count_lp hp w g
      _ = (∑' k : ℤ, w k) ^ p * ∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p) := by rw [← hS2]
  rw [hS1, eLpNorm_count_eq_tsum_ofReal f hp0]
  calc (∑' n : ℤ, ENNReal.ofReal
        (‖Work.BourgainPlan.IonescuWainger.opArc φ hφ E f hf n‖ ^ p)) ^ (1 / p)
      ≤ ((∑' k : ℤ, w k) ^ p * ∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hstep (one_div_pos.mpr hp0).le
    _ = (∑' k : ℤ, w k) * (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p)) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hp0).le, ← ENNReal.rpow_mul,
          show p * (1 / p) = 1 by field_simp, ENNReal.rpow_one]
    _ ≤ ENNReal.ofReal ((E.card : ℝ) * K)
          * (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p)) ^ (1 / p) :=
        mul_le_mul' hsumw le_rfl

end Work.BourgainPlan.KPWW
