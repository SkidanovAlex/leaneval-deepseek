import Mathlib
import Submission.Work.BourgainPlan.Maximal.major_arc_model
import Submission.Work.BourgainPlan.IonescuWainger.OpArcLinear
import Submission.Work.BourgainPlan.KPWW.opArc_lp_bound_of_coeff
import Submission.Work.BourgainPlan.IonescuWainger.opArc_eq_tsum_kernel
import Submission.Work.IonescuWainger.young_count_lp

namespace Work.Maximal

open MeasureTheory
open scoped ENNReal BigOperators

set_option autoImplicit false

local notation "Circle" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haar" => (AddCircle.haarAddCircle (T := 1))

/-- `eLpNorm` against the counting measure on `ℤ` as a (possibly infinite) `ℓ^q` sum. -/
private lemma eLpNorm_count_eq_tsum_ofReal (f : ℤ → ℂ) {q : ℝ} (hq : 0 < q) :
    MeasureTheory.eLpNorm f (ENNReal.ofReal q) MeasureTheory.Measure.count
      = (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ q)) ^ (1 / q) := by
  rw [MeasureTheory.eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
      (measurable_of_countable f).aestronglyMeasurable,
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

/-- **The Fourier coefficients of a weighted arc symbol.**  With `c m = ∫ φ · conj e_m`, the `m`-th
coefficient of `Σ_{β ∈ Es} w β · φ(· - β)` is `(Σ_{β ∈ Es} w β · conj e_m(β)) · c m`. -/
private lemma integral_arcSymbolW_mul_fourier (φ : Circle → ℂ) (hφ : MemLp φ ⊤ haar)
    {c : ℤ → ℂ} (hc : ∀ m : ℤ, ∫ ξ, φ ξ * star (fourier m ξ) ∂haar = c m)
    (w : Circle → ℂ) (Es : Finset Circle) (m : ℤ) :
    ∫ ξ, Work.BourgainPlan.Maximal.arcSymbolW (fun β : Circle => β) w Es φ ξ
        * star (fourier m ξ) ∂haar
      = (∑ β ∈ Es, w β * star (fourier m β)) * c m := by
  have hpoint : (fun ξ : Circle =>
        Work.BourgainPlan.Maximal.arcSymbolW (fun β : Circle => β) w Es φ ξ
          * star (fourier m ξ))
      = fun ξ : Circle => ∑ β ∈ Es, w β * (φ (ξ - β) * star (fourier m ξ)) := by
    funext ξ
    rw [Work.BourgainPlan.Maximal.arcSymbolW_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun β _ => by ring)
  rw [hpoint]
  rw [MeasureTheory.integral_finsetSum Es (fun β _ => ?_)]
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    have htr : ∫ a : Circle, φ (a - β) * star (fourier m a) ∂haar
        = star (fourier m β) * ∫ a : Circle, φ a * star (fourier m a) ∂haar :=
      Work.BourgainPlan.IonescuWainger.fourierCoeff_arcTranslate φ hφ β m
    rw [MeasureTheory.integral_const_mul, htr, hc m]
    ring
  · have hArc : MemLp (Work.BourgainPlan.IonescuWainger.arcTranslate β φ) ⊤ haar :=
      Work.BourgainPlan.IonescuWainger.memLp_arcTranslate hφ β
    have hfour : MemLp (fun ξ : Circle => star (fourier m ξ)) ⊤ haar :=
      MemLp.of_bound ((fourier m).continuous.aestronglyMeasurable.star) 1 (by
        filter_upwards with ξ
        rw [norm_star, Work.BourgainPlan.IonescuWainger.norm_fourier_apply' m ξ])
    have hmem : MemLp (fun ξ : Circle =>
        Work.BourgainPlan.IonescuWainger.arcTranslate β φ ξ * star (fourier m ξ)) ⊤ haar :=
      MemLp.of_le hArc (hArc.aestronglyMeasurable.mul hfour.aestronglyMeasurable) (by
        filter_upwards with ξ
        rw [norm_mul, norm_star, Work.BourgainPlan.IonescuWainger.norm_fourier_apply' m ξ,
          mul_one])
    exact ((hmem.mono_exponent le_top).integrable le_rfl).const_mul _

/-- **Young's inequality for a *weighted* arc symbol.**  Let `φ ∈ L^∞(𝕋)` have summable Fourier coefficients `c m = ∫ φ · conj e_m` of total mass `≤ K`, let `Es` be a finite set of circle points with complex weights `w β`, `‖w β‖ ≤ W`, and let `p ≥ 1`.  Then the multiplier with the weighted arc symbol `arcSymbolWLp (fun β => β) w Es φ` = `Σ_{β ∈ Es} w β · φ(· - β)` is bounded on `ℓᵖ(ℤ)` with constant `W · #Es · K`.  This is the weighted companion of `Work.BourgainPlan.KPWW.opArc_lp_bound_of_coeff` (which is the case `w ≡ 1`, `Es ⊆ 𝕋`); the proof is the same: the `m`-th Fourier coefficient of the weighted symbol is `(Σ_{β ∈ Es} w β · conj e_m(β)) · c m` (finite sums exchange with the integral, Haar translation invariance `fourierCoeff_arcTranslate`), so the convolution kernel has `ℓ¹`-mass `≤ W · #Es · K`, and Young's inequality for the counting measure (`Work.IonescuWainger.young_count_lp`), together with the convolution realisation of the multiplier (`opMul_eq_tsum_kernel`), gives the `ℓᵖ → ℓᵖ` bound for every `p ≥ 1`.  (Model: `Maximal/mstModelFn_kernel_l1_of_coeff` does the weighted Fourier-coefficient computation, and `KPWW/opArc_lp_bound_of_coeff` the Young step.) -/
theorem arcSymbolW_lp_bound_of_coeff {p : ℝ} (hp : 1 ≤ p)
    {φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ}
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {c : ℤ → ℂ}
    (hcsum : Summable fun n : ℤ => ‖c n‖)
    (hc : ∀ n : ℤ, ∫ θ, φ θ * star (fourier n θ) ∂(AddCircle.haarAddCircle (T := 1)) = c n)
    {W K : ℝ} (hW : 0 ≤ W)
    (hcK : (∑' n : ℤ, ‖c n‖) ≤ K)
    (w : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (Es : Finset Work.BourgainPlan.IonescuWainger.Circle)
    (hw : ∀ β ∈ Es, ‖w β‖ ≤ W)
    (g : ℤ →₀ ℂ) :
    MeasureTheory.eLpNorm (fun n : ℤ =>
        Work.BourgainPlan.IonescuWainger.opMul
          (Work.BourgainPlan.Maximal.arcSymbolWLp
            (fun β : Work.BourgainPlan.IonescuWainger.Circle => β) w Es φ hφ)
          (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) n)
        (ENNReal.ofReal p) (MeasureTheory.Measure.count)
      ≤ ENNReal.ofReal (W * (Es.card : ℝ) * K)
        * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  set Φ : Lp ℂ ⊤ haar :=
    Work.BourgainPlan.Maximal.arcSymbolWLp (fun β : Circle => β) w Es φ hφ with hΦdef
  -- ## The Fourier coefficients of the weighted symbol
  have hker : ∀ m : ℤ, ∫ ξ : Circle, (Φ : Circle → ℂ) ξ * star (fourier m ξ) ∂haar
      = (∑ β ∈ Es, w β * star (fourier m β)) * c m := by
    intro m
    have hcoef : ∫ ξ : Circle,
          (Work.BourgainPlan.Maximal.arcSymbolWLp (fun β : Circle => β) w Es φ hφ :
            Circle → ℂ) ξ * star (fourier m ξ) ∂haar
        = ∫ ξ : Circle, Work.BourgainPlan.Maximal.arcSymbolW (fun β : Circle => β) w Es φ ξ
            * star (fourier m ξ) ∂haar := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [Work.BourgainPlan.Maximal.arcSymbolWLp_coeFn
        (fun β : Circle => β) w Es φ hφ] with ξ hξ
      rw [hξ]
    rw [hΦdef, hcoef]
    exact integral_arcSymbolW_mul_fourier φ hφ hc w Es m
  -- ## The `ℓ¹` bound on the convolution kernel
  set A : ℤ → ENNReal :=
    fun m => ENNReal.ofReal ‖(∑ β ∈ Es, w β * star (fourier m β)) * c m‖ with hAdef
  set G : ℤ → ENNReal := fun k => ENNReal.ofReal ‖(⇑g : ℤ → ℂ) k‖ with hGdef
  have hcard : (0 : ℝ) ≤ (Es.card : ℝ) := Nat.cast_nonneg _
  have hWc : (0 : ℝ) ≤ W * (Es.card : ℝ) := mul_nonneg hW hcard
  have hbnd : ∀ m : ℤ, ‖∑ β ∈ Es, w β * star (fourier m β)‖ ≤ W * (Es.card : ℝ) := by
    intro m
    calc ‖∑ β ∈ Es, w β * star (fourier m β)‖
        ≤ ∑ β ∈ Es, ‖w β * star (fourier m β)‖ := norm_sum_le _ _
      _ = ∑ β ∈ Es, ‖w β‖ := by
          refine Finset.sum_congr rfl (fun β _ => ?_)
          rw [norm_mul, norm_star, Work.BourgainPlan.IonescuWainger.norm_fourier_apply' m β,
            mul_one]
      _ ≤ ∑ _β ∈ Es, W := Finset.sum_le_sum (fun β hβ => hw β hβ)
      _ = W * (Es.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hnorm_le : ∀ m : ℤ,
      A m ≤ ENNReal.ofReal (W * (Es.card : ℝ)) * ENNReal.ofReal ‖c m‖ := by
    intro m
    have h1 : ‖(∑ β ∈ Es, w β * star (fourier m β)) * c m‖
        ≤ (W * (Es.card : ℝ)) * ‖c m‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbnd m) (norm_nonneg _)
    calc A m = ENNReal.ofReal ‖(∑ β ∈ Es, w β * star (fourier m β)) * c m‖ := by
          simp only [hAdef]
      _ ≤ ENNReal.ofReal ((W * (Es.card : ℝ)) * ‖c m‖) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (W * (Es.card : ℝ)) * ENNReal.ofReal ‖c m‖ := ENNReal.ofReal_mul hWc
  have hsumA : (∑' m : ℤ, A m) ≤ ENNReal.ofReal (W * (Es.card : ℝ) * K) := by
    calc ∑' m : ℤ, A m
        ≤ ∑' m : ℤ, (ENNReal.ofReal (W * (Es.card : ℝ)) * ENNReal.ofReal ‖c m‖) :=
          ENNReal.tsum_le_tsum hnorm_le
      _ = ENNReal.ofReal (W * (Es.card : ℝ)) * ∑' m : ℤ, ENNReal.ofReal ‖c m‖ :=
          ENNReal.tsum_mul_left
      _ = ENNReal.ofReal (W * (Es.card : ℝ)) * ENNReal.ofReal (∑' m : ℤ, ‖c m‖) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun m : ℤ => ‖c m‖)
            (fun m => norm_nonneg _) hcsum]
      _ ≤ ENNReal.ofReal (W * (Es.card : ℝ)) * ENNReal.ofReal K :=
          mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hcK)
      _ = ENNReal.ofReal (W * (Es.card : ℝ) * K) := (ENNReal.ofReal_mul hWc).symm
  -- ## The pointwise domination by the convolution with `A`
  have hpoint : ∀ n : ℤ, ENNReal.ofReal
        (‖Work.BourgainPlan.IonescuWainger.opMul Φ (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) n‖ ^ p)
      ≤ (∑' k : ℤ, A k * G (n - k)) ^ p := by
    intro n
    have h1 : ENNReal.ofReal ‖Work.BourgainPlan.IonescuWainger.opMul Φ (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) n‖
        ≤ ∑' k : ℤ, G k * A (n - k) := by
      rw [Work.BourgainPlan.IonescuWainger.opMul_eq_tsum_kernel Φ (⇑g)
        (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) hker n]
      calc ENNReal.ofReal ‖∑' k : ℤ, (⇑g) k *
              ((∑ β ∈ Es, w β * star (fourier (n - k) β)) * c (n - k))‖
          ≤ ∑' k : ℤ, ENNReal.ofReal ‖(⇑g) k *
              ((∑ β ∈ Es, w β * star (fourier (n - k) β)) * c (n - k))‖ :=
            ofReal_norm_tsum_le' _
        _ = ∑' k : ℤ, G k * A (n - k) := by
            refine tsum_congr fun k => ?_
            simp only [hGdef, hAdef]
            rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
    have hswap : (∑' k : ℤ, G k * A (n - k)) = ∑' k : ℤ, A k * G (n - k) := by
      rw [← Equiv.tsum_eq (Equiv.subLeft n) (fun j : ℤ => A j * G (n - j))]
      refine tsum_congr fun k => ?_
      rw [Equiv.subLeft_apply]
      have hnk : n - (n - k) = k := by ring
      rw [hnk, mul_comm]
    calc ENNReal.ofReal (‖Work.BourgainPlan.IonescuWainger.opMul Φ (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) n‖ ^ p)
        = (ENNReal.ofReal ‖Work.BourgainPlan.IonescuWainger.opMul Φ (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) n‖) ^ p :=
          (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le).symm
      _ ≤ (∑' k : ℤ, G k * A (n - k)) ^ p := ENNReal.rpow_le_rpow h1 hp0.le
      _ = (∑' k : ℤ, A k * G (n - k)) ^ p := by rw [hswap]
  -- ## Assembling: Young's inequality and the `eLpNorm` bookkeeping
  have hS1 : MeasureTheory.eLpNorm (fun n : ℤ =>
        Work.BourgainPlan.IonescuWainger.opMul Φ (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) n)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      = (∑' n : ℤ, ENNReal.ofReal (‖Work.BourgainPlan.IonescuWainger.opMul Φ (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) n‖ ^ p)) ^ (1 / p) :=
    eLpNorm_count_eq_tsum_ofReal _ hp0
  have hS2 : (∑' n : ℤ, ENNReal.ofReal (‖(⇑g : ℤ → ℂ) n‖ ^ p)) = ∑' n : ℤ, G n ^ p := by
    refine tsum_congr fun n => ?_
    simp only [hGdef]
    exact (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le).symm
  have hstep : (∑' n : ℤ, ENNReal.ofReal (‖Work.BourgainPlan.IonescuWainger.opMul Φ (⇑g)
        (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) n‖ ^ p))
      ≤ (∑' k : ℤ, A k) ^ p * ∑' n : ℤ, ENNReal.ofReal (‖(⇑g : ℤ → ℂ) n‖ ^ p) :=
    calc ∑' n : ℤ, ENNReal.ofReal (‖Work.BourgainPlan.IonescuWainger.opMul Φ (⇑g)
          (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) n‖ ^ p)
        ≤ ∑' n : ℤ, (∑' k : ℤ, A k * G (n - k)) ^ p := ENNReal.tsum_le_tsum hpoint
      _ ≤ (∑' k : ℤ, A k) ^ p * ∑' n : ℤ, G n ^ p :=
          Work.IonescuWainger.young_count_lp hp A G
      _ = (∑' k : ℤ, A k) ^ p * ∑' n : ℤ, ENNReal.ofReal (‖(⇑g : ℤ → ℂ) n‖ ^ p) := by
          rw [← hS2]
  rw [hS1, eLpNorm_count_eq_tsum_ofReal (⇑g) hp0]
  calc (∑' n : ℤ, ENNReal.ofReal (‖Work.BourgainPlan.IonescuWainger.opMul Φ (⇑g)
        (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) n‖ ^ p)) ^ (1 / p)
      ≤ ((∑' k : ℤ, A k) ^ p
          * ∑' n : ℤ, ENNReal.ofReal (‖(⇑g : ℤ → ℂ) n‖ ^ p)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hstep (one_div_pos.mpr hp0).le
    _ = (∑' k : ℤ, A k)
          * (∑' n : ℤ, ENNReal.ofReal (‖(⇑g : ℤ → ℂ) n‖ ^ p)) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hp0).le, ← ENNReal.rpow_mul,
          show p * (1 / p) = 1 by field_simp, ENNReal.rpow_one]
    _ ≤ ENNReal.ofReal (W * (Es.card : ℝ) * K)
          * (∑' n : ℤ, ENNReal.ofReal (‖(⇑g : ℤ → ℂ) n‖ ^ p)) ^ (1 / p) :=
        mul_le_mul' hsumA le_rfl

end Work.Maximal
