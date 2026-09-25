import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.norm_opMul_le_of_kernel
import Submission.Work.IonescuWainger.young_count_lp

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped ENNReal BigOperators


/-- `eLpNorm` against the counting measure on `ℤ` as a (possibly infinite) `ℓ^q` sum. -/
private lemma eLpNorm_count_eq_tsum_ofReal' (f : ℤ → ℂ) {q : ℝ} (hq : 0 < q) :
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
private lemma ofReal_norm_tsum_le'' (x : ℤ → ℂ) :
    ENNReal.ofReal ‖∑' i : ℤ, x i‖ ≤ ∑' i : ℤ, ENNReal.ofReal ‖x i‖ := by
  simpa using enorm_tsum_le_tsum_enorm (f := x)

/-- **The `ℓᵖ` bound for an `L^∞(𝕋)`-multiplier with summable coefficient kernel.**  If the Fourier
coefficients `c n = ∫ θ, Φ θ * star (fourier n θ)` of the symbol class `Φ ∈ L^∞(𝕋)` are summable with
`Σ_m ‖c m‖ ≤ K`, then the multiplier `opMul Φ` is bounded on `ℓᵖ(ℤ)` with constant `K`, for every
`p ≥ 1` (in particular for all `r > 1`); `f` is only assumed square-summable, since `opMul` is
defined through the `ℓ²(ℤ) ≅ L²(𝕋)` dictionary.

Route: the convolution identity `opMul_eq_tsum_kernel` exhibits
`opMul Φ f hf n = Σ'_k f k * c (n - k)`; the discrete Young inequality `Work.IonescuWainger.young_count_lp`
(with `a := fun k => ENNReal.ofReal ‖c k‖` and `g := fun k => ENNReal.ofReal ‖f k‖`) gives
`Σ_n (Σ'_k a k * g (n-k))^p ≤ (Σ_k a k)^p * Σ_n (g n)^p`; and `eLpNorm` against `Measure.count` is the
`p`-th root of the `ℝ≥0∞`-sum of the `p`-th powers of the norms.  This is the `opMul` analogue of
`Work.BourgainPlan.KPWW.opArc_lp_bound_of_coeff` (same proof, no arc set `E`). -/
theorem mst_err1_opmul_coeff {p : ℝ} (hp : 1 ≤ p)
    {Φ : MeasureTheory.Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))} {c : ℤ → ℂ}
    (hcsum : Summable fun n : ℤ => ‖c n‖)
    (hc : ∀ n : ℤ, ∫ θ, (Φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ) θ * star (fourier n θ)
      ∂(AddCircle.haarAddCircle (T := 1)) = c n)
    {K : ℝ} (hcK : (∑' n : ℤ, ‖c n‖) ≤ K) (f : ℤ → ℂ) (hf : Memℓp f 2) :
    MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opMul Φ f hf)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal K * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  set w : ℤ → ENNReal := fun m => ENNReal.ofReal ‖c m‖ with hwdef
  set g : ℤ → ENNReal := fun k => ENNReal.ofReal ‖f k‖ with hgdef
  -- ## The `ℓ¹` bound on the convolution kernel
  have hsumw : (∑' m : ℤ, w m) ≤ ENNReal.ofReal K := by
    have h1 : (∑' m : ℤ, w m) = ENNReal.ofReal (∑' m : ℤ, ‖c m‖) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun m : ℤ => ‖c m‖)
        (fun m => norm_nonneg _) hcsum]
    rw [h1]
    exact ENNReal.ofReal_le_ofReal hcK
  -- ## The pointwise domination by the convolution with `w`
  have hpoint : ∀ n : ℤ, ENNReal.ofReal
        (‖Work.BourgainPlan.IonescuWainger.opMul Φ f hf n‖ ^ p)
      ≤ (∑' k : ℤ, w k * g (n - k)) ^ p := by
    intro n
    have h1 : ENNReal.ofReal ‖Work.BourgainPlan.IonescuWainger.opMul Φ f hf n‖
        ≤ ∑' k : ℤ, g k * w (n - k) := by
      rw [Work.BourgainPlan.IonescuWainger.opMul_eq_tsum_kernel Φ f hf hc n]
      calc ENNReal.ofReal ‖∑' k : ℤ, f k * c (n - k)‖
          ≤ ∑' k : ℤ, ENNReal.ofReal ‖f k * c (n - k)‖ := ofReal_norm_tsum_le'' _
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
    calc ENNReal.ofReal (‖Work.BourgainPlan.IonescuWainger.opMul Φ f hf n‖ ^ p)
        = (ENNReal.ofReal ‖Work.BourgainPlan.IonescuWainger.opMul Φ f hf n‖) ^ p :=
          (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le).symm
      _ ≤ (∑' k : ℤ, g k * w (n - k)) ^ p := ENNReal.rpow_le_rpow h1 hp0.le
      _ = (∑' k : ℤ, w k * g (n - k)) ^ p := by rw [hswap]
  -- ## Assembling: Young's inequality and the `eLpNorm` bookkeeping
  have hS1 : MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opMul Φ f hf)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      = (∑' n : ℤ, ENNReal.ofReal
          (‖Work.BourgainPlan.IonescuWainger.opMul Φ f hf n‖ ^ p)) ^ (1 / p) :=
    eLpNorm_count_eq_tsum_ofReal' _ hp0
  have hS2 : (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p)) = ∑' n : ℤ, g n ^ p := by
    refine tsum_congr fun n => ?_
    simp only [hgdef]
    exact (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le).symm
  have hstep : (∑' n : ℤ, ENNReal.ofReal
        (‖Work.BourgainPlan.IonescuWainger.opMul Φ f hf n‖ ^ p))
      ≤ (∑' k : ℤ, w k) ^ p * ∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p) :=
    calc ∑' n : ℤ, ENNReal.ofReal
          (‖Work.BourgainPlan.IonescuWainger.opMul Φ f hf n‖ ^ p)
        ≤ ∑' n : ℤ, (∑' k : ℤ, w k * g (n - k)) ^ p := ENNReal.tsum_le_tsum hpoint
      _ ≤ (∑' k : ℤ, w k) ^ p * ∑' n : ℤ, g n ^ p :=
          Work.IonescuWainger.young_count_lp hp w g
      _ = (∑' k : ℤ, w k) ^ p * ∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p) := by rw [← hS2]
  rw [hS1, eLpNorm_count_eq_tsum_ofReal' f hp0]
  calc (∑' n : ℤ, ENNReal.ofReal
        (‖Work.BourgainPlan.IonescuWainger.opMul Φ f hf n‖ ^ p)) ^ (1 / p)
      ≤ ((∑' k : ℤ, w k) ^ p * ∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hstep (one_div_pos.mpr hp0).le
    _ = (∑' k : ℤ, w k) * (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p)) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hp0).le, ← ENNReal.rpow_mul,
          show p * (1 / p) = 1 by field_simp, ENNReal.rpow_one]
    _ ≤ ENNReal.ofReal K * (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p)) ^ (1 / p) :=
        mul_le_mul' hsumw le_rfl

end Work.BourgainPlan.Maximal
