import Mathlib
import Submission.Work.BourgainPlan.Maximal.kmsz_major_defs
import Submission.Work.Analysis.Fourier.bandlimited_weighted_reproduction
import Submission.Work.BourgainPlan.IonescuWainger.exists_pairing_attaining_sqrt_sum_sq

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped BigOperators ENNReal FourierTransform

set_option maxHeartbeats 1600000

noncomputable section

/-- Linearity of the inverse Fourier transform in a finite linear combination of *differences*
with constant coefficients:
`𝓕⁻ (∑ i ∈ s, c i * (A i - B i)) x = ∑ i ∈ s, c i * (𝓕⁻ (A i) x - 𝓕⁻ (B i) x)` when the `A i`, `B i`
are integrable.  Both sides are unfolded with `Real.fourierInv_eq'`; the finite sum goes through the
integral by `integral_finsetSum` (the modulated pieces are integrable because the modulating factor
has modulus one), `integral_sub` splits the difference and `integral_const_mul` pulls the constant
out. -/
lemma fourierInv_sum_const_mul_sub {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (A Bd : ι → ℝ → ℂ) (hA : ∀ i ∈ s, MeasureTheory.Integrable (A i))
    (hB : ∀ i ∈ s, MeasureTheory.Integrable (Bd i)) (x : ℝ) :
    FourierTransformInv.fourierInv (fun β => ∑ i ∈ s, c i * (A i β - Bd i β)) x
      = ∑ i ∈ s, c i * (FourierTransformInv.fourierInv (A i) x
          - FourierTransformInv.fourierInv (Bd i) x) := by
  simp only [Real.fourierInv_eq']
  have hintA : ∀ i ∈ s, MeasureTheory.Integrable
      (fun v : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • A i v) := by
    intro i hi
    refine MeasureTheory.Integrable.mono' (hA i hi).norm ?_ ?_
    · exact ((by fun_prop : Continuous (fun v : ℝ =>
        Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I))).aestronglyMeasurable).smul
        (hA i hi).aestronglyMeasurable
    · filter_upwards with v
      rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hintB : ∀ i ∈ s, MeasureTheory.Integrable
      (fun v : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • Bd i v) := by
    intro i hi
    refine MeasureTheory.Integrable.mono' (hB i hi).norm ?_ ?_
    · exact ((by fun_prop : Continuous (fun v : ℝ =>
        Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I))).aestronglyMeasurable).smul
        (hB i hi).aestronglyMeasurable
    · filter_upwards with v
      rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [show (fun v : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) •
        (∑ i ∈ s, c i * (A i v - Bd i v)))
      = fun v : ℝ => ∑ i ∈ s, c i *
          (Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • A i v
            - Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • Bd i v) from by
    funext v
    rw [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [smul_eq_mul, smul_eq_mul]
    ring]
  have hsum_int : (∫ v : ℝ, ∑ i ∈ s, c i *
        (Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • A i v
          - Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • Bd i v))
      = ∑ i ∈ s, ∫ v : ℝ, c i *
        (Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • A i v
          - Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • Bd i v) :=
    MeasureTheory.integral_finsetSum (s := s)
      (f := fun i : ι => fun v : ℝ => c i *
        (Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • A i v
          - Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • Bd i v))
      (fun i hi => (hintA i hi).sub (hintB i hi) |>.const_mul (c i))
  rw [hsum_int]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [show (∫ v : ℝ, c i * (Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • A i v
        - Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • Bd i v))
      = ∫ v : ℝ, (c i * (Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • A i v)
          - c i * (Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) • Bd i v)) from by
    apply integral_congr_ae
    filter_upwards with v
    ring]
  rw [MeasureTheory.integral_sub ((hintA i hi).const_mul (c i)) ((hintB i hi).const_mul (c i)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  ring

/-- The `ℓ²`-length of the increments along a chain is at most the `ℓ¹`-length: for nonnegative
reals `(Σ x_j²)^{1/2} ≤ Σ x_j`.  This is used only to exhibit an integrable majorant. -/
lemma chainLp_two_le_sum_norm {E : Type*} [SeminormedAddCommGroup E]
    (J : ℕ) (a : ℕ → E) (t : ℕ → ℕ) :
    Work.BourgainPlan.Maximal.chainLp 2 J a t
      ≤ ∑ j ∈ Finset.range J, ‖a (t (j + 1)) - a (t j)‖ := by
  rw [Work.BourgainPlan.Maximal.chainLp]
  have h1 : (∑ j ∈ Finset.range J, ‖a (t (j + 1)) - a (t j)‖ ^ (2 : ℝ))
      = ∑ j ∈ Finset.range J, ‖a (t (j + 1)) - a (t j)‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Real.rpow_two]
  rw [h1, ← Real.sqrt_eq_rpow]
  rw [Real.sqrt_le_iff]
  exact ⟨Finset.sum_nonneg (fun j _ => norm_nonneg _),
    Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)⟩

-- Route: `norm_fourierInv_le_weighted` (`Submission/Work/Analysis/Fourier/bandlimited_weighted_reproduction.lean`)
-- gives, for every integrable amplitude `W` with `𝓕 w ≡ 1` on its support,
-- `‖𝓕⁻W x‖ ≤ B * ∫ y, ‖𝓕⁻W y‖ / (1 + (x-y)^2) dy`.  For an admissible chain `(J, t)` and the
-- extremal `c : Fin J → ℂ` with `∑ ‖c j‖ ^ 2 ≤ 1`, apply it to the integrable amplitude
-- `W_c = ∑ j, c j * (W (t (j+1)) - W (t j))` (whose support satisfies the hypothesis `hprod` because
-- a nonvanishing sum has a nonvanishing term), and bound `‖𝓕⁻(W_c) y‖` by Cauchy–Schwarz against
-- `(∑ j, ‖𝓕⁻(W (t (j+1))) y - 𝓕⁻(W (t j)) y‖ ^ 2) ^ (1/2)`, which is `chainLp 2 J (𝓕⁻ ∘ W) t ≤`
-- the variation of the statement.  `FourierTransformInv.fourierInv (W₁ - W₂) x = 𝓕⁻W₁ x - 𝓕⁻W₂ x`
-- and `𝓕⁻ (∑ j, c j * U j) x = ∑ j, c j * 𝓕⁻ (U j) x` are the definitional unfolding of
-- `Real.fourierInv_eq'` with `MeasureTheory.integral_sub` / `MeasureTheory.integral_finset_sum` and
-- `MeasureTheory.integral_const_mul`.
theorem varRho_fourierInv_pointwise (W : ℕ → ℝ → ℂ) (hW : ∀ n, MeasureTheory.Integrable (W n))
    (w : ℝ → ℂ) (B : ℝ) (hB : 0 < B) (hw : MeasureTheory.Integrable w)
    (hwdec : ∀ z : ℝ, ‖w z‖ ≤ B / (1 + z ^ 2))
    (hprod : ∀ (n : ℕ) (β : ℝ), W n β ≠ 0 → FourierTransform.fourier w β = 1)
    (κ : ℕ) (x : ℝ) :
    Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n => FourierTransformInv.fourierInv (W n) x)
      ≤ ENNReal.ofReal B * ∫⁻ y : ℝ, Work.BourgainPlan.Maximal.varRhoFrom 2 κ
          (fun n => FourierTransformInv.fourierInv (W n) y) * ENNReal.ofReal ((1 + (x - y) ^ 2)⁻¹) := by
  unfold Work.BourgainPlan.Maximal.varRhoFrom
  refine iSup_le fun hi => ?_
  conv_lhs => rw [Work.BourgainPlan.Maximal.varRho]
  refine iSup_le fun J => iSup_le fun t => iSup_le fun ht => iSup_le fun hr => ?_
  -- the extremal coefficient vector and the extremal amplitude
  obtain ⟨c, hc_sum, hc_norm⟩ :=
    (exists_pairing_attaining_sqrt_sum_sq (fun j : Fin J =>
      FourierTransformInv.fourierInv (W (t (↑j + 1))) x
        - FourierTransformInv.fourierInv (W (t ↑j)) x)).2
  set Wc : ℝ → ℂ := fun β => ∑ j : Fin J, c j * (W (t (↑j + 1)) β - W (t ↑j) β) with hWc
  -- linearity of `𝓕⁻` on the extremal amplitude
  have hlin : ∀ z : ℝ, FourierTransformInv.fourierInv Wc z
      = ∑ j : Fin J, c j * (FourierTransformInv.fourierInv (W (t (↑j + 1))) z
          - FourierTransformInv.fourierInv (W (t ↑j)) z) := by
    intro z
    rw [hWc]
    exact fourierInv_sum_const_mul_sub Finset.univ c (fun j : Fin J => W (t (↑j + 1)))
      (fun j : Fin J => W (t ↑j)) (fun j _ => hW (t (↑j + 1))) (fun j _ => hW (t ↑j)) z
  -- `Wc` is integrable
  have hWc_int : MeasureTheory.Integrable Wc := by
    rw [hWc]
    refine MeasureTheory.integrable_finsetSum Finset.univ (fun j _ => ?_)
    exact ((hW (t (↑j + 1))).sub (hW (t ↑j))).const_mul (c j)
  -- the support condition transfers from `Wc` to its summands
  have hWc_prod : ∀ β : ℝ, Wc β ≠ 0 → FourierTransform.fourier w β = 1 := by
    intro β hβ
    have hex : ∃ j : Fin J, c j * (W (t (↑j + 1)) β - W (t ↑j) β) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      refine hβ ?_
      rw [hWc]
      exact Finset.sum_eq_zero (fun j _ => hcon j)
    obtain ⟨j, hj⟩ := hex
    have hdiff : W (t (↑j + 1)) β - W (t ↑j) β ≠ 0 := fun h => hj (by rw [h, mul_zero])
    rcases eq_or_ne (W (t (↑j + 1)) β) 0 with hA | hA
    · exact hprod (t ↑j) β (fun h => hdiff (by rw [hA, h, sub_zero]))
    · exact hprod (t (↑j + 1)) β hA
  -- the chain `ℓ²`-length at `x` is `‖𝓕⁻ Wc x‖`
  have hchain : Work.BourgainPlan.Maximal.chainLp 2 J
        (fun n => FourierTransformInv.fourierInv (W n) x) t
      = ‖∑ j : Fin J, c j * (FourierTransformInv.fourierInv (W (t (↑j + 1))) x
          - FourierTransformInv.fourierInv (W (t ↑j)) x)‖ := by
    rw [hc_norm, Work.BourgainPlan.Maximal.chainLp]
    rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      ‖FourierTransformInv.fourierInv (W (t (j + 1))) x
        - FourierTransformInv.fourierInv (W (t j)) x‖ ^ (2 : ℝ)) J]
    refine congrArg (fun r : ℝ => r ^ (1 / 2 : ℝ)) ?_
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Real.rpow_two]
  -- pointwise Cauchy–Schwarz: `‖𝓕⁻ Wc y‖ ≤ chainLp` at every `y`
  have hbound_at : ∀ y : ℝ, ‖FourierTransformInv.fourierInv Wc y‖
      ≤ Work.BourgainPlan.Maximal.chainLp 2 J
          (fun n => FourierTransformInv.fourierInv (W n) y) t := by
    intro y
    rw [hlin y]
    refine le_trans ((exists_pairing_attaining_sqrt_sum_sq (fun j : Fin J =>
      FourierTransformInv.fourierInv (W (t (↑j + 1))) y
        - FourierTransformInv.fourierInv (W (t ↑j)) y)).1 c hc_sum) ?_
    rw [Work.BourgainPlan.Maximal.chainLp]
    refine Real.rpow_le_rpow (Finset.sum_nonneg (fun j _ => by positivity)) ?_ (by norm_num)
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      ‖FourierTransformInv.fourierInv (W (t (j + 1))) y
        - FourierTransformInv.fourierInv (W (t j)) y‖ ^ 2) J]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [Real.rpow_two]
  -- a uniform bound on `chainLp` in the space variable
  set C₀ : ℕ → ℝ := fun n => ∫ β : ℝ, ‖W n β‖ with hC₀
  have hbddW : ∀ (n : ℕ) (y : ℝ), ‖FourierTransformInv.fourierInv (W n) y‖ ≤ C₀ n := by
    intro n y
    rw [hC₀]
    rw [Real.fourierInv_eq']
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
    apply integral_congr_ae
    filter_upwards with β
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hCn : ∀ y : ℝ, Work.BourgainPlan.Maximal.chainLp 2 J
      (fun n => FourierTransformInv.fourierInv (W n) y) t
      ≤ ∑ j : Fin J, (C₀ (t (↑j + 1)) + C₀ (t ↑j)) := by
    intro y
    calc Work.BourgainPlan.Maximal.chainLp 2 J
          (fun n => FourierTransformInv.fourierInv (W n) y) t
        ≤ ∑ j ∈ Finset.range J, ‖FourierTransformInv.fourierInv (W (t (j + 1))) y
            - FourierTransformInv.fourierInv (W (t j)) y‖ :=
          chainLp_two_le_sum_norm J _ t
      _ ≤ ∑ j ∈ Finset.range J, (C₀ (t (j + 1)) + C₀ (t j)) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          exact (norm_sub_le _ _).trans (add_le_add (hbddW (t (j + 1)) y) (hbddW (t j) y))
      _ = ∑ j : Fin J, (C₀ (t (↑j + 1)) + C₀ (t ↑j)) := by
          rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => C₀ (t (j + 1)) + C₀ (t j)) J]
  -- continuity of the chain function
  have hcontF : ∀ n : ℕ, Continuous (fun y : ℝ => FourierTransformInv.fourierInv (W n) y) := by
    intro n
    have h1 : (⇑(Real.Lp.fourierTransformInv
        (MemLp.toLp (W n) (memLp_one_iff_integrable.mpr (hW n)))) : ℝ → ℂ)
        = FourierTransformInv.fourierInv (W n) := Real.Lp.fourierTransformInv_toLp _
    rw [← h1]
    exact (Real.Lp.fourierTransformInv _).continuous
  have hchain_cont : Continuous (fun y : ℝ => Work.BourgainPlan.Maximal.chainLp 2 J
      (fun n => FourierTransformInv.fourierInv (W n) y) t) := by
    rw [show (fun y : ℝ => Work.BourgainPlan.Maximal.chainLp 2 J
          (fun n => FourierTransformInv.fourierInv (W n) y) t)
        = fun y : ℝ => (∑ j ∈ Finset.range J,
            ‖FourierTransformInv.fourierInv (W (t (j + 1))) y
              - FourierTransformInv.fourierInv (W (t j)) y‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) from rfl]
    exact (Real.continuous_rpow_const (q := (1 / 2 : ℝ)) (by norm_num)).comp
      (continuous_finsetSum _ (fun j _ =>
        (Real.continuous_rpow_const (q := (2 : ℝ)) (by norm_num)).comp
          (((hcontF (t (j + 1))).sub (hcontF (t j))).norm)))
  -- the weighted majorant is integrable
  have hwt_int : MeasureTheory.Integrable (fun y : ℝ => (1 + (x - y) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_sub_left x
  have hGint : MeasureTheory.Integrable (fun y : ℝ => Work.BourgainPlan.Maximal.chainLp 2 J
      (fun n => FourierTransformInv.fourierInv (W n) y) t * (1 + (x - y) ^ 2)⁻¹) := by
    refine MeasureTheory.Integrable.bdd_mul
      (f := fun y : ℝ => Work.BourgainPlan.Maximal.chainLp 2 J
        (fun n => FourierTransformInv.fourierInv (W n) y) t)
      (g := fun y : ℝ => (1 + (x - y) ^ 2)⁻¹)
      (c := ∑ j : Fin J, (C₀ (t (↑j + 1)) + C₀ (t ↑j)))
      hwt_int hchain_cont.aestronglyMeasurable (Filter.Eventually.of_forall (fun y => ?_))
    rw [Real.norm_of_nonneg (Work.BourgainPlan.Maximal.chainLp_nonneg 2 J _ t)]
    exact hCn y
  -- the real-valued pointwise bound
  have hreal : Work.BourgainPlan.Maximal.chainLp 2 J
        (fun n => FourierTransformInv.fourierInv (W n) x) t
      ≤ B * ∫ y : ℝ, Work.BourgainPlan.Maximal.chainLp 2 J
          (fun n => FourierTransformInv.fourierInv (W n) y) t * (1 + (x - y) ^ 2)⁻¹ := by
    rw [hchain, ← hlin x]
    refine (Commons.Analysis.Fourier.norm_fourierInv_le_weighted hWc_int hw hB hwdec hWc_prod x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hB.le
    rw [show (fun y : ℝ => ‖FourierTransformInv.fourierInv Wc y‖ / (1 + (x - y) ^ 2))
        = fun y : ℝ => ‖FourierTransformInv.fourierInv Wc y‖ * (1 + (x - y) ^ 2)⁻¹ from by
      funext y; rw [div_eq_mul_inv]]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun y => by positivity)) hGint
      (Filter.Eventually.of_forall (fun y => ?_))
    exact mul_le_mul_of_nonneg_right (hbound_at y) (by positivity)
  -- the `ℝ≥0∞` comparison
  have hle_var : ∀ y : ℝ, ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp 2 J
        (fun n => FourierTransformInv.fourierInv (W n) y) t)
      ≤ ⨆ hi' : ℕ, Work.BourgainPlan.Maximal.varRho 2 κ hi'
          (fun n => FourierTransformInv.fourierInv (W n) y) := by
    intro y
    refine le_trans ?_ (le_iSup (fun hi' : ℕ => Work.BourgainPlan.Maximal.varRho 2 κ hi'
      (fun n => FourierTransformInv.fourierInv (W n) y)) hi)
    exact le_iSup_of_le J (le_iSup_of_le t (le_iSup_of_le ht (le_iSup_of_le hr le_rfl)))
  have hnonneg : 0 ≤ᵐ[volume] (fun y : ℝ => Work.BourgainPlan.Maximal.chainLp 2 J
      (fun n => FourierTransformInv.fourierInv (W n) y) t * (1 + (x - y) ^ 2)⁻¹) :=
    Filter.Eventually.of_forall
      (fun y => mul_nonneg (Work.BourgainPlan.Maximal.chainLp_nonneg 2 J _ t) (by positivity))
  calc ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp 2 J
        (fun n => FourierTransformInv.fourierInv (W n) x) t)
      ≤ ENNReal.ofReal (B * ∫ y : ℝ, Work.BourgainPlan.Maximal.chainLp 2 J
          (fun n => FourierTransformInv.fourierInv (W n) y) t * (1 + (x - y) ^ 2)⁻¹) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal B * ENNReal.ofReal (∫ y : ℝ, Work.BourgainPlan.Maximal.chainLp 2 J
          (fun n => FourierTransformInv.fourierInv (W n) y) t * (1 + (x - y) ^ 2)⁻¹) :=
        ENNReal.ofReal_mul hB.le
    _ = ENNReal.ofReal B * ∫⁻ y : ℝ, ENNReal.ofReal
          (Work.BourgainPlan.Maximal.chainLp 2 J
            (fun n => FourierTransformInv.fourierInv (W n) y) t * (1 + (x - y) ^ 2)⁻¹) := by
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hGint hnonneg]
    _ = ENNReal.ofReal B * ∫⁻ y : ℝ, ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp 2 J
            (fun n => FourierTransformInv.fourierInv (W n) y) t)
          * ENNReal.ofReal ((1 + (x - y) ^ 2)⁻¹) := by
        congr 1
        refine lintegral_congr (fun y => ?_)
        rw [ENNReal.ofReal_mul (Work.BourgainPlan.Maximal.chainLp_nonneg 2 J _ t)]
    _ ≤ ENNReal.ofReal B * ∫⁻ y : ℝ, (⨆ hi' : ℕ, Work.BourgainPlan.Maximal.varRho 2 κ hi'
            (fun n => FourierTransformInv.fourierInv (W n) y))
          * ENNReal.ofReal ((1 + (x - y) ^ 2)⁻¹) := by
        apply mul_le_mul_right
        refine lintegral_mono (fun y => ?_)
        exact mul_le_mul_left (hle_var y) _

end

end Work.BourgainPlan.IonescuWainger
