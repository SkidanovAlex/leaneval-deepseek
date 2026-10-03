import Mathlib
import Submission.Work.KMTAreas.A7.lacDilDevSqSumViaAlt
import Submission.Port.Aesm

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-!
# The lacunary variational estimate for discrete low-pass (bump) convolution operators

The target `Work.KMTAreas.A7.lacunaryBumpDilationVar` is proved here from the two halves of the
pointwise decomposition `bumpOp = lacConst K • triSmooth + devOp` (`lacDilDefs.bump_decomp`):

* `lacDilTriVar` — the martingale/Lépingle half: the variation of the triangular (Fejér)
  smoothing family `n ↦ triSmooth σ n f` at the lacunary dyadic levels `lacLev σ n`;
* `lacDilDevSqSumViaAlt` — the almost-orthogonality half: the values square function
  `x ↦ (∑'_n ‖devOp K σ n f x‖²)^{1/2}` of the deviation is `ℓᵖ`-bounded.  It is assembled from the
  discrete Calderón–Zygmund inputs for the linearised deviation kernel (`lacDevSymBoundAlt`,
  `lacDevL2`, `lacDevHormanderAlt`) through `lacDilDevSqSum_of_inputs`.

The deviation's variational norm is then controlled by its values square function through the
elementary `Work.KMTAreas.A7.variationalNorm_le_sqSum`, and the two pieces are combined by
subadditivity/homogeneity of the variational norm (`Submission.VarNorm`) and Minkowski's
inequality in `ℓᵖ`.
-/


/-- The `eLpNorm` of an `ℝ≥0∞`-valued function on `ℤ` (counting measure) is the `L^p` "norm". -/
theorem eLpNorm_count_ennreal_eq (p : ℝ) (hp : 0 < p) (F : ℤ → ℝ≥0∞) :
    MeasureTheory.eLpNorm F (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      = (∫⁻ y : ℤ, F y ^ p ∂MeasureTheory.Measure.count) ^ (1 / p) := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  exact congrArg (fun z => z ^ (1 / p)) (lintegral_congr fun y => by rw [enorm_eq_self])

/-- **Minkowski's inequality for `ℝ≥0∞`-valued functions on `ℤ`** (two terms). -/
theorem eLpNorm_count_add_le (p : ℝ) (hp : 1 ≤ p) (F G : ℤ → ℝ≥0∞) :
    MeasureTheory.eLpNorm (fun y : ℤ => F y + G y) (ENNReal.ofReal p)
        (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ MeasureTheory.eLpNorm F (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        + MeasureTheory.eLpNorm G (ENNReal.ofReal p)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  rw [eLpNorm_count_ennreal_eq p hp0 (fun y : ℤ => F y + G y),
    eLpNorm_count_ennreal_eq p hp0 F, eLpNorm_count_ennreal_eq p hp0 G]
  exact ENNReal.lintegral_Lp_add_le (μ := MeasureTheory.Measure.count)
    (measurable_of_countable F).aemeasurable (measurable_of_countable G).aemeasurable hp

/-- The variational norm of the deviation sequence is dominated by the values square function
(elementary, `Work.KMTAreas.A7.variationalNorm_le_sqSum`). -/
theorem dev_var_le_sqSum (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (r : NNReal) (hr : 2 ≤ r)
    (f : ℤ → ℂ) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => devOp K σ n f x) ≤
      ENNReal.ofReal (2 * (2 : ℝ) ^ (1 / (r : ℝ)) + 1) *
        (∑' n : ℕ, ‖devOp K σ n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
  variationalNorm_le_sqSum hr _

/-- The variational norm of the (scaled) triangular smoothing sequence is the scalar times the
variational norm of the smoothing sequence. -/
theorem tri_var_smul (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (r : NNReal) (hr : 1 ≤ r)
    (f : ℤ → ℂ) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => lacConst K * triSmooth σ n f x) =
      ‖lacConst K‖ₑ * PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => triSmooth σ n f x) := by
  have hfun : (fun n : ℕ => lacConst K * triSmooth σ n f x)
      = lacConst K • (fun n : ℕ => triSmooth σ n f x) := rfl
  rw [hfun]
  exact Submission.PointwiseErgodicTheorems.variationalNorm_smul hr (lacConst K) _

/-- **The assembly step.**  From the two halves one obtains the target estimate. -/
theorem lacunaryBumpDilationVar_of_pieces (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r)
    (K : SchwartzMap ℝ ℂ)
    (hTri : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (σ : ℕ → ℕ), (∀ n, 1 ≤ σ n) →
      (∀ n, 2 * σ n ≤ σ (n + 1)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => triSmooth σ n f x))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C₁ * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count)
    (hDev : ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (σ : ℕ → ℕ), (∀ n, 1 ≤ σ n) →
      (∀ n, 2 * σ n ≤ σ (n + 1)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ =>
          (∑' n : ℕ, ‖devOp K σ n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C₂ * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n)
      (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' j : ℤ, (1 / (σ n : ℝ)) * K ((j : ℝ) / (σ n)) * f (x - j)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
  obtain ⟨C₁, hC₁pos, hTri'⟩ := hTri
  obtain ⟨C₂, hC₂pos, hDev'⟩ := hDev
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  have hr2 : (2 : NNReal) ≤ r := le_of_lt hr
  have hcne : ‖lacConst K‖ₑ ≠ ⊤ := enorm_ne_top
  set D : ℝ := 2 * (2 : ℝ) ^ (1 / (r : ℝ)) + 1 with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  refine ⟨(‖lacConst K‖ₑ.toReal + D) * (C₁ + C₂) + 1, by positivity, ?_⟩
  intro σ hσ1 hσ2 f
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => bumpOp K σ n f x)
      ≤ ‖lacConst K‖ₑ * PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => triSmooth σ n f x)
        + ENNReal.ofReal D * (∑' n : ℕ, ‖devOp K σ n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    intro x
    have hseq : (fun n : ℕ => bumpOp K σ n f x)
        = (fun n : ℕ => lacConst K * triSmooth σ n f x) + (fun n : ℕ => devOp K σ n f x) := by
      funext n
      rw [Pi.add_apply, bump_decomp K σ n f x]
    rw [hseq]
    refine (Submission.PointwiseErgodicTheorems.variationalNorm_add_le hr1 _ _).trans ?_
    rw [tri_var_smul K σ r hr1 f x]
    refine add_le_add le_rfl ?_
    rw [hD]
    exact dev_var_le_sqSum K σ r hr2 f x
  have hpt' : ∀ x : ℤ, ‖PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => bumpOp K σ n f x)‖ₑ
      ≤ ‖‖lacConst K‖ₑ * PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => triSmooth σ n f x)
        + ENNReal.ofReal D * (∑' n : ℕ, ‖devOp K σ n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)‖ₑ :=
    fun x => by simpa only [enorm_eq_self] using hpt x
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hpt').trans ?_
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; linarith
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  refine (eLpNorm_count_add_le p hp.le
      (fun x : ℤ => ‖lacConst K‖ₑ * PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => triSmooth σ n f x))
      (fun x : ℤ => ENNReal.ofReal D * (∑' n : ℕ, ‖devOp K σ n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))).trans ?_
  rw [Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal hcne hp0 hptop,
    Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal ENNReal.ofReal_ne_top hp0 hptop]
  set A : ℝ≥0∞ := MeasureTheory.eLpNorm f (ENNReal.ofReal p)
      (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
  set A₁ : ℝ≥0∞ := MeasureTheory.eLpNorm
      (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => triSmooth σ n f x))
      (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
  set A₂ : ℝ≥0∞ := MeasureTheory.eLpNorm
      (fun x : ℤ => (∑' n : ℕ, ‖devOp K σ n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ))
      (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
  have hcoef : ‖lacConst K‖ₑ * ENNReal.ofReal C₁ + ENNReal.ofReal D * ENNReal.ofReal C₂
      ≤ ENNReal.ofReal ((‖lacConst K‖ₑ.toReal + D) * (C₁ + C₂) + 1) := by
    have hreal : ‖lacConst K‖ₑ.toReal * C₁ + D * C₂
        ≤ (‖lacConst K‖ₑ.toReal + D) * (C₁ + C₂) + 1 := by
      nlinarith [hC₁pos, hC₂pos, hDpos, ENNReal.toReal_nonneg (a := ‖lacConst K‖ₑ)]
    calc ‖lacConst K‖ₑ * ENNReal.ofReal C₁ + ENNReal.ofReal D * ENNReal.ofReal C₂
        = ENNReal.ofReal (‖lacConst K‖ₑ.toReal) * ENNReal.ofReal C₁
            + ENNReal.ofReal D * ENNReal.ofReal C₂ := by
            conv_lhs => rw [← ENNReal.ofReal_toReal hcne]
      _ = ENNReal.ofReal (‖lacConst K‖ₑ.toReal * C₁) + ENNReal.ofReal (D * C₂) := by
          rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul hDpos.le]
      _ = ENNReal.ofReal (‖lacConst K‖ₑ.toReal * C₁ + D * C₂) := by
          rw [ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg hC₁pos.le)
            (mul_nonneg hDpos.le hC₂pos.le)]
      _ ≤ ENNReal.ofReal ((‖lacConst K‖ₑ.toReal + D) * (C₁ + C₂) + 1) :=
          ENNReal.ofReal_le_ofReal hreal
  calc ‖lacConst K‖ₑ * A₁ + ENNReal.ofReal D * A₂
      ≤ ‖lacConst K‖ₑ * (ENNReal.ofReal C₁ * A) + ENNReal.ofReal D * (ENNReal.ofReal C₂ * A) := by
        have h1 : A₁ ≤ ENNReal.ofReal C₁ * A := hTri' σ hσ1 hσ2 f
        have h2 : A₂ ≤ ENNReal.ofReal C₂ * A := hDev' σ hσ1 hσ2 f
        gcongr
    _ = (‖lacConst K‖ₑ * ENNReal.ofReal C₁ + ENNReal.ofReal D * ENNReal.ofReal C₂) * A := by ring
    _ ≤ ENNReal.ofReal ((‖lacConst K‖ₑ.toReal + D) * (C₁ + C₂) + 1) * A := by
        gcongr

/-- **The lacunary variational estimate for a family of discrete low-pass (bump) convolution
operators on `ℤ`.**  For a fixed Schwartz kernel `K : ℝ → ℂ` and a `2`-lacunary sequence of integral
scales `σ : ℕ → ℕ`, the `r`-variation, `2 < r`, of the family
`f ↦ (K_{σ_n} * f)(x) = Σ_j (1/σ_n) K (j/σ_n) f (x - j)` is bounded on `ℓᵖ(ℤ)`, `1 < p < ∞`, by a
constant times `‖f‖_{ℓᵖ}`. -/
theorem lacunaryBumpDilationVar (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r)
    (K : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℕ) (hσ1 : ∀ n, 1 ≤ σ n)
      (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' j : ℤ, (1 / (σ n : ℝ)) * K ((j : ℝ) / (σ n)) * f (x - j)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
  exact lacunaryBumpDilationVar_of_pieces p hp r hr K (lacDilTriVar p hp r hr) (lacDilDevSqSumViaAlt p hp K)

end

end Work.KMTAreas.A7
