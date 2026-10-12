import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.blockIIDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dictIIDefs` — vocabulary for the `L¹` block-`II` dictionary

* `JL21`, `JL23` — the two explicit triple integrals of the block-`II` row shapes (the
  `qmqKR`-form to which `rowShape21`/`rowShape23` reduce, see `dictII_L1`);
* `acubePair ℓ` — the product measure `(volume↾Λ) ⊗ (volume↾Λ)` on `Λ × Λ`, `Λ = acube ℓ`;
* `kBound ℓ b` — the pointwise dominator of `qmqKR ℓ b`;
* `clampK n b` — the level-`n` truncation of a pair kernel.

Everything here is `sorry`-free.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- The block-`II.1` triple integral: the `u,y`-averaged integral of the state against the real
`Q M Q` kernel `qmqKR ℓ k`. -/
noncomputable def JL21 {n : ℕ} (ℓ : ℝ) (Ψ : Xn n → ℝ) (k : E3 → E3 → ℝ)
    (p : Fin n × Fin n) : ℝ :=
  ∫ x in Submission.BoseGases.abox n ℓ, ∫ y in Submission.BoseGases.acube ℓ,
    ∫ u in Submission.BoseGases.acube ℓ,
      Ψ x * qmqKR ℓ k u y * Ψ (Function.update (Function.update x p.1 y) p.2 u)

/-- The block-`II.2` triple integral (the kernel evaluated at the two configuration slots). -/
noncomputable def JL23 {n : ℕ} (ℓ : ℝ) (Ψ : Xn n → ℝ) (k : E3 → E3 → ℝ)
    (p : Fin n × Fin n) : ℝ :=
  ∫ x in Submission.BoseGases.abox n ℓ, ∫ y in Submission.BoseGases.acube ℓ,
    ∫ u in Submission.BoseGases.acube ℓ,
      Ψ x * qmqKR ℓ k (x p.1) (x p.2) * Ψ (Function.update (Function.update x p.1 y) p.2 u)

/-- The product measure `(volume↾Λ) ⊗ (volume↾Λ)` on `Λ × Λ`, where `Λ = acube ℓ`. -/
noncomputable def acubePair (ℓ : ℝ) : Measure (E3 × E3) :=
  ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
    ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))

/-- The pointwise dominator of `qmqKR ℓ b`: the four rows of `|b|` and its box averages. -/
noncomputable def kBound (ℓ : ℝ) (b : E3 → E3 → ℝ) : E3 × E3 → ℝ :=
  fun p => |b p.1 p.2|
    + |(ℓ ^ 3)⁻¹| * (∫ y' in Submission.BoseGases.acube ℓ, |b p.1 y'|)
    + |(ℓ ^ 3)⁻¹| * (∫ w' in Submission.BoseGases.acube ℓ, |b w' p.2|)
    + |(ℓ ^ 3)⁻¹| ^ 2 * (∫ w' in Submission.BoseGases.acube ℓ,
        ∫ y' in Submission.BoseGases.acube ℓ, |b w' y'|)

/-- The level-`n` truncation of a pair kernel. -/
noncomputable def clampK (n : ℕ) (b : E3 → E3 → ℝ) : E3 → E3 → ℝ :=
  fun w y => max (-(n : ℝ)) (min (n : ℝ) (b w y))

/-- The volume restricted to the centred cube. -/
noncomputable abbrev cubeμ (ℓ : ℝ) : Measure E3 :=
  (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)

/-- The integrand of the block-`II.1` triple integral `JL21`. -/
noncomputable def Phi21 {n : ℕ} (ℓ : ℝ) (Ψ : Xn n → ℝ) (k : E3 → E3 → ℝ) (p : Fin n × Fin n)
    (x : Xn n) (y u : E3) : ℝ :=
  Ψ x * qmqKR ℓ k u y * Ψ (Function.update (Function.update x p.1 y) p.2 u)

/-- The integrand of the block-`II.2` triple integral `JL23`. -/
noncomputable def Phi23 {n : ℕ} (ℓ : ℝ) (Ψ : Xn n → ℝ) (k : E3 → E3 → ℝ) (p : Fin n × Fin n)
    (x : Xn n) (y u : E3) : ℝ :=
  Ψ x * qmqKR ℓ k (x p.1) (x p.2) * Ψ (Function.update (Function.update x p.1 y) p.2 u)

/-- `|a − b| ≤ |a| + |b|` for reals. -/
theorem abs_sub_le_abs_add' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa [sub_eq_add_neg] using abs_add_le a (-b)

/-- `kBound` dominates `qmqKR` pointwise (for an integrable kernel, so that the inner box average
is a genuine integrable function). -/
theorem norm_qmqKR_le_kBound {ℓ : ℝ} {b : E3 → E3 → ℝ}
    (hint : Integrable (Function.uncurry b) (acubePair ℓ)) (w y : E3) :
    ‖qmqKR ℓ b w y‖ ≤ kBound ℓ b (w, y) := by
  have hinner : ∀ w' : E3, |∫ y' in Submission.BoseGases.acube ℓ, b w' y'|
      ≤ ∫ y' in Submission.BoseGases.acube ℓ, |b w' y'| := fun w' =>
    (by simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm
        (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
        (f := fun y' => b w' y')))
  have hA := hinner w
  have hB : |∫ w' in Submission.BoseGases.acube ℓ, b w' y|
      ≤ ∫ w' in Submission.BoseGases.acube ℓ, |b w' y| := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm
        (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
        (f := fun w' => b w' y))
  have hC : ‖∫ w' in Submission.BoseGases.acube ℓ,
        ∫ y' in Submission.BoseGases.acube ℓ, b w' y'‖
      ≤ ∫ w' in Submission.BoseGases.acube ℓ,
        ∫ y' in Submission.BoseGases.acube ℓ, |b w' y'| := by
    refine le_trans (norm_integral_le_integral_norm
      (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
      (f := fun w' => ∫ y' in Submission.BoseGases.acube ℓ, b w' y')) ?_
    refine integral_mono_of_nonneg (Eventually.of_forall fun w' => norm_nonneg _) ?_
      (Eventually.of_forall fun w' => ?_)
    · simpa [acubePair, Function.uncurry, Real.norm_eq_abs] using
        (hint.integral_norm_prod_left
          (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
          (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)))
    · simpa only [Real.norm_eq_abs] using hinner w'
  have hstep : |qmqKR ℓ b w y|
      ≤ |b w y| + |(ℓ ^ 3)⁻¹| * |∫ y' in Submission.BoseGases.acube ℓ, b w y'|
        + |(ℓ ^ 3)⁻¹| * |∫ w' in Submission.BoseGases.acube ℓ, b w' y|
        + |(ℓ ^ 3)⁻¹| ^ 2 * |∫ w' in Submission.BoseGases.acube ℓ,
            ∫ y' in Submission.BoseGases.acube ℓ, b w' y'| := by
    rw [qmqKR]
    calc |(b w y - (ℓ ^ 3)⁻¹ * (∫ y' in Submission.BoseGases.acube ℓ, b w y')
            - (ℓ ^ 3)⁻¹ * (∫ w' in Submission.BoseGases.acube ℓ, b w' y))
          + ((ℓ ^ 3)⁻¹) ^ 2 * (∫ w' in Submission.BoseGases.acube ℓ,
              ∫ y' in Submission.BoseGases.acube ℓ, b w' y')|
        ≤ |(b w y - (ℓ ^ 3)⁻¹ * (∫ y' in Submission.BoseGases.acube ℓ, b w y'))
            - (ℓ ^ 3)⁻¹ * (∫ w' in Submission.BoseGases.acube ℓ, b w' y)|
          + |((ℓ ^ 3)⁻¹) ^ 2 * (∫ w' in Submission.BoseGases.acube ℓ,
              ∫ y' in Submission.BoseGases.acube ℓ, b w' y')| := abs_add_le _ _
      _ ≤ (|b w y| + |(ℓ ^ 3)⁻¹ * (∫ y' in Submission.BoseGases.acube ℓ, b w y')|)
            + |(ℓ ^ 3)⁻¹ * (∫ w' in Submission.BoseGases.acube ℓ, b w' y)|
          + |((ℓ ^ 3)⁻¹) ^ 2 * (∫ w' in Submission.BoseGases.acube ℓ,
              ∫ y' in Submission.BoseGases.acube ℓ, b w' y')| := by
          linarith [abs_sub_le_abs_add' (b w y)
              ((ℓ ^ 3)⁻¹ * (∫ y' in Submission.BoseGases.acube ℓ, b w y')),
            abs_sub_le_abs_add'
              (b w y - (ℓ ^ 3)⁻¹ * (∫ y' in Submission.BoseGases.acube ℓ, b w y'))
              ((ℓ ^ 3)⁻¹ * (∫ w' in Submission.BoseGases.acube ℓ, b w' y))]
      _ = |b w y| + |(ℓ ^ 3)⁻¹| * |∫ y' in Submission.BoseGases.acube ℓ, b w y'|
            + |(ℓ ^ 3)⁻¹| * |∫ w' in Submission.BoseGases.acube ℓ, b w' y|
            + |(ℓ ^ 3)⁻¹| ^ 2 * |∫ w' in Submission.BoseGases.acube ℓ,
                ∫ y' in Submission.BoseGases.acube ℓ, b w' y'| := by
          simp only [abs_mul, abs_pow]
  refine le_trans (le_of_eq (Real.norm_eq_abs _)) (le_trans hstep ?_)
  simp only [kBound]
  have hC' : |∫ w' in Submission.BoseGases.acube ℓ,
        ∫ y' in Submission.BoseGases.acube ℓ, b w' y'|
      ≤ ∫ w' in Submission.BoseGases.acube ℓ,
        ∫ y' in Submission.BoseGases.acube ℓ, |b w' y'| := by
    simpa only [Real.norm_eq_abs] using hC
  nlinarith [abs_nonneg (b w y), abs_nonneg (ℓ ^ 3)⁻¹,
    mul_le_mul_of_nonneg_left hA (abs_nonneg (ℓ ^ 3)⁻¹),
    mul_le_mul_of_nonneg_left hB (abs_nonneg (ℓ ^ 3)⁻¹),
    mul_le_mul_of_nonneg_left hC' (sq_nonneg |(ℓ ^ 3)⁻¹|)]

/-- `kBound` is nonnegative. -/
theorem kBound_nonneg (ℓ : ℝ) (b : E3 → E3 → ℝ) (p : E3 × E3) : 0 ≤ kBound ℓ b p := by
  have h1 : 0 ≤ ∫ y' in Submission.BoseGases.acube ℓ, |b p.1 y'| :=
    integral_nonneg fun y' => abs_nonneg _
  have h2 : 0 ≤ ∫ w' in Submission.BoseGases.acube ℓ, |b w' p.2| :=
    integral_nonneg fun w' => abs_nonneg _
  have h3 : 0 ≤ ∫ w' in Submission.BoseGases.acube ℓ,
      ∫ y' in Submission.BoseGases.acube ℓ, |b w' y'| :=
    integral_nonneg fun w' => integral_nonneg fun y' => abs_nonneg _
  simp only [kBound]
  nlinarith [abs_nonneg (b p.1 p.2), abs_nonneg (ℓ ^ 3)⁻¹, sq_nonneg |(ℓ ^ 3)⁻¹|]

/-! ## The truncations -/

theorem clampK_measurable (n : ℕ) {b : E3 → E3 → ℝ}
    (hb : Measurable (Function.uncurry b)) : Measurable (Function.uncurry (clampK n b)) := by
  have h : Function.uncurry (clampK n b)
      = fun p : E3 × E3 => max (-(n : ℝ)) (min (n : ℝ) (Function.uncurry b p)) := by
    funext p
    rfl
  rw [h]
  exact measurable_const.max (measurable_const.min hb)

theorem clampK_symm {b : E3 → E3 → ℝ} (hb : ∀ w y, b w y = b y w) (n : ℕ) :
    ∀ w y, clampK n b w y = clampK n b y w := by
  intro w y
  simp only [clampK, hb w y]

theorem clampK_abs_le (n : ℕ) (b : E3 → E3 → ℝ) (w y : E3) :
    |clampK n b w y| ≤ |b w y| := by
  rw [clampK, abs_le]
  refine ⟨?_, ?_⟩
  · refine le_trans (le_min ?_ (neg_abs_le _)) (le_max_right _ _)
    exact le_trans (neg_nonpos.mpr (abs_nonneg _)) (Nat.cast_nonneg n)
  · refine max_le ?_ ?_
    · exact le_trans (neg_nonpos.mpr (Nat.cast_nonneg n)) (abs_nonneg _)
    · exact le_trans (min_le_right _ _) (le_abs_self _)

theorem clampK_abs_le_n (n : ℕ) (b : E3 → E3 → ℝ) (w y : E3) :
    |clampK n b w y| ≤ (n : ℝ) := by
  rw [clampK, abs_le]
  exact ⟨le_max_left _ _, max_le (neg_le_self (Nat.cast_nonneg n)) (min_le_left _ _)⟩

theorem clampK_tendsto (b : E3 → E3 → ℝ) (w y : E3) :
    Tendsto (fun n : ℕ => clampK n b w y) atTop (𝓝 (b w y)) := by
  have h1 : ∀ᶠ n : ℕ in atTop, min (n : ℝ) (b w y) = b w y := by
    filter_upwards [eventually_ge_atTop (Nat.ceil (b w y))] with n hn
    rw [min_eq_right]
    exact le_trans (Nat.le_ceil (b w y)) (by exact_mod_cast hn)
  have h2 : ∀ᶠ n : ℕ in atTop, max (-(n : ℝ)) (b w y) = b w y := by
    filter_upwards [eventually_ge_atTop (Nat.ceil (-(b w y)))] with n hn
    rw [max_eq_right]
    have hle : -(b w y) ≤ (n : ℝ) :=
      le_trans (Nat.le_ceil (-(b w y))) (by exact_mod_cast hn)
    linarith
  have h3 : (fun n : ℕ => clampK n b w y) =ᶠ[atTop] fun _ : ℕ => b w y := by
    filter_upwards [h1, h2] with n h1n h2n
    simp only [clampK, h1n, h2n]
  rw [Filter.tendsto_congr' h3]
  exact tendsto_const_nhds

end Work.BoseBoxFock
