import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7AK.W1rows.W1omega0_rows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseB7AK/W1rows/W1omegaFun_moment_integrable.lean`

**The `‖x‖²·|W₁ω(x)|` moment row of the dilute-regime kernel bundle:** for a
nonnegative radial potential `v` of range `R` in the FS dilute regime
`R ≤ ℓ·chiR0`, with a scattering solution `h : ScatSol v`, the second-moment
weighted kernel

    `x ↦ ‖x‖²·|Work.BoseFixR.W1omegaFun v h ℓ x|`,
    `W₁ω = wScaled ℓ (x ↦ g₀(x)·ω(x))`, `g₀ = v(1−ω)`, `ω = Classical.choose h`,

is Lebesgue integrable.  (This is the `L¹(ℝ³, ‖x‖²dx)` statement FS uses to
differentiate/expand `Ŵ₁ω` twice at `k = 0`.)  Since `𝓡 v`'s weight is exactly
a second moment of `W₁ω`-type kernels, this row is what makes the
`X²𝓡`-term of `CloseBoundR`/`errKafz` finite.

## Route (everything is already in the corpus)

1. **The numerator is `L¹`.**  `W1omegaNum v h = g₀ω = (v(1−ω))ω`, which is
   integrable by `ScatGIntegrals.scat_gomega_integrable` (`v ≥ 0`, `v` radial).

2. **The numerator is supported in `‖z‖ ≤ R`** (`g₀_zero_of_norm_ge`, `tsupport v
   ⊆ ball 0 R`), so `wScaled_abs_le_two` applies with the majorant `2|Num|`.

3. **The moment is dominated.**  Pointwise, for every `x`:
   `‖x‖²·|W₁ω(x)| ≤ 2R²·|W1omegaNum x|` — trivially `0` where `Num x = 0`
   (`‖x‖ ≥ R`, where also `W₁ω x = Num x/convScale = 0`), and otherwise
   `‖x‖² ≤ R²` together with `|wScaled ℓ Num x| ≤ 2|Num x|`.

4. `Integrable.mono'` against `(2R²)·|Num|`, with a.e. strong measurability of
   the majorised function from `AEMeasurable.div` (`Num` is `L¹`, `convScale ℓ`
   is continuous).
-/

namespace Work.BoseB7AK.W1rows

noncomputable section

open MeasureTheory

open scoped Topology

/-- **The second moment `∫ ‖x‖²|W₁ω(x)| dx < ∞`.** -/
theorem W1omegaFun_moment_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (h : Work.UBB.ScatSol v)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      ‖x‖ ^ 2 * |Work.BoseFixR.W1omegaFun v h ℓ x|) := by
  have hvnn : (0 : EuclideanSpace ℝ (Fin 3) → ℝ) ≤ v := hv_nonneg
  -- Step 1: the numerator `g₀ω` is in `L¹`.
  have hNil : MeasureTheory.Integrable (W1omegaNum v h) := by
    obtain ⟨hrad, hw⟩ := Classical.choose_spec h
    exact Submission.BoseGases.scat_gomega_integrable hvnn hvrad hv_supp hrad hw
  -- Step 2: the numerator vanishes for `‖z‖ ≥ R`.
  have hsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → W1omegaNum v h z = 0 := fun z hz => by
    have hz0 : Submission.BoseGases.g0 v h z = 0 :=
      Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
    simp [W1omegaNum, hz0]
  -- Step 3: the pointwise domination `‖x‖²|W₁ω(x)| ≤ 2R²|Num(x)|`.
  have hpt : ∀ x : EuclideanSpace ℝ (Fin 3),
      ‖‖x‖ ^ 2 * |Work.BoseFixR.W1omegaFun v h ℓ x|‖ ≤ 2 * R ^ 2 * |W1omegaNum v h x| := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rcases le_total R ‖x‖ with hx | hx
    · have hx0 : W1omegaNum v h x = 0 := hsupp x hx
      rw [W1omegaFun_eq]
      simp [Submission.BoseGases.wScaled, hx0]
    · have hb := Submission.BoseGases.wScaled_abs_le_two hℓ hR.le hRℓ hsupp x
      rw [W1omegaFun_eq]
      have hx2 : ‖x‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg x, hx]
      calc ‖x‖ ^ 2 * |Submission.BoseGases.wScaled ℓ (W1omegaNum v h) x|
          ≤ R ^ 2 * (2 * |W1omegaNum v h x|) :=
            mul_le_mul hx2 hb (abs_nonneg _) (sq_nonneg R)
        _ = 2 * R ^ 2 * |W1omegaNum v h x| := by ring
  -- Step 4: `W₁ω = Num/convScale` is a.e. strongly measurable.
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖ ^ 2 * |Work.BoseFixR.W1omegaFun v h ℓ x|) := by
    have h1 : AEMeasurable (Work.BoseFixR.W1omegaFun v h ℓ) := by
      rw [W1omegaFun_eq]
      exact hNil.aemeasurable.div
        (Submission.BoseGases.convScale_continuous ℓ).aemeasurable
    exact ((continuous_norm.pow 2).aestronglyMeasurable.mul
      (continuous_abs.comp_aestronglyMeasurable h1.aestronglyMeasurable))
  refine MeasureTheory.Integrable.mono' (hNil.abs.const_mul (2 * R ^ 2)) haesm ?_
  exact ae_of_all _ hpt

end

end Work.BoseB7AK.W1rows
