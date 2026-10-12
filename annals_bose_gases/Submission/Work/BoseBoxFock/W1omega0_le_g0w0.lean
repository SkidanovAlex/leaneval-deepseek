import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7AK.W1rows.W1omega_low_nonneg
import Submission.Work.BoseBoxFock.PotGroupDefs
import Submission.Work.BoseRowsFS.W1sub_g0_ae_bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.W1omega0_le_g0w0`

**The sharp comparison of `Ŵ₁ω(0) = ∫ W₁ω` with the `g₀ω`-mass.**

With `W₁ = Work.BoseFixR.W1fun v h ℓ = wScaled ℓ (g₀)` and
`W₁ω = Work.BoseFixR.W1omegaFun v h ℓ = wScaled ℓ (g₀·ω)`, `g₀ = v(1−ω)`,
`ω = Classical.choose h`, one has in the FS dilute regime `R ≤ ℓ·chiR0`

    `Ŵ₁ω(0) ≤ (1 + 2C₁(R/ℓ)²) · ∫ g₀ω`,

where `C₁` is any *global* quadratic deviation constant for `χ⋆χ`,
`|(χ⋆χ)(t) − 1| ≤ C₁‖t‖²`.  This is FS's `eq:W1-g` applied to the numerator
`g₀ω` (which is supported in `ball 0 R` and a.e. nonnegative).

## Proof

1. `chat_zero`: `Ŵ₁ω(0) = ∫ W₁ω`.
2. `W₁ω` is the product of `W₁` and `ω`:
   `W₁ω(x) = (g₀(x)·ω(x))/(χ⋆χ)(x/ℓ) = W₁(x)·ω(x)` (`W1omegaFun_eq_W1fun_mul`).
3. `ω ≥ 0` a.e. and, by the sharp a.e. sandwich
   `Work.BoseB7AK.C3Q.W1_sharp_ae_aux` (FS `eq:W1-g`, which handles both the
   sharp regime `C₁(R/ℓ)² ≤ 1/2` and the crude regime `C₁(R/ℓ)² > 1/2`),
   `W₁(x) ≤ (1 + 2C₁(R/ℓ)²)·g₀(x)` a.e.  Multiplying by `ω(x) ≥ 0` gives
   `W₁ω(x ≤ (1 + 2C₁(R/ℓ)²)·(g₀ω)(x)` a.e.
4. Both sides are integrable (`W1omegaFun_integrable`, `g0w0_integrable`), so
   `integral_mono_ae` plus `integral_const_mul` conclude.
-/

namespace Work.BoseBoxFock

/-- **`W₁ω` is the product of `W₁` and `ω`.**  Definitionally both sides have
numerator divided by the same convolution `(χ⋆χ)(·/ℓ)`; the only content is
`(a·b)/c = (a/c)·b`, which holds for the total division of a field. -/
private lemma W1omegaFun_eq_W1fun_mul (v : EuclideanSpace ℝ (Fin 3) → ℝ)
    (h : Work.UBB.ScatSol v) (ℓ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixR.W1omegaFun v h ℓ x
      = Work.BoseFixR.W1fun v h ℓ x * Classical.choose h x := by
  simp only [Work.BoseFixR.W1omegaFun, Work.BoseFixR.W1fun, Submission.BoseGases.wScaled]
  ring

theorem W1omega0_le_g0w0 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R ℓ C₁ : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ) (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ t : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.conv3 Submission.BoseGases.chi
      Submission.BoseGases.chi t - 1| ≤ C₁ * ‖t‖ ^ 2)
    (hv_nonneg : 0 ≤ v) (hvrad : BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h ℓ) 0
      ≤ (1 + 2 * C₁ * (R / ℓ) ^ 2) * (∫ z : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.g0 v h z * Classical.choose h z) := by
  rw [Work.BoseB7AK.W1rows.chat_zero]
  -- the sharp a.e. sandwich `W₁ ≤ (1+2C₁(R/ℓ)²)·g₀` for the FS kernel `W₁`
  have hsharp :=
    Work.BoseB7AK.C3Q.W1_sharp_ae_aux hR hℓ hC₁0 hC₁ hv_nonneg hvrad hv_supp h hRℓ
  -- the a.e. bounds `0 ≤ ω ≤ 1` on the chosen scattering solution
  obtain ⟨hωnn, hωle⟩ :=
    Submission.BoseGases.chosen_w0_bounds_ae hR hv_nonneg hvrad hv_supp h
  have hpt : ∀ᵐ z ∂(MeasureTheory.volume :
      MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      Work.BoseFixR.W1omegaFun v h ℓ z
        ≤ (1 + 2 * C₁ * (R / ℓ) ^ 2)
            * (Submission.BoseGases.g0 v h z * Classical.choose h z) := by
    filter_upwards [hsharp, hωnn] with z hz hzω
    have hzle : Work.BoseFixR.W1fun v h ℓ z
        ≤ (1 + 2 * C₁ * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h z := hz.2
    rw [W1omegaFun_eq_W1fun_mul]
    calc Work.BoseFixR.W1fun v h ℓ z * Classical.choose h z
        ≤ ((1 + 2 * C₁ * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h z)
            * Classical.choose h z :=
          mul_le_mul_of_nonneg_right hzle hzω
      _ = (1 + 2 * C₁ * (R / ℓ) ^ 2)
            * (Submission.BoseGases.g0 v h z * Classical.choose h z) := by ring
  have hWi : MeasureTheory.Integrable (Work.BoseFixR.W1omegaFun v h ℓ) :=
    Work.BoseB7AK.W1rows.W1omegaFun_integrable hR hℓ hv_nonneg hvrad hv_supp h hRℓ
  have hgω : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.g0 v h z * Classical.choose h z) :=
    Submission.BoseGases.g0w0_integrable hR hv_nonneg hvrad hv_supp h
  calc ∫ z, Work.BoseFixR.W1omegaFun v h ℓ z
      ≤ ∫ z, (1 + 2 * C₁ * (R / ℓ) ^ 2)
          * (Submission.BoseGases.g0 v h z * Classical.choose h z) :=
        MeasureTheory.integral_mono_ae hWi (hgω.const_mul _) hpt
    _ = (1 + 2 * C₁ * (R / ℓ) ^ 2)
          * ∫ z, Submission.BoseGases.g0 v h z * Classical.choose h z :=
        MeasureTheory.integral_const_mul _ _

end Work.BoseBoxFock
