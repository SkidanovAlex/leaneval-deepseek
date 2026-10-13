import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.StrongEps.E5G

open MeasureTheory

/-- Weighted-average Hölder estimate: if `ψ ≥ 0` is a probability density supported on `K`
(so that `∫_K ψ = 1`), `ψ` vanishes off a `δ`-neighbourhood of `q`, and `f` is `1/2`-Hölder
(with constant `C`) at `q` on `K`, then the `ψ`-average of `f` is within `C δ^{1/2}` of `f q`.

This is the "mollifier peak" step: `∫ f ψ - f q = ∫ (f - f q) ψ`, and `|f p - f q| ≤ C δ^{1/2}`
on the support of `ψ`. -/
lemma dist_setIntegral_mul_le {K : Set (ℝ × ℝ)} (hK : IsCompact K) {f ψ : ℝ × ℝ → ℝ} {q : ℝ × ℝ} {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hf : ContinuousOn f K) (hψ : ContinuousOn ψ K) (hψnn : ∀ p, 0 ≤ ψ p) (hψK : ∀ p, ψ p ≠ 0 → p ∈ K) (hψint : (∫ p in K, ψ p) = 1) (hb : ∀ p ∈ K, dist (f p) (f q) ≤ C * dist p q ^ (1 / 2 : ℝ)) (hδb : ∀ p, ψ p ≠ 0 → dist p q ≤ δ) : dist (∫ p in K, f p * ψ p) (f q) ≤ C * δ ^ (1 / 2 : ℝ) := by
  -- integrability on the compact set `K`
  have hintψ : IntegrableOn ψ K := hψ.integrableOn_compact hK
  have hintfψ : IntegrableOn (fun p => f p * ψ p) K := (hf.mul hψ).integrableOn_compact hK
  have hintcψ : IntegrableOn (fun p => f q * ψ p) K :=
    (continuousOn_const.mul hψ).integrableOn_compact hK
  have hintg : IntegrableOn (fun p => (C * δ ^ (1 / 2 : ℝ)) * ψ p) K :=
    (continuousOn_const.mul hψ).integrableOn_compact hK
  -- pointwise bound of the difference integrand
  have hpt : ∀ p, ‖f p * ψ p - f q * ψ p‖ ≤ (C * δ ^ (1 / 2 : ℝ)) * ψ p := by
    intro p
    rcases eq_or_ne (ψ p) 0 with h0 | hne
    · rw [h0]; simp
    · have hpK : p ∈ K := hψK p hne
      have hd : dist p q ≤ δ := hδb p hne
      have hsq : dist p q ^ (1 / 2 : ℝ) ≤ δ ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow dist_nonneg hd (by norm_num)
      have hle : dist (f p) (f q) ≤ C * δ ^ (1 / 2 : ℝ) :=
        le_trans (hb p hpK) (mul_le_mul_of_nonneg_left hsq hC)
      calc ‖f p * ψ p - f q * ψ p‖
          = ‖(f p - f q) * ψ p‖ := by
            rw [show f p * ψ p - f q * ψ p = (f p - f q) * ψ p from by ring]
        _ = dist (f p) (f q) * ψ p := by
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hψnn p),
              ← Real.dist_eq]
        _ ≤ (C * δ ^ (1 / 2 : ℝ)) * ψ p := mul_le_mul_of_nonneg_right hle (hψnn p)
  -- replace the centre `f q` by its weighted average `∫ f q ψ = f q`
  have hmain : dist (∫ p in K, f p * ψ p) (f q) ≤ ∫ p in K, (C * δ ^ (1 / 2 : ℝ)) * ψ p := by
    rw [dist_eq_norm]
    have h1 : (∫ p in K, f p * ψ p) - f q = ∫ p in K, (f p * ψ p - f q * ψ p) := by
      rw [MeasureTheory.integral_sub hintfψ hintcψ, MeasureTheory.integral_const_mul,
        hψint, mul_one]
    rw [h1]
    calc ‖∫ p in K, (f p * ψ p - f q * ψ p)‖
        ≤ ∫ p in K, ‖f p * ψ p - f q * ψ p‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ p in K, (C * δ ^ (1 / 2 : ℝ)) * ψ p :=
          integral_mono_ae ((hintfψ.sub hintcψ).norm) hintg (Filter.Eventually.of_forall hpt)
  calc dist (∫ p in K, f p * ψ p) (f q)
      ≤ ∫ p in K, (C * δ ^ (1 / 2 : ℝ)) * ψ p := hmain
    _ = C * δ ^ (1 / 2 : ℝ) := by
        rw [MeasureTheory.integral_const_mul, hψint, mul_one]

end Work.FTS.StrongEps.E5G
