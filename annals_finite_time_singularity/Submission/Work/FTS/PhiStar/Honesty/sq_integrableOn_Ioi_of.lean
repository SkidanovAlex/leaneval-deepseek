import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

-- Intended file: Submission/Work/FTS/PhiStar/Honesty/sq_integrableOn_Ioi_of.lean
-- Intended namespace: Work.FTS.PhiStar.Honesty.
open MeasureTheory Set Filter

/-- **`c² ∈ L¹(z,∞)` for every `z > 0`, from the two standing hypotheses.**
For `z > 0`: on `(z,1)` one has `(c t)² ≤ (c t)²/t⁴` (as `t⁴ ≤ 1`) and `(c t)²/t⁴` is integrable
there by `hnear`; on `(1,∞)` the integrand is `(c t)²`, covered by `hfar`.
Measurability of `c²` on each piece comes from the corresponding hypothesis
(`c²/t⁴` a.e.-strongly-measurable times `t⁴`, resp. `c²` a.e.-strongly-measurable directly).

Route: `Ioi z ⊆ Ioo z 1 ∪ Ici 1`. On the near piece `(c t)²` is *literally* `(c t)²/t⁴ * t⁴`
(`t ≠ 0` there), so its integrability is transported from `hnear` by
`IntegrableOn.mul_continuousOn_of_subset` (the factor `t⁴` is continuous, hence bounded on the
compact `[z,1]`) followed by `IntegrableOn.congr_fun`; the far piece is `Ioi 1 =ᵐ[volume] Ici 1`
(differing by the null set `{1}`), so `IntegrableOn.congr_set_ae` applies to `hfar`. -/
theorem sq_integrableOn_Ioi_of {c : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi z) := by
  -- Piece 1: `(z,1) ⊆ (0,1)`, where `(c t)² ≤ (c t)²/t⁴`.
  have hnear' : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Ioo z 1) :=
    hnear.mono_set fun t ht => ⟨by linarith [hz, ht.1], ht.2⟩
  have hmul : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4 * t ^ 4) (Ioo z 1) :=
    hnear'.mul_continuousOn_of_subset (K := Icc z 1) ((continuous_pow 4).continuousOn)
      measurableSet_Ioo isCompact_Icc fun t ht => ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hnear2 : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ioo z 1) :=
    hmul.congr_fun (fun t ht => by
      have ht0 : t ≠ 0 := ne_of_gt (lt_trans hz ht.1)
      show (c t) ^ 2 / t ^ 4 * t ^ 4 = (c t) ^ 2
      rw [div_mul_cancel₀ _ (pow_ne_zero 4 ht0)]) measurableSet_Ioo
  -- Piece 2: `(1,∞) ⊆ [1,∞)`, differing by the null set `{1}`.
  have hfar2 : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Ici 1) :=
    hfar.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 1)).symm
  -- The two pieces cover `(z,∞)`.
  exact (hnear2.union hfar2).mono_set fun t ht => by
    rcases lt_or_ge t 1 with h | h
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr h

end Work.FTS.PhiStar.Honesty
