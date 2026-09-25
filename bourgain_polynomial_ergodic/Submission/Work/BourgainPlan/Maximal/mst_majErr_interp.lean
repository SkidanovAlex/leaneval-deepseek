import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mst_minor_per_n
import Submission.Work.BourgainPlan.Maximal.ellp_interpolation

/-!
# Interpolating the two endpoints of a major-arc error: the `2^{−cn}` gains of MST §4.2

Each of the two major-arc errors of Mirek–Stein–Trojan §4.2 is estimated twice:

* in `ℓ²`, with an exponential gain (`2^{−n/2}` for `m_{2^n}Ξ_n − ν_{2^n}`, `2^{−cn}` for
  `ν_{2^n} − Σ_{s<n}ν_{2^n}^s`) — eqs. (70), (76);
* in `ℓʳ` for every `r > 1`, with the *loss* `exp((n^l)^{1/(10l)}) = exp(n^{1/10})` coming from the
  number of arcs (`#𝒰(n) ≤ exp(n^{1/10})`) — eqs. (72), (78).

Riesz–Thorin between the two endpoints at an exponent `p ∈ (r, 2)` converts the exponential loss
into an exponential gain `2^{−cn}` for some `c > 0` (eqs. (73), (80)).  This module contains that
elementary step in the two pieces the assembly needs:

* `opMulFinsuppLM_interp` — the Riesz–Thorin interpolation itself, phrased for the `ℂ`-linear map
  `opMulFinsuppLM Φ` on finitely supported sequences (so that `ellp_interpolation` applies);
* `mst_interp_arithmetic` — the numerical comparison `(C₂ 2^{−n/2})^{1−θ}(C₁ e^{n^{1/10}})^θ ≤ C 2^{−cn}`
  for `0 < θ < 1`.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-- **Riesz–Thorin interpolation of the two endpoints of an arc multiplier.**  With `1 < r < p < 2`
and `θ := (1/r − 1/p)/(1/r − 1/2) ∈ (0,1)` (so that `1/p = (1−θ)/r + θ/2`), an `ℓʳ` bound with
constant `A` and an `ℓ²` bound with constant `B` for the multiplier with symbol class `Φ` combine
into an `ℓᵖ` bound with constant `A^{1−θ}B^{θ}`. -/
theorem opMulFinsuppLM_interp (Φ : Lp ℂ ⊤ haarT) {r p A B : ℝ} (hr : 1 < r) (hrp : r < p)
    (hp : p < 2) (hA : 0 < A) (hB : 0 < B)
    (hr' : ∀ f : ℤ →₀ ℂ, MeasureTheory.eLpNorm (opMulFinsuppLM Φ f) (ENNReal.ofReal r)
      MeasureTheory.Measure.count
        ≤ ENNReal.ofReal A * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal r) MeasureTheory.Measure.count)
    (h2 : ∀ f : ℤ →₀ ℂ, MeasureTheory.eLpNorm (opMulFinsuppLM Φ f) (ENNReal.ofReal 2)
      MeasureTheory.Measure.count
        ≤ ENNReal.ofReal B * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal 2) MeasureTheory.Measure.count) :
    ∀ f : ℤ →₀ ℂ, MeasureTheory.eLpNorm (opMulFinsuppLM Φ f) (ENNReal.ofReal p)
      MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (A ^ (1 - (1 / r - 1 / p) / (1 / r - 1 / 2))
            * B ^ ((1 / r - 1 / p) / (1 / r - 1 / 2)))
          * MeasureTheory.eLpNorm (⇑f) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  have hr2 : r < 2 := lt_trans hrp hp
  have hp1 : (1 : ℝ) < p := lt_trans hr hrp
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp1
  have hden : (0 : ℝ) < 1 / r - 1 / 2 := by
    have h : (1 : ℝ) / 2 < 1 / r := one_div_lt_one_div_of_lt hr0 hr2
    linarith
  have hnum : (0 : ℝ) < 1 / r - 1 / p := by
    have h : (1 : ℝ) / p < 1 / r := one_div_lt_one_div_of_lt hr0 hrp
    linarith
  have hθ0 : 0 ≤ (1 / r - 1 / p) / (1 / r - 1 / 2) := le_of_lt (div_pos hnum hden)
  have hθ1 : (1 / r - 1 / p) / (1 / r - 1 / 2) ≤ 1 := by
    rw [div_le_one hden]
    have h : (1 : ℝ) / 2 < 1 / p := one_div_lt_one_div_of_lt hp0 hp
    linarith
  have hθp : 1 / p = (1 - (1 / r - 1 / p) / (1 / r - 1 / 2)) / r
      + ((1 / r - 1 / p) / (1 / r - 1 / 2)) / 2 := by
    have h1 : (1 / r - 1 / p) / (1 / r - 1 / 2) * (1 / r - 1 / 2) = 1 / r - 1 / p :=
      div_mul_cancel₀ _ (ne_of_gt hden)
    have h2 : 1 / r - (1 / r - 1 / p) = 1 / p := by ring
    have h3 : (1 - (1 / r - 1 / p) / (1 / r - 1 / 2)) / r
        + ((1 / r - 1 / p) / (1 / r - 1 / 2)) / 2
        = 1 / r - ((1 / r - 1 / p) / (1 / r - 1 / 2)) * (1 / r - 1 / 2) := by
      field_simp
      ring
    rw [h3, h1, h2]
  exact ellp_interpolation (q₀ := r) (q₁ := 2) (p := p)
    (θ := (1 / r - 1 / p) / (1 / r - 1 / 2)) (A := A) (B := B)
    (le_of_lt hr) (le_of_lt hr2) hp1 hθ0 hθ1 hθp hA hB (opMulFinsuppLM Φ) hr' h2

end

end Work.BourgainPlan.Maximal
