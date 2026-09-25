import Mathlib
import Submission.Work.BourgainPlan.Maximal.ell2MaxWeakOne
import Submission.Work.BourgainPlan.Maximal.ell2MaxLpLtTwo

/-!
# The vector-valued (`ℓ²`) dyadic maximal inequality in the range `1 < p < 2`

Assembly of the two delegated bricks:

* `ell2MaxWeakOne` — the weak-`(1,1)` bound for the `ℓ²`-valued dyadic maximal function
  (`ℓ²MaxWeakOne`, the Calderón–Zygmund stopping-time argument, uniform in the number of
  components), and
* `ell2MaxLpLtTwo` — Marcinkiewicz interpolation of that bound with the `L²(ℓ²)` endpoint
  (`lintegral_ell2Max_le`),

giving the per-component Fefferman–Stein estimate

`‖ (Σ_t (dyMax f_t)²)^{1/2} ‖_{L^p} ≤ C_p ‖ (Σ_t |f_t|²)^{1/2} ‖_{L^p}`,  `1 < p < 2`,

with a constant independent of the number `n` of components.  This is the input `(eq:47)` of
Mirek–Stein–Trojan's §4 maximal argument in the range `p < 2`; the range `p ≥ 2` needs a different
argument (the per-component `L^∞(ℓ²)` endpoint is false — see `WINDOW_WEAK_TYPE_STATUS_S9.md` §5).
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- **Fefferman--Stein for the `ℓ²`-valued dyadic maximal function, `1 < p < 2`**, with a constant
uniform in the number of components. -/
theorem ell2MaxLpLtTwo' {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) →
      ∫⁻ x, (ell2Max f x) ^ (p / 2) ≤ ENNReal.ofReal (C ^ p) *
        ∫⁻ x, (ell2Sq f x) ^ (p / 2) := by
  obtain ⟨C₀, hC₀, hweak⟩ := ell2MaxWeakOne
  exact ell2MaxLpLtTwo hC₀ hweak hp₁ hp₂

end Work.BourgainPlan.Maximal
