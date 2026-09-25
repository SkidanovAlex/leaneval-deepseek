import Mathlib
import Submission.Work.BourgainPlan.Maximal.ell2HLMaxLpLtTwo
import Submission.Work.BourgainPlan.Maximal.ell2HLMaxLpGtTwo
import Submission.Work.BourgainPlan.Maximal.ell2Maximal
import Submission.Work.BourgainPlan.Maximal.ell2MaxLp
import Submission.Work.BourgainPlan.Maximal.dyadicMaximal

/-!
# The `ℓ²`-valued Hardy--Littlewood maximal inequality on `L^p(ℓ²)` for all `1 < p < ∞`

Assembly of the two halves of Mirek--Stein--Trojan's input `(eq:47)` for the corpus's *centred*
maximal function `Commons.Analysis.Maximal.hlMax`:

* `ell2HLMaxLpLtTwo` — the range `1 < p < 2` (two dyadic grids + Marcinkiewicz interpolation of the
  weak-`(1,1)` bound with the `L²(ℓ²)` endpoint);
* `ell2HLMaxLpGtTwo` — the range `2 < p` (weighted Cotlar inequality + bootstrap).

The endpoint `p = 2` is not covered by either (both need a *strict* inequality), so it is proved
directly here: for `p = 2` the inequality is a plain sum of the *scalar* `L²` bounds of `hlMax`
(`hlMaxStrongTypeENNReal (q := 2)`), with no Fefferman--Stein loss.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

open Commons.Analysis.Maximal (hlMax measurable_hlMax)

namespace Work.BourgainPlan.Maximal

/-! ### The endpoint `p = 2` -/

/-- **The `ℓ²`-valued `hlMax` maximal inequality at `p = 2`.**  Since `(Σ_t (hlMax f_t)²)^{2/2} =
Σ_t (hlMax f_t)²` and `Σ_t ‖f_t‖ₑ² = ell2Sq f`, this is just the sum over `t` of the scalar `L²`
bound `∫ (hlMax ψ)² ≤ C² ∫ ψ²`. -/
theorem ell2HLMaxLp_two :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) →
      ∫⁻ x, (∑ t, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ ((2 : ℝ) / 2)
        ≤ ENNReal.ofReal (C ^ (2 : ℝ)) *
            ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Sq f x) ^ ((2 : ℝ) / 2) := by
  obtain ⟨C, hC, hb⟩ := hlMaxStrongTypeENNReal (q := 2) (by norm_num)
  refine ⟨C, hC, fun n f hf => ?_⟩
  have h2 : ((2 : ℝ) / 2) = (1 : ℝ) := by norm_num
  have hcomp : ∀ t : Fin n,
      Measurable fun x => (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ) :=
    fun t => (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp
      (measurable_hlMax _)
  have hsq : ∀ t : Fin n, Measurable fun x => ‖f t x‖ₑ ^ (2 : ℝ) :=
    fun t => (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp (hf t).enorm
  have hfin : ∀ t : Fin n, ∀ x, ‖f t x‖ₑ ≠ ⊤ := fun t x => by
    rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top
  calc ∫⁻ x, (∑ t, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^
          ((2 : ℝ) / 2)
      = ∫⁻ x, ∑ t : Fin n, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ) :=
        lintegral_congr fun x => by simp only [h2, ENNReal.rpow_one]
    _ = ∑ t : Fin n, ∫⁻ x, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ) :=
        lintegral_finsetSum _ (fun t _ => hcomp t)
    _ ≤ ∑ t : Fin n, ENNReal.ofReal (C ^ (2 : ℝ)) * ∫⁻ x, ‖f t x‖ₑ ^ (2 : ℝ) :=
        Finset.sum_le_sum fun t _ => hb _ (hf t).enorm (hfin t)
    _ = ENNReal.ofReal (C ^ (2 : ℝ)) *
          ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Sq f x) ^ ((2 : ℝ) / 2) := by
        rw [← Finset.mul_sum]
        congr 1
        refine ((lintegral_finsetSum _ (fun t _ => hsq t)).symm).trans ?_
        refine lintegral_congr fun x => ?_
        rw [h2, ENNReal.rpow_one]
        rfl

/-- **The `ℓ²`-valued Hardy--Littlewood maximal inequality on `L^p(ℓ²)` for all `1 < p < ∞`.**

`∫⁻ (Σ_t (hlMax ‖f_t‖)²)^{p/2} ≤ C^p ∫⁻ (Σ_t ‖f_t‖²)^{p/2}`, with `C` depending only on `p` (and
not on the number `n` of components), where `hlMax` is the centred Hardy--Littlewood maximal
function of the corpus. -/
theorem ell2HLMaxLp {p : ℝ} (hp : 1 < p) : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) → ∫⁻ x, (∑ t, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ (p / 2) ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Sq f x) ^ (p / 2) := by
  rcases lt_trichotomy p 2 with hlt | heq | hgt
  · exact ell2HLMaxLpLtTwo hp hlt
  · subst heq
    exact ell2HLMaxLp_two
  · exact ell2HLMaxLpGtTwo hgt

end Work.BourgainPlan.Maximal
