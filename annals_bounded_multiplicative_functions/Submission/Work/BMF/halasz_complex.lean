import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.halasz_basic
import Submission.Work.BMF.halasz_avg_bound
import Submission.Work.BMF.halasz_majm
import Submission.Work.BMF.halasz_final
import Submission.Work.BMF.halasz_casdiv
import Submission.Work.BMF.halasz_wsup_bound
import Submission.Work.BMF.halasz_sharp
import Submission.Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Halász's theorem (complex version), with the window `|t| ≤ 2T`

`‖Σ_{n ≤ x} f n‖ ≤ C x ((1 + M) e^{-M} + 1/√T)`,  `M = min_{|t| ≤ 2T} 𝔻(f, n ↦ n^{it}; x)²`,

for `f` multiplicative with `f 1 = 1` and `‖f n‖ ≤ 1`.

The proof is the Montgomery–Tenenbaum/Ramaré route, assembled from the pieces of this directory:

* `Work.BMF.halasz_casdiv` — Ramaré's `casdiv` bound (specialised to `r ≡ 1`), which controls
  `‖Mf f x‖` by `(x/log x)(∫ exp (Wsup f x α (T+1)) dα/α + e^Z/√T + e^Z/log x)`;
* `Work.BMF.halasz_wsup_bound` — the sharp and trivial pointwise bounds for `Wsup`;
* `Work.BMF.halasz_sharp` — the sharp Halász crossover integral
  `∫_{1/L}^{1} exp (g α) dα/α ≤ C e^{Z+C₁} (1+m) e^{-m}` (a strengthening, without the spurious
  additive `1`, of `Work.BMF.halasz_crossover`), together with the interval-integrability of the
  weight `α ↦ exp (Wsup f x α T)/α`;
* `Work.BMF.halasz_majm_of_pieces` — the assembly giving the "majm" bound
  `‖Mf f x‖ ≤ C x ((1+m)e^{-m} + 1/√T + 1/log x)`, `m = mHal f x (2T)`;
* `Work.BMF.halasz_final_reduction` — which absorbs the extra `1/log x` (using the averaging bound
  `Work.BMF.halasz_avg_bound`) and rewrites the infimum over `|t| ≤ 2T` of
  `𝔻 f (n ↦ n^{it}) x ^ 2` as `mHal f x (2T)` (using `Work.BMF.target_M_eq_mHal`), yielding the
  statement above.
-/

namespace Work.BMF

open Finset Real
open BoundedMultiplicativeFunctions

set_option maxHeartbeats 1000000

/-- The "majm" bound of Halász's theorem, instantiated from its pieces. -/
theorem halasz_majm :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x T : ℝ, 3 ≤ x → 2 ≤ T →
        ‖Mf f x‖ ≤ C₁ * x * ((1 + mHal f x (2 * T)) * Real.exp (-(mHal f x (2 * T))) +
          1 / Real.sqrt T + 1 / Real.log x) := by
  obtain ⟨Cs, hCspos, hws_s⟩ := halasz_wsup_bound.1
  obtain ⟨Ct, hCtpos, hws_t⟩ := halasz_wsup_bound.2
  refine halasz_majm_of_pieces halasz_casdiv
    ⟨max Cs Ct, lt_of_lt_of_le hCspos (le_max_left _ _), ?_, ?_⟩
    sharp_crossover wsup_intervalIntegrable
  · intro f hb x α T hx hT hα hα1
    have h := hws_s f hb x α T hx hT hα hα1
    have hle : Cs ≤ max Cs Ct := le_max_left _ _
    linarith
  · intro f hb x α T hx hT hα hα1
    have h := hws_t f hb x α T hx hT hα hα1
    have hle : Ct ≤ max Cs Ct := le_max_right _ _
    linarith

theorem halasz_complex :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ (x T : ℝ), 2 ≤ x → 1 ≤ T →
        let M : ℝ := ⨅ (t : {t : ℝ // |t| ≤ 2 * T}),
          BoundedMultiplicativeFunctions.𝔻 f (fun n ↦ (n : ℂ) ^ (Complex.I * t.1)) x ^ 2
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n‖ ≤ C * x * ((1 + M) * Real.exp (-M) + 1 / Real.sqrt T) := by
  obtain ⟨C₁, hC₁pos, hmajm⟩ := halasz_majm
  exact halasz_final_reduction C₁ hC₁pos hmajm

end Work.BMF
