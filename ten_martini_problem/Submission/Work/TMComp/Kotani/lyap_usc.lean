import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.Kotani.continuous_iterC_prod
import Submission.Work.TMComp.Kotani.det_iterC
import Submission.Work.TMComp.Kotani.frob_sqrt_two_le_of_det_one

/-!
# The Lyapunov exponent is nonnegative and upper semicontinuous (C8, Kotani)

The Lyapunov exponent is *defined* (AJ (2.2)--(2.5), `Work.TMContract.lyap`) as the infimum

`lyap α lam E = ⨅ n, (1/(n+1)) ∫₀¹ log ‖A_{n+1}(x; E)‖_F dx`

over the finite-scale averages `lyapAvg α lam n E`, which are functions of the complex energy `E`.

* **Nonnegativity.** Every transfer matrix `tmC lam E x` has determinant `1`
  (`Matrix.det_fin_two`), hence so does every iterate `iterC α lam E k x` (`det_iterC`),
  and a determinant-one `2 × 2` complex matrix has Frobenius norm at least `√2 > 1`
  (`frob_sqrt_two_le_of_det_one`, the AM–GM bound).  Therefore each integrand
  `log ‖A_{n+1}(x)‖_F` is nonnegative, each finite-scale average is nonnegative, and so is
  their infimum.

* **Upper semicontinuity in the energy.** For fixed `n` the finite-scale average `lyapAvg α lam n`
  is a continuous function of `E`: the map `(E, x) ↦ iterC α lam E k x` is jointly continuous
  (`continuous_iterC_prod`), `frob` is continuous, and `frob` never vanishes on the cocycle (it
  is `≥ √2`), so `log ∘ frob ∘ iterC` is jointly continuous; the parametric interval integral of
  a jointly continuous function is continuous (`continuous_parametric_intervalIntegral_of_continuous'`).
  An infimum of continuous functions is upper semicontinuous: given `ε > 0` choose `n` with
  `lyapAvg n E₀ < lyap E₀ + ε` (possible since `lyap E₀ = ⨅ₙ lyapAvg n E₀`), and on a neighbourhood
  of `E₀` continuity gives `lyapAvg n E < lyap E₀ + ε`, whence `lyap E ≤ lyapAvg n E < lyap E₀ + ε`.

Nothing is assumed about `α, λ` or `E₀`: both statements hold unconditionally.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace Work.TMComp.Kotani

open Work.TMContract

/-- The `n`-th finite-scale Lyapunov average `(1/(n+1)) ∫₀¹ log ‖A_{n+1}(x; E)‖_F dx`,
whose infimum over `n` is `Work.TMContract.lyap`. -/
def lyapAvg (α lam : ℝ) (n : ℕ) (E : ℂ) : ℝ :=
  (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E (n + 1) x))) / ((n : ℝ) + 1)

/-- `Work.TMContract.lyap` is *defined* as the infimum of the finite-scale averages. -/
theorem lyap_eq_iInf (α lam : ℝ) (E : ℂ) :
    Work.TMContract.lyap α lam E = ⨅ n : ℕ, lyapAvg α lam n E := rfl

/-! ## Continuity of `frob` and positivity on the cocycle -/

/-- `frob` is continuous (it is the square root of a sum of squares of the entries). -/
theorem continuous_frob :
    Continuous (fun A : Matrix (Fin 2) (Fin 2) ℂ => frob A) := by
  have h : (fun A : Matrix (Fin 2) (Fin 2) ℂ => frob A)
      = fun A => Real.sqrt (‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 + ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2) := rfl
  rw [h]
  fun_prop

/-- The transfer iterates have determinant one, hence Frobenius norm at least `√2 > 0`. -/
theorem frob_iterC_pos (α lam : ℝ) (E : ℂ) (k : ℕ) (x : ℝ) :
    0 < frob (iterC α lam E k x) := by
  have h2 : Real.sqrt 2 ≤ frob (iterC α lam E k x) :=
    frob_sqrt_two_le_of_det_one (det_iterC α lam E k x)
  have h3 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  linarith

/-- `(E, x) ↦ log ‖A_k(x; E)‖_F` is jointly continuous: the cocycle is jointly continuous,
`frob` is continuous and never vanishes on it. -/
theorem continuous_log_frob_iterC_prod (α lam : ℝ) (k : ℕ) :
    Continuous (fun p : ℂ × ℝ => Real.log (frob (iterC α lam p.1 k p.2))) :=
  (continuous_frob.comp (continuous_iterC_prod α lam k)).log
    (fun p => ne_of_gt (frob_iterC_pos α lam p.1 k p.2))

/-! ## The finite-scale averages are continuous and nonnegative -/

/-- For fixed `n` the finite-scale Lyapunov average is continuous in the energy. -/
theorem continuous_lyapAvg (α lam : ℝ) (n : ℕ) :
    Continuous (fun E : ℂ => lyapAvg α lam n E) := by
  have hjoint : Continuous (Function.uncurry
      (fun (E : ℂ) (x : ℝ) => Real.log (frob (iterC α lam E (n + 1) x)))) :=
    continuous_log_frob_iterC_prod α lam (n + 1)
  have hcomp := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hjoint (0 : ℝ) 1
  exact hcomp.div_const _

/-- Every finite-scale Lyapunov average is nonnegative: the integrand `log ‖A_{n+1}(x)‖_F`
is nonnegative because `‖A_{n+1}(x)‖_F ≥ √2 > 1`. -/
theorem lyapAvg_nonneg (α lam : ℝ) (E : ℂ) (n : ℕ) : 0 ≤ lyapAvg α lam n E := by
  refine div_nonneg ?_ (by positivity)
  refine intervalIntegral.integral_nonneg (by norm_num) ?_
  intro u _
  refine Real.log_nonneg ?_
  have hle : Real.sqrt 2 ≤ frob (iterC α lam E (n + 1) u) :=
    frob_sqrt_two_le_of_det_one (det_iterC α lam E (n + 1) u)
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  linarith

/-- The family of finite-scale averages is bounded below by `0`, so its infimum is well
behaved (`ciInf_le`). -/
theorem lyapAvg_bddBelow (α lam : ℝ) (E : ℂ) :
    BddBelow (Set.range fun n : ℕ => lyapAvg α lam n E) := by
  refine ⟨0, ?_⟩
  rintro y ⟨n, rfl⟩
  exact lyapAvg_nonneg α lam E n

/-! ## The Lyapunov exponent: nonnegativity and upper semicontinuity -/

theorem lyap_usc (α lam : ℝ) :
    (∀ E : ℂ, 0 ≤ Work.TMContract.lyap α lam E) ∧
    (∀ (E₀ : ℂ) (ε : ℝ), 0 < ε →
      ∀ᶠ E in nhds E₀, Work.TMContract.lyap α lam E < Work.TMContract.lyap α lam E₀ + ε) := by
  constructor
  · intro E
    have : 0 ≤ Work.TMContract.lyap α lam E := by
      rw [lyap_eq_iInf]
      exact le_ciInf fun n => lyapAvg_nonneg α lam E n
    exact this
  · intro E₀ ε hε
    -- Step 1: a scale `n` at which the finite average is already within `ε` of `lyap E₀`.
    obtain ⟨n, hn⟩ : ∃ n : ℕ, lyapAvg α lam n E₀ < Work.TMContract.lyap α lam E₀ + ε := by
      have hlt : (⨅ n : ℕ, lyapAvg α lam n E₀) < Work.TMContract.lyap α lam E₀ + ε := by
        rw [lyap_eq_iInf α lam E₀]
        linarith
      exact exists_lt_of_ciInf_lt hlt
    -- Step 2: continuity of that fixed average, and `lyap` as its infimum.
    filter_upwards [(continuous_lyapAvg α lam n).continuousAt.eventually (eventually_lt_nhds hn)]
      with E hE
    have hle : Work.TMContract.lyap α lam E ≤ lyapAvg α lam n E := by
      rw [lyap_eq_iInf]
      exact ciInf_le (lyapAvg_bddBelow α lam E) n
    exact lt_of_le_of_lt hle hE

end Work.TMComp.Kotani
