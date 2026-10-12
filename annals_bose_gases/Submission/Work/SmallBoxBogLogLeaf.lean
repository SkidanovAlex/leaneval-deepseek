import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import ChallengeDeps
import Submission.Work.SmallBoxBogMainTerm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-260 part 10 — the `|p| < a⁻¹` complementary log shell (skeleton +
first certified leaf)

FS lm:appbogolubov's refined bound (eq:refinedaprioribog) splits
`∫_{|p|>2c} ℬ²/𝒜` at the scale `|p| = a⁻¹`: the `|p| ≥ a⁻¹`-part is the
`(1+C·(dsℓ)⁻¹a)`-prefactor (committed, `SmallBoxBogLatticeFactor` +
`SmallBoxBogMainTerm`); the complementary `|p| ∈ (2c, a⁻¹)`-part is
log-divergent and, cut by `|Ŵ₁(p)| ≤ C₀·a` (FS eq:WSestimate), gives the
bracket's `(av)²·c0·ln((c0·(av))⁻¹)`-term.  This module starts that piece:

  * **`momentum_shell_inv_cube_reduce` (PROVEN)** — the closed-shell radial
    reduction `∫_{A ≤ ‖p‖ ≤ B} ‖p‖⁻³ = 4π·∫_{r ∈ Icc A B} r⁻¹` (via the
    corpus `MeanValue.integral_annulus_radial`, `0 < A ≤ B`);
  * **`interval_Icc_inv_log` (PROVEN)** — the 1-D FTC leaf
    `∫_{r ∈ Icc A B} r⁻¹ = ln B − ln A` (set-integral over `Icc` = over
    `Ioc` up to the measure-zero endpoint `A` —
    `MeasureTheory.ae_iff` + `Real.volume_singleton`; then
    `intervalIntegral.integral_of_le` (note: it is the `Ioc` form) +
    `intervalIntegral.integral_deriv_eq_sub` with `f := Real.log`,
    `Real.deriv_log`, `Real.differentiableAt_log_iff`);
  * **`momentum_log_shell_value` (PROVEN)** — the shell value
    `4π(ln B − ln A)`;
  * **`momentum_shell_log_bound` / `momentum_shell_log_bound_ln` (PROVEN)** —
    `∫_{2c0 ≤ ‖p‖ ≤ a⁻¹} c0·‖p‖⁻³ = 4π·c0·ln((2c0·a)⁻¹)` for `2c0·a ≤ 1`
    (via `log_collapse`, `Real.log_inv` + `Real.log_mul`), the FS-shape
    complementary bound `ln(dsℓ/a)`-form.

Per the design-note Session-260 part 7, the `(av)c0³`- and `(av)⁴c0⁻³`-
bracket terms come from `momentum_ball_integral_one` (`∫_{‖p‖<2c0}1`) and
the commons `eucl_ball_exterior_pow_six` (`∫_{‖p‖≥2c0}‖p‖⁻⁶`); the per-mode
Fock2Mode instantiation attaches only after these momentum leaves are solid.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
namespace Submission
open _root_.BoseGases
namespace BoseGases
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma momentum_shell_inv_cube_reduce {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    (∫ p : ℝ³ in {p : ℝ³ | A ≤ ‖p‖ ∧ ‖p‖ ≤ B}, (‖p‖ ^ 3)⁻¹)
      = 4 * π * (∫ r in Set.Icc A B, r⁻¹) := by
  have hred := integral_annulus_radial (a := A) (b := B) hA hAB (G := fun r : ℝ => (r ^ 3)⁻¹)
  calc
    (∫ p : ℝ³ in {p : ℝ³ | A ≤ ‖p‖ ∧ ‖p‖ ≤ B}, (‖p‖ ^ 3)⁻¹)
        = 4 * π * (∫ r in Set.Icc A B, r ^ 2 * (r ^ 3)⁻¹) := hred
    _ = 4 * π * (∫ r in Set.Icc A B, r⁻¹) := by
          congr 1
          have hmem : ∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Icc A B)),
              r ∈ Set.Icc A B := MeasureTheory.ae_restrict_mem measurableSet_Icc
          apply integral_congr_ae
          filter_upwards [hmem] with r hr
          have hpos : 0 < r := lt_of_lt_of_le hA hr.1
          field_simp [ne_of_gt hpos]

/-- the 1-D FTC leaf: `∫_{r ∈ Icc A B} r⁻¹ = ln B − ln A` for `0 < A ≤ B`
(set integral over `Icc` = over `Ioc` up to the measure-zero endpoint `A`,
then `intervalIntegral.integral_deriv_eq_sub` with `f := Real.log`). -/
lemma interval_Icc_inv_log {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    (∫ r in Set.Icc A B, r⁻¹) = Real.log B - Real.log A := by
  let f : ℝ → ℝ := fun x => x⁻¹
  -- step 0: ∫ over Icc = ∫ over Ioc (they differ only at the endpoint A, measure zero)
  have hae_ne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ A := by
    rw [MeasureTheory.ae_iff]
    have hset : {r : ℝ | ¬ r ≠ A} = ({A} : Set ℝ) := by
      ext r
      by_cases h : r = A <;> simp [h]
    rw [hset]
    exact Real.volume_singleton (a := A)
  have hpt : ∀ᵐ r ∂(volume : Measure ℝ),
      (Set.Icc A B).indicator f r = (Set.Ioc A B).indicator f r := by
    filter_upwards [hae_ne] with r hr
    have hne : r ≠ A := hr
    have hiff : r ∈ Set.Icc A B ↔ r ∈ Set.Ioc A B := by
      constructor
      · intro h
        exact ⟨lt_of_le_of_ne h.1 (Ne.symm hne), h.2⟩
      · intro h
        exact ⟨le_of_lt h.1, h.2⟩
    by_cases hIn : r ∈ Set.Icc A B
    · have hIn2 : r ∈ Set.Ioc A B := hiff.mp hIn
      simp [hIn, hIn2]
    · have hIn2 : r ∉ Set.Ioc A B := fun h => hIn (hiff.mpr h)
      simp [hIn, hIn2]
  have hIccIoc : (∫ r in Set.Icc A B, f r) = ∫ r in Set.Ioc A B, f r := by
    calc
      (∫ r in Set.Icc A B, f r) = ∫ r, (Set.Icc A B).indicator f r := by
            rw [← integral_indicator (s := Set.Icc A B) (f := f) (μ := (volume : Measure ℝ)) measurableSet_Icc]
      _ = ∫ r, (Set.Ioc A B).indicator f r := by
            exact integral_congr_ae hpt
      _ = ∫ r in Set.Ioc A B, f r := by
            rw [integral_indicator (s := Set.Ioc A B) (f := f) (μ := (volume : Measure ℝ)) measurableSet_Ioc]
  -- step 1: interval integral ∫ A..B = ∫ over Ioc A B  (integral_of_le)
  have hIntIoc : (∫ r in A..B, f r) = ∫ r in Set.Ioc A B, f r := by
    simpa [f] using (intervalIntegral.integral_of_le hAB)
  -- step 2: FTC: ∫ A..B (deriv log) = log B − log A
  have hderiv : ∀ x ∈ Set.uIcc A B, DifferentiableAt ℝ Real.log x := by
    intro x hx
    have hxI : x ∈ Set.Icc A B := by simpa [Set.uIcc_of_le hAB] using hx
    exact (Real.differentiableAt_log_iff).2 (ne_of_gt (lt_of_lt_of_le hA hxI.1))
  have hcont : ContinuousOn (fun y : ℝ => y⁻¹) (Set.uIcc A B) := by
    refine ContinuousOn.inv₀ continuous_id.continuousOn ?_
    intro y hy
    have hyI : y ∈ Set.Icc A B := by simpa [Set.uIcc_of_le hAB] using hy
    exact ne_of_gt (lt_of_lt_of_le hA hyI.1)
  have hcontD : ContinuousOn (deriv Real.log) (Set.uIcc A B) := by
    refine hcont.congr ?_
    intro y hy
    exact Real.deriv_log y
  have hint : IntervalIntegrable (deriv Real.log) volume A B := hcontD.intervalIntegrable
  have hftc : (∫ y in A..B, deriv Real.log y) = Real.log B - Real.log A :=
    intervalIntegral.integral_deriv_eq_sub (f := Real.log) hderiv hint
  have hder : (fun y : ℝ => deriv Real.log y) = f := by
    funext y
    exact Real.deriv_log y
  have hFTC : (∫ y in A..B, f y) = Real.log B - Real.log A := by
    simpa [hder] using hftc
  -- assemble
  calc
    (∫ r in Set.Icc A B, r⁻¹) = ∫ r in Set.Icc A B, f r := by rfl
    _ = ∫ r in Set.Ioc A B, f r := hIccIoc
    _ = (∫ r in A..B, f r) := hIntIoc.symm
    _ = Real.log B - Real.log A := hFTC


/-- **the log-shell value (PROVEN)**: for `0 < A ≤ B` the closed shell
integral of `‖p‖⁻³` equals `4π·(ln B − ln A)`. -/
lemma momentum_log_shell_value {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hAB : A ≤ B) :
    (∫ p : ℝ³ in {p : ℝ³ | A ≤ ‖p‖ ∧ ‖p‖ ≤ B}, (‖p‖ ^ 3)⁻¹)
      = 4 * Real.pi * (Real.log B - Real.log A) := by
  calc
    (∫ p : ℝ³ in {p : ℝ³ | A ≤ ‖p‖ ∧ ‖p‖ ≤ B}, (‖p‖ ^ 3)⁻¹)
        = 4 * Real.pi * (∫ r in Set.Icc A B, r⁻¹) := momentum_shell_inv_cube_reduce hA hAB
    _ = 4 * Real.pi * (Real.log B - Real.log A) := by
          congr 1
          exact interval_Icc_inv_log hA hAB

/-- **the `|p| < a⁻¹` complementary shell bound (PROVEN)**: with the split
scale `a` and `2c0 ≤ a⁻¹` (so `2c0·a ≤ 1`), the `c0·‖p‖⁻³`-integral over the
shell `2c0 ≤ ‖p‖ ≤ a⁻¹` equals `4π·c0·(ln(a⁻¹) − ln(2c0))` — the momentum
leaf of FS lm:appbogolubov's log-error group (times `(C₀·(av))²` and the
mode-count factors at the per-mode Fock assembly it yields the bracket's
`(av)²c0·ln((c0·(av))⁻¹)`-term, the `2`-and-`C₀` constants absorbed). -/
lemma momentum_shell_log_bound (c0 : ℝ) (hc0 : 0 < c0) (a : ℝ) (ha : 0 < a)
    (hreg : 2 * c0 * a ≤ 1) :
    (∫ p : ℝ³ in {p : ℝ³ | 2 * c0 ≤ ‖p‖ ∧ ‖p‖ ≤ a⁻¹}, c0 * (‖p‖ ^ 3)⁻¹)
      = 4 * Real.pi * c0 * (Real.log (a⁻¹) - Real.log (2 * c0)) := by
  have hB : 0 < a⁻¹ := inv_pos.mpr ha
  have hAB : 2 * c0 ≤ a⁻¹ := by
    -- 2 c0 ≤ a⁻¹ = 1/a ⟺ (multiply a > 0) 2 c0 a ≤ 1
    simpa [one_div] using (le_div_iff₀ ha).mpr hreg
  have hval := momentum_log_shell_value (A := 2 * c0) (B := a⁻¹) (by positivity : 0 < 2 * c0) hB hAB
  calc
    (∫ p : ℝ³ in {p : ℝ³ | 2 * c0 ≤ ‖p‖ ∧ ‖p‖ ≤ a⁻¹}, c0 * (‖p‖ ^ 3)⁻¹)
        = c0 * (∫ p : ℝ³ in {p : ℝ³ | 2 * c0 ≤ ‖p‖ ∧ ‖p‖ ≤ a⁻¹}, (‖p‖ ^ 3)⁻¹) := by
            rw [integral_const_mul]
    _ = c0 * (4 * Real.pi * (Real.log (a⁻¹) - Real.log (2 * c0))) := by rw [hval]
    _ = 4 * Real.pi * c0 * (Real.log (a⁻¹) - Real.log (2 * c0)) := by ring

/-- the log-collapse identity `ln(a⁻¹) − ln(2c) = ln((2ca)⁻¹)` (positive
`a, c`), used to reach the FS `ln(dsℓ/a)`-form. -/
lemma log_collapse {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Real.log (a⁻¹) - Real.log (2 * c) = Real.log ((2 * c * a)⁻¹) := by
  have h1 : Real.log (a⁻¹) = -Real.log a := Real.log_inv a
  have h2 : Real.log ((2 * c * a)⁻¹) = -Real.log (2 * c * a) := Real.log_inv (2 * c * a)
  have h3 : Real.log (2 * c * a) = Real.log (2 * c) + Real.log a := by
    have hc0 : 2 * c ≠ 0 := by positivity
    have ha0 : a ≠ 0 := ne_of_gt ha
    exact Real.log_mul hc0 ha0
  rw [h1, h2, h3]
  ring

/-- **the `|p| < a⁻¹` complementary shell bound in FS-ln form (PROVEN)**:
`∫_{2c0 ≤ ‖p‖ ≤ a⁻¹} c0·‖p‖⁻³ = 4π·c0·ln((2c0·a)⁻¹)` for `2c0·a ≤ 1`
(the momentum leaf of FS lm:appbogolubov's log-error group, `ln(dsℓ/a)`-form
with the universal `2`; times `(C₀·(av))²` and the mode-count factors at
the per-mode Fock assembly it yields the bracket's
`(av)²c0·ln((c0·(av))⁻¹)·((N̂+1)N̂)/s³`-term). -/
lemma momentum_shell_log_bound_ln (c0 : ℝ) (hc0 : 0 < c0) (a : ℝ) (ha : 0 < a)
    (hreg : 2 * c0 * a ≤ 1) :
    (∫ p : ℝ³ in {p : ℝ³ | 2 * c0 ≤ ‖p‖ ∧ ‖p‖ ≤ a⁻¹}, c0 * (‖p‖ ^ 3)⁻¹)
      = 4 * Real.pi * c0 * Real.log ((2 * c0 * a)⁻¹) := by
  have hb := momentum_shell_log_bound c0 hc0 a ha hreg
  calc
    (∫ p : ℝ³ in {p : ℝ³ | 2 * c0 ≤ ‖p‖ ∧ ‖p‖ ≤ a⁻¹}, c0 * (‖p‖ ^ 3)⁻¹)
        = 4 * Real.pi * c0 * (Real.log (a⁻¹) - Real.log (2 * c0)) := hb
    _ = 4 * Real.pi * c0 * Real.log ((2 * c0 * a)⁻¹) := by
          congr 1
          exact log_collapse ha hc0

end BoseGases
end Submission
