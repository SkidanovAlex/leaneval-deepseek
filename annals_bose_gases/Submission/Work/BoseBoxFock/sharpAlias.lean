import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.tauPhi_row
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sharpAlias` — the sharp-symbol aliasing inequality (the residual of
# `Work.BoseBoxFock.tauPhi_row`)

This file *pins down*, in checkable form, the single inequality to which the row
`Work.BoseBoxFock.tauPhi_row` (and its windowed form `Work.BoseBoxFock.tauPhiRowWindow`) reduces,
and which is therefore the mathematical heart of the target.

## Notation (all definitions below)

For `ℓ, c > 0`, `g : ℝ³ → ℂ`, with `k_n = kmomInt ℓ n = (2π/ℓ)·n`, `τ̃_c(r) = c²·tauPhi (r/c)`,
`C₀ = tauPhiC0 = ∫t²K` (`K = tauKer`):

* `deficit c r        = [r−c]₊² − τ̃_c(r) ≥ 0`               (the *profile deficit* `δ_c`),
* `contDeficit c g    = (2π)⁻³∫ δ_c(‖p‖)‖ĝ(p)‖² dp`          (`C(δ_c)`),
* `latDeficit ℓ c g   = Σ_n ℓ⁻³ δ_c(‖k_n‖)‖ĝ(k_n)‖²`         (`L(δ_c)`),
* `lowGain ℓ c g      = Σ_n ℓ⁻³ Θ_c(‖k_n‖)‖ĝ(k_n)‖² − (2π)⁻³∫ Θ_c(‖p‖)‖ĝ(p)‖²dp`,
  with `Θ_c(r) = [c−r]₊²`                                    (`ν(Θ_c)`, the *low-frequency lattice
  gain*),
* `slackAlias ℓ c g   = latSlack ℓ c g − contSlack c g`, where
  `slack c r = δ_c(r) − (c·r − (5/4+C₀)c²) ≥ 0` is the *window slack* (`Σ`, supported in
  frequency on `r ≤ 2c`, `Σ(0) = (5/4+C₀)c²`)                                 (`ν(Σ)`),
* `S1 = tauLatPow ℓ 1 g` (`L(‖·‖)`), `R1 = tauContPow 1 g` (`C(‖·‖)`), `D = R1 − S1`.

## The two statements

**(★) — the exact form of the row** (`sharpAliasRow`):

    latDeficit ℓ c g + lowGain ℓ c g  ≥  2·c·(R1 − S1) .

Using the two *proved* moment identities `L(1) = C(1)` (`frame_lattice_ball` +
`kinFT_plancherel`) and `L((·)²) = C((·)²)` (`moment2Lattice*`) together with the pointwise symbol
identities of `tauPhi_row.lean` (`rescaled_tauPhi_eq_tail`, `deficit_ge_linear`), (★) is
**equivalent** to the row (for every state of the row's class).

**(♦) — the "deficit pays the aliasing deficit" form** (`sharpAliasContDeficit`): the *continuum*
deficit pays three times the aliasing deficit,

    3·c·(R1 − S1)  ≤  contDeficit c g + slackAlias ℓ c g + lowGain ℓ c g .

(♦) is the form in which the *sharp symbols* are isolated: `contDeficit = C(δ_c)` is the payer,
`slackAlias = ν(Σ)` is the aliasing of the `C^∞`, compact-frequency-support symbol `Σ` (so it is
**provably tiny**: the Schwartz kernel decay at scale `1/c`), and `lowGain = ν(Θ_c)` is the
low-frequency gain that decides the spread regime.  The two forms are related by the *exact*
identity `C(δ_c) = latDeficit + c·D + lowGain + ν(ϑ)` (with `ϑ = τ̃_c − r² + 3cr − (9/4+C₀)c²`,
`ν(ϑ) = latAlias ϑ − contAlias ϑ`): (★) says `C(δ_c) + ν(ϑ) ≥ 3cD`, and (♦) says the same with
`ν(ϑ)` replaced by `slackAlias + lowGain − lowGain = …` — the difference is exactly the
(provably tiny) aliasing of the `C^∞` symbols `Σ` and `ϑ`.

## Acceptance test (recorded from the numerics of `FINDING_tauPhi_row.md` §3)

For the extremal family `g = e^{iq₀·x}·(R²−r²)⁶_+` (`ℓ = 1`, `c = 4π`, `q₀ = (kπ,kπ,kπ)`,
`‖q₀‖ ≫ c`) the *row* ratio is `→ 1` **from below** with the exact asymptotic

    ratio = 1 − c/‖q₀‖        (measured: ‖q₀‖ = 114, 136, 190, 245, 299 →
                               1 − ratio = .119, .0988, .0693, .0533, .0433; gap·‖q₀‖ ≈ 13.0 = c),

which is the *pointwise* ratio `τ̃_c(r)/F_c(r) = (r−3c/2)²/(r−c)² → 1 − c/r`.  So the inequality is
*sharp*: a proof may lose a fixed small factor in the spread regime but nothing in the
cancellation `(♦)`.  (Warning: for states of finite smoothness `L(τ̃_c)` converges only
conditionally — use `C^∞` states for numerics.)
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The **profile deficit** `δ_c(r) = [r−c]₊² − τ̃_c(r) ≥ 0` (`τ̃_c(r) = c²·tauPhi (r/c)`). -/
noncomputable def deficit (c r : ℝ) : ℝ := (max (r - c) 0) ^ 2 - c ^ 2 * tauPhi (r / c)

/-- The **window slack** `Σ(r) = δ_c(r) − (c·r − (5/4+C₀)c²) ≥ 0` (zero for `r ≥ 2c`). -/
noncomputable def slack (c r : ℝ) : ℝ := deficit c r - (c * r - (5 / 4 + tauPhiC0) * c ^ 2)

/-- The **low-frequency symbol** `Θ_c(r) = [c−r]₊²`. -/
noncomputable def thetaSym (c r : ℝ) : ℝ := (max (c - r) 0) ^ 2

/-- `C(δ_c)`: the continuum form of the profile deficit. -/
noncomputable def contDeficit (c : ℝ) (g : E3 → ℂ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, deficit c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- `L(δ_c)`: the lattice form of the profile deficit. -/
noncomputable def latDeficit (ℓ c : ℝ) (g : E3 → ℂ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * deficit c ‖kmomInt ℓ n‖
    * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2

/-- `ν(Θ_c) = L(Θ_c) − C(Θ_c)`: the **low-frequency lattice gain**. -/
noncomputable def lowGain (ℓ c : ℝ) (g : E3 → ℂ) : ℝ :=
  (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * thetaSym c ‖kmomInt ℓ n‖
      * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
    - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, thetaSym c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- `C(Σ)`: the continuum form of the window slack. -/
noncomputable def contSlack (c : ℝ) (g : E3 → ℂ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, slack c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2

/-- `L(Σ)`: the lattice form of the window slack. -/
noncomputable def latSlack (ℓ c : ℝ) (g : E3 → ℂ) : ℝ :=
  ∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * slack c ‖kmomInt ℓ n‖
    * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2

/-- `ν(Σ) = L(Σ) − C(Σ)`: (provably tiny) aliasing of the `C^∞`, compact-frequency-support
symbol `Σ`. -/
noncomputable def slackAlias (ℓ c : ℝ) (g : E3 → ℂ) : ℝ := latSlack ℓ c g - contSlack c g

/-! ## The pointwise calculus of `δ_c` and `Σ` (the bricks of the reduction)

These are the symbol-level facts that turn the *row* into `(★)`: `δ_c ≥ 0` (the deficit is a
credit), `δ_c = c·r − (5/4+C₀)c²` in the tail `r ≥ 2c` (`Σ = 0` there), `δ_c = 0` below `c`, and
the linear lower bound `δ_c(r) ≥ c·r − (5/4+C₀)c²` which is what makes `Σ ≥ 0`. -/

/-- The profile deficit is nonnegative: `τ̃_c ≤ [·−c]₊²` (`rescaled_tauPhi_le_sharp`). -/
lemma deficit_nonneg {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) : 0 ≤ deficit c r := by
  have h := rescaled_tauPhi_le_sharp hc hr
  have hfs : Submission.BoseGases.fsKinCoeff c r = (max (r - c) 0) ^ 2 := rfl
  rw [hfs] at h
  exact sub_nonneg.mpr h

/-- In the tail `r ≥ 2c` the deficit is *exactly* its linear expression. -/
lemma deficit_eq_tail {c r : ℝ} (hc : 0 < c) (hr : 2 * c ≤ r) :
    deficit c r = c * r - (5 / 4 + tauPhiC0) * c ^ 2 := by
  have h := rescaled_tauPhi_eq_tail hc hr
  have hmax : (max (r - c) 0) ^ 2 = (r - c) ^ 2 := by
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ r - c)]
  rw [deficit, hmax, h]
  ring

/-- Below the threshold the profile vanishes, so the deficit vanishes as well. -/
lemma deficit_eq_zero_of_le {c r : ℝ} (hc : 0 < c) (hr : r ≤ c) : deficit c r = 0 := by
  have hz : tauPhi (r / c) = 0 :=
    tauPhi_zero_of_le_one (r / c) (by rw [div_le_one hc]; exact hr)
  have hmax : (max (r - c) 0) ^ 2 = 0 := by
    rw [max_eq_right (by linarith : r - c ≤ 0)]; ring
  rw [deficit, hz, mul_zero, hmax, sub_zero]

/-- The linear lower bound for the deficit (`deficit_ge_linear` in the `deficit` vocabulary). -/
lemma deficit_ge_linear' {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    c * r - (5 / 4 + tauPhiC0) * c ^ 2 ≤ deficit c r := by
  have h := deficit_ge_linear hc hr
  have hfs : Submission.BoseGases.fsKinCoeff c r = (max (r - c) 0) ^ 2 := rfl
  rw [hfs] at h
  exact h

/-- The window slack is nonnegative. -/
lemma slack_nonneg {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) : 0 ≤ slack c r := by
  have h := deficit_ge_linear' hc hr
  rw [slack]
  linarith

/-- The window slack vanishes in the tail `r ≥ 2c`. -/
lemma slack_eq_zero_of_two_mul_le {c r : ℝ} (hc : 0 < c) (hr : 2 * c ≤ r) :
    slack c r = 0 := by
  rw [slack, deficit_eq_tail hc hr, sub_self]

/-- The lattice form of the deficit is nonnegative (it is a sum of nonnegative terms). -/
lemma latDeficit_nonneg {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (g : E3 → ℂ) :
    0 ≤ latDeficit ℓ c g := by
  rw [latDeficit]
  refine tsum_nonneg fun n => ?_
  have hδ : 0 ≤ deficit c ‖kmomInt ℓ n‖ := deficit_nonneg hc (norm_nonneg _)
  have hℓ3 : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹ := by positivity
  have : (0 : ℝ) ≤ ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := sq_nonneg _
  positivity

/-- The lattice form of the window slack is nonnegative. -/
lemma latSlack_nonneg {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (g : E3 → ℂ) :
    0 ≤ latSlack ℓ c g := by
  rw [latSlack]
  refine tsum_nonneg fun n => ?_
  have hSl : 0 ≤ slack c ‖kmomInt ℓ n‖ := slack_nonneg hc (norm_nonneg _)
  have hℓ3 : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹ := by positivity
  have : (0 : ℝ) ≤ ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2 := sq_nonneg _
  positivity

/-- The continuum form of the deficit is nonnegative. -/
lemma contDeficit_nonneg {c : ℝ} (hc : 0 < c) (g : E3 → ℂ) : 0 ≤ contDeficit c g := by
  rw [contDeficit]
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro p
  have hδ : 0 ≤ deficit c ‖p‖ := deficit_nonneg hc (norm_nonneg _)
  positivity

/-- The continuum form of the window slack is nonnegative. -/
lemma contSlack_nonneg {c : ℝ} (hc : 0 < c) (g : E3 → ℂ) : 0 ≤ contSlack c g := by
  rw [contSlack]
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro p
  have hSl : 0 ≤ slack c ‖p‖ := slack_nonneg hc (norm_nonneg _)
  positivity

/-- **(★) The sharp-symbol aliasing inequality, exact form.**  The profile deficit (lattice side)
together with the low-frequency lattice gain pays twice the aliasing deficit of the first moment.
This is *equivalent* to the row `Work.BoseBoxFock.tauPhi_row` (see the module docstring). -/
theorem sharpAliasRow {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (hcℓ : 4 * Real.pi ≤ c * ℓ)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2)) :
    2 * c * (tauContPow 1 g - tauLatPow ℓ 1 g) ≤ latDeficit ℓ c g + lowGain ℓ c g := by
  sorry

/-- **(♦) The "deficit pays the aliasing deficit" form**: the *continuum* deficit `C(δ_c)` pays
three times the aliasing deficit `3cD`, up to the (provably tiny) aliasing of the `C^∞`
compact-frequency-support symbols (`slackAlias = ν(Σ)` and `lowGain = ν(Θ_c)`). -/
theorem sharpAliasContDeficit {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (hcℓ : 4 * Real.pi ≤ c * ℓ)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    (hgsupp : tsupport g ⊆ Metric.ball 0 (ℓ / 2)) :
    3 * c * (tauContPow 1 g - tauLatPow ℓ 1 g)
      ≤ contDeficit c g + slackAlias ℓ c g + lowGain ℓ c g := by
  sorry

end Work.BoseBoxFock
