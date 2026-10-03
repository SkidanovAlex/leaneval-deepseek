/-
# The low case (`CaseRest`) of area A6: vocabulary and the scale split

Area **A6** of the KMT contract (`Submission/Work/KMTContract/Areas.lean`) is Krause--Mirek--Tao's
Theorem `varp` at `(p₁,p₂,p) = (2,2,1)` with the exponential gain `2^{-c·L}`,
`L = max(max l₁ l₂)(max k₁ k₂)`.  `Work.KMTPlan.Model` splits the quadruples `(l₁,l₂,k₁,k₂)` into
the *high-high* case `CaseHH` (`k₁,k₂ ≥ 1`) and its complement `CaseRest` (`k₁ = 0 ∨ k₂ = 0`); the
present module is the vocabulary of the **low case** `CaseRest`.

In the paper's §5 notation, with the contract's bottom scale `u = 0`, the quadruple index
`(l₁,l₂,k₁,k₂)` stands for the pieces `F^{0,l₁,k₁}_N f`, `G^{0,l₂,k₂}_N g`, and `CaseRest` is the
case `s₁ = -u` or `s₂ = -u`: one of the two pieces is the *bottom* piece
`Π_{l,≤-Log N} f` (a single projection, not a Littlewood--Paley difference).  The paper
(Krause--Mirek--Tao, §6, Theorem `model-est`) treats this case by the model-operator analysis
(§6 `mod-approx`, §7 small scales, §8 large scales), while the high-high case is Proposition
`high-high-l2`.

Following the paper's §6, the scale set `I^{l,k₁,k₂}` is split at `2^{2^u}`, `u = ⌊C₂2^{2ρL}⌋`
(`C₂ = 1`, `Work.KMTAreas.A7.splitCut`), into

* `colSmall` — the columns clamped to the *small* scales `N ≤ splitCut ρ L`;
* `colLarge` — the columns clamped to the *large* scales `N > splitCut ρ L`.

The two halves of the low case are then the two `Prop`s `LcSmall` and `LcLarge`: on the small
scales one may use the two-dimensional Rademacher--Menshov inequality (`rm-bil`) together with
the single-scale estimate `ssu` (which is `mod-approx` run backwards at `N = 2^u` plus
`improv`), on the large scales the quantitative Shannon sampling theorem together with the
arithmetic bilinear estimate `bile` and the vector-valued Lépingle inequality.  Their assembly is
the proof of `Work.KMTPlan.A6.lowCase`.

Everything in this module is definitional; no proof is postulated.
-/
import Submission.Work.KMTPlan.Model
import Submission.Work.KMTAreas.A7.Large.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTContract

/-- **The scale `L = max(max l₁ l₂)(max k₁ k₂)` of the gain.** -/
def lcL (l₁ l₂ k₁ k₂ : ℕ) : ℕ := max (max l₁ l₂) (max k₁ k₂)

/-- `lcL` is the `ℕ`-valued version of the maximum entering the contract's weight
`2^{-c·max(max l₁ l₂)(max k₁ k₂)}`. -/
theorem lcL_eq (l₁ l₂ k₁ k₂ : ℕ) :
    (lcL l₁ l₂ k₁ k₂ : ℤ) = lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
  rw [lcL, lmax]
  push_cast
  ring

/-- **The weight `2^{-c·L}` of the low case**, `L = max(max l₁ l₂)(max k₁ k₂)`. -/
noncomputable def lcWeight (c : ℝ) (l₁ l₂ k₁ k₂ : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(c * (lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ)))

theorem lcWeight_nonneg (c : ℝ) (l₁ l₂ k₁ k₂ : ℕ) : 0 ≤ lcWeight c l₁ l₂ k₁ k₂ :=
  Real.rpow_nonneg (by norm_num) _

/-- The weight is antitone in `c`: a larger rate gives a smaller weight. -/
theorem lcWeight_le_of_le {c c' : ℝ} (hc : c ≤ c') (l₁ l₂ k₁ k₂ : ℕ) :
    lcWeight c' l₁ l₂ k₁ k₂ ≤ lcWeight c l₁ l₂ k₁ k₂ := by
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hL : (0 : ℝ) ≤ (lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
      rw [lmax]
      exact le_trans (Int.natCast_nonneg l₁)
        (le_trans (le_max_left _ _) (le_max_left _ _))
    exact_mod_cast this
  nlinarith

/-- **The columns clamped to the small scales** `N ≤ splitCut ρ L`: this is the family whose
variational norm is controlled by the Rademacher--Menshov / single-scale analysis of §7. -/
noncomputable def colSmall (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if Nat.floor (a n) ≤ Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) then
      varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x
    else 0

/-- **The columns clamped to the large scales** `N > splitCut ρ L`: the family whose variational
norm is controlled by the sampling/`bile` analysis of §8. -/
noncomputable def colLarge (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) < Nat.floor (a n) then
      varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x
    else 0

theorem colSmall_apply (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ) (x : ℤ) :
    colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x =
      if Nat.floor (a n) ≤ Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) then
        varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x
      else 0 := rfl

theorem colLarge_apply (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ) (x : ℤ) :
    colLarge ρ P C₀ a f g l₁ l₂ k₁ k₂ n x =
      if Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) < Nat.floor (a n) then
        varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x
      else 0 := rfl

/-- The two clamped families sum to the full column family. -/
theorem colSmall_add_colLarge (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) :
    colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ + colLarge ρ P C₀ a f g l₁ l₂ k₁ k₂
      = varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ := by
  funext n x
  show colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      + colLarge ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
    = varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x
  rw [colSmall_apply, colLarge_apply]
  by_cases h : Nat.floor (a n) ≤ Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂)
  · rw [if_pos h, if_neg (not_lt.mpr h), add_zero]
  · rw [if_neg h, if_pos (not_le.mp h), zero_add]

/-- **The small-scale half of the low case.**  See the module docstring. -/
def LcSmall (P : ℤ[X]) (r : ℝ≥0) (C₀ : ℕ) : Prop :=
  1 ≤ C₀ → ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
    ∃ C : ℝ≥0 → ℝ≥0,
      ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) → (k₁ = 0 ∨ k₂ = 0) →
        eLpNorm (fun x : ℤ =>
            variationalNorm r (fun n : ℕ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 Measure.count
          ≤ (C Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂) *
              eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count

/-- **The large-scale half of the low case.**  See the module docstring. -/
def LcLarge (P : ℤ[X]) (r : ℝ≥0) (C₀ : ℕ) : Prop :=
  1 ≤ C₀ → ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
    ∃ C : ℝ≥0 → ℝ≥0,
      ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) → (k₁ = 0 ∨ k₂ = 0) →
        eLpNorm (fun x : ℤ =>
            variationalNorm r (fun n : ℕ => colLarge ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 Measure.count
          ≤ (C Λ : ℝ≥0∞) * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂) *
              eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count

end

end Work.KMTPlan.A6
