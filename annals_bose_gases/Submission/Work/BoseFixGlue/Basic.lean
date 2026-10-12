import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBoxFix.Defs
import Submission.Work.BoseKinLoc.Compare.compare_box_energy_v2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Basic` — the glue chapter for the corrected BoseBox nodes

Subproject `Submission/Work/BoseFixGlue/` (area lead: `curric-46`'s BoseFix glue deliverable,
2026-10-03).  The frozen vocabulary is `Work.BoseBoxFix.Defs` (do not edit): the box-restricted
word `wordB`, its norm `normB`, the low class `IsLowB`, the box bound `BoxBoundB`, the
admissibility predicate `Adm`, the box theorem `LHYBoxB` and the four nodes `NodeB1B`,
`B2AprioriWindowB`, `B2GradingDataB`, `NodeB2gB`, `NodeRestrictedB`.

This module fixes the *parameter abbreviations* used throughout the glue chapter (they keep the
long `(paramsAt μ (a v)).d` expressions out of the statements) and provides the elementary
`wordB`/`normB` API plus the threshold arithmetic that the wiring needs.

## The two glue targets of the chapter

* the **ports** of the proved BoseBox chapter into the frozen vocabulary:
  `nodeB2gB_of_data`, `B2AprioriWindowB_of_NodeB1B`, `nodeB0B_dichotomy`,
  `LHYBoxB_of_grading`;
* the **wiring** `HBoxGSymStateScaled_of_LHYBoxB`, from an `LHYBoxB` box theorem (plus the
  fibre/kinetic inputs of FS §3 localisation) to `Work.BoseTop.HBoxGSymStateScaled`, the
  handoff consumed by the proved `Work.BoseTop.theorem_1_2_of_HBoxGSymStateScaled`.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixGlue

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The FS parameter block at `(μ, a v)`, projected

These are definitional abbreviations (all `rfl-`unfolding to `paramsAt`/`sideAt`); they make the
statements below readable and pin the convention: the diluteness is `μ * (a v)^3`, the box side is
`sideAt μ (a v) = K_ℓ (μ a)^{-1/2}` (`Work.BoseBox.sideAt`), and `dB, sB, eTB, bB` are FS's
`d = X⁶`, `s = X`, `ε_T = X^{23/4}`, `b = 1/16` read off `paramsAt μ (a v)`. -/

/-- The box side `ℓ(μ) = K_ℓ (μ a v)^{-1/2}` (FS `sec:params`). -/
def ℓB (v : ℝ³ → ℝ) (μ : ℝ) : ℝ := sideAt μ (a v)

/-- FS's `d = X⁶` at the chemical potential `μ`. -/
def dB (v : ℝ³ → ℝ) (μ : ℝ) : ℝ := (paramsAt μ (a v)).d

/-- FS's `s = X` at the chemical potential `μ`. -/
def sB (v : ℝ³ → ℝ) (μ : ℝ) : ℝ := (paramsAt μ (a v)).s

/-- FS's `ε_T = X^{23/4}` at the chemical potential `μ`. -/
def eTB (v : ℝ³ → ℝ) (μ : ℝ) : ℝ := (paramsAt μ (a v)).eT

/-- FS's gap coefficient `b = bValue` at the chemical potential `μ`. -/
def bB (v : ℝ³ → ℝ) (μ : ℝ) : ℝ := (paramsAt μ (a v)).b

@[simp] lemma ℓB_def (v : ℝ³ → ℝ) (μ : ℝ) : ℓB v μ = sideAt μ (a v) := rfl
@[simp] lemma dB_def (v : ℝ³ → ℝ) (μ : ℝ) : dB v μ = (paramsAt μ (a v)).d := rfl
@[simp] lemma sB_def (v : ℝ³ → ℝ) (μ : ℝ) : sB v μ = (paramsAt μ (a v)).s := rfl
@[simp] lemma eTB_def (v : ℝ³ → ℝ) (μ : ℝ) : eTB v μ = (paramsAt μ (a v)).eT := rfl
@[simp] lemma bB_def (v : ℝ³ → ℝ) (μ : ℝ) : bB v μ = (paramsAt μ (a v)).b := rfl

/-- FS's parameters at FS's own choice: `b = bValue = 1/16` identically. -/
@[simp] lemma bB_eq_bValue (v : ℝ³ → ℝ) (μ : ℝ) : bB v μ = bValue := rfl

/-- The centre of the corner box `[0,L]³`: the vector `(L/2, L/2, L/2)`.  The cell shift by it,
`cellShift N (cubeC L)`, maps the corner box `box N L` onto the centred box `abox N L`, which is
how a state of the corpus' corner box is handed to the centred-box localisation comparison
`Work.BoseKinLoc.Compare.compare_box_energy_v2`. -/
def cubeC (L : ℝ) : ℝ³ := WithLp.toLp 2 (fun _ : Fin 3 => L / 2)

/-- The FS box word `wordB` is the box-restricted form `boxFormB` at the projected parameters. -/
lemma wordB_eq (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (Φ : X n → ℝ) :
    wordB v h μ n Φ
      = boxFormB n v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ) Φ := rfl

/-- The FS norm square `normB` is the centred-box `L²` norm of BoseKinLoc. -/
lemma normB_eq (v : ℝ³ → ℝ) (μ : ℝ) (n : ℕ) (Φ : X n → ℝ) :
    normB v μ n Φ = sqNormB n (ℓB v μ) Φ := rfl

/-! ## 2. Elementary `normB` API -/

lemma normB_nonneg (v : ℝ³ → ℝ) (μ : ℝ) (n : ℕ) (Φ : X n → ℝ) : 0 ≤ normB v μ n Φ := by
  rw [normB_eq, sqNormB]
  exact integral_nonneg (fun x => sq_nonneg _)

lemma normB_pos_of_pos {v : ℝ³ → ℝ} {μ : ℝ} {n : ℕ} {Φ : X n → ℝ}
    (h : 0 < normB v μ n Φ) : 0 < normB v μ n Φ := h

/-- The type of smooth symmetric box states is nonempty (the constant state; no support
condition is imposed on `BoxState`).  This is what the `iInf` API over `BoxState` consumes. -/
instance instNonemptyBoxState (n : ℕ) (ℓ : ℝ) : Nonempty (BoxState n ℓ) :=
  ⟨⟨fun _ => 1, contDiff_const, fun σ x => rfl, one_ne_zero⟩⟩

lemma const_boxState_normB_pos {v : ℝ³ → ℝ} {μ : ℝ} (hℓ : 0 < ℓB v μ) (n : ℕ) :
    0 < normB v μ n (fun _ : X n => (1 : ℝ)) := by
  rw [normB_eq, sqNormB]
  simp only [one_pow]
  rw [MeasureTheory.setIntegral_const]
  have hvol : (volume : Measure (X n)).real (abox n (ℓB v μ)) = (ℓB v μ ^ 3) ^ n := by
    rw [Measure.real, Submission.BoseGases.abox_volume n (ℓB v μ) hℓ.le,
      ENNReal.toReal_ofReal]
    positivity
  rw [hvol, smul_eq_mul, mul_one]
  positivity

/-! ## 3. The threshold arithmetic: `Λ ≤ 0` for small diluteness -/

/-- **`Λ(a, C, η₀, μ) ≤ 0` for small `μa³`.**  `Λ` is negative for small diluteness: its bracket
is `1 − lhyC √(μa³) + C (μa³)^{1/2+η₀}` with the last term `≥ 0` (`C ≥ 0`), so
`lhyC √(μa³) ≤ 1/2` suffices, i.e. `μa³ ≤ (1/(2·lhyC))²`. -/
theorem Lambda_nonpos_of_small {a C η₀ : ℝ} (ha : 0 < a) (hC : 0 ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ : ℝ, 0 < μ → μ * a ^ 3 ≤ ε → Lambda a C η₀ μ ≤ 0 := by
  have hlhyC0 : 0 < lhyC := by
    dsimp [lhyC]
    positivity
  refine ⟨min 1 ((1 / (2 * lhyC)) ^ 2), lt_min one_pos (by positivity), ?_⟩
  intro μ hμ hle
  have ht : 0 < μ * a ^ 3 := by positivity
  have hle2 : μ * a ^ 3 ≤ (1 / (2 * lhyC)) ^ 2 := le_trans hle (min_le_right _ _)
  have hsqrt : √(μ * a ^ 3) ≤ 1 / (2 * lhyC) := by
    have h1 : √(μ * a ^ 3) ≤ √((1 / (2 * lhyC)) ^ 2) := Real.sqrt_le_sqrt hle2
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hkey : lhyC * √(μ * a ^ 3) ≤ 1 / 2 := by
    have h2 : lhyC * √(μ * a ^ 3) ≤ lhyC * (1 / (2 * lhyC)) :=
      mul_le_mul_of_nonneg_left hsqrt hlhyC0.le
    have h3 : lhyC * (1 / (2 * lhyC)) = 1 / 2 := by
      field_simp
    linarith [h2, h3.le, h3.ge]
  have hpow : 0 ≤ C * (μ * a ^ 3) ^ (1 / 2 + η₀) :=
    mul_nonneg hC (Real.rpow_nonneg ht.le _)
  have hbr : 0 ≤ 1 - lhyC * √(μ * a ^ 3) + C * (μ * a ^ 3) ^ (1 / 2 + η₀) := by
    linarith
  have hcoef : 0 ≤ 4 * π * μ ^ 2 * a := by positivity
  have hprod := mul_nonneg hcoef hbr
  rw [Lambda]
  linarith

end Work.BoseFixGlue
