import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1P` — the vocabulary of the box-gap pairing

This module fixes the objects used by the lemma

`Work.BoseFixB1P.cnPlusBoxInd_integral_u_le_neuFrac`

(FS `eq:appTB` gap term against FS `eq:DefT`'s first term / Brietzke–Solovej `lm:hQuuav` at
the *sharp* constant `1 + π⁻²`).

## The mathematical shape of the proof (for the record)

* at one particle the corpus's FS-faithful excited count is the *local mean-free mass*

      cnPlusBoxInd ℓ (dlBox ℓ d u) (boxMass ℓ d u) (φ ∘ proj)
        = ∫_{B(u)} (φ - m_u)²,   m_u = |B(u)|⁻¹ ∫_{B(u)} φ ,   B(u) = dlBox ℓ d u;

* `B(u)` is an axis-parallel box with all side lengths `≤ a := ℓ*d`, so the *per-box*
  inequality gives, for every smooth trial `g` and with `h := φ - M`
  (`M = |acube ℓ|⁻¹ ∫_{acube ℓ} φ`),

      ∫_{B(u)} (h - (m_u - M))² ≤ (1+π⁻²) · boxTrialForm a⁻² (B(u)) h g;

* the four pieces of the right-hand side are *tube integrals*
  (`∫_u ∫_{B(u)} F = ∫_{acube ℓ} F`), so their `u`-integral is exactly
  `boxTrialForm a⁻² (acube ℓ) h g`, which is precisely the trial functional of
  `Work.BoseKinLoc.neuFrac ℓ (d*ℓ)⁻² 0 (Qfree ℓ 0 φ)`;

* `neuFrac` is the `sInf` of those trial values, so the claim follows.

The per-box inequality is the sharp mean-free Neumann estimate on a box of side `≤ a`:
for a box `P` with `|P| > 0`, a mean-free trial part `v` and the trial box Dirichlet form
`∫_P ∑_k (∂_k v)² ≥ (π²/a²) ∫_P v²`, one has (`c = a⁻²`, `u = Q_P h`)

    2c ∫_P u v ≤ c ∫_P |∇v|² + c² ∫_P v² + ‖u‖²/(1+π²),

which is the two-variable Young inequality at the sharp Poincaré constant `π²/a²`; the
constant parts of `h` and `g` combine into the perfect square `|P|(m - c·n)²`.

## Contents

Vocabulary only: the axis-parallel box `Box3`, its volume `volBox`, the trial functional
`boxTrialForm` (written *in the exact shape of the `neuFrac` trial set*, with the
`kcStdBasis` sum of squared partial derivatives) and the local mean-free mass `localVar`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1P

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## 1. Axis-parallel boxes and their volume -/

/-- The closed axis-parallel box `∏_j [p_j, q_j]`, with the corners given as coordinate
functions (this is the form in which the sliding box `dlBox ℓ d u` naturally arises). -/
def Box3 (p q : Fin 3 → ℝ) : Set ℝ³ := {x : ℝ³ | ∀ j : Fin 3, x j ∈ Set.Icc (p j) (q j)}

@[simp] lemma mem_Box3 {p q : Fin 3 → ℝ} {x : ℝ³} :
    x ∈ Box3 p q ↔ ∀ j : Fin 3, x j ∈ Set.Icc (p j) (q j) := Iff.rfl

/-- The standard cube `acube a` is the box with the corners `±a/2`. -/
lemma Box3_cube (a : ℝ) : Box3 (fun _ => -(a / 2)) (fun _ => a / 2) = acube a := by
  ext x; simp only [Box3, mem_acube_iff, Set.mem_setOf_eq]
  constructor <;> intro h m
  · have := h m; constructor <;> linarith [this.1, this.2]
  · have := h m; constructor <;> linarith [this.1, this.2]

/-- The (real) volume of a set. -/
noncomputable def volBox (P : Set ℝ³) : ℝ := (volume : Measure ℝ³).real P

/-- `Box3` is measurable. -/
lemma measurableSet_Box3 (p q : Fin 3 → ℝ) : MeasurableSet (Box3 p q) := by
  have h : Box3 p q = ⋂ j : Fin 3, {x : ℝ³ | x j ∈ Set.Icc (p j) (q j)} := by
    ext x; simp [Box3]
  rw [h]
  exact MeasurableSet.iInter fun j =>
    measurableSet_Icc.preimage (by fun_prop)

/-- `volBox` is nonnegative. -/
lemma volBox_nonneg (P : Set ℝ³) : 0 ≤ volBox P := by
  rw [volBox]; exact ENNReal.toReal_nonneg

/-! ## 2. The trial functional of `neuFrac` and the local mean-free mass -/

/-- **The trial functional of `Work.BoseKinLoc.neuFrac`**, written for a general box `P`:
with `h := Qfree ℓ 0 φ` and `P := acube ℓ` this is *definitionally* the value of the `neuFrac`
trial set at the smooth compactly supported trial `g`. -/
noncomputable def boxTrialForm (c : ℝ) (P : Set ℝ³) (h g : ℝ³ → ℝ) : ℝ :=
  (∫ x in P, (h x) ^ 2) - 2 * c * (∫ x in P, h x * g x)
    + c * ((∑ k : Fin 3, ∫ x in P,
              (fderiv ℝ g x (Submission.BoseGases.kcStdBasis k)) ^ 2)
            + c * (∫ x in P, (g x) ^ 2))

/-- **The local mean-free mass** of `h` over `P`: `∫_P (h - |P|⁻¹∫_P h)²`.  This is the
one-particle excited count of the box `P` (`cnPlusBoxInd` at `N = 1`). -/
noncomputable def localVar (P : Set ℝ³) (h : ℝ³ → ℝ) : ℝ :=
  ∫ x in P, (h x - (1 / volBox P) * ∫ y in P, h y) ^ 2

end Work.BoseFixB1P
