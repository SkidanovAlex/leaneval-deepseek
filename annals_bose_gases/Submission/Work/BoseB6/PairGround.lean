import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Submission.Fock2ModeShift
import Submission.Work.BoseB6.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6 — the delivered two-mode Bogoliubov lemma, in chapter vocabulary

`Submission.Fock2Mode` / `Submission.Fock2ModeShift` already deliver FS App.
`thm:bogolubov-complete`:

* `Submission.BoseGases.fock_two_mode_identity` — `eq:BogIdentity` with `κ = 0`;
* `Submission.BoseGases.fms_shift_identity` — `eq:BogIdentity` with the real
  linear term `κ = L`;
* `Submission.BoseGases.fms_ground_estimate` — `eq:BogIneq` with `κ = L`:
  `fsQuadLin 𝒜 ℬ L M φ ≥ −[(𝒜−√(𝒜²−ℬ²)) + 2L²/(𝒜+ℬ)]·‖φ‖²`.

This module re-exposes those two results using the chapter's names
(`bogZeroPoint`, `bogDD`, `bogKappaErr` of `Work.BoseB6.Defs`), so that a
consumer of node B6 imports `Work.BoseB6.PairGround` and gets the two-mode
Bogoliubov lemma in the same vocabulary as the rest of the chapter, without
having to know about `Submission.Fock2Mode*`.

Nothing is proved here that was not already proved in the graded corpus; these
are definitional restatements (the chapter's `bogZeroPoint`/`bogDD`/`bogKappaErr`
*are* the corpus's `A − bogS`, `bogD`, `2L²/(A+B)`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB6

open Submission.BoseGases

/-- **FS `eq:BogIdentity` with `κ = L`** (`thm:bogolubov-complete`), in chapter
vocabulary: on the two-mode number basis, with `𝒟 = bogDD 𝒜 ℬ`,
`b₊ = fmsBPlus 𝒜 ℬ L`, `b₋ = fmsBMinus 𝒜 ℬ L`,

  `⟨φ,Hφ⟩ = 𝒟(‖b₊φ‖² + ‖b₋φ‖²) − (𝒜−√(𝒜²−ℬ²))‖φ‖² − (2L²/(𝒜+ℬ))‖φ‖²`. -/
theorem pairForm_identity {A B L : ℝ} (hA : 0 < A) (hB : |B| ≤ A) (hAB : 0 < A + B)
    (M : ℕ) {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    fsQuadLin A B L M φ =
      bogDD A B * (rectNorm M (fmsBPlus A B L φ) + rectNorm M (fmsBMinus A B L φ)) -
        bogZeroPoint A B * rectNorm M φ - bogKappaErr A B L * rectNorm M φ := by
  have h := fms_shift_identity (L := L) hA hB hAB M hφ
  rw [bogDD_eq_bogD, bogZeroPoint_eq, bogKappaErr_eq]
  linarith [h]

/-- **FS `eq:BogIneq` with `κ = L`** (`thm:bogolubov-complete`), in chapter
vocabulary: the two-mode Bogoliubov form is bounded below by minus the
zero-point constant minus the `κ`-error. -/
theorem pairForm_ground {A B L : ℝ} (hA : 0 < A) (hB : |B| ≤ A) (hAB : 0 < A + B)
    (M : ℕ) {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    -(bogZeroPoint A B + bogKappaErr A B L) * rectNorm M φ ≤ fsQuadLin A B L M φ := by
  have h := fms_ground_estimate (L := L) hA hB hAB M hφ
  rw [bogZeroPoint_eq, bogKappaErr_eq]
  linarith [h]

/-- FS `eq:BogIneq` with `κ = 0` (the case used before the `𝒞`-shift is put
back): `⟨φ,Hφ⟩ ≥ −(𝒜−√(𝒜²−ℬ²))·‖φ‖²`. -/
theorem pairForm_ground_zero {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A)
    (M : ℕ) {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    -(bogZeroPoint A B) * rectNorm M φ ≤ fsQuad A B M φ := by
  have h := fock_ground_estimate hA hB M hφ
  rw [bogZeroPoint_eq]
  linarith [h]

/-- The two-mode Bogoliubov identity with `κ = 0`, in chapter vocabulary. -/
theorem pairForm_identity_zero {A B : ℝ} (hA : 0 < A) (hB : |B| ≤ A)
    (M : ℕ) {φ : ℕ × ℕ → ℝ} (hφ : vanishOn M φ) :
    fsQuad A B M φ =
      bogDD A B * (rectNorm M (bPlus (bogAlphaP A B) φ) +
        rectNorm M (bMinus (bogAlphaP A B) φ)) - bogZeroPoint A B * rectNorm M φ := by
  have h := fock_two_mode_identity hA hB M hφ
  rw [bogDD_eq_bogD, bogAlphaP_eq_bogAlpha, bogZeroPoint_eq]
  linarith [h]

end Work.BoseB6
