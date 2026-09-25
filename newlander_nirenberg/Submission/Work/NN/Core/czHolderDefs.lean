/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Vocabulary for the Calderón–Zygmund (Schauder) estimate `czHolderEstimate`

This module collects the definitions and elementary facts used by
`Submission/Work/NN/Core/czHolderEstimate.lean` and by the auxiliary lemmas about
the singular integral

  `z ↦ ∫_{‖x‖ < 4R} Φ x · (g (z + x) - g z)`

for a Calderón–Zygmund kernel `Φ` of homogeneity `-2n` on `ℂⁿ = Fin n → ℂ`.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmCz.eucRadialBound
import Submission.Work.CR.Flat.Cauchy.bmCz.abs_eucNorm_sub_le

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Work.NN.Core

open Work.CR.Flat.Cauchy

/-! ### Elementary facts about `eucNorm` -/

/-- `eucNorm` is the `L²` norm of `x` in `WithLp 2 (Fin n → ℂ)`. -/
lemma eucNorm_eq_norm_withLp {n : ℕ} (x : Fin n → ℂ) :
    eucNorm x = ‖(WithLp.equiv 2 (Fin n → ℂ)).symm x‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp [eucNorm]

lemma eucNorm_add_le {n : ℕ} (x y : Fin n → ℂ) : eucNorm (x + y) ≤ eucNorm x + eucNorm y := by
  rw [eucNorm_eq_norm_withLp (x + y), eucNorm_eq_norm_withLp x, eucNorm_eq_norm_withLp y]
  rw [show (WithLp.equiv 2 (Fin n → ℂ)).symm (x + y)
      = (WithLp.equiv 2 (Fin n → ℂ)).symm x + (WithLp.equiv 2 (Fin n → ℂ)).symm y from by
    simp [WithLp.equiv_symm_apply]]
  exact norm_add_le _ _

lemma eucNorm_sub_le' {n : ℕ} (x y : Fin n → ℂ) : eucNorm (x - y) ≤ eucNorm x + eucNorm y := by
  rw [eucNorm_eq_norm_withLp (x - y), eucNorm_eq_norm_withLp x, eucNorm_eq_norm_withLp y]
  rw [show (WithLp.equiv 2 (Fin n → ℂ)).symm (x - y)
      = (WithLp.equiv 2 (Fin n → ℂ)).symm x - (WithLp.equiv 2 (Fin n → ℂ)).symm y from by
    simp [WithLp.equiv_symm_apply]]
  exact norm_sub_le _ _

lemma eucNorm_neg {n : ℕ} (x : Fin n → ℂ) : eucNorm (-x) = eucNorm x := by
  simp [eucNorm]

lemma eucNorm_sub_comm {n : ℕ} (x y : Fin n → ℂ) : eucNorm (x - y) = eucNorm (y - x) := by
  rw [show y - x = -(x - y) from by abel, eucNorm_neg]

/-- Triangle inequality in the form `‖u - z'‖ ≥ ‖u - z‖ - ‖z - z'‖`. -/
lemma eucNorm_le_add_eucNorm_sub {n : ℕ} (u z z' : Fin n → ℂ) :
    eucNorm (u - z) ≤ eucNorm (u - z') + eucNorm (z' - z) := by
  have h := eucNorm_add_le (u - z') (z' - z)
  rwa [show (u - z') + (z' - z) = u - z from by abel] at h

/-- Triangle inequality in the form `‖u - z'‖ ≥ ‖u - z‖ - ‖z - z'‖`. -/
lemma sub_le_eucNorm_sub {n : ℕ} (u z z' : Fin n → ℂ) :
    eucNorm (u - z) - eucNorm (z' - z) ≤ eucNorm (u - z') := by
  have h := eucNorm_le_add_eucNorm_sub u z z'
  linarith

/-! ### Translation of set integrals on `ℂⁿ` -/

/-- Translation of a set integral on `ℂⁿ`: `∫_{x ∈ A} F (x + c) = ∫_{u ∈ c + A} F u`. -/
lemma setIntegral_translate_euc {n : ℕ} (c : Fin n → ℂ) (F : (Fin n → ℂ) → ℂ)
    (A : Set (Fin n → ℂ)) :
    ∫ x in A, F (x + c) = ∫ u in (fun x : Fin n → ℂ => x + c) '' A, F u := by
  have hmp : MeasurePreserving (fun x : Fin n → ℂ => x + c) volume volume :=
    MeasureTheory.measurePreserving_add_right volume c
  have hemb : MeasurableEmbedding (fun x : Fin n → ℂ => x + c) :=
    (Homeomorph.addRight c).measurableEmbedding
  have h := hmp.setIntegral_preimage_emb hemb F ((fun x : Fin n → ℂ => x + c) '' A)
  rw [show (fun x : Fin n → ℂ => x + c) ⁻¹' ((fun x : Fin n → ℂ => x + c) '' A) = A from by
    ext x; simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨a, ha, hax⟩; rwa [add_right_cancel hax] at ha
    · intro hx; exact ⟨x, hx, rfl⟩] at h
  exact h

/-- The translated shell is measurable. -/
lemma measurableSet_image_add {n : ℕ} (c : Fin n → ℂ) {A : Set (Fin n → ℂ)}
    (hA : MeasurableSet A) : MeasurableSet ((fun x : Fin n → ℂ => x + c) '' A) :=
  (Homeomorph.addRight c).measurableEmbedding.measurableSet_image' hA

/-- Membership in a translated shell. -/
@[simp] lemma mem_image_add {n : ℕ} (c : Fin n → ℂ) {A : Set (Fin n → ℂ)}
    (u : Fin n → ℂ) : u ∈ (fun x : Fin n → ℂ => x + c) '' A ↔ u - c ∈ A := by
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro h; exact ⟨u - c, h, by abel⟩

/-! ### The singular integral -/

/-- The Calderón–Zygmund transform of the difference `g (z + ·) - g z` against the kernel `Φ`,
integrated over the ball of radius `4R`.  This is exactly the integral appearing in
`Work.NN.Core.czHolderEstimate`. -/
def czInt {n : ℕ} (Φ : (Fin n → ℂ) → ℂ) (g : (Fin n → ℂ) → ℂ) (R : ℝ)
    (z : Fin n → ℂ) : ℂ :=
  ∫ x in Work.CR.Flat.Cauchy.eucBall (4 * R), Φ x * (g (z + x) - g z)

end Work.NN.Core
