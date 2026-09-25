import Mathlib
import Submission.Work.LT.lr_local_defs

/-!
# The two one-step walks attached to a label class of edges

`Work.LT.classOpA A` is the walk on `Fin 2 × G` which, from `(0,g)`, jumps to `(1, A i * g)` and
from `(1,g)` to `(0, (A i)⁻¹ * g)`, each with probability `1/Δ`.  Its two components are the
normalised left-averaging operator `POp A` and its transpose-like companion `ROp A` (left
averaging with the inverses of the `A i`).

This file collects the definitions and the elementary summation facts shared with the helper
lemmas proved elsewhere in the workspace.
-/

set_option autoImplicit false

namespace Work.LT

open Classical
open scoped BigOperators

variable {G : Type*} [Group G] [Fintype G] {Δ : ℕ}

/-- Normalised left-averaging operator: `POp A w g = (1/Δ) ∑_i w (A i * g)`. -/
noncomputable def POp (A : Fin Δ → G) (w : G → ℝ) : G → ℝ :=
  fun g => (∑ i, w (A i * g)) / (Δ : ℝ)

/-- Normalised left-averaging operator with the inverses of the `A i`:
`ROp A w g = (1/Δ) ∑_i w ((A i)⁻¹ * g)`. -/
noncomputable def ROp (A : Fin Δ → G) (w : G → ℝ) : G → ℝ :=
  fun g => (∑ i, w ((A i)⁻¹ * g)) / (Δ : ℝ)

/-- `POp A` is exactly the walk whose contraction on mean-zero functions is `leftExpander`. -/
lemma POp_gap (A : Fin Δ → G) (μ : ℝ) (hA : leftExpander A μ) (w : G → ℝ)
    (hw : ∑ g, w g = 0) :
    ∑ g, (POp A w g) ^ 2 ≤ μ ^ 2 * ∑ g, w g ^ 2 := by
  simpa [POp] using hA w hw

/-- `POp A` preserves the total sum. -/
lemma POp_sum (A : Fin Δ → G) (w : G → ℝ) (hΔ : (Δ : ℝ) ≠ 0) :
    ∑ g, POp A w g = ∑ g, w g := by
  simp only [POp]
  rw [← Finset.sum_div, Finset.sum_comm]
  have h : ∀ i : Fin Δ, (∑ g, w (A i * g)) = ∑ g, w g := fun i =>
    Equiv.sum_comp (Equiv.mulLeft (A i)) w
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- `POp A` fixes the constant functions. -/
lemma POp_const (A : Fin Δ → G) (c : ℝ) (hΔ : (Δ : ℝ) ≠ 0) :
    POp A (fun _ => c) = fun _ => c := by
  funext g
  simp only [POp]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- `POp A` is additive in a constant shift. -/
lemma POp_add_const (A : Fin Δ → G) (w : G → ℝ) (c : ℝ) (hΔ : (Δ : ℝ) ≠ 0) :
    POp A (fun g => w g + c) = fun g => POp A w g + c := by
  funext g
  simp only [POp]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end Work.LT
