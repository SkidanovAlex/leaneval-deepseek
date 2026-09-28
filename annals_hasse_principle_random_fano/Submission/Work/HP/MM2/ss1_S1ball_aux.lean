import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.SstarMobiusMix
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MinkDefs

/-!
# Auxiliary `S1ball` lemmas for the mixed second moment

Small, self-contained facts about `Work.HP.MM2.S1ball` needed by `Sstar1_mix_pair` and
`Sstar1_mix_tail`: the height-box form, monotonicity in the radius, and the comparison
`Sk 1 (GamMix …) (TmixSet …) ≤ S1ball`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.HP.MM2

attribute [local instance] Classical.propDecidable

open Filter Finset MeasureTheory
open Work.HP

/-- `S1ball` is `Sk 1` on `Λ_{ν(x)}` with the ball as the region. -/
private lemma ss1_S1ball_eq_Sk (d n : ℕ) [DecidableEq (Mon d n)] (x : Fin (n + 1) → ℤ) (T : ℝ) :
    S1ball d n x T = Sk d n 1 (latOrth (veronese d n x)) {a | eNorm a ≤ T} := by
  rw [S1ball, Sk]
  simp only [Set.mem_ofPred_eq, pow_one]

/-- `S1ball` as a sum over the height box `nBox d n A`, for `A ≥ T`. -/
theorem ss1_S1ball_eq_sum_nBoxA (d n : ℕ) [DecidableEq (Mon d n)] (x : Fin (n + 1) → ℤ)
    (A T : ℝ) (hTA : T ≤ A) :
    S1ball d n x T = ∑ a ∈ nBox d n A,
      (if a ∈ latOrth (veronese d n x) ∧ a ≠ 0 ∧ eNorm a ≤ T then 1 / eNorm a else 0) := by
  classical
  rw [ss1_S1ball_eq_Sk]
  rw [Sk_eq_sum_nBox (d := d) (n := n) 1 (latOrth (veronese d n x)) {a | eNorm a ≤ T} (A := A)
      (fun a ha => le_trans ha hTA)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases h : a ∈ latOrth (veronese d n x) ∧ a ≠ 0 ∧ eNorm a ≤ T <;> simp [h, pow_one]

/-- `S1ball` is monotone in the radius. -/
theorem ss1_S1ball_mono (d n : ℕ) [DecidableEq (Mon d n)] (x : Fin (n + 1) → ℤ) {T T' : ℝ}
    (h : T ≤ T') : S1ball d n x T ≤ S1ball d n x T' := by
  classical
  rw [ss1_S1ball_eq_sum_nBoxA d n x (max T T') T (le_max_left _ _),
    ss1_S1ball_eq_sum_nBoxA d n x (max T T') T' (le_max_right _ _)]
  refine Finset.sum_le_sum (fun a _ => ?_)
  by_cases h1 : a ∈ latOrth (veronese d n x) ∧ a ≠ 0 ∧ eNorm a ≤ T
  · rw [if_pos h1, if_pos ⟨h1.1, h1.2.1, le_trans h1.2.2 h⟩]
  · rw [if_neg h1]
    by_cases h2 : a ∈ latOrth (veronese d n x) ∧ a ≠ 0 ∧ eNorm a ≤ T'
    · rw [if_pos h2]; exact div_nonneg zero_le_one (le_of_lt ((eNorm_pos_iff).mpr h2.2.1))
    · rw [if_neg h2]

/-- `Sk 1 (GamMix x y Q) (TmixSet y T α) ≤ S1ball d n x T`. -/
theorem ss1_Sk_le_S1ball (d n : ℕ) [DecidableEq (Mon d n)] (x y : Fin (n + 1) → ℤ) (Q : ℕ)
    (T α : ℝ) :
    Sk d n 1 (GamMix d n x y Q) (TmixSet d n y T α) ≤ S1ball d n x T := by
  classical
  rw [Sk_eq_sum_nBox (d := d) (n := n) 1 (GamMix d n x y Q) (TmixSet d n y T α) (A := T)
      (fun a ha => ha.1)]
  rw [ss1_S1ball_eq_sum_nBoxA d n x T T le_rfl]
  refine Finset.sum_le_sum (fun a _ => ?_)
  by_cases h : a ∈ GamMix d n x y Q ∧ a ≠ 0 ∧ a ∈ TmixSet d n y T α
  · have hL : a ∈ latOrth (veronese d n x) := by
      have h1 := h.1; rw [GamMix] at h1; exact h1.1
    rw [if_pos h, if_pos ⟨hL, h.2.1, h.2.2.1⟩, pow_one]
  · rw [if_neg h]
    by_cases h2 : a ∈ latOrth (veronese d n x) ∧ a ≠ 0 ∧ eNorm a ≤ T
    · rw [if_pos h2]; exact div_nonneg zero_le_one (le_of_lt ((eNorm_pos_iff).mpr h2.2.1))
    · rw [if_neg h2]

end Work.HP.MM2
