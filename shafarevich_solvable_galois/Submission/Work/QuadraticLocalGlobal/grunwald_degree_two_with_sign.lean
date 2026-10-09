import Mathlib
import Submission.Work.QuadraticLocalGlobal.Defs
import Submission.Work.QuadraticLocalGlobal.GrunwaldPrelim
import Submission.Work.QuadraticLocalGlobal.exists_local_parity_sameSquare
import Submission.Work.QuadraticLocalGlobal.exists_rat_unit_sameSquare_of_local_data
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.QuadraticLocalGlobal

theorem grunwald_degree_two_with_sign {ι : Type*} [Fintype ι] (q : ι → ℕ) [∀ i, Fact (q i).Prime] (hq : Function.Injective q) (c : ∀ i, (ℚ_[q i])ˣ) (ε : ℚˣ) : ∃ d : ℚˣ, (0 < (d : ℚ) * (ε : ℚ)) ∧ ∀ i, Work.QuadraticLocalGlobal.SameSquare ((d : ℚ_[q i])) ((c i : (ℚ_[q i])ˣ) : ℚ_[q i]) := by
  classical
  -- Local reduction: at each `q i` the local square class is `(q i) ^ (e i) * (n i)`.
  choose e n hrest using fun i => exists_local_parity_sameSquare (c i)
  have he : ∀ i, e i ≤ 1 := fun i => (hrest i).1
  have hn : ∀ i, n i ≠ 0 := fun i => (hrest i).2.1
  have hnc : ∀ i, (n i).Coprime (q i) := fun i => (hrest i).2.2.1
  have hsq : ∀ i, SameSquare (((q i : ℚ_[q i]) ^ (e i)) * (n i : ℚ_[q i]))
      ((c i : (ℚ_[q i])ˣ) : ℚ_[q i]) := fun i => (hrest i).2.2.2
  -- The sign prescribed by `ε`.
  set σ : ℤˣ := if (0 : ℚ) < (ε : ℚ) then 1 else -1 with hσdef
  -- The Grünwald construction realises all the local square classes and the sign.
  obtain ⟨d, hd_sign, hd_loc⟩ :=
    exists_rat_unit_sameSquare_of_local_data q hq e he n hn hnc σ
  refine ⟨d, ?_, fun i => sameSquare_trans (hd_loc i) (hsq i)⟩
  by_cases hε : (0 : ℚ) < (ε : ℚ)
  · have hσ : ((σ : ℤ) : ℚ) = 1 := by rw [hσdef]; simp [hε]
    rw [hσ, mul_one] at hd_sign
    exact mul_pos hd_sign hε
  · have hσ : ((σ : ℤ) : ℚ) = -1 := by rw [hσdef]; simp [hε]
    rw [hσ] at hd_sign
    have hd_neg : (d : ℚ) < 0 := by nlinarith [hd_sign]
    have hε_neg : (ε : ℚ) < 0 := lt_of_le_of_ne (not_lt.mp hε) (by simpa using ε.ne_zero)
    exact mul_pos_of_neg_of_neg hd_neg hε_neg

end Work.QuadraticLocalGlobal
