import Mathlib
import Submission.Work.SynFFT.defs

namespace Work.SynFFT

/-- Shifting the array index by a multiple of the block length `t * B` does not change the
block residue `(p / B) % t`. -/
lemma divB_mod_t_eq (t B σ p : ℕ) (h : t * B ∣ σ) :
    ((σ + p) / B) % t = (p / B) % t := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · subst hB; simp
  · obtain ⟨k, hk⟩ := h
    subst hk
    have hdiv : (t * B * k + p) / B = t * k + p / B := by
      rw [show t * B * k = B * (t * k) by ring]
      rw [Nat.mul_add_div hB]
    rw [hdiv, Nat.mul_add_mod]

/-- Reindexing the axis-`t` sum after a shift by a multiple `σ` of `t * B`. -/
lemma axisT_index_eq (t B σ p u : ℕ) (h : t * B ∣ σ) :
    σ + (p - (p / B % t) * B + u * B) =
      (σ + p) - (((σ + p) / B) % t) * B + u * B := by
  have hmod := divB_mod_t_eq t B σ p h
  have hle : (p / B % t) * B ≤ p :=
    le_trans (Nat.mul_le_mul_right _ (Nat.mod_le _ _)) (Nat.div_mul_le_self p B)
  rw [hmod]
  omega

theorem axisTShift (r t B : ℕ) (sgn : ℤ) (σ : ℕ) (a : Work.SynFFT.Arr r) (h : t * B ∣ σ) :
    ∀ p : ℕ, Work.SynFFT.axisT r t B sgn (fun x c => a (σ + x) c) p =
      Work.SynFFT.axisT r t B sgn a (σ + p) := by
  intro p
  funext c
  simp only [axisT]
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  rw [axisT_index_eq t B σ p u h, divB_mod_t_eq t B σ p h]

end Work.SynFFT
