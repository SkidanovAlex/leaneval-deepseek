import Mathlib
import Submission.Work.Residues.KMinusCuspDefs

namespace Work.Residues

open UpperHalfPlane

/-- Congruence for `CuspBound`: pointwise equal functions have the same bounds. -/
lemma CuspBound.of_eq {f g : ℍ → ℂ} {m k : ℕ} (hfg : ∀ τ, f τ = g τ)
    (hg : CuspBound g m k) : CuspBound f m k := by
  obtain ⟨H, C, hC, hb⟩ := hg
  exact ⟨H, C, hC, fun τ hτ => by rw [hfg τ]; exact hb τ hτ⟩

/-- If `S` is a continuous function of the two cusp coordinates `(U-1, V)`, then
`V^k · S (U-1, V)` is a `CuspBound` with vanishing order `k` and polynomial growth `0`.
This is the engine behind every entry of `CuspPolyBounds`, since `‖V‖ = O(tpar)` near the
cusp and `S` is bounded there. -/
lemma cuspBound_bcusp_pow_mul_poly {S : ℂ → ℂ → ℂ}
    (hS : Continuous fun p : ℂ × ℂ => S p.1 p.2) (k : ℕ) :
    CuspBound (fun τ : ℍ => bcusp τ ^ k * S (acusp τ) (bcusp τ)) 0 k := by
  obtain ⟨H1, C1, hC1, h1⟩ := bcusp_bound
  obtain ⟨H2, C2, hC2, h2⟩ := poly2_cusp_bound S hS
  refine ⟨max H1 H2, C1 ^ k * C2, mul_pos (pow_pos hC1 k) hC2, fun τ hτ => ?_⟩
  have hτ1 : H1 ≤ τ.im := le_trans (le_max_left _ _) hτ
  have hτ2 : H2 ≤ τ.im := le_trans (le_max_right _ _) hτ
  rw [norm_mul, norm_pow]
  calc ‖bcusp τ‖ ^ k * ‖S (acusp τ) (bcusp τ)‖
      ≤ (C1 * tpar τ) ^ k * C2 :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (h1 τ hτ1) k) (h2 τ hτ2)
          (norm_nonneg _) (pow_nonneg (mul_nonneg hC1.le (tpar_nonneg τ)) k)
    _ = C1 ^ k * C2 * (1 + ‖(τ : ℂ)‖) ^ 0 * tpar τ ^ k := by ring

/-- A function that agrees pointwise with `V^k · S (U-1, V)` for a continuous `S` is a
`CuspBound` of order `k`. -/
lemma cuspBound_of_eq_poly {f : ℍ → ℂ} {S : ℂ → ℂ → ℂ}
    (hS : Continuous fun p : ℂ × ℂ => S p.1 p.2) (k : ℕ)
    (hf : ∀ τ, f τ = bcusp τ ^ k * S (acusp τ) (bcusp τ)) : CuspBound f 0 k :=
  CuspBound.of_eq hf (cuspBound_bcusp_pow_mul_poly hS k)

theorem CuspPolyBounds :
    Work.Residues.CuspBound Work.Residues.P1fun 0 2 ∧
    Work.Residues.CuspBound Work.Residues.P2fun 0 2 ∧
    Work.Residues.CuspBound Work.Residues.Xfun 0 2 ∧
    Work.Residues.CuspBound Work.Residues.Q1fun 0 1 ∧
    Work.Residues.CuspBound Work.Residues.Q2fun 0 1 ∧
    Work.Residues.CuspBound Work.Residues.Yfun 0 1 ∧
    Work.Residues.CuspBound Work.Residues.Ntfun 0 4 ∧
    Work.Residues.CuspBound Work.Residues.Ntbfun 0 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cuspBound_of_eq_poly (S := S_P1) (by unfold S_P1; fun_prop) 2
      (fun τ => by simp only [P1fun_eq, pow_one])
  · exact cuspBound_of_eq_poly (S := S_P2) (by unfold S_P2; fun_prop) 2
      (fun τ => by simp only [P2fun_eq, pow_one])
  · exact cuspBound_of_eq_poly (S := S_X) (by unfold S_X; fun_prop) 2
      (fun τ => by simp only [Xfun_eq, pow_one])
  · exact cuspBound_of_eq_poly (S := S_Q1) (by unfold S_Q1; fun_prop) 1
      (fun τ => by simp only [Q1fun_eq, pow_one])
  · exact cuspBound_of_eq_poly (S := S_Q2) (by unfold S_Q2; fun_prop) 1
      (fun τ => by simp only [Q2fun_eq, pow_one])
  · exact cuspBound_of_eq_poly (S := S_Y) (by unfold S_Y; fun_prop) 1
      (fun τ => by simp only [Yfun_eq, pow_one])
  · exact cuspBound_of_eq_poly (S := S_Nt) (by unfold S_Nt; fun_prop) 4
      (fun τ => by simp only [Ntfun_eq, pow_one])
  · exact cuspBound_of_eq_poly (S := S_Ntb) (by unfold S_Ntb; fun_prop) 1
      (fun τ => by simp only [Ntbfun_eq, pow_one])

end Work.Residues
