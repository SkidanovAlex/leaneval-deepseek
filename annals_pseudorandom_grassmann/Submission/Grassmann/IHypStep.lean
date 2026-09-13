import Submission.Grassmann.ReindexFibre

/-!
# P5: the inductive step `IHyp C (d−1) → IHyp C d` at a *fixed* constant `C`

The paper's induction (`thm:Hypercontractivity in the Bilinear scheme`, arXiv:2209.04243) uses
`(1/162)‖f‖₄⁴ ≤ q^{6d²}‖f‖₂⁴ + q^{100d²−31d} Σ_{V₃,W₃} E_T‖D_{V₃,W₃,T}f‖₂⁴`: the shave
`q^{−31d}` is **independent of the summation index**, and `162 ≤ q^{31d}` then pays for the
constant `162`.

Our reindexed form (`sum_l4q_XtPred_le`) has the same feature thanks to the strengthened fibre
bound `fiber_weight_le_sharp2`: it supplies `q^{−12d}` on top of the `q^{−12dk}`, and
`2·2^{Cd²}·2^{−12d}·2 ≤ 2^{Cd²}/2` for `d ≥ 1`, leaving room for `162·2^{6d²} ≤ 2^{Cd²}/2`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-- **The inductive step.**  `IHyp C (d−1)` implies `IHyp C d` for `100 ≤ C` and `1 ≤ d`. -/
theorem IHyp_step (C : ℕ) (hC : 100 ≤ C) (D : ℕ) (hD : 1 ≤ D)
    (hIH : IHyp C (D - 1)) : IHyp C D := by
  intro m n d f hd' hf
  rcases lt_or_eq_of_le hd' with hlt | heq
  · exact hIH m n d f (by omega) hf
  · subst heq
    set Sall : ℝ := ∑ V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W : Submodule 𝔽₂ (Fin m → 𝔽₂),
      D4 V₀ W (Lsub V₀ W f) with hSdef
    set T : ℝ := ∑ t : Triple m n, (if totOrder t = 0 then 0 else
      (2 : ℝ) ^ (26 * d * totOrder t) * l4q (lapMulN (XtPred t) (Lsub t.1 t.2.1 f))) with hTdef
    have hS0 : (0 : ℝ) ≤ Sall := by
      rw [hSdef]
      exact Finset.sum_nonneg fun V₀ _ => Finset.sum_nonneg fun W _ => D4_nonneg _ _ _
    have hl2 : (l2sq f) ^ 2 ≤ Sall := by
      rw [hSdef]
      exact (l2sq_sq_le_sum_D4 d f).trans (le_of_eq (sum_D4_eq_sum_D4_of_degLe hf))
    have h2 : T ≤ (2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (12 * d))⁻¹ * 2 * Sall := by
      rw [hTdef, hSdef]
      exact sum_l4q_XtPred_le (m := m) (n := n) d C (by omega) hIH hf
    have h1 : l4q f ≤ 162 * (2 : ℝ) ^ (6 * d ^ 2) * (l2sq f) ^ 2 + 2 * T := by
      rw [hTdef]
      exact after_restricting' (m := m) (n := n) hf
    have hconst : 162 * (2 : ℝ) ^ (6 * d ^ 2) * (l2sq f) ^ 2
        ≤ 162 * (2 : ℝ) ^ (6 * d ^ 2) * Sall :=
      mul_le_mul_of_nonneg_left hl2 (by positivity)
    have htwo : 2 * T ≤ 2 * ((2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (12 * d))⁻¹ * 2 * Sall) :=
      mul_le_mul_of_nonneg_left h2 (by norm_num)
    have hstep : l4q f ≤
        (162 * (2 : ℝ) ^ (6 * d ^ 2)
          + 2 * ((2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (12 * d))⁻¹ * 2)) * Sall := by
      calc l4q f ≤ 162 * (2 : ℝ) ^ (6 * d ^ 2) * (l2sq f) ^ 2
              + 2 * T := h1
        _ ≤ 162 * (2 : ℝ) ^ (6 * d ^ 2) * Sall
              + 2 * ((2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (12 * d))⁻¹ * 2 * Sall) :=
            add_le_add hconst htwo
        _ = (162 * (2 : ℝ) ^ (6 * d ^ 2)
              + 2 * ((2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (12 * d))⁻¹ * 2)) * Sall := by ring
    have hcoef : 162 * (2 : ℝ) ^ (6 * d ^ 2)
        + 2 * ((2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (12 * d))⁻¹ * 2) ≤ (2 : ℝ) ^ (C * d ^ 2) := by
      have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ (12 * d) := by
        calc (8 : ℝ) = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (12 * d) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2inv : ((2 : ℝ) ^ (12 * d))⁻¹ ≤ 1 / 8 := by
        rw [show (1 : ℝ) / 8 = ((8 : ℝ))⁻¹ by norm_num]
        rw [inv_le_inv₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (12 * d)) (by norm_num : (0:ℝ) < 8)]
        exact h8
      have hA : 2 * ((2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (12 * d))⁻¹ * 2)
          ≤ (2 : ℝ) ^ (C * d ^ 2) * (1 / 2) := by
        have h4 : (2 : ℝ) * ((2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (12 * d))⁻¹ * 2)
            = (2 : ℝ) ^ (C * d ^ 2) * (4 * ((2 : ℝ) ^ (12 * d))⁻¹) := by ring
        rw [h4]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (4 : ℝ) * ((2 : ℝ) ^ (12 * d))⁻¹ ≤ 4 * (1 / 8) :=
              mul_le_mul_of_nonneg_left h2inv (by norm_num)
          _ = 1 / 2 := by norm_num
      have hB : 162 * (2 : ℝ) ^ (6 * d ^ 2) ≤ (2 : ℝ) ^ (C * d ^ 2) * (1 / 2) := by
        have hd2 : 1 ≤ d * d := by nlinarith [hD]
        have h15 : 6 * d ^ 2 + 9 ≤ C * d ^ 2 := by nlinarith [hC, hd2]
        rw [show (2 : ℝ) ^ (C * d ^ 2) * (1 / 2) = (2 : ℝ) ^ (C * d ^ 2) / 2 by ring]
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
        calc 162 * (2 : ℝ) ^ (6 * d ^ 2) * 2 = 324 * (2 : ℝ) ^ (6 * d ^ 2) := by ring
          _ ≤ (2 : ℝ) ^ 9 * (2 : ℝ) ^ (6 * d ^ 2) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity); norm_num
          _ = (2 : ℝ) ^ (6 * d ^ 2 + 9) := by rw [← pow_add]; congr 1; ring
          _ ≤ (2 : ℝ) ^ (C * d ^ 2) := pow_le_pow_right₀ (by norm_num) h15
      have hsum : (2 : ℝ) ^ (C * d ^ 2) * (1 / 2) + (2 : ℝ) ^ (C * d ^ 2) * (1 / 2)
          = (2 : ℝ) ^ (C * d ^ 2) := by ring
      linarith
    refine hstep.trans ?_
    refine (mul_le_mul_of_nonneg_right hcoef hS0).trans (le_of_eq ?_)
    rw [hSdef, sum_D4_eq_sum_D4_of_degLe hf]

/-- **Every `IHyp` level holds at the fixed constant `C`** as soon as `100 ≤ C`. -/
theorem forall_IHyp (C : ℕ) (hC : 100 ≤ C) : ∀ D, IHyp C D :=
  forall_IHyp_of_step C (fun d hd hIH => IHyp_step C hC d hd hIH) (IHyp_zero C)

/-- **Theorem 1.5** (the Bonami-type lemma for the bilinear scheme, arXiv:2209.04243). -/
theorem HypHyperUC_of_step : HypHyperUC :=
  HypHyperUC_of_IHyp 100 (by norm_num) (forall_IHyp 100 (by norm_num))

end
end Submission.Grassmann
