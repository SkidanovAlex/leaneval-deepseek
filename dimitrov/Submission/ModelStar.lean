import Mathlib
import Submission.KLCloseB

/-!
# Model-star bridge: KL gives the 4^(1/s) lower bound on the unit-circle max

In the Eremenko/vIRZ representation of a capacity-1 hedgehog, the model map is

    F(z) = ∏_j ((z − z_j)·(z^{-1} − z̄_j))^{r_j},        Σ_j r_j = 1,

on |z| > 1; on the unit circle |F(z)| = ∏_j |z − z_j|^(2 r_j) and the spike
lengths are the arc maxima of |F|.  The present module records the *analytic
content* that is used at the end of the Eremenko route (and needs no conformal
machinery): for any `s` unit points `z_j` and weights `r_j ≥ 0` with `Σ r_j = 1`,
some point `w` of the unit circle satisfies

    (4 : ℝ) ^ (1 / s) ≤ ∏_j ‖w − z_j‖ ^ (2 * r_j).

This is a direct consequence of the verified Konyagin–Lev circle inequality
(`Submission.KLMain.koniagin_lev_circle`) applied to the weights `p_j := s·r_j`
(Σ p_j = s = number of points): KL gives ∏_j ‖w−z_j‖^(s·r_j) ≥ 2; taking the
`s`-th root gives ∏_j ‖w−z_j‖^(r_j) ≥ 2^(1/s), and squaring gives the claim.

Statement: `max_product_ge_four_rpow_inv`.
-/

noncomputable section

open scoped Real BigOperators
open Filter

namespace Submission.ModelStar

open Submission.KLMain

/-- Real `rpow` distributes over finite products of nonnegative factors. -/
private lemma rpow_prod_eq_prod_rpow {ι : Type*} [Fintype ι] (f : ι → ℝ) (z : ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    (∏ i : ι, f i) ^ z = ∏ i : ι, (f i) ^ z := by
  classical
  have main : ∀ s : Finset ι, (∏ i ∈ s, f i) ^ z = ∏ i ∈ s, (f i) ^ z := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp [Real.one_rpow]
    · intro a s has ih
      rw [Finset.prod_insert has, Real.mul_rpow (hf a) (Finset.prod_nonneg (fun i hi => hf i)), ih]
      rw [Finset.prod_insert has]
  simpa using main Finset.univ

/-- **Model-star bridge.**  For `s ≥ 1` unit circle points `z_j` and nonnegative
weights `r_j` summing to `1`, some unit `w` satisfies
`4^(1/s) ≤ ∏_j ‖w − z_j‖^(2·r_j)`. -/
theorem max_product_ge_four_rpow_inv (s : ℕ) (hs : 0 < s)
    (z : Fin s → ℂ) (hz : ∀ j : Fin s, ‖z j‖ = 1)
    (r : Fin s → ℝ) (hr : ∀ j : Fin s, 0 ≤ r j)
    (hsum : (∑ j : Fin s, r j) = 1) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      (4 : ℝ) ^ (1 / (s : ℝ)) ≤ ∏ j : Fin s, ‖w - z j‖ ^ (2 * r j) := by
  classical
  have hsRpos : 0 < (s : ℝ) := by exact_mod_cast hs
  have hsR0 : (s : ℝ) ≠ 0 := ne_of_gt hsRpos
  have hz2 : 0 ≤ 2 / (s : ℝ) := div_nonneg (by norm_num) (le_of_lt hsRpos)
  -- weights p_j := s·r_j sum to s
  let p : Fin s → ℝ := fun j => (s : ℝ) * r j
  have hp0 : ∀ j : Fin s, 0 ≤ p j := by
    intro j
    dsimp [p]
    exact mul_nonneg (le_of_lt hsRpos) (hr j)
  have hpsum : (∑ j : Fin s, p j) = (s : ℝ) := by
    dsimp [p]
    rw [← Finset.mul_sum]
    rw [hsum]
    simp
  -- KL on the circle with weights p
  rcases koniagin_lev_circle s hs z p hz hp0 hpsum with ⟨w, hw, hprod⟩
  refine ⟨w, hw, ?_⟩
  -- hprod : 2 ≤ ∏ ‖w - z j‖ ^ p j ; raise to the power 2/s
  have hineq : (2 : ℝ) ^ (2 / (s : ℝ)) ≤
      (∏ j : Fin s, ‖w - z j‖ ^ p j) ^ (2 / (s : ℝ)) := by
    exact Real.rpow_le_rpow (by norm_num : 0 ≤ (2 : ℝ)) hprod hz2
  -- equality: (∏ ‖w-z j‖^p j)^(2/s) = ∏ ‖w-z j‖^(2·r j)
  have hpow : (∏ j : Fin s, ‖w - z j‖ ^ p j) ^ (2 / (s : ℝ)) =
      ∏ j : Fin s, ‖w - z j‖ ^ (2 * r j) := by
    rw [rpow_prod_eq_prod_rpow (fun j : Fin s => ‖w - z j‖ ^ p j) (2 / (s : ℝ))
      (fun j => Real.rpow_nonneg (norm_nonneg (w - z j)) (p j))]
    apply Finset.prod_congr rfl
    intro j hj
    rw [← Real.rpow_mul (norm_nonneg (w - z j))]
    congr 1
    dsimp [p]
    field_simp [hsR0]
  -- 4^(1/s) = 2^(2/s)
  have h4eq : (4 : ℝ) ^ (1 / (s : ℝ)) = (2 : ℝ) ^ (2 / (s : ℝ)) := by
    rw [show (4 : ℝ) = (2 : ℝ) * (2 : ℝ) by norm_num]
    rw [Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) (by norm_num : 0 ≤ (2 : ℝ))]
    rw [← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
    congr 1
    ring
  calc
    (4 : ℝ) ^ (1 / (s : ℝ)) = (2 : ℝ) ^ (2 / (s : ℝ)) := h4eq
    _ ≤ (∏ j : Fin s, ‖w - z j‖ ^ p j) ^ (2 / (s : ℝ)) := hineq
    _ = ∏ j : Fin s, ‖w - z j‖ ^ (2 * r j) := hpow

end Submission.ModelStar

end
