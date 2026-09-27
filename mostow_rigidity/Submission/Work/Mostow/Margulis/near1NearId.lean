import Mathlib
import Submission.Work.Mostow.margulisCuspDefs
import Submission.Work.Mostow.abs_mat_le_tpart_actO
import Submission.Work.Mostow.hlift_entry_le_cosh_one
import Submission.Mostow.HLDefs

open scoped _root_.Matrix

namespace Work.Mostow.Margulis

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- **Entrywise nearness to `1` implies near-identity at the base point.** If the sheet-preserving
lift `ToO g` of `g : PO n 1` has all matrix entries within `q` of the identity matrix, then `g`
moves every point of the closed unit ball of the chart around `0` by less than `η`, provided `q`
is small enough (depending only on `n` and `η`).

Proof sketch. For `hdist 0 u ≤ 1` write `x = hlift u` and `y = hlift (g • u) = mat (ToO g) *ᵥ x`
(`hlift_LambdaMat`, `mat_ToO`). `x` has all coordinates bounded by `cosh 1`
(`|u i| ≤ ‖u‖ = sinh (hdist 0 u) ≤ sinh 1 ≤ cosh 1` and `tpart u = cosh (hdist 0 u) ≤ cosh 1`),
and `(y - x) k = ∑ j, (mat (ToO g) k j - dE k j) * x j` has absolute value at most
`(n+1) * q * cosh 1`. Since `mform (hlift w) (hlift w) = -1` for all `w` and
`cosh (hdist u v) = -mform (hlift u) (hlift v)` (`cosh_hdist`, `mform_hlift_self`), bilinearity of
`mform` gives `2 * (cosh (hdist u (g • u)) - 1) = mform (y - x) (y - x) ≤ C q²`, so
`hdist u (g • u) ≤ arcosh (1 + C q²) ≤ sqrt (2C) q` once `C q² ≤ 1`; take `q < η / sqrt (2C)`. -/
theorem near1NearId (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) :
    ∀ η : ℝ, 0 < η → ∃ q : ℝ, 0 < q ∧ ∀ g : PO n 1, Near1 (ToO g) q → NearIdAt g (0 : E n) η := by
  intro η hη
  -- the constants
  set M : ℝ := msz n * Real.cosh 1 with hM
  set C : ℝ := msz n * M ^ 2 with hC
  have hMpos : 0 < M := by
    rw [hM]
    have h1 : (0 : ℝ) < msz n := lt_of_lt_of_le zero_lt_one (one_le_msz n)
    have h2 : (0 : ℝ) < Real.cosh 1 := Real.cosh_pos 1
    positivity
  have hCpos : 0 < C := by
    rw [hC]
    exact mul_pos (lt_of_lt_of_le zero_lt_one (one_le_msz n)) (pow_pos hMpos 2)
  have hcoshη : 1 < Real.cosh η := by
    rw [Real.one_lt_cosh]; exact ne_of_gt hη
  have hnum : 0 < (Real.cosh η - 1) / C := by
    exact div_pos (by linarith) hCpos
  -- the threshold
  set q0 : ℝ := min 1 (Real.sqrt ((Real.cosh η - 1) / C)) with hq0
  have hq0pos : 0 < q0 := by
    rw [hq0]; exact lt_min one_pos (Real.sqrt_pos.2 hnum)
  have hq0nonneg : 0 ≤ q0 := le_of_lt hq0pos
  have hq0le : q0 ≤ Real.sqrt ((Real.cosh η - 1) / C) := by
    rw [hq0]; exact min_le_right _ _
  refine ⟨q0, hq0pos, ?_⟩
  intro g hg u hu
  -- every coordinate of `hlift u` is bounded by `cosh 1`
  have hxu : ∀ k : Fin n ⊕ Fin 1, |hlift u k| ≤ Real.cosh 1 :=
    hlift_entry_le_cosh_one hu
  -- the difference `hlift (g • u) - hlift u`
  have hy : hlift (g • u) = mat (ToO g) *ᵥ hlift u := by
    rw [hlift_LambdaMat hA g u, mat_ToO]
  have hz : ∀ k : Fin n ⊕ Fin 1, |(hlift (g • u) - hlift u) k| ≤ M * q0 := by
    intro k
    have hzk : (hlift (g • u) - hlift u) k
        = ∑ j, (mat (ToO g) k j - dE n k j) * hlift u j := by
      rw [hy]
      rw [Pi.sub_apply,
        show (mat (ToO g) *ᵥ hlift u) k = ∑ j, mat (ToO g) k j * hlift u j from rfl,
        show hlift u k = ∑ j, dE n k j * hlift u j from ?_]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
      rw [Finset.sum_eq_single k]
      · rw [dE_self, one_mul]
      · intro b _ hb; rw [dE_ne (fun h => hb h.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [hzk]
    calc |∑ j, (mat (ToO g) k j - dE n k j) * hlift u j|
        ≤ ∑ j, |(mat (ToO g) k j - dE n k j) * hlift u j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n ⊕ Fin 1, q0 * Real.cosh 1 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hg k j) (hxu j) (abs_nonneg _) hq0nonneg
      _ = M * q0 := by
          rw [sum_const_sum]; simp only [hM]; ring
  -- the Minkowski form of the difference
  have hmfz : mform (hlift (g • u) - hlift u) (hlift (g • u) - hlift u)
      = 2 * (Real.cosh (hdist u (g • u)) - 1) := by
    have hxy : mform (hlift u) (hlift (g • u)) = - Real.cosh (hdist u (g • u)) := by
      rw [mform_hlift_hlift, cosh_hdist]; ring
    rw [mform_sub_left, mform_sub_right, mform_sub_right, mform_hlift_self (g • u),
      mform_hlift_self u, mform_comm (hlift (g • u)) (hlift u), hxy]
    ring
  -- bound the form by the entrywise bound
  have hbound : 2 * (Real.cosh (hdist u (g • u)) - 1) ≤ msz n * (M * q0) ^ 2 := by
    rw [← hmfz, mform_self_apply]
    have hsum : (∑ i : Fin n, (hlift (g • u) - hlift u) (Sum.inl i) ^ 2)
        ≤ ∑ _i : Fin n, (M * q0) ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hh := hz (Sum.inl i)
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg (le_of_lt hMpos) hq0nonneg)]
      exact hh
    calc (∑ i : Fin n, (hlift (g • u) - hlift u) (Sum.inl i) ^ 2)
            - (hlift (g • u) - hlift u) (Sum.inr 0) ^ 2
        ≤ ∑ i : Fin n, (hlift (g • u) - hlift u) (Sum.inl i) ^ 2 := by
          have := sq_nonneg ((hlift (g • u) - hlift u) (Sum.inr 0)); linarith
      _ ≤ ∑ _i : Fin n, (M * q0) ^ 2 := hsum
      _ = (n : ℝ) * (M * q0) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ msz n * (M * q0) ^ 2 := by
          have h0 : (0 : ℝ) ≤ (M * q0) ^ 2 := sq_nonneg _
          have h1 : (n : ℝ) ≤ msz n := by simp only [msz]; linarith
          exact mul_le_mul_of_nonneg_right h1 h0
  -- the two elementary bounds on `q0`
  have hq0sq : q0 ^ 2 ≤ (Real.cosh η - 1) / C := by
    calc q0 ^ 2 = q0 * q0 := by ring
      _ ≤ (Real.sqrt ((Real.cosh η - 1) / C)) * (Real.sqrt ((Real.cosh η - 1) / C)) :=
          mul_self_le_mul_self hq0nonneg hq0le
      _ = (Real.cosh η - 1) / C := Real.mul_self_sqrt (le_of_lt hnum)
  have hCq : C * q0 ^ 2 ≤ Real.cosh η - 1 := by
    have h := mul_le_mul_of_nonneg_left hq0sq (le_of_lt hCpos)
    have h2 : C * ((Real.cosh η - 1) / C) = Real.cosh η - 1 := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ (Real.cosh η - 1) (ne_of_gt hCpos)]
    linarith [h, h2]
  have hCsq : msz n * (M * q0) ^ 2 = C * q0 ^ 2 := by rw [hC]; ring
  have hCd : Real.cosh (hdist u (g • u)) ≤ (Real.cosh η + 1) / 2 := by
    linarith [hbound, hCsq, hCq]
  -- conclude
  have hlt : Real.cosh (hdist u (g • u)) < Real.cosh η := by linarith [hCd, hcoshη]
  have hlt2 := Real.cosh_lt_cosh.mp hlt
  rwa [abs_of_nonneg (hdist_nonneg u (g • u)), abs_of_pos hη] at hlt2

end Work.Mostow.Margulis
