import Submission.CompQNums
import Submission.Bclps

/-!
# Pointwise perturbation bound for the complementary polynomial

Helper for `Submission/CompQRoots.lean`.  With `Q0 = ∏_{j'<D} (T − c_{r,j'})`,
`Q1 = Q0 + Σ_{1≤t≤d} ε_t·auxPoly t` (`d = (D−1)r`, `|ε_t| < 2`,
`|auxPoly t| ≤ 2κ^t` on the interval) and `Q = Q1 + N` (`0 ≤ N ≤ 2·C2val⁻¹·κ^{Dr}`),
the pointwise gap between `Q` and `Q0` on the Serre interval is
`≤ κ^{Dr}·(4/((κ−1)·κ^{r−1}) + 2·C2val⁻¹)`.
-/

noncomputable section

open scoped Real BigOperators
open Polynomial

namespace Submission.CompQpert

open Submission.SerreExample
open Submission.ChebSerre
open Submission.AdjustedCheb
open Submission.Bclps
open Submission.DivLinear
open Submission.CompQNums

/-- the auxiliary-degree `d = (D−1)·r` (same as in `CompQRoots`). -/
def d (r : ℕ) : ℕ := (Bclps.Dconst - 1) * r

/-- κ > 1. -/
lemma kappa_gt_one : (1 : ℝ) < kappaC := ChebSerre.kappaC_gt_one

/-- κ − 1 > 0. -/
lemma kappa_sub_one_pos : 0 < kappaC - 1 := by
  have h := kappa_gt_one
  linarith

/-- κ > 0. -/
lemma kappa_pos : 0 < kappaC := by
  have h := kappa_gt_one
  linarith

/-- geometric bound over an interval `[1,n]`: `Σ_{t=1}^n κ^t ≤ κ^{n+1}/(κ−1)`. -/
lemma geom_Icc_sum_le (n : ℕ) :
    (∑ t ∈ Finset.Icc 1 n, kappaC ^ t) ≤ kappaC ^ (n + 1) / (kappaC - 1) := by
  induction' n with n ih
  · have hpos : 0 < kappaC - 1 := kappa_sub_one_pos
    simp
    exact le_of_lt (div_pos kappa_pos hpos)
  · calc
      (∑ t ∈ Finset.Icc 1 (n + 1), kappaC ^ t)
          = (∑ t ∈ Finset.Icc 1 n, kappaC ^ t) + kappaC ^ (n + 1) := by
              rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ n + 1)]
      _ ≤ kappaC ^ (n + 1) / (kappaC - 1) + kappaC ^ (n + 1) := by
              exact add_le_add ih (le_rfl)
      _ = kappaC ^ (n + 2) / (kappaC - 1) := by
              have hne : kappaC - 1 ≠ 0 := ne_of_gt kappa_sub_one_pos
              have hpown : kappaC ^ (n + 1) * kappaC = kappaC ^ (n + 2) := by
                rw [← pow_succ (kappaC) (n + 1)]
              rw [← hpown]
              field_simp [hne]
              ring

/-- geometric bound for the ε-perturbation:
`Σ_{1≤t≤d} 4·κ^t ≤ κ^{Dr}·4/((κ−1)·κ^{r−1})`. -/
lemma sum_aux_bound (r : ℕ) :
    (∑ t ∈ Finset.Icc 1 (d r), 4 * kappaC ^ t) ≤
      kappaC ^ (Bclps.Dconst * r) * (4 / ((kappaC - 1) * kappaC ^ (r - 1))) := by
  by_cases hr0 : r = 0
  · subst r
    have hsub : ((0 : ℕ) - 1) = 0 := by omega
    simp [d, hsub]
    exact div_nonneg (by norm_num) (le_of_lt kappa_sub_one_pos)
  · have hr1 : 1 ≤ r := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hr0)
    have hne : kappaC - 1 ≠ 0 := ne_of_gt kappa_sub_one_pos
    have hpowne : kappaC ^ (r - 1) ≠ 0 := pow_ne_zero (r - 1) (ne_of_gt kappa_pos)
    have hgeo := geom_Icc_sum_le (d r)
    calc
      (∑ t ∈ Finset.Icc 1 (d r), 4 * kappaC ^ t)
          = 4 * (∑ t ∈ Finset.Icc 1 (d r), kappaC ^ t) := by
              rw [Finset.mul_sum]
      _ ≤ 4 * (kappaC ^ ((d r) + 1) / (kappaC - 1)) := by
              exact mul_le_mul_of_nonneg_left hgeo (by norm_num)
      _ = kappaC ^ (Bclps.Dconst * r) * (4 / ((kappaC - 1) * kappaC ^ (r - 1))) := by
              have hnat : (d r) + 1 + (r - 1) = Bclps.Dconst * r := by
                unfold d
                have hD : Bclps.Dconst = (Bclps.Dconst - 1) + 1 := by
                  have hdp : 1 ≤ Bclps.Dconst := Bclps.Dconst_pos
                  omega
                calc
                  (Bclps.Dconst - 1) * r + 1 + (r - 1)
                      = (Bclps.Dconst - 1) * r + (1 + (r - 1)) := by omega
                  _ = (Bclps.Dconst - 1) * r + r := by
                      congr 1
                      omega
                  _ = ((Bclps.Dconst - 1) + 1) * r := by rw [add_mul, one_mul]
                  _ = Bclps.Dconst * r := by rw [← hD]
              have hDr : kappaC ^ (Bclps.Dconst * r) =
                  kappaC ^ ((d r) + 1) * kappaC ^ (r - 1) := by
                rw [← hnat]
                rw [pow_add]
              rw [hDr]
              field_simp [hne, hpowne]

/-- **Pointwise closeness of `Q` and `Q0` on the Serre interval.** -/
theorem pert_bound_total (r : ℕ) {Q0 Q1 Q : Polynomial ℝ} (eps : ℕ → ℝ) (N : ℝ)
    (hQ1 : Q1 = Q0 + (∑ t ∈ Finset.Icc 1 (d r), Polynomial.C (eps t) * Bclps.auxPoly t))
    (hQ : Q = Q1 + Polynomial.C N)
    (heps : ∀ t : ℕ, t ∈ Finset.Icc 1 (d r) → |eps t| < 2)
    (hN : 0 ≤ N) (hNle : N ≤ 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r))
    {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    |Q.eval x - Q0.eval x| ≤ kappaC ^ (Bclps.Dconst * r) *
      (4 / ((kappaC - 1) * kappaC ^ (r - 1)) + 2 * C2val⁻¹) := by
  let S : Polynomial ℝ := ∑ t ∈ Finset.Icc 1 (d r), Polynomial.C (eps t) * Bclps.auxPoly t
  let valS : ℝ := ∑ t ∈ Finset.Icc 1 (d r), (eps t) * (Bclps.auxPoly t).eval x
  have hQ' : Q = Q0 + S + Polynomial.C N := by
    dsimp [S]
    rw [hQ, hQ1]
  have heval : Q.eval x - Q0.eval x = N + valS := by
    rw [hQ']
    dsimp [S, valS]
    simp [Polynomial.eval_add, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  have htri : |Q.eval x - Q0.eval x| ≤ N + |valS| := by
    rw [heval]
    calc
      |N + valS| ≤ |N| + |valS| := abs_add_le N valS
      _ = N + |valS| := by rw [abs_of_nonneg hN]
  have hsumabs : |valS| ≤ (∑ t ∈ Finset.Icc 1 (d r), 4 * kappaC ^ t) := by
    dsimp [valS]
    calc
      |∑ t ∈ Finset.Icc 1 (d r), (eps t) * (Bclps.auxPoly t).eval x|
          ≤ ∑ t ∈ Finset.Icc 1 (d r), |(eps t) * (Bclps.auxPoly t).eval x| :=
              Finset.abs_sum_le_sum_abs (fun t => (eps t) * (Bclps.auxPoly t).eval x)
                (Finset.Icc 1 (d r))
      _ ≤ ∑ t ∈ Finset.Icc 1 (d r), 4 * kappaC ^ t := by
          apply Finset.sum_le_sum
          intro t ht
          have hepsle : |eps t| ≤ 2 := le_of_lt (heps t ht)
          have hA : |(Bclps.auxPoly t).eval x| ≤ 2 * kappaC ^ t := by
            exact le_trans (DivLinear.abs_eval_le_supNorm (P := Bclps.auxPoly t) x hx)
              (Bclps.auxPoly_supNorm_le t)
          have hnonnegA : 0 ≤ 2 * kappaC ^ t := by
            exact mul_nonneg (by norm_num) (pow_nonneg (le_of_lt kappa_pos) t)
          calc
            |(eps t) * (Bclps.auxPoly t).eval x|
                = |eps t| * |(Bclps.auxPoly t).eval x| := by rw [abs_mul]
            _ ≤ |eps t| * (2 * kappaC ^ t) := mul_le_mul_of_nonneg_left hA (abs_nonneg _)
            _ ≤ 2 * (2 * kappaC ^ t) := mul_le_mul_of_nonneg_right hepsle hnonnegA
            _ = 4 * kappaC ^ t := by ring
  have hmain : |Q.eval x - Q0.eval x| ≤
      N + (∑ t ∈ Finset.Icc 1 (d r), 4 * kappaC ^ t) := by
    calc
      |Q.eval x - Q0.eval x| ≤ N + |valS| := htri
      _ ≤ N + (∑ t ∈ Finset.Icc 1 (d r), 4 * kappaC ^ t) := add_le_add_right hsumabs N
  calc
    |Q.eval x - Q0.eval x|
        ≤ N + (∑ t ∈ Finset.Icc 1 (d r), 4 * kappaC ^ t) := hmain
    _ ≤ N + kappaC ^ (Bclps.Dconst * r) * (4 / ((kappaC - 1) * kappaC ^ (r - 1))) := by
        exact add_le_add_right (sum_aux_bound r) N
    _ ≤ kappaC ^ (Bclps.Dconst * r) * (2 * C2val⁻¹) +
        kappaC ^ (Bclps.Dconst * r) * (4 / ((kappaC - 1) * kappaC ^ (r - 1))) := by
        have hNle' : N ≤ kappaC ^ (Bclps.Dconst * r) * (2 * C2val⁻¹) := by
          calc
            N ≤ 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := hNle
            _ = kappaC ^ (Bclps.Dconst * r) * (2 * C2val⁻¹) := by ring
        exact add_le_add hNle' (le_rfl)
    _ = kappaC ^ (Bclps.Dconst * r) *
        (4 / ((kappaC - 1) * kappaC ^ (r - 1)) + 2 * C2val⁻¹) := by
        ring

end Submission.CompQpert
