import Mathlib
import Submission.Work.Cert.aLoop_aux

namespace Work.Cert

open Complex

/-! ## Small helpers for the base case of the `A`-loop invariant -/

/-- `md 0 b = 0`: the mantissa product with a zero mantissa is exact. -/
lemma aInv_base_md_zero_left (b : ℤ) : md 0 b = 0 := by
  unfold md fdiv
  rw [zero_mul]
  exact Int.ediv_eq_of_eq_mul_left (by norm_num [S] : S ≠ 0) (by ring : (0 : ℤ) = 0 * S)

lemma aInv_base_S_ne_C : (S : ℂ) ≠ 0 := by
  have h : (S : ℤ) ≠ 0 := by norm_num [S]
  exact_mod_cast h

/-- `cx S 0 = 1`: the scale itself is the point `1` (used for the first step, where the mantissa
multiplication by `S` is exact). -/
lemma aInv_base_cx_S_zero : cx S 0 = 1 := by
  simp only [cx]
  push_cast
  rw [div_self aInv_base_S_ne_C]
  simp

/-- The first two partial sums of `thetaA`: `Asum q 2 = 1 + q`. -/
lemma aInv_base_Asum_two (q : ℂ) : Asum q (1 + 1) = 1 + q := by
  rw [Asum, Finset.sum_range_succ, Finset.sum_range_one]
  simp

lemma aInv_base_Bd_one : Bd 1 = 9 := by
  rw [Bd, Finset.sum_range_one]
  norm_num [tri]

lemma aInv_base_BdM_one (m rq : ℤ) : BdM m rq 1 = (rq : ℝ) := by
  rw [BdM, Finset.sum_range_one]
  simp [tri]

/-- Base case of the `A`-loop invariant: after the first step from the loop's initial state
`⟨S, 0, S, 0, S, 0, S, S, 0, 0⟩` (i.e. `1 + 0·i` in mantissa units, `T = 0`, budgets `0`) the
invariant `Work.Cert.AInv` (from `Submission.Work.Cert.ThetaDefs`) holds at index `1`.  Here the
roundings are exact (`md S x = x`, `mu S x = x`), the state after the step is `pn = pT = qc`,
`T = 1`, `mn = m+1`, `mT = m+2`, `Ar + i·Ai = 1 + qc`, `dA = mu (dvu (m+2) m) rq + 9`, and the only
inequality is `Bd 1 + BdM m rq 1 = 9 + rq ≤ mu (dvu (m+2) m) rq + 9`, which follows from `mu_ge'`
and `dvu_ge'` (i.e. `dvu (m+2) m ≥ (m+2)·S/m` and `mu x rq ≥ x·rq/S`) with `rq ≥ 0`, `m ≥ 1`. -/
theorem aInv_base
    (hcxmul : ∀ a b c d : ℤ, ‖Work.Cert.cx (Work.Cert.cmr a b c d) (Work.Cert.cmi a b c d) - Work.Cert.cx a b * Work.Cert.cx c d‖ ≤ 3 / ((Work.Cert.S : ℝ)))
    (qr qi rq m : ℤ) (hm : 1 ≤ m) (hrq : 0 ≤ rq) (hμ : Work.Cert.mub m ≤ 79 / 100) (hz : ‖Work.Cert.qc qr qi‖ ≤ Work.Cert.mub m) :
    Work.Cert.AInv qr qi rq m 1 (Work.Cert.aStep qr qi rq m 1 ⟨Work.Cert.S, 0, Work.Cert.S, 0, Work.Cert.S, 0, Work.Cert.S, Work.Cert.S, 0, 0⟩) := by
  -- the explicit state reached after the first step
  have hstep : aStep qr qi rq m 1 ⟨S, 0, S, 0, S, 0, S, S, 0, 0⟩ =
      ⟨qr, qi, qr, qi, S + qr, qi, m + 1, m + 2, mu (dvu (m + 2) m) rq + 9, 1⟩ := by
    simp only [aStep, cmr, cmi, md_S, mu_S, aInv_base_md_zero_left]
    norm_num
    refine ⟨by ring, ?_⟩
    rw [show m + 1 + 1 = m + 2 from by ring]
    ring
  rw [hstep]
  unfold AInv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `pn` error: `cx qr qi = qc qr qi` exactly
    have h : cx qr qi - (qc qr qi) ^ 1 = 0 := by rw [pow_one]; simp [qc]
    rw [h, norm_zero]
    exact div_nonneg (by norm_num) (le_of_lt thS_pos)
  · -- `pT` error: `tri 1 = 1`, so again exact
    have h : cx qr qi - (qc qr qi) ^ tri 1 = 0 := by rw [tri_one, pow_one]; simp [qc]
    rw [h, norm_zero]
    norm_num
  · -- `T = tri 1 = 1`
    norm_num
  · -- `mn = m+1 ≥ m/S`
    rw [pow_one, mub]
    push_cast
    rw [div_le_div_iff_of_pos_right thS_pos]
    linarith
  · -- `mT = m+2 ≥ m/S`
    rw [tri_one, pow_one, mub]
    push_cast
    rw [div_le_div_iff_of_pos_right thS_pos]
    linarith
  · -- `Bd 1 + BdM m rq 1 = 9 + rq ≤ mu (dvu (m+2) m) rq + 9`
    rw [aInv_base_Bd_one, aInv_base_BdM_one]
    push_cast
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show (0 : ℤ) < m by omega)
    have hrqR : (0 : ℝ) ≤ (rq : ℝ) := by exact_mod_cast hrq
    have hdS : (S : ℝ) ≤ ((dvu (m + 2) m : ℤ) : ℝ) := by
      have h := dvu_ge' (m + 2) m (show (0 : ℤ) < m by omega)
      have h2 : (S : ℝ) ≤ ((m + 2 : ℤ) : ℝ) * (S : ℝ) / (m : ℝ) := by
        rw [le_div_iff₀ hmR]
        push_cast
        nlinarith [thS_pos, hmR]
      linarith
    have key : (rq : ℝ) ≤ ((dvu (m + 2) m : ℤ) : ℝ) * (rq : ℝ) / (S : ℝ) := by
      have h1 : (S : ℝ) * (rq : ℝ) ≤ ((dvu (m + 2) m : ℤ) : ℝ) * (rq : ℝ) :=
        mul_le_mul_of_nonneg_right hdS hrqR
      rw [le_div_iff₀ thS_pos]
      nlinarith [h1]
    have hmu := mu_ge' (dvu (m + 2) m) rq
    linarith
  · -- `Ar + i·Ai = 1 + qc = Asum (qc) 2`
    rw [aInv_base_Bd_one]
    have hx : cx (S + qr) qi - Asum (qc qr qi) (1 + 1) = 0 := by
      rw [aInv_base_Asum_two]
      have h1 := cx_add S 0 qr qi
      rw [show (0 : ℤ) + qi = qi from by ring] at h1
      rw [h1, aInv_base_cx_S_zero]
      simp only [qc]
      ring
    rw [hx, norm_zero]
    exact div_nonneg (by norm_num) (le_of_lt thS_pos)

end Work.Cert
