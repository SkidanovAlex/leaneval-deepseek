import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmCz.abs_eucNorm_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.cz_num_core
import Submission.Work.CR.Flat.Cauchy.bmCz.cz_real_core
import Submission.Work.CR.Flat.Cauchy.bmCz.norm_bmDzKernel_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.dCoord_bmKernel
import Submission.Work.CR.Flat.Cauchy.bmCz.hasFDerivAt_bmKernel
import Submission.Work.CR.Flat.Cauchy.bmCz.inv_pow_sub_inv_pow_bound
import Submission.Work.CR.Flat.Cauchy.bmCz.cz_num_diff_bound

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy.bmCz

open Work.CR.Flat.Cauchy

/-- The antilinear kernel `∂_{\bar z_k}` of `bmKernel j`, written with the numerator
`\bar z_k z_j` collected as a single factor. -/
lemma bmDbarKernel_eq {n : ℕ} (j k : Fin n) (z : Fin n → ℂ) : bmDbarKernel j k z =
    (if j = k then (1:ℂ) else 0) / ((eucNorm z : ℂ) ^ (2*n))
      - (n : ℂ) * (starRingEnd ℂ (z k) * z j) / ((eucNorm z : ℂ) ^ (2*n+2)) := by
  simp only [bmDbarKernel]; ring

/-- Calderón–Zygmund kernel-difference estimate for `∂_{\bar z_k}(bmKernel j)`.

This is the antiholomorphic companion of `norm_bmDzKernel_sub_le`: the kernel
`bmDbarKernel j k x = δ_{jk} ‖x‖^{-2n} - n \bar x_k x_j ‖x‖^{-2n-2}` is smooth off the
origin and its difference is bounded by `C ‖h‖ / ‖x‖^{2n+1}` whenever `2‖h‖ ≤ ‖x‖`. -/
theorem norm_bmDbarKernel_sub_le {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j k : Fin n) (x h : Fin n → ℂ), 2 * eucNorm h ≤ eucNorm x →
      ‖bmDbarKernel j k (x - h) - bmDbarKernel j k x‖
        ≤ C * eucNorm h / (eucNorm x) ^ (2 * n + 1) := by
  refine ⟨((2*n:ℕ):ℝ) * (3/2)^(2*n-1) * 2^(2*n)
      + (n:ℝ) * (5/2 + ((2*n+2:ℕ):ℝ) * (3/2)^((2*n+2)-1) * 2^((2*n+2)-2)) + 1, ?_, ?_⟩
  · positivity
  · intro j k x h hxh
    rcases eq_or_lt_of_le (eucNorm_nonneg x) with hX0 | hXpos
    · -- degenerate case `x = 0`
      have hx0 : x = 0 := eucNorm_eq_zero.mp hX0.symm
      have hH0 : eucNorm h = 0 := by
        have h2 := hxh; rw [← hX0] at h2; linarith [eucNorm_nonneg h]
      have hh0 : h = 0 := eucNorm_eq_zero.mp hH0
      rw [hh0, hx0]
      simp only [sub_zero, eucNorm_zero]
      rw [sub_self, norm_zero, mul_zero, zero_div]
    · -- main case `x ≠ 0`
      set Cd : ℝ := ((2*n:ℕ):ℝ) * (3/2)^(2*n-1) * 2^(2*n) with hCddef
      set Cz : ℝ := 5/2 + ((2*n+2:ℕ):ℝ) * (3/2)^((2*n+2)-1) * 2^((2*n+2)-2) with hCzdef
      set X := eucNorm x with hXdef
      set H := eucNorm h with hHdef
      set Y := eucNorm (x - h) with hYdef
      have hXpos' : 0 < X := by rw [hXdef]; exact hXpos
      have hHnn : 0 ≤ H := by rw [hHdef]; exact eucNorm_nonneg h
      have h2HY : 2 * H ≤ X := hxh
      have htri : |X - Y| ≤ H := by
        rw [hXdef, hYdef, hHdef]
        have hsub : x - (x - h) = h := by abel
        simpa [hsub] using abs_eucNorm_sub_le x (x - h)
      have hXYle : X - Y ≤ H := (abs_le.mp htri).2
      have hXYge : -H ≤ X - Y := (abs_le.mp htri).1
      have hYge : X / 2 ≤ Y := by linarith
      have hYpos : 0 < Y := by linarith
      have hYu : 2 * Y ≤ 3 * X := by linarith
      have hYe : X ≤ 2 * Y := by linarith
      -- the numerator `\bar x_k x_j` of the singular part and its shifted analogue
      set A2 : ℂ := starRingEnd ℂ (x k) * x j with hA2def
      set B2 : ℂ := starRingEnd ℂ ((x - h) k) * (x - h) j with hB2def
      have hA2_le : ‖A2‖ ≤ X ^ 2 := by
        rw [hA2def, norm_mul]
        have h1 : ‖starRingEnd ℂ (x k)‖ ≤ X := by
          rw [Complex.norm_conj, hXdef]; exact norm_apply_le_eucNorm' x k
        have h2 : ‖x j‖ ≤ X := by rw [hXdef]; exact norm_apply_le_eucNorm' x j
        calc ‖starRingEnd ℂ (x k)‖ * ‖x j‖ ≤ X * X :=
              mul_le_mul h1 h2 (norm_nonneg _) hXpos'.le
          _ = X ^ 2 := by ring
      have hB2_le : ‖B2‖ ≤ Y ^ 2 := by
        rw [hB2def, norm_mul]
        have h1 : ‖starRingEnd ℂ ((x - h) k)‖ ≤ Y := by
          rw [Complex.norm_conj, hYdef]; exact norm_apply_le_eucNorm' (x - h) k
        have h2 : ‖(x - h) j‖ ≤ Y := by rw [hYdef]; exact norm_apply_le_eucNorm' (x - h) j
        calc ‖starRingEnd ℂ ((x - h) k)‖ * ‖(x - h) j‖ ≤ Y * Y :=
              mul_le_mul h1 h2 (norm_nonneg _) hYpos.le
          _ = Y ^ 2 := by ring
      have hAB_le : ‖A2 - B2‖ ≤ (5/2) * X * H := by
        have hfac : A2 - B2 = (starRingEnd ℂ (x k) - starRingEnd ℂ ((x - h) k)) * (x - h) j
            + starRingEnd ℂ (x k) * (x j - (x - h) j) := by
          rw [hA2def, hB2def]; ring
        have e1 : ‖starRingEnd ℂ (x k) - starRingEnd ℂ ((x - h) k)‖ ≤ H := by
          have hconj : starRingEnd ℂ (x k) - starRingEnd ℂ ((x - h) k) = starRingEnd ℂ (h k) := by
            rw [← map_sub]; congr 1; simp [Pi.sub_apply]
          rw [hconj, Complex.norm_conj, hHdef]
          exact norm_apply_le_eucNorm' h k
        have e2 : ‖(x - h) j‖ ≤ 3 * X / 2 := by
          calc ‖(x - h) j‖ ≤ eucNorm (x - h) := norm_apply_le_eucNorm' (x - h) j
            _ = Y := hYdef.symm
            _ ≤ 3 * X / 2 := by linarith
        have e3 : ‖starRingEnd ℂ (x k)‖ ≤ X := by
          rw [Complex.norm_conj, hXdef]; exact norm_apply_le_eucNorm' x k
        have e4 : ‖x j - (x - h) j‖ ≤ H := by
          have hsub2 : x j - (x - h) j = h j := by rw [Pi.sub_apply]; ring
          rw [hsub2, hHdef]; exact norm_apply_le_eucNorm' h j
        rw [hfac]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        refine (add_le_add (mul_le_mul e1 e2 (norm_nonneg _) hHnn)
          (mul_le_mul e3 e4 (norm_nonneg _) hXpos'.le)).trans ?_
        have hfin : H * (3 * X / 2) + X * H = (5/2) * X * H := by ring
        linarith
      set w : ℂ := (1:ℂ) / ((eucNorm (x - h) : ℂ) ^ (2*n)) - (1:ℂ) / ((eucNorm x : ℂ) ^ (2*n)) with hwdef
      set v : ℂ := B2 / ((eucNorm (x - h) : ℂ) ^ (2*n+2)) - A2 / ((eucNorm x : ℂ) ^ (2*n+2)) with hvdef
      have hker : bmDbarKernel j k (x - h) - bmDbarKernel j k x
          = (if j = k then (1:ℂ) else 0) * w - (n:ℂ) * v := by
        rw [bmDbarKernel_eq (n:=n) j k (x-h), bmDbarKernel_eq (n:=n) j k x, ← hA2def, ← hB2def,
          hwdef, hvdef]
        ring
      -- bound on the diagonal (identity) part
      have hdiag : ‖(if j = k then (1:ℂ) else 0) * w‖ ≤ Cd * H / X ^ (2*n+1) := by
        have hw : ‖w‖ = |1 / Y^(2*n) - 1 / X^(2*n)| := by
          have h1 : w = (((1:ℝ)/Y^(2*n) - 1/X^(2*n) : ℝ) : ℂ) := by
            rw [hwdef]
            have ha : (1:ℂ) / ((eucNorm (x-h):ℂ)^(2*n)) = (((1:ℝ)/Y^(2*n):ℝ):ℂ) := by
              rw [← hYdef, ← Complex.ofReal_pow,
                show (1:ℂ) = ((1:ℝ):ℂ) from Complex.ofReal_one.symm, ← Complex.ofReal_div]
            have hb : (1:ℂ) / ((eucNorm x:ℂ)^(2*n)) = (((1:ℝ)/X^(2*n):ℝ):ℂ) := by
              rw [← hXdef, ← Complex.ofReal_pow,
                show (1:ℂ) = ((1:ℝ):ℂ) from Complex.ofReal_one.symm, ← Complex.ofReal_div]
            rw [ha, hb, ← Complex.ofReal_sub]
          rw [h1, Complex.norm_real, Real.norm_eq_abs]
        have hbound := inv_pow_sub_inv_pow_bound (m := 2*n) (by omega) hXpos' hYpos hHnn htri hYe hYu
        calc ‖(if j = k then (1:ℂ) else 0) * w‖
            = ‖(if j = k then (1:ℂ) else 0)‖ * ‖w‖ := norm_mul _ _
          _ ≤ 1 * ‖w‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              split_ifs <;> simp
          _ = ‖w‖ := by ring
          _ = |1 / Y^(2*n) - 1 / X^(2*n)| := hw
          _ ≤ Cd * H / X ^ (2*n+1) := by rw [hCddef]; exact hbound
      -- bound on the singular (rational) part
      have hoff : ‖(n:ℂ) * v‖ ≤ ((n:ℝ) * Cz) * H / X ^ (2*n+1) := by
        rw [norm_mul]
        have hnc : ‖(n:ℂ)‖ = (n:ℝ) := by simp
        rw [hnc]
        have hv : ‖v‖ = ‖A2 / ((X:ℂ)^(2*n+2)) - B2 / ((Y:ℂ)^(2*n+2))‖ := by
          rw [hvdef]
          have hsym : B2 / ((eucNorm (x-h):ℂ)^(2*n+2)) - A2 / ((eucNorm x:ℂ)^(2*n+2))
              = -(A2 / ((eucNorm x:ℂ)^(2*n+2)) - B2 / ((eucNorm (x-h):ℂ)^(2*n+2))) := by ring
          rw [hsym, norm_neg, ← hXdef, ← hYdef]
        rw [hv]
        have hm2 : 2 ≤ 2*n+2 := by omega
        have hcz := cz_num_diff_bound (m := 2*n+2) hm2 hXpos' hYpos hHnn htri hYe hYu hB2_le hAB_le
        rw [show 2*n+2-1 = 2*n+1 from by omega] at hcz
        calc (n:ℝ) * ‖A2 / ((X:ℂ)^(2*n+2)) - B2 / ((Y:ℂ)^(2*n+2))‖
            ≤ (n:ℝ) * (Cz * H / X^(2*n+1)) := by
              apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
              rw [hCzdef]; exact hcz
          _ = ((n:ℝ) * Cz) * H / X^(2*n+1) := by ring
      -- combine the two bounds
      rw [hker]
      refine (norm_sub_le _ _).trans ?_
      refine (add_le_add hdiag hoff).trans ?_
      have hXp : (0:ℝ) < X ^ (2*n+1) := pow_pos hXpos' _
      have hstep : Cd * H / X ^ (2*n+1) + (n:ℝ) * Cz * H / X ^ (2*n+1)
          ≤ (Cd + (n:ℝ) * Cz + 1) * H / X ^ (2*n+1) := by
        rw [← add_div, show Cd * H + (n:ℝ) * Cz * H = (Cd + (n:ℝ)*Cz) * H from by ring]
        apply div_le_div_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right (by linarith) hHnn
        · exact hXp.le
      calc Cd * H / X ^ (2 * n + 1) + (n:ℝ) * Cz * H / X ^ (2 * n + 1)
          ≤ (Cd + (n:ℝ) * Cz + 1) * H / X ^ (2 * n + 1) := hstep
        _ = (Cd + (n:ℝ) * Cz + 1) * eucNorm h / (eucNorm x) ^ (2 * n + 1) := by
            rw [hHdef, hXdef]

end Work.CR.Flat.Cauchy.bmCz
