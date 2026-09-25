import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmCz.abs_eucNorm_sub_le
import Submission.Work.CR.Flat.Cauchy.bmCz.cz_real_core
import Submission.Work.CR.Flat.Cauchy.bmCz.cz_num_core

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy.bmCz

open Work.CR.Flat.Cauchy

/-! ### Elementary facts about `eucNorm` and about the norm on `ℂ` -/

/-- Each coordinate of `x` is bounded by its Euclidean norm. -/
lemma norm_apply_le_eucNorm' {n : ℕ} (x : Fin n → ℂ) (i : Fin n) : ‖x i‖ ≤ eucNorm x := by
  have h : ‖x i‖ ^ 2 ≤ eucNorm x ^ 2 := by
    rw [eucNorm_sq]
    exact Finset.single_le_sum (f := fun l : Fin n => ‖x l‖ ^ 2) (fun l _ => sq_nonneg (‖x l‖))
      (Finset.mem_univ i)
  have h3 : |‖x i‖| ≤ |eucNorm x| := sq_le_sq.mp h
  rwa [abs_of_nonneg (norm_nonneg (x i)), abs_of_nonneg (eucNorm_nonneg x)] at h3

@[simp] lemma norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by simp

/-- The constant produced by the Calderón–Zygmund kernel-difference estimate. -/
noncomputable def czCC (n : ℕ) : ℝ :=
  (n : ℝ) * (5 / 2 + ((2 * n + 2 : ℕ) : ℝ) * (3 / 2 : ℝ) ^ ((2 * n + 2) - 1)
    * (2 : ℝ) ^ ((2 * n + 2) - 2)) + 1

/-- Calderón–Zygmund kernel-difference estimate for `∂_{z_k}(bmKernel j)`. -/
theorem norm_bmDzKernel_sub_le {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k j : Fin n) (x h : Fin n → ℂ),
      2 * Work.CR.Flat.Cauchy.eucNorm h ≤ Work.CR.Flat.Cauchy.eucNorm x →
        ‖Work.CR.Flat.Cauchy.bmDzKernel k j (x - h) - Work.CR.Flat.Cauchy.bmDzKernel k j x‖
          ≤ C * Work.CR.Flat.Cauchy.eucNorm h
              * (Work.CR.Flat.Cauchy.eucNorm x) ^ (-(2 * (n : ℝ) + 1)) := by
  refine ⟨czCC n, ?_, ?_⟩
  · rw [czCC]; positivity
  · intro k j x h hxh
    rcases eq_or_lt_of_le (eucNorm_nonneg x) with hX0 | hXpos
    · -- degenerate case `x = 0`
      have hx0 : x = 0 := eucNorm_eq_zero.mp hX0.symm
      have hH0 : eucNorm h = 0 := by
        have h2 := hxh
        rw [← hX0] at h2
        linarith [eucNorm_nonneg h]
      have hh0 : h = 0 := eucNorm_eq_zero.mp hH0
      have hz : (0 : ℝ) ^ (-(2 * (n : ℝ) + 1)) = 0 := by
        apply Real.zero_rpow
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        linarith
      rw [hx0, hh0]
      simp only [eucNorm_zero]
      rw [hz]
      simp [bmDzKernel]
    · -- main case
      set X := eucNorm x with hXdef
      set H := eucNorm h with hHdef
      set Y := eucNorm (x - h) with hYdef
      have hXpos' : 0 < X := by rw [hXdef]; exact hXpos
      have hHnn : 0 ≤ H := by rw [hHdef]; exact eucNorm_nonneg h
      have h2HY : 2 * H ≤ X := by rw [hHdef, hXdef]; exact hxh
      have htri : |X - Y| ≤ H := by
        rw [hXdef, hYdef, hHdef]
        have hsub : x - (x - h) = h := by abel
        simpa [hsub] using abs_eucNorm_sub_le x (x - h)
      have hXYle : X - Y ≤ H := (abs_le.mp htri).2
      have hXYge : -H ≤ X - Y := (abs_le.mp htri).1
      have hYge : X / 2 ≤ Y := by linarith
      have hYpos : 0 < Y := by linarith
      have hYle : Y ≤ X + H := by linarith
      have hYu : 2 * Y ≤ 3 * X := by linarith
      have hYe : X ≤ 2 * Y := by linarith
      -- the numerator of the kernel and its shifted analogue
      set A : ℂ := starRingEnd ℂ (x j) * starRingEnd ℂ (x k) with hA
      set B : ℂ := starRingEnd ℂ ((x - h) j) * starRingEnd ℂ ((x - h) k) with hB
      have hA_le : ‖A‖ ≤ X ^ 2 := by
        rw [hA, norm_mul]
        have h1 : ‖starRingEnd ℂ (x j)‖ ≤ X := by
          rw [Complex.norm_conj, hXdef]; exact norm_apply_le_eucNorm' x j
        have h2 : ‖starRingEnd ℂ (x k)‖ ≤ X := by
          rw [Complex.norm_conj, hXdef]; exact norm_apply_le_eucNorm' x k
        calc ‖starRingEnd ℂ (x j)‖ * ‖starRingEnd ℂ (x k)‖ ≤ X * X :=
              mul_le_mul h1 h2 (norm_nonneg _) hXpos'.le
          _ = X ^ 2 := by ring
      have hB_le : ‖B‖ ≤ Y ^ 2 := by
        rw [hB, norm_mul]
        have h1 : ‖starRingEnd ℂ ((x - h) j)‖ ≤ Y := by
          rw [Complex.norm_conj, hYdef]; exact norm_apply_le_eucNorm' (x - h) j
        have h2 : ‖starRingEnd ℂ ((x - h) k)‖ ≤ Y := by
          rw [Complex.norm_conj, hYdef]; exact norm_apply_le_eucNorm' (x - h) k
        calc ‖starRingEnd ℂ ((x - h) j)‖ * ‖starRingEnd ℂ ((x - h) k)‖ ≤ Y * Y :=
              mul_le_mul h1 h2 (norm_nonneg _) hYpos.le
          _ = Y ^ 2 := by ring
      have hAB_le : ‖A - B‖ ≤ (5 / 2) * X * H := by
        have hfac : A - B =
            (starRingEnd ℂ (x j) - starRingEnd ℂ ((x - h) j)) * starRingEnd ℂ ((x - h) k)
              + starRingEnd ℂ (x j) * (starRingEnd ℂ (x k) - starRingEnd ℂ ((x - h) k)) := by
          rw [hA, hB]; ring
        have e1 : ‖starRingEnd ℂ (x j) - starRingEnd ℂ ((x - h) j)‖ ≤ H := by
          have hconj : starRingEnd ℂ (x j) - starRingEnd ℂ ((x - h) j) = starRingEnd ℂ (h j) := by
            rw [← map_sub]; congr 1; simp [Pi.sub_apply]
          rw [hconj, Complex.norm_conj, hHdef]
          exact norm_apply_le_eucNorm' h j
        have e4 : ‖starRingEnd ℂ (x k) - starRingEnd ℂ ((x - h) k)‖ ≤ H := by
          have hconj : starRingEnd ℂ (x k) - starRingEnd ℂ ((x - h) k) = starRingEnd ℂ (h k) := by
            rw [← map_sub]; congr 1; simp [Pi.sub_apply]
          rw [hconj, Complex.norm_conj, hHdef]
          exact norm_apply_le_eucNorm' h k
        have e2 : ‖starRingEnd ℂ ((x - h) k)‖ ≤ 3 * X / 2 := by
          rw [Complex.norm_conj]
          calc ‖(x - h) k‖ ≤ eucNorm (x - h) := norm_apply_le_eucNorm' (x - h) k
            _ = Y := hYdef.symm
            _ ≤ 3 * X / 2 := by linarith
        have e3 : ‖starRingEnd ℂ (x j)‖ ≤ X := by
          rw [Complex.norm_conj, hXdef]; exact norm_apply_le_eucNorm' x j
        rw [hfac]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
        refine (add_le_add (mul_le_mul e1 e2 (norm_nonneg _) hHnn)
          (mul_le_mul e3 e4 (norm_nonneg _) hXpos'.le)).trans ?_
        have : H * (3 * X / 2) + X * H = (5 / 2) * X * H := by ring
        linarith
      -- the difference of kernels as a difference of two fractions
      have hbmd (z : Fin n → ℂ) : bmDzKernel k j z =
          -(n : ℂ) * (starRingEnd ℂ (z j) * starRingEnd ℂ (z k))
            / ((eucNorm z : ℂ) ^ (2 * n + 2)) := by
        simp only [bmDzKernel]; ring
      have hdenX : (eucNorm x : ℂ) ^ (2 * n + 2) = ((X ^ (2 * n + 2) : ℝ) : ℂ) := by
        rw [← hXdef, ← Complex.ofReal_pow]
      have hdenY : (eucNorm (x - h) : ℂ) ^ (2 * n + 2) = ((Y ^ (2 * n + 2) : ℝ) : ℂ) := by
        rw [← hYdef, ← Complex.ofReal_pow]
      have hXp : ((X ^ (2 * n + 2) : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_pow]
        exact pow_ne_zero _ (fun hc => hXpos'.ne' (Complex.ofReal_injective (by simpa using hc)))
      have hYp : ((Y ^ (2 * n + 2) : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_pow]
        exact pow_ne_zero _ (fun hc => hYpos.ne' (Complex.ofReal_injective (by simpa using hc)))
      have hker : bmDzKernel k j (x - h) - bmDzKernel k j x =
          (n : ℂ) * (A / ((X ^ (2 * n + 2) : ℝ) : ℂ)
            - B / ((Y ^ (2 * n + 2) : ℝ) : ℂ)) := by
        rw [hbmd (x - h), hbmd x, hdenX, hdenY, ← hA, ← hB]
        field_simp
        ring
      -- the Calderón–Zygmund estimate for the bracket
      have hmain : ‖A / ((X ^ (2 * n + 2) : ℝ) : ℂ) - B / ((Y ^ (2 * n + 2) : ℝ) : ℂ)‖
          ≤ (5 / 2 + ((2 * n + 2 : ℕ) : ℝ) * (3 / 2 : ℝ) ^ ((2 * n + 2) - 1)
              * (2 : ℝ) ^ ((2 * n + 2) - 2)) * H * (X ^ ((2 * n + 2) - 1))⁻¹ := by
        have hdecomp : A / ((X ^ (2 * n + 2) : ℝ) : ℂ) - B / ((Y ^ (2 * n + 2) : ℝ) : ℂ)
            = (A * ((Y ^ (2 * n + 2) : ℝ) : ℂ) - B * ((X ^ (2 * n + 2) : ℝ) : ℂ))
              / (((X ^ (2 * n + 2) : ℝ) : ℂ) * ((Y ^ (2 * n + 2) : ℝ) : ℂ)) := by
          field_simp
        rw [hdecomp, norm_div]
        have hden : ‖(((X ^ (2 * n + 2) : ℝ) : ℂ) * ((Y ^ (2 * n + 2) : ℝ) : ℂ))‖
            = X ^ (2 * n + 2) * Y ^ (2 * n + 2) := by
          rw [norm_mul, norm_ofReal_eq_abs, norm_ofReal_eq_abs, abs_of_pos (by positivity),
            abs_of_pos (by positivity)]
        rw [hden]
        refine (cz_num_core (m := 2 * n + 2) (by omega) hXpos' hYpos hHnn htri hYu
          hB_le hAB_le).trans ?_
        refine (cz_real_core (m := 2 * n + 2) (by omega) hXpos' hYpos hHnn htri hYe hYu).trans
          (le_of_eq ?_)
        ring
      -- combine
      rw [hker, norm_mul]
      have hnc : ‖(n : ℂ)‖ = (n : ℝ) := by simp
      rw [hnc]
      have hKnn : 0 ≤ H * (X ^ ((2 * n + 2) - 1))⁻¹ := by positivity
      have hstep1 : (n : ℝ) * ‖A / ((X ^ (2 * n + 2) : ℝ) : ℂ)
            - B / ((Y ^ (2 * n + 2) : ℝ) : ℂ)‖
          ≤ (n : ℝ) * ((5 / 2 + ((2 * n + 2 : ℕ) : ℝ) * (3 / 2 : ℝ) ^ ((2 * n + 2) - 1)
              * (2 : ℝ) ^ ((2 * n + 2) - 2)) * H * (X ^ ((2 * n + 2) - 1))⁻¹) :=
        mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg n)
      have hstep2 : (n : ℝ) * ((5 / 2 + ((2 * n + 2 : ℕ) : ℝ) * (3 / 2 : ℝ) ^ ((2 * n + 2) - 1)
              * (2 : ℝ) ^ ((2 * n + 2) - 2)) * H * (X ^ ((2 * n + 2) - 1))⁻¹)
          ≤ czCC n * H * (X ^ ((2 * n + 2) - 1))⁻¹ := by
        rw [czCC]
        calc (n : ℝ) * ((5 / 2 + ((2 * n + 2 : ℕ) : ℝ) * (3 / 2 : ℝ) ^ ((2 * n + 2) - 1)
                * (2 : ℝ) ^ ((2 * n + 2) - 2)) * H * (X ^ ((2 * n + 2) - 1))⁻¹)
            = ((n : ℝ) * (5 / 2 + ((2 * n + 2 : ℕ) : ℝ) * (3 / 2 : ℝ) ^ ((2 * n + 2) - 1)
                * (2 : ℝ) ^ ((2 * n + 2) - 2))) * (H * (X ^ ((2 * n + 2) - 1))⁻¹) := by ring
          _ ≤ ((n : ℝ) * (5 / 2 + ((2 * n + 2 : ℕ) : ℝ) * (3 / 2 : ℝ) ^ ((2 * n + 2) - 1)
                * (2 : ℝ) ^ ((2 * n + 2) - 2)) + 1) * (H * (X ^ ((2 * n + 2) - 1))⁻¹) :=
              mul_le_mul_of_nonneg_right (by linarith) hKnn
          _ = ((n : ℝ) * (5 / 2 + ((2 * n + 2 : ℕ) : ℝ) * (3 / 2 : ℝ) ^ ((2 * n + 2) - 1)
                * (2 : ℝ) ^ ((2 * n + 2) - 2)) + 1) * H * (X ^ ((2 * n + 2) - 1))⁻¹ := by ring
      have hstep3 : czCC n * H * (X ^ ((2 * n + 2) - 1))⁻¹
          = czCC n * H * (eucNorm x) ^ (-(2 * (n : ℝ) + 1)) := by
        rw [hXdef]
        congr 1
        rw [show 2 * (n : ℝ) + 1 = ((2 * n + 1 : ℕ) : ℝ) by push_cast; ring]
        rw [Real.rpow_neg (le_of_lt hXpos), Real.rpow_natCast]
        rw [show (2 * n + 2) - 1 = 2 * n + 1 by omega]
      calc (n : ℝ) * ‖A / ((X ^ (2 * n + 2) : ℝ) : ℂ)
              - B / ((Y ^ (2 * n + 2) : ℝ) : ℂ)‖
          ≤ (n : ℝ) * ((5 / 2 + ((2 * n + 2 : ℕ) : ℝ) * (3 / 2 : ℝ) ^ ((2 * n + 2) - 1)
              * (2 : ℝ) ^ ((2 * n + 2) - 2)) * H * (X ^ ((2 * n + 2) - 1))⁻¹) := hstep1
        _ ≤ czCC n * H * (X ^ ((2 * n + 2) - 1))⁻¹ := hstep2
        _ = czCC n * H * (eucNorm x) ^ (-(2 * (n : ℝ) + 1)) := hstep3

end Work.CR.Flat.Cauchy.bmCz
