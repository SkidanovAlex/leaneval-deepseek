import Mathlib
import Submission.Work.LinnikAreas2.PsiDefs2

namespace Work.LinnikAreas2

/-- The Heath-Brown weight `wt L U X n = e^{-n/X} - e^{-nL²/U}` is bounded in absolute value by
the sum of the two exponentials that define it. -/
lemma wt_abs_le {L U X : ℝ} (n : ℕ) :
    |Work.LinnikAreas2.wt L U X n|
      ≤ Real.exp (-(n:ℝ)/X) + Real.exp (-(n:ℝ)*L^2/U) := by
  have hle := Work.LinnikAreas2.wt_le_exp (L := L) (U := U) (X := X) n
  have hge : -(Real.exp (-(n:ℝ)/X) + Real.exp (-(n:ℝ)*L^2/U))
      ≤ Work.LinnikAreas2.wt L U X n := by
    have h2' : (0:ℝ) ≤ Real.exp (-(n:ℝ)*L^2/U) := (Real.exp_pos _).le
    have h1' : (0:ℝ) ≤ Real.exp (-(n:ℝ)/X) := (Real.exp_pos _).le
    rw [Work.LinnikAreas2.wt]
    linarith
  rw [abs_le]
  refine ⟨hge, ?_⟩
  have h2' : (0:ℝ) ≤ Real.exp (-(n:ℝ)*L^2/U) := (Real.exp_pos _).le
  linarith

/-- The geometric-type exponential sequence `n ↦ e^{-n/Y}` is summable for `Y > 0`. -/
lemma summable_exp_neg_div {Y : ℝ} (hY : 0 < Y) :
    Summable (fun n : ℕ => Real.exp (-(n:ℝ)/Y)) := by
  have heq : (fun n : ℕ => Real.exp (-(n:ℝ)/Y)) = fun n : ℕ => (Real.exp (-(Y⁻¹)))^n := by
    funext n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq]
  apply summable_geometric_of_norm_lt_one
  have hr : Real.exp (-(Y⁻¹)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : (0:ℝ) < Y⁻¹ := inv_pos.mpr hY
    linarith
  rwa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem summable_psiSq_mul_wt {L U V X A : ℝ} (hL : 0 < L) (hU : 0 < U) (hX : 0 < X)
    (hA : 0 ≤ A) (hAle : ∀ n : ℕ, Work.LinnikAreas2.psiSq U V n ≤ A * n) :
    Summable (fun n : ℕ => Work.LinnikAreas2.psiSq U V n * (n:ℝ)⁻¹
      * Work.LinnikAreas2.wt L U X n) := by
  -- termwise bound by an explicitly summable majorant
  have hbound : ∀ n : ℕ,
      ‖Work.LinnikAreas2.psiSq U V n * (n:ℝ)⁻¹
        * Work.LinnikAreas2.wt L U X n‖
      ≤ A * (Real.exp (-(n:ℝ)/X) + Real.exp (-(n:ℝ)*L^2/U)) := by
    intro n
    -- the weight factor is bounded by the sum of the two exponentials
    have h3n := wt_abs_le (L := L) (U := U) (X := X) n
    -- the `psiSq` factor times `1/n` is bounded by `A`
    have hnn : (n:ℝ) * (n:ℝ)⁻¹ ≤ 1 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · rw [mul_inv_cancel₀ (by positivity : ((n:ℝ)) ≠ 0)]
    have hprod : Work.LinnikAreas2.psiSq U V n * (n:ℝ)⁻¹ ≤ A := by
      have h1 := mul_le_mul_of_nonneg_right (hAle n) (by positivity : (0:ℝ) ≤ (n:ℝ)⁻¹)
      have h2 : A * (n:ℝ) * (n:ℝ)⁻¹ ≤ A := by
        have hrw : A * (n:ℝ) * (n:ℝ)⁻¹ = A * ((n:ℝ) * (n:ℝ)⁻¹) := by ring
        rw [hrw]
        simpa using mul_le_mul_of_nonneg_left hnn hA
      linarith [h1, h2]
    have habs : |Work.LinnikAreas2.psiSq U V n * (n:ℝ)⁻¹
        * Work.LinnikAreas2.wt L U X n|
        = Work.LinnikAreas2.psiSq U V n * (n:ℝ)⁻¹
          * |Work.LinnikAreas2.wt L U X n| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Work.LinnikAreas2.psiSq_nonneg U V n),
        abs_of_nonneg (by positivity)]
    rw [Real.norm_eq_abs, habs]
    exact mul_le_mul hprod h3n (abs_nonneg _) hA
  -- summability of the two exponential majorants
  have hsum1 : Summable (fun n : ℕ => Real.exp (-(n:ℝ)/X)) :=
    summable_exp_neg_div hX
  have hsum2 : Summable (fun n : ℕ => Real.exp (-(n:ℝ)*L^2/U)) := by
    have hY : 0 < L^2/U := div_pos (by positivity) hU
    have heq : (fun n : ℕ => Real.exp (-(n:ℝ)*L^2/U))
        = fun n : ℕ => (Real.exp (-(L^2/U)))^n := by
      funext n
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [heq]
    apply summable_geometric_of_norm_lt_one
    have hr : Real.exp (-(L^2/U)) < 1 := by
      rw [Real.exp_lt_one_iff]; linarith
    rwa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hmaj : Summable (fun n : ℕ =>
      A * (Real.exp (-(n:ℝ)/X) + Real.exp (-(n:ℝ)*L^2/U))) :=
    (hsum1.add hsum2).mul_left A
  exact hmaj.of_norm_bounded hbound

end Work.LinnikAreas2
