import Mathlib
import Submission.Work.FIArea1.QboxDefs

namespace Work.FIArea1

/-- **The size of the substituted ball.**  For `X ≥ 1` the sum `∑_{y ∈ Qbim X} (√|Im y| + 1)`
is `≪ X^{5/4}`: `Qbim X` is contained in the box `gBox (KZ X)` with `KZ X = ⌈√(2X)⌉`, so it has
at most `(2⌈√(2X)⌉+1)² ≤ 50X` points (`Work.FIArea1.card_gBox` from the imported module), and each
of them satisfies `|Im y| ≤ √(2X)` because `|y|² ≤ 2X` (`Work.FIArea1.mem_Qbim_iff`).  Hence
`∑ (√|Im y| + 1) ≤ 50X·(2X)^{1/4} + 50X ≤ C X^{5/4}` for `X ≥ 1`. -/
theorem Qbim_sqrt_im_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      (∑ y ∈ Work.FIArea1.Qbim X, (Real.sqrt |(y.im : ℝ)| + 1))
        ≤ C * X ^ ((5 : ℝ) / 4) := by
  refine ⟨150, by norm_num, ?_⟩
  intro X hX
  have hXpos : (0:ℝ) < X := by linarith
  have hXnonneg : (0:ℝ) ≤ X := by linarith
  -- Bound each summand by `3 · X^{1/4}`.
  have hterm : ∀ y ∈ Work.FIArea1.Qbim X,
      Real.sqrt |(y.im : ℝ)| + 1 ≤ 3 * X ^ ((1:ℝ)/4) := by
    intro y hy
    obtain ⟨h0, hgn, him⟩ := Work.FIArea1.mem_Qbim_iff.mp hy
    have hgn_eq : (Work.FIPlan.gnorm y : ℝ) = (y.re : ℝ)^2 + (y.im : ℝ)^2 := by
      have h := congrArg (fun t : ℤ => (t : ℝ)) (Work.FIArea1.gnorm_int y)
      push_cast at h
      exact h
    have himsq : (y.im : ℝ)^2 ≤ 2*X := by
      nlinarith [sq_nonneg (y.re:ℝ), hgn_eq, hgn]
    have h_im_le : |(y.im : ℝ)| ≤ Real.sqrt (2*X) := by
      have h1 : Real.sqrt ((y.im:ℝ)^2) ≤ Real.sqrt (2*X) := Real.sqrt_le_sqrt himsq
      rwa [Real.sqrt_sq_eq_abs] at h1
    have hstep1 : Real.sqrt |(y.im:ℝ)| ≤ Real.sqrt (Real.sqrt (2*X)) :=
      Real.sqrt_le_sqrt h_im_le
    have h2X : (0:ℝ) ≤ 2*X := by linarith
    have hsqrt2 : Real.sqrt (Real.sqrt (2*X)) = (2*X) ^ ((1:ℝ)/4) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      rw [← Real.rpow_mul (x := 2*X) h2X]
      norm_num
    have hsq_le : Real.sqrt (Real.sqrt (2*X)) ≤ 2 * X ^ ((1:ℝ)/4) := by
      rw [hsqrt2, Real.mul_rpow (x := 2) (y := X) (z := (1:ℝ)/4) (by norm_num) hXnonneg]
      have h2 : (2:ℝ) ^ ((1:ℝ)/4) ≤ 2 := by
        have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
          (by norm_num : (1:ℝ)/4 ≤ 1)
        rwa [Real.rpow_one] at h
      have hXn : (0:ℝ) ≤ X ^ ((1:ℝ)/4) := Real.rpow_nonneg hXnonneg _
      nlinarith
    have h1le : (1:ℝ) ≤ X ^ ((1:ℝ)/4) := Real.one_le_rpow hX (by norm_num)
    linarith [hstep1, hsq_le, h1le]
  -- `Qbim X` sits in `gBox (KZ X)`, whose cardinality is `(2⌈√(2X)⌉+1)²`.
  have hcard_le : (Work.FIArea1.Qbim X).card ≤ (2*(Work.FIArea1.KZ X).natAbs + 1)^2 := by
    calc (Work.FIArea1.Qbim X).card ≤ (Work.FIPlan.gBox (Work.FIArea1.KZ X)).card := by
          apply Finset.card_le_card
          intro z hz
          exact Work.FIArea1.mem_gBox_KZ_of_gnorm_le (Work.FIArea1.mem_Qbim_iff.mp hz).2.1
      _ = (2*(Work.FIArea1.KZ X).natAbs+1)^2 := Work.FIArea1.card_gBox _ (Work.FIArea1.KZ_nonneg X)
  -- `(2⌈√(2X)⌉+1)² ≤ 50 X` for `X ≥ 1`.
  have hk : ((Work.FIArea1.KZ X).natAbs : ℝ) ≤ Real.sqrt (2*X) + 1 := by
    have he : ((Work.FIArea1.KZ X).natAbs : ℝ) = ((⌈Real.sqrt (2*X)⌉₊ : ℕ) : ℝ) := by
      simp [Work.FIArea1.KZ]
    rw [he]
    have h2 := Nat.ceil_lt_add_one (Real.sqrt_nonneg (2*X))
    linarith
  have hcardR : ((Work.FIArea1.Qbim X).card : ℝ) ≤ 50*X := by
    have h1 : (((2*(Work.FIArea1.KZ X).natAbs+1)^2 : ℕ) : ℝ) ≤ 50*X := by
      push_cast
      have hk0 : (0:ℝ) ≤ ((Work.FIArea1.KZ X).natAbs : ℝ) := by positivity
      have ht2 : (Real.sqrt (2*X))^2 = 2*X := Real.sq_sqrt (by linarith)
      have htle : Real.sqrt (2*X) ≤ 2*X := by
        have h : Real.sqrt (2*X) ≤ Real.sqrt ((2*X)^2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (2*X-1)])
        rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith)] at h
      have h23 : (2*((Work.FIArea1.KZ X).natAbs : ℝ)+1)^2 ≤ (2*Real.sqrt (2*X)+3)^2 := by
        apply pow_le_pow_left₀ (by linarith) (by linarith)
      nlinarith [sq_nonneg (Real.sqrt (2*X))]
    calc ((Work.FIArea1.Qbim X).card : ℝ) ≤ (((2*(Work.FIArea1.KZ X).natAbs+1)^2 : ℕ) : ℝ) := by
          exact_mod_cast hcard_le
      _ ≤ 50*X := h1
  -- Assemble.
  calc (∑ y ∈ Work.FIArea1.Qbim X, (Real.sqrt |(y.im : ℝ)| + 1))
      ≤ ((Work.FIArea1.Qbim X).card : ℝ) * (3 * X ^ ((1:ℝ)/4)) := by
        calc (∑ y ∈ Work.FIArea1.Qbim X, (Real.sqrt |(y.im : ℝ)| + 1))
            ≤ ∑ y ∈ Work.FIArea1.Qbim X, (3 * X ^ ((1:ℝ)/4)) := Finset.sum_le_sum hterm
          _ = ((Work.FIArea1.Qbim X).card) • (3 * X ^ ((1:ℝ)/4)) := Finset.sum_const _
          _ = ((Work.FIArea1.Qbim X).card : ℝ) * (3 * X ^ ((1:ℝ)/4)) := by rw [nsmul_eq_mul]
    _ ≤ (50*X) * (3 * X ^ ((1:ℝ)/4)) := by
        apply mul_le_mul_of_nonneg_right hcardR
        have : (0:ℝ) ≤ X ^ ((1:ℝ)/4) := Real.rpow_nonneg hXnonneg _
        linarith
    _ = 150 * (X * X ^ ((1:ℝ)/4)) := by ring
    _ = 150 * X ^ ((5:ℝ)/4) := by
        have hpow : X ^ ((5:ℝ)/4) = X * X ^ ((1:ℝ)/4) := by
          rw [show (5:ℝ)/4 = 1 + 1/4 by norm_num, Real.rpow_add hXpos, Real.rpow_one]
        rw [hpow]

end Work.FIArea1
