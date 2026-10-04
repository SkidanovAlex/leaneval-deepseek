import Mathlib
import Submission.Work.Diff.STE.ENormSq_seriesFun_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Weighted `ℓ²` summability of the iterated Fourier multiplier

The Fourier multiplier `dmulV q γ` of the iterated derivative in the directions `q` satisfies

  `‖dmulV q γ m‖² ≤ ((2π)² ⟨m⟩)^{|q|} ‖γ m‖²`

(`Work.Diff.STE.norm_sq_dmulV_le`).  Multiplying through by the (real) weight `⟨m⟩^j` and using
that `⟨m⟩ ≥ 1` together with `j + |q| ≤ k` gives the pointwise domination

  `⟨m⟩^j ‖dmulV q γ m‖² ≤ ((2π)²)^{|q|} · ⟨m⟩^k ‖γ m‖²`,

which transports summability and the value of the `ℓ²` norm from the weight `k` to the weight `j`,
at the price of the constant `((2π)²)^{|q|}`.
-/

noncomputable section

namespace Work.Diff.STE.flat

open Work.Diff.STE

/-- **Pointwise weight exchange.**  For `j + |q| ≤ k` the weight `⟨m⟩^j` applied to the
multiplied-out derivative is dominated by the weight `⟨m⟩^k` applied to `γ`, up to the
multiplier `((2π)²)^{|q|}`. -/
lemma wt_rpow_mul_normSq_dmulV_le {n : ℕ} (q : List (Fin n)) (j : ℝ) (k : ℕ)
    (γ : (Fin n → ℤ) → ℂ) (hjq : j + (q.length : ℝ) ≤ (k : ℝ)) (m : Fin n → ℤ) :
    (wt m) ^ j * ‖dmulV q γ m‖ ^ 2
      ≤ ((2 * Real.pi) ^ 2) ^ q.length * ((wt m) ^ k * ‖γ m‖ ^ 2) := by
  have hw : 0 < wt m := wt_pos m
  have hw1 : 1 ≤ wt m := wt_one_le m
  have hstep : (wt m) ^ j * (wt m) ^ (q.length : ℝ) ≤ (wt m) ^ k := by
    rw [← Real.rpow_add hw]
    calc (wt m) ^ (j + (q.length : ℝ)) ≤ (wt m) ^ ((k : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hw1 hjq
      _ = (wt m) ^ k := Real.rpow_natCast (wt m) k
  refine (mul_le_mul_of_nonneg_left (norm_sq_dmulV_le q γ m)
    (Real.rpow_nonneg hw.le j)).trans ?_
  calc (wt m) ^ j * (((2 * Real.pi) ^ 2 * wt m) ^ q.length * ‖γ m‖ ^ 2)
      = ((2 * Real.pi) ^ 2) ^ q.length
          * ((wt m) ^ j * (wt m) ^ ((q.length : ℕ) : ℝ) * ‖γ m‖ ^ 2) := by
        rw [mul_pow, Real.rpow_natCast]
        ring
    _ ≤ ((2 * Real.pi) ^ 2) ^ q.length * ((wt m) ^ k * ‖γ m‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hstep (sq_nonneg _))
          (pow_nonneg (by positivity) _)

theorem summable_wt_dmulV_le {n : ℕ} (q : List (Fin n)) (j : ℝ) (k : ℕ)
    (γ : (Fin n → ℤ) → ℂ)
    (hjq : j + (q.length : ℝ) ≤ (k : ℝ))
    (hγ : Summable (fun m : Fin n → ℤ => (Work.Diff.STE.wt m) ^ k * ‖γ m‖ ^ 2)) :
    Summable (fun m : Fin n → ℤ => (Work.Diff.STE.wt m) ^ j * ‖Work.Diff.STE.dmulV q γ m‖ ^ 2) ∧
      (∑' m : Fin n → ℤ, (Work.Diff.STE.wt m) ^ j * ‖Work.Diff.STE.dmulV q γ m‖ ^ 2)
        ≤ ((2 * Real.pi) ^ 2) ^ q.length
          * (∑' m : Fin n → ℤ, (Work.Diff.STE.wt m) ^ k * ‖γ m‖ ^ 2) := by
  have hpt : ∀ m : Fin n → ℤ,
      (wt m) ^ j * ‖dmulV q γ m‖ ^ 2
        ≤ ((2 * Real.pi) ^ 2) ^ q.length * ((wt m) ^ k * ‖γ m‖ ^ 2) :=
    fun m => wt_rpow_mul_normSq_dmulV_le q j k γ hjq m
  have hsum : Summable (fun m : Fin n → ℤ => (wt m) ^ j * ‖dmulV q γ m‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (Real.rpow_nonneg (wt_pos m).le j) (sq_nonneg _)) hpt (hγ.mul_left _)
  refine ⟨hsum, ?_⟩
  calc (∑' m : Fin n → ℤ, (wt m) ^ j * ‖dmulV q γ m‖ ^ 2)
      ≤ ∑' m : Fin n → ℤ, ((2 * Real.pi) ^ 2) ^ q.length * ((wt m) ^ k * ‖γ m‖ ^ 2) :=
        Summable.tsum_le_tsum hpt hsum (hγ.mul_left _)
    _ = ((2 * Real.pi) ^ 2) ^ q.length * ∑' m : Fin n → ℤ, (wt m) ^ k * ‖γ m‖ ^ 2 :=
        Summable.tsum_mul_left _ hγ

end Work.Diff.STE.flat
