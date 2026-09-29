import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.yMulFacts

/-!
# `pairErr`: error propagation through the butterfly and through `yMul`

This is the purely numerical part of `HasPair` (`Submission/Work/SynFFT/hasPair.lean`).

Suppose two coefficient vectors `w₁`, `w₂` approximate `u₁`, `u₂` with error `≤ e` in the
`2^p`-scaled sense, and suppose the "sum" and "difference" words `va`, `wd` have computed
`(w₁ + w₂)/2` and `(w₁ - w₂)/2` to within `1/2^p` (i.e. with scaled error `< 1`).  Then `va`
approximates `(u₁ + u₂)/2` and `wd` approximates `(u₁ - u₂)/2` with scaled error `≤ e + 1`
(triangle inequality), and the same holds after applying `yMul r E` — because `yMul r E` is a
signed permutation of the coefficients (`Work.SynFFT.yMulFacts`), hence preserves the
*coordinatewise* error.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

/-- `‖z / 2‖ = ‖z‖ / 2` for `z : ℂ`. -/
lemma norm_div_two (z : ℂ) : ‖z / 2‖ = ‖z‖ / 2 := by
  rw [norm_div]
  norm_num

/-- Triangle-inequality step of the butterfly: if `X` has scaled error `< 1` and `B`, `C` have
scaled error `≤ e`, then `X + Y/2` has scaled error `≤ e + 1`, provided
`‖Y‖ ≤ ‖B‖ + ‖C‖` (true for `Y = B + C` and for `Y = B - C`). -/
lemma tri_step {K e : ℝ} (hK : 0 ≤ K) (X Y B C : ℂ)
    (hY : ‖Y‖ ≤ ‖B‖ + ‖C‖) (hX : K * ‖X‖ < 1) (hB : K * ‖B‖ ≤ e) (hC : K * ‖C‖ ≤ e) :
    K * ‖X + Y / 2‖ ≤ e + 1 := by
  have h1 : ‖X + Y / 2‖ ≤ ‖X‖ + ‖Y‖ / 2 := by
    calc ‖X + Y / 2‖ ≤ ‖X‖ + ‖Y / 2‖ := norm_add_le _ _
      _ = ‖X‖ + ‖Y‖ / 2 := by rw [norm_div_two]
  have h2 : K * ‖Y‖ ≤ K * (‖B‖ + ‖C‖) := mul_le_mul_of_nonneg_left hY hK
  have hXle : K * ‖X‖ ≤ 1 := le_of_lt hX
  have h4 : K * (‖X‖ + ‖Y‖ / 2) ≤ e + 1 := by
    nlinarith [h2, hB, hC, hXle, hK, norm_nonneg Y, norm_nonneg B, norm_nonneg C]
  calc K * ‖X + Y / 2‖ ≤ K * (‖X‖ + ‖Y‖ / 2) := mul_le_mul_of_nonneg_left h1 hK
    _ ≤ e + 1 := h4

/-- `yMul r E` is a signed permutation of the coefficients: the norm of a coordinate of the
difference of the images is the norm of a coordinate of the difference. -/
lemma yMul_sub_coord_norm (r : ℕ) (hr : 0 < r) (E : ℤ) (a b : Fin r → ℂ) (c : Fin r) :
    ∃ j : Fin r, ‖yMul r E a c - yMul r E b c‖ = ‖a j - b j‖ := by
  have hwf := yMulFacts r hr
  have hlin : yMul r E (fun k => a k - b k) c = yMul r E a c - yMul r E b c := by
    have h1 : (fun k => a k - b k) = a + (-1 : ℂ) • b := by
      funext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul, one_mul, sub_eq_add_neg]
    rw [h1, hwf.2.2.1, hwf.2.2.2.1]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨s, j, hs, hsj⟩ := hwf.2.2.2.2.1 E (fun k => a k - b k) c
  refine ⟨j, ?_⟩
  rw [← hlin, hsj]
  have hs1 : ‖s‖ = 1 := by rcases hs with h | h <;> simp [h]
  rw [norm_mul, hs1, one_mul]

theorem pairErr (p r : ℕ) (w₁ w₂ va wd : List (ℤ × ℤ)) (u₁ u₂ : Fin r → ℂ) (e : ℝ) (E : ℤ) (h1 : ∀ c : Fin r, (2 : ℝ) ^ p * ‖HvdH.fxC p (w₁.getD (c : ℕ) (0, 0)) - u₁ c‖ ≤ e) (h2 : ∀ c : Fin r, (2 : ℝ) ^ p * ‖HvdH.fxC p (w₂.getD (c : ℕ) (0, 0)) - u₂ c‖ ≤ e) (h3 : ∀ c : Fin r, (2 : ℝ) ^ p * ‖HvdH.fxC p (va.getD (c : ℕ) (0, 0)) - (HvdH.fxC p (w₁.getD (c : ℕ) (0, 0)) + HvdH.fxC p (w₂.getD (c : ℕ) (0, 0))) / 2‖ < 1) (h4 : ∀ c : Fin r, (2 : ℝ) ^ p * ‖HvdH.fxC p (wd.getD (c : ℕ) (0, 0)) - (HvdH.fxC p (w₁.getD (c : ℕ) (0, 0)) - HvdH.fxC p (w₂.getD (c : ℕ) (0, 0))) / 2‖ < 1) : (∀ c : Fin r, (2 : ℝ) ^ p * ‖HvdH.fxC p (va.getD (c : ℕ) (0, 0)) - (u₁ c + u₂ c) / 2‖ ≤ e + 1) ∧ (∀ c : Fin r, (2 : ℝ) ^ p * ‖HvdH.fxC p (wd.getD (c : ℕ) (0, 0)) - (u₁ c - u₂ c) / 2‖ ≤ e + 1) ∧ (∀ c : Fin r, (2 : ℝ) ^ p * ‖HvdH.yMul r E (fun c' => HvdH.fxC p (wd.getD (c' : ℕ) (0, 0))) c - HvdH.yMul r E (fun c' => (u₁ c' - u₂ c') / 2) c‖ ≤ e + 1) := by
  have hK : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
  have hva : ∀ c : Fin r, (2 : ℝ) ^ p * ‖HvdH.fxC p (va.getD (c : ℕ) (0, 0)) - (u₁ c + u₂ c) / 2‖ ≤ e + 1 := by
    intro c
    have hdec : HvdH.fxC p (va.getD (c : ℕ) (0, 0)) - (u₁ c + u₂ c) / 2 =
        (HvdH.fxC p (va.getD (c : ℕ) (0, 0)) -
          (HvdH.fxC p (w₁.getD (c : ℕ) (0, 0)) + HvdH.fxC p (w₂.getD (c : ℕ) (0, 0))) / 2) +
        ((HvdH.fxC p (w₁.getD (c : ℕ) (0, 0)) - u₁ c) +
          (HvdH.fxC p (w₂.getD (c : ℕ) (0, 0)) - u₂ c)) / 2 := by ring
    rw [hdec]
    exact tri_step hK _ _ _ _ (norm_add_le _ _) (h3 c) (h1 c) (h2 c)
  have hwd : ∀ c : Fin r, (2 : ℝ) ^ p * ‖HvdH.fxC p (wd.getD (c : ℕ) (0, 0)) - (u₁ c - u₂ c) / 2‖ ≤ e + 1 := by
    intro c
    have hdec : HvdH.fxC p (wd.getD (c : ℕ) (0, 0)) - (u₁ c - u₂ c) / 2 =
        (HvdH.fxC p (wd.getD (c : ℕ) (0, 0)) -
          (HvdH.fxC p (w₁.getD (c : ℕ) (0, 0)) - HvdH.fxC p (w₂.getD (c : ℕ) (0, 0))) / 2) +
        ((HvdH.fxC p (w₁.getD (c : ℕ) (0, 0)) - u₁ c) -
          (HvdH.fxC p (w₂.getD (c : ℕ) (0, 0)) - u₂ c)) / 2 := by ring
    rw [hdec]
    exact tri_step hK _ _ _ _ (norm_sub_le _ _) (h4 c) (h1 c) (h2 c)
  refine ⟨hva, hwd, ?_⟩
  intro c
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le (c : ℕ)) c.isLt
  obtain ⟨j, hj⟩ :=
    yMul_sub_coord_norm r hr E (fun c' => HvdH.fxC p (wd.getD (c' : ℕ) (0, 0)))
      (fun c' => (u₁ c' - u₂ c') / 2) c
  rw [hj]
  exact hwd j

end Work.SynFFT
