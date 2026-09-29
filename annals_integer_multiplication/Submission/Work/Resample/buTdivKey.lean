import Mathlib
import Submission.Work.Resample.sliceB1defs
import Submission.Work.Resample.buDefs
import Submission.Work.Fx.FxTdivReal

/-!
# `Work.Resample.buTdivKey`

The truncating-division rounding error of one Gaussian convolution round `buRound`.

For an arbitrary integer weight table `Wt`, the round

`buRound Wt p α s t hs v ℓ = ((tdiv S₁ 2^p), (tdiv S₂ 2^p))`,
`S₁ = Σ_{h∈H} Wt(ℓ,h)·v(ℓ+h)₁`, `S₂ = Σ_{h∈H} Wt(ℓ,h)·v(ℓ+h)₂`, `H = egHset (egM p α)`,

satisfies, in fixed-point metric,

`fxC p (buRound Wt p α s t hs v ℓ)
   = Σ_{h∈H} (Wt(ℓ,h)/2^p) · fxC p (v(ℓ+h)) - ρ`,  with `2^p·‖ρ‖ ≤ √2`.

Indeed each coordinate of `tdiv` differs from the true quotient by at most `1`
(`Work.Fx.FxTdivReal`), so the two-coordinate remainder has norm at most `√2` before the final
`2^{-p}` rescaling.  Nothing else enters: the weights `Wt` are arbitrary integers.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-- A complex number whose real and imaginary parts are both bounded by `1` in absolute value has
norm at most `√2`. -/
private lemma norm_ofReal_add_mul_I_le_sqrt_two (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    ‖(a : ℂ) + (b : ℂ) * Complex.I‖ ≤ Real.sqrt 2 := by
  rw [Real.le_sqrt (norm_nonneg _) (by norm_num), Complex.sq_norm, Complex.normSq_add_mul_I]
  have h1 : a ^ 2 ≤ 1 := by nlinarith [abs_le.mp ha]
  have h2 : b ^ 2 ≤ 1 := by nlinarith [abs_le.mp hb]
  linarith

/-- Sum identity for one convolution round: the sum of the rescaled fixed-point values is the
complex combination of the two coordinate sums, divided by `(2^p)²`. -/
private lemma buRound_sum_eq (H : Finset ℤ) (W : ℤ → ℤ) (f : ℤ → ℤ × ℤ) (p : ℕ) :
    (∑ h ∈ H, (((W h : ℝ) / (2 : ℝ) ^ p : ℝ) : ℂ) * HvdH.fxC p (f h))
    = ((((∑ h ∈ H, W h * (f h).1 : ℤ)) : ℂ)
        + (((∑ h ∈ H, W h * (f h).2 : ℤ)) : ℂ) * Complex.I)
        / ((2 : ℂ) ^ p * (2 : ℂ) ^ p) := by
  have h1 : ∀ h ∈ H, (((W h : ℝ) / (2 : ℝ) ^ p : ℝ) : ℂ) * HvdH.fxC p (f h)
      = ((W h : ℂ) * ((f h).1 : ℂ) + (W h : ℂ) * ((f h).2 : ℂ) * Complex.I)
          / ((2 : ℂ) ^ p * (2 : ℂ) ^ p) := by
    intro h _
    rw [HvdH.fxC]
    push_cast
    rw [div_mul_div_comm]
    congr 1
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_div]
  congr 1
  rw [Int.cast_sum, Int.cast_sum, Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl (fun h _ => ?_); push_cast; ring
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun h _ => ?_); push_cast; ring

/-- Truncating division of the two coordinates by `2^p` moves the complex value by at most `√2`:
each coordinate changes by at most `1` (`Work.Fx.FxTdivReal`) and `1² + 1² = 2`. -/
private lemma bu_tdiv_sqrt2 (A B : ℤ) (p : ℕ) :
    ‖(((Int.tdiv A ((2 : ℤ) ^ p) : ℤ) : ℂ)
        + ((Int.tdiv B ((2 : ℤ) ^ p) : ℤ) : ℂ) * Complex.I
      - ((A : ℂ) + (B : ℂ) * Complex.I) / (2 : ℂ) ^ p)‖ ≤ Real.sqrt 2 := by
  have hb : (0 : ℤ) < (2 : ℤ) ^ p := by positivity
  have hA := (Work.Fx.FxTdivReal A ((2 : ℤ) ^ p) hb).1
  have hB := (Work.Fx.FxTdivReal B ((2 : ℤ) ^ p) hb).1
  have hcast : (((2 : ℤ) ^ p : ℤ) : ℝ) = (2 : ℝ) ^ p := by push_cast; ring
  rw [hcast] at hA hB
  have hkey : (((Int.tdiv A ((2 : ℤ) ^ p) : ℤ) : ℂ)
        + ((Int.tdiv B ((2 : ℤ) ^ p) : ℤ) : ℂ) * Complex.I
      - ((A : ℂ) + (B : ℂ) * Complex.I) / (2 : ℂ) ^ p)
      = ((((Int.tdiv A ((2 : ℤ) ^ p) : ℤ) : ℝ) - (A : ℝ) / (2 : ℝ) ^ p : ℝ) : ℂ)
        + ((((Int.tdiv B ((2 : ℤ) ^ p) : ℤ) : ℝ) - (B : ℝ) / (2 : ℝ) ^ p : ℝ) : ℂ)
            * Complex.I := by
    push_cast
    field_simp
    ring
  rw [hkey]
  exact norm_ofReal_add_mul_I_le_sqrt_two _ _ hA hB

theorem buTdivKey (Wt : ℤ → ℤ → ℤ) (p α s t : ℕ) (hs : 0 < s) (v : Fin s → ℤ × ℤ) (ℓ : Fin s) :
    ∃ ρ : ℂ, (2 : ℝ) ^ p * ‖ρ‖ ≤ Real.sqrt 2 ∧
      HvdH.fxC p (Work.Resample.buRound Wt p α s t hs v ℓ)
        = (∑ h ∈ Work.Resample.egHset (Work.Resample.egM p α), (((Wt (ℓ : ℤ) h : ℝ) / (2 : ℝ) ^ p : ℝ) : ℂ)
            * HvdH.fxC p (v (Work.Resample.egIdx s hs ((ℓ : ℤ) + h)))) - ρ := by
  classical
  -- The two coordinate sums of the round and the numerators of the round / of the exact average.
  set S1 : ℤ := ∑ h ∈ egHset (egM p α),
    Wt (ℓ : ℤ) h * (v (egIdx s hs ((ℓ : ℤ) + h))).1 with hS1
  set S2 : ℤ := ∑ h ∈ egHset (egM p α),
    Wt (ℓ : ℤ) h * (v (egIdx s hs ((ℓ : ℤ) + h))).2 with hS2
  set W : ℂ := (S1 : ℂ) + (S2 : ℂ) * Complex.I with hW
  set X : ℂ := ((Int.tdiv S1 ((2 : ℤ) ^ p) : ℤ) : ℂ)
    + ((Int.tdiv S2 ((2 : ℤ) ^ p) : ℤ) : ℂ) * Complex.I with hX
  set c : ℂ := (2 : ℂ) ^ p with hc
  set ρ : ℂ := (W / c - X) / c with hρ
  have hcne : c ≠ 0 := by rw [hc]; exact pow_ne_zero _ (by norm_num)
  -- The exact average of the rounded weights, in complex form.
  have hT : (∑ h ∈ egHset (egM p α),
        (((Wt (ℓ : ℤ) h : ℝ) / (2 : ℝ) ^ p : ℝ) : ℂ)
          * HvdH.fxC p (v (egIdx s hs ((ℓ : ℤ) + h)))) = W / (c * c) := by
    have h := buRound_sum_eq (egHset (egM p α)) (fun h => Wt (ℓ : ℤ) h)
      (fun h => v (egIdx s hs ((ℓ : ℤ) + h))) p
    simpa [← hS1, ← hS2, hW, hc] using h
  -- The round, in complex form.
  have hfx : HvdH.fxC p (buRound Wt p α s t hs v ℓ) = X / c := by
    have hbu : buRound Wt p α s t hs v ℓ
        = (Int.tdiv S1 ((2 : ℤ) ^ p), Int.tdiv S2 ((2 : ℤ) ^ p)) := by
      simp only [buRound]
      rw [← hS1, ← hS2]
    rw [hbu]
    simp only [HvdH.fxC]
    rw [← hX, ← hc]
  refine ⟨ρ, ?_, ?_⟩
  · -- `‖W/c - X‖ ≤ √2`, and `ρ` is this divided by `c`.
    have hnorm : ‖W / c - X‖ ≤ Real.sqrt 2 := by
      have hWs : W / c - X = -(((Int.tdiv S1 ((2 : ℤ) ^ p) : ℤ) : ℂ)
          + ((Int.tdiv S2 ((2 : ℤ) ^ p) : ℤ) : ℂ) * Complex.I
          - ((S1 : ℂ) + (S2 : ℂ) * Complex.I) / (2 : ℂ) ^ p) := by
        rw [hX, hW, hc]; ring
      rw [hWs, norm_neg]
      exact bu_tdiv_sqrt2 S1 S2 p
    have heq : (2 : ℝ) ^ p * ‖ρ‖ = ‖W / c - X‖ := by
      rw [hρ, norm_div]
      have hnormc : ‖c‖ = (2 : ℝ) ^ p := by rw [hc, norm_pow]; norm_num
      rw [hnormc, mul_div_cancel₀ _ (by positivity : (2 : ℝ) ^ p ≠ 0)]
    rw [heq]; exact hnorm
  · -- `T - ρ = W/(c·c) - (W/c - X)/c = X/c = fxC p (buRound …)`.
    rw [hρ, hfx, hT]
    field_simp
    ring

end Work.Resample
