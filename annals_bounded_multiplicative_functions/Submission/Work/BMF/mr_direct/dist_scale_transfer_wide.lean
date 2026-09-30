import Mathlib
import Submission.Work.BMF.mr_direct.dist_scale_transfer
import Submission.Work.BMF.mr_direct.contDist_sq_le
import Submission.Work.BMF.mr_direct.D_mono
import Submission.Work.BMF.mr_direct.nat_cpow_I_norm_le
import Submission.Commons.NumberTheory.Mertens.mertens_lower
import Submission.Work.BMF.mr_direct.primeRecips_sub_le_log
import Submission.Work.BMF.mr_direct.log_bound_wide

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open BoundedMultiplicativeFunctions
open scoped ComplexConjugate

noncomputable section

/-- `𝔻 f g X` is nonnegative for `1`-bounded `f`, `g`: it is the square root of a
nonnegative prime sum. -/
private lemma D_nonneg (f g : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (X : ℝ) :
    0 ≤ BoundedMultiplicativeFunctions.𝔻 f g X := by
  unfold BoundedMultiplicativeFunctions.𝔻
  apply Real.rpow_nonneg
  apply Finset.sum_nonneg
  intro p hp
  have h1 : ‖f p * conj (g p)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg (f p), norm_nonneg (g p), hf p, hg p]
  have h2 : (f p * conj (g p)).re ≤ 1 := le_trans (Complex.re_le_norm _) h1
  exact div_nonneg (by linarith) (Nat.cast_nonneg p)

/-- The reciprocal-prime excess over `(x, Y]` is at most `16` in the wide window
`Y ≤ x ^ 8`, `16 ≤ x ≤ Y`. -/
private lemma primeRecips_sub_sixteen {x Y : ℝ} (hx : 16 ≤ x) (hxY : x ≤ Y) (hYx : Y ≤ x ^ 8) :
    Commons.NumberTheory.Mertens.primeRecips Y - Commons.NumberTheory.Mertens.primeRecips x ≤ 16 := by
  have hxpos : 0 < x := by linarith
  have hlog : Real.log Y ≤ 8 * Real.log x := by
    have h := Real.log_le_log (by linarith : (0:ℝ) < Y) hYx
    rw [Real.log_pow] at h
    norm_num at h
    linarith
  exact le_trans (primeRecips_sub_le_log (by linarith) hxY) (log_bound_wide hx hxY hlog)

/-- **Scale transfer in the wide window.**  If `𝔻 g (n ↦ n^{iu}) ≥ B` at the single scale `Y`,
for all `|u| ≤ M`, and `Y ≥ 16⁸`, then the same lower bound holds, at the price of the constant
`√(B²/2)`, at *every* scale `x` with `Y^{1/8} ≤ x ≤ 16 Y`.

The window `[Y^{1/8}, 16Y]` is wider than the one of `dist_scale_transfer`; the price is the
stronger hypothesis `Y ≥ 16⁸`, which guarantees `Y ≤ x⁸` and hence `log Y ≤ 8 log x`, so that
the intervening prime-reciprocal mass `∑_{x < p ≤ Y} 1/p` stays below `16 ≤ B²/4`. -/
theorem dist_scale_transfer_wide (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) (B M Y : ℝ)
    (hB : 8 ≤ B) (hY : 16 ^ 8 ≤ Y)
    (hhyp : ∀ u : ℝ, |u| ≤ M →
      B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y) :
    ∀ x : ℝ, Y ^ (1/8:ℝ) ≤ x → x ≤ 16 * Y → ∀ u : ℝ, |u| ≤ M →
      Real.sqrt (B ^ 2 / 2) ≤
        BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) x := by
  intro x hxlow hxupp u hu
  set ψ : ℕ → ℂ := fun n => (n : ℂ) ^ (Complex.I * u) with hψdef
  have hψ : ∀ n, ‖ψ n‖ ≤ 1 := fun n => nat_cpow_I_norm_le n u
  have hBpos : 0 < B := by linarith
  have hYpos : 0 < Y := by
    have : (0:ℝ) < 16^8 := by norm_num
    linarith
  -- `Y^{1/8} ≥ 16`, so `x ≥ 16`
  have h16 : (16:ℝ) ≤ Y ^ (1/8:ℝ) := by
    have hpow : ((16:ℝ)^8) ^ (1/8:ℝ) ≤ Y ^ (1/8:ℝ) :=
      Real.rpow_le_rpow (by norm_num) hY (by norm_num)
    have hval : ((16:ℝ)^8) ^ (1/8:ℝ) = 16 := by
      rw [← Real.rpow_natCast (16:ℝ) 8]
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 16)]
      norm_num
    rw [hval] at hpow
    exact hpow
  have hx16 : 16 ≤ x := le_trans h16 hxlow
  -- `Y ≤ x ^ 8`
  have hYx : Y ≤ x ^ 8 := by
    have h1 : (Y ^ (1/8:ℝ)) ^ 8 ≤ x ^ 8 :=
      pow_le_pow_left₀ (Real.rpow_nonneg hYpos.le _) hxlow 8
    have h2 : (Y ^ (1/8:ℝ)) ^ 8 = Y := by
      rw [← Real.rpow_natCast (Y ^ (1/8:ℝ)) 8]
      rw [← Real.rpow_mul hYpos.le]
      norm_num
    rwa [h2] at h1
  by_cases hxY : x ≤ Y
  · -- transfer down from `Y` to `x`: the intervening primes are cheap
    have hsub : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesLE ⌊Y⌋₊ :=
      Nat.primesLE_mono (Nat.floor_mono hxY)
    have hsdiff : (∑ p ∈ (Nat.primesLE ⌊Y⌋₊ \ Nat.primesLE ⌊x⌋₊), (1:ℝ)/(p:ℝ))
        = Commons.NumberTheory.Mertens.primeRecips Y
          - Commons.NumberTheory.Mertens.primeRecips x := by
      unfold Commons.NumberTheory.Mertens.primeRecips
      have h := Finset.sum_sdiff (s₁ := Nat.primesLE ⌊x⌋₊) (s₂ := Nat.primesLE ⌊Y⌋₊)
        (f := fun p => (1:ℝ)/(p:ℝ)) hsub
      linarith
    have hS : (∑ p ∈ (Nat.primesLE ⌊Y⌋₊ \ Nat.primesLE ⌊x⌋₊), (1:ℝ)/(p:ℝ)) ≤ 16 := by
      rw [hsdiff]
      exact primeRecips_sub_sixteen hx16 hxY hYx
    have hDY : B ≤ BoundedMultiplicativeFunctions.𝔻 g ψ Y := by
      rw [hψdef]; exact hhyp u hu
    have hDY2 : B^2 ≤ BoundedMultiplicativeFunctions.𝔻 g ψ Y ^ 2 := by
      have hnn := D_nonneg g ψ hg hψ Y
      nlinarith
    have hcd := contDist_sq_le g ψ hg hψ hxY
    have hDx2 : B^2/2 ≤ BoundedMultiplicativeFunctions.𝔻 g ψ x ^ 2 := by
      nlinarith [hDY2, hcd, hS, hB]
    have hDxnn : 0 ≤ BoundedMultiplicativeFunctions.𝔻 g ψ x := D_nonneg g ψ hg hψ x
    have hfinal : Real.sqrt (B^2/2) ≤ BoundedMultiplicativeFunctions.𝔻 g ψ x := by
      rw [Real.sqrt_le_iff]
      exact ⟨hDxnn, hDx2⟩
    rw [hψdef] at hfinal
    exact hfinal
  · -- `x > Y`: monotonicity of `𝔻` in the scale
    have hxY' : Y ≤ x := le_of_lt (lt_of_not_ge hxY)
    have hmono := D_mono g ψ hg hψ hxY'
    have hDY : B ≤ BoundedMultiplicativeFunctions.𝔻 g ψ Y := by
      rw [hψdef]; exact hhyp u hu
    have hBle : B ≤ BoundedMultiplicativeFunctions.𝔻 g ψ x := le_trans hDY hmono
    have hsqrtB : Real.sqrt (B^2/2) ≤ B := by
      rw [Real.sqrt_le_iff]
      exact ⟨hBpos.le, by nlinarith⟩
    have hfinal : Real.sqrt (B^2/2) ≤ BoundedMultiplicativeFunctions.𝔻 g ψ x :=
      le_trans hsqrtB hBle
    rw [hψdef] at hfinal
    exact hfinal

end

end Work.BMF.mr_direct
