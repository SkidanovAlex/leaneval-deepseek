/-
# `Submission.Work.FIArea6Road.HeartAux`

Two elementary bricks of the §16 heart (`Work.FIArea6.S16TsumHeart`):

* `norm_Tsum_le_window` — the *trivial* (no-cancellation) bound for the Möbius-twisted Hecke sum,
  obtained from the finite-window form `Work.FIArea6Road.TsumWindow` by the triangle inequality and
  `‖λ_m(n)‖ ≤ 4τ(n)`, `|γ(n;C)| ≤ τ(n)`, `|p| ≤ 1`:
  `‖Tsum Pa χ m p‖ ≤ 4·Σ_{1 ≤ n ≤ ⌊(1+θ)N⌋} τ(n)²`.
  This is the input of the *trivial regime* of the heart (the complement of the contour regime in
  the §16 contour shift, where the shift's far piece cannot be bounded by `exp(-√log N)` because
  the amplitude `θ^{-1} = (log x)^{A'}` may exceed `exp(√log N/2)`).

* `norm_int_shift_le` — Cauchy's theorem on the rectangle `[σ₀,σ] × [-T,T]` for an analytic `G`,
  in the *norm* form in which the contour shift consumes it: the integral on the shifted (left)
  vertical segment is bounded by the integral on the original (right) vertical segment plus the two
  horizontal segments.
-/
import Mathlib
import Submission.Work.FIArea6Road.TsumWindow
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIPlan.Interface

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FIArea6Road

open Finset MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `|μ(n)| ≤ 1`, in the form needed for the trivial mass bound (the `ℂ`-valued version).

(The name carries the `aux_` prefix because `Submission.Work.FIArea6Road.EulerDefs` — written
later, in the same directory — also defines a `norm_moebius_le_one`, and the two modules are
imported together by the §16 heart.) -/
lemma aux_norm_moebius_le_one (n : ℕ) : ‖((ArithmeticFunction.moebius n : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> rw [h] <;> norm_num

lemma norm_gammaTrunc_le (C : ℝ) (n : ℕ) :
    ‖(Work.FIPlan.gammaTrunc C n : ℂ)‖ ≤ (n.divisors.card : ℝ) := by
  rw [Work.FIPlan.gammaTrunc, Complex.norm_real, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C),
        |(ArithmeticFunction.moebius d : ℝ)|
      ≤ ∑ _d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C), (1 : ℝ) := by
        refine Finset.sum_le_sum fun d _ => ?_
        have h := aux_norm_moebius_le_one d
        rw [Complex.norm_real, Real.norm_eq_abs] at h
        simpa using h
    _ ≤ (n.divisors.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast Finset.card_filter_le n.divisors _

lemma norm_tsumTerm_le (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (hp : ∀ u : ℝ, |p u| ≤ 1) (n : ℕ) :
    ‖Work.FIArea6.TauPieces.tsumTerm Pa chi m p n‖
      ≤ 4 * ((n.divisors.card : ℝ)) ^ 2 := by
  unfold Work.FIArea6.TauPieces.tsumTerm
  by_cases hn : Work.FIArea6Hecke.NoSmallPrimesNat Pa n
  · rw [if_pos hn, norm_mul, norm_mul, norm_mul]
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        exact (hn 2 Nat.prime_two Pa.hP2 (dvd_zero 2)).elim
      · exact h
    have h1 : ‖Work.FIArea5.S16Hecke.heckeLam chi m n‖ ≤ 4 * (n.divisors.card : ℝ) :=
      Work.FIArea5.S16Hecke.heckeLam_bound chi m hchi hn1
    have h2 := aux_norm_moebius_le_one n
    have h3 := norm_gammaTrunc_le Pa.C n
    have h4 : ‖(p (n : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hp _
    have hd : (0 : ℝ) ≤ (n.divisors.card : ℝ) := by positivity
    calc ‖Work.FIArea5.S16Hecke.heckeLam chi m n‖ * ‖((ArithmeticFunction.moebius n : ℝ) : ℂ)‖
            * ‖(Work.FIPlan.gammaTrunc Pa.C n : ℂ)‖ * ‖(p (n : ℝ) : ℂ)‖
        ≤ (4 * (n.divisors.card : ℝ)) * 1 * (n.divisors.card : ℝ) * 1 :=
          mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (by norm_num) (by positivity)) h3
            (norm_nonneg _) (by positivity)) h4 (norm_nonneg _) (by positivity)
      _ = 4 * ((n.divisors.card : ℝ)) ^ 2 := by ring
  · rw [if_neg hn, norm_zero]; positivity

theorem norm_Tsum_le_window (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (p : ℝ → ℝ) (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (hp : ∀ u : ℝ, |p u| ≤ 1)
    (hpsupp : ∀ u : ℝ, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) :
    ‖Work.FIArea6Hecke.Tsum Pa chi m p‖
      ≤ 4 * ∑ n ∈ Finset.Icc 1 ⌊(1 + Pa.θ) * Pa.N⌋₊, ((n.divisors.card : ℝ)) ^ 2 := by
  rw [TsumWindow Pa chi m p hpsupp]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun n _ => norm_tsumTerm_le Pa chi m p hchi hp n)

theorem norm_int_shift_le {G : ℂ → ℂ} {σ₀ σ T : ℝ}
    (hG : DifferentiableOn ℂ G (Set.uIcc σ₀ σ ×ℂ Set.uIcc (-T) T)) :
    ‖∫ y in (-T)..T, G ((σ₀ : ℂ) + (y : ℂ) * Complex.I)‖
      ≤ ‖∫ y in (-T)..T, G ((σ : ℂ) + (y : ℂ) * Complex.I)‖
        + ‖∫ x in σ₀..σ, G ((x : ℂ) + ((-T:ℝ) : ℂ) * Complex.I)‖
        + ‖∫ x in σ₀..σ, G ((x : ℂ) + ((T:ℝ) : ℂ) * Complex.I)‖ := by
  have hcauchy : (∫ x in σ₀..σ, G ((x : ℂ) + ((-T:ℝ) : ℂ) * Complex.I))
      - (∫ x in σ₀..σ, G ((x : ℂ) + ((T:ℝ) : ℂ) * Complex.I))
      + Complex.I * (∫ y in (-T)..T, G ((σ : ℂ) + (y : ℂ) * Complex.I))
      - Complex.I * (∫ y in (-T)..T, G ((σ₀ : ℂ) + (y : ℂ) * Complex.I)) = 0 := by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
      ((σ₀ : ℂ) - (T : ℂ) * Complex.I) ((σ : ℂ) + (T : ℂ) * Complex.I) ?_
    · simpa [smul_eq_mul, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc,
        Complex.ofReal_neg] using h
    · rw [show ((σ₀ : ℂ) - (T : ℂ) * Complex.I).re = σ₀ from by simp,
          show ((σ : ℂ) + (T : ℂ) * Complex.I).re = σ from by simp,
          show ((σ₀ : ℂ) - (T : ℂ) * Complex.I).im = -T from by simp,
          show ((σ : ℂ) + (T : ℂ) * Complex.I).im = T from by simp]
      exact hG
  set A : ℂ := ∫ x in σ₀..σ, G ((x : ℂ) + ((-T:ℝ) : ℂ) * Complex.I) with hA
  set B : ℂ := ∫ x in σ₀..σ, G ((x : ℂ) + ((T:ℝ) : ℂ) * Complex.I) with hB
  set C : ℂ := ∫ y in (-T)..T, G ((σ : ℂ) + (y : ℂ) * Complex.I) with hC
  set D : ℂ := ∫ y in (-T)..T, G ((σ₀ : ℂ) + (y : ℂ) * Complex.I) with hD
  have hID : Complex.I * D = (A - B) + Complex.I * C := (sub_eq_zero.mp hcauchy).symm
  have hbound : ‖D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ := by
    have h1' : ‖D‖ = ‖Complex.I * D‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    rw [h1', hID]
    calc ‖(A - B) + Complex.I * C‖ ≤ ‖A - B‖ + ‖Complex.I * C‖ := norm_add_le _ _
      _ = ‖A - B‖ + ‖C‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ (‖A‖ + ‖B‖) + ‖C‖ := by linarith [norm_sub_le A B]
  linarith [hbound]

/-- **The trivial mass bound on the *support window*.**  Because the radial mollifier `p` vanishes
at every `u ≤ N` (`hpsupp`), every summand with `n ≤ ⌊N⌋₊` is zero, so the trivial bound only has
to be summed over the actual window `⌊N⌋₊ + 1 ≤ n ≤ ⌊(1+θ)N⌋₊` — which is what gives the factor
`θ` in the trivial regime of the §16 heart. -/
lemma tsumTerm_eq_zero_of_p_zero (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (p : ℝ → ℝ) {n : ℕ} (h : p (n : ℝ) = 0) :
    Work.FIArea6.TauPieces.tsumTerm Pa chi m p n = 0 := by
  unfold Work.FIArea6.TauPieces.tsumTerm
  split
  · rw [h, Complex.ofReal_zero, mul_zero]
  · rfl

lemma tsumTerm_eq_zero_of_le (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (p : ℝ → ℝ) (hpsupp : ∀ u : ℝ, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    {n : ℕ} (hn : (n : ℝ) ≤ Pa.N) : Work.FIArea6.TauPieces.tsumTerm Pa chi m p n = 0 := by
  refine tsumTerm_eq_zero_of_p_zero Pa chi m p ?_
  by_contra hne
  have h2 := (hpsupp (n : ℝ) hne).1
  linarith

theorem norm_Tsum_le_suppWindow (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (p : ℝ → ℝ) (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (hp : ∀ u : ℝ, |p u| ≤ 1)
    (hpsupp : ∀ u : ℝ, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) :
    ‖Work.FIArea6Hecke.Tsum Pa chi m p‖
      ≤ 4 * ∑ n ∈ Finset.Icc (⌊Pa.N⌋₊ + 1) ⌊(1 + Pa.θ) * Pa.N⌋₊,
            ((n.divisors.card : ℝ)) ^ 2 := by
  set M : ℕ := ⌊(1 + Pa.θ) * Pa.N⌋₊ with hM
  have hTW := TsumWindow Pa chi m p hpsupp
  rw [← hM] at hTW
  by_cases hcase : ⌊Pa.N⌋₊ + 1 ≤ M
  · have hsub : Finset.Icc (⌊Pa.N⌋₊ + 1) M ⊆ Finset.Icc 1 M := by
      intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      exact ⟨by omega, hn.2⟩
    have hzero : ∀ n ∈ Finset.Icc 1 M, n ∉ Finset.Icc (⌊Pa.N⌋₊ + 1) M →
        Work.FIArea6.TauPieces.tsumTerm Pa chi m p n = 0 := by
      intro n hn hnnot
      rw [Finset.mem_Icc] at hn
      refine tsumTerm_eq_zero_of_le Pa chi m p hpsupp ?_
      have hle : n ≤ ⌊Pa.N⌋₊ := by
        by_contra hc
        exact hnnot (Finset.mem_Icc.mpr ⟨by omega, hn.2⟩)
      have h2 : (n : ℝ) ≤ (⌊Pa.N⌋₊ : ℝ) := by exact_mod_cast hle
      have h3 : (⌊Pa.N⌋₊ : ℝ) ≤ Pa.N := Nat.floor_le (by linarith [Pa.hN1])
      linarith
    have hsum := Finset.sum_subset hsub hzero
    rw [hTW, ← hsum]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun n _ => norm_tsumTerm_le Pa chi m p hchi hp n)
  · have hzero : ∀ n ∈ Finset.Icc 1 M,
        Work.FIArea6.TauPieces.tsumTerm Pa chi m p n = 0 := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      refine tsumTerm_eq_zero_of_le Pa chi m p hpsupp ?_
      have hle : n ≤ ⌊Pa.N⌋₊ := by omega
      have h2 : (n : ℝ) ≤ (⌊Pa.N⌋₊ : ℝ) := by exact_mod_cast hle
      have h3 : (⌊Pa.N⌋₊ : ℝ) ≤ Pa.N := Nat.floor_le (by linarith [Pa.hN1])
      linarith
    rw [hTW, Finset.sum_eq_zero hzero, norm_zero]
    have hnn : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc (⌊Pa.N⌋₊ + 1) M, ((n.divisors.card : ℝ)) ^ 2 :=
      Finset.sum_nonneg (fun n _ => sq_nonneg _)
    linarith [hnn]

end

end Work.FIArea6Road
