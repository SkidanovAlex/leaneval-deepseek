import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Finset
open scoped BigOperators

namespace Commons.Analysis.Abel

open MeasureTheory intervalIntegral

/-- Fundamental theorem of calculus for `t ↦ t^{-s}` on the positive reals:
`n^{-s} - (n+1)^{-s} = s ∫_n^{n+1} t^{-s-1} dt` for `n ≥ 1`. -/
private lemma cpow_sub_succ {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)
      = s * ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), (x : ℂ) ^ (-s - 1) := by
  have hnn : (n : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  have hsne : -s ≠ 0 := by
    intro h
    have : s = 0 := neg_eq_zero.mp h
    rw [this] at hs; simp at hs
  have hderiv : ∀ x ∈ Set.uIcc (n:ℝ) (((n+1:ℕ)):ℝ),
      HasDerivAt (fun y : ℝ => (y:ℂ)^(-s)) ((-s) * (x:ℂ)^(-s-1)) x := by
    intro x hx
    rw [Set.uIcc_of_le hnn] at hx
    have hx1 : (1:ℝ) ≤ x := le_trans (by exact_mod_cast hn) hx.1
    have hxne : x ≠ 0 := by linarith
    exact hasDerivAt_ofReal_cpow_const hxne hsne
  have hcont : ContinuousOn (fun x : ℝ => (-s) * (x:ℂ)^(-s-1))
      (Set.uIcc (n:ℝ) (((n+1:ℕ)):ℝ)) := by
    intro x hx
    rw [Set.uIcc_of_le hnn] at hx
    have hx1 : (1:ℝ) ≤ x := le_trans (by exact_mod_cast hn) hx.1
    have hxne : x ≠ 0 := by linarith
    exact ((Complex.continuousAt_ofReal_cpow_const x (-s-1) (Or.inr hxne)).const_mul (-s)).continuousWithinAt
  have hint : IntervalIntegrable (fun x : ℝ => (-s) * (x:ℂ)^(-s-1)) volume (n:ℝ) (((n+1:ℕ)):ℝ) :=
    hcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hFTC
  have : s * ∫ x in (n:ℝ)..(((n+1:ℕ)):ℝ), (x:ℂ)^(-s-1)
      = (n:ℂ)^(-s) - (((n+1:ℕ)):ℂ)^(-s) := by
    linear_combination (-1 : ℂ) * hFTC
  exact this.symm

/-- The discrete difference of `k ↦ k^{-s}` is bounded by the corresponding
difference of the decreasing real weight `k ↦ k^{-s.re}`:
`‖n^{-s} - (n+1)^{-s}‖ ≤ (‖s‖/s.re) (n^{-s.re} - (n+1)^{-s.re})` for `n ≥ 1`. -/
private lemma diff_bound {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)‖
      ≤ (‖s‖ / s.re) * ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re)) := by
  have hnn : (n:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.le_succ n
  have hnpos : (0:ℝ) < n := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnorm : ‖(n:ℂ)^(-s) - (((n+1:ℕ)):ℂ)^(-s)‖
      = ‖s‖ * ‖∫ x in (n:ℝ)..(((n+1:ℕ)):ℝ), (x:ℂ)^(-s-1)‖ := by
    rw [cpow_sub_succ hs hn, norm_mul]
  rw [hnorm]
  have hle1 : ‖∫ x in (n:ℝ)..(((n+1:ℕ)):ℝ), (x:ℂ)^(-s-1)‖
      ≤ ∫ x in (n:ℝ)..(((n+1:ℕ)):ℝ), ‖(x:ℂ)^(-s-1)‖ :=
    intervalIntegral.norm_integral_le_integral_norm hnn
  have heq : ∫ x in (n:ℝ)..(((n+1:ℕ)):ℝ), ‖(x:ℂ)^(-s-1)‖
      = ∫ x in (n:ℝ)..(((n+1:ℕ)):ℝ), x^(-s.re - 1) := by
    apply intervalIntegral.integral_congr
    intro x hx
    change ‖(x:ℂ)^(-s-1)‖ = x^(-s.re-1)
    rw [Set.uIcc_of_le hnn] at hx
    have hxpos : 0 < x := lt_of_lt_of_le hnpos hx.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos (-s-1)]
    simp
  have hne : (-s.re - 1) ≠ -1 := by intro h; linarith [hs]
  have hnotmem : (0:ℝ) ∉ Set.uIcc (n:ℝ) (((n+1:ℕ)):ℝ) := by
    rw [Set.uIcc_of_le hnn, Set.mem_Icc]
    intro h; exact absurd h.1 (not_le.mpr hnpos)
  have hIval : ∫ x in (n:ℝ)..(((n+1:ℕ)):ℝ), x^(-s.re - 1)
      = ((n:ℝ)^(-s.re) - (((n+1:ℕ)):ℝ)^(-s.re)) / s.re := by
    rw [integral_rpow (Or.inr ⟨hne, hnotmem⟩)]
    have h1 : (-s.re - 1 + 1) = -s.re := by ring
    rw [h1]
    field_simp
    ring
  have h2 : ‖∫ x in (n:ℝ)..(((n+1:ℕ)):ℝ), (x:ℂ)^(-s-1)‖
      ≤ ((n:ℝ)^(-s.re) - (((n+1:ℕ)):ℝ)^(-s.re)) / s.re := by
    calc ‖∫ x in (n:ℝ)..(((n+1:ℕ)):ℝ), (x:ℂ)^(-s-1)‖
        ≤ ∫ x in (n:ℝ)..(((n+1:ℕ)):ℝ), ‖(x:ℂ)^(-s-1)‖ := hle1
      _ = ∫ x in (n:ℝ)..(((n+1:ℕ)):ℝ), x^(-s.re-1) := heq
      _ = ((n:ℝ)^(-s.re) - (((n+1:ℕ)):ℝ)^(-s.re)) / s.re := hIval
  calc ‖s‖ * ‖∫ x in (n:ℝ)..(((n+1:ℕ)):ℝ), (x:ℂ)^(-s-1)‖
      ≤ ‖s‖ * (((n:ℝ)^(-s.re) - (((n+1:ℕ)):ℝ)^(-s.re)) / s.re) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg s)
    _ = (‖s‖ / s.re) * ((n:ℝ)^(-s.re) - (((n+1:ℕ)):ℝ)^(-s.re)) := by ring

/-- Abel summation by parts over the window `Icc N M`, expressing the sum via the
partial sums `Σ_{k=N}^{n} a k` starting at `N`. -/
private lemma abel_window_from_N (a w : ℕ → ℂ) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Icc N M, a n * w n)
      = (∑ k ∈ Finset.Icc N M, a k) * w M
        + ∑ n ∈ Finset.Icc N (M - 1), (∑ k ∈ Finset.Icc N n, a k) * (w n - w (n + 1)) := by
  induction M, hNM using Nat.le_induction with
  | base =>
      have hempty : Finset.Icc N (N - 1) = ∅ := by
        rw [Finset.Icc_eq_empty_iff]; omega
      rw [hempty, Finset.sum_empty]
      simp [Finset.Icc_self]
  | succ m hm ih =>
      have hmm : m + 1 - 1 = m := by omega
      rw [hmm]
      have hsum1 : (∑ n ∈ Finset.Icc N (m + 1), a n * w n)
          = (∑ n ∈ Finset.Icc N m, a n * w n) + a (m + 1) * w (m + 1) :=
        Finset.sum_Icc_succ_top (by omega) (fun n => a n * w n)
      have hsum2 : (∑ k ∈ Finset.Icc N (m + 1), a k)
          = (∑ k ∈ Finset.Icc N m, a k) + a (m + 1) :=
        Finset.sum_Icc_succ_top (by omega) a
      have hsplit : (∑ n ∈ Finset.Icc N m, (∑ k ∈ Finset.Icc N n, a k) * (w n - w (n + 1)))
          = (∑ n ∈ Finset.Icc N (m - 1), (∑ k ∈ Finset.Icc N n, a k) * (w n - w (n + 1)))
            + (∑ k ∈ Finset.Icc N m, a k) * (w m - w (m + 1)) := by
        have := Finset.sum_Icc_succ_top (a := N) (b := m - 1) (by omega : N ≤ (m - 1) + 1)
          (fun n => (∑ k ∈ Finset.Icc N n, a k) * (w n - w (n + 1)))
        rwa [show (m - 1) + 1 = m from by omega] at this
      rw [hsum1, hsum2, hsplit, ih]
      ring

/-- Telescoping of the discrete decrements of `n ↦ n^{-σ}` over `Icc N (M-1)`. -/
private lemma sum_rpow_telescope (σ : ℝ) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Icc N (M - 1), ((n:ℝ)^(-σ) - ((n+1:ℕ):ℝ)^(-σ)))
      = (N:ℝ)^(-σ) - (M:ℝ)^(-σ) := by
  rcases lt_or_eq_of_le hNM with hlt | heq
  · have hle : N ≤ M - 1 := by omega
    have h := Finset.sum_Icc_sub (f := fun n : ℕ => -((n:ℝ)^(-σ))) hle
    rw [show (M - 1) + 1 = M from by omega] at h
    calc (∑ n ∈ Finset.Icc N (M - 1), ((n:ℝ)^(-σ) - ((n+1:ℕ):ℝ)^(-σ)))
        = ∑ i ∈ Finset.Icc N (M - 1), (-(((i+1:ℕ)):ℝ)^(-σ) - -((i:ℝ)^(-σ))) := by
          apply Finset.sum_congr rfl; intro i _; ring
      _ = (N:ℝ)^(-σ) - (M:ℝ)^(-σ) := by rw [h]; ring
  · subst heq
    rw [Finset.Icc_eq_empty_iff.mpr (by omega : ¬ N ≤ N - 1), Finset.sum_empty]
    ring

theorem tail_bound_finite {a : ℕ → ℂ} (B : ℝ) (hB : ∀ x y : ℕ, x ≤ y →
    ‖∑ n ∈ Finset.Icc x y, a n‖ ≤ B) (s : ℂ) (hs : 0 < s.re)
    {N M : ℕ} (hNM : N ≤ M) (hN1 : 1 ≤ N) :
    ‖∑ k ∈ Finset.Icc N M, a k * (k : ℂ) ^ (-s)‖
      ≤ B * (N : ℝ) ^ (-s.re) * (1 + ‖s‖ / s.re) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB N M hNM)
  have hNpos : (0:ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hsr : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg s) hs.le
  have hMpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have habel := abel_window_from_N a (fun k : ℕ => (k:ℂ)^(-s)) hN1 hNM
  rw [habel]
  have hterm1 : ‖(∑ k ∈ Finset.Icc N M, a k) * (M:ℂ)^(-s)‖ ≤ B * (N:ℝ)^(-s.re) := by
    have h1 : ‖∑ k ∈ Finset.Icc N M, a k‖ ≤ B := hB N M hNM
    have h2 : ‖(M:ℂ)^(-s)‖ ≤ (N:ℝ)^(-s.re) := by
      have hMposN : 0 < M := by omega
      rw [Complex.norm_natCast_cpow_of_pos hMposN, Complex.neg_re]
      exact Real.rpow_le_rpow_of_nonpos hNpos (by exact_mod_cast hNM) (by linarith)
    calc ‖(∑ k ∈ Finset.Icc N M, a k) * (M:ℂ)^(-s)‖
        = ‖∑ k ∈ Finset.Icc N M, a k‖ * ‖(M:ℂ)^(-s)‖ := norm_mul _ _
      _ ≤ B * (N:ℝ)^(-s.re) := mul_le_mul h1 h2 (norm_nonneg _) hB0
  have hterm2 : ‖∑ n ∈ Finset.Icc N (M-1),
        (∑ k ∈ Finset.Icc N n, a k) * ((n:ℂ)^(-s) - ((n+1:ℕ):ℂ)^(-s))‖
      ≤ B * (‖s‖/s.re) * (N:ℝ)^(-s.re) := by
    have htele := sum_rpow_telescope (s.re) hN1 hNM
    calc ‖∑ n ∈ Finset.Icc N (M-1),
            (∑ k ∈ Finset.Icc N n, a k) * ((n:ℂ)^(-s) - ((n+1:ℕ):ℂ)^(-s))‖
        ≤ ∑ n ∈ Finset.Icc N (M-1),
            ‖(∑ k ∈ Finset.Icc N n, a k) * ((n:ℂ)^(-s) - ((n+1:ℕ):ℂ)^(-s))‖ :=
              norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc N (M-1),
            B * ((‖s‖/s.re) * ((n:ℝ)^(-s.re) - ((n+1:ℕ):ℝ)^(-s.re))) := by
            apply Finset.sum_le_sum
            intro n hn
            rw [Finset.mem_Icc] at hn
            have hn1 : 1 ≤ n := le_trans hN1 hn.1
            have hAn : ‖∑ k ∈ Finset.Icc N n, a k‖ ≤ B := hB N n hn.1
            have hdiff := diff_bound hs hn1
            calc ‖(∑ k ∈ Finset.Icc N n, a k) * ((n:ℂ)^(-s) - ((n+1:ℕ):ℂ)^(-s))‖
                = ‖∑ k ∈ Finset.Icc N n, a k‖ * ‖(n:ℂ)^(-s) - ((n+1:ℕ):ℂ)^(-s)‖ :=
                    norm_mul _ _
              _ ≤ B * ((‖s‖/s.re) * ((n:ℝ)^(-s.re) - ((n+1:ℕ):ℝ)^(-s.re))) :=
                    mul_le_mul hAn hdiff (norm_nonneg _) hB0
      _ = (B * (‖s‖/s.re)) * ∑ n ∈ Finset.Icc N (M-1),
            ((n:ℝ)^(-s.re) - ((n+1:ℕ):ℝ)^(-s.re)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro n _; ring
      _ = (B * (‖s‖/s.re)) * ((N:ℝ)^(-s.re) - (M:ℝ)^(-s.re)) := by rw [htele]
      _ ≤ (B * (‖s‖/s.re)) * (N:ℝ)^(-s.re) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB0 hsr)
            exact sub_le_self _ (Real.rpow_nonneg hMpos.le _)
  calc ‖(∑ k ∈ Finset.Icc N M, a k) * (M:ℂ)^(-s)
        + ∑ n ∈ Finset.Icc N (M-1), (∑ k ∈ Finset.Icc N n, a k) * ((n:ℂ)^(-s) - ((n+1:ℕ):ℂ)^(-s))‖
      ≤ ‖(∑ k ∈ Finset.Icc N M, a k) * (M:ℂ)^(-s)‖
        + ‖∑ n ∈ Finset.Icc N (M-1),
            (∑ k ∈ Finset.Icc N n, a k) * ((n:ℂ)^(-s) - ((n+1:ℕ):ℂ)^(-s))‖ := norm_add_le _ _
    _ ≤ B * (N:ℝ)^(-s.re) + B * (‖s‖/s.re) * (N:ℝ)^(-s.re) := add_le_add hterm1 hterm2
    _ = B * (N:ℝ)^(-s.re) * (1 + ‖s‖/s.re) := by ring

end Commons.Analysis.Abel