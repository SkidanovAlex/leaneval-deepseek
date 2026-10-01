import Mathlib
import Submission.Work.LinnikAreas2.d1_of_area1
import Submission.Work.LinnikAreas.Density4.det_split

namespace Work.LinnikAreas2

open scoped BigOperators

/-! ## HB §11 — the diagonal bound for the `a`-coefficients

HB (11.17) evaluates the diagonal `Σ_n (Σ_{d|n} θ_d)² n^{1-2Re ρ} wt_n`.  The present file
records the elementary consequence used in the assembly: the diagonal of the Gram matrix of the
family `a_n` of HB (11.11) is bounded by the value of that series.

The two ingredients are

* `summable_thetaS_diag`: the diagonal series is summable (no hypothesis at all), since
  `|Σ_{d|n} θ_d| ≤ n` and `wt_n` is a difference of the two exponentials
  `e^{-n/q^x}`, `e^{-n(log q)²/q^u}`;
* a termwise comparison `‖a_n‖² ≤ w_χ · (Σ_{d|n} θ_d)² n^{1-2Re ρ} wt_n`, because
  `‖χ(n)‖ ≤ 1` and `‖n^{1/2-ρ}‖ = n^{1/2-Re ρ}` (and `a_0 = 0`).
-/

/-- The diagonal series `Σ_n (Σ_{d|n} θ_d)² n^{1-2Re ρ} wt_n` of HB (11.17) converges. -/
theorem summable_thetaS_diag {q : ℕ} [NeZero q] (u w x : ℝ) (ρ : ℂ) :
    Summable (fun n : ℕ => ((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ))^2
        * (n:ℝ)^(1 - 2*ρ.re) * Work.LinnikAreas2.WT q u x n) := by
  rcases eq_or_ne q 1 with hq1 | hq1
  · subst hq1
    -- for `q = 1` every `θ_d` vanishes, so the series is identically zero
    have hone : ((1:ℕ):ℝ)^w = (1:ℝ) := by
      rw [show ((1:ℕ):ℝ) = (1:ℝ) by norm_num, Real.one_rpow]
    have hthetazero : ∀ d : ℕ, Work.LinnikAreas.Density4.thetaM (((1:ℕ):ℝ)^w) d = 0 := by
      intro d
      rw [hone]
      unfold Work.LinnikAreas.Density4.thetaM
      by_cases hd : (d:ℝ) ≤ (1:ℝ)
      · rw [if_pos hd, Real.log_one, div_zero]
      · rw [if_neg hd]
    have hfun : (fun n : ℕ => ((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM (((1:ℕ):ℝ)^w) d : ℝ))^2
        * (n:ℝ)^(1 - 2*ρ.re) * Work.LinnikAreas2.WT 1 u x n) = 0 := by
      funext n
      rw [Finset.sum_eq_zero (fun d _ => hthetazero d)]
      simp
    rw [hfun]
    exact summable_zero
  · -- `q ≥ 2`: `|Σ_{d|n} θ_d| ≤ n` and `wt_n` is a difference of two decaying exponentials
    have hq2 : 2 ≤ q := by have hq0 : q ≠ 0 := NeZero.ne q; omega
    have hqpos : (0:ℝ) < (q:ℝ) := by positivity
    have hqgt1 : (1:ℝ) < (q:ℝ) := by exact_mod_cast hq2
    have hαpos : 0 < 1 / (q:ℝ)^x := one_div_pos.mpr (Real.rpow_pos_of_pos hqpos x)
    have hβpos : 0 < (Real.log (q:ℝ))^2 / (q:ℝ)^u :=
      div_pos (sq_pos_of_pos (Real.log_pos hqgt1)) (Real.rpow_pos_of_pos hqpos u)
    have hs1 : Summable (fun n : ℕ => (n:ℝ)^(⌈3 - 2*ρ.re⌉₊) * Real.exp (-(1 / (q:ℝ)^x) * n)) :=
      Real.summable_pow_mul_exp_neg_nat_mul _ hαpos
    have hs2 : Summable (fun n : ℕ =>
        (n:ℝ)^(⌈3 - 2*ρ.re⌉₊) * Real.exp (-((Real.log (q:ℝ))^2 / (q:ℝ)^u) * n)) :=
      Real.summable_pow_mul_exp_neg_nat_mul _ hβpos
    have hmaj : Summable (fun n : ℕ => (n:ℝ)^(⌈3 - 2*ρ.re⌉₊) * Real.exp (-(1 / (q:ℝ)^x) * n)
        + (n:ℝ)^(⌈3 - 2*ρ.re⌉₊) * Real.exp (-((Real.log (q:ℝ))^2 / (q:ℝ)^u) * n)) :=
      hs1.add hs2
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hmaj
    intro n
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst hn0
      have hz : ((∑ d ∈ (0:ℕ).divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ))^2
          * ((0:ℕ):ℝ)^(1 - 2*ρ.re) * Work.LinnikAreas2.WT q u x 0 = 0 := by
        rw [Nat.divisors_zero, Finset.sum_empty]
        ring
      rw [hz, norm_zero]
      positivity
    · have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have hSn : |(∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)| ≤ (n:ℝ) :=
        Work.LinnikAreas.Density4.abs_thetaS_le ((q:ℝ)^w) n
      have hSsq : (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)^2
          ≤ (n:ℝ)^2 := by
        have h := pow_le_pow_left₀ (abs_nonneg _) hSn 2
        simpa only [sq_abs] using h
      have hpow : (n:ℝ)^2 * (n:ℝ)^(1 - 2*ρ.re) ≤ (n:ℝ)^(⌈3 - 2*ρ.re⌉₊) := by
        have hnpos : (0:ℝ) < (n:ℝ) := by linarith
        have h3 : (3 - 2*ρ.re) ≤ ((⌈3 - 2*ρ.re⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
        calc (n:ℝ)^2 * (n:ℝ)^(1 - 2*ρ.re)
            = (n:ℝ)^((2:ℝ) + (1 - 2*ρ.re)) := by
                rw [← Real.rpow_natCast (n:ℝ) 2, ← Real.rpow_add hnpos]
                norm_num
          _ = (n:ℝ)^(3 - 2*ρ.re) := by rw [show (2:ℝ) + (1-2*ρ.re) = 3 - 2*ρ.re by ring]
          _ ≤ (n:ℝ)^((⌈3 - 2*ρ.re⌉₊ : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 h3
          _ = (n:ℝ)^(⌈3 - 2*ρ.re⌉₊) := Real.rpow_natCast _ _
      have hWT : |Work.LinnikAreas2.WT q u x n|
          ≤ Real.exp (-(1 / (q:ℝ)^x) * n) + Real.exp (-((Real.log (q:ℝ))^2 / (q:ℝ)^u) * n) := by
        have h1 : Work.LinnikAreas2.WT q u x n
            = Real.exp (-(n:ℝ)/(q:ℝ)^x) - Real.exp (-(n:ℝ)*(Real.log (q:ℝ))^2/(q:ℝ)^u) := rfl
        rw [h1]
        calc |Real.exp (-(n:ℝ)/(q:ℝ)^x) - Real.exp (-(n:ℝ)*(Real.log (q:ℝ))^2/(q:ℝ)^u)|
            = |Real.exp (-(n:ℝ)/(q:ℝ)^x) + -Real.exp (-(n:ℝ)*(Real.log (q:ℝ))^2/(q:ℝ)^u)| := by
                rw [sub_eq_add_neg]
          _ ≤ |Real.exp (-(n:ℝ)/(q:ℝ)^x)| + |-Real.exp (-(n:ℝ)*(Real.log (q:ℝ))^2/(q:ℝ)^u)| :=
                abs_add_le _ _
          _ = |Real.exp (-(n:ℝ)/(q:ℝ)^x)| + |Real.exp (-(n:ℝ)*(Real.log (q:ℝ))^2/(q:ℝ)^u)| := by
                rw [abs_neg]
          _ = Real.exp (-(n:ℝ)/(q:ℝ)^x) + Real.exp (-(n:ℝ)*(Real.log (q:ℝ))^2/(q:ℝ)^u) := by
                rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
          _ = Real.exp (-(1/(q:ℝ)^x) * n) + Real.exp (-((Real.log (q:ℝ))^2/(q:ℝ)^u) * n) := by
                rw [show -(n:ℝ)/(q:ℝ)^x = -(1/(q:ℝ)^x) * (n:ℝ) by ring,
                    show -(n:ℝ)*(Real.log (q:ℝ))^2/(q:ℝ)^u
                      = -((Real.log (q:ℝ))^2/(q:ℝ)^u) * (n:ℝ) by ring]
      calc ‖(∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)^2
            * (n:ℝ)^(1 - 2*ρ.re) * Work.LinnikAreas2.WT q u x n‖
          = (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)^2
            * (n:ℝ)^(1 - 2*ρ.re) * |Work.LinnikAreas2.WT q u x n| := by
              rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _),
                  abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
        _ ≤ (n:ℝ)^2 * (n:ℝ)^(1 - 2*ρ.re) * |Work.LinnikAreas2.WT q u x n| := by gcongr
        _ ≤ (n:ℝ)^(⌈3 - 2*ρ.re⌉₊) * |Work.LinnikAreas2.WT q u x n| :=
              mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
        _ ≤ (n:ℝ)^(⌈3 - 2*ρ.re⌉₊)
              * (Real.exp (-(1 / (q:ℝ)^x) * n) + Real.exp (-((Real.log (q:ℝ))^2 / (q:ℝ)^u) * n)) :=
              mul_le_mul_of_nonneg_left hWT (pow_nonneg (Nat.cast_nonneg n) _)
        _ = (n:ℝ)^(⌈3 - 2*ρ.re⌉₊) * Real.exp (-(1 / (q:ℝ)^x) * n)
              + (n:ℝ)^(⌈3 - 2*ρ.re⌉₊) * Real.exp (-((Real.log (q:ℝ))^2 / (q:ℝ)^u) * n) := by ring

/-- **HB §11, diagonal bound.**  If the weighted diagonal series `Σ_n (Σ_{d|n}θ_d)² n^{1-2Re ρ} wt_n`
satisfies `w_χ · Σ_n ⋯ ≤ 1 + c₁`, then the sum of the squared norms of the coefficients `a_n` of
HB (11.11) is at most `1 + c₁`. -/
theorem acoef_diag_bound {q : ℕ} [NeZero q] {u w x : ℝ}
    (χ : DirichletCharacter ℂ q) (ρ : ℂ) {wc c1 : ℝ}
    (hwc : 0 ≤ wc) (hwt : ∀ n : ℕ, 0 ≤ Work.LinnikAreas2.WT q u x n)
    (hdiag : wc * (∑' n : ℕ, ((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ))^2
        * (n:ℝ)^(1 - 2*ρ.re) * Work.LinnikAreas2.WT q u x n) ≤ 1 + c1) :
    (∑' n : ℕ, ‖Work.LinnikAreas2.acoef q u w x χ ρ wc n‖^2) ≤ 1 + c1 := by
  -- the termwise comparison `‖a_n‖² ≤ w_χ · (Σ_{d|n}θ_d)² n^{1-2Re ρ} wt_n`
  have key : ∀ n : ℕ, ‖Work.LinnikAreas2.acoef q u w x χ ρ wc n‖^2
      ≤ wc * ((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)^2
        * (n:ℝ)^(1 - 2*ρ.re) * Work.LinnikAreas2.WT q u x n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst hn0
      rw [Work.LinnikAreas2.acoef_zero]
      simp [Nat.divisors_zero]
    · have hnormeq : ‖Work.LinnikAreas2.acoef q u w x χ ρ wc n‖
          = Real.sqrt wc * |(∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)|
            * ‖χ (n : ZMod q)‖
            * (n:ℝ)^(1/2 - ρ.re) * Real.sqrt (Work.LinnikAreas2.WT q u x n) := by
        simp only [Work.LinnikAreas2.acoef, Work.LinnikAreas.Density4.thetaS]
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg wc)]
        rw [Complex.norm_real, Real.norm_eq_abs]
        rw [Complex.norm_natCast_cpow_of_pos hn]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        congr 2
        simp
      have hbound : ‖Work.LinnikAreas2.acoef q u w x χ ρ wc n‖
          ≤ Real.sqrt wc * |(∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)|
            * (n:ℝ)^(1/2 - ρ.re)
            * Real.sqrt (Work.LinnikAreas2.WT q u x n) := by
        rw [hnormeq]
        calc Real.sqrt wc * |(∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)|
                * ‖χ (n : ZMod q)‖
                * (n:ℝ)^(1/2 - ρ.re) * Real.sqrt (Work.LinnikAreas2.WT q u x n)
            ≤ Real.sqrt wc * |(∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)|
                * 1 * (n:ℝ)^(1/2 - ρ.re) * Real.sqrt (Work.LinnikAreas2.WT q u x n) := by
              gcongr
              exact DirichletCharacter.norm_le_one χ _
          _ = Real.sqrt wc * |(∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)|
                * (n:ℝ)^(1/2 - ρ.re)
                * Real.sqrt (Work.LinnikAreas2.WT q u x n) := by ring
      have hna : ((n:ℝ)^(1/2 - ρ.re))^2 = (n:ℝ)^(1 - 2*ρ.re) := by
        rw [sq, ← Real.rpow_add (by exact_mod_cast hn)]
        congr 1
        ring
      have hsquare : (Real.sqrt wc
            * |(∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)|
            * (n:ℝ)^(1/2 - ρ.re) * Real.sqrt (Work.LinnikAreas2.WT q u x n))^2
          = wc * (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)^2
            * (n:ℝ)^(1 - 2*ρ.re)
            * Work.LinnikAreas2.WT q u x n := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hwc, sq_abs, hna, Real.sq_sqrt (hwt n)]
      calc ‖Work.LinnikAreas2.acoef q u w x χ ρ wc n‖^2
          ≤ (Real.sqrt wc
              * |(∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)|
              * (n:ℝ)^(1/2 - ρ.re) * Real.sqrt (Work.LinnikAreas2.WT q u x n))^2 :=
              pow_le_pow_left₀ (by positivity) hbound 2
        _ = wc * (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)^2
              * (n:ℝ)^(1 - 2*ρ.re)
              * Work.LinnikAreas2.WT q u x n := hsquare
        _ = wc * ((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)^2
              * (n:ℝ)^(1 - 2*ρ.re) * Work.LinnikAreas2.WT q u x n) := by ring
  have hsummable : Summable (fun n : ℕ =>
      ((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ))^2
        * (n:ℝ)^(1 - 2*ρ.re) * Work.LinnikAreas2.WT q u x n) := summable_thetaS_diag u w x ρ
  have hwcsum : Summable (fun n : ℕ => wc *
      ((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)^2
        * (n:ℝ)^(1 - 2*ρ.re) * Work.LinnikAreas2.WT q u x n)) := hsummable.mul_left wc
  have hgcsum : Summable (fun n : ℕ => ‖Work.LinnikAreas2.acoef q u w x χ ρ wc n‖^2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) key hwcsum
  have hle : (∑' n : ℕ, wc *
      ((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)^2
        * (n:ℝ)^(1 - 2*ρ.re) * Work.LinnikAreas2.WT q u x n)) ≤ 1 + c1 := by
    rw [tsum_mul_left]
    exact hdiag
  calc (∑' n : ℕ, ‖Work.LinnikAreas2.acoef q u w x χ ρ wc n‖^2)
      ≤ (∑' n : ℕ, wc * ((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)^2
          * (n:ℝ)^(1 - 2*ρ.re) * Work.LinnikAreas2.WT q u x n)) :=
        Summable.tsum_le_tsum key hgcsum hwcsum
    _ ≤ 1 + c1 := hle

end Work.LinnikAreas2
