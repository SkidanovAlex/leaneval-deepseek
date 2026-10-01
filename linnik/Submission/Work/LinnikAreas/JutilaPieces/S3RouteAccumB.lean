import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.S3RouteAux
import Submission.Work.LinnikAreas.JutilaPieces.S3RouteEstimates
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.LinnikAreas.JutilaPieces.S3AccumDefs

/-!
# The elementary `S₃` floor-vs-continuous bound (`S3RouteAccumB`)

We prove `|s3exact z N − s3cont z N| ≤ C·N` for `2 ≤ z ≤ N < z²`, with an absolute constant,
**without any arithmetic input**.  The argument is a term-by-term triangle inequality:

* `s3exact − s3cont = Σ_q Σ_{r,t} (s3sumE − s3sumC)`, and for each `(q,r,t)` the two summands share
  the coefficient `[r ⟂ t]·μ(r)μ(t)·s3c(rt)`, of modulus `≤ 1`, while the bracket difference
  `⌊M⌋·B(⌊M⌋) − M·B(M)` (`M = N/(qrt)`) is controlled by the already-proven `s3floor_pointwise`
  (`≤ 6·(1+log(x/r))·(1+log(x/t))`, `x = N/(qz)`);
* the double `(r,t)`-sum therefore factors as `6·S(q)²` with `S(q) = Σ_{r ≤ ⌊x⌋}(1+log(x/r)) ≤ 3x`
  (`S3LogSumBound`);
* finally `Σ_q x² = (N/z)²·Σ_q 1/q² ≤ 2·(N/z)²` and `(N/z)² ≤ N` since `N < z²`.

The resulting constant is `108`; we use `200` for slack.
-/

namespace Work.LinnikAreas.JutilaPieces

open Finset

noncomputable section

/-! ## Elementary auxiliary facts -/

/-- `|Σ f − Σ g| ≤ Σ |f − g|`. -/
lemma abs_sum_sub_le {α : Type*} (s : Finset α) (f g : α → ℝ) :
    |∑ x ∈ s, f x - ∑ x ∈ s, g x| ≤ ∑ x ∈ s, |f x - g x| := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs (fun x => f x - g x) s

/-- `Σ_{q ≤ M} 1/q² ≤ 2` (elementary telescoping: `1/q² ≤ 2/q − 2/(q+1)`). -/
lemma sum_inv_sq_le_two (M : ℕ) : ∑ q ∈ Finset.Icc 1 M, (1:ℝ)/((q:ℝ)^2) ≤ 2 := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  · have hpt : ∀ q ∈ Finset.Icc 1 M, (1:ℝ)/((q:ℝ)^2) ≤ (2:ℝ)/(q:ℝ) - 2/((q:ℝ)+1) := by
      intro q hq
      have hq1 : (1:ℝ) ≤ (q:ℝ) := by
        have : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        exact_mod_cast this
      have hq0 : (0:ℝ) < (q:ℝ) := by linarith
      have hqsq : (0:ℝ) < (q:ℝ)^2 := by positivity
      have hkey : (2:ℝ)/(q:ℝ) - 2/((q:ℝ)+1) = 2/((q:ℝ) * ((q:ℝ)+1)) := by
        field_simp; ring
      rw [hkey, div_le_div_iff₀ hqsq (by positivity)]
      nlinarith
    calc ∑ q ∈ Finset.Icc 1 M, (1:ℝ)/((q:ℝ)^2)
        ≤ ∑ q ∈ Finset.Icc 1 M, ((2:ℝ)/(q:ℝ) - 2/((q:ℝ)+1)) := Finset.sum_le_sum hpt
      _ = -(∑ q ∈ Finset.Icc 1 M, ((2:ℝ)/((q:ℝ)+1) - 2/(q:ℝ))) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl; intro q _; ring
      _ = -(2/((M:ℝ)+1) - 2) := by
            congr 1
            have hsub := Finset.sum_Icc_sub hM (fun i : ℕ => (2:ℝ)/(i:ℝ))
            simpa using hsub
      _ ≤ 2 := by
            have hM1 : (0:ℝ) < (M:ℝ)+1 := by positivity
            have h2 : (0:ℝ) < 2/((M:ℝ)+1) := by positivity
            linarith

/-- The `q`-square sum: `Σ_{q ≤ N/z} (N/(q z))² ≤ 2 (N/z)²`. -/
theorem S3AccumXqSqSum (z N : ℕ) (hz : 1 ≤ z) :
    ∑ q ∈ Finset.Icc 1 (N / z), (s3xq z N q)^2 ≤ 2 * ((N : ℝ)^2 / (z : ℝ)^2) := by
  rcases Nat.eq_zero_or_pos (N / z) with hM | hM
  · rw [hM]
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0:ℕ) < 1), Finset.sum_empty]
    positivity
  · have hzR : (0:ℝ) < z := by exact_mod_cast (by omega : 0 < z)
    have hterm : ∀ q ∈ Finset.Icc 1 (N / z),
        (s3xq z N q)^2 = ((N:ℝ)^2/(z:ℝ)^2) * (1/((q:ℝ)^2)) := by
      intro q hq
      have hq0 : (q:ℝ) ≠ 0 := by
        have : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        positivity
      simp only [s3xq, div_pow]
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    calc ((N:ℝ)^2/(z:ℝ)^2) * ∑ q ∈ Finset.Icc 1 (N/z), (1/((q:ℝ)^2))
        ≤ ((N:ℝ)^2/(z:ℝ)^2) * 2 := by
          apply mul_le_mul_of_nonneg_left (sum_inv_sq_le_two (N/z))
          positivity
      _ = 2 * ((N:ℝ)^2/(z:ℝ)^2) := by ring

/-- The inner factorisation weight: `0 ≤ s3S` and `s3S ≤ 3 x`. -/
theorem S3AccumSBound (z N q : ℕ) (hq : 1 ≤ q) (hz : 1 ≤ z) :
    0 ≤ s3S z N q ∧ s3S z N q ≤ 3 * s3xq z N q := by
  have hqz : 0 < q * z := Nat.mul_pos (by omega) (by omega)
  have hfloor : ⌊s3xq z N q⌋₊ = N / (q * z) := by
    simp only [s3xq]
    rw [show (N:ℝ)/((q:ℝ)*(z:ℝ)) = (N:ℝ)/(((q*z:ℕ)):ℝ) by push_cast; ring]
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  have hnn : 0 ≤ s3xq z N q := by simp only [s3xq]; positivity
  have hrle : ∀ r ∈ Finset.Icc 1 (N / (q * z)), (r:ℝ) ≤ s3xq z N q := by
    intro r hr
    have hr1 : r ≤ N / (q * z) := (Finset.mem_Icc.mp hr).2
    have h2 : ((N / (q*z) : ℕ) : ℝ) ≤ s3xq z N q := by
      have := Nat.floor_le hnn
      rwa [hfloor] at this
    exact le_trans (by exact_mod_cast hr1) h2
  constructor
  · rw [s3S]
    apply Finset.sum_nonneg
    intro r hr
    have hx : 1 ≤ s3xq z N q / (r:ℝ) := by
      rw [le_div_iff₀ (by
        have := (Finset.mem_Icc.mp hr).1
        exact_mod_cast (by omega : 0 < r))]
      simpa using hrle r hr
    have := Real.log_nonneg hx
    linarith
  · by_cases hx1 : 1 ≤ s3xq z N q
    · rw [s3S, ← hfloor]
      exact S3LogSumBound _ hx1
    · simp only [not_le] at hx1
      have h0 : N / (q * z) = 0 := by
        rw [← hfloor]
        exact Nat.floor_eq_zero.mpr hx1
      rw [s3S, h0]
      simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (0:ℕ) < 1), Finset.sum_empty]
      positivity

/-- **Pointwise summand comparison.**  The `s3exact`- and `s3cont`-summands differ by at most the
bracket defect controlled by `s3floor_pointwise`. -/
theorem S3AccumPointwise (z N q r t : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r) (ht : 1 ≤ t)
    (hz : 2 ≤ z) (hNz : N < z * z) (hrx : r ≤ N / (q * z)) (htx : t ≤ N / (q * z)) :
    |s3sumE z N q r t - s3sumC z N q r t|
      ≤ 6 * (1 + Real.log (s3xq z N q / (r : ℝ))) * (1 + Real.log (s3xq z N q / (t : ℝ))) := by
  have hq0 : q ≠ 0 := by omega
  have hr0 : r ≠ 0 := by omega
  have ht0 : t ≠ 0 := by omega
  have hz0 : z ≠ 0 := by omega
  have hzR : (0:ℝ) < (z:ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  have htR : (0:ℝ) < (t:ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hxq_nn : 0 ≤ s3xq z N q := by simp only [s3xq]; positivity
  have hfloor : ⌊s3xq z N q⌋₊ = N / (q * z) := by
    simp only [s3xq]
    rw [show (N:ℝ)/((q:ℝ)*(z:ℝ)) = (N:ℝ)/(((q*z:ℕ)):ℝ) by push_cast; ring]
    rw [Nat.floor_div_natCast, Nat.floor_natCast]
  have hxr : (r:ℝ) ≤ s3xq z N q := by
    have h2 : ((N / (q*z) : ℕ) : ℝ) ≤ s3xq z N q := by
      have := Nat.floor_le hxq_nn; rwa [hfloor] at this
    exact le_trans (by exact_mod_cast hrx) h2
  have hxt : (t:ℝ) ≤ s3xq z N q := by
    have h2 : ((N / (q*z) : ℕ) : ℝ) ≤ s3xq z N q := by
      have := Nat.floor_le hxq_nn; rwa [hfloor] at this
    exact le_trans (by exact_mod_cast htx) h2
  have hqrt : q * r * t ≤ N := by
    have hqq : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    have hNzR : (N:ℝ) < (z:ℝ)^2 := by
      have hzz : ((z*z : ℕ):ℝ) = (z:ℝ)^2 := by push_cast; ring
      rw [← hzz]; exact_mod_cast hNz
    have hrt : (r:ℝ) * (t:ℝ) ≤ s3xq z N q * s3xq z N q :=
      mul_le_mul hxr hxt (le_of_lt htR) hxq_nn
    have hxe : s3xq z N q * s3xq z N q = (N:ℝ)^2 / ((q:ℝ)^2 * (z:ℝ)^2) := by
      simp only [s3xq]; field_simp
    have hqne : (q:ℝ) ≠ 0 := ne_of_gt hqR
    have hzne : (z:ℝ) ≠ 0 := ne_of_gt hzR
    have hqrtR : ((q * r * t : ℕ) : ℝ) ≤ (N : ℝ) := by
      push_cast
      calc (q:ℝ) * (r:ℝ) * (t:ℝ) = (q:ℝ) * ((r:ℝ) * (t:ℝ)) := by ring
        _ ≤ (q:ℝ) * (s3xq z N q * s3xq z N q) := mul_le_mul_of_nonneg_left hrt (le_of_lt hqR)
        _ = (N:ℝ)^2 / ((q:ℝ) * (z:ℝ)^2) := by rw [hxe]; field_simp
        _ ≤ (N:ℝ)^2 / (z:ℝ)^2 := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            nlinarith [hqq, hzR]
        _ = (N:ℝ) * ((N:ℝ)/(z:ℝ)^2) := by ring
        _ ≤ (N:ℝ) * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [div_le_one (by positivity)]
            exact le_of_lt hNzR
        _ = (N:ℝ) := by ring
    exact_mod_cast hqrtR
  have hfp := s3floor_pointwise z N q r t hq0 hr0 ht0 hz0 hqrt hxr hxt
  have hA : 0 ≤ Real.log (s3xq z N q / (r : ℝ)) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hrR]; simpa using hxr
  have hB : 0 ≤ Real.log (s3xq z N q / (t : ℝ)) := by
    apply Real.log_nonneg; rw [le_div_iff₀ htR]; simpa using hxt
  set X : ℝ := (((N / (q * r * t) : ℕ) : ℝ) *
        ((Real.log (((N / (q * r * t) : ℕ) : ℝ) * (t : ℝ) / (z : ℝ)) - 1) *
           (Real.log (((N / (q * r * t) : ℕ) : ℝ) * (r : ℝ) / (z : ℝ)) - 1) + 1)
      - ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)) *
        ((Real.log (((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * (t : ℝ) / (z : ℝ)) - 1) *
           (Real.log (((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * (r : ℝ) / (z : ℝ)) - 1) + 1))) with hXdef
  have hXle : |X| ≤ 6 * (1 + Real.log (s3xq z N q / (r : ℝ))) * (1 + Real.log (s3xq z N q / (t : ℝ))) := by
    rw [hXdef]; exact hfp
  by_cases hc : Nat.Coprime r t
  · have hfac : s3sumE z N q r t - s3sumC z N q r t
        = ((ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ))
          * LinnikAreas.Density4.BzS3.s3c (r * t) * X := by
      rw [hXdef]; simp only [s3sumE, s3sumC, if_pos hc]; ring
    rw [hfac, abs_mul, abs_mul]
    have hmu : |(ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ)| ≤ 1 := by
      rw [abs_mul]
      calc |(ArithmeticFunction.moebius r : ℝ)| * |(ArithmeticFunction.moebius t : ℝ)|
            ≤ 1 * 1 := mul_le_mul (Commons.NumberTheory.Moebius.moebius_abs_le_one r)
              (Commons.NumberTheory.Moebius.moebius_abs_le_one t) (abs_nonneg _) (by norm_num)
        _ = 1 := by ring
    have hsc : |LinnikAreas.Density4.BzS3.s3c (r * t)| ≤ 1 := by
      rw [abs_of_nonneg (LinnikAreas.Density4.BzS3.s3c_nonneg _)]
      exact LinnikAreas.Density4.BzS3.s3c_le_one _
    calc |(ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ)|
            * |LinnikAreas.Density4.BzS3.s3c (r * t)| * |X|
        ≤ 1 * 1 * |X| := by
          apply mul_le_mul (mul_le_mul hmu hsc (abs_nonneg _) (by norm_num)) (le_refl _)
            (abs_nonneg _) (by norm_num)
      _ = |X| := by ring
      _ ≤ 6 * (1 + Real.log (s3xq z N q / (r : ℝ))) * (1 + Real.log (s3xq z N q / (t : ℝ))) := hXle
  · have hfac : s3sumE z N q r t - s3sumC z N q r t = 0 := by
      simp only [s3sumE, s3sumC, if_neg hc, zero_mul, sub_zero]
    rw [hfac, abs_zero]
    nlinarith [hA, hB]

/-! ## The target -/

theorem S3RouteAccumB : ∃ C : ℝ, 0 < C ∧ ∀ (z N : ℕ), 2 ≤ z → z ≤ N → N < z * z →
    |Work.ZeroDensity.Jutila.s3exact z N - Work.ZeroDensity.Jutila.s3cont z N| ≤ C * (N : ℝ) := by
  refine ⟨200, by norm_num, ?_⟩
  intro z N hz hzN hNz
  have hz1 : 1 ≤ z := by omega
  have hzR : (0:ℝ) < (z:ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have h2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast (le_trans hz hzN)
    linarith
  have hNnn : (0:ℝ) ≤ (N:ℝ) := le_of_lt hNpos
  -- step 1: triple-sum triangle inequality
  have hstep1 : |Work.ZeroDensity.Jutila.s3exact z N - Work.ZeroDensity.Jutila.s3cont z N|
      ≤ ∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
          ∑ t ∈ Finset.Icc 1 (N / (q * z)), |s3sumE z N q r t - s3sumC z N q r t| := by
    rw [s3exact_eq_sum, s3cont_eq_sum]
    calc |(∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
            ∑ t ∈ Finset.Icc 1 (N / (q * z)), s3sumE z N q r t)
          - (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
            ∑ t ∈ Finset.Icc 1 (N / (q * z)), s3sumC z N q r t)|
        ≤ ∑ q ∈ Finset.Icc 1 (N / z), |(∑ r ∈ Finset.Icc 1 (N / (q * z)),
            ∑ t ∈ Finset.Icc 1 (N / (q * z)), s3sumE z N q r t)
          - (∑ r ∈ Finset.Icc 1 (N / (q * z)), ∑ t ∈ Finset.Icc 1 (N / (q * z)),
            s3sumC z N q r t)| := abs_sum_sub_le _ _ _
      _ ≤ ∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
            |(∑ t ∈ Finset.Icc 1 (N / (q * z)), s3sumE z N q r t)
              - (∑ t ∈ Finset.Icc 1 (N / (q * z)), s3sumC z N q r t)| :=
              Finset.sum_le_sum (fun q _ => abs_sum_sub_le _ _ _)
      _ ≤ _ := Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun r _ => abs_sum_sub_le _ _ _))
  -- step 2: per-`q` factorisation
  have hstep2 : ∀ q ∈ Finset.Icc 1 (N / z),
      (∑ r ∈ Finset.Icc 1 (N / (q * z)), ∑ t ∈ Finset.Icc 1 (N / (q * z)),
          |s3sumE z N q r t - s3sumC z N q r t|) ≤ 6 * (s3S z N q)^2 := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hpt : ∀ r ∈ Finset.Icc 1 (N / (q * z)), ∀ t ∈ Finset.Icc 1 (N / (q * z)),
        |s3sumE z N q r t - s3sumC z N q r t|
          ≤ 6 * (1 + Real.log (s3xq z N q / (r : ℝ))) * (1 + Real.log (s3xq z N q / (t : ℝ))) := by
      intro r hr t ht
      exact S3AccumPointwise z N q r t hq1 (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp ht).1
        hz hNz (Finset.mem_Icc.mp hr).2 (Finset.mem_Icc.mp ht).2
    refine le_trans (Finset.sum_le_sum (fun r hr => Finset.sum_le_sum (fun t ht => hpt r hr t ht))) ?_
    have h1 : (∑ r ∈ Finset.Icc 1 (N/(q*z)), ∑ t ∈ Finset.Icc 1 (N/(q*z)),
          6 * (1 + Real.log (s3xq z N q / (r:ℝ))) * (1 + Real.log (s3xq z N q / (t:ℝ))))
        = 6 * (∑ r ∈ Finset.Icc 1 (N/(q*z)), ∑ t ∈ Finset.Icc 1 (N/(q*z)),
          (1 + Real.log (s3xq z N q / (r:ℝ))) * (1 + Real.log (s3xq z N q / (t:ℝ)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro t _
      ring
    have h2 : (∑ r ∈ Finset.Icc 1 (N/(q*z)), ∑ t ∈ Finset.Icc 1 (N/(q*z)),
          (1 + Real.log (s3xq z N q / (r:ℝ))) * (1 + Real.log (s3xq z N q / (t:ℝ))))
        = (s3S z N q)^2 := by
      rw [s3S, sq, ← Finset.sum_mul_sum]
    rw [h1, h2]
  -- step 3: `S(q)² ≤ (3x)²` and the `q`-sum
  have hstep3 : (∑ q ∈ Finset.Icc 1 (N / z), 6 * (s3S z N q)^2)
      ≤ ∑ q ∈ Finset.Icc 1 (N / z), 6 * (3 * s3xq z N q)^2 := by
    apply Finset.sum_le_sum
    intro q hq
    have hS := S3AccumSBound z N q (Finset.mem_Icc.mp hq).1 hz1
    have hxqnn : 0 ≤ s3xq z N q := by simp only [s3xq]; positivity
    have hsq : (s3S z N q)^2 ≤ (3 * s3xq z N q)^2 := by
      apply sq_le_sq'
      · nlinarith [hS.1, hxqnn]
      · exact hS.2
    exact mul_le_mul_of_nonneg_left hsq (by norm_num)
  -- final assembly
  have hNzR : (N:ℝ) < (z:ℝ)^2 := by
    have hzz : ((z*z : ℕ):ℝ) = (z:ℝ)^2 := by push_cast; ring
    rw [← hzz]; exact_mod_cast hNz
  have hratio : (N:ℝ)^2/(z:ℝ)^2 ≤ (N:ℝ) := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (z:ℝ)^2)]
    nlinarith [hNzR, hNnn, hzR]
  calc |Work.ZeroDensity.Jutila.s3exact z N - Work.ZeroDensity.Jutila.s3cont z N|
      ≤ ∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
          ∑ t ∈ Finset.Icc 1 (N / (q * z)), |s3sumE z N q r t - s3sumC z N q r t| := hstep1
    _ ≤ ∑ q ∈ Finset.Icc 1 (N / z), 6 * (s3S z N q)^2 := Finset.sum_le_sum hstep2
    _ ≤ ∑ q ∈ Finset.Icc 1 (N / z), 6 * (3 * s3xq z N q)^2 := hstep3
    _ = 54 * ∑ q ∈ Finset.Icc 1 (N / z), (s3xq z N q)^2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro q _; ring
    _ ≤ 54 * (2 * ((N:ℝ)^2/(z:ℝ)^2)) := by
          apply mul_le_mul_of_nonneg_left (S3AccumXqSqSum z N hz1) (by norm_num)
    _ ≤ 200 * (N:ℝ) := by nlinarith [hratio, hNnn, hNpos]

end

end Work.LinnikAreas.JutilaPieces
