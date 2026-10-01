import Mathlib
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.ZeroDensity.Jutila.Bz3Reduce
import Submission.Work.LinnikAreas.JutilaPieces.S3FloorDefs
import Submission.Work.LinnikAreas.JutilaPieces.S3LogExpansion
import Submission.Work.LinnikAreas.JutilaPieces.S3BracketExpandBounded
import Submission.Work.LinnikAreas.JutilaPieces.HarmonicLogBound
import Submission.Commons.Analysis.Abel.summation_by_parts
import Submission.Work.LinnikAreas.JutilaPieces.S3GhatSup
import Submission.Work.LinnikAreas.JutilaPieces.S3GhatTV
import Submission.Work.LinnikAreas.JutilaPieces.S3TsumBounds2
import Submission.Work.LinnikAreas.JutilaPieces.S3T0Bound

/-!
# `S₃` floor reduction

`s3exact z N` (floor form) and `s3cont z N` (continuous form) differ by `O(N)`, uniformly in
`2 ≤ z ≤ N < z²`.

Route (all of it elementary once the Mertens input `KappaMertensInput` is available): after
`s3c (r*t) = ζ(2)^{-1}(r/κ r)(t/κ t)` each `(q,t)`-slice of the difference is
`μ(t)(t/κ t)·Σ_r [r⟂t](μ r/κ r)·Ĝ(r)` with `Ĝ(r) = r(X_r B(X_r) − x_r B(x_r))`; summation by parts
against the partial sums of `μ(r)/κ r` (bounded by the input's `e^{−c√log}`) splits at the
threshold `s3T0 c z`.
-/

namespace Work.LinnikAreas.JutilaPieces

open Finset

noncomputable section

/-- the `r`-sum for fixed `(q,t)`: `Σ_r [r⟂t]·(μ r / κ r)·Ĝ(r)` -/
def Sqt (z N q t : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (N / (q * z)),
    (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / Work.ZeroDensity.Jutila.kap r else 0)
      * s3Ghat z N q r t

/-- `κ`-form summand of `s3exact`. -/
def kSDf (z N q r t : ℕ) : ℝ :=
  (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0)
    * (((r : ℝ) / Work.ZeroDensity.Jutila.kap r * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t))
        * (((N / (q * r * t) : ℕ) : ℝ) * s3Bfloor z N q r t))

/-- `κ`-form summand of `s3cont`. -/
def kSDc (z N q r t : ℕ) : ℝ :=
  (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0)
    * (((r : ℝ) / Work.ZeroDensity.Jutila.kap r * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t))
        * ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)) * s3Bcont z N q r t))

/-- **Termwise identity** (abstract form): the difference of the two `κ`-form summands is the
`r`-weight of `Ĝ` times the `t`-weight. Pure algebra. -/
lemma kSD_sub_abs (q r t : ℕ) (Xf xc Bf Bc : ℝ) :
    (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0)
        * (((r : ℝ) / Work.ZeroDensity.Jutila.kap r * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t)) * (Xf * Bf))
      - (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0)
        * (((r : ℝ) / Work.ZeroDensity.Jutila.kap r * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t)) * (xc * Bc))
      = ((ArithmeticFunction.moebius t : ℝ) * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t))
          * ((if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / Work.ZeroDensity.Jutila.kap r else 0)
              * ((r : ℝ) * (Xf * Bf - xc * Bc))) := by
  by_cases hc : Nat.Coprime r t
  · have e1 : (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0)
        = (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) := if_pos hc
    have e2 : (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / Work.ZeroDensity.Jutila.kap r else 0)
        = (ArithmeticFunction.moebius r : ℝ) / Work.ZeroDensity.Jutila.kap r := if_pos hc
    rw [e1, e2]; ring
  · have e1 : (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) = 0 := if_neg hc
    have e2 : (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / Work.ZeroDensity.Jutila.kap r else 0) = 0 := if_neg hc
    rw [e1, e2]; ring

lemma kSD_sub (z N q r t : ℕ) :
    kSDf z N q r t - kSDc z N q r t
      = ((ArithmeticFunction.moebius t : ℝ) * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t))
          * ((if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / Work.ZeroDensity.Jutila.kap r else 0)
              * s3Ghat z N q r t) := by
  unfold kSDf kSDc s3Ghat
  exact kSD_sub_abs q r t _ _ (s3Bfloor z N q r t) (s3Bcont z N q r t)

lemma s3exact_eq_ksum (z N : ℕ) :
    Work.ZeroDensity.Jutila.s3exact z N
      = (Real.pi ^ 2 / 6)⁻¹
          * ∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
              ∑ t ∈ Finset.Icc 1 (N / (q * z)), kSDf z N q r t := by
  rw [Work.ZeroDensity.Jutila.s3exact_eq_kappa]
  simp only [kSDf, s3Bfloor]

lemma s3cont_eq_ksum (z N : ℕ) :
    Work.ZeroDensity.Jutila.s3cont z N
      = (Real.pi ^ 2 / 6)⁻¹
          * ∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
              ∑ t ∈ Finset.Icc 1 (N / (q * z)), kSDc z N q r t := by
  rw [Work.ZeroDensity.Jutila.s3cont_eq_kappa]
  simp only [kSDc, s3Bcont]

lemma s3diff_eq (z N : ℕ) :
    Work.ZeroDensity.Jutila.s3exact z N - Work.ZeroDensity.Jutila.s3cont z N
      = (Real.pi ^ 2 / 6)⁻¹
          * ∑ q ∈ Finset.Icc 1 (N / z), ∑ t ∈ Finset.Icc 1 (N / (q * z)),
              ((ArithmeticFunction.moebius t : ℝ) * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t))
                * Sqt z N q t := by
  rw [s3exact_eq_ksum, s3cont_eq_ksum, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro q hq
  have step1 : (∑ r ∈ Finset.Icc 1 (N / (q * z)), ∑ t ∈ Finset.Icc 1 (N / (q * z)), kSDf z N q r t)
      - (∑ r ∈ Finset.Icc 1 (N / (q * z)), ∑ t ∈ Finset.Icc 1 (N / (q * z)), kSDc z N q r t)
      = ∑ t ∈ Finset.Icc 1 (N / (q * z)), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
          (kSDf z N q r t - kSDc z N q r t) := by
    rw [← Finset.sum_sub_distrib]
    rw [show (∑ r ∈ Finset.Icc 1 (N / (q * z)), (∑ t ∈ Finset.Icc 1 (N / (q * z)), kSDf z N q r t
            - ∑ t ∈ Finset.Icc 1 (N / (q * z)), kSDc z N q r t))
        = ∑ r ∈ Finset.Icc 1 (N / (q * z)), ∑ t ∈ Finset.Icc 1 (N / (q * z)),
            (kSDf z N q r t - kSDc z N q r t)
        from Finset.sum_congr rfl (fun r _ =>
          (Finset.sum_sub_distrib (fun t => kSDf z N q r t) (fun t => kSDc z N q r t)).symm)]
    exact Finset.sum_comm
  have step2 : (∑ t ∈ Finset.Icc 1 (N / (q * z)), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
          (kSDf z N q r t - kSDc z N q r t))
      = ∑ t ∈ Finset.Icc 1 (N / (q * z)),
          ((ArithmeticFunction.moebius t : ℝ) * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t))
            * Sqt z N q t := by
    apply Finset.sum_congr rfl; intro t ht
    rw [show (∑ r ∈ Finset.Icc 1 (N / (q * z)), (kSDf z N q r t - kSDc z N q r t))
        = ∑ r ∈ Finset.Icc 1 (N / (q * z)),
            ((ArithmeticFunction.moebius t : ℝ) * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t))
              * ((if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / Work.ZeroDensity.Jutila.kap r else 0)
                  * s3Ghat z N q r t)
        from Finset.sum_congr rfl (fun r _ => kSD_sub z N q r t)]
    rw [← Finset.mul_sum]
    rfl
  rw [step1, step2]

/-- **Summation by parts, boundary at `1`**: if `A n = Σ_{k ≤ n} a k`, then
`Σ_{r ≤ R} a r g r = A R · g 1 + Σ_{r < R} (g r − g (r+1)) (A r − A R)`.
The Abel correction against the *telescoping* difference of the partial sums keeps the boundary
term at `r = 1` (where `|g|` is under control) rather than at `r = R`. -/
lemma abel_identity (a g : ℕ → ℝ) (R : ℕ) :
    (∑ r ∈ Finset.Icc 1 R, a r * g r)
      = (∑ r ∈ Finset.Icc 1 R, a r) * g 1
        + ∑ r ∈ Finset.Icc 1 (R - 1),
            (g r - g (r + 1)) * ((∑ k ∈ Finset.Icc 1 r, a k) - (∑ k ∈ Finset.Icc 1 R, a k)) := by
  rcases R with _ | n
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [show (∑ r ∈ Finset.Icc 1 (n+1), a r * g r) = ∑ r ∈ Finset.Icc 1 (n+1), g r * a r
        from Finset.sum_congr rfl (fun r _ => mul_comm _ _)]
    have h := Commons.Analysis.Abel.summation_by_parts g a (n + 1)
    rw [Nat.add_sub_cancel] at h
    rw [h]
    set A := ∑ k ∈ Finset.Icc 1 (n + 1), a k with hA
    have hkey : (∑ m ∈ Finset.Icc 1 n, (g m - g (m + 1)) * (∑ k ∈ Finset.Icc 1 m, a k))
        = (∑ m ∈ Finset.Icc 1 n, (g m - g (m + 1))) * A
          + ∑ m ∈ Finset.Icc 1 n, (g m - g (m + 1)) * ((∑ k ∈ Finset.Icc 1 m, a k) - A) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro m hm; ring
    have htel : (∑ m ∈ Finset.Icc 1 n, (g m - g (m + 1))) = g 1 - g (n + 1) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · rw [show (∑ m ∈ Finset.Icc 1 n, (g m - g (m + 1)))
              = - (∑ m ∈ Finset.Icc 1 n, (g (m+1) - g m)) from by
              rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro m _; ring]
        rw [Finset.sum_Icc_sub hn g]
        ring
    rw [hkey, htel]
    ring

lemma s3Kt_pos (Ch : ℝ) (t : ℕ) : 0 < s3Kt Ch t := lt_of_lt_of_le one_pos (le_max_left _ _)

lemma s3Kt_ge_one (Ch : ℝ) (t : ℕ) : 1 ≤ s3Kt Ch t := le_max_left _ _

lemma s3Eanti (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) {m n : ℕ} (hm1 : (1:ℝ) ≤ (m:ℝ)) (hmn : m ≤ n) :
    K * Real.exp (-(c * Real.sqrt (Real.log (n : ℝ))))
      ≤ K * Real.exp (-(c * Real.sqrt (Real.log (m : ℝ)))) := by
  have hm0 : (0:ℝ) < (m:ℝ) := by linarith
  have hlog : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hm0 (by exact_mod_cast hmn)
  have hsq : Real.sqrt (Real.log (m : ℝ)) ≤ Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_le_sqrt hlog
  have hexp : Real.exp (-(c * Real.sqrt (Real.log (n : ℝ)))) ≤ Real.exp (-(c * Real.sqrt (Real.log (m : ℝ)))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hsq]
  exact mul_le_mul_of_nonneg_left hexp hK

set_option maxHeartbeats 1000000 in
lemma Sqt_bound (z N q t : ℕ) (hz : 2 ≤ z) (hNz : N < z*z)
    (hq : 1 ≤ q) (hqz : q * z ≤ N) (ht : 1 ≤ t) (htR : t ≤ N/(q*z)) (htsf : Squarefree t)
    (Ch c C1 C2 : ℝ) (hCh : 0 < Ch) (hc : 0 < c) (hC1 : 0 < C1) (hC2 : 0 < C2)
    (hsupb : ∀ r : ℕ, 1 ≤ r → r ≤ N/(q*z) → |s3Ghat z N q r t| ≤ C1*(r:ℝ)*(Real.log (z:ℝ)+2)^2)
    (htvb : (∑ r ∈ Finset.Icc 1 (N/(q*z)-1), |s3Ghat z N q (r+1) t - s3Ghat z N q r t|)
              ≤ C2*((N:ℝ)/((q:ℝ)*(t:ℝ)))*(Real.log (z:ℝ)+2)^3)
    (hmert : ∀ Rn : ℕ, 2 ≤ Rn → Rn ≤ N/(q*z) →
        |∑ r ∈ Finset.Icc 1 Rn, (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ)/Work.ZeroDensity.Jutila.kap r else 0)|
          ≤ Ch*(∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ))*Real.exp (-(c*Real.sqrt (Real.log (Rn:ℝ)))))
    : |Sqt z N q t| ≤ 5*C1*s3Kt Ch t*((s3T0 c z : ℝ)+1)^2*(Real.log (z:ℝ)+2)^2
        + 2*C2*s3Kt Ch t*Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z : ℝ))))*((N:ℝ)/((q:ℝ)*(t:ℝ)))*(Real.log (z:ℝ)+2)^3 := by
  set R := N/(q*z) with hRdef
  set K := s3Kt Ch t with hKdef
  set Lz := Real.log (z:ℝ) + 2 with hLzdef
  set T0 := s3T0 c z with hT0def
  let Aa : ℕ → ℝ := fun k => if Nat.Coprime k t then (ArithmeticFunction.moebius k : ℝ)/Work.ZeroDensity.Jutila.kap k else 0
  have hR1 : 1 ≤ R := by
    rw [hRdef]; exact (Nat.one_le_div_iff (by positivity)).mpr hqz
  have hKpos : 0 < K := by rw [hKdef]; exact s3Kt_pos Ch t
  have hK1 : 1 ≤ K := by rw [hKdef]; exact s3Kt_ge_one Ch t
  have hKnn : 0 ≤ K := le_of_lt hKpos
  have hT0pos : (1:ℝ) ≤ (T0 : ℝ) := by
    have : 2 ≤ s3T0 c z := by rw [s3T0]; omega
    have : (2:ℝ) ≤ (T0:ℝ) := by rw [hT0def]; exact_mod_cast this
    linarith
  have hLz1 : 1 ≤ Lz := by
    rw [hLzdef]
    have : 0 ≤ Real.log (z:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ z))
    linarith
  -- partial sums
  have hA : ∀ n : ℕ, 1 ≤ n → n ≤ R →
      |∑ k ∈ Finset.Icc 1 n, Aa k| ≤ K * Real.exp (-(c*Real.sqrt (Real.log (n:ℝ)))) := by
    intro n hn1 hnR
    rcases eq_or_lt_of_le hn1 with h1 | h2
    · subst h1
      have hone : (∑ k ∈ Finset.Icc 1 1, Aa k) = 1 := by
        rw [Finset.Icc_self, Finset.sum_singleton]
        simp only [Aa]
        rw [if_pos (Nat.coprime_one_left t), ArithmeticFunction.moebius_apply_one]
        rw [show Work.ZeroDensity.Jutila.kap 1 = 1 from by rw [Work.ZeroDensity.Jutila.kap]; simp]
        norm_num
      rw [hone, abs_one]
      have he1 : Real.exp (-(c*Real.sqrt (Real.log ((1:ℕ):ℝ)))) = 1 := by norm_num
      rw [he1, mul_one]
      exact hK1
    · have hm := hmert n h2 hnR
      have hle : Ch * (∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ)) ≤ K := by
        rw [hKdef]; exact le_max_right _ _
      have he : 0 ≤ Real.exp (-(c*Real.sqrt (Real.log (n:ℝ)))) := Real.exp_nonneg _
      exact le_trans hm (mul_le_mul_of_nonneg_right hle he)
  have hAK : ∀ n : ℕ, 1 ≤ n → n ≤ R → |∑ k ∈ Finset.Icc 1 n, Aa k| ≤ K := by
    intro n hn1 hnR
    refine le_trans (hA n hn1 hnR) ?_
    have h2 : Real.exp (-(c*Real.sqrt (Real.log (n:ℝ)))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ Real.sqrt (Real.log (n:ℝ)) := Real.sqrt_nonneg _
      nlinarith [hc]
    calc K * Real.exp (-(c*Real.sqrt (Real.log (n:ℝ)))) ≤ K * 1 := mul_le_mul_of_nonneg_left h2 hKnn
      _ = K := mul_one K
  -- Abel
  have habel := abel_identity Aa (fun k => s3Ghat z N q k t) R
  have hSqt : Sqt z N q t = (∑ k ∈ Finset.Icc 1 R, Aa k) * s3Ghat z N q 1 t
      + ∑ k ∈ Finset.Icc 1 (R-1), (s3Ghat z N q k t - s3Ghat z N q (k+1) t)
          * ((∑ i ∈ Finset.Icc 1 k, Aa i) - (∑ i ∈ Finset.Icc 1 R, Aa i)) := by
    have : Sqt z N q t = ∑ k ∈ Finset.Icc 1 R, Aa k * s3Ghat z N q k t := rfl
    rw [this, habel]
  have hg1 : |s3Ghat z N q 1 t| ≤ C1*Lz^2 := by
    have := hsupb 1 (le_refl 1) hR1
    simpa using this
  have hbound1 : |(∑ k ∈ Finset.Icc 1 R, Aa k) * s3Ghat z N q 1 t| ≤ C1*K*Lz^2 := by
    rw [abs_mul]
    calc |∑ k ∈ Finset.Icc 1 R, Aa k| * |s3Ghat z N q 1 t| ≤ K * (C1*Lz^2) :=
          mul_le_mul (hAK R hR1 le_rfl) hg1 (abs_nonneg _) hKnn
      _ = C1*K*Lz^2 := by ring
  have hdgd : ∀ r : ℕ, 1 ≤ r → r ≤ R → |s3Ghat z N q r t - s3Ghat z N q (r+1) t| ≤ 2*C1*((T0:ℝ)+1)*Lz^2 →
      True := fun _ _ _ _ => trivial
  have hbound2 : |∑ k ∈ Finset.Icc 1 (R-1), (s3Ghat z N q k t - s3Ghat z N q (k+1) t)
          * ((∑ i ∈ Finset.Icc 1 k, Aa i) - (∑ i ∈ Finset.Icc 1 R, Aa i))|
      ≤ 4*K*C1*Lz^2*(T0+1)^2 + 2*K*Real.exp (-(c*Real.sqrt (Real.log (T0:ℝ))))*C2*((N:ℝ)/((q:ℝ)*(t:ℝ)))*Lz^3 := by
    refine le_trans (abs_sum_le_sum_abs _ _) ?_
    rw [show (∑ k ∈ Finset.Icc 1 (R - 1), |(s3Ghat z N q k t - s3Ghat z N q (k + 1) t)
            * ((∑ i ∈ Finset.Icc 1 k, Aa i) - (∑ i ∈ Finset.Icc 1 R, Aa i))|)
        = ∑ k ∈ Finset.Icc 1 (R - 1), |s3Ghat z N q k t - s3Ghat z N q (k + 1) t|
            * |(∑ i ∈ Finset.Icc 1 k, Aa i) - (∑ i ∈ Finset.Icc 1 R, Aa i)| from
        Finset.sum_congr rfl (fun k _ => abs_mul _ _)]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (R-1)) (fun r => r < T0)]
    have hhead : (∑ r ∈ (Finset.Icc 1 (R - 1)).filter (fun r => r < T0),
          |s3Ghat z N q r t - s3Ghat z N q (r + 1) t| * |(∑ i ∈ Finset.Icc 1 r, Aa i) - (∑ i ∈ Finset.Icc 1 R, Aa i)|)
        ≤ 4*K*C1*Lz^2*(T0+1)^2 := by
      have hcard : ((Finset.Icc 1 (R - 1)).filter (fun r => r < T0)).card ≤ T0 := by
        have hsub : (Finset.Icc 1 (R - 1)).filter (fun r => r < T0) ⊆ Finset.Icc 1 (T0 - 1) := by
          intro r hr
          rw [Finset.mem_filter, Finset.mem_Icc] at hr
          exact Finset.mem_Icc.mpr ⟨hr.1.1, by omega⟩
        calc ((Finset.Icc 1 (R - 1)).filter (fun r => r < T0)).card ≤ (Finset.Icc 1 (T0 - 1)).card := Finset.card_le_card hsub
          _ = T0 - 1 := by rw [Nat.card_Icc]; omega
          _ ≤ T0 := by omega
      have hterm : ∀ r ∈ (Finset.Icc 1 (R - 1)).filter (fun r => r < T0),
          |s3Ghat z N q r t - s3Ghat z N q (r + 1) t| * |(∑ i ∈ Finset.Icc 1 r, Aa i) - (∑ i ∈ Finset.Icc 1 R, Aa i)|
            ≤ 4*K*C1*Lz^2*(T0+1) := by
        intro r hr
        rw [Finset.mem_filter, Finset.mem_Icc] at hr
        obtain ⟨⟨hr1, hr2⟩, hr3⟩ := hr
        have hrr : r ≤ R := by omega
        have hgr : |s3Ghat z N q r t| ≤ C1*(r:ℝ)*Lz^2 := hsupb r hr1 hrr
        have hgr1 : |s3Ghat z N q (r+1) t| ≤ C1*((r+1:ℕ):ℝ)*Lz^2 := hsupb (r+1) (by omega) (by omega)
        have hd : |s3Ghat z N q r t - s3Ghat z N q (r + 1) t| ≤ 2*C1*((T0:ℝ)+1)*Lz^2 := by
          have hle : |s3Ghat z N q r t - s3Ghat z N q (r + 1) t| ≤ C1*(r:ℝ)*Lz^2 + C1*((r+1:ℕ):ℝ)*Lz^2 :=
            le_trans (abs_sub_le _ 0 _) (by simp only [sub_zero, zero_sub, abs_neg]; exact add_le_add hgr hgr1)
          have hrT : ((r:ℝ) + ((r+1:ℕ):ℝ)) ≤ 2*((T0:ℝ)+1) := by
            have h1 : ((r:ℝ) ≤ (T0:ℝ)) := by exact_mod_cast (by omega : r ≤ T0)
            have h2 : (((r+1:ℕ):ℝ) ≤ (T0:ℝ)) := by exact_mod_cast (by omega : r+1 ≤ T0)
            linarith
          have hCL : 0 ≤ C1*Lz^2 := by positivity
          have h2 : C1*Lz^2 * ((r:ℝ) + ((r+1:ℕ):ℝ)) ≤ C1*Lz^2 * (2*((T0:ℝ)+1)) :=
            mul_le_mul_of_nonneg_left hrT hCL
          nlinarith [hle, h2]
        have hArR : |(∑ i ∈ Finset.Icc 1 r, Aa i) - (∑ i ∈ Finset.Icc 1 R, Aa i)| ≤ 2*K := by
          refine le_trans (abs_sub_le _ 0 _) ?_
          have h1 : |∑ i ∈ Finset.Icc 1 r, Aa i| ≤ K := hAK r hr1 hrr
          have h2 : |∑ i ∈ Finset.Icc 1 R, Aa i| ≤ K := hAK R hR1 le_rfl
          simp only [sub_zero, zero_sub, abs_neg]
          linarith
        calc |s3Ghat z N q r t - s3Ghat z N q (r + 1) t| * |(∑ i ∈ Finset.Icc 1 r, Aa i) - (∑ i ∈ Finset.Icc 1 R, Aa i)|
            ≤ (2*C1*((T0:ℝ)+1)*Lz^2) * (2*K) := by
              apply mul_le_mul hd hArR (abs_nonneg _); positivity
          _ = 4*K*C1*Lz^2*(T0+1) := by ring
      calc (∑ r ∈ (Finset.Icc 1 (R - 1)).filter (fun r => r < T0),
            |s3Ghat z N q r t - s3Ghat z N q (r + 1) t| * |(∑ i ∈ Finset.Icc 1 r, Aa i) - (∑ i ∈ Finset.Icc 1 R, Aa i)|)
          ≤ ∑ r ∈ (Finset.Icc 1 (R - 1)).filter (fun r => r < T0), 4*K*C1*Lz^2*(T0+1) := Finset.sum_le_sum hterm
        _ = (((Finset.Icc 1 (R - 1)).filter (fun r => r < T0)).card : ℝ) * (4*K*C1*Lz^2*(T0+1)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (T0:ℝ) * (4*K*C1*Lz^2*(T0+1)) := by
              have hc' : (((Finset.Icc 1 (R - 1)).filter (fun r => r < T0)).card : ℝ) ≤ (T0:ℝ) := by
                exact_mod_cast hcard
              exact mul_le_mul_of_nonneg_right hc' (by positivity)
        _ ≤ 4*K*C1*Lz^2*(T0+1)^2 := by
              have h1 : (T0:ℝ) * (4*K*C1*Lz^2*(T0+1)) = 4*K*C1*Lz^2*((T0:ℝ)*((T0:ℝ)+1)) := by ring
              have h3 : (T0:ℝ)*((T0:ℝ)+1) ≤ ((T0:ℝ)+1)^2 := by
                nlinarith [(Nat.cast_nonneg T0 : (0:ℝ) ≤ (T0:ℝ))]
              have h4 : 4*K*C1*Lz^2*((T0:ℝ)*((T0:ℝ)+1)) ≤ 4*K*C1*Lz^2*((T0:ℝ)+1)^2 := by
                apply mul_le_mul_of_nonneg_left h3
                positivity
              linarith [h1, h4]
    have htail : (∑ r ∈ (Finset.Icc 1 (R - 1)).filter (fun r => ¬ r < T0),
          |s3Ghat z N q r t - s3Ghat z N q (r + 1) t| * |(∑ i ∈ Finset.Icc 1 r, Aa i) - (∑ i ∈ Finset.Icc 1 R, Aa i)|)
        ≤ 2*K*Real.exp (-(c*Real.sqrt (Real.log (T0:ℝ))))*C2*((N:ℝ)/((q:ℝ)*(t:ℝ)))*Lz^3 := by
      have hsub : (Finset.Icc 1 (R - 1)).filter (fun r => ¬ r < T0) ⊆ Finset.Icc 1 (R-1) := Finset.filter_subset _ _
      have hterm : ∀ r ∈ (Finset.Icc 1 (R - 1)).filter (fun r => ¬ r < T0),
          |s3Ghat z N q r t - s3Ghat z N q (r + 1) t| * |(∑ i ∈ Finset.Icc 1 r, Aa i) - (∑ i ∈ Finset.Icc 1 R, Aa i)|
            ≤ 2*K*Real.exp (-(c*Real.sqrt (Real.log (T0:ℝ)))) * |s3Ghat z N q r t - s3Ghat z N q (r + 1) t| := by
        intro r hr
        rw [Finset.mem_filter, Finset.mem_Icc] at hr
        obtain ⟨⟨hr1, hr2⟩, hr3⟩ := hr
        have hT0r : T0 ≤ r := by omega
        have hRge : T0 ≤ R := by omega
        have hE1 : |∑ i ∈ Finset.Icc 1 r, Aa i| ≤ K * Real.exp (-(c*Real.sqrt (Real.log (T0:ℝ)))) := by
          refine le_trans (hA r hr1 (by omega)) ?_
          exact s3Eanti c K hc hKnn hT0pos hT0r
        have hE2 : |∑ i ∈ Finset.Icc 1 R, Aa i| ≤ K * Real.exp (-(c*Real.sqrt (Real.log (T0:ℝ)))) := by
          refine le_trans (hA R hR1 le_rfl) ?_
          exact s3Eanti c K hc hKnn hT0pos hRge
        have hArR : |(∑ i ∈ Finset.Icc 1 r, Aa i) - (∑ i ∈ Finset.Icc 1 R, Aa i)| ≤ 2*K*Real.exp (-(c*Real.sqrt (Real.log (T0:ℝ)))) := by
          refine le_trans (abs_sub_le _ 0 _) ?_
          simp only [sub_zero, zero_sub, abs_neg]
          linarith
        calc |s3Ghat z N q r t - s3Ghat z N q (r + 1) t| * |(∑ i ∈ Finset.Icc 1 r, Aa i) - (∑ i ∈ Finset.Icc 1 R, Aa i)|
            = |(∑ i ∈ Finset.Icc 1 r, Aa i) - (∑ i ∈ Finset.Icc 1 R, Aa i)| * |s3Ghat z N q r t - s3Ghat z N q (r + 1) t| := by ring
          _ ≤ (2*K*Real.exp (-(c*Real.sqrt (Real.log (T0:ℝ))))) * |s3Ghat z N q r t - s3Ghat z N q (r + 1) t| :=
              mul_le_mul_of_nonneg_right hArR (abs_nonneg _)
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.mul_sum]
      have h1 : (∑ r ∈ (Finset.Icc 1 (R - 1)).filter (fun r => ¬ r < T0), |s3Ghat z N q r t - s3Ghat z N q (r + 1) t|)
          ≤ ∑ r ∈ Finset.Icc 1 (R - 1), |s3Ghat z N q r t - s3Ghat z N q (r + 1) t| :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => abs_nonneg _)
      have htvb' : (∑ r ∈ Finset.Icc 1 (R - 1), |s3Ghat z N q r t - s3Ghat z N q (r + 1) t|)
          ≤ C2*((N:ℝ)/((q:ℝ)*(t:ℝ)))*Lz^3 := by
        refine le_trans (le_of_eq ?_) htvb
        apply Finset.sum_congr rfl; intro r _; rw [abs_sub_comm]
      calc (2*K*Real.exp (-(c*Real.sqrt (Real.log (T0:ℝ))))) * (∑ r ∈ (Finset.Icc 1 (R - 1)).filter (fun r => ¬ r < T0), |s3Ghat z N q r t - s3Ghat z N q (r + 1) t|)
          ≤ (2*K*Real.exp (-(c*Real.sqrt (Real.log (T0:ℝ))))) * (∑ r ∈ Finset.Icc 1 (R - 1), |s3Ghat z N q r t - s3Ghat z N q (r + 1) t|) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ (2*K*Real.exp (-(c*Real.sqrt (Real.log (T0:ℝ))))) * (C2*((N:ℝ)/((q:ℝ)*(t:ℝ)))*Lz^3) :=
            mul_le_mul_of_nonneg_left htvb' (by positivity)
        _ = 2*K*Real.exp (-(c*Real.sqrt (Real.log (T0:ℝ))))*C2*((N:ℝ)/((q:ℝ)*(t:ℝ)))*Lz^3 := by ring
    linarith [hhead, htail]
  rw [hSqt]
  calc |(∑ k ∈ Finset.Icc 1 R, Aa k) * s3Ghat z N q 1 t
        + ∑ k ∈ Finset.Icc 1 (R-1), (s3Ghat z N q k t - s3Ghat z N q (k+1) t)
            * ((∑ i ∈ Finset.Icc 1 k, Aa i) - (∑ i ∈ Finset.Icc 1 R, Aa i))|
      ≤ |(∑ k ∈ Finset.Icc 1 R, Aa k) * s3Ghat z N q 1 t| + |∑ k ∈ Finset.Icc 1 (R-1), (s3Ghat z N q k t - s3Ghat z N q (k+1) t)
            * ((∑ i ∈ Finset.Icc 1 k, Aa i) - (∑ i ∈ Finset.Icc 1 R, Aa i))| := abs_add_le _ _
    _ ≤ C1*K*Lz^2 + (4*K*C1*Lz^2*(T0+1)^2 + 2*K*Real.exp (-(c*Real.sqrt (Real.log (T0:ℝ))))*C2*((N:ℝ)/((q:ℝ)*(t:ℝ)))*Lz^3) :=
        add_le_add hbound1 hbound2
    _ ≤ 5*C1*K*(T0+1)^2*Lz^2 + 2*C2*K*Real.exp (-(c*Real.sqrt (Real.log (T0:ℝ))))*((N:ℝ)/((q:ℝ)*(t:ℝ)))*Lz^3 := by
        have h5 : C1*K*Lz^2 ≤ C1*K*(T0+1)^2*Lz^2 := by
          have h6 : (1:ℝ) ≤ ((T0:ℝ)+1)^2 := by nlinarith [hT0pos]
          calc C1*K*Lz^2 = C1*K*Lz^2*1 := by ring
            _ ≤ C1*K*Lz^2*((T0:ℝ)+1)^2 := mul_le_mul_of_nonneg_left h6 (by positivity)
            _ = C1*K*(T0+1)^2*Lz^2 := by ring
        linarith [h5]


lemma s3T0_exp_le (c : ℝ) (hc : 0 < c) (z : ℕ) (hz : 2 ≤ z) :
    Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z : ℝ)))) * (Real.log (z:ℝ) + 2)^5 ≤ 1 := by
  set T0 := s3T0 c z with hT0def
  have hLge1 : (1:ℝ) ≤ Real.log (z:ℝ) + 2 := by
    have hz1 : (1:ℝ) ≤ (z:ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
    have := Real.log_nonneg hz1
    linarith
  have hlogL : 0 ≤ Real.log (Real.log (z:ℝ) + 2) := Real.log_nonneg hLge1
  have hT0ge : Real.exp (25 * (Real.log (Real.log (z:ℝ) + 2) + 1)^2 / c^2) ≤ (T0:ℝ) := by
    rw [hT0def, s3T0]
    push_cast
    exact le_trans (Nat.le_ceil _) (le_add_of_nonneg_right (by norm_num))
  have hlogT : 25 * (Real.log (Real.log (z:ℝ) + 2) + 1)^2 / c^2 ≤ Real.log (T0:ℝ) := by
    have h2 := Real.log_le_log (Real.exp_pos _) hT0ge
    rwa [Real.log_exp] at h2
  have hsq : (5 * (Real.log (Real.log (z:ℝ) + 2) + 1) / c)^2 ≤ Real.log (T0:ℝ) := by
    have hc2 : 0 < c^2 := by positivity
    have h' := hlogT
    rw [div_le_iff₀ hc2] at h'
    rw [div_pow]
    have h25 : (5 * (Real.log (Real.log (z:ℝ) + 2) + 1))^2
        = 25 * (Real.log (Real.log (z:ℝ) + 2) + 1)^2 := by ring
    rw [h25]
    rw [div_le_iff₀ hc2]
    exact h'
  have hL1pos : 0 < (5 * (Real.log (Real.log (z:ℝ) + 2) + 1))/c := by positivity
  have hsqrt : 5 * (Real.log (Real.log (z:ℝ) + 2) + 1)/c ≤ Real.sqrt (Real.log (T0:ℝ)) := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (le_of_lt hL1pos)] at h
  have hkey : 5 * Real.log (Real.log (z:ℝ) + 2) ≤ c * Real.sqrt (Real.log (T0:ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left hsqrt (le_of_lt hc)
    rw [mul_div_cancel₀ _ (ne_of_gt hc)] at h1
    have h2 : 5 * Real.log (Real.log (z:ℝ) + 2) ≤ 5 * (Real.log (Real.log (z:ℝ) + 2) + 1) := by linarith
    linarith
  have h5eq : (Real.log (z:ℝ) + 2)^5 = Real.exp (5 * Real.log (Real.log (z:ℝ) + 2)) := by
    have h1 : Real.exp (Real.log (Real.log (z:ℝ) + 2)) = Real.log (z:ℝ) + 2 := Real.exp_log (by linarith)
    rw [← h1, ← Real.exp_nat_mul]
    norm_num
  calc Real.exp (-(c*Real.sqrt (Real.log (T0:ℝ)))) * (Real.log (z:ℝ)+2)^5
      = Real.exp (-(c*Real.sqrt (Real.log (T0:ℝ))) + 5 * Real.log (Real.log (z:ℝ) + 2)) := by
        rw [h5eq, ← Real.exp_add]
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero


/-- absolute value of `μ t` as a real, on squarefree `t`. -/
lemma abs_moebius_real (t : ℕ) (ht : Squarefree t) :
    |(ArithmeticFunction.moebius t : ℝ)| = 1 := by
  have h1 := ArithmeticFunction.abs_moebius_eq_one_of_squarefree ht
  rw [← Int.cast_abs, h1]
  norm_num

/-- for squarefree `t`, `t/κ(t) = ∏_{p | t} p/(p+1) ≤ 1`. -/
lemma div_kap_le_one (t : ℕ) (ht : Squarefree t) :
    (t : ℝ) / Work.ZeroDensity.Jutila.kap t ≤ 1 := by
  have hprod : (∏ p ∈ t.primeFactors, (p:ℝ)) = (t:ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree ht]
  have hkey : (t : ℝ) / Work.ZeroDensity.Jutila.kap t
      = ∏ p ∈ t.primeFactors, ((p:ℝ) / ((p:ℝ)+1)) := by
    rw [Work.ZeroDensity.Jutila.kap, ← hprod, ← Finset.prod_div_distrib]
  rw [hkey]
  refine Finset.prod_le_one₀ (fun p hp => ?_) (fun p hp => ?_)
  · exact div_nonneg (by positivity) (by positivity)
  · rw [div_le_one (by positivity)]; linarith [show (0:ℝ) ≤ (p:ℝ) by positivity]

/-- `1 ≤ σ_{−1/2}(t)` for `t ≥ 1`. -/
lemma one_le_sigma (t : ℕ) (ht : 1 ≤ t) :
    (1:ℝ) ≤ ∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ) := by
  have h1 : (1:ℕ) ∈ t.divisors := Nat.mem_divisors.mpr ⟨one_dvd t, by omega⟩
  have h2 : (0:ℝ) ≤ 1/Real.sqrt (((1:ℕ)):ℝ) := by positivity
  have := Finset.single_le_sum (f := fun d : ℕ => 1/Real.sqrt (d:ℝ))
    (fun d hd => by positivity) h1
  simpa using this

lemma s3Kt_le (Ch : ℝ) (hCh : 0 ≤ Ch) (t : ℕ) :
    s3Kt Ch t ≤ 1 + Ch*(∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ)) := by
  have h0 : 0 ≤ ∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ) := Finset.sum_nonneg (fun d hd => by positivity)
  rw [s3Kt]
  exact max_le (by linarith [mul_nonneg hCh h0]) (by linarith)

set_option maxHeartbeats 2000000 in
lemma S3FloorReduce_aux (Ch c C1 C2 C3 C4 C5 : ℝ) (hCh : 0 < Ch) (hc : 0 < c)
    (hC1 : 0 < C1) (hC2 : 0 < C2) (hC3 : 0 < C3) (hC4 : 0 < C4) (hC5 : 0 < C5)
    (hsupb : ∀ (z N q r t : ℕ), 2 ≤ z → N < z*z → 1 ≤ q → 1 ≤ r → 1 ≤ t →
        r ≤ N/(q*z) → t ≤ N/(q*z) → |s3Ghat z N q r t| ≤ C1*(r:ℝ)*(Real.log (z:ℝ)+2)^2)
    (htvb : ∀ (z N q t : ℕ), 2 ≤ z → N < z*z → 1 ≤ q → 1 ≤ t → t ≤ N/(q*z) →
        (∑ r ∈ Finset.Icc 1 (N/(q*z)-1), |s3Ghat z N q (r+1) t - s3Ghat z N q r t|)
          ≤ C2*((N:ℝ)/((q:ℝ)*(t:ℝ)))*(Real.log (z:ℝ)+2)^3)
    (hts1 : ∀ T : ℕ, (∑ t ∈ Finset.Icc 1 T, |(ArithmeticFunction.moebius t : ℝ)|
        * ((t:ℝ)/Work.ZeroDensity.Jutila.kap t) * (∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ))) ≤ C3*(T:ℝ))
    (hts2 : ∀ T : ℕ, (∑ t ∈ Finset.Icc 1 T, |(ArithmeticFunction.moebius t : ℝ)|
        * (∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ))/Work.ZeroDensity.Jutila.kap t) ≤ C4*Real.log ((T:ℝ)+2))
    (ht0 : ∀ z : ℕ, 2 ≤ z → (s3T0 c z : ℝ)^2*(Real.log (z:ℝ)+2)^3/(z:ℝ) ≤ C5)
    (hmert : ∀ (t Rn : ℕ), Squarefree t → 2 ≤ Rn →
        |∑ r ∈ Finset.Icc 1 Rn, (if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ)/Work.ZeroDensity.Jutila.kap r else 0)|
          ≤ Ch*(∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ))*Real.exp (-(c*Real.sqrt (Real.log (Rn:ℝ)))))
    : ∃ C : ℝ, 0 < C ∧ ∀ (z N : ℕ), 2 ≤ z → z ≤ N → N < z*z →
        |Work.ZeroDensity.Jutila.s3exact z N - Work.ZeroDensity.Jutila.s3cont z N| ≤ C*(N:ℝ) := by
  refine ⟨(Real.pi^2/6)⁻¹ * (20*C1*(1+Ch*C3)*C5 + 2*C2*(1+Ch)*C4), by positivity, ?_⟩
  intro z N hz hzN hNz
  set Lz := Real.log (z:ℝ) + 2 with hLzdef
  have hz1 : (1:ℝ) ≤ (z:ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
  have hLz1 : 1 ≤ Lz := by
    rw [hLzdef]
    have := Real.log_nonneg hz1
    linarith
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hT0exp := s3T0_exp_le c hc z hz
  have hT0ge2 : (1:ℕ) ≤ s3T0 c z := by
    rw [s3T0, Nat.add_comm]
    exact le_trans (by norm_num : 1 ≤ 2) (Nat.le_add_right 2 _)
  have hT0posR : (1:ℝ) ≤ (s3T0 c z : ℝ) := by exact_mod_cast hT0ge2
  have hlogNz_le : Real.log ((N:ℝ)/(z:ℝ)) ≤ Real.log (z:ℝ) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ (by linarith)]
    nlinarith [show (N:ℝ) < (z:ℝ)*(z:ℝ) by exact_mod_cast hNz]
  have hlogNz_nn : 0 ≤ Real.log ((N:ℝ)/(z:ℝ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith), one_mul]
    exact_mod_cast hzN
  -- key t-sum bounds
  have hT1 : ∀ T : ℕ, (∑ t ∈ (Finset.Icc 1 T).filter Squarefree,
        ((t:ℝ)/Work.ZeroDensity.Jutila.kap t) * s3Kt Ch t) ≤ (1+Ch*C3)*(T:ℝ) := by
    intro T
    calc (∑ t ∈ (Finset.Icc 1 T).filter Squarefree, ((t:ℝ)/Work.ZeroDensity.Jutila.kap t) * s3Kt Ch t)
        ≤ ∑ t ∈ (Finset.Icc 1 T).filter Squarefree, (((t:ℝ)/Work.ZeroDensity.Jutila.kap t) * 1
            + Ch * (((t:ℝ)/Work.ZeroDensity.Jutila.kap t) * (∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ)))) := by
          apply Finset.sum_le_sum; intro t ht
          have h0 : 0 ≤ (t:ℝ)/Work.ZeroDensity.Jutila.kap t :=
            div_nonneg (by positivity) (le_of_lt (Work.ZeroDensity.Jutila.kap_pos t))
          have := mul_le_mul_of_nonneg_left (s3Kt_le Ch (le_of_lt hCh) t) h0
          linarith [this]
      _ = (∑ t ∈ (Finset.Icc 1 T).filter Squarefree, ((t:ℝ)/Work.ZeroDensity.Jutila.kap t))
            + Ch * (∑ t ∈ (Finset.Icc 1 T).filter Squarefree,
                ((t:ℝ)/Work.ZeroDensity.Jutila.kap t) * (∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ))) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl; intro t ht; rw [mul_one]
      _ ≤ (T:ℝ) + Ch*(C3*(T:ℝ)) := by
          have ha : (∑ t ∈ (Finset.Icc 1 T).filter Squarefree, ((t:ℝ)/Work.ZeroDensity.Jutila.kap t)) ≤ (T:ℝ) := by
            calc (∑ t ∈ (Finset.Icc 1 T).filter Squarefree, ((t:ℝ)/Work.ZeroDensity.Jutila.kap t))
                ≤ ∑ t ∈ (Finset.Icc 1 T).filter Squarefree, (1:ℝ) :=
                  Finset.sum_le_sum (fun t ht => div_kap_le_one t (Finset.mem_filter.mp ht).2)
              _ = (((Finset.Icc 1 T).filter Squarefree).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
              _ ≤ (T:ℝ) := by
                  have hc' := Finset.card_le_card (Finset.filter_subset (fun t => Squarefree t) (Finset.Icc 1 T))
                  rw [Nat.card_Icc, Nat.add_sub_cancel] at hc'
                  exact_mod_cast hc'
          have hb : (∑ t ∈ (Finset.Icc 1 T).filter Squarefree,
                ((t:ℝ)/Work.ZeroDensity.Jutila.kap t) * (∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ))) ≤ C3*(T:ℝ) := by
            refine le_trans (le_of_eq ?_) (hts1 T)
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl; intro t ht
            by_cases h : Squarefree t
            · rw [if_pos h, abs_moebius_real t h, one_mul]
            · rw [if_neg h]
              have hz0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree h
              rw [hz0]; simp
          linarith [ha, mul_le_mul_of_nonneg_left hb (le_of_lt hCh)]
      _ = (1+Ch*C3)*(T:ℝ) := by ring
  have hT2 : ∀ T : ℕ, (∑ t ∈ (Finset.Icc 1 T).filter Squarefree,
        s3Kt Ch t / Work.ZeroDensity.Jutila.kap t) ≤ (1+Ch)*C4*Real.log ((T:ℝ)+2) := by
    intro T
    calc (∑ t ∈ (Finset.Icc 1 T).filter Squarefree, s3Kt Ch t / Work.ZeroDensity.Jutila.kap t)
        ≤ ∑ t ∈ (Finset.Icc 1 T).filter Squarefree, (1 + Ch*(∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ)))
            / Work.ZeroDensity.Jutila.kap t := by
          apply Finset.sum_le_sum; intro t ht
          apply div_le_div_of_nonneg_right (s3Kt_le Ch (le_of_lt hCh) t) (le_of_lt (Work.ZeroDensity.Jutila.kap_pos t))
      _ = (∑ t ∈ (Finset.Icc 1 T).filter Squarefree, (1/Work.ZeroDensity.Jutila.kap t))
            + Ch * (∑ t ∈ (Finset.Icc 1 T).filter Squarefree,
                (∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ))/Work.ZeroDensity.Jutila.kap t) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro t ht; ring
      _ ≤ (∑ t ∈ (Finset.Icc 1 T).filter Squarefree,
              (∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ))/Work.ZeroDensity.Jutila.kap t)
            + Ch * (∑ t ∈ (Finset.Icc 1 T).filter Squarefree,
                (∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ))/Work.ZeroDensity.Jutila.kap t) := by
          have hle : (∑ t ∈ (Finset.Icc 1 T).filter Squarefree, (1/Work.ZeroDensity.Jutila.kap t))
              ≤ ∑ t ∈ (Finset.Icc 1 T).filter Squarefree,
                  (∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ))/Work.ZeroDensity.Jutila.kap t := by
            apply Finset.sum_le_sum; intro t ht
            have ht1 : 1 ≤ t := (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).1
            apply div_le_div_of_nonneg_right (one_le_sigma t ht1) (le_of_lt (Work.ZeroDensity.Jutila.kap_pos t))
          linarith
      _ = (1+Ch) * (∑ t ∈ (Finset.Icc 1 T).filter Squarefree,
                (∑ d ∈ t.divisors, 1/Real.sqrt (d:ℝ))/Work.ZeroDensity.Jutila.kap t) := by ring
      _ ≤ (1+Ch) * (C4*Real.log ((T:ℝ)+2)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          refine le_trans (le_of_eq ?_) (hts2 T)
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl; intro t ht
          by_cases h : Squarefree t
          · rw [if_pos h, abs_moebius_real t h, one_mul]
          · rw [if_neg h]
            have hz0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree h
            rw [hz0]; simp
      _ = (1+Ch)*C4*Real.log ((T:ℝ)+2) := by ring
  -- auxiliary q-sums
  have hsumR : (∑ q ∈ Finset.Icc 1 (N/z), ((N/(q*z) : ℕ) : ℝ)) ≤ ((N:ℝ)/(z:ℝ))*Lz := by
    have h1 : (1:ℝ) + Real.log (((N/z : ℕ) : ℝ)) ≤ Lz := by
      have ha : Real.log (((N/z : ℕ) : ℝ)) ≤ Real.log ((N:ℝ)/(z:ℝ)) := by
        apply Real.log_le_log
        · exact_mod_cast (Nat.div_pos hzN (by omega : 0 < z))
        · exact Nat.cast_div_le
      rw [hLzdef]; linarith [hlogNz_le]
    calc (∑ q ∈ Finset.Icc 1 (N/z), ((N/(q*z) : ℕ) : ℝ))
        ≤ ∑ q ∈ Finset.Icc 1 (N/z), (N:ℝ)/((q:ℝ)*(z:ℝ)) :=
          Finset.sum_le_sum (fun q hq => by simpa [Nat.cast_mul] using Nat.cast_div_le (α := ℝ) (m := N) (n := q*z))
      _ = ((N:ℝ)/(z:ℝ)) * (∑ q ∈ Finset.Icc 1 (N/z), (1:ℝ)/(q:ℝ)) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q hq
          ring_nf
      _ ≤ ((N:ℝ)/(z:ℝ)) * Lz := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact le_trans (HarmonicLogBound (N/z)) h1
  have hsumQ : (∑ q ∈ Finset.Icc 1 (N/z), (1:ℝ)/(q:ℝ)) ≤ Lz := by
    have h1 : (1:ℝ) + Real.log (((N/z : ℕ) : ℝ)) ≤ Lz := by
      have ha : Real.log (((N/z : ℕ) : ℝ)) ≤ Real.log ((N:ℝ)/(z:ℝ)) := by
        apply Real.log_le_log
        · exact_mod_cast (Nat.div_pos hzN (by omega : 0 < z))
        · exact Nat.cast_div_le
      rw [hLzdef]; linarith [hlogNz_le]
    exact le_trans (HarmonicLogBound (N/z)) h1
  have hlogRq : ∀ q : ℕ, 1 ≤ q → Real.log ((((N/(q*z) : ℕ) : ℝ))+2) ≤ Lz := by
    intro q hq1
    have hRq : (((N/(q*z) : ℕ) : ℝ)) ≤ (N:ℝ)/((q:ℝ)*(z:ℝ)) := by
      simpa [Nat.cast_mul] using Nat.cast_div_le (α := ℝ) (m := N) (n := q*z)
    have h2 : (N:ℝ)/((q:ℝ)*(z:ℝ)) ≤ (z:ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      have hq1' : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
      nlinarith [show (N:ℝ) < (z:ℝ)*(z:ℝ) by exact_mod_cast hNz, hq1', hz1]
    have h3 : ((((N/(q*z) : ℕ) : ℝ))+2) ≤ (z:ℝ) + 2 := by linarith
    have h4 : Real.log ((((N/(q*z) : ℕ) : ℝ))+2) ≤ Real.log ((z:ℝ)+2) := Real.log_le_log (by positivity) h3
    rw [hLzdef]
    have h5 : Real.log ((z:ℝ)+2) ≤ Real.log (z:ℝ) + 2 := by
      have hz2 : (2:ℝ) ≤ (z:ℝ) := by exact_mod_cast hz
      have h6 : (z:ℝ) + 2 ≤ (z:ℝ) * 2 := by linarith [hz2]
      have h7 : Real.log ((z:ℝ)+2) ≤ Real.log ((z:ℝ)*2) := Real.log_le_log (by positivity) h6
      have h8 : Real.log ((z:ℝ)*2) = Real.log (z:ℝ) + Real.log 2 := Real.log_mul (by positivity) (by norm_num)
      have h9 : Real.log 2 ≤ 2 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
        linarith
      linarith [h7, h8, h9]
    linarith
  -- main estimate
  have hsum : |∑ q ∈ Finset.Icc 1 (N / z), ∑ t ∈ Finset.Icc 1 (N / (q * z)),
        (ArithmeticFunction.moebius t : ℝ) * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t) * Sqt z N q t|
      ≤ (20*C1*(1+Ch*C3)*C5 + 2*C2*(1+Ch)*C4)*(N:ℝ) := by
    have hstep1 : |∑ q ∈ Finset.Icc 1 (N / z), ∑ t ∈ Finset.Icc 1 (N / (q * z)),
          (ArithmeticFunction.moebius t : ℝ) * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t) * Sqt z N q t|
        ≤ ∑ q ∈ Finset.Icc 1 (N / z), ∑ t ∈ (Finset.Icc 1 (N / (q * z))).filter Squarefree,
            ((t : ℝ) / Work.ZeroDensity.Jutila.kap t) * |Sqt z N q t| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      apply Finset.sum_le_sum; intro q hq
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hsf : (∑ t ∈ Finset.Icc 1 (N / (q * z)),
            |(ArithmeticFunction.moebius t : ℝ) * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t) * Sqt z N q t|)
          = ∑ t ∈ (Finset.Icc 1 (N / (q * z))).filter Squarefree,
            |(ArithmeticFunction.moebius t : ℝ) * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t) * Sqt z N q t| := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
        intro t ht hnt
        rw [Finset.mem_filter] at hnt
        have hns : ¬ Squarefree t := fun hs => hnt ⟨ht, hs⟩
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]
        simp
      rw [hsf]
      apply Finset.sum_le_sum; intro t ht
      rw [Finset.mem_filter] at ht
      rw [abs_mul, abs_mul]
      have h1 : |(ArithmeticFunction.moebius t : ℝ)| ≤ 1 := by
        have h := ArithmeticFunction.abs_moebius_le_one (n := t)
        exact_mod_cast h
      have h2 : 0 ≤ (t:ℝ)/Work.ZeroDensity.Jutila.kap t :=
        div_nonneg (by positivity) (le_of_lt (Work.ZeroDensity.Jutila.kap_pos t))
      rw [abs_of_nonneg h2]
      calc |(ArithmeticFunction.moebius t : ℝ)| * ((t:ℝ)/Work.ZeroDensity.Jutila.kap t) * |Sqt z N q t|
          ≤ (1 * ((t:ℝ)/Work.ZeroDensity.Jutila.kap t)) * |Sqt z N q t| := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_right h1 h2
        _ = ((t : ℝ) / Work.ZeroDensity.Jutila.kap t) * |Sqt z N q t| := by ring
    refine le_trans hstep1 ?_
    have hperq : ∀ q ∈ Finset.Icc 1 (N / z),
        (∑ t ∈ (Finset.Icc 1 (N / (q * z))).filter Squarefree,
            ((t : ℝ) / Work.ZeroDensity.Jutila.kap t) * |Sqt z N q t|)
        ≤ 5*C1*(1+Ch*C3)*((s3T0 c z : ℝ)+1)^2*Lz^2 * ((N/(q*z) : ℕ) : ℝ)
          + 2*C2*(1+Ch)*C4*Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z : ℝ))))*Lz^4*((N:ℝ)/(q:ℝ)) := by
        intro q hq
        -- per-q bound
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        have hqz : q*z ≤ N := by
          have h2 := (Finset.mem_Icc.mp hq).2
          calc q*z ≤ (N/z)*z := Nat.mul_le_mul_right z h2
            _ ≤ N := Nat.div_mul_le_self N z
        have hA : ∀ t ∈ (Finset.Icc 1 (N/(q*z))).filter Squarefree,
            ((t:ℝ)/Work.ZeroDensity.Jutila.kap t) * |Sqt z N q t| ≤ ((t:ℝ)/Work.ZeroDensity.Jutila.kap t) *
              (5*C1*(s3Kt Ch t)*((s3T0 c z:ℝ)+1)^2*Lz^2
                + 2*C2*(s3Kt Ch t)*Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z:ℝ))))*((N:ℝ)/((q:ℝ)*(t:ℝ)))*Lz^3) := by
          intro t ht
          rw [Finset.mem_filter, Finset.mem_Icc] at ht
          obtain ⟨⟨ht1, ht2⟩, htsf⟩ := ht
          have hb := Sqt_bound z N q t hz hNz hq1 hqz ht1 ht2 htsf Ch c C1 C2 hCh hc hC1 hC2
              (fun r hr1 hrR => hsupb z N q r t hz hNz hq1 hr1 ht1 hrR ht2)
              (htvb z N q t hz hNz hq1 ht1 ht2)
              (fun Rn h2' hRn => hmert t Rn htsf h2')
          exact mul_le_mul_of_nonneg_left hb
            (div_nonneg (by positivity) (le_of_lt (Work.ZeroDensity.Jutila.kap_pos t)))
        have hRq1 : (0:ℝ) ≤ ((N/(q*z) : ℕ) : ℝ) := by positivity
        have hNq : (0:ℝ) ≤ (N:ℝ)/(q:ℝ) := by positivity
        calc (∑ t ∈ (Finset.Icc 1 (N/(q*z))).filter Squarefree,
                ((t:ℝ)/Work.ZeroDensity.Jutila.kap t) * |Sqt z N q t|)
            ≤ ∑ t ∈ (Finset.Icc 1 (N/(q*z))).filter Squarefree, ((t:ℝ)/Work.ZeroDensity.Jutila.kap t) *
                (5*C1*(s3Kt Ch t)*((s3T0 c z:ℝ)+1)^2*Lz^2
                  + 2*C2*(s3Kt Ch t)*Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z:ℝ))))*((N:ℝ)/((q:ℝ)*(t:ℝ)))*Lz^3) :=
                  Finset.sum_le_sum hA
          _ = 5*C1*((s3T0 c z : ℝ)+1)^2*Lz^2 * (∑ t ∈ (Finset.Icc 1 (N/(q*z))).filter Squarefree,
                  ((t:ℝ)/Work.ZeroDensity.Jutila.kap t) * s3Kt Ch t)
                + 2*C2*Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z : ℝ))))*Lz^3*((N:ℝ)/(q:ℝ))
                    * (∑ t ∈ (Finset.Icc 1 (N/(q*z))).filter Squarefree,
                        s3Kt Ch t / Work.ZeroDensity.Jutila.kap t) := by
                rw [show (∑ t ∈ (Finset.Icc 1 (N/(q*z))).filter Squarefree, ((t:ℝ)/Work.ZeroDensity.Jutila.kap t) *
                      (5*C1*(s3Kt Ch t)*((s3T0 c z:ℝ)+1)^2*Lz^2
                        + 2*C2*(s3Kt Ch t)*Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z:ℝ))))*((N:ℝ)/((q:ℝ)*(t:ℝ)))*Lz^3))
                    = ∑ t ∈ (Finset.Icc 1 (N/(q*z))).filter Squarefree,
                        (5*C1*((s3T0 c z : ℝ)+1)^2*Lz^2 * (((t:ℝ)/Work.ZeroDensity.Jutila.kap t) * s3Kt Ch t)
                          + 2*C2*Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z : ℝ))))*Lz^3*((N:ℝ)/(q:ℝ))
                              * (s3Kt Ch t / Work.ZeroDensity.Jutila.kap t)) from
                    Finset.sum_congr rfl (fun t ht => by
                      have ht0 : (t:ℝ) ≠ 0 := by
                        have h1 : 1 ≤ t := (Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).1
                        positivity
                      have hq0 : (q:ℝ) ≠ 0 := by positivity
                      have hk0 : Work.ZeroDensity.Jutila.kap t ≠ 0 := Work.ZeroDensity.Jutila.kap_ne_zero t
                      field_simp)]
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          _ ≤ 5*C1*((s3T0 c z : ℝ)+1)^2*Lz^2 * ((1+Ch*C3)*((N/(q*z) : ℕ) : ℝ))
                + 2*C2*Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z : ℝ))))*Lz^3*((N:ℝ)/(q:ℝ))
                    * ((1+Ch)*C4*Lz) := by
                refine add_le_add ?_ ?_
                · exact mul_le_mul_of_nonneg_left (hT1 (N/(q*z))) (by positivity)
                · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                  calc (∑ t ∈ (Finset.Icc 1 (N/(q*z))).filter Squarefree,
                          s3Kt Ch t / Work.ZeroDensity.Jutila.kap t)
                      ≤ (1+Ch)*C4*Real.log ((((N/(q*z) : ℕ) : ℝ))+2) := hT2 (N/(q*z))
                    _ ≤ (1+Ch)*C4*Lz := mul_le_mul_of_nonneg_left (hlogRq q hq1) (by positivity)
          _ ≤ 5*C1*(1+Ch*C3)*((s3T0 c z : ℝ)+1)^2*Lz^2 * ((N/(q*z) : ℕ) : ℝ)
                + 2*C2*(1+Ch)*C4*Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z : ℝ))))*Lz^4*((N:ℝ)/(q:ℝ)) := by
                refine add_le_add (le_of_eq ?_) (le_of_eq ?_)
                · ring
                · ring
    have hstep2 : (∑ q ∈ Finset.Icc 1 (N / z), ∑ t ∈ (Finset.Icc 1 (N / (q * z))).filter Squarefree,
            ((t : ℝ) / Work.ZeroDensity.Jutila.kap t) * |Sqt z N q t|)
        ≤ 5*C1*(1+Ch*C3)*((s3T0 c z : ℝ)+1)^2*Lz^2 * ((N:ℝ)/(z:ℝ))*Lz
          + 2*C2*(1+Ch)*C4*Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z : ℝ))))*Lz^4*(N:ℝ)*Lz := by
      refine le_trans (Finset.sum_le_sum hperq) ?_
      · -- sum over q
        have h1 : (∑ q ∈ Finset.Icc 1 (N/z), 5*C1*(1+Ch*C3)*((s3T0 c z : ℝ)+1)^2*Lz^2 * ((N/(q*z) : ℕ) : ℝ))
            = 5*C1*(1+Ch*C3)*((s3T0 c z : ℝ)+1)^2*Lz^2 * (∑ q ∈ Finset.Icc 1 (N/z), ((N/(q*z) : ℕ) : ℝ)) := by
              rw [Finset.mul_sum]
        have h2 : (∑ q ∈ Finset.Icc 1 (N/z), 2*C2*(1+Ch)*C4*Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z : ℝ))))*Lz^4*((N:ℝ)/(q:ℝ)))
            = 2*C2*(1+Ch)*C4*Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z : ℝ))))*Lz^4*(N:ℝ) * (∑ q ∈ Finset.Icc 1 (N/z), (1:ℝ)/(q:ℝ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro q hq
              have hq0 : (q:ℝ) ≠ 0 := by
                have : 1 ≤ q := (Finset.mem_Icc.mp hq).1
                positivity
              field_simp
        rw [Finset.sum_add_distrib, h1, h2]
        have h3 := mul_le_mul_of_nonneg_left hsumR (show (0:ℝ) ≤ 5*C1*(1+Ch*C3)*((s3T0 c z : ℝ)+1)^2*Lz^2 by positivity)
        have h4 := mul_le_mul_of_nonneg_left hsumQ (show (0:ℝ) ≤ 2*C2*(1+Ch)*C4*Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z : ℝ))))*Lz^4*(N:ℝ) by positivity)
        linarith [h3, h4]
    refine le_trans hstep2 ?_
    -- final numerics
    have hexp1 : Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z : ℝ)))) * Lz^5 ≤ 1 := hT0exp
    have hT0sq : ((s3T0 c z : ℝ)+1)^2 ≤ 4*(s3T0 c z : ℝ)^2 := by
      have h := hT0posR
      nlinarith [h]
    have hfirst : 5*C1*(1+Ch*C3)*((s3T0 c z : ℝ)+1)^2*Lz^2 * ((N:ℝ)/(z:ℝ))*Lz
        ≤ 5*C1*(1+Ch*C3)*4*C5*(N:ℝ) := by
      have hzpos : (0:ℝ) < (z:ℝ) := by linarith [hz1]
      have hb := ht0 z hz
      rw [div_mul_eq_mul_div] at *
      have h5 : (0:ℝ) ≤ 5*C1*(1+Ch*C3)*(N:ℝ) := by positivity
      have hb : (s3T0 c z : ℝ)^2*Lz^3/(z:ℝ) ≤ C5 := ht0 z hz
      have : ((s3T0 c z : ℝ)+1)^2*Lz^3/(z:ℝ) ≤ 4*C5 := by
        rw [div_le_iff₀ hzpos]
        have hb' : (s3T0 c z : ℝ)^2*Lz^3 ≤ C5*(z:ℝ) := by
          have h := ht0 z hz
          rwa [div_le_iff₀ hzpos] at h
        have h8 : ((s3T0 c z : ℝ)+1)^2*Lz^3 ≤ 4*(s3T0 c z : ℝ)^2*Lz^3 :=
          mul_le_mul_of_nonneg_right hT0sq (by positivity)
        linarith [h8, hb']
      calc 5*C1*(1+Ch*C3)*((s3T0 c z : ℝ)+1)^2*Lz^2 * ((N:ℝ)/(z:ℝ))*Lz
          = 5*C1*(1+Ch*C3)*(N:ℝ)*(((s3T0 c z : ℝ)+1)^2*Lz^3/(z:ℝ)) := by
            field_simp
        _ ≤ 5*C1*(1+Ch*C3)*(N:ℝ)*(4*C5) := mul_le_mul_of_nonneg_left this h5
        _ = 5*C1*(1+Ch*C3)*4*C5*(N:ℝ) := by ring
    have hsecond : 2*C2*(1+Ch)*C4*Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z : ℝ))))*Lz^4*(N:ℝ)*Lz
        ≤ 2*C2*(1+Ch)*C4*(N:ℝ) := by
      have h5 : (0:ℝ) ≤ 2*C2*(1+Ch)*C4*(N:ℝ) := by positivity
      have h6 : Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z : ℝ)))) * Lz^4 ≤ 1 := by
        have h7 : Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z : ℝ)))) * Lz^4 ≤
            Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z : ℝ)))) * Lz^5 :=
          mul_le_mul_of_nonneg_left (by
            have h8 := mul_le_mul_of_nonneg_right hLz1 (by positivity : (0:ℝ) ≤ Lz^4)
            simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using h8) (Real.exp_nonneg _)
        linarith [h7, hexp1]
      calc 2*C2*(1+Ch)*C4*Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z : ℝ))))*Lz^4*(N:ℝ)*Lz
          = 2*C2*(1+Ch)*C4*(N:ℝ)*(Real.exp (-(c*Real.sqrt (Real.log (s3T0 c z : ℝ))))*Lz^5) := by ring
        _ ≤ 2*C2*(1+Ch)*C4*(N:ℝ)*1 := mul_le_mul_of_nonneg_left hexp1 h5
        _ = 2*C2*(1+Ch)*C4*(N:ℝ) := by ring
    linarith [hfirst, hsecond]
  rw [s3diff_eq]
  rw [abs_mul, abs_of_pos (show (0:ℝ) < (Real.pi ^ 2 / 6)⁻¹ by positivity)]
  refine le_trans (mul_le_mul_of_nonneg_left hsum (show (0:ℝ) ≤ (Real.pi ^ 2 / 6)⁻¹ by positivity)) (le_of_eq ?_)
  ring


theorem S3FloorReduce (h : Work.ZeroDensity.Jutila.KappaMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z N : ℕ), 2 ≤ z → z ≤ N → N < z * z →
      |Work.ZeroDensity.Jutila.s3exact z N - Work.ZeroDensity.Jutila.s3cont z N| ≤ C * (N : ℝ) := by
  obtain ⟨Ch, c, hCh, hc, hm1, hm2⟩ := h
  obtain ⟨C1, hC1, hsupb⟩ := S3GhatSup
  obtain ⟨C2, hC2, htvb⟩ := S3GhatTV
  obtain ⟨⟨C3, hC3, hts1⟩, ⟨C4, hC4, hts2⟩⟩ := S3TsumBounds2
  obtain ⟨C5, hC5, ht0⟩ := S3T0Bound c hc
  exact S3FloorReduce_aux Ch c C1 C2 C3 C4 C5 hCh hc hC1 hC2 hC3 hC4 hC5
    hsupb htvb hts1 hts2 ht0 hm2

end

end Work.LinnikAreas.JutilaPieces