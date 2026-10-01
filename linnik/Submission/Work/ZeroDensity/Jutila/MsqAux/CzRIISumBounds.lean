/-
# The four Region-II sum bounds

For `c > 0` there is `C = C(c)` bounding, uniformly in `1 ≤ w ≤ y ≤ N`, `N < w·y` and `q`:

1. `Σ_{q ≤ ⌊N/y⌋} (1/q)·Dc c ⌊N/(qw)⌋`,
2. `Σ_{q ≤ ⌊N/y⌋} (1/q)·Dc c ⌊N/(qy)⌋`,
3. `Σ_{r ≤ R} (Σ_{d ∣ r} d^{-1/2})·Dc c (czTmax w y N q r)` by `C·(y/w + R·Dc c ⌊N/(qy)⌋)`,
4. `Σ_{r ≤ R} (Σ_{d ∣ r} d^{-1/2})·(czTmax w y N q r / w)²` by `C·R³/y²`,

where `R = ⌊N/(qw)⌋` and `czTmax w y N q r = min ⌊N/(qy)⌋ ⌊w/(⌊y/r⌋+1)⌋`.

Clauses 1, 2 are `LzDiffAux.CzRIIQSumBoundFinal` and clause 4 is `LzDiffAux.CzRIIRow4Final`;
both are reused verbatim.  Clause 3 is proved here.  Writing `T = ⌊N/(qy)⌋`, `W = y/w` and
`R = ⌊N/(qw)⌋`, the argument is:

* for `r ≤ R` one has `r < y`, and since `⌊y/r⌋+1 ≤ 2y/r` the floor cut-off in `czTmax`
  is at least `⌊w·r/(2y)⌋ ≥ w·r/(4y)` whenever `w·r/(4y) ≥ 1`; hence

    `Dc c (czTmax w y N q r) ≤ Dc c T + czEpsR c (w·r/(4y))`;

* the divisor swap (`LzDiffAux.SumDivisorsIccSwap`) turns the enveloped part into
  `Σ_{d ≤ R} d^{-1/2} Σ_{m ≤ R/d} czEpsR c ((w·d/(4y))·m)`, and the sum bound
  `czRII_eps_sum_le` (`Σ_{m ≤ M} czEpsR c (a·m) ≤ K·M·czEpsR c (a·M)`, valid for *every* `a > 0`)
  evaluates it as `≪ R·czEpsR c (w·R/(4y))·Σ_{d ≤ R} d^{-3/2} ≪ R·Dc c T`, where the last
  comparison is the scale bound `czRII_scale_le`, which uses `R ≥ W·T - 1`.

The remaining elementary inputs are `Σ_{r ≤ R} σ_{-1/2}(r) ≤ C·R` (`czRII_sumSig_le`) and the
envelope comparisons `czRII_czEpsR_div_le` (rescaling by a factor `n ≥ 1` costs at most
`exp (c√log n)`).
-/
import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.czReindexDefs
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs
import Submission.Work.ZeroDensity.Jutila.BzCross.ModelBDefs
import Submission.Work.ZeroDensity.Jutila.KappaMertensDefs
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRIIQSumBoundFinal
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzRIIRow4Final
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.SumDivisorsIccSwap
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.CzSigmaTsumHere
import Submission.Work.ZeroDensity.Jutila.BzCross.czRII_aux_bounds
import Submission.Work.BGTZ.sum_inv_sqrt_le

set_option autoImplicit false

namespace Work.ZeroDensity.Jutila.MsqAux

open Finset
open Work.ZeroDensity.Jutila
open Work.ZeroDensity.Jutila.BzCross (czEpsR czEpsR_anti czEpsR_one czEpsR_nonneg sqrt_le_sqrt_add Dc_eq_epsR)

noncomputable section

private lemma czRII_exp_half_log (x : ℝ) (hx : 0 < x) :
    Real.exp (Real.log x / 2) = Real.sqrt x := by
  have h2 : (Real.exp (Real.log x / 2)) ^ 2 = x := by
    rw [sq, ← Real.exp_add]
    have : Real.log x / 2 + Real.log x / 2 = Real.log x := by ring
    rw [this, Real.exp_log hx]
  have hs : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have key : (Real.exp (Real.log x / 2)) ^ 2 = Real.sqrt x ^ 2 := by rw [h2, hs]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp key with h | h
  · exact h
  · have h1 := Real.exp_pos (Real.log x / 2)
    have h3 := Real.sqrt_pos.mpr hx
    linarith

lemma czRII_czEpsR_div_le (c : ℝ) (hc : 0 ≤ c) {x n : ℝ} (hx : 0 < x) (hn : 1 ≤ n) :
    czEpsR c (x / n) ≤ Real.exp (c * Real.sqrt (Real.log n)) * czEpsR c x := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  rcases le_or_gt x n with hxn | hxn
  · have h1 : czEpsR c (x / n) = 1 :=
      czEpsR_one (by positivity) (by rw [div_le_one hn0]; exact hxn)
    rw [h1]
    have hlog : Real.log x ≤ Real.log n := Real.log_le_log hx hxn
    have hsq : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log n) := by
      rcases lt_or_ge (Real.log x) 0 with h | h
      · rw [Real.sqrt_eq_zero_of_nonpos h.le]; exact Real.sqrt_nonneg _
      · exact Real.sqrt_le_sqrt hlog
    have h2 : Real.exp (-(c * Real.sqrt (Real.log n))) ≤ czEpsR c x := by
      rw [czEpsR]
      exact Real.exp_le_exp.mpr (by nlinarith [hsq, hc])
    calc (1:ℝ) = Real.exp (c * Real.sqrt (Real.log n)) * Real.exp (-(c * Real.sqrt (Real.log n))) := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      _ ≤ Real.exp (c * Real.sqrt (Real.log n)) * czEpsR c x :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  · have hxn1 : 1 < x / n := by rw [lt_div_iff₀ hn0]; nlinarith
    have hlogxn : Real.log (x / n) = Real.log x - Real.log n := Real.log_div hx.ne' hn0.ne'
    have h1 : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log (x / n)) + Real.sqrt (Real.log n) := by
      have h := sqrt_le_sqrt_add (x := Real.log x) (y := Real.log (x / n))
        (by rw [hlogxn]; linarith [Real.log_nonneg hn])
      rwa [show Real.log x - Real.log (x / n) = Real.log n by rw [hlogxn]; ring] at h
    rw [czEpsR, czEpsR, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [h1, hc]

lemma czRII_czEpsR_ratio (c : ℝ) (hc : 0 ≤ c) {a : ℝ} (ha : 0 < a) {m M : ℕ}
    (hm1 : 1 ≤ m) (hmM : m ≤ M) :
    czEpsR c (a * (m : ℝ))
      ≤ czEpsR c (a * (M : ℝ)) * Real.exp (c * Real.sqrt (Real.log ((M : ℝ) / (m : ℝ)))) := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hM0 : (0:ℝ) < (M:ℝ) := by
    have : 0 < M := lt_of_lt_of_le (by omega : 0 < m) hmM
    exact_mod_cast this
  have hmM' : (m:ℝ) ≤ (M:ℝ) := by exact_mod_cast hmM
  have hMm1 : (1:ℝ) ≤ (M:ℝ)/(m:ℝ) := by rw [le_div_iff₀ hm0]; simpa using hmM'
  have hlogMm : 0 ≤ Real.log ((M:ℝ)/(m:ℝ)) := Real.log_nonneg hMm1
  have hKsplit : Real.log (a * (M:ℝ)) = Real.log (a * (m:ℝ)) + Real.log ((M:ℝ)/(m:ℝ)) := by
    rw [Real.log_mul ha.ne' hM0.ne', Real.log_mul ha.ne' hm0.ne',
        Real.log_div hM0.ne' hm0.ne']
    ring
  have hMm0 : 0 < (M:ℝ)/(m:ℝ) := div_pos hM0 hm0
  rcases lt_or_ge (Real.log (a * (m:ℝ))) 0 with hL | hL
  · have h1 : czEpsR c (a * (m:ℝ)) = 1 := by
      rw [czEpsR, Real.sqrt_eq_zero_of_nonpos hL.le, mul_zero, neg_zero, Real.exp_zero]
    rw [h1]
    have hKle : Real.log (a * (M:ℝ)) ≤ Real.log ((M:ℝ)/(m:ℝ)) := by rw [hKsplit]; linarith
    have hsq : Real.sqrt (Real.log (a * (M:ℝ))) ≤ Real.sqrt (Real.log ((M:ℝ)/(m:ℝ))) := by
      rcases lt_or_ge (Real.log (a * (M:ℝ))) 0 with h | h
      · rw [Real.sqrt_eq_zero_of_nonpos h.le]; exact Real.sqrt_nonneg _
      · exact Real.sqrt_le_sqrt hKle
    have hcz : Real.exp (-(c * Real.sqrt (Real.log ((M:ℝ)/(m:ℝ))))) ≤ czEpsR c (a * (M:ℝ)) := by
      rw [czEpsR]; exact Real.exp_le_exp.mpr (by nlinarith [hsq, hc])
    calc (1:ℝ) = Real.exp (c * Real.sqrt (Real.log ((M:ℝ)/(m:ℝ))))
          * Real.exp (-(c * Real.sqrt (Real.log ((M:ℝ)/(m:ℝ))))) := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      _ ≤ Real.exp (c * Real.sqrt (Real.log ((M:ℝ)/(m:ℝ)))) * czEpsR c (a * (M:ℝ)) :=
          mul_le_mul_of_nonneg_left hcz (Real.exp_pos _).le
      _ = czEpsR c (a * (M:ℝ)) * Real.exp (c * Real.sqrt (Real.log ((M:ℝ)/(m:ℝ)))) := by ring
  · have hsub : Real.sqrt (Real.log (a * (M:ℝ)))
        ≤ Real.sqrt (Real.log (a * (m:ℝ))) + Real.sqrt (Real.log ((M:ℝ)/(m:ℝ))) := by
      have h := sqrt_le_sqrt_add (x := Real.log (a * (M:ℝ))) (y := Real.log (a * (m:ℝ)))
        (by rw [hKsplit]; linarith [hlogMm])
      rwa [show Real.log (a * (M:ℝ)) - Real.log (a * (m:ℝ)) = Real.log ((M:ℝ)/(m:ℝ)) by
            rw [hKsplit]; ring] at h
    rw [czEpsR, czEpsR, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hsub, hc]

lemma czRII_eps_sum_le (c : ℝ) (hc : 0 ≤ c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a : ℝ) (M : ℕ), 0 < a →
      (∑ m ∈ Finset.Icc 1 M, czEpsR c (a * (m : ℝ)))
        ≤ K * (M : ℝ) * czEpsR c (a * (M : ℝ)) := by
  refine ⟨2 * Real.exp (2 * c^2), by positivity, ?_⟩
  intro a M ha
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  have hpt : ∀ m ∈ Finset.Icc 1 M, czEpsR c (a * (m:ℝ))
      ≤ czEpsR c (a * (M:ℝ)) * (Real.exp (2*c^2) * Real.sqrt ((M:ℝ)/(m:ℝ))) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmM : m ≤ M := (Finset.mem_Icc.mp hm).2
    have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hmM' : (m:ℝ) ≤ (M:ℝ) := by exact_mod_cast hmM
    have hs1 : (1:ℝ) ≤ (M:ℝ)/(m:ℝ) := by rw [le_div_iff₀ hm0]; simpa using hmM'
    have hs0 : 0 ≤ Real.log ((M:ℝ)/(m:ℝ)) := Real.log_nonneg hs1
    have hMs0 : (0:ℝ) < (M:ℝ) := lt_of_lt_of_le hm0 hmM'
    have hSm0 : 0 < (M:ℝ)/(m:ℝ) := div_pos hMs0 hm0
    refine le_trans (czRII_czEpsR_ratio c hc ha hm1 hmM)
      (mul_le_mul_of_nonneg_left ?_ (czEpsR_nonneg c _))
    rcases le_or_gt (Real.log ((M:ℝ)/(m:ℝ))) (4*c^2) with hs | hs
    · have h1 : Real.sqrt (Real.log ((M:ℝ)/(m:ℝ))) ≤ 2*c := by
        rw [Real.sqrt_le_iff]
        exact ⟨by linarith, by nlinarith⟩
      have h2 : c * Real.sqrt (Real.log ((M:ℝ)/(m:ℝ))) ≤ 2*c^2 :=
        calc c * Real.sqrt (Real.log ((M:ℝ)/(m:ℝ))) ≤ c * (2*c) :=
              mul_le_mul_of_nonneg_left h1 hc
          _ = 2*c^2 := by ring
      have h3 : 1 ≤ Real.sqrt ((M:ℝ)/(m:ℝ)) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hs1
      calc Real.exp (c * Real.sqrt (Real.log ((M:ℝ)/(m:ℝ)))) ≤ Real.exp (2*c^2) :=
            Real.exp_le_exp.mpr h2
        _ ≤ Real.exp (2*c^2) * Real.sqrt ((M:ℝ)/(m:ℝ)) := by
            nlinarith [Real.exp_pos (2*c^2), h3]
    · have h4 : Real.sqrt (4*c^2) = 2*c := by
        rw [show (4:ℝ)*c^2 = (2*c)^2 by ring, Real.sqrt_sq (by linarith : (0:ℝ) ≤ 2*c)]
      have h5 : 2*c ≤ Real.sqrt (Real.log ((M:ℝ)/(m:ℝ))) := by
        rw [← h4]; exact Real.sqrt_le_sqrt hs.le
      have hs2 : c * Real.sqrt (Real.log ((M:ℝ)/(m:ℝ))) ≤ Real.log ((M:ℝ)/(m:ℝ)) / 2 := by
        nlinarith [h5, Real.sqrt_nonneg (Real.log ((M:ℝ)/(m:ℝ))), Real.sq_sqrt hs0]
      have h7 : 1 ≤ Real.exp (2*c^2) := by
        rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity)
      calc Real.exp (c * Real.sqrt (Real.log ((M:ℝ)/(m:ℝ))))
            ≤ Real.exp (Real.log ((M:ℝ)/(m:ℝ))/2) := Real.exp_le_exp.mpr hs2
        _ = Real.sqrt ((M:ℝ)/(m:ℝ)) := czRII_exp_half_log _ hSm0
        _ ≤ Real.exp (2*c^2) * Real.sqrt ((M:ℝ)/(m:ℝ)) := by
            nlinarith [Real.sqrt_nonneg ((M:ℝ)/(m:ℝ)), h7]
  calc (∑ m ∈ Finset.Icc 1 M, czEpsR c (a * (m:ℝ)))
      ≤ ∑ m ∈ Finset.Icc 1 M,
          czEpsR c (a * (M:ℝ)) * (Real.exp (2*c^2) * Real.sqrt ((M:ℝ)/(m:ℝ))) :=
        Finset.sum_le_sum hpt
    _ = czEpsR c (a * (M:ℝ)) * Real.exp (2*c^2)
          * (∑ m ∈ Finset.Icc 1 M, Real.sqrt ((M:ℝ)/(m:ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro m _; ring
    _ ≤ czEpsR c (a * (M:ℝ)) * Real.exp (2*c^2) * (2*(M:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (czEpsR_nonneg c _) (Real.exp_pos _).le)
        exact Work.ZeroDensity.Jutila.LzDiffAux.sum_sqrt_div_le_two_mul M
    _ = 2 * Real.exp (2*c^2) * (M:ℝ) * czEpsR c (a * (M:ℝ)) := by ring

lemma czRII_sumSig_le :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ,
      (∑ r ∈ Finset.Icc 1 R, ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) ≤ C * (R : ℝ) := by
  refine ⟨3, by norm_num, ?_⟩
  intro R
  rw [Work.ZeroDensity.Jutila.LzDiffAux.SumDivisorsIccSwap (fun d (_ : ℕ) => (1:ℝ)/Real.sqrt (d:ℝ)) R]
  calc ∑ d ∈ Finset.Icc 1 R, ∑ m ∈ Finset.Icc 1 (R/d), (1:ℝ)/Real.sqrt (d:ℝ)
      = ∑ d ∈ Finset.Icc 1 R, ((R/d : ℕ) : ℝ) * ((1:ℝ)/Real.sqrt (d:ℝ)) := by
        apply Finset.sum_congr rfl; intro d _
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        simp
    _ ≤ ∑ d ∈ Finset.Icc 1 R, ((R:ℝ)/(d:ℝ)) * ((1:ℝ)/Real.sqrt (d:ℝ)) := by
        apply Finset.sum_le_sum; intro d _
        exact mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)
    _ = (R:ℝ) * ∑ d ∈ Finset.Icc 1 R, (1/Real.sqrt (d:ℝ)) * (1/(d:ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro d hd
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
        rw [div_eq_mul_inv, one_div, one_div]
        ring
    _ ≤ (R:ℝ) * 3 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg R)
        exact Work.ZeroDensity.Jutila.LzDiffAux.sum_inv_sqrt_mul_inv_le_three_lz R
    _ = 3 * (R:ℝ) := by ring

/-! ## The row-3 bound -/

/-- `czEpsR c x ≤ 1` for `c ≥ 0`. -/
lemma czRII_czEpsR_le_one (c : ℝ) (hc : 0 ≤ c) (x : ℝ) : czEpsR c x ≤ 1 := by
  rw [czEpsR, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by
    have := Real.sqrt_nonneg (Real.log x)
    nlinarith [hc, this])

/-- Pointwise bound of `Dc c (czTmax …)` by `Dc c (czT …)` plus the envelope at `w·r/(4y)`. -/
lemma czRII_Dc_czTmax_le (c : ℝ) (hc : 0 ≤ c) {w y : ℝ} (hw : 0 < w) (hwy : w ≤ y)
    {N q r : ℕ} (hr1 : 1 ≤ r) (hry : (r : ℝ) < y) :
    Dc c (Work.ZeroDensity.Jutila.BzCross.czTmax w y N q r)
      ≤ Dc c (czT y N q) + czEpsR c (w * (r : ℝ) / (4 * y)) := by
  have hy0 : 0 < y := lt_of_lt_of_le hw hwy
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hcz : Work.ZeroDensity.Jutila.BzCross.czTmax w y N q r
      = min (czT y N q) ⌊w / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1)⌋₊ := rfl
  rw [hcz]
  rcases le_total (czT y N q) ⌊w / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1)⌋₊ with h | h
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (czEpsR_nonneg c _)
  · rw [min_eq_right h]
    refine le_trans ?_ (le_add_of_nonneg_left (Dc_pos c (czT y N q)).le)
    set F := ⌊w / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1)⌋₊ with hF
    by_cases hsmall : w * (r : ℝ) / (4 * y) ≤ 1
    · rw [czEpsR_one (by positivity) hsmall]
      exact Dc_le_one hc F
    · have hsmall' : 1 < w * (r : ℝ) / (4 * y) := lt_of_not_ge hsmall
      have hXpos : 0 < w * (r : ℝ) / (4 * y) := by positivity
      have hAle : ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) ≤ y / (r : ℝ) := Nat.floor_le (by positivity)
      have h1r : (1 : ℝ) ≤ y / (r : ℝ) := by rw [le_div_iff₀ hr0]; linarith [hry.le]
      have hden : ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1 ≤ 2 * y / (r : ℝ) := by
        have h2 : y / (r : ℝ) + y / (r : ℝ) = 2 * y / (r : ℝ) := by ring
        linarith [hAle, h1r, h2]
      have hdenpos : (0 : ℝ) < ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1 := by positivity
      have hAr : (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ)) * (r : ℝ) ≤ y := by
        have h := mul_le_mul_of_nonneg_right hAle hr0.le
        rwa [div_mul_cancel₀ _ (ne_of_gt hr0)] at h
      have hwdiv : w * (r : ℝ) / (2 * y) ≤ w / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1) := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * y) hdenpos]
        nlinarith [hAr, hry.le, hw, hy0]
      have hXle : w * (r : ℝ) / (4 * y) + 1 ≤ w / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1) := by
        have : w * (r : ℝ) / (2 * y) = 2 * (w * (r : ℝ) / (4 * y)) := by ring
        linarith
      have hFle : w * (r : ℝ) / (4 * y) ≤ (F : ℝ) := by
        have h' : w / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1) < (F : ℝ) + 1 := by
          rw [hF]; exact Nat.lt_floor_add_one _
        linarith
      exact czEpsR_anti hc hXpos hFle

/-- Scale comparison: the envelope at `w·R/(4y)` is bounded by `exp(c√log 5)·Dc c (czT …)`. -/
lemma czRII_scale_le (c : ℝ) (hc : 0 ≤ c) {w y : ℝ} (hw : 1 ≤ w) (hwy : w ≤ y)
    {N q : ℕ} (hq : 1 ≤ q) :
    czEpsR c (w * (czR w N q : ℝ) / (4 * y))
      ≤ Real.exp (c * Real.sqrt (Real.log 5)) * Dc c (czT y N q) := by
  have hw0 : 0 < w := lt_of_lt_of_le zero_lt_one hw
  have hy0 : 0 < y := lt_of_lt_of_le hw0 hwy
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hTle : (czT y N q : ℝ) ≤ (N : ℝ) / ((q : ℝ) * y) := by
    rw [czT]; exact Nat.floor_le (by positivity)
  have hRlt : (N : ℝ) / ((q : ℝ) * w) < (czR w N q : ℝ) + 1 := by
    rw [czR]; exact Nat.lt_floor_add_one _
  have hkey : ((czT y N q : ℝ) - 1) / 4 ≤ w * (czR w N q : ℝ) / (4 * y) := by
    have h1 : (czT y N q : ℝ) * y ≤ (N : ℝ) / (q : ℝ) := by
      rw [le_div_iff₀ hq0]
      have h := hTle
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) * y)] at h
      linarith [h]
    have h2 : (N : ℝ) / (q : ℝ) < w * ((czR w N q : ℝ) + 1) := by
      rw [div_lt_iff₀ hq0]
      have h := hRlt
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) * w)] at h
      nlinarith [h]
    have h3a : (czT y N q : ℝ) * y < w * (czR w N q : ℝ) + w := by
      have heq : w * ((czR w N q : ℝ) + 1) = w * (czR w N q : ℝ) + w := by ring
      linarith [h1, h2, heq]
    have h3b : (czT y N q : ℝ) < w * (czR w N q : ℝ) / y + w / y := by
      have hdiv : w * (czR w N q : ℝ) / y + w / y = (w * (czR w N q : ℝ) + w) / y := by ring
      rw [hdiv, lt_div_iff₀ hy0]
      linarith [h3a]
    have h3c : w / y ≤ 1 := (div_le_one hy0).mpr hwy
    have h3 : (czT y N q : ℝ) - 1 < w * (czR w N q : ℝ) / y := by linarith [h3b, h3c]
    have h3'' : ((czT y N q : ℝ) - 1) * y < w * (czR w N q : ℝ) := by
      rw [lt_div_iff₀ hy0] at h3
      exact h3
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) (by positivity : (0 : ℝ) < 4 * y)]
    nlinarith [h3'', hy0]
  rcases le_or_gt (czT y N q) 5 with hT5 | hT5
  · have h1 : czEpsR c (w * (czR w N q : ℝ) / (4 * y)) ≤ 1 :=
      czRII_czEpsR_le_one c hc _
    have hT5' : (czT y N q : ℝ) ≤ 5 := by exact_mod_cast hT5
    have hDc : Real.exp (-(c * Real.sqrt (Real.log 5))) ≤ Dc c (czT y N q) := by
      have h := Dc_antitone hc hT5
      rw [Dc] at h ⊢
      exact h
    calc czEpsR c (w * (czR w N q : ℝ) / (4 * y)) ≤ 1 := h1
      _ = Real.exp (c * Real.sqrt (Real.log 5)) * Real.exp (-(c * Real.sqrt (Real.log 5))) := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      _ ≤ Real.exp (c * Real.sqrt (Real.log 5)) * Dc c (czT y N q) :=
          mul_le_mul_of_nonneg_left hDc (Real.exp_pos _).le
  · have hT5' : 5 < czT y N q := hT5
    have hTpos : (0 : ℝ) < (czT y N q : ℝ) := by
      have : (5 : ℝ) < (czT y N q : ℝ) := by exact_mod_cast hT5
      linarith
    have hstep1 : czEpsR c (w * (czR w N q : ℝ) / (4 * y))
        ≤ czEpsR c (((czT y N q : ℝ) - 1) / 4) := by
      refine czEpsR_anti hc ?_ hkey
      have : (5 : ℝ) < (czT y N q : ℝ) := by exact_mod_cast hT5
      linarith
    have hstep2 : czEpsR c (((czT y N q : ℝ) - 1) / 4)
        ≤ czEpsR c ((czT y N q : ℝ) / 5) := by
      refine czEpsR_anti hc (by positivity) ?_
      have : (5 : ℝ) ≤ (czT y N q : ℝ) := by exact_mod_cast le_of_lt hT5
      linarith
    have hstep3 : czEpsR c ((czT y N q : ℝ) / 5)
        ≤ Real.exp (c * Real.sqrt (Real.log 5)) * czEpsR c (czT y N q : ℝ) :=
      czRII_czEpsR_div_le c hc hTpos (by norm_num)
    exact le_trans hstep1 (le_trans hstep2 hstep3)

/-- The `σ`-weighted enveloped divisor sum, via the divisor swap. -/
lemma czRII_czSigEpsR_sum_le (c : ℝ) (hc : 0 ≤ c) (Ke : ℝ) (hKe : 0 < Ke)
    (hE : ∀ (a : ℝ) (M : ℕ), 0 < a →
      (∑ m ∈ Finset.Icc 1 M, czEpsR c (a * (m : ℝ)))
        ≤ Ke * (M : ℝ) * czEpsR c (a * (M : ℝ)))
    {w y : ℝ} (hw : 0 < w) (hy : 0 < y) (R : ℕ) :
    (∑ r ∈ Finset.Icc 1 R, (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
        * czEpsR c (w * (r : ℝ) / (4 * y)))
      ≤ 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)) * (R : ℝ)
          * czEpsR c (w * (R : ℝ) / (4 * y)) := by
  rcases Nat.eq_zero_or_pos R with h0 | hR1
  · subst h0; simp
  have h1 : (∑ r ∈ Finset.Icc 1 R, (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
        * czEpsR c (w * (r : ℝ) / (4 * y)))
      = ∑ r ∈ Finset.Icc 1 R, ∑ d ∈ r.divisors,
          (1 / Real.sqrt (d : ℝ)) * czEpsR c (w * (r : ℝ) / (4 * y)) := by
    apply Finset.sum_congr rfl; intro r _; rw [Finset.sum_mul]
  rw [h1, Work.ZeroDensity.Jutila.LzDiffAux.SumDivisorsIccSwap
      (fun d r => (1 / Real.sqrt (d : ℝ)) * czEpsR c (w * (r : ℝ) / (4 * y))) R]
  have hY : 0 < Real.exp (c * Real.sqrt (Real.log 2)) := Real.exp_pos _
  have hε0 : 0 ≤ czEpsR c (w * (R : ℝ) / (4 * y)) := czEpsR_nonneg c _
  have hmid : ∀ d ∈ Finset.Icc 1 R,
      czEpsR c ((w * (d : ℝ) / (4 * y)) * (((R / d : ℕ) : ℝ)))
        ≤ Real.exp (c * Real.sqrt (Real.log 2)) * czEpsR c (w * (R : ℝ) / (4 * y)) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdR : d ≤ R := (Finset.mem_Icc.mp hd).2
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have h2d : R ≤ 2 * (d * (R / d)) := by
      have hdiv := Nat.div_add_mod R d
      have hmod : R % d < d := Nat.mod_lt R (by omega : 0 < d)
      have hdX : d ≤ d * (R / d) := by
        have : 1 ≤ R / d := (Nat.one_le_div_iff (by omega : 0 < d)).mpr hdR
        calc d = d * 1 := by ring
          _ ≤ d * (R / d) := Nat.mul_le_mul_left d this
      omega
    have h2d' : (R : ℝ) ≤ 2 * (((d * (R / d) : ℕ)) : ℝ) := by exact_mod_cast h2d
    have harg : (w * (R : ℝ) / (4 * y)) / 2 ≤ (w * (d : ℝ) / (4 * y)) * (((R / d : ℕ) : ℝ)) := by
      have e1 : (w * (R : ℝ) / (4 * y)) / 2 = w * (R : ℝ) / (8 * y) := by ring
      have e2 : (w * (d : ℝ) / (4 * y)) * (((R / d : ℕ) : ℝ))
          = w * ((d : ℝ) * (((R / d : ℕ) : ℝ))) / (4 * y) := by ring
      have h2d'' : (R : ℝ) * 4 ≤ ((d : ℝ) * (((R / d : ℕ) : ℝ))) * 8 := by
        have h := h2d'
        push_cast at h
        linarith [h]
      have hgoal : w * (R : ℝ) * (4 * y) ≤ w * ((d : ℝ) * (((R / d : ℕ) : ℝ))) * (8 * y) := by
        calc w * (R : ℝ) * (4 * y) = ((R : ℝ) * 4) * (w * y) := by ring
          _ ≤ (((d : ℝ) * (((R / d : ℕ) : ℝ))) * 8) * (w * y) :=
              mul_le_mul_of_nonneg_right h2d'' (mul_nonneg hw.le hy.le)
          _ = w * ((d : ℝ) * (((R / d : ℕ) : ℝ))) * (8 * y) := by ring
      rw [e1, e2, div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * y) (by positivity : (0 : ℝ) < 4 * y)]
      exact hgoal
    calc czEpsR c ((w * (d : ℝ) / (4 * y)) * (((R / d : ℕ) : ℝ)))
        ≤ czEpsR c ((w * (R : ℝ) / (4 * y)) / 2) := czEpsR_anti hc (by positivity) harg
      _ ≤ Real.exp (c * Real.sqrt (Real.log 2)) * czEpsR c (w * (R : ℝ) / (4 * y)) :=
          czRII_czEpsR_div_le c hc (by positivity) (by norm_num)
  calc ∑ d ∈ Finset.Icc 1 R, ∑ m ∈ Finset.Icc 1 (R / d),
        (1 / Real.sqrt (d : ℝ)) * czEpsR c (w * (((d * m : ℕ)) : ℝ) / (4 * y))
      = ∑ d ∈ Finset.Icc 1 R, (1 / Real.sqrt (d : ℝ))
          * (∑ m ∈ Finset.Icc 1 (R / d), czEpsR c ((w * (d : ℝ) / (4 * y)) * (m : ℝ))) := by
        apply Finset.sum_congr rfl; intro d _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro m _
        congr 1
        push_cast
        ring
    _ ≤ ∑ d ∈ Finset.Icc 1 R, (1 / Real.sqrt (d : ℝ))
          * (Ke * (((R / d : ℕ)) : ℝ) * czEpsR c ((w * (d : ℝ) / (4 * y)) * (((R / d : ℕ)) : ℝ))) := by
        apply Finset.sum_le_sum; intro d hd
        have hd0 : (0 : ℝ) < (d : ℝ) := by
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          exact_mod_cast (by omega : 0 < d)
        have ha : 0 < w * (d : ℝ) / (4 * y) := by positivity
        exact mul_le_mul_of_nonneg_left (hE (w * (d : ℝ) / (4 * y)) (R / d) ha)
          (by positivity)
    _ ≤ ∑ d ∈ Finset.Icc 1 R, (1 / Real.sqrt (d : ℝ))
          * (Ke * ((R : ℝ) / (d : ℝ))
              * (Real.exp (c * Real.sqrt (Real.log 2)) * czEpsR c (w * (R : ℝ) / (4 * y)))) := by
        apply Finset.sum_le_sum; intro d hd
        have hd0 : (0 : ℝ) < (d : ℝ) := by
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          exact_mod_cast (by omega : 0 < d)
        have hcoef : (((R / d : ℕ)) : ℝ) ≤ (R : ℝ) / (d : ℝ) := Nat.cast_div_le
        have hcomb : Ke * (((R / d : ℕ)) : ℝ) * czEpsR c ((w * (d : ℝ) / (4 * y)) * (((R / d : ℕ)) : ℝ))
            ≤ Ke * ((R : ℝ) / (d : ℝ))
                * (Real.exp (c * Real.sqrt (Real.log 2)) * czEpsR c (w * (R : ℝ) / (4 * y))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hcoef hKe.le) (hmid d hd)
            (czEpsR_nonneg c _) (by positivity)
        exact mul_le_mul_of_nonneg_left hcomb (by positivity)
    _ = Ke * Real.exp (c * Real.sqrt (Real.log 2)) * czEpsR c (w * (R : ℝ) / (4 * y))
          * (∑ d ∈ Finset.Icc 1 R, (1 / Real.sqrt (d : ℝ)) * ((R : ℝ) / (d : ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro d _; ring
    _ ≤ Ke * Real.exp (c * Real.sqrt (Real.log 2)) * czEpsR c (w * (R : ℝ) / (4 * y))
          * ((R : ℝ) * ∑ d ∈ Finset.Icc 1 R, ((1 / Real.sqrt (d : ℝ)) * (1 / (d : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (mul_nonneg hKe.le (Real.exp_pos _).le) (czEpsR_nonneg c _))
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro d hd
        have hd0 : (0 : ℝ) < (d : ℝ) := by
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          exact_mod_cast (by omega : 0 < d)
        exact le_of_eq (by rw [div_eq_mul_inv, div_eq_mul_inv]; ring)
    _ ≤ Ke * Real.exp (c * Real.sqrt (Real.log 2)) * czEpsR c (w * (R : ℝ) / (4 * y))
          * ((R : ℝ) * 3) := by
        apply mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (mul_nonneg hKe.le (Real.exp_pos _).le) (czEpsR_nonneg c _))
        exact mul_le_mul_of_nonneg_left
          (Work.ZeroDensity.Jutila.LzDiffAux.sum_inv_sqrt_mul_inv_le_three_lz R) (Nat.cast_nonneg R)
    _ = 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)) * (R : ℝ)
          * czEpsR c (w * (R : ℝ) / (4 * y)) := by ring

/-- **Clause 3**: the `Dc c (czTmax …)`-weighted `r`-sum. -/
lemma czRII_sumSigDcTmax_le (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ) (q : ℕ), 1 ≤ w → w ≤ y → (N : ℝ) < w * y →
      (∑ r ∈ Finset.Icc 1 (czR w N q),
        (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
          * Dc c (Work.ZeroDensity.Jutila.BzCross.czTmax w y N q r))
        ≤ C * (y / w + (czR w N q : ℝ) * Dc c (czT y N q)) := by
  obtain ⟨Cs, hCs, hSsig⟩ := czRII_sumSig_le
  obtain ⟨Ke, hKe, hE⟩ := czRII_eps_sum_le c hc.le
  refine ⟨Cs + 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)) * Real.exp (c * Real.sqrt (Real.log 5)),
    by positivity, ?_⟩
  intro w y N q hw hwy hNwy
  have hw0 : 0 < w := by linarith
  have hy0 : 0 < y := by linarith
  rcases Nat.eq_zero_or_pos q with hq0 | hq1
  · subst hq0
    have hR : czR w N 0 = 0 := by simp [czR]
    rw [hR, Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    have hnn : (0 : ℝ) ≤ y / w + (0 : ℝ) * Dc c (czT y N 0) := by
      have : (0 : ℝ) ≤ y / w := div_nonneg hy0.le hw0.le
      simp [this]
    have hCpos : 0 < Cs + 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2))
        * Real.exp (c * Real.sqrt (Real.log 5)) := by
      have h1 : 0 < Ke := hKe
      have h2 : 0 < Real.exp (c * Real.sqrt (Real.log 2)) := Real.exp_pos _
      have h3 : 0 < Real.exp (c * Real.sqrt (Real.log 5)) := Real.exp_pos _
      have hp : 0 < 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2))
          * Real.exp (c * Real.sqrt (Real.log 5)) := by
        nlinarith [h1, h2, h3, mul_pos h1 h2, mul_pos (mul_pos h1 h2) h3]
      linarith [hCs, hp]
    have := mul_nonneg hCpos.le hnn
    linarith
  · have hq0' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hRy : (czR w N q : ℝ) < y := by
      have h1 : (czR w N q : ℝ) ≤ (N : ℝ) / ((q : ℝ) * w) := by
        rw [czR]; exact Nat.floor_le (by positivity)
      have h2 : (N : ℝ) / ((q : ℝ) * w) < y := by
        rw [div_lt_iff₀ (by positivity)]
        have hq1' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
        have hle : w * y ≤ (q : ℝ) * (w * y) := by
          have h := mul_le_mul_of_nonneg_right hq1' (mul_nonneg hw0.le hy0.le)
          simpa using h
        have heq : (q : ℝ) * (w * y) = y * ((q : ℝ) * w) := by ring
        linarith [hNwy, hle, heq]
      linarith
    have hpt : ∀ r ∈ Finset.Icc 1 (czR w N q),
        (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
          * Dc c (Work.ZeroDensity.Jutila.BzCross.czTmax w y N q r)
          ≤ (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
            * (Dc c (czT y N q) + czEpsR c (w * (r : ℝ) / (4 * y))) := by
      intro r hr
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hrR : r ≤ czR w N q := (Finset.mem_Icc.mp hr).2
      have hry : (r : ℝ) < y := lt_of_le_of_lt (by exact_mod_cast hrR) hRy
      exact mul_le_mul_of_nonneg_left (czRII_Dc_czTmax_le c hc.le hw0 hwy hr1 hry)
        (Finset.sum_nonneg (fun d _ => by positivity))
    have hscale : czEpsR c (w * (czR w N q : ℝ) / (4 * y))
        ≤ Real.exp (c * Real.sqrt (Real.log 5)) * Dc c (czT y N q) :=
      czRII_scale_le c hc.le hw hwy hq1
    have hε : (∑ r ∈ Finset.Icc 1 (czR w N q),
          (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * czEpsR c (w * (r : ℝ) / (4 * y)))
        ≤ 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)) * (czR w N q : ℝ)
            * czEpsR c (w * (czR w N q : ℝ) / (4 * y)) :=
      czRII_czSigEpsR_sum_le c hc.le Ke hKe hE hw0 hy0 (czR w N q)
    have hDT : (0 : ℝ) ≤ Dc c (czT y N q) := (Dc_pos c _).le
    have hRnn : (0 : ℝ) ≤ (czR w N q : ℝ) := Nat.cast_nonneg _
    have hyw : (0 : ℝ) ≤ y / w := div_nonneg hy0.le hw0.le
    have h2 : 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)) * (czR w N q : ℝ)
          * czEpsR c (w * (czR w N q : ℝ) / (4 * y))
        ≤ 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)) * Real.exp (c * Real.sqrt (Real.log 5))
          * ((czR w N q : ℝ) * Dc c (czT y N q)) := by
      have h0 : (0 : ℝ) ≤ 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)) * (czR w N q : ℝ) := by
        positivity
      have := mul_le_mul_of_nonneg_left hscale h0
      nlinarith [this]
    calc (∑ r ∈ Finset.Icc 1 (czR w N q),
          (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
          * Dc c (Work.ZeroDensity.Jutila.BzCross.czTmax w y N q r))
        ≤ ∑ r ∈ Finset.Icc 1 (czR w N q),
            (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
              * (Dc c (czT y N q) + czEpsR c (w * (r : ℝ) / (4 * y))) :=
          Finset.sum_le_sum hpt
      _ = (∑ r ∈ Finset.Icc 1 (czR w N q),
              (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * Dc c (czT y N q))
            + ∑ r ∈ Finset.Icc 1 (czR w N q),
                (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * czEpsR c (w * (r : ℝ) / (4 * y)) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro r _; ring
      _ ≤ Dc c (czT y N q) * (Cs * (czR w N q : ℝ))
            + 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)) * (czR w N q : ℝ)
              * czEpsR c (w * (czR w N q : ℝ) / (4 * y)) := by
          refine add_le_add ?_ hε
          calc (∑ r ∈ Finset.Icc 1 (czR w N q),
                (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * Dc c (czT y N q))
              = (∑ r ∈ Finset.Icc 1 (czR w N q),
                  (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))) * Dc c (czT y N q) := by
                rw [Finset.sum_mul]
            _ ≤ (Cs * (czR w N q : ℝ)) * Dc c (czT y N q) :=
                mul_le_mul_of_nonneg_right (hSsig (czR w N q)) hDT
            _ = Dc c (czT y N q) * (Cs * (czR w N q : ℝ)) := by ring
      _ ≤ (Cs + 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)) * Real.exp (c * Real.sqrt (Real.log 5)))
            * (y / w + (czR w N q : ℝ) * Dc c (czT y N q)) := by
          have h1 : Dc c (czT y N q) * (Cs * (czR w N q : ℝ))
              ≤ Cs * ((czR w N q : ℝ) * Dc c (czT y N q)) := by
            nlinarith [hDT, hRnn, hCs]
          have h3 : (0 : ℝ) ≤ Cs + 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2))
              * Real.exp (c * Real.sqrt (Real.log 5)) := by
            have h2 : 0 < Real.exp (c * Real.sqrt (Real.log 2)) := Real.exp_pos _
            have h5 : 0 < Real.exp (c * Real.sqrt (Real.log 5)) := Real.exp_pos _
            have hp : 0 < 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2))
                * Real.exp (c * Real.sqrt (Real.log 5)) := by
              nlinarith [hKe, h2, h5, mul_pos hKe h2, mul_pos (mul_pos hKe h2) h5]
            linarith [hCs, hp]
          have h4 : ((czR w N q : ℝ) * Dc c (czT y N q))
              ≤ y / w + (czR w N q : ℝ) * Dc c (czT y N q) := le_add_of_nonneg_left hyw
          have h5 : (Cs + 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)) * Real.exp (c * Real.sqrt (Real.log 5)))
              * ((czR w N q : ℝ) * Dc c (czT y N q))
              ≤ (Cs + 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)) * Real.exp (c * Real.sqrt (Real.log 5)))
                * (y / w + (czR w N q : ℝ) * Dc c (czT y N q)) :=
            mul_le_mul_of_nonneg_left h4 h3
          have h6 : (Cs + 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)) * Real.exp (c * Real.sqrt (Real.log 5)))
                * ((czR w N q : ℝ) * Dc c (czT y N q))
              = Cs * ((czR w N q : ℝ) * Dc c (czT y N q))
                + 3 * Ke * Real.exp (c * Real.sqrt (Real.log 2)) * Real.exp (c * Real.sqrt (Real.log 5))
                  * ((czR w N q : ℝ) * Dc c (czT y N q)) := by ring
          linarith [h1, h2, h5, h6]

/-- **The four Region-II sum bounds.** -/
theorem CzRIISumBounds (c : ℝ) (hc : 0 < c) :
  ∃ C : ℝ, 0 < C ∧
  (∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) → (N : ℝ) < w * y →
      (∑ q ∈ Finset.Icc 1 (Work.ZeroDensity.Jutila.czQ y N), (1 : ℝ) / q
        * Work.ZeroDensity.Jutila.Dc c (Work.ZeroDensity.Jutila.czR w N q)) ≤ C)
  ∧ (∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) → (N : ℝ) < w * y →
      (∑ q ∈ Finset.Icc 1 (Work.ZeroDensity.Jutila.czQ y N), (1 : ℝ) / q
        * Work.ZeroDensity.Jutila.Dc c (Work.ZeroDensity.Jutila.czT y N q)) ≤ C)
  ∧ (∀ (w y : ℝ) (N : ℕ) (q : ℕ), 1 ≤ w → w ≤ y → (N : ℝ) < w * y →
      (∑ r ∈ Finset.Icc 1 (Work.ZeroDensity.Jutila.czR w N q),
        (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
        * Work.ZeroDensity.Jutila.Dc c (Work.ZeroDensity.Jutila.BzCross.czTmax w y N q r))
        ≤ C * (y / w + (Work.ZeroDensity.Jutila.czR w N q : ℝ)
            * Work.ZeroDensity.Jutila.Dc c (Work.ZeroDensity.Jutila.czT y N q)))
  ∧ (∀ (w y : ℝ) (N : ℕ) (q : ℕ), 1 ≤ w → w ≤ y → (N : ℝ) < w * y →
      (∑ r ∈ Finset.Icc 1 (Work.ZeroDensity.Jutila.czR w N q),
        (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
        * (((Work.ZeroDensity.Jutila.BzCross.czTmax w y N q r : ℝ) / w) ^ 2))
        ≤ C * ((Work.ZeroDensity.Jutila.czR w N q : ℝ) ^ 3 / y ^ 2)) := by
  obtain ⟨C12, hC12, hQ1, hQ2⟩ :=
    Work.ZeroDensity.Jutila.LzDiffAux.CzRIIQSumBoundFinal c hc
  obtain ⟨C3, hC3, hRow3⟩ := czRII_sumSigDcTmax_le c hc
  obtain ⟨C4, hC4, hRow4⟩ := Work.ZeroDensity.Jutila.LzDiffAux.CzRIIRow4Final c hc
  have hC12le : C12 ≤ max (max C12 (max C3 C4)) 1 :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hC3le : C3 ≤ max (max C12 (max C3 C4)) 1 :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hC4le : C4 ≤ max (max C12 (max C3 C4)) 1 :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  refine ⟨max (max C12 (max C3 C4)) 1, by positivity, ?_, ?_, ?_, ?_⟩
  · intro w y N hw hwy hyN hNwy
    exact le_trans (hQ1 w y N hw hwy hyN hNwy) hC12le
  · intro w y N hw hwy hyN hNwy
    exact le_trans (hQ2 w y N hw hwy hyN hNwy) hC12le
  · intro w y N q hw hwy hNwy
    have hw0 : (0 : ℝ) < w := by linarith
    have hy0 : (0 : ℝ) < y := by linarith
    refine le_trans (hRow3 w y N q hw hwy hNwy)
      (mul_le_mul_of_nonneg_right hC3le ?_)
    exact add_nonneg (div_nonneg hy0.le hw0.le)
      (mul_nonneg (Nat.cast_nonneg _) (Dc_pos c _).le)
  · intro w y N q hw hwy hNwy
    have hy0 : (0 : ℝ) < y := by linarith
    refine le_trans (hRow4 w y N q hw hwy hNwy)
      (mul_le_mul_of_nonneg_right hC4le ?_)
    positivity

end

end Work.ZeroDensity.Jutila.MsqAux
