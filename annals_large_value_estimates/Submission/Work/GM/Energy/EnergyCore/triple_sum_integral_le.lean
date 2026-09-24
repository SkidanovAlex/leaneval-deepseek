import Mathlib
import Submission.Work.GM.Energy.Defs
import Submission.Work.GM.Energy.EnergyCore.normSq_smoothedPoly_eq
import Submission.Work.GM.Energy.EnergyCore.triple_sum_cpow_eq

/-!
# The triple-sum/integral bound of GM §11 (`‖R‖³` term)

Writing `D(u) = smoothedPoly N b u = ∑_{n ∈ [N,2N]} w(n/N) b_n n^{iu}`, we prove
(`triple_sum_integral_le`)

`∑_{t₁,t₂,t₃ ∈ W} ∫_{t₁+t₂-t₃-L}^{t₁+t₂-t₃+L} ‖D(u)‖² du ≤ 2 L C_w² ∑_{n₁,n₂ ∈ [N,2N]} ‖R(n₁/n₂)‖³`

where `C_w` bounds `|w|` and `R(v) = ∑_{t∈W} |v|^{it}`.

The route is the one used in GM Lemma 11.4.  Substituting `u = t₁+t₂-t₃+v` and expanding
`‖D‖²` as a double sum (`normSq_smoothedPoly_eq`), the sum over `t₁,t₂,t₃` produces, after
swapping the (`t`) and (`n`) summations, the discrete third moment `R(v)² conj(R(v))`
(`triple_sum_cpow_eq`).  The remaining factor `v^{iu}` has modulus `1`, so the whole complex
sum is bounded pointwise in `u` by `C_w² ∑ ‖R(n₁/n₂)‖³`, and integrating over an interval of
length `2L` gives the stated bound.

The key point (and the reason the bound is not the trivial `|W|³`) is the *factorization*
of the triple sum over `t`, which turns `|W|³` into `‖R‖³ ≤ |W|³`.
-/

namespace Work.GM.Energy.EnergyCore

open Complex Finset MeasureTheory
open scoped BigOperators
set_option autoImplicit false

/-- The coefficient `w(n₁/N) w(n₂/N) b_{n₁} conj(b_{n₂})` of the pair `(n₁,n₂)` in the
expansion of `‖D(u)‖²`. -/
private noncomputable def pairCoef (N : ℕ) (b : ℕ → ℂ) (n1 n2 : ℕ) : ℂ :=
  ((Submission.LargeValues.bumpW ((n1 : ℝ) / (N : ℝ))) : ℂ)
    * ((Submission.LargeValues.bumpW ((n2 : ℝ) / (N : ℝ))) : ℂ) * b n1
    * (starRingEnd ℂ) (b n2)

/-- The ratio `n₁/n₂`, as a real number (the variable of `R`). -/
private noncomputable def ratio (n1 n2 : ℕ) : ℝ := (n1 : ℝ) / (n2 : ℝ)

private lemma ratio_pos {n1 n2 : ℕ} (h1 : 1 ≤ n1) (h2 : 1 ≤ n2) : 0 < ratio n1 n2 := by
  have h1' : (0 : ℝ) < (n1 : ℝ) := by exact_mod_cast h1
  have h2' : (0 : ℝ) < (n2 : ℝ) := by exact_mod_cast h2
  unfold ratio
  exact div_pos h1' h2'

/-- The expansion of `‖D(u)‖²` as the real part of a double sum, in the notation of this file.
(Read off from `normSq_smoothedPoly_eq`; the only difference is
`(n₁:ℂ)/(n₂:ℂ) = ↑(n₁/n₂)`, by `Complex.ofReal_div`.) -/
private lemma normSq_eq_pair (N : ℕ) (hN : 1 ≤ N) (b : ℕ → ℂ) (u : ℝ) :
    ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2
      = (∑ n1 ∈ Finset.Icc N (2 * N), ∑ n2 ∈ Finset.Icc N (2 * N),
          pairCoef N b n1 n2 * ((ratio n1 n2 : ℂ)) ^ (I * (u : ℂ))).re := by
  rw [← Complex.normSq_eq_norm_sq, normSq_smoothedPoly_eq N hN b u]
  congr 1
  refine Finset.sum_congr rfl fun n1 _ => Finset.sum_congr rfl fun n2 _ => ?_
  simp only [pairCoef, ratio, Complex.ofReal_div]

/-- **The discrete third moment, with an extra factor.** For `r > 0` and any shift `v`,
`∑_{t₁,t₂,t₃ ∈ W} r^{i(t₁+t₂-t₃+v)} = R(r)² conj(R(r)) r^{iv}`.
This is `triple_sum_cpow_eq` combined with the additivity of `r^{(·)}` (`Complex.cpow_add`) and
the fact that the factor `r^{iv}` does not depend on `t₁,t₂,t₃`. -/
private lemma triple_shift_sum (W : Finset ℝ) {r : ℝ} (hr : 0 < r) (v : ℝ) :
    (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ((r : ℂ)) ^ (I * ((t1 + t2 - t3 + v : ℝ) : ℂ)))
      = Submission.GM.Rfun W r * Submission.GM.Rfun W r
          * (starRingEnd ℂ) (Submission.GM.Rfun W r) * ((r : ℂ)) ^ (I * (v : ℂ)) := by
  have hrne : ((r : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hsplit : ∀ t1 t2 t3 : ℝ,
      ((r : ℂ)) ^ (I * ((t1 + t2 - t3 + v : ℝ) : ℂ))
        = ((r : ℂ)) ^ (I * (((t1 + t2 - t3 : ℝ)) : ℂ)) * ((r : ℂ)) ^ (I * (v : ℂ)) := by
    intro t1 t2 t3
    rw [← Complex.cpow_add _ _ hrne]
    congr 1
    push_cast
    ring
  simp only [hsplit, ← Finset.sum_mul]
  rw [triple_sum_cpow_eq W hr]

/-- Interchange of a triple sum over `W` (three real variables) with a double sum over `s`
(two natural variables): both orders give the same (finite) sum. -/
private lemma swap5 (W : Finset ℝ) (s : Finset ℕ) (g : ℕ → ℕ → ℝ → ℝ → ℝ → ℂ) :
    (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, ∑ n1 ∈ s, ∑ n2 ∈ s, g n1 n2 t1 t2 t3)
      = ∑ n1 ∈ s, ∑ n2 ∈ s, ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W, g n1 n2 t1 t2 t3 := by
  conv_lhs =>
    enter [2, t1, 2, t2]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, t1]
    rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, a, 2, b, 2, c]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, a, 2, b]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, a]
    rw [Finset.sum_comm]

/-- **The pointwise (in `u`) bound.** For every `v`,
`∑_{t₁,t₂,t₃ ∈ W} ‖D(t₁+t₂-t₃+v)‖² ≤ C_w² ∑_{n₁,n₂ ∈ [N,2N]} ‖R(n₁/n₂)‖³`. -/
private lemma pointwise_le (N : ℕ) (hN : 1 ≤ N) (b : ℕ → ℂ) (hb : ∀ n, ‖b n‖ ≤ 1)
    (Cw : ℝ) (hCw0 : 0 ≤ Cw) (hCw : ∀ x, |Submission.LargeValues.bumpW x| ≤ Cw)
    (W : Finset ℝ) (v : ℝ) :
    (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        ‖Submission.LargeValues.smoothedPoly N b (t1 + t2 - t3 + v)‖ ^ 2)
      ≤ Cw ^ 2 * ∑ n1 ∈ Finset.Icc N (2 * N), ∑ n2 ∈ Finset.Icc N (2 * N),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3 := by
  set s : Finset ℕ := Finset.Icc N (2 * N) with hs
  have hs1 : ∀ n ∈ s, 1 ≤ n := by
    intro n hn
    rw [hs] at hn
    exact le_trans hN (Finset.mem_Icc.mp hn).1
  -- The triple sum over `W` factors through the discrete third moment.
  have hkey : (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        ‖Submission.LargeValues.smoothedPoly N b (t1 + t2 - t3 + v)‖ ^ 2)
      = (∑ n1 ∈ s, ∑ n2 ∈ s, pairCoef N b n1 n2
          * (Submission.GM.Rfun W (ratio n1 n2) * Submission.GM.Rfun W (ratio n1 n2)
              * (starRingEnd ℂ) (Submission.GM.Rfun W (ratio n1 n2))
              * ((ratio n1 n2 : ℂ)) ^ (I * (v : ℂ)))).re := by
    have hexp : ∀ t1 t2 t3 : ℝ,
        ‖Submission.LargeValues.smoothedPoly N b (t1 + t2 - t3 + v)‖ ^ 2
          = (∑ n1 ∈ s, ∑ n2 ∈ s, pairCoef N b n1 n2
              * ((ratio n1 n2 : ℂ)) ^ (I * (((t1 + t2 - t3 + v : ℝ)) : ℂ))).re := by
      intro t1 t2 t3
      rw [normSq_eq_pair N hN b (t1 + t2 - t3 + v)]
    simp only [hexp]
    simp only [← Complex.re_sum]
    rw [swap5 W s (fun n1 n2 t1 t2 t3 => pairCoef N b n1 n2
        * ((ratio n1 n2 : ℂ)) ^ (I * (((t1 + t2 - t3 + v : ℝ)) : ℂ)))]
    simp only [← Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun n1 hn1 => Finset.sum_congr rfl fun n2 hn2 => ?_
    rw [triple_shift_sum W (ratio_pos (hs1 n1 hn1) (hs1 n2 hn2)) v]
  rw [hkey]
  have hcoef : ∀ n1 ∈ s, ∀ n2 ∈ s, ‖pairCoef N b n1 n2‖ ≤ Cw ^ 2 := by
    intro n1 _ n2 _
    have h1 : ‖((Submission.LargeValues.bumpW ((n1 : ℝ) / (N : ℝ))) : ℂ)‖ ≤ Cw := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hCw _
    have h2 : ‖((Submission.LargeValues.bumpW ((n2 : ℝ) / (N : ℝ))) : ℂ)‖ ≤ Cw := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hCw _
    have h4 : ‖(starRingEnd ℂ) (b n2)‖ ≤ 1 := by rw [Complex.norm_conj]; exact hb n2
    have hAB : ‖((Submission.LargeValues.bumpW ((n1 : ℝ) / (N : ℝ))) : ℂ)‖
        * ‖((Submission.LargeValues.bumpW ((n2 : ℝ) / (N : ℝ))) : ℂ)‖ ≤ Cw * Cw :=
      mul_le_mul h1 h2 (norm_nonneg _) hCw0
    calc ‖pairCoef N b n1 n2‖
        = ‖((Submission.LargeValues.bumpW ((n1 : ℝ) / (N : ℝ))) : ℂ)‖
            * ‖((Submission.LargeValues.bumpW ((n2 : ℝ) / (N : ℝ))) : ℂ)‖
            * ‖b n1‖ * ‖(starRingEnd ℂ) (b n2)‖ := by
          simp only [pairCoef, norm_mul]
      _ ≤ Cw * Cw * 1 * 1 := by
          refine mul_le_mul (mul_le_mul hAB (hb n1) (norm_nonneg _) (by positivity)) h4
            (norm_nonneg _) (by positivity)
      _ = Cw ^ 2 := by ring
  have hratio1 : ∀ n1 ∈ s, ∀ n2 ∈ s, ‖((ratio n1 n2 : ℂ)) ^ (I * (v : ℂ))‖ = 1 := by
    intro n1 hn1 n2 hn2
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (ratio_pos (hs1 n1 hn1) (hs1 n2 hn2))]
    simp [Complex.ofReal_im]
  calc (∑ n1 ∈ s, ∑ n2 ∈ s, pairCoef N b n1 n2
          * (Submission.GM.Rfun W (ratio n1 n2) * Submission.GM.Rfun W (ratio n1 n2)
              * (starRingEnd ℂ) (Submission.GM.Rfun W (ratio n1 n2))
              * ((ratio n1 n2 : ℂ)) ^ (I * (v : ℂ)))).re
      ≤ ‖∑ n1 ∈ s, ∑ n2 ∈ s, pairCoef N b n1 n2
          * (Submission.GM.Rfun W (ratio n1 n2) * Submission.GM.Rfun W (ratio n1 n2)
              * (starRingEnd ℂ) (Submission.GM.Rfun W (ratio n1 n2))
              * ((ratio n1 n2 : ℂ)) ^ (I * (v : ℂ)))‖ := Complex.re_le_norm _
    _ ≤ ∑ n1 ∈ s, ∑ n2 ∈ s, ‖pairCoef N b n1 n2
          * (Submission.GM.Rfun W (ratio n1 n2) * Submission.GM.Rfun W (ratio n1 n2)
              * (starRingEnd ℂ) (Submission.GM.Rfun W (ratio n1 n2))
              * ((ratio n1 n2 : ℂ)) ^ (I * (v : ℂ)))‖ := by
          calc _ ≤ ∑ n1 ∈ s, ‖∑ n2 ∈ s, pairCoef N b n1 n2
                * (Submission.GM.Rfun W (ratio n1 n2) * Submission.GM.Rfun W (ratio n1 n2)
                    * (starRingEnd ℂ) (Submission.GM.Rfun W (ratio n1 n2))
                    * ((ratio n1 n2 : ℂ)) ^ (I * (v : ℂ)))‖ := norm_sum_le _ _
            _ ≤ ∑ n1 ∈ s, ∑ n2 ∈ s, ‖pairCoef N b n1 n2
                * (Submission.GM.Rfun W (ratio n1 n2) * Submission.GM.Rfun W (ratio n1 n2)
                    * (starRingEnd ℂ) (Submission.GM.Rfun W (ratio n1 n2))
                    * ((ratio n1 n2 : ℂ)) ^ (I * (v : ℂ)))‖ :=
                Finset.sum_le_sum fun n1 _ => norm_sum_le _ _
    _ ≤ ∑ n1 ∈ s, ∑ n2 ∈ s, Cw ^ 2 * ‖Submission.GM.Rfun W (ratio n1 n2)‖ ^ 3 := by
          refine Finset.sum_le_sum fun n1 hn1 => Finset.sum_le_sum fun n2 hn2 => ?_
          have hR3 : ‖Submission.GM.Rfun W (ratio n1 n2) * Submission.GM.Rfun W (ratio n1 n2)
              * (starRingEnd ℂ) (Submission.GM.Rfun W (ratio n1 n2))‖
              = ‖Submission.GM.Rfun W (ratio n1 n2)‖ ^ 3 := by
            rw [norm_mul, norm_mul, Complex.norm_conj]; ring
          calc ‖pairCoef N b n1 n2
                * (Submission.GM.Rfun W (ratio n1 n2) * Submission.GM.Rfun W (ratio n1 n2)
                    * (starRingEnd ℂ) (Submission.GM.Rfun W (ratio n1 n2))
                    * ((ratio n1 n2 : ℂ)) ^ (I * (v : ℂ)))‖
              = ‖pairCoef N b n1 n2‖ * (‖Submission.GM.Rfun W (ratio n1 n2)
                    * Submission.GM.Rfun W (ratio n1 n2)
                    * (starRingEnd ℂ) (Submission.GM.Rfun W (ratio n1 n2))‖
                  * ‖((ratio n1 n2 : ℂ)) ^ (I * (v : ℂ))‖) := by
                rw [norm_mul, norm_mul]
            _ ≤ Cw ^ 2 * (‖Submission.GM.Rfun W (ratio n1 n2)‖ ^ 3 * 1) := by
                refine mul_le_mul (hcoef n1 hn1 n2 hn2) ?_ (by positivity) (by positivity)
                exact mul_le_mul (le_of_eq hR3) (le_of_eq (hratio1 n1 hn1 n2 hn2))
                  (norm_nonneg _) (by positivity)
            _ = Cw ^ 2 * ‖Submission.GM.Rfun W (ratio n1 n2)‖ ^ 3 := by ring
    _ = Cw ^ 2 * ∑ n1 ∈ s, ∑ n2 ∈ s, ‖Submission.GM.Rfun W (ratio n1 n2)‖ ^ 3 := by
          simp only [Finset.mul_sum]

/-- `D = smoothedPoly N b` is continuous, for `N ≥ 1` (each term `n^{iu}` is continuous for
`1 ≤ n`). -/
private lemma continuous_smoothedPoly (N : ℕ) (hN : 1 ≤ N) (b : ℕ → ℂ) :
    Continuous (fun t : ℝ => Submission.LargeValues.smoothedPoly N b t) := by
  unfold Submission.LargeValues.smoothedPoly
  refine continuous_finsetSum _ fun n hn => ?_
  have hn1 : 1 ≤ n := le_trans hN (Finset.mem_Icc.mp hn).1
  have hnne : (n : ℂ) ≠ 0 := by
    have h : (0 : ℕ) < n := lt_of_lt_of_le (by norm_num) hn1
    exact_mod_cast h.ne'
  have hg : Continuous fun t : ℝ => Complex.I * (t : ℂ) := by fun_prop
  have h1 : Continuous fun t : ℝ => (n : ℂ) ^ (Complex.I * (t : ℂ)) :=
    Continuous.const_cpow hg (Or.inl hnne)
  exact h1.const_mul _

/-- **GM §11 (`‖R‖³` term).** For `N ≥ 1`, `‖b‖_∞ ≤ 1`, `|w| ≤ C_w`, any finite `W` and `L > 0`,
`∑_{t₁,t₂,t₃ ∈ W} ∫_{t₁+t₂-t₃-L}^{t₁+t₂-t₃+L} ‖D(u)‖² du ≤ 2 L C_w² ∑_{n₁,n₂} ‖R(n₁/n₂)‖³`. -/
theorem triple_sum_integral_le (N : ℕ) (hN : 1 ≤ N) (b : ℕ → ℂ) (hb : ∀ n, ‖b n‖ ≤ 1)
    (Cw : ℝ) (hCw0 : 0 ≤ Cw) (hCw : ∀ x, |Submission.LargeValues.bumpW x| ≤ Cw)
    (W : Finset ℝ) (L : ℝ) (hL : 0 < L) :
    (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        ∫ u in (t1 + t2 - t3 - L)..(t1 + t2 - t3 + L),
          ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2)
      ≤ 2 * L * Cw ^ 2 *
          ∑ n1 ∈ Finset.Icc N (2 * N), ∑ n2 ∈ Finset.Icc N (2 * N),
            ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3 := by
  have hcon : Continuous (fun t : ℝ => Submission.LargeValues.smoothedPoly N b t) :=
    continuous_smoothedPoly N hN b
  -- change of variables `u = t₁+t₂-t₃+v` in each inner integral
  have hcv : ∀ t1 t2 t3 : ℝ,
      (∫ u in (t1 + t2 - t3 - L)..(t1 + t2 - t3 + L),
          ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2)
        = ∫ v in (-L)..L, ‖Submission.LargeValues.smoothedPoly N b (t1 + t2 - t3 + v)‖ ^ 2 := by
    intro t1 t2 t3
    have he : t1 + t2 - t3 - L = (t1 + t2 - t3) + (-L) := by ring
    rw [he, ← intervalIntegral.integral_comp_add_left
      (fun u : ℝ => ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2) (t1 + t2 - t3)]
  have hcont3 : ∀ t1 t2 t3 : ℝ, Continuous
      (fun v : ℝ => ‖Submission.LargeValues.smoothedPoly N b (t1 + t2 - t3 + v)‖ ^ 2) :=
    fun t1 t2 t3 => ((hcon.comp (by fun_prop)).norm.pow 2)
  -- interchange the triple sum with the integral
  have hswap : (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        ∫ v in (-L)..L, ‖Submission.LargeValues.smoothedPoly N b (t1 + t2 - t3 + v)‖ ^ 2)
      = ∫ v in (-L)..L, ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
          ‖Submission.LargeValues.smoothedPoly N b (t1 + t2 - t3 + v)‖ ^ 2 := by
    symm
    rw [intervalIntegral.integral_finsetSum (μ := volume)
      (f := fun t1 (v : ℝ) => ∑ t2 ∈ W, ∑ t3 ∈ W,
          ‖Submission.LargeValues.smoothedPoly N b (t1 + t2 - t3 + v)‖ ^ 2)
      (h := fun t1 _ => (continuous_finsetSum W (fun t2 _ =>
          continuous_finsetSum W (fun t3 _ => hcont3 t1 t2 t3))).intervalIntegrable (-L) L)]
    refine Finset.sum_congr rfl fun t1 _ => ?_
    rw [intervalIntegral.integral_finsetSum (μ := volume)
      (f := fun t2 (v : ℝ) => ∑ t3 ∈ W,
          ‖Submission.LargeValues.smoothedPoly N b (t1 + t2 - t3 + v)‖ ^ 2)
      (h := fun t2 _ => (continuous_finsetSum W (fun t3 _ =>
          hcont3 t1 t2 t3)).intervalIntegrable (-L) L)]
    refine Finset.sum_congr rfl fun t2 _ => ?_
    rw [intervalIntegral.integral_finsetSum (μ := volume)
      (f := fun t3 (v : ℝ) =>
          ‖Submission.LargeValues.smoothedPoly N b (t1 + t2 - t3 + v)‖ ^ 2)
      (h := fun t3 _ => (hcont3 t1 t2 t3).intervalIntegrable (-L) L)]
  have hInt1 : IntervalIntegrable (fun v : ℝ => ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
      ‖Submission.LargeValues.smoothedPoly N b (t1 + t2 - t3 + v)‖ ^ 2) volume (-L) L :=
    (continuous_finsetSum W (fun t1 _ => continuous_finsetSum W (fun t2 _ =>
      continuous_finsetSum W (fun t3 _ => hcont3 t1 t2 t3)))).intervalIntegrable (-L) L
  calc (∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
        ∫ u in (t1 + t2 - t3 - L)..(t1 + t2 - t3 + L),
          ‖Submission.LargeValues.smoothedPoly N b u‖ ^ 2)
      = ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
          ∫ v in (-L)..L, ‖Submission.LargeValues.smoothedPoly N b (t1 + t2 - t3 + v)‖ ^ 2 := by
        simp only [hcv]
    _ = ∫ v in (-L)..L, ∑ t1 ∈ W, ∑ t2 ∈ W, ∑ t3 ∈ W,
          ‖Submission.LargeValues.smoothedPoly N b (t1 + t2 - t3 + v)‖ ^ 2 := hswap
    _ ≤ ∫ v in (-L)..L, Cw ^ 2 * ∑ n1 ∈ Finset.Icc N (2 * N), ∑ n2 ∈ Finset.Icc N (2 * N),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3 := by
        refine intervalIntegral.integral_mono_on (by linarith) hInt1 ?_ (fun v _ => ?_)
        · exact (continuous_const).intervalIntegrable (-L) L
        · exact pointwise_le N hN b hb Cw hCw0 hCw W v
    _ = 2 * L * Cw ^ 2 * ∑ n1 ∈ Finset.Icc N (2 * N), ∑ n2 ∈ Finset.Icc N (2 * N),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3 := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring

end Work.GM.Energy.EnergyCore
