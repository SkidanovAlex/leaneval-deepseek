import Mathlib
import Submission.Work.ZeroDensity.Jutila.LzAux.CzAuxDefs
import Submission.Work.LinnikAreas.Density4.BzHard.mertens_log_weighted_one
import Submission.Work.ZeroDensity.Jutila.LzAux.MertensReal
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.SigHalfLogSqfreeHere
import Submission.Work.ZeroDensity.Jutila.LzAux.ExpSqrtLogMulLogSq
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.KappaMertensHere
import Submission.Work.ZeroDensity.Jutila.LzAux.SumInvLogSqBound
import Submission.Commons.Analysis.SpecialFunctions.Harmonic.harmonic_log_bounds


/-! Re-homing into `Work.ZeroDensity.Jutila.LzDiffAux` of the proof of `CzModelCont` from
`Submission/Work/ZeroDensity/Jutila/LzAux/CzModelCont.lean`, required so that the dependency closure avoids a broken import
(see the module docstring of the original).  Contents are otherwise unchanged. -/

/-!
# The continuous model `czModelCont` of the two-sided `S₃` sum: `N log(N/y) + O(N)`
-/

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila
open Work.ZeroDensity.Jutila.LzAux

/-- `Σ_{q ≤ Q} (1/q)·1/(1 + (log(Q/q))²) ≤ C` (re-exported from the proved version of
`LzAux`). -/
theorem SumInvLogSqBound : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q →
    ∑ q ∈ Finset.Icc 1 Q, (1/(q:ℝ)) * (1/(1 + (Real.log ((Q:ℝ)/(q:ℝ)))^2)) ≤ C :=
  Work.ZeroDensity.Jutila.LzAux.SumInvLogSqBound

noncomputable section

/-- `czMain` in the "monomial" form used for the algebraic comparison. -/
lemma czC_czMain (c : ℕ) (α β X : ℝ) :
    czMain c α β X
      = LinnikAreas.Density4.BzS3.s3c c
          * (X * ((Real.log X - α - 1) * (Real.log X - β - 1) + 1)) := by
  rw [czMain]; ring

/-- The first log-argument of the continuous model, rewritten in terms of `Y₁`. -/
lemma czC_log1 (w : ℝ) (N q r t : ℕ)
    (hw : w ≠ 0) (hq : (q : ℝ) ≠ 0) (hr : (r : ℝ) ≠ 0) (ht : (t : ℝ) ≠ 0) (hN : (N : ℝ) ≠ 0) :
    Real.log ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) - czAl w t - 1
      = Real.log (cY1 N q w / (r : ℝ)) - 1 := by
  have hqr : ((q : ℝ) * (r : ℝ)) ≠ 0 := mul_ne_zero hq hr
  have hqrt : ((q : ℝ) * (r : ℝ) * (t : ℝ)) ≠ 0 := mul_ne_zero hqr ht
  have hqw : ((q : ℝ) * w) ≠ 0 := mul_ne_zero hq hw
  have hNqw : (N : ℝ) / ((q : ℝ) * w) ≠ 0 := div_ne_zero hN hqw
  unfold czAl cY1
  rw [Real.log_div (x := (N : ℝ)) (y := ((q : ℝ) * (r : ℝ) * (t : ℝ))) hN hqrt,
      Real.log_div (x := ((N : ℝ) / ((q : ℝ) * w))) (y := (r : ℝ)) hNqw hr,
      Real.log_div (x := (N : ℝ)) (y := ((q : ℝ) * w)) hN hqw,
      Real.log_mul (x := ((q : ℝ) * (r : ℝ))) (y := (t : ℝ)) hqr ht,
      Real.log_mul (x := (q : ℝ)) (y := (r : ℝ)) hq hr,
      Real.log_div (x := (w : ℝ)) (y := (t : ℝ)) hw ht,
      Real.log_mul (x := (q : ℝ)) (y := (w : ℝ)) hq hw]
  ring

/-- The second log-argument of the continuous model, rewritten in terms of `Y₂`. -/
lemma czC_log2 (y : ℝ) (N q r t : ℕ)
    (hy : y ≠ 0) (hq : (q : ℝ) ≠ 0) (hr : (r : ℝ) ≠ 0) (ht : (t : ℝ) ≠ 0) (hN : (N : ℝ) ≠ 0) :
    Real.log ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) - czBe y r - 1
      = Real.log (cY2 N q y / (t : ℝ)) - 1 := by
  have hqr : ((q : ℝ) * (r : ℝ)) ≠ 0 := mul_ne_zero hq hr
  have hqrt : ((q : ℝ) * (r : ℝ) * (t : ℝ)) ≠ 0 := mul_ne_zero hqr ht
  have hqy : ((q : ℝ) * y) ≠ 0 := mul_ne_zero hq hy
  have hNqy : (N : ℝ) / ((q : ℝ) * y) ≠ 0 := div_ne_zero hN hqy
  unfold czBe cY2
  rw [Real.log_div (x := (N : ℝ)) (y := ((q : ℝ) * (r : ℝ) * (t : ℝ))) hN hqrt,
      Real.log_div (x := ((N : ℝ) / ((q : ℝ) * y))) (y := (t : ℝ)) hNqy ht,
      Real.log_div (x := (N : ℝ)) (y := ((q : ℝ) * y)) hN hqy,
      Real.log_mul (x := ((q : ℝ) * (r : ℝ))) (y := (t : ℝ)) hqr ht,
      Real.log_mul (x := (q : ℝ)) (y := (r : ℝ)) hq hr,
      Real.log_div (x := (y : ℝ)) (y := (r : ℝ)) hy hr,
      Real.log_mul (x := (q : ℝ)) (y := (y : ℝ)) hq hy]
  ring

/-- **Termwise algebra of the continuous model.** -/
lemma czC_term (w y : ℝ) (N q r t : ℕ)
    (hw : w ≠ 0) (hy : y ≠ 0) (hq : (q : ℝ) ≠ 0) (hr : (r : ℝ) ≠ 0) (ht : (t : ℝ) ≠ 0)
    (hN : (N : ℝ) ≠ 0) :
    czMM r t * czMain (r * t) (czAl w t) (czBe y r) ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ)))
      = (Real.pi ^ 2 / 6)⁻¹ * ((N : ℝ) / (q : ℝ))
          * ((if Nat.Coprime r t then
                (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0)
              * (1 / kap r) * (1 / kap t)
              * ((Real.log (cY1 N q w / (r : ℝ)) - 1) * (Real.log (cY2 N q y / (t : ℝ)) - 1) + 1)) := by
  rw [czC_czMain]
  have h1 := czC_log1 w N q r t hw hq hr ht hN
  have h2 := czC_log2 y N q r t hy hq hr ht hN
  simp only [h1, h2]
  unfold czMM
  by_cases hc : Nat.Coprime r t
  · rw [if_pos hc]
    by_cases hsr : Squarefree r
    · by_cases hst : Squarefree t
      · rw [s3c_mul_eq_of_coprime hsr hst hc]
        have hkr : kap r ≠ 0 := kap_ne_zero r
        have hkt : kap t ≠ 0 := kap_ne_zero t
        field_simp
      · have hmu : (ArithmeticFunction.moebius t : ℝ) = 0 := by
          rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hst]; norm_num
        rw [hmu]; ring
    · have hmu : (ArithmeticFunction.moebius r : ℝ) = 0 := by
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsr]; norm_num
      rw [hmu]; ring
  · rw [if_neg hc]; ring

/-- Pointwise factorisation of the summand of `czModelCont`: the `r`-dependent part is
`[r⊥t]·(μ(r)/κ(r))` and the `t`-weight is `μ(t)/κ(t)`. -/
lemma czC_point (w y : ℝ) (N q r t : ℕ) (hkr : kap r ≠ 0) (hkt : kap t ≠ 0) :
    (if Nat.Coprime r t then
        (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0)
      * (1 / kap r) * (1 / kap t)
      * ((Real.log (cY1 N q w / (r : ℝ)) - 1) * (Real.log (cY2 N q y / (t : ℝ)) - 1) + 1)
    = ((ArithmeticFunction.moebius t : ℝ) / kap t)
      * ((if Nat.Coprime r t then (ArithmeticFunction.moebius r : ℝ) / kap r else 0)
          * ((Real.log (cY1 N q w / (r : ℝ)) - 1) * (Real.log (cY2 N q y / (t : ℝ)) - 1) + 1)) := by
  by_cases hc : Nat.Coprime r t
  · rw [if_pos hc, if_pos hc]; field_simp
  · rw [if_neg hc, if_neg hc]; ring

/-- The inner `r`-sum of the `q`-th slice factorises into `czP` and `czS`. -/
lemma czC_inner_eq (w y : ℝ) (N q t : ℕ) (hkt : kap t ≠ 0) :
    ∑ r ∈ Finset.Icc 1 (czR w N q),
        (if Nat.Coprime r t then
            (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0)
          * (1 / kap r) * (1 / kap t)
          * ((Real.log (cY1 N q w / (r : ℝ)) - 1) * (Real.log (cY2 N q y / (t : ℝ)) - 1) + 1)
      = ((ArithmeticFunction.moebius t : ℝ) / kap t)
          * ((Real.log (cY2 N q y / (t : ℝ)) - 1) * czP w N q t + czS w N q t) := by
  rw [czP, czS, mul_add, ← mul_assoc, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [czC_point w y N q r t (kap_ne_zero r) hkt]
  ring

/-- The `q`-th slice of `czModelCont` is the constant `ζ(2)⁻¹(N/q)` times `czTq`. -/
lemma czC_slice (w y : ℝ) (N q : ℕ) (hw : w ≠ 0) (hy : y ≠ 0) (hq : (q : ℝ) ≠ 0)
    (hN : (N : ℝ) ≠ 0) :
    (∑ r ∈ Finset.Icc 1 (czR w N q), ∑ t ∈ Finset.Icc 1 (czT y N q),
        czMM r t * czMain (r * t) (czAl w t) (czBe y r)
          ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))))
      = (Real.pi ^ 2 / 6)⁻¹ * ((N : ℝ) / (q : ℝ)) * czTq w y N q := by
  rw [Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (fun t ht =>
    czC_term w y N q r t hw hy hq (by have := (Finset.mem_Icc.mp hr).1; positivity)
      (by have := (Finset.mem_Icc.mp ht).1; positivity) hN))]
  rw [czTq, Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← Finset.mul_sum, czC_inner_eq w y N q t (kap_ne_zero t)]

/-- **Reduction of `czModelCont` to the `t`-sums `czTq`.** -/
lemma czModelCont_eq (w y : ℝ) (N : ℕ) (hw : w ≠ 0) (hy : y ≠ 0) (hN : (N : ℝ) ≠ 0) :
    czModelCont w y N
      = ∑ q ∈ Finset.Icc 1 (czQ y N),
          (Real.pi ^ 2 / 6)⁻¹ * ((N : ℝ) / (q : ℝ)) * czTq w y N q := by
  unfold czModelCont
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  exact czC_slice w y N q hw hy hq0 hN


/-! ## Elementary order facts for the `(q,r,t)`-ranges -/

lemma czQ_pos {y : ℝ} {N : ℕ} (h : 1 ≤ (N : ℝ) / y) : 1 ≤ czQ y N :=
  (Nat.one_le_floor_iff _).mpr h

lemma czR_pos {w : ℝ} {N q : ℕ} (h : 1 ≤ (N : ℝ) / ((q : ℝ) * w)) : 1 ≤ czR w N q :=
  (Nat.one_le_floor_iff _).mpr h

lemma czT_pos {y : ℝ} {N q : ℕ} (h : 1 ≤ (N : ℝ) / ((q : ℝ) * y)) : 1 ≤ czT y N q :=
  (Nat.one_le_floor_iff _).mpr h

lemma cY2_eq_czT (N q : ℕ) (y : ℝ) : ⌊cY2 N q y⌋₊ = czT y N q := rfl

lemma cY1_eq_czR (N q : ℕ) (w : ℝ) : ⌊cY1 N q w⌋₊ = czR w N q := rfl

/-- `1/2 ≤ log 2`. -/
lemma half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 2)]
  have hsq : Real.exp ((1 : ℝ) / 2) * Real.exp ((1 : ℝ) / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos ((1 : ℝ) / 2), Real.exp_one_lt_three, hsq]

lemma log_two_lt_one : Real.log 2 < 1 := by
  have h := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) (by norm_num)
  linarith

/-! ## The sharp Mertens sum `czG` with a real argument -/

/-- `|czG T − 1| ≤ C/(1 + log²T)` for all real `T ≥ 1`. -/
lemma czG_bound : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
    |czG T - 1| ≤ C * (1 / (1 + (Real.log T) ^ 2)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := MertensReal
  refine ⟨max 4 (17 * C₁), lt_max_of_lt_left (by norm_num), fun T hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hlogTnn : 0 ≤ Real.log T := Real.log_nonneg hT
  have hden : 0 < 1 + (Real.log T) ^ 2 := by positivity
  have hdenpos : 0 < 1 / (1 + (Real.log T) ^ 2) := by positivity
  have hb4 : (4 : ℝ) ≤ max 4 (17 * C₁) := le_max_left _ _
  have hb17 : 17 * C₁ ≤ max 4 (17 * C₁) := le_max_right _ _
  rcases lt_or_ge T 2 with h2 | h2
  · have hfloor : ⌊T⌋₊ = 1 := by
      have h1 : 1 ≤ ⌊T⌋₊ := (Nat.one_le_floor_iff T).mpr hT
      have h2' : ⌊T⌋₊ < 2 := (Nat.floor_lt (by linarith : (0 : ℝ) ≤ T)).mpr h2
      omega
    have hval : czG T = Real.log T - 1 := by
      rw [czG, hfloor, Finset.Icc_self, Finset.sum_singleton,
          ArithmeticFunction.moebius_apply_one]
      norm_num
    rw [hval]
    have hlogT2 : Real.log T ≤ Real.log 2 := Real.log_le_log hT0 (le_of_lt h2)
    have hkey : |Real.log T - 1 - 1| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [hlogTnn, hlogT2, log_two_lt_one]
    have h2h : (2 : ℝ) ≤ 4 * (1 / (1 + (Real.log T) ^ 2)) := by
      rw [mul_one_div, le_div_iff₀ hden]
      nlinarith [hlogTnn, hlogT2, log_two_lt_one]
    calc |Real.log T - 1 - 1| ≤ 2 := hkey
      _ ≤ max 4 (17 * C₁) * (1 / (1 + (Real.log T) ^ 2)) := by
          have hstep : 4 * (1 / (1 + (Real.log T) ^ 2))
              ≤ max 4 (17 * C₁) * (1 / (1 + (Real.log T) ^ 2)) :=
            mul_le_mul_of_nonneg_right hb4 hdenpos.le
          linarith
  · have hT2 : 2 ≤ T := h2
    have hlogTpos : 0 < Real.log T := Real.log_pos (by linarith)
    have hlogTge : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT2
    have hsq : (Real.log 2) ^ 2 ≤ (Real.log T) ^ 2 := by nlinarith [hlogTge, half_le_log_two]
    have hinv : 1 / (Real.log T) ^ 2 ≤ 4 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (Real.log T) ^ 2)]
      nlinarith [hsq, half_le_log_two]
    have hratio : 1 / (Real.log T) ^ 2 ≤ 17 * (1 / (1 + (Real.log T) ^ 2)) := by
      rw [mul_one_div, le_div_iff₀ hden]
      have hsplit : 1 / (Real.log T) ^ 2 * (1 + (Real.log T) ^ 2)
          = 1 / (Real.log T) ^ 2 + 1 := by
        field_simp
      rw [hsplit]; linarith
    rw [czG]
    calc |∑ t ∈ Finset.Icc 1 ⌊T⌋₊, ↑(ArithmeticFunction.moebius t) * (Real.log (T / ↑t) - 1) / ↑t - 1|
        ≤ C₁ / (Real.log T) ^ 2 := h₁ T hT2
      _ = C₁ * (1 / (Real.log T) ^ 2) := by ring
      _ ≤ C₁ * (17 * (1 / (1 + (Real.log T) ^ 2))) :=
          mul_le_mul_of_nonneg_left hratio hC₁.le
      _ = (17 * C₁) * (1 / (1 + (Real.log T) ^ 2)) := by ring
      _ ≤ max 4 (17 * C₁) * (1 / (1 + (Real.log T) ^ 2)) :=
          mul_le_mul_of_nonneg_right hb17 hdenpos.le

/-! ## The harmonic sum versus `log(N/y)` -/

lemma harm_bound : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (y : ℝ), 1 ≤ y → y ≤ (N : ℝ) →
    |(∑ q ∈ Finset.Icc 1 (czQ y N), (1 : ℝ) / (q : ℝ)) - Real.log ((N : ℝ) / y)| ≤ C := by
  obtain ⟨hlog, hH, _⟩ := Commons.Analysis.SpecialFunctions.Harmonic.harmonic_log_bounds
  refine ⟨1 + Real.log 2, by positivity, fun N y hy1 hyN => ?_⟩
  have hy0 : 0 < y := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hy0 hyN
  have hQ1 : 1 ≤ czQ y N := czQ_pos (by rw [le_div_iff₀ hy0, one_mul]; exact hyN)
  have hQ0 : 0 < czQ y N := by omega
  have hQ0R : (0 : ℝ) < (czQ y N : ℝ) := by exact_mod_cast hQ0
  have hQle : (czQ y N : ℝ) ≤ (N : ℝ) / y := Nat.floor_le (by positivity)
  have hQlt : (N : ℝ) / y < (czQ y N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlogQnn : 0 ≤ Real.log (czQ y N : ℝ) := Real.log_nonneg (by exact_mod_cast hQ1)
  have hlogmono : Real.log (czQ y N : ℝ) ≤ Real.log ((N : ℝ) / y) :=
    Real.log_le_log hQ0R hQle
  have hdiff : Real.log ((N : ℝ) / y) - Real.log (czQ y N : ℝ) ≤ Real.log 2 := by
    have hratio : ((N : ℝ) / y) / (czQ y N : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hQ0R, div_le_iff₀ hy0]
      have h1 : (N : ℝ) < ((czQ y N : ℝ) + 1) * y := (div_lt_iff₀ hy0).mp hQlt
      have h2 : ((czQ y N : ℝ) + 1) ≤ 2 * (czQ y N : ℝ) := by
        have : (1 : ℝ) ≤ (czQ y N : ℝ) := by exact_mod_cast hQ1
        linarith
      have h3 : ((czQ y N : ℝ) + 1) * y ≤ (2 * (czQ y N : ℝ)) * y :=
        mul_le_mul_of_nonneg_right h2 hy0.le
      linarith
    rw [← Real.log_div (x := (N : ℝ) / y) (y := ((czQ y N : ℕ) : ℝ)) (by positivity)
          (ne_of_gt hQ0R)]
    exact Real.log_le_log (by positivity) hratio
  have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have := hlog (czQ y N) hQ1
    linarith
  · have := hH (czQ y N) hQ1
    linarith

/-! ## The per-`q` bound: `czTq = ζ(2)·czG(Y₂) + O(1/(1+log²(Q/q)))` -/

/-- `1/(1+log²Y₂) ≤ 2/(1+log²(Q/q))` for `q ∈ [1,Q]` (uses `Y₂ = N/(qy) ≥ Q/q ≥ 1`). -/
lemma czY2_cmp {N : ℕ} {y : ℝ} {q : ℕ} (hq : q ∈ Finset.Icc 1 (czQ y N)) (hy0 : 0 < y) :
    1 / (1 + (Real.log (cY2 N q y)) ^ 2)
      ≤ 2 * (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)) := by
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hqle : q ≤ czQ y N := (Finset.mem_Icc.mp hq).2
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hXge1 : 1 ≤ ((czQ y N : ℕ) : ℝ) / (q : ℝ) := by
    rw [le_div_iff₀ hq0]; simpa using hqle
  have hXle : ((czQ y N : ℕ) : ℝ) / (q : ℝ) ≤ cY2 N q y := by
    rw [cY2, div_le_div_iff₀ hq0 (mul_pos hq0 hy0)]
    have h : ((czQ y N : ℕ) : ℝ) * y ≤ (N : ℝ) := by
      have h2 := Nat.floor_le (show (0 : ℝ) ≤ (N : ℝ) / y by positivity)
      rw [le_div_iff₀ hy0] at h2; exact h2
    nlinarith [h, hq0]
  have hlognn : 0 ≤ Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ)) := Real.log_nonneg hXge1
  have hlogle : Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ)) ≤ Real.log (cY2 N q y) :=
    Real.log_le_log (by linarith) hXle
  have hY2pos : (0 : ℝ) < 1 + (Real.log (cY2 N q y)) ^ 2 := by positivity
  have hXpos : (0 : ℝ) < 1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2 := by positivity
  have hkey : (1 / 2) * (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)
      ≤ 1 + (Real.log (cY2 N q y)) ^ 2 := by
    by_cases h1 : 1 ≤ Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))
    · nlinarith [hlogle, hlognn, h1]
    · have h1' : Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ)) < 1 := lt_of_not_ge h1
      nlinarith [hlognn, h1']
  rw [mul_one_div, div_le_div_iff₀ hY2pos hXpos]
  linarith

/-- `1 ≤ Y₂ = N/(qy)` for `q ∈ [1, ⌊N/y⌋]`, `y > 0`. -/
lemma cY2_ge_one {y : ℝ} {N q : ℕ} (hy0 : 0 < y) (hq : q ∈ Finset.Icc 1 (czQ y N)) :
    1 ≤ cY2 N q y := by
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hqle : q ≤ czQ y N := (Finset.mem_Icc.mp hq).2
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hQy : ((czQ y N : ℕ) : ℝ) * y ≤ (N : ℝ) := by
    have h := Nat.floor_le (show (0 : ℝ) ≤ (N : ℝ) / y by positivity)
    rw [le_div_iff₀ hy0] at h; exact h
  rw [cY2, le_div_iff₀ (mul_pos hq0 hy0), one_mul]
  have : (q : ℝ) ≤ ((czQ y N : ℕ) : ℝ) := by exact_mod_cast hqle
  nlinarith [hQy, this, hy0]

/-- `Y₂ ≤ Y₁` for `0 < w ≤ y`. -/
lemma cY2_le_cY1 {w y : ℝ} {N q : ℕ} (hw0 : 0 < w) (hy0 : 0 < y) (hwy : w ≤ y)
    (hq : q ∈ Finset.Icc 1 (czQ y N)) : cY2 N q y ≤ cY1 N q w := by
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have hQ1 : 1 ≤ czQ y N := le_trans hq1 (Finset.mem_Icc.mp hq).2
    have h : (0 : ℝ) < (czQ y N : ℝ) := by exact_mod_cast (by omega : 0 < czQ y N)
    have hQle := Nat.floor_le (show (0 : ℝ) ≤ (N : ℝ) / y by positivity)
    have hone : (1 : ℝ) ≤ (N : ℝ) / y := le_trans (by exact_mod_cast hQ1) hQle
    have := (le_div_iff₀ hy0).mp hone
    linarith
  rw [cY1, cY2, div_le_div_iff₀ (mul_pos hq0 hy0) (mul_pos hq0 hw0)]
  apply mul_le_mul_of_nonneg_left _ hNpos.le
  nlinarith [hwy, hq0]

/-- The termwise bound of the large-`R₁` case, with the two Mertens bounds abstracted as `D`. -/
lemma czTq_term_bound (w y : ℝ) (N q t : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hP : |czP w N q t - (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))| ≤ D * (1 + Real.log 2))
    (hS : |czS w N q t| ≤ D)
    (ht1 : 1 ≤ t) :
    |((ArithmeticFunction.moebius t : ℝ) / kap t)
          * ((Real.log (cY2 N q y / (t : ℝ)) - 1) * czP w N q t + czS w N q t)
        - (Real.pi ^ 2 / 6)
            * ((ArithmeticFunction.moebius t : ℝ) * (Real.log (cY2 N q y / (t : ℝ)) - 1)
                / (t : ℝ))|
      ≤ (D * (2 + Real.log 2)) * ((1 + |Real.log (cY2 N q y / (t : ℝ))|) / kap t) := by
  have h1log2 : (0 : ℝ) < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hkt : (0 : ℝ) < kap t := kap_pos t
  have hktne : kap t ≠ 0 := (kap_pos t).ne'
  have htne : (t : ℝ) ≠ 0 := ne_of_gt ht0
  have hmu : |(ArithmeticFunction.moebius t : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]; exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := t))
  have hfold : ((ArithmeticFunction.moebius t : ℝ) / kap t)
        * ((Real.log (cY2 N q y / (t : ℝ)) - 1) * czP w N q t + czS w N q t)
      - (Real.pi ^ 2 / 6)
          * ((ArithmeticFunction.moebius t : ℝ) * (Real.log (cY2 N q y / (t : ℝ)) - 1)
              / (t : ℝ))
      = ((ArithmeticFunction.moebius t : ℝ) / kap t)
        * ((Real.log (cY2 N q y / (t : ℝ)) - 1)
            * (czP w N q t - (Real.pi ^ 2 / 6) * (kap t / (t : ℝ)))
          + czS w N q t) := by
    field_simp
    ring
  rw [hfold]
  have hL : |Real.log (cY2 N q y / (t : ℝ)) - 1| ≤ 1 + |Real.log (cY2 N q y / (t : ℝ))| := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [le_abs_self (Real.log (cY2 N q y / (t : ℝ))),
      neg_le_abs (Real.log (cY2 N q y / (t : ℝ)))]
  have hAb : |(Real.log (cY2 N q y / (t : ℝ)) - 1)
        * (czP w N q t - (Real.pi ^ 2 / 6) * (kap t / (t : ℝ)))|
      ≤ (1 + |Real.log (cY2 N q y / (t : ℝ))|) * (D * (1 + Real.log 2)) := by
    rw [abs_mul]
    exact mul_le_mul hL hP (abs_nonneg _) (by positivity)
  have hBb : |czS w N q t| ≤ (1 + |Real.log (cY2 N q y / (t : ℝ))|) * D := by
    have h1le : (1 : ℝ) ≤ 1 + |Real.log (cY2 N q y / (t : ℝ))| := by
      have := abs_nonneg (Real.log (cY2 N q y / (t : ℝ)))
      linarith
    calc |czS w N q t| ≤ D := hS
      _ = 1 * D := by ring
      _ ≤ (1 + |Real.log (cY2 N q y / (t : ℝ))|) * D :=
          mul_le_mul_of_nonneg_right h1le hD
  have hsum : |(Real.log (cY2 N q y / (t : ℝ)) - 1)
        * (czP w N q t - (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))) + czS w N q t|
      ≤ (1 + |Real.log (cY2 N q y / (t : ℝ))|) * (D * (1 + Real.log 2)) + (1 + |Real.log (cY2 N q y / (t : ℝ))|) * D := by
    calc |_ + _| ≤ _ + _ := abs_add_le _ _
      _ ≤ _ := add_le_add hAb hBb
  have hfac : |(ArithmeticFunction.moebius t : ℝ) / kap t|
      * ((1 + |Real.log (cY2 N q y / (t : ℝ))|) * (D * (1 + Real.log 2)) + (1 + |Real.log (cY2 N q y / (t : ℝ))|) * D)
      ≤ (D * (2 + Real.log 2)) * ((1 + |Real.log (cY2 N q y / (t : ℝ))|) / kap t) := by
    rw [abs_div, abs_of_pos hkt, div_eq_mul_inv]
    have h1 : |(ArithmeticFunction.moebius t : ℝ)| * (kap t)⁻¹
        * ((1 + |Real.log (cY2 N q y / (t : ℝ))|) * (D * (1 + Real.log 2)) + (1 + |Real.log (cY2 N q y / (t : ℝ))|) * D)
        ≤ 1 * (kap t)⁻¹
        * ((1 + |Real.log (cY2 N q y / (t : ℝ))|) * (D * (1 + Real.log 2)) + (1 + |Real.log (cY2 N q y / (t : ℝ))|) * D) := by
      apply mul_le_mul_of_nonneg_right _
        (add_nonneg (mul_nonneg (by positivity) (mul_nonneg hD h1log2.le))
          (mul_nonneg (by positivity) hD))
      exact mul_le_mul_of_nonneg_right hmu (by positivity)
    refine h1.trans (le_of_eq ?_)
    ring
  calc |((ArithmeticFunction.moebius t : ℝ) / kap t)
        * ((Real.log (cY2 N q y / (t : ℝ)) - 1)
            * (czP w N q t - (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))) + czS w N q t)|
      = |(ArithmeticFunction.moebius t : ℝ) / kap t|
        * |(Real.log (cY2 N q y / (t : ℝ)) - 1)
            * (czP w N q t - (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))) + czS w N q t| := by
        rw [abs_mul]
    _ ≤ |(ArithmeticFunction.moebius t : ℝ) / kap t|
        * ((1 + |Real.log (cY2 N q y / (t : ℝ))|) * (D * (1 + Real.log 2)) + (1 + |Real.log (cY2 N q y / (t : ℝ))|) * D) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (D * (2 + Real.log 2)) * ((1 + |Real.log (cY2 N q y / (t : ℝ))|) / kap t) := hfac

end

end Work.ZeroDensity.Jutila.LzDiffAux

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila
open Work.ZeroDensity.Jutila.LzAux

noncomputable section

/-- The small-`R₁` case (`⌊Y₁⌋ = 1`): both `czTq` and `ζ(2)czG(Y₂)` are explicitly
`(log Y₁ − 1)(log Y₂ − 1) + 1` and `log Y₂ − 1`, so the difference is at most `4`. -/
lemma czTq_small {w y : ℝ} {N q : ℕ} (hw0 : 0 < w) (hy0 : 0 < y) (hwy : w ≤ y)
    (hsmall : czR w N q = 1) (hq : q ∈ Finset.Icc 1 (czQ y N)) :
    |czTq w y N q - (Real.pi ^ 2 / 6) * czG (cY2 N q y)| ≤ 5 := by
  have hY2ge1 := cY2_ge_one hy0 hq
  have hY21 := cY2_le_cY1 hw0 hy0 hwy hq
  have hY1ge1 : 1 ≤ cY1 N q w := le_trans hY2ge1 hY21
  have hR2ge1 : 1 ≤ czT y N q := (Nat.one_le_floor_iff _).mpr hY2ge1
  have hR2leR1 : czT y N q ≤ czR w N q := Nat.floor_mono hY21
  have hR2one : czT y N q = 1 := by omega
  have hY1lt2 : cY1 N q w < 2 := by
    have h2 : ⌊cY1 N q w⌋₊ < 2 := by rw [cY1_eq_czR, hsmall]; norm_num
    exact (Nat.floor_lt (by positivity : (0 : ℝ) ≤ cY1 N q w)).mp h2
  have hY2lt2 : cY2 N q y < 2 := lt_of_le_of_lt hY21 hY1lt2
  have hP1 : czP w N q 1 = Real.log (cY1 N q w) - 1 := by
    rw [czP, hsmall, Finset.Icc_self, Finset.sum_singleton,
      ArithmeticFunction.moebius_apply_one]
    simp [kap]
  have hS1 : czS w N q 1 = 1 := by
    rw [czS, hsmall, Finset.Icc_self, Finset.sum_singleton,
      ArithmeticFunction.moebius_apply_one]
    simp [kap]
  have hval : czTq w y N q
      = (Real.log (cY1 N q w) - 1) * (Real.log (cY2 N q y) - 1) + 1 := by
    rw [czTq, hR2one, Finset.Icc_self, Finset.sum_singleton, hP1, hS1,
      ArithmeticFunction.moebius_apply_one]
    simp [kap]
    ring
  have hvalG : czG (cY2 N q y) = Real.log (cY2 N q y) - 1 := by
    rw [czG, cY2_eq_czT, hR2one, Finset.Icc_self, Finset.sum_singleton,
      ArithmeticFunction.moebius_apply_one]
    norm_num
  rw [hval, hvalG]
  have hlogY1nn : 0 ≤ Real.log (cY1 N q w) := Real.log_nonneg hY1ge1
  have hlogY2nn : 0 ≤ Real.log (cY2 N q y) := Real.log_nonneg hY2ge1
  have hlogY1le : Real.log (cY1 N q w) ≤ Real.log 2 :=
    Real.log_le_log (by linarith) (le_of_lt hY1lt2)
  have hlogY2le : Real.log (cY2 N q y) ≤ Real.log 2 :=
    Real.log_le_log (by linarith) (le_of_lt hY2lt2)
  have hA : |Real.log (cY1 N q w) - 1| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hlogY1nn, hlogY1le, log_two_lt_one]
  have hB : |Real.log (cY2 N q y) - 1| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hlogY2nn, hlogY2le, log_two_lt_one]
  have hz : (Real.pi ^ 2 / 6) ≤ 3 := by nlinarith [Real.pi_gt_three, Real.pi_lt_four]
  have hzpos : 0 ≤ (Real.pi ^ 2 / 6) := by positivity
  have hrew : (Real.log (cY1 N q w) - 1) * (Real.log (cY2 N q y) - 1) + 1
        - (Real.pi ^ 2 / 6) * (Real.log (cY2 N q y) - 1)
      = (Real.log (cY2 N q y) - 1) * ((Real.log (cY1 N q w) - 1) - (Real.pi ^ 2 / 6)) + 1 := by
    ring
  rw [hrew]
  have h2 : |(Real.log (cY1 N q w) - 1) - (Real.pi ^ 2 / 6)| ≤ 1 + 3 := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [le_abs_self (Real.log (cY1 N q w) - 1), hzpos],
      by linarith [neg_le_abs (Real.log (cY1 N q w) - 1), hz]⟩
  calc |(Real.log (cY2 N q y) - 1) * ((Real.log (cY1 N q w) - 1) - (Real.pi ^ 2 / 6)) + 1|
      ≤ |(Real.log (cY2 N q y) - 1) * ((Real.log (cY1 N q w) - 1) - (Real.pi ^ 2 / 6))| + |(1 : ℝ)| :=
        abs_add_le _ _
    _ = |Real.log (cY2 N q y) - 1| * |(Real.log (cY1 N q w) - 1) - (Real.pi ^ 2 / 6)| + 1 := by
        rw [abs_mul, abs_one]
    _ ≤ 1 * (1 + 3) + 1 := by
        exact add_le_add (mul_le_mul hB h2 (abs_nonneg _) (by norm_num)) le_rfl
    _ = 5 := by norm_num

end

end Work.ZeroDensity.Jutila.LzDiffAux

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila
open Work.ZeroDensity.Jutila.LzAux

noncomputable section

/-- In the small case `⌊Y₁⌋ = 1` one has `Q/q < 2`. -/
lemma czQ_div_q_lt_two {w y : ℝ} {N q : ℕ} (hw0 : 0 < w) (hwy : w ≤ y) (hy0 : 0 < y)
    (hsmall : czR w N q = 1) (hq : q ∈ Finset.Icc 1 (czQ y N)) :
    ((czQ y N : ℕ) : ℝ) / (q : ℝ) < 2 := by
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hQ1 : 1 ≤ czQ y N := le_trans hq1 (Finset.mem_Icc.mp hq).2
  have hcY1pos : 0 < cY1 N q w := by
    have h1 : 1 ≤ cY1 N q w := by
      rw [← Nat.one_le_floor_iff (cY1 N q w), cY1_eq_czR, hsmall]
    linarith
  have hY1lt2 : cY1 N q w < 2 := by
    have h : ⌊cY1 N q w⌋₊ < 2 := by rw [cY1_eq_czR, hsmall]; norm_num
    exact (Nat.floor_lt (le_of_lt hcY1pos)).mp h
  have hNlt : (N : ℝ) < 2 * ((q : ℝ) * w) := by
    rw [cY1, div_lt_iff₀ (mul_pos hq0 hw0)] at hY1lt2
    exact hY1lt2
  have hQy : ((czQ y N : ℕ) : ℝ) * y ≤ (N : ℝ) := by
    have h := Nat.floor_le (show (0 : ℝ) ≤ (N : ℝ) / y by positivity)
    rwa [le_div_iff₀ hy0] at h
  rw [div_lt_iff₀ hq0]
  have hqw : (q : ℝ) * w ≤ (q : ℝ) * y := by nlinarith [hwy, hq0]
  nlinarith [hQy, hNlt, hqw, hy0]

/-- The large-`R₁` case of the per-`q` bound. -/
lemma czTq_large {w y : ℝ} {N q : ℕ} {C c Cs K : ℝ}
    (hC : 0 < C) (hCs : 0 < Cs) (hK : 0 < K)
    (hw1 : 1 ≤ w) (hwy : w ≤ y) (hy0 : 0 < y)
    (hq : q ∈ Finset.Icc 1 (czQ y N)) (hR1ge2 : 2 ≤ czR w N q)
    (hP : ∀ t : ℕ, Squarefree t → |czP w N q t - (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))|
        ≤ (C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
            * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ))))) * (1 + Real.log 2))
    (hS : ∀ t : ℕ, Squarefree t → |czS w N q t|
        ≤ C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
            * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ)))))
    (hEu : ∀ Y R : ℝ, 1 ≤ Y → 1 ≤ R → Y ≤ 2 * R →
        (1 + Real.log Y) ^ 2 * Real.exp (-(c * Real.sqrt (Real.log R))) ≤ K / (1 + (Real.log Y) ^ 2))
    (hSs : ∀ T : ℝ, 1 ≤ T → ∑ t ∈ (Finset.Icc 1 ⌊T⌋₊).filter (fun t => Squarefree t),
        ((∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) / kap t) * (1 + |Real.log (T / (t : ℝ))|)
        ≤ Cs * (1 + Real.log T) ^ 2) :
    |czTq w y N q - (Real.pi ^ 2 / 6) * czG (cY2 N q y)|
      ≤ (2 * (2 + Real.log 2) * C * Cs * K)
        * (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)) := by
  have hw0 : 0 < w := by linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hY2ge1 := cY2_ge_one hy0 hq
  have hY21 := cY2_le_cY1 hw0 hy0 hwy hq
  have hR2ge1 : 1 ≤ czT y N q := (Nat.one_le_floor_iff _).mpr hY2ge1
  have hcY1pos : 0 < cY1 N q w := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hY2ge1) hY21
  have hR1le : ((czR w N q : ℕ) : ℝ) ≤ cY1 N q w := Nat.floor_le (le_of_lt hcY1pos)
  have hY2le2R1 : cY2 N q y ≤ 2 * ((czR w N q : ℕ) : ℝ) := by
    have hlt : cY1 N q w < ((czR w N q : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hR1ge2R : (2 : ℝ) ≤ ((czR w N q : ℕ) : ℝ) := by exact_mod_cast hR1ge2
    linarith
  have hsplit : czTq w y N q - (Real.pi ^ 2 / 6) * czG (cY2 N q y)
      = ∑ t ∈ Finset.Icc 1 (czT y N q),
          (((ArithmeticFunction.moebius t : ℝ) / kap t)
              * ((Real.log (cY2 N q y / (t : ℝ)) - 1) * czP w N q t + czS w N q t)
            - (Real.pi ^ 2 / 6)
                * ((ArithmeticFunction.moebius t : ℝ) * (Real.log (cY2 N q y / (t : ℝ)) - 1)
                    / (t : ℝ))) := by
    rw [czTq, czG, cY2_eq_czT, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hsplit]
  have hterm : ∀ t ∈ Finset.Icc 1 (czT y N q),
      |((ArithmeticFunction.moebius t : ℝ) / kap t)
            * ((Real.log (cY2 N q y / (t : ℝ)) - 1) * czP w N q t + czS w N q t)
          - (Real.pi ^ 2 / 6)
              * ((ArithmeticFunction.moebius t : ℝ) * (Real.log (cY2 N q y / (t : ℝ)) - 1)
                  / (t : ℝ))|
        ≤ |((ArithmeticFunction.moebius t : ℤ) : ℝ)|
          * ((C * (2 + Real.log 2) * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
            * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ)))))
          * ((1 + |Real.log (cY2 N q y / (t : ℝ))|) / kap t)) := by
    intro t ht
    by_cases hsf : Squarefree t
    · have hDnn : (0 : ℝ) ≤ C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
          * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ)))) := by positivity
      have hb := czTq_term_bound w y N q t
        (C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
          * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ))))) hDnn (hP t hsf) (hS t hsf)
        (Finset.mem_Icc.mp ht).1
      have heq : (C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
            * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ))))) * (2 + Real.log 2)
          = C * (2 + Real.log 2) * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
            * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ)))) := by ring
      have hmu1 : |((ArithmeticFunction.moebius t : ℤ) : ℝ)| = 1 := by
        rw [← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree hsf]
        norm_num
      rw [heq] at hb
      simpa only [hmu1, one_mul] using hb
    · have hmu : (ArithmeticFunction.moebius t : ℝ) = 0 := by
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; norm_num
      have hzero : ((ArithmeticFunction.moebius t : ℝ) / kap t)
              * ((Real.log (cY2 N q y / (t : ℝ)) - 1) * czP w N q t + czS w N q t)
            - (Real.pi ^ 2 / 6)
                * ((ArithmeticFunction.moebius t : ℝ) * (Real.log (cY2 N q y / (t : ℝ)) - 1)
                    / (t : ℝ)) = 0 := by
        rw [hmu]; ring
      rw [hzero]
      have hmu0 : ((ArithmeticFunction.moebius t : ℤ) : ℝ) = 0 := by
        rw [hmu]
      simp [hmu0]
  calc |∑ t ∈ Finset.Icc 1 (czT y N q),
          (((ArithmeticFunction.moebius t : ℝ) / kap t)
              * ((Real.log (cY2 N q y / (t : ℝ)) - 1) * czP w N q t + czS w N q t)
            - (Real.pi ^ 2 / 6)
                * ((ArithmeticFunction.moebius t : ℝ) * (Real.log (cY2 N q y / (t : ℝ)) - 1)
                    / (t : ℝ)))|
      ≤ ∑ t ∈ Finset.Icc 1 (czT y N q),
          |((ArithmeticFunction.moebius t : ℝ) / kap t)
              * ((Real.log (cY2 N q y / (t : ℝ)) - 1) * czP w N q t + czS w N q t)
            - (Real.pi ^ 2 / 6)
                * ((ArithmeticFunction.moebius t : ℝ) * (Real.log (cY2 N q y / (t : ℝ)) - 1)
                    / (t : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.Icc 1 (czT y N q),
          |((ArithmeticFunction.moebius t : ℤ) : ℝ)|
          * ((C * (2 + Real.log 2) * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
            * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ)))))
          * ((1 + |Real.log (cY2 N q y / (t : ℝ))|) / kap t)) := Finset.sum_le_sum hterm
    _ = C * (2 + Real.log 2) * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ))))
          * ∑ t ∈ (Finset.Icc 1 (czT y N q)).filter (fun t => Squarefree t),
              ((∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) / kap t)
                * (1 + |Real.log (cY2 N q y / (t : ℝ))|) := by
        rw [Finset.mul_sum]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro t _
        by_cases hsf : Squarefree t
        · have hmu1 : |((ArithmeticFunction.moebius t : ℤ) : ℝ)| = 1 := by
            rw [← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree hsf]
            norm_num
          rw [if_pos hsf, hmu1]
          ring
        · have hmu0 : ((ArithmeticFunction.moebius t : ℤ) : ℝ) = 0 := by
            rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; norm_num
          rw [if_neg hsf, hmu0]
          ring
    _ ≤ C * (2 + Real.log 2) * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ))))
          * (Cs * (1 + Real.log (cY2 N q y)) ^ 2) := by
        have hE1 : (0 : ℝ) ≤ C * (2 + Real.log 2)
            * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ)))) := by positivity
        apply mul_le_mul_of_nonneg_left _ hE1
        have hh := hSs (cY2 N q y) hY2ge1
        rwa [cY2_eq_czT] at hh
    _ = C * (2 + Real.log 2) * Cs
          * ((1 + Real.log (cY2 N q y)) ^ 2
              * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ))))) := by ring
    _ ≤ C * (2 + Real.log 2) * Cs * (K / (1 + (Real.log (cY2 N q y)) ^ 2)) := by
        have hCnn : (0 : ℝ) ≤ C * (2 + Real.log 2) * Cs :=
          mul_nonneg (mul_nonneg hC.le (by linarith)) hCs.le
        exact mul_le_mul_of_nonneg_left
          (hEu (cY2 N q y) (czR w N q) hY2ge1 (by exact_mod_cast (by omega : 1 ≤ czR w N q)) hY2le2R1) hCnn
    _ ≤ C * (2 + Real.log 2) * Cs * K
          * (2 * (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2))) := by
        have h1' : K / (1 + (Real.log (cY2 N q y)) ^ 2)
            ≤ K * (2 * (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2))) := by
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_left (czY2_cmp hq hy0) hK.le
        have hCc : (0 : ℝ) ≤ C * (2 + Real.log 2) * Cs :=
          mul_nonneg (mul_nonneg hC.le (le_of_lt (by linarith : (0:ℝ) < 2 + Real.log 2))) hCs.le
        have h2' := mul_le_mul_of_nonneg_left h1' hCc
        calc C * (2 + Real.log 2) * Cs * (K / (1 + (Real.log (cY2 N q y)) ^ 2))
            ≤ C * (2 + Real.log 2) * Cs
              * (K * (2 * (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)))) := h2'
          _ = C * (2 + Real.log 2) * Cs * K
              * (2 * (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2))) := by ring
    _ = (2 * (2 + Real.log 2) * C * Cs * K)
          * (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)) := by ring

end

end Work.ZeroDensity.Jutila.LzDiffAux

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila
open Work.ZeroDensity.Jutila.LzAux

noncomputable section

/-- **The per-`q` bound with the extracted constants.** -/
lemma czTq_bound (h : KappaMertensInput) : ∃ C : ℝ, 0 < C ∧
    ∀ (w y : ℝ) (N q : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      q ∈ Finset.Icc 1 (czQ y N) →
      |czTq w y N q - (Real.pi ^ 2 / 6) * czG (cY2 N q y)|
        ≤ C * (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)) := by
  obtain ⟨C, c, hC, hc, h1, h2⟩ := h
  obtain ⟨Cs, hCs, hS⟩ := SigHalfLogSqfreeHere
  obtain ⟨K, hK, hE⟩ := ExpSqrtLogMulLogSq hc
  refine ⟨max 25 (2 * (2 + Real.log 2) * C * Cs * K), lt_max_of_lt_left (by norm_num),
    fun w y N q hw1 hwy hyN hq => ?_⟩
  have hy0 : 0 < y := by linarith
  have hthnn : (0 : ℝ) < 1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2) := by positivity
  by_cases hsmall : czR w N q = 1
  · have h5 := czTq_small (by linarith : (0 : ℝ) < w) hy0 hwy hsmall hq
    have hq0 : (0 : ℝ) < (q : ℝ) := by
      have : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      exact_mod_cast (by omega : 0 < q)
    have hQq1 : 1 ≤ ((czQ y N : ℕ) : ℝ) / (q : ℝ) := by
      rw [le_div_iff₀ hq0, one_mul]
      exact_mod_cast (Finset.mem_Icc.mp hq).2
    have hlt := czQ_div_q_lt_two (by linarith : (0 : ℝ) < w) hwy hy0 hsmall hq
    have hth : (1 : ℝ) / 2 ≤ 1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2) := by
      have hnn : 0 ≤ Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ)) := Real.log_nonneg hQq1
      have hlt1 : Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ)) < 1 := by
        have h := Real.log_lt_log (by positivity) hlt
        linarith [log_two_lt_one]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)]
      nlinarith [hnn, hlt1]
    calc |czTq w y N q - (Real.pi ^ 2 / 6) * czG (cY2 N q y)| ≤ 5 := h5
      _ ≤ max 25 (2 * (2 + Real.log 2) * C * Cs * K)
            * (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)) := by
          have h25 : (25 : ℝ) ≤ max 25 (2 * (2 + Real.log 2) * C * Cs * K) := le_max_left _ _
          nlinarith [h25, hth]
  · have hR1ge1 : 1 ≤ czR w N q := by
      have hY2ge1 := cY2_ge_one hy0 hq
      have hY21 := cY2_le_cY1 (by linarith : (0 : ℝ) < w) hy0 hwy hq
      exact (Nat.one_le_floor_iff _).mpr (le_trans hY2ge1 hY21)
    have hR1ge2 : 2 ≤ czR w N q := by omega
    have hP : ∀ t : ℕ, Squarefree t → |czP w N q t - (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))|
        ≤ (C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
            * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ))))) * (1 + Real.log 2) := by
      intro t hsf
      have h1t := h1 t (czR w N q) (cY1 N q w) hsf hR1ge2 (Nat.floor_le (by positivity))
      rw [← czP, ← czS] at h1t
      have h2t := h2 t (czR w N q) hsf hR1ge2
      rw [← czS] at h2t
      have hR1pos : (0 : ℝ) < ((czR w N q : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < czR w N q)
      have hratio_ge1 : 1 ≤ cY1 N q w / ((czR w N q : ℕ) : ℝ) := by
        rw [le_div_iff₀ hR1pos, one_mul]
        exact Nat.floor_le (by positivity)
      have hratio_le2 : cY1 N q w / ((czR w N q : ℕ) : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hR1pos]
        have hlt := Nat.lt_floor_add_one (cY1 N q w)
        rw [cY1_eq_czR] at hlt
        have hR1ge2R : (2 : ℝ) ≤ ((czR w N q : ℕ) : ℝ) := by exact_mod_cast hR1ge2
        linarith
      have hlogr_nn : 0 ≤ Real.log (cY1 N q w / ((czR w N q : ℕ) : ℝ)) := Real.log_nonneg hratio_ge1
      have hlogr_le : Real.log (cY1 N q w / ((czR w N q : ℕ) : ℝ)) ≤ Real.log 2 :=
        Real.log_le_log (by positivity) hratio_le2
      have hEnn : (0 : ℝ) ≤ C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
          * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ)))) := by positivity
      have hkey : czP w N q t - (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))
          = (czP w N q t - (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))
              - Real.log (cY1 N q w / ((czR w N q : ℕ) : ℝ)) * czS w N q t)
            + Real.log (cY1 N q w / ((czR w N q : ℕ) : ℝ)) * czS w N q t := by ring
      rw [hkey]
      have hBb : |Real.log (cY1 N q w / ((czR w N q : ℕ) : ℝ)) * czS w N q t| ≤ Real.log 2 *
          (C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
            * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ))))) := by
        rw [abs_mul, abs_of_nonneg hlogr_nn]
        calc Real.log (cY1 N q w / ((czR w N q : ℕ) : ℝ)) * |czS w N q t|
            ≤ Real.log (cY1 N q w / ((czR w N q : ℕ) : ℝ))
              * (C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
                * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ))))) :=
              mul_le_mul_of_nonneg_left h2t hlogr_nn
          _ ≤ Real.log 2 * (C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
                * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ))))) :=
              mul_le_mul_of_nonneg_right hlogr_le hEnn
      calc |(czP w N q t - (Real.pi ^ 2 / 6) * (kap t / (t : ℝ))
              - Real.log (cY1 N q w / ((czR w N q : ℕ) : ℝ)) * czS w N q t)
            + Real.log (cY1 N q w / ((czR w N q : ℕ) : ℝ)) * czS w N q t|
          ≤ _ + _ := abs_add_le _ _
        _ ≤ C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
              * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ))))
            + Real.log 2 * (C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
              * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ))))) := add_le_add h1t hBb
        _ = (C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
              * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ))))) * (1 + Real.log 2) := by ring
    have hS' : ∀ t : ℕ, Squarefree t → |czS w N q t|
        ≤ C * (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ))
            * Real.exp (-(c * Real.sqrt (Real.log (czR w N q : ℝ)))) := by
      intro t hsf
      have h := h2 t (czR w N q) hsf hR1ge2
      rwa [← czS] at h
    have hb := czTq_large (C := C) (c := c) (Cs := Cs) (K := K) hC hCs hK hw1 hwy hy0 hq hR1ge2
      hP hS' hE hS
    calc |czTq w y N q - (Real.pi ^ 2 / 6) * czG (cY2 N q y)|
        ≤ (2 * (2 + Real.log 2) * C * Cs * K)
          * (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)) := hb
      _ ≤ max 25 (2 * (2 + Real.log 2) * C * Cs * K)
          * (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hthnn.le

end

end Work.ZeroDensity.Jutila.LzDiffAux

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila
open Work.ZeroDensity.Jutila.LzAux

noncomputable section

/-- **The continuous model reproduces the leading term**, from the Mertens input. -/
theorem CzModelCont_of (h : KappaMertensInput) : ∃ C : ℝ, 0 < C ∧
    ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      |czModelCont w y N - (N : ℝ) * Real.log ((N : ℝ) / y)| ≤ C * (N : ℝ) := by
  obtain ⟨Ct, hCt, hTq⟩ := czTq_bound h
  obtain ⟨Cg, hCg, hG⟩ := czG_bound
  obtain ⟨Cinv, hCinv, hInv⟩ := SumInvLogSqBound
  obtain ⟨Ch, hCh, hH⟩ := harm_bound
  refine ⟨(Real.pi ^ 2 / 6)⁻¹ * Ct * Cinv + 2 * Cg * Cinv + Ch, by positivity, ?_⟩
  intro w y N hw1 hwy hyN
  have hy0 : 0 < y := by linarith
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (N : ℝ) := by linarith
    positivity
  have hw0 : w ≠ 0 := by linarith
  have hpi0 : (Real.pi ^ 2 / 6)⁻¹ * (Real.pi ^ 2 / 6) = 1 := by
    have : (Real.pi ^ 2 / 6) ≠ 0 := by positivity
    field_simp
  -- rewrite `czModelCont`
  have hMC : czModelCont w y N
      = (N : ℝ) * ((Real.pi ^ 2 / 6)⁻¹
          * ∑ q ∈ Finset.Icc 1 (czQ y N), czTq w y N q / (q : ℝ)) := by
    rw [czModelCont_eq w y N hw0 (ne_of_gt hy0) hN0, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hq0 : (q : ℝ) ≠ 0 := by
      have h1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      exact ne_of_gt (by exact_mod_cast (by omega : 0 < q))
    field_simp
  rw [hMC]
  rw [show (N : ℝ) * ((Real.pi ^ 2 / 6)⁻¹ * ∑ q ∈ Finset.Icc 1 (czQ y N), czTq w y N q / (q : ℝ))
        - (N : ℝ) * Real.log ((N : ℝ) / y)
      = (N : ℝ) * ((Real.pi ^ 2 / 6)⁻¹ * (∑ q ∈ Finset.Icc 1 (czQ y N), czTq w y N q / (q : ℝ))
          - Real.log ((N : ℝ) / y)) from by ring]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ))]
  have hbr : |(Real.pi ^ 2 / 6)⁻¹ * (∑ q ∈ Finset.Icc 1 (czQ y N), czTq w y N q / (q : ℝ))
        - Real.log ((N : ℝ) / y)|
      ≤ (Real.pi ^ 2 / 6)⁻¹ * Ct * Cinv + 2 * Cg * Cinv + Ch := by
    have hstep : (Real.pi ^ 2 / 6)⁻¹ * (∑ q ∈ Finset.Icc 1 (czQ y N), czTq w y N q / (q : ℝ))
          - Real.log ((N : ℝ) / y)
        = ((Real.pi ^ 2 / 6)⁻¹ * (∑ q ∈ Finset.Icc 1 (czQ y N), czTq w y N q / (q : ℝ))
            - (∑ q ∈ Finset.Icc 1 (czQ y N), (1 : ℝ) / (q : ℝ)))
          + ((∑ q ∈ Finset.Icc 1 (czQ y N), (1 : ℝ) / (q : ℝ)) - Real.log ((N : ℝ) / y)) := by
      ring
    rw [hstep]
    have hA : |(Real.pi ^ 2 / 6)⁻¹ * (∑ q ∈ Finset.Icc 1 (czQ y N), czTq w y N q / (q : ℝ))
          - (∑ q ∈ Finset.Icc 1 (czQ y N), (1 : ℝ) / (q : ℝ))|
        ≤ (Real.pi ^ 2 / 6)⁻¹ * Ct * Cinv + 2 * Cg * Cinv := by
      have hrew : (Real.pi ^ 2 / 6)⁻¹ * (∑ q ∈ Finset.Icc 1 (czQ y N), czTq w y N q / (q : ℝ))
            - (∑ q ∈ Finset.Icc 1 (czQ y N), (1 : ℝ) / (q : ℝ))
          = ∑ q ∈ Finset.Icc 1 (czQ y N),
              ((Real.pi ^ 2 / 6)⁻¹ * czTq w y N q - 1) / (q : ℝ) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro q hq
        have hq0 : (q : ℝ) ≠ 0 := by
          have h1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
          exact ne_of_gt (by exact_mod_cast (by omega : 0 < q))
        field_simp
      rw [hrew]
      have hper : ∀ q ∈ Finset.Icc 1 (czQ y N),
          |((Real.pi ^ 2 / 6)⁻¹ * czTq w y N q - 1) / (q : ℝ)|
            ≤ ((Real.pi ^ 2 / 6)⁻¹
                * (Ct * (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)))
                + Cg * (1 / (1 + (Real.log (cY2 N q y)) ^ 2))) / (q : ℝ) := by
        intro q hq
        have hq0 : (0 : ℝ) < (q : ℝ) := by
          have h1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
          exact_mod_cast (by omega : 0 < q)
        have hY2ge1 := cY2_ge_one hy0 hq
        have hczt := hTq w y N q hw1 hwy hyN hq
        have hczg := hG (cY2 N q y) hY2ge1
        have hpi0nn : (0 : ℝ) ≤ (Real.pi ^ 2 / 6)⁻¹ := by positivity
        have hdecomp : (Real.pi ^ 2 / 6)⁻¹ * czTq w y N q - 1
            = (Real.pi ^ 2 / 6)⁻¹ * (czTq w y N q - (Real.pi ^ 2 / 6) * czG (cY2 N q y))
              + (czG (cY2 N q y) - 1) := by
          have hkey2 : (Real.pi ^ 2 / 6)⁻¹ * ((Real.pi ^ 2 / 6) * czG (cY2 N q y))
              = czG (cY2 N q y) := by
            rw [← mul_assoc, hpi0, one_mul]
          rw [mul_sub, hkey2]; ring
        rw [abs_div, abs_of_pos hq0, hdecomp]
        have h1 : |(Real.pi ^ 2 / 6)⁻¹ * (czTq w y N q - (Real.pi ^ 2 / 6) * czG (cY2 N q y))
              + (czG (cY2 N q y) - 1)|
            ≤ (Real.pi ^ 2 / 6)⁻¹
                * (Ct * (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)))
              + Cg * (1 / (1 + (Real.log (cY2 N q y)) ^ 2)) := by
          calc |(Real.pi ^ 2 / 6)⁻¹ * (czTq w y N q - (Real.pi ^ 2 / 6) * czG (cY2 N q y))
                + (czG (cY2 N q y) - 1)|
              ≤ _ + _ := abs_add_le _ _
            _ ≤ (Real.pi ^ 2 / 6)⁻¹ * |czTq w y N q - (Real.pi ^ 2 / 6) * czG (cY2 N q y)|
                + |czG (cY2 N q y) - 1| := by
                rw [abs_mul, abs_of_nonneg hpi0nn]
            _ ≤ (Real.pi ^ 2 / 6)⁻¹
                  * (Ct * (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)))
                + Cg * (1 / (1 + (Real.log (cY2 N q y)) ^ 2)) :=
                add_le_add (mul_le_mul_of_nonneg_left hczt hpi0nn) hczg
        exact div_le_div_of_nonneg_right h1 hq0.le
      calc |∑ q ∈ Finset.Icc 1 (czQ y N), ((Real.pi ^ 2 / 6)⁻¹ * czTq w y N q - 1) / (q : ℝ)|
          ≤ ∑ q ∈ Finset.Icc 1 (czQ y N),
              |((Real.pi ^ 2 / 6)⁻¹ * czTq w y N q - 1) / (q : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ q ∈ Finset.Icc 1 (czQ y N),
              ((Real.pi ^ 2 / 6)⁻¹
                  * (Ct * (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)))
                + Cg * (1 / (1 + (Real.log (cY2 N q y)) ^ 2))) / (q : ℝ) :=
            Finset.sum_le_sum hper
        _ = ∑ q ∈ Finset.Icc 1 (czQ y N),
              ((Real.pi ^ 2 / 6)⁻¹ * Ct
                  * ((1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)) / (q : ℝ))
                + Cg * ((1 / (1 + (Real.log (cY2 N q y)) ^ 2)) / (q : ℝ))) := by
            apply Finset.sum_congr rfl
            intro q hq
            have hq0 : (q : ℝ) ≠ 0 := by
              have h1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
              exact ne_of_gt (by exact_mod_cast (by omega : 0 < q))
            field_simp
        _ = (Real.pi ^ 2 / 6)⁻¹ * Ct
              * (∑ q ∈ Finset.Icc 1 (czQ y N),
                  (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)) / (q : ℝ))
            + Cg * (∑ q ∈ Finset.Icc 1 (czQ y N),
                  (1 / (1 + (Real.log (cY2 N q y)) ^ 2)) / (q : ℝ)) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ (Real.pi ^ 2 / 6)⁻¹ * Ct * Cinv + 2 * Cg * Cinv := by
            have hT1eq : (∑ q ∈ Finset.Icc 1 (czQ y N),
                  (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)) / (q : ℝ))
                = ∑ q ∈ Finset.Icc 1 (czQ y N),
                  (1 / (q : ℝ)) * (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)) := by
              apply Finset.sum_congr rfl
              intro q hq
              ring
            have hQ1 : 1 ≤ czQ y N := czQ_pos (by rw [le_div_iff₀ hy0, one_mul]; linarith)
            have hT1 : (∑ q ∈ Finset.Icc 1 (czQ y N),
                  (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)) / (q : ℝ)) ≤ Cinv := by
              rw [hT1eq]; exact hInv (czQ y N) hQ1
            have hT2 : (∑ q ∈ Finset.Icc 1 (czQ y N),
                  (1 / (1 + (Real.log (cY2 N q y)) ^ 2)) / (q : ℝ)) ≤ 2 * Cinv := by
              have h2 : (∑ q ∈ Finset.Icc 1 (czQ y N),
                    (1 / (1 + (Real.log (cY2 N q y)) ^ 2)) / (q : ℝ))
                  ≤ ∑ q ∈ Finset.Icc 1 (czQ y N),
                      (2 * (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2))) / (q : ℝ) := by
                apply Finset.sum_le_sum
                intro q hq
                have hq0 : (0 : ℝ) < (q : ℝ) := by
                  have h1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
                  exact_mod_cast (by omega : 0 < q)
                exact div_le_div_of_nonneg_right (czY2_cmp hq hy0) hq0.le
              calc (∑ q ∈ Finset.Icc 1 (czQ y N),
                    (1 / (1 + (Real.log (cY2 N q y)) ^ 2)) / (q : ℝ))
                  ≤ ∑ q ∈ Finset.Icc 1 (czQ y N),
                      (2 * (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2))) / (q : ℝ) := h2
                _ = 2 * (∑ q ∈ Finset.Icc 1 (czQ y N),
                      (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)) / (q : ℝ)) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro q hq
                    ring
                _ ≤ 2 * Cinv := mul_le_mul_of_nonneg_left hT1 (by norm_num)
            calc (Real.pi ^ 2 / 6)⁻¹ * Ct
                  * (∑ q ∈ Finset.Icc 1 (czQ y N),
                      (1 / (1 + (Real.log (((czQ y N : ℕ) : ℝ) / (q : ℝ))) ^ 2)) / (q : ℝ))
                + Cg * (∑ q ∈ Finset.Icc 1 (czQ y N),
                      (1 / (1 + (Real.log (cY2 N q y)) ^ 2)) / (q : ℝ))
                ≤ (Real.pi ^ 2 / 6)⁻¹ * Ct * Cinv + Cg * (2 * Cinv) := by
                  apply add_le_add
                  · exact mul_le_mul_of_nonneg_left hT1 (by positivity)
                  · exact mul_le_mul_of_nonneg_left hT2 hCg.le
              _ = (Real.pi ^ 2 / 6)⁻¹ * Ct * Cinv + 2 * Cg * Cinv := by ring
    have hB := hH N y (by linarith) hyN
    calc |(Real.pi ^ 2 / 6)⁻¹ * (∑ q ∈ Finset.Icc 1 (czQ y N), czTq w y N q / (q : ℝ))
            - (∑ q ∈ Finset.Icc 1 (czQ y N), (1 : ℝ) / (q : ℝ))
          + ((∑ q ∈ Finset.Icc 1 (czQ y N), (1 : ℝ) / (q : ℝ)) - Real.log ((N : ℝ) / y))|
        ≤ _ + _ := abs_add_le _ _
      _ ≤ ((Real.pi ^ 2 / 6)⁻¹ * Ct * Cinv + 2 * Cg * Cinv) + Ch := add_le_add hA hB
      _ = (Real.pi ^ 2 / 6)⁻¹ * Ct * Cinv + 2 * Cg * Cinv + Ch := by ring
  calc (N : ℝ) * |(Real.pi ^ 2 / 6)⁻¹ * (∑ q ∈ Finset.Icc 1 (czQ y N), czTq w y N q / (q : ℝ))
          - Real.log ((N : ℝ) / y)|
      ≤ (N : ℝ) * ((Real.pi ^ 2 / 6)⁻¹ * Ct * Cinv + 2 * Cg * Cinv + Ch) :=
        mul_le_mul_of_nonneg_left hbr (by positivity)
    _ = ((Real.pi ^ 2 / 6)⁻¹ * Ct * Cinv + 2 * Cg * Cinv + Ch) * (N : ℝ) := by ring

end

end Work.ZeroDensity.Jutila.LzDiffAux

namespace Work.ZeroDensity.Jutila.LzDiffAux

theorem CzModelContHere : ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
    |Work.ZeroDensity.Jutila.czModelCont w y N - (N : ℝ) * Real.log ((N : ℝ) / y)| ≤ C * (N : ℝ) :=
  CzModelCont_of KappaMertensHere

end Work.ZeroDensity.Jutila.LzDiffAux
