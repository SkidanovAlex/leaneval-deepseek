import Mathlib
import Submission.Work.ZeroDensity.Ingham.AfeProof.afeAux
import Submission.Work.ZeroDensity.Ingham.AfeProof.afeResonanceAux
import Submission.Work.ZeroDensity.Ingham.AfeProof.afeC0NormCriticalLine
import Submission.Work.ZeroDensity.Ingham.AfeSelf.Defs
import Submission.Work.ZeroDensity.Ingham.AfeSelf.sinIntegralLowerSharp
import Submission.Work.ZeroDensity.Zeta.sinIntegralTailBalanced
import Submission.Work.ZeroDensity.Zeta.sinTailUniform
import Submission.Work.ZeroDensity.Zeta.sinMellinSplitBalanced
import Submission.Work.ZeroDensity.Zeta.balAux.harmMain
import Submission.Work.ZeroDensity.Zeta.balAux.harmTailPtwise
import Submission.Work.ZeroDensity.Zeta.balAux.harmTailTelescope
import Submission.Work.ZeroDensity.Zeta.balAux.harmTailNumeric

/-!
# The resonance sum bound

`afeResonanceSumBound` states that the sawtooth–Fourier sum `afeTsum t` and the
resonance constant times the dual truncated Dirichlet sum `afeC0 (cls t) * afeDual t`
differ by `O(1/t)`.

The sawtooth sum is split at the resonance `y = t/(2πN)`, `N = afeNt t`:

* the *main* part `i < ⌊y⌋ - 1` is converted, term by term, into `c₀·(i+1)^{s-1}`
  plus an error controlled by `sinIntegralLowerSharp` (the Kummer bound), and summed
  with `harmMain`;
* the *boundary* term `i = ⌊y⌋ - 1` is controlled by the resonance constant bound and
  the uniform sine-tail bound;
* the *far tail* `i ≥ ⌊y⌋` is controlled by `sinIntegralTailBalanced` and the harmonic
  tail estimate.

The last ingredient, the harmonic tail estimate, is derived here from
`harmTailPtwise`, `harmTailTelescope` and `harmTailNumeric` (whose own prover left a
`sorry`), so that nothing below depends on an unproved statement.
-/

namespace Work.ZeroDensity.Ingham.AfeProof

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-! ## Elementary reindexing and `rpow` manipulations -/

/-- Reindex a sum over `range Y` of `f(i+1)` as a sum over `Icc 1 Y`. -/
private lemma sum_range_one_add {M : Type*} [AddCommMonoid M] (f : ℕ → M) (Y : ℕ) :
    ∑ i ∈ Finset.range Y, f (i + 1) = ∑ n ∈ Finset.Icc 1 Y, f n := by
  have h1 : ∑ i ∈ Finset.range Y, f (i + 1) = ∑ i ∈ Finset.range Y, f (1 + i) :=
    Finset.sum_congr rfl (fun i _ => by rw [Nat.add_comm])
  rw [h1]
  have hIcc : Finset.Icc 1 Y = Finset.Ico 1 (Y + 1) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc]
  have h := Finset.sum_Ico_eq_sum_range f 1 (Y + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [← h]

/-- Elementary `rpow` recombination for the main-sum term. -/
private lemma rpow_combine {P : ℝ} (hP : 0 < P) {n : ℝ} (hn : 0 < n) (u c : ℝ) :
    n ^ (-(1 / 2 : ℝ)) * (c * (P * n) ^ (-(1 / 2 : ℝ)) / (P * u))
      = c * P ^ (-(3 / 2 : ℝ)) * (1 / (n * u)) := by
  have hn2 : n ^ (-(1 / 2 : ℝ)) * n ^ (-(1 / 2 : ℝ)) = n⁻¹ := by
    rw [← Real.rpow_add hn, show (-(1 / 2 : ℝ)) + (-(1 / 2 : ℝ)) = -1 by norm_num,
      Real.rpow_neg_one]
  have hP2 : P ^ (-(1 / 2 : ℝ)) * P⁻¹ = P ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one P, ← Real.rpow_add hP,
      show (-(1 / 2 : ℝ)) + -1 = -(3 / 2 : ℝ) by norm_num]
  rcases eq_or_ne u 0 with hu | hu
  · simp [hu]
  · rw [Real.mul_rpow (le_of_lt hP) (le_of_lt hn)]
    have hkey : n ^ (-(1 / 2 : ℝ)) * (c * (P ^ (-(1 / 2 : ℝ)) * n ^ (-(1 / 2 : ℝ))) / (P * u))
        = c * (P ^ (-(1 / 2 : ℝ)) * P⁻¹) * (n ^ (-(1 / 2 : ℝ)) * n ^ (-(1 / 2 : ℝ))) * u⁻¹ := by
      field_simp
    rw [hkey, hn2, hP2, one_div, mul_inv]
    ring

/-- Elementary `rpow` recombination for the second tail term. -/
private lemma rpow_combine2 {P : ℝ} (hP : 0 < P) {n : ℝ} (hn : 0 < n) (c : ℝ) :
    n ^ (-(1 / 2 : ℝ)) * (c * (P * n) ^ (-(3 / 2 : ℝ))) = c * P ^ (-(3 / 2 : ℝ)) * (1 / n ^ 2) := by
  have hn2 : n ^ (-(1 / 2 : ℝ)) * n ^ (-(3 / 2 : ℝ)) = (n ^ 2)⁻¹ := by
    rw [← Real.rpow_add hn, show (-(1 / 2 : ℝ)) + (-(3 / 2 : ℝ)) = -(2 : ℝ) by norm_num,
      Real.rpow_neg hn.le]
    norm_num
  rw [Real.mul_rpow (le_of_lt hP) (le_of_lt hn),
    show n ^ (-(1 / 2 : ℝ)) * (c * (P ^ (-(3 / 2 : ℝ)) * n ^ (-(3 / 2 : ℝ))))
      = c * P ^ (-(3 / 2 : ℝ)) * (n ^ (-(1 / 2 : ℝ)) * n ^ (-(3 / 2 : ℝ))) by ring, hn2, one_div]

/-! ## The resonance constant on the critical line -/

/-- `‖c₀(1/2+it)‖ ≤ 4/t` for `t ≥ 10⁶`. -/
lemma afeC0_bound {t : ℝ} (ht : 1000000 ≤ t) : ‖afeC0 (cls t)‖ ≤ 4 / t := by
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have htpos : (0 : ℝ) < t := by linarith
  rw [norm_afeC0_cls t]
  have hclt : t ≤ ‖cls t‖ := by
    rw [norm_cls, Real.le_sqrt (by linarith) (by positivity)]
    nlinarith
  have hspos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hstep : Real.pi / (Real.sqrt (2 * Real.pi) * ‖cls t‖)
      ≤ Real.pi / (Real.sqrt (2 * Real.pi) * t) := by
    apply div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) (by positivity)
    nlinarith [hclt]
  refine hstep.trans ?_
  rw [div_le_div_iff₀ (mul_pos hspos htpos) htpos]
  have h2 : (8 : ℝ) ≤ 4 * Real.sqrt (2 * Real.pi) := by
    have h : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith [Real.pi_gt_three]
    linarith
  nlinarith [Real.pi_lt_four]

/-! ## Splitting `afeTerm` -/

/-- `afeTerm` with the scaling constant `afeP t` made explicit. -/
lemma afeTerm_eq (t : ℝ) (k : ℕ) :
    afeTerm t k = (((k : ℝ) + 1 : ℂ)) ^ (cls t - 1) * afeT (cls t) (afeP t * ((k : ℝ) + 1)) := by
  rw [afeTerm, afeP]
  congr 2
  ring

/-- The split `afeT s A = c₀(s) - afeL s A` for `1 ≤ A`. -/
lemma afeT_eq_c0_sub {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {A : ℝ} (hA : 1 ≤ A) :
    afeT s A = afeC0 s - afeL s A :=
  Work.ZeroDensity.Zeta.sinMellinSplitBalanced hs0 hs1 hA

/-- `‖afeT (cls t) A‖ ≤ 8 A^{-1/2}/(t - A)` for `1 ≤ A < t`. -/
lemma norm_afeL_le {t A : ℝ} (hA : 1 ≤ A) (hAt : A < t) (ht : 0 ≤ t) :
    ‖afeL (cls t) A‖ ≤ 8 * A ^ (-(1 / 2 : ℝ)) / (t - A) := by
  have hs0 : 0 < (cls t).re := cls_re_pos t
  have h := Work.ZeroDensity.Ingham.AfeSelf.sinIntegralLowerSharp (s := cls t) hs0 hA
    (by rw [cls_im, abs_of_nonneg ht]; exact hAt)
  rw [cls_re] at h
  have him : |(cls t).im| = t := by rw [cls_im, abs_of_nonneg ht]
  rw [him] at h
  exact h

/-- `‖afeT (cls t) A‖ ≤ 2 A^{-1/2}/(A - t) + 2 A^{-3/2}` for `t < A`. -/
lemma norm_afeT_le_tail {t A : ℝ} (hA : 1 ≤ A) (hAt : t < A) (ht : 0 ≤ t) :
    ‖afeT (cls t) A‖ ≤ 2 * A ^ (-(1 / 2 : ℝ)) / (A - t) + 2 * A ^ (-(1 / 2 : ℝ) - 1) := by
  have hs0 : 0 < (cls t).re := cls_re_pos t
  have h := Work.ZeroDensity.Zeta.sinIntegralTailBalanced (s := cls t) hs0 hA
    (by rw [cls_im, abs_of_nonneg ht]; exact hAt)
  rw [cls_re] at h
  have him : |(cls t).im| = t := by rw [cls_im, abs_of_nonneg ht]
  rw [him] at h
  exact h

/-! ## Summability of the sawtooth–Fourier sum -/

lemma afeTerm_summable (t : ℝ) (ht : 1000000 ≤ t) :
    Summable (fun k : ℕ => afeTerm t k) := by
  have htpos : (0 : ℝ) < t := by linarith
  have hPpos : (0 : ℝ) < afeP t := afeP_pos t
  have hypos : 0 < afeY t := afeY_pos ht
  have hymul : afeY t * afeP t = t := afeY_mul ht
  have hg0 : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (-(2 : ℝ))) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (show (-(2 : ℝ)) < -1 by norm_num))
    simpa [Nat.cast_add, Nat.cast_one] using this
  have key : ∀ k : ℕ, ((k : ℝ) + 1) ^ (-(2 : ℝ)) = (1 : ℝ) / (((k : ℝ) + 1) ^ 2) := by
    intro k
    rw [one_div, Real.rpow_neg (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity) 2]
    norm_num
  have hg1 : Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) ^ 2)) := hg0.congr key
  have hg : Summable (fun k : ℕ => 6 * (afeP t) ^ (-(3 / 2 : ℝ)) * (1 / (((k : ℝ) + 1) ^ 2))) :=
    Summable.mul_left _ hg1
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Nat.cofinite_eq_atTop]
  refine Filter.eventually_atTop.mpr ⟨2 * ⌈afeY t⌉₊, fun k hk => ?_⟩
  have hky : (k : ℝ) ≥ 2 * (⌈afeY t⌉₊ : ℝ) := by exact_mod_cast hk
  have hceil : afeY t ≤ (⌈afeY t⌉₊ : ℝ) := Nat.le_ceil _
  have hn2y : 2 * afeY t < ((k : ℝ) + 1) := by linarith
  have hAt2 : 2 * t < afeP t * ((k : ℝ) + 1) := by
    have h2t : (2 : ℝ) * t = afeP t * (2 * afeY t) := by
      rw [show afeP t * (2 * afeY t) = 2 * (afeY t * afeP t) by ring, hymul]
    rw [h2t]
    exact mul_lt_mul_of_pos_left hn2y hPpos
  have hApos : 0 < afeP t * ((k : ℝ) + 1) := mul_pos hPpos (by positivity)
  have hA1 : 1 ≤ afeP t * ((k : ℝ) + 1) := by
    have h1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    nlinarith [afeP_ge t, h1]
  have hb := norm_afeT_le_tail (t := t) (A := afeP t * ((k : ℝ) + 1)) hA1
    (by linarith) (le_of_lt htpos)
  have hexp : (-(1 / 2 : ℝ) - 1) = (-(3 / 2 : ℝ)) := by norm_num
  rw [hexp] at hb
  have hsub_pos : 0 < afeP t * ((k : ℝ) + 1) - t := by linarith
  have hge : (afeP t * ((k : ℝ) + 1) - t) ≥ (afeP t * ((k : ℝ) + 1)) / 2 := by linarith
  have hterm1 : 2 * (afeP t * ((k : ℝ) + 1)) ^ (-(1 / 2 : ℝ)) / (afeP t * ((k : ℝ) + 1) - t)
      ≤ 4 * (afeP t * ((k : ℝ) + 1)) ^ (-(3 / 2 : ℝ)) := by
    have hA3 : (4 : ℝ) * (afeP t * ((k : ℝ) + 1)) ^ (-(3 / 2 : ℝ))
        = 4 * (afeP t * ((k : ℝ) + 1)) ^ (-(1 / 2 : ℝ)) / (afeP t * ((k : ℝ) + 1)) := by
      rw [show (-(3 / 2 : ℝ)) = (-(1 / 2 : ℝ)) + (-1) by norm_num, Real.rpow_add hApos,
        Real.rpow_neg_one, div_eq_mul_inv]
      ring
    rw [hA3, div_le_div_iff₀ hsub_pos hApos]
    have hp1 : (0 : ℝ) < (afeP t * ((k : ℝ) + 1)) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hApos _
    nlinarith [hge, hp1]
  have hb2 : ‖afeT (cls t) (afeP t * ((k : ℝ) + 1))‖ ≤ 6 * (afeP t * ((k : ℝ) + 1)) ^ (-(3 / 2 : ℝ)) := by
    calc ‖afeT (cls t) (afeP t * ((k : ℝ) + 1))‖
        ≤ 2 * (afeP t * ((k : ℝ) + 1)) ^ (-(1 / 2 : ℝ)) / (afeP t * ((k : ℝ) + 1) - t)
          + 2 * (afeP t * ((k : ℝ) + 1)) ^ (-(3 / 2 : ℝ)) := hb
      _ ≤ 4 * (afeP t * ((k : ℝ) + 1)) ^ (-(3 / 2 : ℝ))
          + 2 * (afeP t * ((k : ℝ) + 1)) ^ (-(3 / 2 : ℝ)) := add_le_add hterm1 le_rfl
      _ = 6 * (afeP t * ((k : ℝ) + 1)) ^ (-(3 / 2 : ℝ)) := by ring
  rw [afeTerm_eq, norm_mul, norm_idx_pow]
  calc ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ)) * ‖afeT (cls t) (afeP t * ((k : ℝ) + 1))‖
      ≤ ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ)) * (6 * (afeP t * ((k : ℝ) + 1)) ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hb2 (Real.rpow_nonneg (by positivity) _)
    _ = 6 * (afeP t) ^ (-(3 / 2 : ℝ)) * (1 / (((k : ℝ) + 1) ^ 2)) := by
        rw [rpow_combine2 hPpos (by positivity : (0 : ℝ) < (k : ℝ) + 1) 6]

/-! ## The main part -/

lemma afeMain_bound (t : ℝ) (ht : 1000000 ≤ t) :
    ‖∑ i ∈ Finset.range (afeYc t),
        (afeTerm t i - afeC0 (cls t) * (((i : ℝ) + 1 : ℂ)) ^ (cls t - 1))‖ ≤ 320 / t := by
  have hs0 : 0 < (cls t).re := cls_re_pos t
  have hs1 : (cls t).re < 1 := cls_re_lt_one t
  have hPpos : 0 < afeP t := afeP_pos t
  have hy3 : 3 ≤ afeY t := afeY_ge ht
  have hypos : 0 < afeY t := afeY_pos ht
  have hymul : afeY t * afeP t = t := afeY_mul ht
  have htpos : 0 < t := by linarith
  have hYc : afeYc t = ⌊afeY t⌋₊ - 1 := afeYc_eq t
  have hA1 : ∀ i : ℕ, 1 ≤ afeP t * ((i : ℝ) + 1) := by
    intro i
    have h1 : (1 : ℝ) ≤ (i : ℝ) + 1 := by
      have h0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    nlinarith [afeP_ge t, h1]
  have hterm : ∀ i ∈ Finset.range (afeYc t),
      afeTerm t i - afeC0 (cls t) * (((i : ℝ) + 1 : ℂ)) ^ (cls t - 1)
        = - ((((i : ℝ) + 1 : ℂ)) ^ (cls t - 1)) * afeL (cls t) (afeP t * ((i : ℝ) + 1)) := by
    intro i hi
    rw [afeTerm_eq, afeT_eq_c0_sub hs0 hs1 (hA1 i)]
    ring
  have hcongr : (∑ i ∈ Finset.range (afeYc t),
        (afeTerm t i - afeC0 (cls t) * (((i : ℝ) + 1 : ℂ)) ^ (cls t - 1)))
      = ∑ i ∈ Finset.range (afeYc t),
          - ((((i : ℝ) + 1 : ℂ)) ^ (cls t - 1)) * afeL (cls t) (afeP t * ((i : ℝ) + 1)) :=
    Finset.sum_congr rfl hterm
  rw [hcongr]
  have hb1 : ‖∑ i ∈ Finset.range (afeYc t),
        - ((((i : ℝ) + 1 : ℂ)) ^ (cls t - 1)) * afeL (cls t) (afeP t * ((i : ℝ) + 1))‖
      ≤ 8 * (afeP t) ^ (-(3 / 2 : ℝ)) * ∑ i ∈ Finset.range (afeYc t),
          1 / (((i : ℝ) + 1) * (afeY t - ((i : ℝ) + 1))) := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hilt := afeYc_lt ht i hi
    have hymul' : afeP t * afeY t = t := by rw [mul_comm]; exact hymul
    have hAt : afeP t * ((i : ℝ) + 1) < t := by
      have h := mul_lt_mul_of_pos_left hilt hPpos
      rwa [hymul'] at h
    have hb := norm_afeL_le (t := t) (A := afeP t * ((i : ℝ) + 1)) (hA1 i) hAt (le_of_lt htpos)
    rw [neg_mul, norm_neg, norm_mul, norm_idx_pow]
    have htu : t - afeP t * ((i : ℝ) + 1) = afeP t * (afeY t - ((i : ℝ) + 1)) := by
      have h1 : afeP t * (afeY t - ((i : ℝ) + 1)) = afeP t * afeY t - afeP t * ((i : ℝ) + 1) := by
        ring
      rw [h1, mul_comm (afeP t) (afeY t), hymul]
    calc ((i : ℝ) + 1) ^ (-(1 / 2 : ℝ)) * ‖afeL (cls t) (afeP t * ((i : ℝ) + 1))‖
        ≤ ((i : ℝ) + 1) ^ (-(1 / 2 : ℝ)) *
            (8 * (afeP t * ((i : ℝ) + 1)) ^ (-(1 / 2 : ℝ)) / (t - afeP t * ((i : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (by positivity) (-(1 / 2 : ℝ)))
      _ = ((i : ℝ) + 1) ^ (-(1 / 2 : ℝ)) *
            (8 * (afeP t * ((i : ℝ) + 1)) ^ (-(1 / 2 : ℝ)) / (afeP t * (afeY t - ((i : ℝ) + 1)))) := by
          rw [htu]
      _ = 8 * (afeP t) ^ (-(3 / 2 : ℝ)) * (1 / (((i : ℝ) + 1) * (afeY t - ((i : ℝ) + 1)))) :=
          rpow_combine hPpos (by positivity : (0 : ℝ) < (i : ℝ) + 1) _ 8
  have hb2 : (∑ i ∈ Finset.range (afeYc t), 1 / (((i : ℝ) + 1) * (afeY t - ((i : ℝ) + 1))))
      = ∑ n ∈ Finset.Icc 1 (afeYc t), 1 / ((n : ℝ) * (afeY t - (n : ℝ))) := by
    rw [← sum_range_one_add (fun n => (1 : ℝ) / ((n : ℝ) * (afeY t - (n : ℝ)))) (afeYc t)]
    apply Finset.sum_congr rfl
    intro i hi
    have h1 : (((i + 1 : ℕ)) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    rw [h1]
  have hb3 : (∑ n ∈ Finset.Icc 1 (afeYc t), 1 / ((n : ℝ) * (afeY t - (n : ℝ))))
      ≤ 4 * (Real.log (afeY t) + 1) / afeY t := by
    rw [hYc]
    exact Work.ZeroDensity.Zeta.balAux.harmMain (afeY t) hy3
  refine le_trans hb1 ?_
  rw [hb2]
  refine le_trans (mul_le_mul_of_nonneg_left hb3 (by positivity)) ?_
  have hlog' : Real.log (afeY t) + 1 ≤ 10 * (afeP t) ^ (1 / 2 : ℝ) := logY_bound ht
  rw [le_div_iff₀ htpos]
  have hdiv : t / afeY t = afeP t := by
    rw [div_eq_iff hypos.ne', mul_comm]; exact hymul.symm
  have hsimp : 8 * (afeP t) ^ (-(3 / 2 : ℝ)) * (4 * (Real.log (afeY t) + 1) / afeY t) * t
      = 32 * (Real.log (afeY t) + 1) * (afeP t) ^ (-(1 / 2 : ℝ)) := by
    rw [show (-(3 / 2 : ℝ)) = (-(1 / 2 : ℝ)) + (-1) by norm_num, Real.rpow_add hPpos,
      Real.rpow_neg_one]
    rw [show 8 * ((afeP t) ^ (-(1 / 2 : ℝ)) * (afeP t)⁻¹)
          * (4 * (Real.log (afeY t) + 1) / afeY t) * t
        = 32 * (Real.log (afeY t) + 1) * (t / afeY t)
          * ((afeP t) ^ (-(1 / 2 : ℝ)) * (afeP t)⁻¹) by ring, hdiv]
    rw [show (32 * (Real.log (afeY t) + 1) * afeP t
          * ((afeP t) ^ (-(1 / 2 : ℝ)) * (afeP t)⁻¹))
        = 32 * (Real.log (afeY t) + 1)
          * ((afeP t) ^ (-(1 / 2 : ℝ)) * (afeP t * (afeP t)⁻¹)) by ring,
      mul_inv_cancel₀ hPpos.ne', mul_one]
  rw [hsimp]
  have hPmul : (afeP t) ^ (1 / 2 : ℝ) * (afeP t) ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hPpos]; norm_num
  have hstep1 : 32 * (Real.log (afeY t) + 1) * (afeP t) ^ (-(1 / 2 : ℝ))
      ≤ 32 * (10 * (afeP t) ^ (1 / 2 : ℝ)) * (afeP t) ^ (-(1 / 2 : ℝ)) := by
    apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog' (by norm_num))
    exact Real.rpow_nonneg (le_of_lt hPpos) _
  have hstep2 : 32 * (10 * (afeP t) ^ (1 / 2 : ℝ)) * (afeP t) ^ (-(1 / 2 : ℝ)) = 320 := by
    rw [show (32 : ℝ) * (10 * (afeP t) ^ (1 / 2 : ℝ)) * (afeP t) ^ (-(1 / 2 : ℝ))
        = 320 * ((afeP t) ^ (1 / 2 : ℝ) * (afeP t) ^ (-(1 / 2 : ℝ))) by ring, hPmul, mul_one]
  linarith [hstep1, hstep2]

/-! ## The harmonic tail estimate -/

/-- Summability of `k ↦ 1/(k+1)²`. -/
private lemma summable_inv_sq_succ : Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) ^ 2)) := by
  have hg0 : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (-(2 : ℝ))) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (show (-(2 : ℝ)) < -1 by norm_num))
    simpa [Nat.cast_add, Nat.cast_one] using this
  refine hg0.congr ?_
  intro k
  rw [one_div, Real.rpow_neg (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity) 2]
  norm_num

/-- The summand of the harmonic tail estimate. -/
private def harmTailG (y : ℝ) (k : ℕ) : ℝ :=
  1 / (((k + ⌊y⌋₊ + 2 : ℕ) : ℝ) * (((k + ⌊y⌋₊ + 2 : ℕ) : ℝ) - y))
    + 1 / ((((k + ⌊y⌋₊ + 2 : ℕ) : ℝ)) ^ 2)

private lemma harmTailG_pos_arg {y : ℝ} (hy : 3 ≤ y) (k : ℕ) :
    0 < ((k + ⌊y⌋₊ + 2 : ℕ) : ℝ) - y := by
  have hfl := Nat.lt_floor_add_one y
  push_cast
  linarith

private lemma harmTailG_nonneg {y : ℝ} (hy : 3 ≤ y) (k : ℕ) : 0 ≤ harmTailG y k := by
  have h1 : (0 : ℝ) < ((k + ⌊y⌋₊ + 2 : ℕ) : ℝ) := by positivity
  have h2 := harmTailG_pos_arg hy k
  simp only [harmTailG]
  positivity

private lemma harmTailG_summable {y : ℝ} (hy : 3 ≤ y) : Summable (harmTailG y) := by
  refine Summable.of_nonneg_of_le (harmTailG_nonneg hy) (fun k => ?_)
    (summable_inv_sq_succ.mul_left (4 : ℝ))
  have hpt := Work.ZeroDensity.Zeta.balAux.harmTailPtwise y hy k
  simp only [harmTailG] at hpt ⊢
  refine hpt.trans ?_
  simp only [Nat.cast_add, Nat.cast_one] at ⊢
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hkn : (1 : ℝ) ≤ (k : ℝ) + (⌊y⌋₊ : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h1 : (0 : ℝ) ≤ (⌊y⌋₊ : ℝ) := Nat.cast_nonneg _
    linarith
  have hA : (0 : ℝ) < ((k : ℝ) + 1) * ((k : ℝ) + (⌊y⌋₊ : ℝ) + 1) := by positivity
  rw [show (4 : ℝ) * (1 / ((k : ℝ) + 1) ^ 2) = 4 / ((k : ℝ) + 1) ^ 2 by ring]
  rw [div_le_div_iff₀ hA (by positivity : (0 : ℝ) < ((k : ℝ) + 1) ^ 2)]
  nlinarith [hkn, hk1]

private lemma harmTailG_partial {y : ℝ} (hy : 3 ≤ y) (n : ℕ) :
    ∑ k ∈ Finset.range n, harmTailG y k ≤ 16 * (Real.log y + 1) / y := by
  have hN1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ y from le_trans (by norm_num) hy)
  have h1 : ∑ k ∈ Finset.range n, harmTailG y k
      ≤ ∑ k ∈ Finset.range n, (2 : ℝ) / (((k + 1 : ℕ) : ℝ) * (((k + ⌊y⌋₊ + 1 : ℕ) : ℝ))) := by
    apply Finset.sum_le_sum
    intro k _
    simpa only [harmTailG] using Work.ZeroDensity.Zeta.balAux.harmTailPtwise y hy k
  refine h1.trans ?_
  have h2 := Work.ZeroDensity.Zeta.balAux.harmTailTelescope ⌊y⌋₊ n hN1
  refine h2.trans ?_
  exact Work.ZeroDensity.Zeta.balAux.harmTailNumeric y hy

/-- Harmonic tail estimate feeding the far tail of the sawtooth sum. -/
private lemma harm_tail_bound (y : ℝ) (hy : 3 ≤ y) :
    ∑' k : ℕ, harmTailG y k ≤ 16 * (Real.log y + 1) / y := by
  have hsumm := harmTailG_summable hy
  exact le_of_tendsto hsumm.hasSum.tendsto_sum_nat
    (Filter.Eventually.of_forall (harmTailG_partial hy))

/-! ## The far tail -/

/-- `‖m^{cls t - 1}‖ = m^{-1/2}` for `m ≥ 1`. -/
private lemma norm_nat_cpow_cls (t : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    ‖((m : ℂ)) ^ (cls t - 1)‖ = (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  congr 1
  simp only [Complex.sub_re, Complex.one_re, cls_re]
  norm_num

/-- The summand controlling the far tail. -/
private def farTailB (y : ℝ) (i : ℕ) : ℝ :=
  1 / (((i + ⌊y⌋₊ + 3 : ℕ) : ℝ) * (((i + ⌊y⌋₊ + 3 : ℕ) : ℝ) - y))
    + 1 / ((((i + ⌊y⌋₊ + 3 : ℕ) : ℝ)) ^ 2)

private lemma farTailB_le_harmTailG (y : ℝ) (i : ℕ) : farTailB y i ≤ harmTailG y i := by
  have h1 : (0 : ℝ) < ((i + ⌊y⌋₊ + 2 : ℕ) : ℝ) := by positivity
  have h2 : (0 : ℝ) < ((i + ⌊y⌋₊ + 3 : ℕ) : ℝ) := by positivity
  have hmyle : ((i + ⌊y⌋₊ + 2 : ℕ) : ℝ) ≤ ((i + ⌊y⌋₊ + 3 : ℕ) : ℝ) := by push_cast; ring_nf; norm_num
  have hmy2le : ((i + ⌊y⌋₊ + 2 : ℕ) : ℝ) - y ≤ ((i + ⌊y⌋₊ + 3 : ℕ) : ℝ) - y := by
    push_cast; ring_nf; norm_num
  have hposnd : 0 < ((i + ⌊y⌋₊ + 2 : ℕ) : ℝ) - y := by
    have hfl := Nat.lt_floor_add_one y
    push_cast; linarith
  have hposmd : 0 < ((i + ⌊y⌋₊ + 3 : ℕ) : ℝ) - y := by
    have hfl := Nat.lt_floor_add_one y
    push_cast; linarith
  simp only [farTailB, harmTailG]
  apply add_le_add
  · apply one_div_le_one_div_of_le
    · exact mul_pos h1 hposnd
    · exact mul_le_mul hmyle hmy2le hposnd.le h2.le
  · apply one_div_le_one_div_of_le (by positivity) (by nlinarith [h2])

/-- The resonance constant bound for the far tail of the sawtooth sum. -/
lemma afeFarTail_bound (Cres : ℝ)
    (hCres : ∀ t : ℝ, 1000000 ≤ t → ∀ A : ℝ, 1 ≤ A → ‖afeT (cls t) A‖ ≤ Cres / t)
    (t : ℝ) (ht : 1000000 ≤ t) :
    ‖∑' i : ℕ, afeTerm t (i + afeMt t)‖ ≤ 2 * Cres / t + 320 / t := by
  have htpos : (0 : ℝ) < t := by linarith
  have hPpos : 0 < afeP t := afeP_pos t
  have hy3 : 3 ≤ afeY t := afeY_ge ht
  have hypos : 0 < afeY t := afeY_pos ht
  have hymul : afeY t * afeP t = t := afeY_mul ht
  have hymul' : afeP t * afeY t = t := by rw [mul_comm]; exact hymul
  have hMt : afeMt t = ⌊afeY t⌋₊ := afeMt_eq t
  have hsumm : Summable (fun k : ℕ => afeTerm t k) := afeTerm_summable t ht
  have hA1 : ∀ k : ℕ, 1 ≤ afeP t * ((k : ℝ) + 1) := by
    intro k
    have h1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    nlinarith [afeP_ge t, h1]
  have hres : ∀ k : ℕ, ‖afeTerm t k‖ ≤ Cres / t := by
    intro k
    rw [afeTerm_eq, norm_mul, norm_idx_pow]
    have hc := hCres t ht (afeP t * ((k : ℝ) + 1)) (hA1 k)
    have hp : ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      have h := Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ (k : ℝ) + 1 by
          have h0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith)
        (show (-(1 / 2 : ℝ)) ≤ 0 by norm_num)
      rwa [Real.rpow_zero] at h
    calc ((k : ℝ) + 1) ^ (-(1 / 2 : ℝ)) * ‖afeT (cls t) (afeP t * ((k : ℝ) + 1))‖
        ≤ 1 * (Cres / t) := mul_le_mul hp hc (norm_nonneg _) (by norm_num)
      _ = Cres / t := one_mul _
  have hsumm2 : Summable (fun i : ℕ => afeTerm t (i + afeMt t)) :=
    (summable_nat_add_iff (afeMt t)).mpr hsumm
  have hsplit := Summable.sum_add_tsum_nat_add (f := fun i : ℕ => afeTerm t (i + afeMt t)) 2 hsumm2
  rw [← hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have h2 : ‖∑ i ∈ Finset.range 2, afeTerm t (i + afeMt t)‖ ≤ 2 * Cres / t := by
    refine le_trans (norm_sum_le _ _) ?_
    have hle : (∑ i ∈ Finset.range 2, ‖afeTerm t (i + afeMt t)‖) ≤ ∑ _i ∈ Finset.range 2, (Cres / t) :=
      Finset.sum_le_sum (fun i _ => hres (i + afeMt t))
    refine hle.trans ?_
    have hsum2 : (∑ _i ∈ Finset.range 2, (Cres / t)) = 2 * Cres / t := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    exact hsum2.le
  have h3 : ‖∑' i : ℕ, afeTerm t ((i + 2) + afeMt t)‖ ≤ 320 / t := by
    have hsummT : Summable (fun i : ℕ => afeTerm t ((i + 2) + afeMt t)) := by
      have h := (summable_nat_add_iff (afeMt t + 2)).mpr hsumm
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have hnormsumm : Summable (fun i : ℕ => ‖afeTerm t ((i + 2) + afeMt t)‖) := hsummT.norm
    refine le_trans (norm_tsum_le_tsum_norm hnormsumm) ?_
    have hpt : ∀ i : ℕ, ‖afeTerm t ((i + 2) + afeMt t)‖ ≤ 2 * (afeP t) ^ (-(3 / 2 : ℝ)) * farTailB (afeY t) i := by
      intro i
      have hm : ((i + 2) + afeMt t : ℕ) + 1 = i + ⌊afeY t⌋₊ + 3 := by rw [hMt]; omega
      set n : ℝ := ((i + ⌊afeY t⌋₊ + 3 : ℕ) : ℝ) with hn
      have hnpos : 0 < n := by rw [hn]; positivity
      have hlt_y : afeY t < n := by
        rw [hn]
        have hfl := Nat.lt_floor_add_one (afeY t)
        push_cast
        linarith
      have hA : t < afeP t * n := by
        have h := mul_lt_mul_of_pos_left hlt_y hPpos
        rwa [hymul'] at h
      have hAn1 : 1 ≤ afeP t * n := by
        have h1 : (1 : ℝ) ≤ n := by
          rw [hn]
          have : (1 : ℕ) ≤ i + ⌊afeY t⌋₊ + 3 := by omega
          exact_mod_cast this
        nlinarith [afeP_ge t, h1]
      have hb := norm_afeT_le_tail (t := t) (A := afeP t * n) hAn1 hA (le_of_lt htpos)
      have hexp : (-(1 / 2 : ℝ) - 1) = (-(3 / 2 : ℝ)) := by norm_num
      rw [hexp] at hb
      have hkn : (((i + 2) + afeMt t : ℕ) : ℝ) + 1 = n := by
        have h1 : ((((i + 2) + afeMt t : ℕ) : ℝ) + 1) = ((((i + 2) + afeMt t + 1 : ℕ)) : ℝ) := by
          push_cast; ring
        rw [h1, hm]
      rw [afeTerm_eq, norm_mul, norm_idx_pow, hkn]
      have htu : afeP t * n - t = afeP t * (n - afeY t) := by
        have hh : afeP t * (n - afeY t) = afeP t * n - afeP t * afeY t := by ring
        rw [hh, hymul']
      have hnd : 0 < n - afeY t := by linarith
      calc n ^ (-(1 / 2 : ℝ)) * ‖afeT (cls t) (afeP t * n)‖
          ≤ n ^ (-(1 / 2 : ℝ)) * (2 * (afeP t * n) ^ (-(1 / 2 : ℝ)) / (afeP t * n - t)
              + 2 * (afeP t * n) ^ (-(3 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hnpos.le _)
        _ = 2 * (afeP t) ^ (-(3 / 2 : ℝ)) * farTailB (afeY t) i := by
            simp only [farTailB]
            rw [htu, mul_add, rpow_combine hPpos hnpos (n - afeY t) 2,
              rpow_combine2 hPpos hnpos 2, mul_add]
    have hbmsumm : Summable (fun i : ℕ => farTailB (afeY t) i) :=
      Summable.of_nonneg_of_le
        (fun i => by
          have h1 : (0 : ℝ) < ((i + ⌊afeY t⌋₊ + 3 : ℕ) : ℝ) := by positivity
          have h2 : (0 : ℝ) < ((i + ⌊afeY t⌋₊ + 3 : ℕ) : ℝ) - afeY t := by
            have hfl := Nat.lt_floor_add_one (afeY t)
            push_cast; linarith
          simp only [farTailB]; positivity)
        (fun i => farTailB_le_harmTailG (afeY t) i) (harmTailG_summable hy3)
    have hle := Summable.tsum_le_tsum hpt hnormsumm (hbmsumm.mul_left (2 * (afeP t) ^ (-(3 / 2 : ℝ))))
    refine le_trans hle ?_
    rw [tsum_mul_left]
    have hbm_le : ∑' i : ℕ, farTailB (afeY t) i ≤ 16 * (Real.log (afeY t) + 1) / afeY t :=
      (Summable.tsum_le_tsum (fun i => farTailB_le_harmTailG (afeY t) i) hbmsumm
        (harmTailG_summable hy3)).trans (harm_tail_bound (afeY t) hy3)
    refine le_trans (mul_le_mul_of_nonneg_left hbm_le (by positivity)) ?_
    rw [le_div_iff₀ htpos]
    have hlog' : Real.log (afeY t) + 1 ≤ 10 * (afeP t) ^ (1 / 2 : ℝ) := logY_bound ht
    have hdiv : t / afeY t = afeP t := by
      rw [div_eq_iff hypos.ne', mul_comm]; exact hymul.symm
    have hsimp : 2 * (afeP t) ^ (-(3 / 2 : ℝ)) * (16 * (Real.log (afeY t) + 1) / afeY t) * t
        = 32 * (Real.log (afeY t) + 1) * (afeP t) ^ (-(1 / 2 : ℝ)) := by
      rw [show (-(3 / 2 : ℝ)) = (-(1 / 2 : ℝ)) + (-1) by norm_num, Real.rpow_add hPpos,
        Real.rpow_neg_one]
      rw [show 2 * ((afeP t) ^ (-(1 / 2 : ℝ)) * (afeP t)⁻¹)
            * (16 * (Real.log (afeY t) + 1) / afeY t) * t
          = 32 * (Real.log (afeY t) + 1) * (t / afeY t)
            * ((afeP t) ^ (-(1 / 2 : ℝ)) * (afeP t)⁻¹) by ring, hdiv]
      rw [show (32 * (Real.log (afeY t) + 1) * afeP t
            * ((afeP t) ^ (-(1 / 2 : ℝ)) * (afeP t)⁻¹))
          = 32 * (Real.log (afeY t) + 1)
            * ((afeP t) ^ (-(1 / 2 : ℝ)) * (afeP t * (afeP t)⁻¹)) by ring,
        mul_inv_cancel₀ hPpos.ne', mul_one]
    rw [hsimp]
    have hPmul : (afeP t) ^ (1 / 2 : ℝ) * (afeP t) ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hPpos]; norm_num
    have hstep1 : 32 * (Real.log (afeY t) + 1) * (afeP t) ^ (-(1 / 2 : ℝ))
        ≤ 32 * (10 * (afeP t) ^ (1 / 2 : ℝ)) * (afeP t) ^ (-(1 / 2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog' (by norm_num))
      exact Real.rpow_nonneg (le_of_lt hPpos) _
    have hstep2 : 32 * (10 * (afeP t) ^ (1 / 2 : ℝ)) * (afeP t) ^ (-(1 / 2 : ℝ)) = 320 := by
      rw [show (32 : ℝ) * (10 * (afeP t) ^ (1 / 2 : ℝ)) * (afeP t) ^ (-(1 / 2 : ℝ))
          = 320 * ((afeP t) ^ (1 / 2 : ℝ) * (afeP t) ^ (-(1 / 2 : ℝ))) by ring, hPmul, mul_one]
    linarith [hstep1, hstep2]
  linarith [h2, h3]

theorem afeResonanceSumBound : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1000000 ≤ t →
    ‖Work.ZeroDensity.Ingham.afeTsum t
      - Work.ZeroDensity.Ingham.afeC0 (Work.ZeroDensity.Ingham.cls t)
        * Work.ZeroDensity.Ingham.afeDual t‖ ≤ C / t := by
  obtain ⟨Cres, hCrespos, hCres⟩ := Work.ZeroDensity.Zeta.sinTailUniform
  refine ⟨644 + 3 * Cres, by linarith, ?_⟩
  intro t ht
  have htpos : (0 : ℝ) < t := by linarith
  have hsumm : Summable (fun k : ℕ => afeTerm t k) := afeTerm_summable t ht
  have hysucc : afeYc t + 1 = afeMt t := afeYc_succ ht
  -- split `afeTsum`
  have hsplit : afeTsum t
      = (∑ i ∈ Finset.range (afeYc t), afeTerm t i) + ∑' i : ℕ, afeTerm t (i + afeYc t) := by
    rw [afeTsum, Summable.sum_add_tsum_nat_add (afeYc t) hsumm]
  -- peel off the boundary term
  have hsumm2 : Summable (fun i : ℕ => afeTerm t (i + afeYc t)) :=
    (summable_nat_add_iff (afeYc t)).mpr hsumm
  have hpeel := Summable.sum_add_tsum_nat_add (f := fun i : ℕ => afeTerm t (i + afeYc t)) 1 hsumm2
  have htail_eq : (∑' i : ℕ, afeTerm t (i + afeYc t))
      = afeTerm t (afeYc t) + ∑' i : ℕ, afeTerm t (i + afeMt t) := by
    rw [← hpeel, Finset.sum_range_one, show (0 + afeYc t) = afeYc t by omega]
    congr 1
    apply tsum_congr
    intro i
    congr 1
    omega
  -- the dual sum, split at the cut
  have hdual_shift : (∑ m ∈ Finset.Icc 1 (afeYc t + 1), (m : ℂ) ^ (cls t - 1))
      = (∑ m ∈ Finset.Icc 1 (afeYc t), (m : ℂ) ^ (cls t - 1))
        + ((afeYc t + 1 : ℕ) : ℂ) ^ (cls t - 1) := by
    rw [← sum_range_one_add (fun m => (m : ℂ) ^ (cls t - 1)) (afeYc t + 1), Finset.sum_range_succ,
      sum_range_one_add (fun m => (m : ℂ) ^ (cls t - 1)) (afeYc t)]
  have hdual_reindex : (∑ m ∈ Finset.Icc 1 (afeYc t), (m : ℂ) ^ (cls t - 1))
      = ∑ i ∈ Finset.range (afeYc t), (((i : ℝ) + 1 : ℂ)) ^ (cls t - 1) := by
    rw [← sum_range_one_add (fun m => (m : ℂ) ^ (cls t - 1)) (afeYc t)]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    push_cast; ring
  have hdual : afeDual t
      = (∑ i ∈ Finset.range (afeYc t), (((i : ℝ) + 1 : ℂ)) ^ (cls t - 1))
        + (((afeYc t + 1 : ℕ) : ℂ)) ^ (cls t - 1) := by
    rw [afeDual_apply, ← hysucc, hdual_shift, hdual_reindex]
  -- the boundary term
  have hbnd : ‖afeTerm t (afeYc t)
      - afeC0 (cls t) * (((afeYc t + 1 : ℕ) : ℂ)) ^ (cls t - 1)‖ ≤ 4 / t + Cres / t := by
    have hs0 : 0 < (cls t).re := cls_re_pos t
    have hs1 : (cls t).re < 1 := cls_re_lt_one t
    have hBcast : (((afeYc t : ℝ) + 1 : ℂ)) = (((afeYc t + 1 : ℕ) : ℂ)) := by push_cast; ring
    have hAcast : afeP t * ((afeYc t : ℝ) + 1) = afeP t * ((afeYc t + 1 : ℕ) : ℝ) := by
      push_cast; ring
    have hA1 : 1 ≤ afeP t * ((afeYc t + 1 : ℕ) : ℝ) := by
      have h1 : (1 : ℝ) ≤ ((afeYc t + 1 : ℕ) : ℝ) := by
        have h2 : (1 : ℕ) ≤ afeYc t + 1 := by omega
        exact_mod_cast h2
      nlinarith [afeP_ge t, h1]
    have hterm : afeTerm t (afeYc t)
        = (((afeYc t + 1 : ℕ) : ℂ)) ^ (cls t - 1)
          * afeT (cls t) (afeP t * ((afeYc t + 1 : ℕ) : ℝ)) := by
      rw [afeTerm_eq, hBcast, hAcast]
    have hfact : (((afeYc t + 1 : ℕ) : ℂ)) ^ (cls t - 1)
          * afeT (cls t) (afeP t * ((afeYc t + 1 : ℕ) : ℝ))
          - afeC0 (cls t) * (((afeYc t + 1 : ℕ) : ℂ)) ^ (cls t - 1)
        = - ((((afeYc t + 1 : ℕ) : ℂ)) ^ (cls t - 1)
            * afeL (cls t) (afeP t * ((afeYc t + 1 : ℕ) : ℝ))) := by
      rw [afeT_eq_c0_sub hs0 hs1 hA1]
      ring
    have hLeq : afeL (cls t) (afeP t * ((afeYc t + 1 : ℕ) : ℝ))
        = afeC0 (cls t) - afeT (cls t) (afeP t * ((afeYc t + 1 : ℕ) : ℝ)) := by
      rw [afeT_eq_c0_sub hs0 hs1 hA1]; ring
    have hL : ‖afeL (cls t) (afeP t * ((afeYc t + 1 : ℕ) : ℝ))‖ ≤ 4 / t + Cres / t := by
      calc ‖afeL (cls t) (afeP t * ((afeYc t + 1 : ℕ) : ℝ))‖
          = ‖afeC0 (cls t) - afeT (cls t) (afeP t * ((afeYc t + 1 : ℕ) : ℝ))‖ := by rw [hLeq]
        _ ≤ ‖afeC0 (cls t)‖ + ‖afeT (cls t) (afeP t * ((afeYc t + 1 : ℕ) : ℝ))‖ := norm_sub_le _ _
        _ ≤ 4 / t + Cres / t := add_le_add (afeC0_bound ht) (hCres t ht _ hA1)
    have hp : (((afeYc t + 1 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      have h1 : (1 : ℝ) ≤ ((afeYc t + 1 : ℕ) : ℝ) := by
        have h2 : (1 : ℕ) ≤ afeYc t + 1 := by omega
        exact_mod_cast h2
      have h := Real.rpow_le_rpow_of_exponent_le h1 (show (-(1 / 2 : ℝ)) ≤ 0 by norm_num)
      rwa [Real.rpow_zero] at h
    rw [hterm, hfact, norm_neg, norm_mul, norm_nat_cpow_cls t (afeYc t + 1) (by omega)]
    calc (((afeYc t + 1 : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))
          * ‖afeL (cls t) (afeP t * ((afeYc t + 1 : ℕ) : ℝ))‖
        ≤ 1 * (4 / t + Cres / t) := mul_le_mul hp hL (norm_nonneg _) (by norm_num)
      _ = 4 / t + Cres / t := by ring
  have hmain := afeMain_bound t ht
  have hfar := afeFarTail_bound Cres (fun t ht A hA => hCres t ht A hA) t ht
  have hkey : afeTsum t - afeC0 (cls t) * afeDual t
      = ((∑ i ∈ Finset.range (afeYc t),
            (afeTerm t i - afeC0 (cls t) * (((i : ℝ) + 1 : ℂ)) ^ (cls t - 1)))
          + (afeTerm t (afeYc t)
              - afeC0 (cls t) * (((afeYc t + 1 : ℕ) : ℂ)) ^ (cls t - 1)))
        + (∑' i : ℕ, afeTerm t (i + afeMt t)) := by
    rw [hsplit, htail_eq, hdual, mul_add, Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  calc ‖afeTsum t - afeC0 (cls t) * afeDual t‖
      = ‖((∑ i ∈ Finset.range (afeYc t),
            (afeTerm t i - afeC0 (cls t) * (((i : ℝ) + 1 : ℂ)) ^ (cls t - 1)))
          + (afeTerm t (afeYc t)
              - afeC0 (cls t) * (((afeYc t + 1 : ℕ) : ℂ)) ^ (cls t - 1)))
        + (∑' i : ℕ, afeTerm t (i + afeMt t))‖ := by rw [hkey]
    _ ≤ ‖(∑ i ∈ Finset.range (afeYc t),
            (afeTerm t i - afeC0 (cls t) * (((i : ℝ) + 1 : ℂ)) ^ (cls t - 1)))
          + (afeTerm t (afeYc t)
              - afeC0 (cls t) * (((afeYc t + 1 : ℕ) : ℂ)) ^ (cls t - 1))‖
        + ‖∑' i : ℕ, afeTerm t (i + afeMt t)‖ := norm_add_le _ _
    _ ≤ (320 / t + (4 / t + Cres / t)) + (2 * Cres / t + 320 / t) := by
        refine add_le_add ?_ hfar
        exact le_trans (norm_add_le _ _) (add_le_add hmain hbnd)
    _ ≤ (644 + 3 * Cres) / t := by
        have h : ((320 : ℝ) / t + (4 / t + Cres / t)) + (2 * Cres / t + 320 / t)
            = (644 + 3 * Cres) / t := by
          field_simp; ring
        exact le_of_eq h

end

end Work.ZeroDensity.Ingham.AfeProof
