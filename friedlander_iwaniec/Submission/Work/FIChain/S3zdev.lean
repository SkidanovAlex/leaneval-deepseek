/-
# `Submission.Work.FIChain.S3zdev` — the deviation lemma for the `S₃`-average

The chain's `assemblyC`/`primeSum_bound_of_prop41` consume the **fixed-`z`** `y`-average of
`Submission.ASP.S3`.  The companion's §8 proves its estimate `S₃ ≪ A(x)(log x)^{-1}` only for the
**`z`-averaged** quantity: §8.4 says "integrate in `z` over `Z<z<eZ` and change `z` into `z=k`", and
that substitution (which removes the `k`-dependence of the `(R′)`-argument) is legitimate only
because `z` is an integration variable.  See `NOTES.md` §46.

This file supplies the **bridge**: if the companion's §4–§7 part of the identity (3.4) is bounded at
every point `z ∈ [Z,eZ]` and the `S₃`-average is bounded at *some* `z₁ ∈ [Z,eZ]`, then the fixed-`z`
(`z = Z`) signed average of `S₃` obeys `E₅ + 2E + Σ_{Z<n≤eZ}|a_n ρ_n Λ(n)|`.
-/
import Mathlib
import Submission.ASP.Smooth
import Submission.Work.FIChain.Defs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

noncomputable section

/-- The signed, fixed-`z`, `y`-averaged `S₃`: `∫_Y^{eY} S₃(a,λ,N,z,(s·y),(s·z)) dy/y`. -/
def S3avgFix (a lam : ℕ → ℝ) (N : ℕ) (z s Y : ℝ) : ℝ :=
  ∫ y in Y..(Real.exp 1 * Y), Submission.ASP.S3 a lam N z (s * y) (s * z) / y

/-- The completion deviation `Σ_{Z<n≤eZ} |a n · ρ n · Λ n|`. -/
def S3delSum (a lam : ℕ → ℝ) (N : ℕ) (Z : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter
      (fun n => Z < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ Real.exp 1 * Z),
    |a n * Submission.ASP.rhoOf lam n * ArithmeticFunction.vonMangoldt n|

/-- The companion's (3.4) identity in split form. -/
theorem S_eq_split (a lam : ℕ → ℝ) (N : ℕ) {Y s z : ℝ}
    (hN : 1 ≤ N) (hY : 0 < Y) (hs : 1 ≤ s) (hz : 0 < z) :
    (∑ n ∈ Finset.Icc 1 N, a n * Submission.ASP.rhoOf lam n *
        (if z < ((n : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt n else 0))
      = (∫ y in Y..(Real.exp 1 * Y),
            (Submission.ASP.Tsum a lam (N : ℝ) y - Submission.ASP.Tsum2 a lam (N : ℝ) y z
              + Submission.ASP.S2 a lam N y z (s * y)
              + Submission.ASP.S1 a lam N (s * y) (s * z)) / y)
        + S3avgFix a lam N z s Y := by
  rw [S3avgFix]
  rw [Submission.ASP.S_eq_y_smoothed a lam N hN hY hs hz]
  have hT' := Submission.ASP.intervalIntegrable_Tsum_div a lam N hY
  have hT2' := Submission.ASP.intervalIntegrable_Tsum2_div a lam N z hY
  have hS2' := Submission.ASP.intervalIntegrable_S2_div (z := z) a lam N hs hY
  have hS1' := Submission.ASP.intervalIntegrable_S1_div (z := z) a lam N hs hY
  have hS3' := Submission.ASP.intervalIntegrable_S3_div (z := z) a lam N hs hY
  have hI1 : IntervalIntegrable (fun y : ℝ =>
      (Submission.ASP.Tsum a lam (N : ℝ) y - Submission.ASP.Tsum2 a lam (N : ℝ) y z
        + Submission.ASP.S2 a lam N y z (s * y)
        + Submission.ASP.S1 a lam N (s * y) (s * z)) / y) volume Y (Real.exp 1 * Y) := by
    have h12 : IntervalIntegrable (fun y : ℝ =>
        Submission.ASP.Tsum a lam (N : ℝ) y / y
          - Submission.ASP.Tsum2 a lam (N : ℝ) y z / y) volume Y (Real.exp 1 * Y) :=
      IntervalIntegrable.sub hT' hT2'
    have h123 : IntervalIntegrable (fun y : ℝ =>
        Submission.ASP.Tsum a lam (N : ℝ) y / y - Submission.ASP.Tsum2 a lam (N : ℝ) y z / y
          + Submission.ASP.S2 a lam N y z (s * y) / y) volume Y (Real.exp 1 * Y) :=
      IntervalIntegrable.add h12 hS2'
    have h1234 : IntervalIntegrable (fun y : ℝ =>
        Submission.ASP.Tsum a lam (N : ℝ) y / y - Submission.ASP.Tsum2 a lam (N : ℝ) y z / y
          + Submission.ASP.S2 a lam N y z (s * y) / y
          + Submission.ASP.S1 a lam N (s * y) (s * z) / y) volume Y (Real.exp 1 * Y) :=
      IntervalIntegrable.add h123 hS1'
    refine h1234.congr ?_
    intro y _
    ring
  have hsplit := intervalIntegral.integral_add hI1 hS3'
  have hfun : (fun y : ℝ =>
        (Submission.ASP.Tsum a lam (N : ℝ) y - Submission.ASP.Tsum2 a lam (N : ℝ) y z
          + Submission.ASP.S2 a lam N y z (s * y) + Submission.ASP.S3 a lam N z (s * y) (s * z)
          + Submission.ASP.S1 a lam N (s * y) (s * z)) / y)
      = fun y : ℝ =>
          (Submission.ASP.Tsum a lam (N : ℝ) y - Submission.ASP.Tsum2 a lam (N : ℝ) y z
            + Submission.ASP.S2 a lam N y z (s * y)
            + Submission.ASP.S1 a lam N (s * y) (s * z)) / y
          + Submission.ASP.S3 a lam N z (s * y) (s * z) / y := by
    funext y; ring
  rw [hfun, hsplit]

/-- The pointwise algebra of the truncation difference. -/
theorem trunc_sub (a lam : ℕ → ℝ) {Z z₁ : ℝ} (hZz₁ : Z ≤ z₁) (n : ℕ) :
    a n * Submission.ASP.rhoOf lam n *
        (if Z < ((n : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt n else 0)
      - a n * Submission.ASP.rhoOf lam n *
          (if z₁ < ((n : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt n else 0)
      = (if Z < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ z₁ then
          a n * Submission.ASP.rhoOf lam n * ArithmeticFunction.vonMangoldt n else 0) := by
  by_cases h1 : Z < ((n : ℕ) : ℝ)
  · by_cases h2 : z₁ < ((n : ℕ) : ℝ)
    · have hnot : ¬ ((n : ℕ) : ℝ) ≤ z₁ := not_le.mpr h2
      rw [if_pos h1, if_pos h2, if_neg (fun hh => hnot hh.2)]; ring
    · have hle : ((n : ℕ) : ℝ) ≤ z₁ := not_lt.mp h2
      rw [if_pos h1, if_neg h2, if_pos ⟨h1, hle⟩]; ring
  · have h2 : ¬ z₁ < ((n : ℕ) : ℝ) := not_lt.mpr (le_trans (not_lt.mp h1) hZz₁)
    rw [if_neg h1, if_neg h2, if_neg (fun hh => h1 hh.1)]; ring

/-- **The deviation lemma.** -/
theorem S3avgFix_le_of_zavg (a lam : ℕ → ℝ) (N : ℕ)
    {Y Z s E E5 H : ℝ} {z₁ : ℝ}
    (hN : 1 ≤ N) (hY : 0 < Y) (hs : 1 ≤ s) (hZ : 0 < Z)
    (hz₁ : z₁ ∈ Set.Icc Z (Real.exp 1 * Z))
    (hPhi : ∀ z ∈ Set.Icc Z (Real.exp 1 * Z),
      |(∫ y in Y..(Real.exp 1 * Y),
          (Submission.ASP.Tsum a lam (N : ℝ) y - Submission.ASP.Tsum2 a lam (N : ℝ) y z
            + Submission.ASP.S2 a lam N y z (s * y)
            + Submission.ASP.S1 a lam N (s * y) (s * z)) / y)
        - H * Submission.ASP.Acount a (N : ℝ)| ≤ E)
    (hS3 : |S3avgFix a lam N z₁ s Y| ≤ E5) :
    |S3avgFix a lam N Z s Y| ≤ E5 + 2 * E + S3delSum a lam N Z := by
  have hz₁pos : 0 < z₁ := lt_of_lt_of_le hZ hz₁.1
  have hkeyZ := S_eq_split a lam N hN hY hs hZ
  have hkey₁ := S_eq_split a lam N hN hY hs hz₁pos
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num)
  have hΦZ := hPhi Z ⟨le_rfl, by nlinarith [hZ, he1]⟩
  have hΦ₁ := hPhi z₁ hz₁
  set GZ := ∑ n ∈ Finset.Icc 1 N, a n * Submission.ASP.rhoOf lam n *
        (if Z < ((n : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt n else 0) with hGZ
  set G₁ := ∑ n ∈ Finset.Icc 1 N, a n * Submission.ASP.rhoOf lam n *
        (if z₁ < ((n : ℕ) : ℝ) then ArithmeticFunction.vonMangoldt n else 0) with hG₁
  set ΦZ := (∫ y in Y..(Real.exp 1 * Y),
          (Submission.ASP.Tsum a lam (N : ℝ) y - Submission.ASP.Tsum2 a lam (N : ℝ) y Z
            + Submission.ASP.S2 a lam N y Z (s * y)
            + Submission.ASP.S1 a lam N (s * y) (s * Z)) / y) with hΦZdef
  set Φ₁ := (∫ y in Y..(Real.exp 1 * Y),
          (Submission.ASP.Tsum a lam (N : ℝ) y - Submission.ASP.Tsum2 a lam (N : ℝ) y z₁
            + Submission.ASP.S2 a lam N y z₁ (s * y)
            + Submission.ASP.S1 a lam N (s * y) (s * z₁)) / y) with hΦ₁def
  have halg : S3avgFix a lam N Z s Y = S3avgFix a lam N z₁ s Y + (GZ - G₁) - (ΦZ - Φ₁) := by
    rw [hGZ, hG₁, hΦZdef, hΦ₁def]
    linarith [hkeyZ, hkey₁]
  have hGdiff : GZ - G₁ = ∑ n ∈ (Finset.Icc 1 N).filter
          (fun n => Z < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ z₁),
          a n * Submission.ASP.rhoOf lam n * ArithmeticFunction.vonMangoldt n := by
    rw [hGZ, hG₁, ← Finset.sum_sub_distrib, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun n _ => trunc_sub a lam hz₁.1 n)
  have hGle : |GZ - G₁| ≤ S3delSum a lam N Z := by
    rw [hGdiff, S3delSum]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => abs_nonneg _)
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1, le_trans hn.2.2 hz₁.2⟩
  have hΦd : |ΦZ - Φ₁| ≤ E + E := by
    have hsplit : ΦZ - Φ₁ = (ΦZ - H * Submission.ASP.Acount a (N : ℝ))
        - (Φ₁ - H * Submission.ASP.Acount a (N : ℝ)) := by rw [hΦZdef, hΦ₁def]; ring
    rw [hsplit]
    refine le_trans (abs_sub _ _) (add_le_add ?_ ?_)
    · rw [hΦZdef] at hΦZ; exact hΦZ
    · have h2 : |Φ₁ - H * Submission.ASP.Acount a (N : ℝ)| ≤ E := by
        rw [hΦ₁def] at hΦ₁; exact hΦ₁
      exact h2
  have hmain : |S3avgFix a lam N Z s Y|
      ≤ |S3avgFix a lam N z₁ s Y| + |GZ - G₁| + |ΦZ - Φ₁| := by
    rw [halg]
    have ha := abs_sub (S3avgFix a lam N z₁ s Y + (GZ - G₁)) (ΦZ - Φ₁)
    have hb := abs_sub (S3avgFix a lam N z₁ s Y) (-(GZ - G₁))
    rw [abs_neg, sub_neg_eq_add] at hb
    linarith
  linarith [hmain, hS3, hGle, hΦd]

end

end Work.FIChain
