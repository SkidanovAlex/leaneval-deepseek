/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Analysis.InverseTheory.Transpose
import Submission.Work.KMTAreas.A4Z.eLpNorm_comp_add_count
import Submission.Port.Aesm

/-!
# `Ã_N^{**}(f,h) ∈ ℓ²` for `f ∈ ℓ²` and `h` bounded by `1`

The second dual function of the halved bilinear average (paper §5, equation `(bkhf)`) is

`Ã_N^{**}(f,h)(x) = N⁻¹ ∑_{N/2 < n ≤ N} f(x + n - P(n)) h(x - P(n))`.

Since `P` is *fixed*, the shifts `n - P(n)` and `P(n)` are just integers, so the definition is a
finite average of the functions `x ↦ f(x + n - P(n)) · h(x - P(n))`, each of which is the translate
of `f` by `n - P(n)`, multiplied pointwise by the `1`-bounded function `h(· - P(n))`.  Hence:

* the triangle inequality in `ℓ²` gives `‖Ã_N^{**}(f,h)‖_{ℓ²} ≤ ‖f‖_{ℓ²}` — the factor
  `N⁻¹ · #(N/2, N] ≤ 1` being at most `1`;
* consequently `f ∈ ℓ²` implies `Ã_N^{**}(f,h) ∈ ℓ²`, with a norm that does not grow in `N`.

This is the estimate used by `Work.KMTAreas.A4Z.pairingBound_of_sivSecondClaim`, where the second
dual function is paired with an `ℓ²` function and Cauchy–Schwarz is applied.

The only non-trivial input is the translation invariance of the `ℓ^p` norm for the counting
measure on `ℤ`, `eLpNorm_comp_add_count` (`Submission/Work/KMTAreas/A4Z/eLpNorm_comp_add_count`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory

namespace Work.KMTAreas.A4Z

/-- **The `ℓ²` bound for the second dual function**: for `h` bounded pointwise by `1` and any
`f : ℤ → ℂ`, `‖Ã_N^{**}(f,h)‖_{ℓ²(ℤ)} ≤ ‖f‖_{ℓ²(ℤ)}`.

(No hypothesis is needed on `f` itself: the estimate is an inequality of `eLpNorm`s and is proved
from the triangle inequality, each summand being a translate of `f` times a `1`-bounded weight.) -/
theorem eLpNorm_ahalfTransposeTwo_le (N : ℕ) (P : Polynomial ℤ) {f h : ℤ → ℂ} (hN : 1 ≤ N)
    (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) :
    MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P f h x)
        2 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  set s : Finset ℕ := Finset.Ioc (N / 2) N with hs
  -- The normalising factor times the number of terms is at most `1`.
  have hcard : ((s.card : ℝ)) * (N : ℝ)⁻¹ ≤ 1 := by
    have hss : s.card ≤ N := by rw [hs, Nat.card_Ioc]; omega
    have hle : (s.card : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hss
    calc ((s.card : ℝ)) * (N : ℝ)⁻¹ ≤ (N : ℝ) * (N : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hNpos)
  have hEnn : ((s.card : ENNReal)) * ENNReal.ofReal ((N : ℝ)⁻¹) ≤ 1 := by
    calc ((s.card : ENNReal)) * ENNReal.ofReal ((N : ℝ)⁻¹)
        = ENNReal.ofReal ((s.card : ℝ)) * ENNReal.ofReal ((N : ℝ)⁻¹) := by
            rw [ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal (((s.card : ℝ)) * (N : ℝ)⁻¹) :=
            (ENNReal.ofReal_mul (Nat.cast_nonneg _)).symm
      _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hcard
      _ = 1 := ENNReal.ofReal_one
  have hc : ‖((((N : ℝ)⁻¹ : ℝ)) : ℂ)‖ₑ = ENNReal.ofReal ((N : ℝ)⁻¹) := by
    rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  -- Each summand is bounded in `ℓ²` by `‖f‖_{ℓ²}`: `h` contributes a factor `≤ 1` and the shift
  -- `x ↦ x + (n - P(n))` preserves the `ℓ²` norm of `f`.
  have hterm : ∀ n ∈ s,
      MeasureTheory.eLpNorm
        (fun x : ℤ => f (x + ((n : ℤ) - P.eval (n : ℤ))) * h (x - P.eval (n : ℤ)))
        2 MeasureTheory.Measure.count ≤ MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    intro n _hn
    calc MeasureTheory.eLpNorm
          (fun x : ℤ => f (x + ((n : ℤ) - P.eval (n : ℤ))) * h (x - P.eval (n : ℤ)))
          2 MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm
          (fun x : ℤ => f (x + ((n : ℤ) - P.eval (n : ℤ)))) 2 MeasureTheory.Measure.count :=
          eLpNorm_mono (hf := by pw_aesm) fun x => by
            rw [norm_mul]
            exact mul_le_of_le_one_right (norm_nonneg _) (hh _)
      _ = MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
          eLpNorm_comp_add_count f 2 ((n : ℤ) - P.eval (n : ℤ))
  -- Expand `Ã_N^{**}(f,h)` as the finite sum of its summands.
  have hfun : (fun x : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P f h x)
      = fun x : ℤ => ((N : ℝ)⁻¹) *
          ∑ n ∈ s, f (x + ((n : ℤ) - P.eval (n : ℤ))) * h (x - P.eval (n : ℤ)) := by
    funext x
    rw [Work.Analysis.InverseTheory.AhalfTranspose₂, ← hs]
    simp only [add_sub_assoc]
  rw [hfun]
  -- Pull the normalising factor out of the `eLpNorm`.
  have hsmul : (fun x : ℤ => ((N : ℝ)⁻¹) * ∑ n ∈ s,
        f (x + ((n : ℤ) - P.eval (n : ℤ))) * h (x - P.eval (n : ℤ)))
      = ((((N : ℝ)⁻¹ : ℝ)) : ℂ) • (fun x : ℤ => ∑ n ∈ s,
        f (x + ((n : ℤ) - P.eval (n : ℤ))) * h (x - P.eval (n : ℤ))) := rfl
  rw [hsmul]
  have hscalar := MeasureTheory.eLpNorm_const_smul ((((N : ℝ)⁻¹ : ℝ)) : ℂ)
    (fun x : ℤ => ∑ n ∈ s, f (x + ((n : ℤ) - P.eval (n : ℤ))) * h (x - P.eval (n : ℤ)))
    2 MeasureTheory.Measure.count
  rw [hscalar, hc]
  -- The triangle inequality followed by the termwise bound.
  have hsum : MeasureTheory.eLpNorm
      (fun x : ℤ => ∑ n ∈ s, f (x + ((n : ℤ) - P.eval (n : ℤ))) * h (x - P.eval (n : ℤ)))
      2 MeasureTheory.Measure.count
      ≤ (s.card : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    have hmain := MeasureTheory.eLpNorm_sum_le (μ := MeasureTheory.Measure.count) (p := 2)
      (s := s)
      (f := fun (n : ℕ) (x : ℤ) => f (x + ((n : ℤ) - P.eval (n : ℤ))) * h (x - P.eval (n : ℤ))) (by norm_num)
    have hcongr : MeasureTheory.eLpNorm
          (fun x : ℤ => ∑ n ∈ s, f (x + ((n : ℤ) - P.eval (n : ℤ))) * h (x - P.eval (n : ℤ)))
          2 MeasureTheory.Measure.count
        = MeasureTheory.eLpNorm (∑ n ∈ s,
            (fun x : ℤ => f (x + ((n : ℤ) - P.eval (n : ℤ))) * h (x - P.eval (n : ℤ))))
          2 MeasureTheory.Measure.count := by
            congr 1
            funext x
            rw [Finset.sum_apply]
    rw [hcongr]
    refine le_trans hmain (le_trans (Finset.sum_le_sum hterm) ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
  calc ENNReal.ofReal ((N : ℝ)⁻¹) * MeasureTheory.eLpNorm
        (fun x : ℤ => ∑ n ∈ s, f (x + ((n : ℤ) - P.eval (n : ℤ))) * h (x - P.eval (n : ℤ)))
        2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((N : ℝ)⁻¹)
          * ((s.card : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) := by
          gcongr
    _ = ((s.card : ENNReal) * ENNReal.ofReal ((N : ℝ)⁻¹))
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
          rw [← mul_assoc,
            mul_comm (ENNReal.ofReal ((N : ℝ)⁻¹)) ((s.card : ENNReal))]
    _ ≤ 1 * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
          gcongr
    _ = MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := one_mul _

/-- **The second dual function of the halved average is in `ℓ²` and is dominated by `f`.**  For
`f ∈ ℓ²(ℤ)` and `h` pointwise bounded by `1`, `Ã_N^{**}(f,h)` (paper §5, claim `(bkhf)`) lies in
`ℓ²(ℤ)` and satisfies `‖Ã_N^{**}(f,h)‖_{ℓ²} ≤ ‖f‖_{ℓ²}`. -/
theorem memLp_ahalfTransposeTwo_of_bdd (N : ℕ) (P : Polynomial ℤ) {f h : ℤ → ℂ} (hN : 1 ≤ N)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) :
    MeasureTheory.MemLp (fun x : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P f h x)
        2 MeasureTheory.Measure.count ∧
      MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P f h x)
        2 MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  have hbound : MeasureTheory.eLpNorm
      (fun x : ℤ => Work.Analysis.InverseTheory.AhalfTranspose₂ N P f h x)
      2 MeasureTheory.Measure.count ≤ MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
    eLpNorm_ahalfTransposeTwo_le (f := f) N P hN hh
  exact ⟨MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt hbound hf.eLpNorm_lt_top), hbound⟩

end Work.KMTAreas.A4Z
