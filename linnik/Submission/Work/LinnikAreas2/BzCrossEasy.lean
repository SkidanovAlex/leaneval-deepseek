/-
# `LinnikAreas2.BzCrossEasy` — the easy case `w·y ≤ N` of Graham's `S₃` (Bz-cross) estimate

The two lemmas `cz_log_mul_le` and `cz_easy_case_of` are copied from
`Submission/Work/ZeroDensity/Jutila/BzCrossAux.lean` (namespace `Work.ZeroDensity.Jutila`) into
this area, unchanged except for the namespace.

Why: `BzCrossAux.lean` also imports `BzCross.ModelB`, which imports the (currently non-building)
`BzCross.czRI_bound`/`czHarmDecay` chain.  The `ψ`-sieve of HB (11.13) only needs the *easy* case
`cz_easy_case_of`, whose proof (from the two stated hypotheses, `vonMangoldtSqEval_here`,
`cross_eq_split` and `cz_log_mul_le`) is entirely independent of that chain.  Copying the two
lemmas keeps the broken `BzCross` modules out of this area's import cone.
-/
import Mathlib
import Submission.Work.ZeroDensity.Jutila.grahamDefs
import Submission.Work.ZeroDensity.Jutila.grahamCrossAssembly

namespace Work.LinnikAreas2

open Finset
open Work.ZeroDensity.Jutila

noncomputable section

/-! ## The elementary bound on the `n = 1` correction -/

/-- `log w · log y ≤ 4 N` for `1 ≤ w ≤ y ≤ N`. -/
lemma cz_log_mul_le {w y : ℝ} {N : ℕ} (hw : 1 ≤ w) (hwy : w ≤ y) (hyN : y ≤ (N : ℝ)) :
    Real.log w * Real.log y ≤ 4 * (N : ℝ) := by
  have hy1 : 1 ≤ y := le_trans hw hwy
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ (N : ℝ) := le_trans hy1 hyN
    exact_mod_cast this
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlogw : 0 ≤ Real.log w := Real.log_nonneg hw
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hwpos : 0 < w := by linarith
  have hypos : 0 < y := by linarith
  have hwl : Real.log w ≤ Real.log (N : ℝ) := Real.log_le_log hwpos (le_trans hwy hyN)
  have hyl : Real.log y ≤ Real.log (N : ℝ) := Real.log_le_log hypos hyN
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have hsq : (Real.log (N : ℝ)) ^ 2 ≤ 4 * (N : ℝ) := log_sq_le_four_mul N hN1
  nlinarith [hlogw, hlogy, hwl, hyl, hsq, hlogN]


/-- `|a − b − c − d − e| ≤ |a| + |b| + |c| + |d| + |e|`. -/
private lemma cz_abs_chain (a b c d e : ℝ) : |a - b - c - d - e| ≤ |a| + |b| + |c| + |d| + |e| := by
  rw [abs_le]
  constructor <;>
    linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b, le_abs_self c,
      neg_abs_le c, le_abs_self d, neg_abs_le d, le_abs_self e, neg_abs_le e]

/-! ## The easy case `w·y ≤ N` -/

/-- **The `w·y ≤ N` case of the two-sided Graham `S₃` estimate.**  Here the pointwise splitting
`Bz_z(n) = Lz_z(n) − Λ(n)` (`grahamDefs.Lz_eq_vonMangoldt_add_Bz`) together with the easy case of
Graham's two-sided estimate (`hLzEasy`: the floor error there is controlled by `w·y`) and the
one-sided evaluation `Σ Λ·Bz_z = −N log(N/z) + O(N)` (`hMulBz`) already give the full estimate,
since the error `O(w·y)` is `O(N)`; the `n = 1` correction `log w·log y` is `O(N)`. -/
theorem cz_easy_case_of
    (hLzEasy : ∃ C : ℝ, 0 < C ∧ ∀ z₁ z₂ : ℝ, 1 ≤ z₁ → z₁ ≤ z₂ → ∀ N : ℕ, z₂ ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Lz z₁ n * Lz z₂ n) - (N : ℝ) * Real.log z₁|
        ≤ C * ((N : ℝ) + z₁ * z₂))
    (hMulBz : ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 1 ≤ z → ∀ N : ℕ, z ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * Bz z n)
        + (N : ℝ) * Real.log ((N : ℝ) / z)| ≤ C * (N : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ), 1 ≤ w → w ≤ y → ∀ N : ℕ, y ≤ (N : ℝ) →
      w * y ≤ (N : ℝ) →
      |(∑ n ∈ Finset.Icc 1 N, Bz w n * Bz y n) - (N : ℝ) * Real.log ((N : ℝ) / y)|
        ≤ C * (N : ℝ) := by
  obtain ⟨C₁, hC₁, hG⟩ := hLzEasy
  obtain ⟨C₂, hC₂, hQ⟩ := vonMangoldtSqEval_here
  obtain ⟨C₃, hC₃, hP⟩ := hMulBz
  refine ⟨2 * C₁ + C₂ + 2 * C₃ + 4, by linarith, ?_⟩
  intro w y hw hwy N hyN hwyN
  have hy1 : 1 ≤ y := le_trans hw hwy
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ (N : ℝ) := le_trans hy1 hyN
    exact_mod_cast this
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hypos : 0 < y := by linarith
  have hwN : w ≤ (N : ℝ) := le_trans hwy hyN
  have hlogmul : Real.log w * Real.log y ≤ 4 * (N : ℝ) := cz_log_mul_le hw hwy hyN
  have hA := hG w y hw hwy N hyN
  have hB := hQ N hN1
  have hC := hP w hw N hwN
  have hD := hP y hy1 N hyN
  have hid := cross_eq_split hw hy1 hN1
  have hdivw : Real.log ((N : ℝ) / w) = Real.log (N : ℝ) - Real.log w :=
    Real.log_div (ne_of_gt hNpos) (by linarith : w ≠ 0)
  have hdivy : Real.log ((N : ℝ) / y) = Real.log (N : ℝ) - Real.log y :=
    Real.log_div (ne_of_gt hNpos) (ne_of_gt hypos)
  have hkey : (∑ n ∈ Finset.Icc 1 N, Bz w n * Bz y n) - (N : ℝ) * Real.log ((N : ℝ) / y)
      = ((∑ n ∈ Finset.Icc 1 N, Lz w n * Lz y n) - (N : ℝ) * Real.log w)
        - ((∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2)
            - (N : ℝ) * Real.log (N : ℝ))
        - ((∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * Bz w n)
            + (N : ℝ) * Real.log ((N : ℝ) / w))
        - ((∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * Bz y n)
            + (N : ℝ) * Real.log ((N : ℝ) / y))
        - Real.log w * Real.log y := by
    rw [hid, hdivw, hdivy]
    ring
  have h1 := abs_le.mp hA
  have h2 := abs_le.mp hB
  have h3 := abs_le.mp hC
  have h4 := abs_le.mp hD
  have hlogmul_nn : 0 ≤ Real.log w * Real.log y :=
    mul_nonneg (Real.log_nonneg hw) (Real.log_nonneg hy1)
  have hwy2 : C₁ * ((N : ℝ) + w * y) ≤ 2 * C₁ * (N : ℝ) := by
    have h : (N : ℝ) + w * y ≤ 2 * (N : ℝ) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h hC₁.le]
  set A : ℝ := (∑ n ∈ Finset.Icc 1 N, Lz w n * Lz y n) - (N : ℝ) * Real.log w with hAdef
  set B : ℝ := (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n ^ 2)
      - (N : ℝ) * Real.log (N : ℝ) with hBdef
  set C : ℝ := (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * Bz w n)
      + (N : ℝ) * Real.log ((N : ℝ) / w) with hCdef
  set D : ℝ := (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * Bz y n)
      + (N : ℝ) * Real.log ((N : ℝ) / y) with hDdef
  set E : ℝ := Real.log w * Real.log y with hEdef
  have hbA : |A| ≤ 2 * C₁ * (N : ℝ) := by
    rw [hAdef]; exact abs_le.mpr ⟨by linarith [h1.1, hwy2], by linarith [h1.2, hwy2]⟩
  have hbB : |B| ≤ C₂ * (N : ℝ) := by rw [hBdef]; exact hB
  have hbC : |C| ≤ C₃ * (N : ℝ) := by rw [hCdef]; exact hC
  have hbD : |D| ≤ C₃ * (N : ℝ) := by rw [hDdef]; exact hD
  have hbE : |E| ≤ 4 * (N : ℝ) := by
    rw [hEdef, abs_of_nonneg hlogmul_nn]; exact hlogmul
  have hkey' : (∑ n ∈ Finset.Icc 1 N, Bz w n * Bz y n) - (N : ℝ) * Real.log ((N : ℝ) / y)
      = A - B - C - D - E := by
    rw [hkey, hAdef, hBdef, hCdef, hDdef, hEdef]
  rw [hkey']
  refine le_trans (cz_abs_chain A B C D E) ?_
  have hsum : |A| + |B| + |C| + |D| + |E|
      ≤ (2 * C₁ + C₂ + 2 * C₃ + 4) * (N : ℝ) := by
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := hNpos.le
    linarith [hbA, hbB, hbC, hbD, hbE]
  exact hsum
end

end Work.LinnikAreas2
