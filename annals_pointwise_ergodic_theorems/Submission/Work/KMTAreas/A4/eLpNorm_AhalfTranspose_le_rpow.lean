import Mathlib
import Submission.Work.KMTAreas.A4.AhalfTransposeBound
import Submission.Port.Aesm

namespace Work.KMTAreas.A4

open MeasureTheory

/-!
# The `ℓ^r` bound for the first dual function `Ã_N^*(h,g)`, `1 ≤ r`

`Work.KMTAreas.A4.AhalfTransposeBound` gives, for `h` supported in `[-N₀,N₀]` and `h, g` bounded
pointwise by `1`, the pointwise bound `‖Ã_N^*(h,g)‖ ≤ 1` (only the pointwise bounds are needed for
this) and the `ℓ¹` bound `‖Ã_N^*(h,g)‖_{ℓ¹} ≤ 2 ((N₀+N)) + 1` (only the support of `h` is needed
for this).  Interpolating between `ℓ¹` and `ℓ^∞` on `ℤ` with counting measure gives, for every
`1 ≤ r`,

`‖Ã_N^*(h,g)‖_{ℓ^r} ≤ (2 ((N₀+N)) + 1)^{1/r}`,

which is the statement of this file.  It is the form of the transposed single-scale bound used in
§5 (`A4`), where the exponent `r` is dictated by the interpolation step that follows.

The interpolation step itself is the general lemma `eLpNorm_count_le_rpow_of_ellOne_le` below: on
`ℤ` with counting measure, if `∑'_x ‖f x‖ ≤ A` and `‖f x‖ ≤ 1` for all `x`, then
`eLpNorm f r count ≤ A^{1/r}` for `1 ≤ r`.  (The point is just `∑'_x ‖f x‖^r ≤ ∑'_x ‖f x‖ ≤ A`
because `‖f x‖^r ≤ ‖f x‖` when `‖f x‖ ≤ 1 ≤ r`.)
-/

/-- **`ℓ¹`–`ℓ^∞` interpolation on `ℤ`.**  If `f : ℤ → ℂ` has `∑'_x ‖f x‖ ≤ A` and is bounded
pointwise by `1`, then for every `1 ≤ r` its `ℒ^r`-norm for counting measure is at most
`A^{1/r}`.

This is the elementary bound `∑_x ‖f x‖^r ≤ (sup_x ‖f x‖^{r-1}) ∑_x ‖f x‖ ≤ A`, valid because
`‖f x‖ ^ r ≤ ‖f x‖` for `0 ≤ ‖f x‖ ≤ 1 ≤ r`. -/
theorem eLpNorm_count_le_rpow_of_ellOne_le {f : ℤ → ℂ} {A r : ℝ} (hA : 0 ≤ A) (hr : 1 ≤ r)
    (hsum : Summable fun x : ℤ => ‖f x‖) (hle : ∑' x : ℤ, ‖f x‖ ≤ A)
    (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    MeasureTheory.eLpNorm f (ENNReal.ofReal r) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ ENNReal.ofReal (A ^ (1 / r)) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hrne : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hr0
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hrne ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_ofReal hr0.le]
  -- identify the `ℒ^r` integral with the `ℓ^r`-sum over the counting measure
  have hInt : ∫⁻ x : ℤ, ‖f x‖ₑ ^ r ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      = ∑' x : ℤ, ENNReal.ofReal (‖f x‖ ^ r) := by
    rw [MeasureTheory.lintegral_count]
    exact tsum_congr fun x => by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le]
  rw [hInt]
  -- `‖f x‖^r ≤ ‖f x‖` termwise dominates `∑'_x ‖f x‖^r` by `∑'_x ‖f x‖ ≤ A`
  have hbnd : ∑' x : ℤ, ENNReal.ofReal (‖f x‖ ^ r) ≤ ENNReal.ofReal A := by
    have hterm : ∀ x : ℤ, ENNReal.ofReal (‖f x‖ ^ r) ≤ ENNReal.ofReal ‖f x‖ := fun x =>
      ENNReal.ofReal_le_ofReal (Real.rpow_le_self_of_le_one (norm_nonneg _) (hbd x) hr)
    calc ∑' x : ℤ, ENNReal.ofReal (‖f x‖ ^ r)
        ≤ ∑' x : ℤ, ENNReal.ofReal ‖f x‖ := ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (∑' x : ℤ, ‖f x‖) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun x => norm_nonneg _) hsum).symm
      _ ≤ ENNReal.ofReal A := ENNReal.ofReal_le_ofReal hle
  calc (∑' x : ℤ, ENNReal.ofReal (‖f x‖ ^ r)) ^ (1 / r)
      ≤ (ENNReal.ofReal A) ^ (1 / r) := ENNReal.rpow_le_rpow hbnd (by positivity)
    _ = ENNReal.ofReal (A ^ (1 / r)) := ENNReal.ofReal_rpow_of_nonneg hA (by positivity)

/-- **The `ℓ^r` bound for the first dual function, `1 ≤ r`.**  If `h` is supported in `[-N₀,N₀]`
and `h`, `g` are bounded pointwise by `1`, then `Ã_N^*(h,g)` has `ℓ^r` norm at most
`(2 (N₀+N) + 1)^{1/r}`.

(Note that only the support of `h` is used, and only pointwise boundedness of `g`: the summand of
`Ã_N^*(h,g)` vanishes unless `h` is evaluated inside `[-N₀,N₀]`, independently of `g`.) -/
theorem eLpNorm_AhalfTranspose_le_rpow {N N₀ : ℕ} {P : Polynomial ℤ} {h g : ℤ → ℂ} (hhs : Work.Analysis.InverseTheory.SupportIn h N₀) (hg1 : ∀ x : ℤ, ‖g x‖ ≤ 1) (hh1 : ∀ x : ℤ, ‖h x‖ ≤ 1) {r : ℝ} (hr : 1 ≤ r) : MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.InverseTheory.AhalfTranspose N P h g x) (ENNReal.ofReal r) MeasureTheory.Measure.count ≤ ENNReal.ofReal ((2 * ((N₀ : ℝ) + (N : ℝ)) + 1) ^ (1 / r)) := by
  have hbd : ∀ x : ℤ, ‖Work.Analysis.InverseTheory.AhalfTranspose N P h g x‖ ≤ 1 := fun x => by
    simpa using Work.KMTAreas.A4.norm_AhalfTranspose_le N P h g zero_le_one zero_le_one
      (fun y => hh1 y) (fun y => hg1 y) x
  have hsupp : Work.Analysis.InverseTheory.SupportIn
      (fun x : ℤ => Work.Analysis.InverseTheory.AhalfTranspose N P h g x) (N₀ + N) :=
    Work.KMTAreas.A4.supportIn_AhalfTranspose (N := N) (M := N₀) (P := P) (g := g) hhs
  have hsum : Summable fun x : ℤ => ‖Work.Analysis.InverseTheory.AhalfTranspose N P h g x‖ :=
    summable_of_ne_finset_zero
      (s := Finset.Icc (-((N₀ + N : ℕ) : ℤ)) (((N₀ + N : ℕ) : ℤ)))
      (fun x hx => by
        simp only [norm_eq_zero]
        by_contra hc
        exact hx (Work.Analysis.InverseTheory.SupportIn.mem_Icc hsupp hc))
  have hle : ∑' x : ℤ, ‖Work.Analysis.InverseTheory.AhalfTranspose N P h g x‖
      ≤ 2 * ((N₀ : ℝ) + (N : ℝ)) + 1 := by
    have h := Work.Analysis.InverseTheory.ellOne_le_of_supportIn
      (Work.Analysis.InverseTheory.AhalfTranspose N P h g) (N₀ + N) hsupp (C := 1) hbd
    rw [Work.Analysis.InverseTheory.ellOne] at h
    simpa using h
  exact eLpNorm_count_le_rpow_of_ellOne_le (by positivity) hr hsum hle hbd

end Work.KMTAreas.A4
