import Mathlib
import Submission.Work.KMTAreas.A4.AhalfTransposeBound
import Submission.Port.Aesm

namespace Work.KMTAreas.A4

open MeasureTheory

/-!
# The `ℓ²` bound for the first dual function `Ã_N^*(h,g)`

`Work.KMTAreas.A4.AhalfTransposeBound` gives, for `h, g` supported in `[-N₀,N₀]` and bounded
pointwise by `1`, the pointwise bound `‖Ã_N^*(h,g)‖ ≤ 1` and the `ℓ¹` bound
`‖Ã_N^*(h,g)‖_{ℓ¹} ≤ 2 ((N₀+N)) + 1`.  Interpolating between `ℓ¹` and `ℓ^∞` on `ℤ` with counting
measure gives the `ℓ²` bound

`‖Ã_N^*(h,g)‖_{ℓ²} ≤ (2 ((N₀+N)) + 1)^{1/2}`,

which is the statement of this file.  This is the estimate that puts the transposed single-scale
averages into `ℓ²` uniformly in the parameters in §5 (`A4`).

The interpolation step itself is the general lemma `eLpNorm_two_count_le_sqrt_ellOne` below: on
`ℤ` with counting measure, if `∑'_x ‖f x‖ ≤ A` and `‖f x‖ ≤ 1` for all `x`, then
`eLpNorm f 2 count ≤ A^{1/2}`.  (Equivalently `∑'_x ‖f x‖² ≤ ∑'_x ‖f x‖ ≤ A`.)
-/

/-- **`ℓ¹`–`ℓ^∞` interpolation on `ℤ`.**  If `f : ℤ → ℂ` has `∑'_x ‖f x‖ ≤ A` and is bounded
pointwise by `1`, then its `ℒ²`-norm for counting measure is at most `A^{1/2}`.

This is the elementary bound `∑_x ‖f x‖² ≤ (sup_x ‖f x‖) ∑_x ‖f x‖ ≤ A`. -/
theorem eLpNorm_two_count_le_sqrt_ellOne {f : ℤ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    (hsum : Summable fun x : ℤ => ‖f x‖) (hle : ∑' x : ℤ, ‖f x‖ ≤ A)
    (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    MeasureTheory.eLpNorm f 2 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ ENNReal.ofReal (A ^ (1/2:ℝ)) := by
  -- `∑_x ‖f x‖²` is summable (it is dominated termwise by the summable `∑_x ‖f x‖`)
  have hsq : Summable fun x : ℤ => ‖f x‖ ^ 2 := hsum.of_nonneg_of_le
    (fun x => by positivity)
    (fun x => by rw [sq]; exact mul_le_of_le_one_right (norm_nonneg _) (hbd x))
  -- identify the `ℒ²`-norm with the `ℓ²`-sum over the counting measure
  have h2 : ((2:ENNReal)) ≠ 0 := by norm_num
  have h2t : ((2:ENNReal)) ≠ ⊤ := by norm_num
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) h2 h2t]
  have hexp : ((2:ENNReal).toReal) = 2 := by norm_num
  have htoRe : (1:ℝ) / ((2:ENNReal).toReal) = 1/2 := by norm_num
  rw [htoRe, hexp]
  have hInt : (∫⁻ x : ℤ, ‖f x‖ₑ ^ (2:ℝ) ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ))
      = ∑' x : ℤ, ENNReal.ofReal (‖f x‖ ^ 2) := by
    rw [MeasureTheory.lintegral_count]
    exact tsum_congr fun x => by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_two]
  rw [hInt]
  calc (∑' x : ℤ, ENNReal.ofReal (‖f x‖ ^ 2)) ^ (1/2:ℝ)
      ≤ (ENNReal.ofReal A) ^ (1/2:ℝ) := by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num : (0:ℝ) ≤ 1/2)
        rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun x : ℤ => ‖f x‖ ^ 2)
          (fun x => by positivity) hsq]
        exact ENNReal.ofReal_le_ofReal
          ((Summable.tsum_le_tsum
            (fun x => by rw [sq]; exact mul_le_of_le_one_right (norm_nonneg _) (hbd x))
            hsq hsum).trans hle)
    _ = ENNReal.ofReal (A ^ (1/2:ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg hA (by norm_num : (0:ℝ) ≤ 1/2)

/-- **The `ℓ²` bound for the first dual function.**  If `h` and `g` are supported in `[-N₀,N₀]`
and are bounded pointwise by `1`, then `Ã_N^*(h,g)` has `ℓ²` norm at most
`(2 (N₀+N) + 1)^{1/2}`. -/
theorem eLpNorm_AhalfTranspose_le {N N₀ : ℕ} {P : Polynomial ℤ} {h g : ℤ → ℂ} (hgs : Work.Analysis.InverseTheory.SupportIn g N₀) (hhs : Work.Analysis.InverseTheory.SupportIn h N₀) (hg1 : ∀ x : ℤ, ‖g x‖ ≤ 1) (hh1 : ∀ x : ℤ, ‖h x‖ ≤ 1) : MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.InverseTheory.AhalfTranspose N P h g x) 2 MeasureTheory.Measure.count ≤ ENNReal.ofReal ((2 * ((N₀ : ℝ) + (N : ℝ)) + 1) ^ (1 / 2 : ℝ)) := by
  obtain ⟨hpt, hell⟩ := Work.KMTAreas.A4.AhalfTransposeBound N P h g N₀ hhs hgs
    (Mh := 1) (Mg := 1) zero_le_one zero_le_one (fun x => hh1 x) (fun x => hg1 x)
  have hbd : ∀ x : ℤ, ‖Work.Analysis.InverseTheory.AhalfTranspose N P h g x‖ ≤ 1 :=
    fun x => by simpa using hpt x
  have hsupp : Work.Analysis.InverseTheory.SupportIn
      (fun x : ℤ => Work.Analysis.InverseTheory.AhalfTranspose N P h g x) (N₀ + N) :=
    Work.KMTAreas.A4.supportIn_AhalfTranspose (N := N) (M := N₀) hhs
  have hsum : Summable fun x : ℤ => ‖Work.Analysis.InverseTheory.AhalfTranspose N P h g x‖ :=
    summable_of_ne_finset_zero (s := Finset.Icc (-((N₀ + N : ℕ) : ℤ)) (((N₀ + N : ℕ) : ℤ)))
      (fun x hx => by
        simp only [norm_eq_zero]
        by_contra hc
        exact hx (Work.Analysis.InverseTheory.SupportIn.mem_Icc hsupp hc))
  have hle : ∑' x : ℤ, ‖Work.Analysis.InverseTheory.AhalfTranspose N P h g x‖
      ≤ 2 * ((N₀ : ℝ) + (N : ℝ)) + 1 := by
    have h := hell
    rw [Work.Analysis.InverseTheory.ellOne] at h
    simpa using h
  exact Work.KMTAreas.A4.eLpNorm_two_count_le_sqrt_ellOne (by positivity) hsum hle hbd

end Work.KMTAreas.A4
