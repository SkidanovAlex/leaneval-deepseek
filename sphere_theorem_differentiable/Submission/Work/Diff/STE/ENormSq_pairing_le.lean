import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cauchy–Schwarz for the energy pairing `Σ_l L2re (∂^l v) (∂^l u)`

The `Hᵏ` energy of the STE development is

`ENormSq k f = ∑_{l : Fin k → ι} ∫_{unitCube} ‖pdVec k l f‖²`

and the companion pairing of two functions is

`∑_{l} L2re (pdVec k l v) (pdVec k l u)`,  with  `L2re f g = Re ∫_{unitCube} f · conj g`.

The bilinear form `B(v,u) := ∑_l L2re (∂^l v) (∂^l u)` is the real inner product of the jets of
`v` and `u` in the direct sum of the Hilbert spaces `L²(cube)`, one summand for each multi-index
`l`; in particular it is symmetric and positive semi-definite, `B(f,f) = ENormSq k f ≥ 0`.  The
lemma `ENormSq_pairing_le` is therefore nothing but Cauchy–Schwarz for `B`, expressed without
any Hilbert-space machinery.

The proof is the elementary two-step reduction:

* **One multi-index.**  Cauchy–Schwarz for the `L²` pairing of a single pair of functions,
  `|L2re f g| ≤ √(∫ ‖f‖²) · √(∫ ‖g‖²)` (`L2re_abs_le_sqrt`).  This is `L²`–Hölder with conjugate
  exponents `2,2`, applied to the *real* functions `‖f‖` and `‖g‖`: nothing but
  `Integrable (fun x => ‖f x‖ ^ 2)` is needed, no continuity, because the `MemLp 2` hypothesis is
  obtained from that integrability via `memLp_two_iff_integrable_sq`.
* **Summing over the multi-indices.**  With `|c l| ≤ √(a l) · √(b l)` for `c l := L2re (∂^l v) (∂^l u)`
  and `a l, b l ≥ 0` the integrals of `‖∂^l v‖²`, resp. `‖∂^l u‖²`, the triangle inequality and
  Cauchy–Schwarz in `ℝ^n` (`Finset.sum_mul_sq_le_sq_mul_sq`) give
  `|∑_l c l|² ≤ (∑_l a l) · (∑_l b l)`.
-/

noncomputable section

open MeasureTheory BigOperators ComplexConjugate Filter

namespace Work.Diff.STE

/-- **Cauchy–Schwarz for the `L²` pairing on one cube.**  If the *squares of the norms* of `f` and
`g` are integrable over the unit cube (no regularity whatsoever is assumed on `f` and `g`
themselves, only the stated integrability), then

`|L2re f g| ≤ √(∫_{cube} ‖f‖²) · √(∫_{cube} ‖g‖²)`.

This is `L²`–Hölder (`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` with `p = q = 2`) applied
to the nonnegative functions `‖f‖`, `‖g‖`; the `MemLp 2` hypotheses are read off from the
integrability of the squares by `MeasureTheory.memLp_two_iff_integrable_sq`, the only point where
almost strong measurability enters being `‖f‖ = √(‖f‖²)` (continuous image of an
`AEStronglyMeasurable` function). -/
lemma L2re_abs_le_sqrt {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : (ι → ℝ) → ℂ)
    (hf : Integrable (fun x : ι → ℝ => ‖f x‖ ^ 2) (volume.restrict (unitCube (ι := ι))))
    (hg : Integrable (fun x : ι → ℝ => ‖g x‖ ^ 2) (volume.restrict (unitCube (ι := ι)))) :
    |L2re f g| ≤ Real.sqrt (∫ x in unitCube (ι := ι), ‖f x‖ ^ 2)
      * Real.sqrt (∫ x in unitCube (ι := ι), ‖g x‖ ^ 2) := by
  set μ : Measure (ι → ℝ) := volume.restrict (unitCube (ι := ι)) with hμ
  have hf' : Integrable (fun x : ι → ℝ => ‖f x‖ ^ 2) μ := hf
  have hg' : Integrable (fun x : ι → ℝ => ‖g x‖ ^ 2) μ := hg
  -- `‖f‖` (resp. `‖g‖`) is `AEStronglyMeasurable`: it is `√(‖f‖²)`, a continuous function of the
  -- integrable function `‖f‖²`.
  have haV : AEStronglyMeasurable (fun x : ι → ℝ => ‖f x‖) μ := by
    have h1 : AEStronglyMeasurable (fun x : ι → ℝ => Real.sqrt (‖f x‖ ^ 2)) μ :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hf'.aestronglyMeasurable
    simpa only [Real.sqrt_sq (norm_nonneg _)] using h1
  have hmV : MemLp (fun x : ι → ℝ => ‖f x‖) 2 μ :=
    (memLp_two_iff_integrable_sq haV).2 hf'
  have haU : AEStronglyMeasurable (fun x : ι → ℝ => ‖g x‖) μ := by
    have h1 : AEStronglyMeasurable (fun x : ι → ℝ => Real.sqrt (‖g x‖ ^ 2)) μ :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hg'.aestronglyMeasurable
    simpa only [Real.sqrt_sq (norm_nonneg _)] using h1
  have hmU : MemLp (fun x : ι → ℝ => ‖g x‖) 2 μ :=
    (memLp_two_iff_integrable_sq haU).2 hg'
  -- Hölder with conjugate exponents `2, 2`.
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun _ => norm_nonneg _) (by simpa using hmV) (by simpa using hmU)
  -- Triangle inequality for the Bochner integral, with `‖f x * conj (g x)‖ = ‖f x‖ * ‖g x‖`.
  have h4 : ‖∫ x, f x * star (g x) ∂μ‖ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [norm_mul, norm_star]
  -- `L2re f g` is the real part of `∫ f · conj g`.
  have h5 : |L2re f g| ≤ ‖∫ x, f x * star (g x) ∂μ‖ := by
    simp only [L2re]
    exact Complex.abs_re_le_norm _
  refine h5.trans (h4.trans (hholder.trans_eq ?_))
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow]

/-- **Cauchy–Schwarz for the `Hᵏ` energy pairing.**  For functions `v`, `u` whose derivatives of
order `≤ k` have square-integrable norms over the unit cube, the pairing
`Σ_{l : Fin k → ι} L2re (∂^l v) (∂^l u)` is bounded by the geometric mean of the two energies
`ENormSq k v`, `ENormSq k u`.

Equivalently: the bilinear form `B(v,u) = Σ_l L2re (∂^l v) (∂^l u)` is a symmetric positive
semi-definite form on the jets of `v`, `u` (`B(f,f) = ENormSq k f`), and this is Cauchy–Schwarz
for it.  No regularity of `v`, `u` beyond the stated integrability is used. -/
theorem ENormSq_pairing_le {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (v u : (ι → ℝ) → ℂ)
    (hv : ∀ l : Fin k → ι, MeasureTheory.Integrable
      (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec k l v x‖ ^ 2)
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι))))
    (hu : ∀ l : Fin k → ι, MeasureTheory.Integrable
      (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec k l u x‖ ^ 2)
      (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := ι)))) :
    |∑ l : Fin k → ι, Work.Diff.STE.L2re (Work.Diff.STE.pdVec k l v) (Work.Diff.STE.pdVec k l u)| ^ 2
      ≤ Work.Diff.STE.ENormSq k v * Work.Diff.STE.ENormSq k u := by
  -- Per multi-index Cauchy–Schwarz, `|c l| ≤ √(a l) · √(b l)`.
  have hcs : ∀ l : Fin k → ι,
      |L2re (pdVec k l v) (pdVec k l u)|
        ≤ Real.sqrt (∫ x in unitCube, ‖pdVec k l v x‖ ^ 2)
          * Real.sqrt (∫ x in unitCube, ‖pdVec k l u x‖ ^ 2) :=
    fun l => L2re_abs_le_sqrt _ _ (hv l) (hu l)
  -- The single integrals are nonnegative, so `(√(a l))² = a l`.
  have hA : ∀ l : Fin k → ι, 0 ≤ ∫ x in unitCube, ‖pdVec k l v x‖ ^ 2 :=
    fun l => integral_nonneg (fun x => sq_nonneg _)
  have hB : ∀ l : Fin k → ι, 0 ≤ ∫ x in unitCube, ‖pdVec k l u x‖ ^ 2 :=
    fun l => integral_nonneg (fun x => sq_nonneg _)
  -- Triangle inequality over the multi-indices.
  have h1 : |∑ l : Fin k → ι, L2re (pdVec k l v) (pdVec k l u)|
      ≤ ∑ l : Fin k → ι, |L2re (pdVec k l v) (pdVec k l u)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : (∑ l : Fin k → ι, |L2re (pdVec k l v) (pdVec k l u)|)
      ≤ ∑ l : Fin k → ι, Real.sqrt (∫ x in unitCube, ‖pdVec k l v x‖ ^ 2)
          * Real.sqrt (∫ x in unitCube, ‖pdVec k l u x‖ ^ 2) :=
    Finset.sum_le_sum (fun l _ => hcs l)
  -- Cauchy–Schwarz in `ℝ^n` for the sequences `√(a l)`, `√(b l)`.
  have h3 : (∑ l : Fin k → ι, Real.sqrt (∫ x in unitCube, ‖pdVec k l v x‖ ^ 2)
          * Real.sqrt (∫ x in unitCube, ‖pdVec k l u x‖ ^ 2)) ^ 2
      ≤ (∑ l : Fin k → ι, ∫ x in unitCube, ‖pdVec k l v x‖ ^ 2)
        * (∑ l : Fin k → ι, ∫ x in unitCube, ‖pdVec k l u x‖ ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k → ι))
      (fun l => Real.sqrt (∫ x in unitCube, ‖pdVec k l v x‖ ^ 2))
      (fun l => Real.sqrt (∫ x in unitCube, ‖pdVec k l u x‖ ^ 2))
    rwa [Finset.sum_congr rfl (fun l _ => Real.sq_sqrt (hA l)),
      Finset.sum_congr rfl (fun l _ => Real.sq_sqrt (hB l))] at h
  -- Square the triangle inequality (both sides are nonnegative).
  have h4 : |∑ l : Fin k → ι, L2re (pdVec k l v) (pdVec k l u)| ^ 2
      ≤ (∑ l : Fin k → ι, Real.sqrt (∫ x in unitCube, ‖pdVec k l v x‖ ^ 2)
          * Real.sqrt (∫ x in unitCube, ‖pdVec k l u x‖ ^ 2)) ^ 2 := by
    have hnon : 0 ≤ ∑ l : Fin k → ι, Real.sqrt (∫ x in unitCube, ‖pdVec k l v x‖ ^ 2)
          * Real.sqrt (∫ x in unitCube, ‖pdVec k l u x‖ ^ 2) :=
      Finset.sum_nonneg (fun l _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
  have hmain : |∑ l : Fin k → ι, L2re (pdVec k l v) (pdVec k l u)| ^ 2
      ≤ (∑ l : Fin k → ι, ∫ x in unitCube, ‖pdVec k l v x‖ ^ 2)
        * (∑ l : Fin k → ι, ∫ x in unitCube, ‖pdVec k l u x‖ ^ 2) := h4.trans h3
  simpa only [ENormSq] using hmain

end Work.Diff.STE
