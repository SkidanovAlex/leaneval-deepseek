import Mathlib
import Submission.MaynardFunctionals
import Submission.SieveWeight
import Submission.Commons.Analysis.Calculus.hasDerivAt_integral_Ioi_of_continuous
import Submission.Commons.Analysis.Calculus.contDiff_integral_Ioi
import Submission.Commons.MeasureTheory.Integral.integral_fintype_prod_indicator_Ioi

/-!
# The antiderivative conversion of the Polymath8a §5.3 tensor data

Given one-variable components `G j i` (continuous, compactly supported), the
"antiderivative" family

  `anti ψ G i u = ψ u * ∫_{s > u} G i s`

(with `ψ` a smooth cutoff equal to `1` on `[0,∞)`) has

  `deriv (anti ψ G i) u = -(G i u)`   for `u > 0`,   `anti ψ G i 0 = ∫_{s>0} G i s`.

Consequently the sieve coefficients `tpAlpha`, `tpBeta` of the tensor data
`f j i := anti ψ (G j) i` are exactly the functionals of the tensor sum
`t ↦ Σ_j c j * ∏ i, G j i (t i)`:

  `tpAlpha c f = ∫_{[0,∞)^k} (Σ_j c j ∏ i, G j i (t i))²`,
  `tpBeta c f i = ∫_{[0,∞)^{k-1}} (∫_{x>0} Σ_j c j ∏ i, G j i (·, x))²`.

This is the interface consumed by the convergence step: a uniform approximation
`G ≈ g` of `g = ∂₁···∂_k f₃` then gives `tpAlpha ≈ Ĩ(f₃)`, `tpBeta ≈ J̃_i(f₃)`.
-/

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

/-- The antiderivative family of a one-variable component `G i`, cut off by `ψ`. -/
def anti (ψ : ℝ → ℝ) {k : ℕ} (G : Fin k → ℝ → ℝ) (i : Fin k) : ℝ → ℝ :=
  fun u => ψ u * ∫ s in Set.Ioi u, G i s

@[simp] theorem anti_apply (ψ : ℝ → ℝ) {k : ℕ} (G : Fin k → ℝ → ℝ) (i : Fin k) (u : ℝ) :
    anti ψ G i u = ψ u * ∫ s in Set.Ioi u, G i s := rfl

/-- On `(0,∞)` the antiderivative family has derivative `-G i`. -/
theorem deriv_anti_eq_of_pos {ψ : ℝ → ℝ} (hψ1 : ∀ u : ℝ, 0 ≤ u → ψ u = 1)
    {G : ℝ → ℝ} (hGc : Continuous G) (hGi : Integrable G)
    (hGv : ∃ R : ℝ, ∀ x : ℝ, R ≤ x → G x = 0) {t : ℝ} (ht : 0 < t) :
    deriv (fun u : ℝ => ψ u * ∫ s in Set.Ioi u, G s) t = - G t := by
  have hev : (fun u : ℝ => ψ u * ∫ s in Set.Ioi u, G s)
      =ᶠ[𝓝 t] (fun u : ℝ => ∫ s in Set.Ioi u, G s) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu
    rw [hψ1 u hu.le, one_mul]
  rw [hev.deriv_eq]
  exact (Commons.Analysis.Calculus.hasDerivAt_integral_Ioi_of_continuous G hGc hGi hGv t).deriv

/-- The value at `0` of the antiderivative family is the halfline integral. -/
theorem anti_zero_of_eq_one {ψ : ℝ → ℝ} (hψ0 : ψ 0 = 1) {k : ℕ} (G : Fin k → ℝ → ℝ)
    (i : Fin k) : anti ψ G i 0 = ∫ s in Set.Ioi (0:ℝ), G i s := by
  simp [anti, hψ0]

/-- **The antiderivative replaces the derivative.**  For `u > 0` the product of the
derivatives of two antiderivative families equals the product of the original components. -/
theorem deriv_anti_mul_eq_of_pos {ψ : ℝ → ℝ} (hψ1 : ∀ u : ℝ, 0 ≤ u → ψ u = 1)
    {G G' : ℝ → ℝ} (hGc : Continuous G) (hGi : Integrable G)
    (hGv : ∃ R : ℝ, ∀ x : ℝ, R ≤ x → G x = 0)
    (hGc' : Continuous G') (hGi' : Integrable G') (hGv' : ∃ R : ℝ, ∀ x : ℝ, R ≤ x → G' x = 0)
    {t : ℝ} (ht : 0 < t) :
    deriv (fun u : ℝ => ψ u * ∫ s in Set.Ioi u, G s) t
        * deriv (fun u : ℝ => ψ u * ∫ s in Set.Ioi u, G' s) t
      = G t * G' t := by
  rw [deriv_anti_eq_of_pos hψ1 hGc hGi hGv ht, deriv_anti_eq_of_pos hψ1 hGc' hGi' hGv' ht]
  ring

/-- **The halfline integral of a product of derivatives.**  For two antiderivative
families the halfline integral of the product of the derivatives equals the halfline
integral of the product of the components. -/
theorem integral_deriv_anti_mul {ψ : ℝ → ℝ} (hψ1 : ∀ u : ℝ, 0 ≤ u → ψ u = 1)
    {G G' : ℝ → ℝ} (hGc : Continuous G) (hGi : Integrable G)
    (hGv : ∃ R : ℝ, ∀ x : ℝ, R ≤ x → G x = 0)
    (hGc' : Continuous G') (hGi' : Integrable G') (hGv' : ∃ R : ℝ, ∀ x : ℝ, R ≤ x → G' x = 0) :
    (∫ t in Set.Ioi (0:ℝ),
        deriv (fun u : ℝ => ψ u * ∫ s in Set.Ioi u, G s) t
          * deriv (fun u : ℝ => ψ u * ∫ s in Set.Ioi u, G' s) t)
      = ∫ t in Set.Ioi (0:ℝ), G t * G' t := by
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  exact deriv_anti_mul_eq_of_pos hψ1 hGc hGi hGv hGc' hGi' hGv' ht

end

end Commons.NumberTheory.MaynardSieve

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

set_option maxHeartbeats 2000000

/-- A bounded measurable function with compact support on `ι → ℝ` is integrable. -/
lemma integrable_of_hasCompactSupport_of_bound {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℝ}
    (hcs : HasCompactSupport f) (hmeas : Measurable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) : Integrable f volume := by
  have hS : volume (tsupport f) < ⊤ := hcs.isCompact.measure_lt_top
  have hInt : IntegrableOn f (tsupport f) volume :=
    IntegrableOn.of_bound hS (hmeas.aestronglyMeasurable.mono_measure Measure.restrict_le_self)
      C (Filter.Eventually.of_forall hC)
  have hind := hInt.integrable_indicator hcs.isCompact.measurableSet
  refine hind.congr ?_
  filter_upwards with x
  by_cases hx : x ∈ tsupport f
  · simp [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    exact (image_eq_zero_of_notMem_tsupport hx).symm

/-- The pointwise product of two compactly supported real functions has compact support. -/
lemma hasCompactSupport_mul {f g : ℝ → ℝ} (hf : HasCompactSupport f)
    (hg : HasCompactSupport g) : HasCompactSupport (fun s => f s * g s) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := tsupport f ∪ tsupport g)
    (hf.union hg) ?_
  intro x hx
  rw [Function.mem_support] at hx
  rw [Set.mem_union]
  by_contra hcon
  push_neg at hcon
  exact hx (by rw [image_eq_zero_of_notMem_tsupport hcon.1, zero_mul])

/-- A product of one-dimensional `Ici 0`-indicators of continuous compactly supported
functions is integrable. -/
lemma integrable_prod_indicator_Ici {ι : Type*} [Fintype ι] (H : ι → ℝ → ℝ)
    (hHc : ∀ i, Continuous (H i)) (hHcs : ∀ i, HasCompactSupport (H i)) :
    Integrable (fun t : ι → ℝ => ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H i s) (t i)) := by
  have hmeas : Measurable (fun t : ι → ℝ =>
      ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H i s) (t i)) :=
    Finset.measurable_prod _ fun i _ =>
      ((hHc i).measurable.indicator measurableSet_Ici).comp (measurable_pi_apply i)
  choose C hC0 hCbd using fun i => exists_abs_bound_of_hasCompactSupport (H i) (hHcs i) (hHc i)
  refine integrable_of_hasCompactSupport_of_bound ?_ hmeas (C := ∏ i, C i) ?_
  · refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_univ_pi fun i => (hHcs i)) ?_
    intro t ht
    rw [Function.mem_support] at ht
    rw [Set.mem_univ_pi]
    by_contra hcon
    push_neg at hcon
    obtain ⟨i, hi⟩ := hcon
    have hzero : H i (t i) = 0 := image_eq_zero_of_notMem_tsupport hi
    exact ht (Finset.prod_eq_zero (Finset.mem_univ i) (by
      by_cases h : t i ∈ Set.Ici (0:ℝ)
      · rw [Set.indicator_of_mem h, hzero]
      · rw [Set.indicator_of_notMem h]))
  · intro t
    calc ‖∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H i s) (t i)‖
        = ∏ i, ‖(Set.Ici (0:ℝ)).indicator (fun s => H i s) (t i)‖ := norm_prod _ _
      _ ≤ ∏ i, C i := by
          refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
          by_cases h : t i ∈ Set.Ici (0:ℝ)
          · rw [Set.indicator_of_mem h, Real.norm_eq_abs]; exact hCbd i (t i)
          · rw [Set.indicator_of_notMem h, norm_zero]; exact hC0 i

/-- The indicator of the orthant, as a product of one-dimensional indicators. -/
def orthInd {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∏ i, (Set.Ici (0:ℝ)).indicator (fun _ => (1:ℝ)) (x i)

lemma orthInd_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ orthInd x :=
  Finset.prod_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _

lemma orthInd_le_one {ι : Type*} [Fintype ι] (x : ι → ℝ) : orthInd x ≤ 1 := by
  refine Finset.prod_le_one₀ (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    (fun i _ => ?_)
  by_cases h : x i ∈ Set.Ici (0:ℝ)
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

lemma orthInd_eq_one {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    orthInd x = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  exact Set.indicator_of_mem (Set.mem_Ici.mpr (hx i).le) _

lemma orthInd_mul_prod {ι : Type*} [Fintype ι] (H : ι → ℝ → ℝ) (x : ι → ℝ) :
    orthInd x * ∏ i, H i (x i)
      = ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H i s) (x i) := by
  rw [orthInd, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : x i ∈ Set.Ici (0:ℝ)
  · simp only [Set.indicator_of_mem h, one_mul]
  · simp only [Set.indicator_of_notMem h, zero_mul]

/-- Fubini form of the squared-integral identity for a weighted tensor sum. -/
lemma sum_integral_prod_eq_integral_sq {ι : Type*} [Fintype ι] {J : ℕ}
    (H : Fin J → ι → ℝ → ℝ) (hHc : ∀ j i, Continuous (H j i))
    (hHcs : ∀ j i, HasCompactSupport (H j i)) (w c : Fin J → ℝ) :
    (∑ j : Fin J, ∑ j' : Fin J, c j * c j' * (w j * w j' *
        ∫ t : ι → ℝ,
          ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H j i s * H j' i s) (t i)))
      = ∫ t : ι → ℝ,
          (∑ j : Fin J, c j * w j * ∏ i, H j i (t i)) ^ 2 * orthInd t := by
  have hInt : ∀ j j' : Fin J, Integrable (fun t : ι → ℝ =>
      ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H j i s * H j' i s) (t i)) :=
    fun j j' => integrable_prod_indicator_Ici _
      (fun i => (hHc j i).mul (hHc j' i)) (fun i => hasCompactSupport_mul (hHcs j i) (hHcs j' i))
  have hpoint : (fun t : ι → ℝ =>
        (∑ j : Fin J, c j * w j * ∏ i, H j i (t i)) ^ 2 * orthInd t)
      = fun t : ι → ℝ => ∑ j : Fin J, ∑ j' : Fin J, (c j * c j' * (w j * w j')) *
          ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H j i s * H j' i s) (t i) := by
    funext t
    have h1 : (∑ j : Fin J, c j * w j * ∏ i, H j i (t i)) ^ 2
        = ∑ j : Fin J, ∑ j' : Fin J,
            (c j * w j * ∏ i, H j i (t i)) * (c j' * w j' * ∏ i, H j' i (t i)) := by
      rw [sq, Finset.sum_mul_sum]
    rw [h1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j' _ => ?_
    have h2 : (∏ i, H j i (t i)) * (∏ i, H j' i (t i)) * orthInd t
        = ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H j i s * H j' i s) (t i) := by
      rw [← orthInd_mul_prod (fun i s => H j i s * H j' i s) t, mul_comm]
      congr 1
      rw [Finset.prod_mul_distrib]
    calc (c j * w j * ∏ i, H j i (t i)) * (c j' * w j' * ∏ i, H j' i (t i)) * orthInd t
        = (c j * c j' * (w j * w j')) *
            ((∏ i, H j i (t i)) * (∏ i, H j' i (t i)) * orthInd t) := by ring
      _ = (c j * c j' * (w j * w j')) *
            ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => H j i s * H j' i s) (t i) := by rw [h2]
  rw [hpoint]
  rw [MeasureTheory.integral_finsetSum (Finset.univ) (fun j _ =>
        MeasureTheory.integrable_finsetSum _ (fun j' _ => (hInt j j').const_mul _))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_finsetSum (Finset.univ) (fun j' _ => (hInt j j').const_mul _)]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [MeasureTheory.integral_const_mul]
  ring

/-- **The `α`-coefficient of the antiderivative tensor data** equals the squared integral
of the tensor sum over the orthant. -/
theorem tpAlpha_anti {J k : ℕ} {ψ : ℝ → ℝ} (hψ1 : ∀ u : ℝ, 0 ≤ u → ψ u = 1)
    (G : Fin J → Fin k → ℝ → ℝ) (hGc : ∀ j i, Continuous (G j i))
    (hGcs : ∀ j i, HasCompactSupport (G j i))
    (hGi : ∀ j i, Integrable (G j i))
    (hGv : ∀ j i, ∃ R : ℝ, ∀ x : ℝ, R ≤ x → G j i x = 0) (c : Fin J → ℝ) :
    tpAlpha c (fun j i => anti ψ (G j) i)
      = ∫ t : Fin k → ℝ, (∑ j : Fin J, c j * ∏ i, G j i (t i)) ^ 2 * orthInd t := by
  rw [tpAlpha]
  have hA : ∀ j j' : Fin J,
      (∏ i : Fin k, ∫ t in Set.Ioi (0:ℝ),
          deriv (anti ψ (G j) i) t * deriv (anti ψ (G j') i) t)
        = ∏ i : Fin k, ∫ t in Set.Ioi (0:ℝ), G j i t * G j' i t := by
    intro j j'
    refine Finset.prod_congr rfl fun i _ => ?_
    show (∫ t in Set.Ioi (0:ℝ),
        deriv (fun u : ℝ => ψ u * ∫ s in Set.Ioi u, G j i s) t
          * deriv (fun u : ℝ => ψ u * ∫ s in Set.Ioi u, G j' i s) t)
      = ∫ t in Set.Ioi (0:ℝ), G j i t * G j' i t
    exact integral_deriv_anti_mul hψ1 (hGc j i) (hGi j i) (hGv j i)
      (hGc j' i) (hGi j' i) (hGv j' i)
  simp only [hA]
  have hB : ∀ j j' : Fin J,
      (∏ i : Fin k, ∫ t in Set.Ioi (0:ℝ), G j i t * G j' i t)
        = ∫ t : Fin k → ℝ,
            ∏ i, (Set.Ici (0:ℝ)).indicator (fun s => G j i s * G j' i s) (t i) := by
    intro j j'
    have h1 : (∏ i : Fin k, ∫ t in Set.Ioi (0:ℝ), G j i t * G j' i t)
        = ∏ i : Fin k, ∫ t : ℝ,
            (Set.Ici (0:ℝ)).indicator (fun s => G j i s * G j' i s) t := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [MeasureTheory.integral_indicator measurableSet_Ici]
      exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioi_ae_eq_Ici
    rw [h1, ← MeasureTheory.integral_fintype_prod_volume_eq_prod
      (f := fun i (s : ℝ) => (Set.Ici (0:ℝ)).indicator (fun s => G j i s * G j' i s) s)]
  simp only [hB]
  simpa using (sum_integral_prod_eq_integral_sq G hGc hGcs (fun _ => (1:ℝ)) c)

/-- Splitting a product over `univ` at one point, in terms of the subtype of the
remaining indices. -/
lemma prod_erase_eq_prod_subtype {k : ℕ} (i : Fin k) (H : Fin k → ℝ) :
    (∏ l ∈ Finset.univ.erase i, H l) = ∏ l : {l : Fin k // l ≠ i}, H l.1 := by
  classical
  rw [Finset.prod_subtype (s := Finset.univ.erase i) (p := fun x : Fin k => x ≠ i)
    (by intro x; simp [Finset.mem_erase]) H]

/-- The subtype-product form of the `β`-coefficient. -/
noncomputable def tpBetaT {k J : ℕ} (c : Fin J → ℝ) (f : Fin J → Fin k → ℝ → ℝ)
    (i : Fin k) : ℝ :=
  ∑ j : Fin J, ∑ j' : Fin J, c j * c j' * (f j i 0) * (f j' i 0) *
    ∏ l : {l : Fin k // l ≠ i},
      (∫ t : ℝ in Set.Ioi 0, deriv (f j l.1) t * deriv (f j' l.1) t)

theorem tpBeta_eq_tpBetaT {k J : ℕ} (c : Fin J → ℝ) (f : Fin J → Fin k → ℝ → ℝ) (i : Fin k) :
    tpBeta c f i = tpBetaT c f i := by
  rw [tpBeta, tpBetaT]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  rw [prod_erase_eq_prod_subtype]

/-- **The `β`-coefficient of the antiderivative tensor data** equals the marginal squared
integral of the tensor sum over the orthant. -/
theorem tpBeta_anti {J k : ℕ} {ψ : ℝ → ℝ} (hψ0 : ψ 0 = 1)
    (hψ1 : ∀ u : ℝ, 0 ≤ u → ψ u = 1)
    (G : Fin J → Fin k → ℝ → ℝ) (hGc : ∀ j i, Continuous (G j i))
    (hGcs : ∀ j i, HasCompactSupport (G j i))
    (hGi : ∀ j i, Integrable (G j i))
    (hGv : ∀ j i, ∃ R : ℝ, ∀ x : ℝ, R ≤ x → G j i x = 0) (c : Fin J → ℝ) (i₀ : Fin k) :
    tpBeta c (fun j i => anti ψ (G j) i) i₀
      = ∫ t : {l : Fin k // l ≠ i₀} → ℝ,
          (∫ x in Set.Ioi (0:ℝ),
              ∑ j : Fin J, c j * ∏ l, G j l (extendAt i₀ x t l)) ^ 2 * orthInd t := by
  rw [tpBeta_eq_tpBetaT, tpBetaT]
  have h0 : ∀ j : Fin J, anti ψ (G j) i₀ 0 = ∫ x in Set.Ioi (0:ℝ), G j i₀ x :=
    fun j => anti_zero_of_eq_one hψ0 (G j) i₀
  have hA : ∀ j j' : Fin J,
      (∏ l : {l : Fin k // l ≠ i₀},
          (∫ t : ℝ in Set.Ioi 0, deriv (anti ψ (G j) l.1) t * deriv (anti ψ (G j') l.1) t))
        = ∏ l : {l : Fin k // l ≠ i₀},
          (∫ t : ℝ in Set.Ioi 0, G j l.1 t * G j' l.1 t) := by
    intro j j'
    refine Finset.prod_congr rfl fun l _ => ?_
    show (∫ t in Set.Ioi (0:ℝ), deriv (fun u : ℝ => ψ u * ∫ s in Set.Ioi u, G j l.1 s) t
          * deriv (fun u : ℝ => ψ u * ∫ s in Set.Ioi u, G j' l.1 s) t)
      = ∫ t in Set.Ioi (0:ℝ), G j l.1 t * G j' l.1 t
    exact integral_deriv_anti_mul hψ1 (hGc j l.1) (hGi j l.1) (hGv j l.1)
      (hGc j' l.1) (hGi j' l.1) (hGv j' l.1)
  simp only [h0, hA]
  have hB : ∀ j j' : Fin J,
      (∏ l : {l : Fin k // l ≠ i₀}, (∫ t : ℝ in Set.Ioi 0, G j l.1 t * G j' l.1 t))
        = ∫ t : {l : Fin k // l ≠ i₀} → ℝ,
            ∏ l, (Set.Ici (0:ℝ)).indicator (fun s => G j l.1 s * G j' l.1 s) (t l) := by
    intro j j'
    have h1 : (∏ l : {l : Fin k // l ≠ i₀}, (∫ t : ℝ in Set.Ioi 0, G j l.1 t * G j' l.1 t))
        = ∏ l : {l : Fin k // l ≠ i₀}, ∫ t : ℝ,
            (Set.Ici (0:ℝ)).indicator (fun s => G j l.1 s * G j' l.1 s) t := by
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [MeasureTheory.integral_indicator measurableSet_Ici]
      exact MeasureTheory.setIntegral_congr_set MeasureTheory.Ioi_ae_eq_Ici
    rw [h1, ← MeasureTheory.integral_fintype_prod_volume_eq_prod
      (f := fun (l : {l : Fin k // l ≠ i₀}) (s : ℝ) =>
        (Set.Ici (0:ℝ)).indicator (fun s => G j l.1 s * G j' l.1 s) s)]
  simp only [hB]
  have hpt : ∀ t : {l : Fin k // l ≠ i₀} → ℝ,
      (∫ x in Set.Ioi (0:ℝ), ∑ j : Fin J, c j * ∏ l, G j l (extendAt i₀ x t l))
        = ∑ j : Fin J, c j * (∫ x in Set.Ioi (0:ℝ), G j i₀ x) *
            ∏ l : {l : Fin k // l ≠ i₀}, G j l.1 (t l) := by
    intro t
    have hfac : ∀ (j : Fin J) (x : ℝ),
        (∏ l : Fin k, G j l (extendAt i₀ x t l))
          = G j i₀ x * ∏ l : {l : Fin k // l ≠ i₀}, G j l.1 (t l) := by
      intro j x
      rw [← Finset.mul_prod_erase Finset.univ (fun l => G j l (extendAt i₀ x t l))
        (Finset.mem_univ i₀)]
      congr 1
      · simp [extendAt]
      · rw [prod_erase_eq_prod_subtype]
        refine Finset.prod_congr rfl fun l _ => ?_
        have hl : extendAt i₀ x t l.1 = t l := by
          simp only [extendAt, dif_neg l.2]
        rw [hl]
    simp only [hfac]
    rw [MeasureTheory.integral_finsetSum (Finset.univ) (fun j _ => ?_)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
      ring
    · have heq : (fun x : ℝ => c j * (G j i₀ x * ∏ l : {l : Fin k // l ≠ i₀}, G j l.1 (t l)))
          = fun x : ℝ =>
            (c j * ∏ l : {l : Fin k // l ≠ i₀}, G j l.1 (t l)) * G j i₀ x := by
        funext x; ring
      rw [heq]
      exact ((hGi j i₀).integrableOn).const_mul _
  simp only [hpt]
  have hgen := sum_integral_prod_eq_integral_sq (ι := {l : Fin k // l ≠ i₀})
      (fun j l => G j l.1) (fun j l => hGc j l.1) (fun j l => hGcs j l.1)
      (fun j => ∫ x in Set.Ioi (0:ℝ), G j i₀ x) c
  simpa only [mul_assoc] using hgen

end

end Commons.NumberTheory.MaynardSieve
