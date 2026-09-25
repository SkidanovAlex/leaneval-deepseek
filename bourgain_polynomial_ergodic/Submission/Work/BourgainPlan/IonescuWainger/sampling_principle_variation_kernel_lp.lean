import Mathlib
import Submission.Work.BourgainPlan.Thm52.varRhoFrom_lintegral_le_of_finsupp_bound
import Submission.Work.BourgainPlan.IonescuWainger.summable_kernel_mul_of_memLp
import Submission.Work.BourgainPlan.IonescuWainger.tendsto_sum_Icc_atTop_tsum
import Submission.Work.BourgainPlan.IonescuWainger.tendsto_lintegral_Icc_truncation

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Truncation of an arbitrary `ℤ`-indexed complex sequence to the symmetric interval
`[-j, j]`, as a finitely supported sequence (the values equal `h` on `[-j, j]` and vanish
outside). -/
noncomputable def trunc (h : ℤ → ℂ) (j : ℕ) : ℤ →₀ ℂ :=
  Finsupp.ofSupportFinite (fun k : ℤ => if k ∈ Finset.Icc (-(j : ℤ)) (j : ℤ) then h k else 0)
    (by
      apply Set.Finite.subset (Finset.finite_toSet (Finset.Icc (-(j : ℤ)) (j : ℤ)))
      intro k hk
      by_contra hc
      apply hk
      have hc' : k ∉ Finset.Icc (-(j : ℤ)) (j : ℤ) := fun h => hc (by simpa using h)
      simp [hc'])

lemma trunc_apply (h : ℤ → ℂ) (j : ℕ) (k : ℤ) :
    trunc h j k = if k ∈ Finset.Icc (-(j : ℤ)) (j : ℤ) then h k else 0 := by
  rw [trunc, Finsupp.ofSupportFinite_coe]

lemma trunc_support_subset (h : ℤ → ℂ) (j : ℕ) :
    (trunc h j).support ⊆ Finset.Icc (-(j : ℤ)) (j : ℤ) := by
  intro k hk
  by_contra hc
  have h0 : (trunc h j) k ≠ 0 := Finsupp.mem_support_iff.mp hk
  rw [trunc_apply] at h0
  exact h0 (by simp [hc])

/-- The sum of the kernel against the truncation of `h` to `[-j, j]` equals the sum over the
symmetric interval (outside the support the truncation vanishes). -/
lemma trunc_sum_eq (h : ℤ → ℂ) (K : ℤ → ℂ) (k : ℤ) (j : ℕ) :
    (∑ i ∈ (trunc h j).support, K (k - i) * (trunc h j) i)
      = ∑ i ∈ Finset.Icc (-(j : ℤ)) (j : ℤ), K (k - i) * h i := by
  have h1 : ∑ i ∈ (trunc h j).support, K (k - i) * (trunc h j) i
      = ∑ i ∈ (trunc h j).support, K (k - i) * h i :=
    Finset.sum_congr rfl
      (fun i hi => by rw [trunc_apply, if_pos (trunc_support_subset h j hi)])
  have h2 : ∑ i ∈ (trunc h j).support, K (k - i) * h i
      = ∑ i ∈ Finset.Icc (-(j : ℤ)) (j : ℤ), K (k - i) * h i := by
    refine Finset.sum_subset (trunc_support_subset h j) (fun i hi hic => ?_)
    have h0 : (trunc h j) i = 0 := by
      by_contra hne
      exact hic (Finsupp.mem_support_iff.mpr hne)
    rw [trunc_apply, if_pos hi] at h0
    rw [h0, mul_zero]
  rw [h1, h2]

/-- The `Lᵖ`-"norm" of an `ℝ≥0∞`-valued function on `ℤ` is the `p`-th root of the integral of
its `p`-th power. -/
theorem eLpNorm_ennreal_eq (p : ℝ) (hp : 0 < p) (F : ℤ → ℝ≥0∞) :
    eLpNorm F (ENNReal.ofReal p) Measure.count
      = (∫⁻ y : ℤ, F y ^ p ∂Measure.count) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top AEStronglyMeasurable.of_discrete,
    ENNReal.toReal_ofReal hp.le]
  exact congrArg (fun z => z ^ (1 / p)) (lintegral_congr fun y => by rw [enorm_eq_self])

/-- **From a bound on `∫⁻ ‖F‖^p` to a bound on the `eLpNorm`**: if
`∫⁻ F^p ≤ ofReal (B^p) · ∫⁻ ‖g‖^p` with `B ≥ 0`, then `eLpNorm F ≤ ofReal B · eLpNorm g`,
by taking the `(1/p)`-th power and using `(B^p)^(1/p) = B`. -/
theorem eLpNorm_le_of_lpPow_le {p : ℝ} (hp : 0 < p) {F : ℤ → ℝ≥0∞} {B : ℝ} (hB : 0 ≤ B)
    {g : ℤ → ℂ}
    (h : ∫⁻ y : ℤ, F y ^ p ∂Measure.count
      ≤ ENNReal.ofReal (B ^ p) * Work.BourgainPlan.Thm52.lpPow p g) :
    eLpNorm F (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal B * Work.BourgainPlan.Thm52.lpNorm p g := by
  have hg : Work.BourgainPlan.Thm52.lpNorm p g
      = (Work.BourgainPlan.Thm52.lpPow p g) ^ (1 / p) := by
    rw [Work.BourgainPlan.Thm52.lpNorm, Work.BourgainPlan.Thm52.lpPow,
      eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top AEStronglyMeasurable.of_discrete]
    rw [ENNReal.toReal_ofReal hp.le]
  rw [eLpNorm_ennreal_eq p hp F, hg]
  refine (ENNReal.rpow_le_rpow h (by positivity)).trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  congr 1
  rw [← ENNReal.ofReal_rpow_of_nonneg hB hp.le, ← ENNReal.rpow_mul,
    show p * (1 / p) = 1 by field_simp, ENNReal.rpow_one]

-- Extension of a finitely-supported kernel bound for the two-variation to all of ell-p of Z: the
-- concrete instantiation of the abstract density/extension step
-- Work.BourgainPlan.Thm52.varRhoFrom_lintegral_le_of_finsupp_bound (in
-- Submission/Work/BourgainPlan/Thm52/varRhoFrom_lintegral_le_of_finsupp_bound.lean).
-- Take T0 n g k = sum over j in g.support of K n (k - j) * g j, T n h k = tsum over j of K n (k - j) * h j
-- and the approximating sequence f i = h restricted to [-i, i]; then hbound is the hypothesis hK,
-- hconv is dominated convergence (each term dominated by the summable sequence of the hypothesis hKsum
-- paired with the ell-p input, hence by Holder along the truncations) and happ is the ell-p-convergence
-- of the truncations.  The hypothesis hKsum is what makes the infinite kernel sum absolutely convergent.
theorem sampling_principle_variation_kernel_lp {p : ℝ} (hp : 1 < p) {κ : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (K : ℕ → ℤ → ℂ) (hKsum : ∀ n : ℕ, Summable (fun j : ℤ => ‖K n j‖ ^ (p / (p - 1))))
    (hK : ∀ a : ℤ →₀ ℂ,
      ∫⁻ k : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
        (fun n : ℕ => ∑ j ∈ a.support, K n (k - j) * a j)) ^ p ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (B ^ p) * Work.BourgainPlan.Thm52.lpPow p (⇑a))
    (h : ℤ → ℂ) (hh : Memℓp h (ENNReal.ofReal p)) :
    MeasureTheory.eLpNorm (fun k : ℤ => Work.BourgainPlan.Maximal.varRhoFrom 2 κ
        (fun n : ℕ => ∑' j : ℤ, K n (k - j) * h j))
      (ENNReal.ofReal p) MeasureTheory.Measure.count
    ≤ ENNReal.ofReal B * MeasureTheory.eLpNorm h (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  -- the finitely supported bound is the hypothesis `hK`, read through the definition of `lpPow`
  have hbound : ∀ a : ℤ →₀ ℂ,
      ∫⁻ k : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
        (fun n : ℕ => ∑ j ∈ a.support, K n (k - j) * a j)) ^ p
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (B ^ p)
        * ∫⁻ k : ℤ, ‖(⇑a : ℤ → ℂ) k‖ₑ ^ p ∂MeasureTheory.Measure.count := by
    intro a
    simpa [Work.BourgainPlan.Thm52.lpPow] using hK a
  -- the pointwise convergence of the truncated sums to the infinite sum (absolute convergence)
  have hconv : ∀ (k : ℤ) (n : ℕ),
      Filter.Tendsto
        (fun j : ℕ => ∑ i ∈ (trunc h j).support, K n (k - i) * (trunc h j) i)
        Filter.atTop (nhds (∑' i : ℤ, K n (k - i) * h i)) := by
    intro k n
    have hsum : Summable (fun i : ℤ => K n (k - i) * h i) :=
      summable_kernel_mul_of_memLp hp (hKsum n) hh k
    have hfun : (fun j : ℕ => ∑ i ∈ (trunc h j).support, K n (k - i) * (trunc h j) i)
        = fun j : ℕ => ∑ i ∈ Finset.Icc (-(j : ℤ)) (j : ℤ), K n (k - i) * h i :=
      funext fun j => trunc_sum_eq h (K n) k j
    rw [hfun]
    exact tendsto_sum_Icc_atTop_tsum hsum
  -- the `ℓᵖ`-convergence of the truncations (monotone convergence)
  have happ : Filter.Tendsto
      (fun j : ℕ => ∫⁻ k : ℤ, ‖(⇑(trunc h j) : ℤ → ℂ) k‖ₑ ^ p
        ∂MeasureTheory.Measure.count)
      Filter.atTop (nhds (∫⁻ k : ℤ, ‖h k‖ₑ ^ p ∂MeasureTheory.Measure.count)) := by
    have h1 : (fun j : ℕ => ∫⁻ k : ℤ, ‖(⇑(trunc h j) : ℤ → ℂ) k‖ₑ ^ p
          ∂MeasureTheory.Measure.count)
        = fun j : ℕ => ∫⁻ k : ℤ, ENNReal.ofReal
            ‖(if k ∈ Finset.Icc (-(j : ℤ)) (j : ℤ) then h k else 0 : ℂ)‖ ^ p
            ∂MeasureTheory.Measure.count := by
      funext j
      refine lintegral_congr (fun k => ?_)
      rw [trunc_apply]
      by_cases hk : k ∈ Finset.Icc (-(j : ℤ)) (j : ℤ) <;> simp [hk]
    have h2 : (∫⁻ k : ℤ, ‖h k‖ₑ ^ p ∂MeasureTheory.Measure.count)
        = (∫⁻ k : ℤ, ENNReal.ofReal ‖h k‖ ^ p ∂MeasureTheory.Measure.count) := by
      refine lintegral_congr (fun k => ?_)
      simp
    rw [h1, h2]
    exact tendsto_lintegral_Icc_truncation p hp0 h
  have hmain :=
    Work.BourgainPlan.Thm52.varRhoFrom_lintegral_le_of_finsupp_bound (p := p) hp κ
      (T := fun n (g : ℤ → ℂ) (k : ℤ) => ∑' j : ℤ, K n (k - j) * g j)
      (T₀ := fun n (a : ℤ →₀ ℂ) (k : ℤ) => ∑ j ∈ a.support, K n (k - j) * a j)
      (B := B) hB hbound h (fun j => trunc h j) hconv happ
  exact eLpNorm_le_of_lpPow_le hp0 hB hmain

end

end Work.BourgainPlan.IonescuWainger
