import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.tendsto_sum_Icc_atTop_tsum
import Submission.Work.BourgainPlan.IonescuWainger.tendsto_lintegral_Icc_truncation
import Submission.Work.BourgainPlan.IonescuWainger.cutoff_extension_lp
import Submission.Work.BourgainPlan.IonescuWainger.exists_kernel_lattice_weight_le
import Submission.Work.BourgainPlan.IonescuWainger.msw_of_cutoff_extension
import Submission.Work.BourgainPlan.IonescuWainger.mz_square_function
import Submission.Work.BourgainPlan.IonescuWainger.varRho_bandlimited_pointwise

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

-- Extension of a finitely-supported kernel bound for the two-variation to all of ell-p of Z: the
-- concrete instantiation of the abstract density/extension step
-- Work.BourgainPlan.Thm52.varRhoFrom_lintegral_le_of_finsupp_bound (in
-- Submission/Work/BourgainPlan/Thm52/varRhoFrom_lintegral_le_of_finsupp_bound.lean).
-- Take T0 n g k = sum over j in g.support of K n (k - j) * g j, T n h k = tsum over j of K n (k - j) * h j
-- and the approximating sequence f i = h restricted to [-i, i]; then hbound is the hypothesis hK,
-- hconv is dominated convergence (each term dominated by the summable sequence of the hypothesis hKsum
-- paired with the ell-p input, hence by Holder along the truncations) and happ is the ell-p-convergence
-- of the truncations.  The hypothesis hKsum is what makes the infinite kernel sum absolutely convergent.
end

end Work.BourgainPlan.IonescuWainger
