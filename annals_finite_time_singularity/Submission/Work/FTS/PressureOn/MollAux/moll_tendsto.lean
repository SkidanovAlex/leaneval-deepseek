/-
# `Work.FTS.PressureOn.MollAux.moll_tendsto`

The pairing `Dpair q Φ f = ∫ ⟪Φ, f⟫ + ∫ q · div f` of the pressure reconstruction is continuous
under mollification of the *test field*: for `q`, `Φ` continuous and `ψ` a `C^∞` field with
compact support,

  `Dpair q Φ (mollV n ψ) → Dpair q Φ ψ`  as `n → ∞`.

## Route

Write `K := tsupport ψ + closedBall 0 1`, a compact set.  For every `n`:

* `mollV n ψ` is supported in `K` and is bounded by `‖ψ‖_∞` (`MollAux.mollV_support_bound`, the support
  part following from `support_convolution_subset` and the fact that `rho n` is supported in the
  ball of radius `1/(n+1) ≤ 1`);
* `div (mollV n ψ) = rho n ⋆ div ψ` (`Auxiliary.div_convolution`), so `div (mollV n ψ)` is supported in
  `K` as well and is bounded by `‖div ψ‖_∞` (`MollAux.convolution_norm_le`);
* mollification against a normalised nonnegative kernel converges pointwise to the function
  (`ContDiffBump.convolution_tendsto_right_of_continuous`).

Hence both integrands converge pointwise to the corresponding integrands of `Dpair q Φ ψ` while
being supported in the fixed compact set `K` and uniformly bounded there, so
`Auxiliary.tendsto_integral_of_compact_support` (dominated convergence on a compact set) gives the two
limits, and `Tendsto.add` assembles them.

## Imports

The three `Auxiliary` lemmas above are the ones proved for this file; everything else is Mathlib
or the existing workspace material (`weyl_pair`, `rho_props`, `Auxiliary.div_convolution`,
`integral_mul_div_eq_neg_inner_gradient`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.MollDefs
import Submission.Work.FTS.PressureOn.MollAux.rho_props
import Submission.Work.FTS.PressureOn.Auxiliary.integral_mul_div_eq_neg_inner_gradient
import Submission.Work.FTS.PressureOn.Auxiliary.div_convolution
import Submission.Work.FTS.PressureOn.MollAux.mollV_support_bound
import Submission.Work.FTS.PressureOn.MollAux.convolution_norm_le
import Submission.Work.FTS.PressureOn.Auxiliary.tendsto_integral_of_compact_support

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter Set
open scoped Topology Pointwise

namespace Work.FTS.PressureOn.MollAux

theorem moll_tendsto (q : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hq : Continuous q) (hΦ : Continuous Φ)
    (ψ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hψ : ∀ n : ℕ, ContDiff ℝ n ψ) (hψc : HasCompactSupport ψ) :
    Filter.Tendsto (fun n : ℕ => Work.FTS.PressureOn.Dpair q Φ (Work.FTS.PressureOn.mollV n ψ))
      Filter.atTop (nhds (Work.FTS.PressureOn.Dpair q Φ ψ)) := by
  -- ## 0. Elementary facts about the mollifier kernel `rho n`
  have hρ_cd : ∀ n : ℕ, ContDiff ℝ 1 (Work.FTS.PressureOn.rho n) := fun n => (rho_props n).1 1
  have hρ_cs : ∀ n : ℕ, HasCompactSupport (Work.FTS.PressureOn.rho n) := fun n => (rho_props n).2.1
  have hρ_one : ∀ n : ℕ, ∫ z, Work.FTS.PressureOn.rho n z = 1 := fun n => (rho_props n).2.2.1
  have hρ_nonneg : ∀ n z, 0 ≤ Work.FTS.PressureOn.rho n z := fun n => (rho_props n).2.2.2.1
  have hρ_int : ∀ n : ℕ,
      MeasureTheory.Integrable (Work.FTS.PressureOn.rho n) MeasureTheory.volume := fun n =>
    ContDiffBump.integrable_normed (Work.FTS.PressureOn.bump n) (μ := MeasureTheory.volume)
  have hρ_supp : ∀ n z, Work.FTS.PressureOn.rho n z ≠ 0 → ‖z‖ ≤ 1 := by
    intro n z hz
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hle : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      calc (1 : ℝ) / ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) / ((n : ℝ) + 1) :=
            div_le_div_of_nonneg_right hn (le_of_lt hpos)
        _ = 1 := div_self (ne_of_gt hpos)
    exact le_trans ((rho_props n).2.2.2.2.2.1 z hz) hle
  have hρ_rOut : Filter.Tendsto (fun n : ℕ => (Work.FTS.PressureOn.bump n).rOut)
      Filter.atTop (nhds 0) := (rho_props 0).2.2.2.2.2.2
  -- ## 1. The compact set containing all the relevant supports
  set K : Set (EuclideanSpace ℝ (Fin 3)) :=
    tsupport ψ + Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 : ℝ) with hKdef
  have hKc : IsCompact K := by
    rw [hKdef]
    exact hψc.isCompact.add (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
  have htsuppK : tsupport ψ ⊆ K := by
    rw [hKdef]
    exact fun x hx => Set.mem_add.mpr ⟨x, hx, 0, by simp [Metric.mem_closedBall], by simp⟩
  -- ## 2. Bounds: `‖ψ‖`, `‖div ψ‖`, and the bounds of `q`, `Φ` on `K`
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ y, ‖ψ y‖ ≤ M := by
    obtain ⟨C, hC⟩ := hψc.isCompact.exists_bound_of_continuousOn (hψ 0).continuous.continuousOn
    refine ⟨max C 0, fun y => ?_⟩
    by_cases hy : y ∈ tsupport ψ
    · exact le_trans (hC y hy) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero]
      exact le_max_right _ _
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (ψ 0)) (hM 0)
  have hdivψ_cont : Continuous (fun y => FiniteTimeSingularity.div ψ y) := by
    rw [funext (Work.FTS.PressureOn.div_eq_sum_single ψ)]
    fun_prop
  have hdivψ_cs : HasCompactSupport (fun y => FiniteTimeSingularity.div ψ y) := by
    refine HasCompactSupport.intro (K := tsupport ψ) hψc.isCompact ?_
    intro y hy
    exact Auxiliary.div_eq_zero_of_notMem_tsupport hy
  obtain ⟨Vd, hVd⟩ : ∃ Vd : ℝ, ∀ y, ‖FiniteTimeSingularity.div ψ y‖ ≤ Vd := by
    obtain ⟨C, hC⟩ := hψc.isCompact.exists_bound_of_continuousOn hdivψ_cont.continuousOn
    refine ⟨max C 0, fun y => ?_⟩
    by_cases hy : y ∈ tsupport ψ
    · exact le_trans (hC y hy) (le_max_left _ _)
    · rw [Auxiliary.div_eq_zero_of_notMem_tsupport hy, norm_zero]
      exact le_max_right _ _
  have hVd0 : 0 ≤ Vd := le_trans (norm_nonneg _) (hVd 0)
  obtain ⟨DΦ₀, hDΦ₀⟩ : ∃ D : ℝ, ∀ x ∈ K, ‖Φ x‖ ≤ D :=
    hKc.exists_bound_of_continuousOn hΦ.continuousOn
  have hDΦ : ∀ x ∈ K, ‖Φ x‖ ≤ max DΦ₀ 0 := fun x hx =>
    le_trans (hDΦ₀ x hx) (le_max_left _ _)
  have hDΦ0 : 0 ≤ max DΦ₀ 0 := le_max_right _ _
  obtain ⟨Dq₀, hDq₀⟩ : ∃ D : ℝ, ∀ x ∈ K, |q x| ≤ D := by
    obtain ⟨D, hD⟩ := hKc.exists_bound_of_continuousOn hq.continuousOn
    exact ⟨D, fun x hx => by rw [← Real.norm_eq_abs]; exact hD x hx⟩
  have hDq : ∀ x ∈ K, |q x| ≤ max Dq₀ 0 := fun x hx =>
    le_trans (hDq₀ x hx) (le_max_left _ _)
  have hDq0 : 0 ≤ max Dq₀ 0 := le_max_right _ _
  -- ## 3. Support and bound of `mollV n ψ`
  have hmollVsupp : ∀ n : ℕ, Function.support (Work.FTS.PressureOn.mollV n ψ) ⊆ K := by
    intro n x hx
    by_contra hxK
    refine hx ((MollAux.mollV_support_bound n ψ M hM).1 x (fun b hb => ?_))
    by_contra hle
    push_neg at hle
    exact hxK (Set.mem_add.mpr ⟨b, hb, x - b, by
      rw [Metric.mem_closedBall, dist_zero_right]
      rwa [dist_eq_norm] at hle, by rw [add_sub_cancel]⟩)
  have hmollVbound : ∀ n x, ‖Work.FTS.PressureOn.mollV n ψ x‖ ≤ M := by
    intro n x
    simpa [Work.FTS.PressureOn.mollV] using
      MollAux.convolution_norm_le (Work.FTS.PressureOn.rho n) ψ (hρ_nonneg n) (hρ_int n)
        (hρ_one n) (hψ 0).continuous hψc M hM x
  have hmollV_cont : ∀ n : ℕ, Continuous (Work.FTS.PressureOn.mollV n ψ) := fun n =>
    (hρ_cs n).continuous_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      ((hρ_cd n).continuous) ((hψ 0).continuous.locallyIntegrable)
  -- ## 4. `div (mollV n ψ) = rho n ⋆ div ψ`, its support and its bound
  have hdiv_mollV : ∀ n : ℕ, ∀ x : EuclideanSpace ℝ (Fin 3),
      FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x =
        MeasureTheory.convolution (Work.FTS.PressureOn.rho n)
          (fun y => FiniteTimeSingularity.div ψ y) (ContinuousLinearMap.lsmul ℝ ℝ)
          MeasureTheory.volume x := by
    intro n x
    simpa [Work.FTS.PressureOn.mollV] using
      Auxiliary.div_convolution (Work.FTS.PressureOn.rho n) ψ
        ((hρ_cd n).continuous.locallyIntegrable) (hψ 1) hψc x
  have hdivmollVsupp : ∀ n : ℕ,
      Function.support (fun x => FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x)
        ⊆ K := by
    intro n x hx
    rw [Function.mem_support] at hx
    have hx' : FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x ≠ 0 := hx
    rw [hdiv_mollV n x] at hx'
    have hmem := support_convolution_subset (μ := MeasureTheory.volume)
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (f := Work.FTS.PressureOn.rho n)
      (g := fun y => FiniteTimeSingularity.div ψ y) hx'
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hmem
    rw [hKdef]
    refine Set.mem_add.mpr ⟨b, ?_, a, ?_, ?_⟩
    · by_contra hbt
      exact hb (Auxiliary.div_eq_zero_of_notMem_tsupport hbt)
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact hρ_supp n a ha
    · rw [add_comm]
      exact hab
  have hdivmollVbound : ∀ n x,
      ‖FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x‖ ≤ Vd := by
    intro n x
    rw [hdiv_mollV n x, MeasureTheory.convolution_def]
    calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (Work.FTS.PressureOn.rho n t)
            (FiniteTimeSingularity.div ψ (x - t))‖
        ≤ ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (Work.FTS.PressureOn.rho n t)
            (FiniteTimeSingularity.div ψ (x - t))‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ = ∫ t, Work.FTS.PressureOn.rho n t * ‖FiniteTimeSingularity.div ψ (x - t)‖ := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with t
          rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (hρ_nonneg n t)]
      _ ≤ ∫ t, Work.FTS.PressureOn.rho n t * Vd := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun t => ?_)
            ((hρ_int n).mul_const Vd) (Filter.Eventually.of_forall fun t => ?_)
          · exact mul_nonneg (hρ_nonneg n t) (norm_nonneg _)
          · exact mul_le_mul_of_nonneg_left (hVd (x - t)) (hρ_nonneg n t)
      _ = (∫ t, Work.FTS.PressureOn.rho n t) * Vd := MeasureTheory.integral_mul_const Vd _
      _ = Vd := by rw [hρ_one n, one_mul]
  have hdivmollV_cont : ∀ n : ℕ,
      Continuous (fun x => FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x) := by
    intro n
    refine Continuous.congr ?_ (fun x => (hdiv_mollV n x).symm)
    exact HasCompactSupport.continuous_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hdivψ_cs ((hρ_cd n).continuous.locallyIntegrable) hdivψ_cont
  -- ## 5. The two integrals converge
  -- ### 5a. the inner-product term
  have hA : Filter.Tendsto
      (fun n : ℕ => ∫ x, inner ℝ (Φ x) (Work.FTS.PressureOn.mollV n ψ x))
      Filter.atTop (nhds (∫ x, inner ℝ (Φ x) (ψ x))) := by
    refine Auxiliary.tendsto_integral_of_compact_support
      (F := fun n x => inner ℝ (Φ x) (Work.FTS.PressureOn.mollV n ψ x))
      (f := fun x => inner ℝ (Φ x) (ψ x)) (K := K) (C := max DΦ₀ 0 * M) hKc
      ?_ ?_ ?_ ?_ ?_ ?_
    · exact mul_nonneg hDΦ0 hM0
    · intro n
      exact (hΦ.inner (hmollV_cont n)).aestronglyMeasurable
    · intro n x hx
      by_contra hxK
      refine hx ?_
      have hzero : Work.FTS.PressureOn.mollV n ψ x = 0 := by
        by_contra hne
        exact hxK (hmollVsupp n hne)
      simp [hzero]
    · intro x hx
      by_contra hxK
      refine hx ?_
      have hzero : ψ x = 0 := by
        by_contra hne
        exact hxK (htsuppK (subset_tsupport ψ hne))
      simp [hzero]
    · intro n x
      by_cases hxK : x ∈ K
      · exact le_trans (norm_inner_le_norm _ _)
          (mul_le_mul (hDΦ x hxK) (hmollVbound n x) (norm_nonneg _) hDΦ0)
      · have hzero : Work.FTS.PressureOn.mollV n ψ x = 0 := by
          by_contra hne
          exact hxK (hmollVsupp n hne)
        simp [hzero]
        exact mul_nonneg hDΦ0 hM0
    · intro x
      refine Tendsto.inner tendsto_const_nhds ?_
      have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := MeasureTheory.volume)
        hρ_rOut ((hψ 0).continuous) x
      simpa [Work.FTS.PressureOn.mollV, Work.FTS.PressureOn.rho] using h
  -- ### 5b. the divergence term
  have hB : Filter.Tendsto
      (fun n : ℕ => ∫ x, q x * FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x)
      Filter.atTop (nhds (∫ x, q x * FiniteTimeSingularity.div ψ x)) := by
    refine Auxiliary.tendsto_integral_of_compact_support
      (F := fun n x => q x * FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x)
      (f := fun x => q x * FiniteTimeSingularity.div ψ x) (K := K) (C := max Dq₀ 0 * Vd) hKc
      ?_ ?_ ?_ ?_ ?_ ?_
    · exact mul_nonneg hDq0 hVd0
    · intro n
      exact (hq.mul (hdivmollV_cont n)).aestronglyMeasurable
    · intro n x hx
      by_contra hxK
      refine hx ?_
      have hzero : FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x = 0 := by
        by_contra hne
        exact hxK (hdivmollVsupp n hne)
      simp [hzero]
    · intro x hx
      by_contra hxK
      refine hx ?_
      have hzero : FiniteTimeSingularity.div ψ x = 0 := by
        by_contra hne
        exact hxK (htsuppK (by
          by_contra hb
          exact hne (Auxiliary.div_eq_zero_of_notMem_tsupport hb)))
      simp [hzero]
    · intro n x
      by_cases hxK : x ∈ K
      · rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hDq x hxK)
          (by rw [← Real.norm_eq_abs]; exact hdivmollVbound n x) (abs_nonneg _) hDq0
      · have hzero : FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x = 0 := by
          by_contra hne
          exact hxK (hdivmollVsupp n hne)
        simp [hzero]
        exact mul_nonneg hDq0 hVd0
    · intro x
      refine Tendsto.const_mul (q x) ?_
      have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := MeasureTheory.volume)
        hρ_rOut hdivψ_cont x
      have heq : (fun n : ℕ => FiniteTimeSingularity.div (Work.FTS.PressureOn.mollV n ψ) x)
          = fun n : ℕ => MeasureTheory.convolution
              ((Work.FTS.PressureOn.bump n).normed MeasureTheory.volume)
              (fun y => FiniteTimeSingularity.div ψ y) (ContinuousLinearMap.lsmul ℝ ℝ)
              MeasureTheory.volume x := by
        funext n
        rw [hdiv_mollV n x]
        rfl
      rw [heq]
      exact h
  -- ## 6. Assembly
  have hsum := hA.add hB
  simpa [Work.FTS.PressureOn.Dpair] using hsum

end Work.FTS.PressureOn.MollAux
