import Mathlib.Analysis.Asymptotics.TVS
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Submission.Commons.NumberTheory.NumberField.Set.tendsto_primeIdealZetaSum_div_log
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Set

open Filter IsDedekindDomain NumberField Topology Set Asymptotics
open scoped BigOperators

/-- If `f = O(1)` and `g → +∞` then `f / g → 0`. -/
private lemma tendsto_div_atTop_of_isBigO_one {f g : ℝ → ℝ}
    (hf : f =O[𝓝[>] (1 : ℝ)] (fun _ : ℝ => (1 : ℝ)))
    (hg : Tendsto g (𝓝[>] (1 : ℝ)) atTop) :
    Tendsto (fun s : ℝ => f s / g s) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hf.bound
  have hC' : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ), ‖f s‖ ≤ max C 0 := by
    filter_upwards [hC] with s hs
    rw [norm_one, mul_one] at hs
    exact hs.trans (le_max_left C 0)
  refine tendsto_bdd_div_atTop_nhds_zero (b := -(max C 0)) (B := max C 0) ?_ ?_ hg
  · filter_upwards [hC'] with s hs
    rw [Real.norm_eq_abs] at hs
    exact (abs_le.mp hs).1
  · filter_upwards [hC'] with s hs
    rw [Real.norm_eq_abs] at hs
    exact (abs_le.mp hs).2

/-- **The converse to `tendsto_primeIdealZetaSum_div_log`.**

If the partial Dirichlet series over `S` satisfies
`∑_{𝔭 ∈ S} N𝔭^{-s} = c * log (1/(s-1)) + O(1)` as `s → 1⁺`, then `S` has Dirichlet density `c`
(see `NumberField.Set.HasDirichletDensity`).

Proof route: by `Commons.NumberField.Set.isBigO_primeIdealZetaSum_sub_log` the full sum equals
`log (1/(s-1)) + O(1)`, and by `Commons.NumberField.Set.tendsto_primeIdealZetaSum_univ_nhdsGT` it
tends to `+∞`, so the ratio defining the density (partial sum over full sum) tends to `c`.  It is
easiest to first show the auxiliary statement that the ratio of the partial sum over `S` and
`log (1/(s-1))` tends to `c` and then multiply by the ratio of `log (1/(s-1))` and the full sum
(which tends to `1` by `tendsto_primeIdealZetaSum_div_log` applied to `S = univ`, or directly from
`isBigO_primeIdealZetaSum_sub_log`). -/
theorem hasDirichletDensity_of_isBigO_primeIdealZetaSum_sub_log {K : Type*} [Field K]
    [NumberField K] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
    {c : ℝ}
    (h : (fun s : ℝ => NumberField.Set.primeIdealZetaSum S s - c * Real.log (1 / (s - 1)))
      =O[𝓝[>] 1] (fun _ : ℝ => (1 : ℝ))) :
    NumberField.Set.HasDirichletDensity S c := by
  rw [NumberField.Set.HasDirichletDensity]
  have hU : (fun s : ℝ => NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s
        - Real.log (1 / (s - 1))) =O[𝓝[>] 1] (fun _ : ℝ => (1 : ℝ)) :=
    isBigO_primeIdealZetaSum_sub_log K
  have hUt : Tendsto (fun s : ℝ => NumberField.Set.primeIdealZetaSum
      (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s)
      (𝓝[>] (1 : ℝ)) atTop := tendsto_primeIdealZetaSum_univ_nhdsGT K
  have hcU : (fun s : ℝ => NumberField.Set.primeIdealZetaSum S s
        - c * NumberField.Set.primeIdealZetaSum
          (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s)
      =O[𝓝[>] 1] (fun _ : ℝ => (1 : ℝ)) := by
    obtain ⟨C₁, h₁⟩ := h.bound
    obtain ⟨C₂, h₂⟩ := hU.bound
    refine IsBigO.of_bound (max C₁ 0 + |c| * max C₂ 0) ?_
    filter_upwards [h₁, h₂] with s hs1 hs2
    rw [norm_one, mul_one] at hs1 hs2
    rw [norm_one, mul_one]
    have hkey : NumberField.Set.primeIdealZetaSum S s
          - c * NumberField.Set.primeIdealZetaSum
            (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s
        = (NumberField.Set.primeIdealZetaSum S s - c * Real.log (1 / (s - 1)))
          - c * (NumberField.Set.primeIdealZetaSum
              (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s
              - Real.log (1 / (s - 1))) := by ring
    rw [hkey]
    have hc1 : ‖NumberField.Set.primeIdealZetaSum S s - c * Real.log (1 / (s - 1))‖
        ≤ max C₁ 0 := hs1.trans (le_max_left C₁ 0)
    have hc2 : ‖NumberField.Set.primeIdealZetaSum
          (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s
          - Real.log (1 / (s - 1))‖ ≤ max C₂ 0 := hs2.trans (le_max_left C₂ 0)
    calc ‖(NumberField.Set.primeIdealZetaSum S s - c * Real.log (1 / (s - 1)))
            - c * (NumberField.Set.primeIdealZetaSum
                (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum
                  (NumberField.RingOfIntegers K))) s - Real.log (1 / (s - 1)))‖
        ≤ ‖NumberField.Set.primeIdealZetaSum S s - c * Real.log (1 / (s - 1))‖
            + ‖c * (NumberField.Set.primeIdealZetaSum
                (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum
                  (NumberField.RingOfIntegers K))) s - Real.log (1 / (s - 1)))‖ :=
          norm_sub_le _ _
      _ = ‖NumberField.Set.primeIdealZetaSum S s - c * Real.log (1 / (s - 1))‖
            + |c| * ‖NumberField.Set.primeIdealZetaSum
                (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum
                  (NumberField.RingOfIntegers K))) s - Real.log (1 / (s - 1))‖ := by
          simp only [norm_mul, Real.norm_eq_abs]
      _ ≤ max C₁ 0 + |c| * max C₂ 0 :=
          add_le_add hc1 (mul_le_mul_of_nonneg_left hc2 (abs_nonneg c))
  have hdiv : Tendsto (fun s : ℝ =>
      (NumberField.Set.primeIdealZetaSum S s - c * NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s)
      / NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s)
      (𝓝[>] (1 : ℝ)) (𝓝 0) := tendsto_div_atTop_of_isBigO_one hcU hUt
  have hcongr : (fun s : ℝ => NumberField.Set.primeIdealZetaSum S s
        / NumberField.Set.primeIdealZetaSum
          (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s)
      =ᶠ[𝓝[>] (1 : ℝ)]
      (fun s : ℝ => c + (NumberField.Set.primeIdealZetaSum S s
        - c * NumberField.Set.primeIdealZetaSum
          (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s)
        / NumberField.Set.primeIdealZetaSum
          (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s) := by
    filter_upwards [hUt.eventually (eventually_gt_atTop (0 : ℝ))] with s hs
    have hne : NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s ≠ 0 :=
      ne_of_gt hs
    field_simp
    ring
  refine Tendsto.congr' hcongr.symm ?_
  have h1 : Tendsto (fun _ : ℝ => c) (𝓝[>] (1 : ℝ)) (𝓝 c) := tendsto_const_nhds
  simpa using h1.add hdiv

end Commons.NumberTheory.NumberField.Set
