import Mathlib
import Submission.NK.BauerGeneral.Basic
import Submission.NK.BauerGeneral.Density
import Submission.NK.Chebotarev.isBigO_primeIdealZetaSum_sub_of_finite_diff

namespace NK.BauerGeneral

open Filter IsDedekindDomain Topology Set Asymptotics

theorem hasDirichletDensity_of_symmDiff_finite {K : Type*} [Field K]
    [NumberField K] {A B : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
    {δ : ℝ} (hAB : (A \ B).Finite) (hBA : (B \ A).Finite)
    (hA : NumberField.Set.HasDirichletDensity A δ) :
    NumberField.Set.HasDirichletDensity B δ := by
  have hfin : (A \ B ∪ B \ A).Finite := hAB.union hBA
  have hbig := NK.Chebotarev.isBigO_primeIdealZetaSum_sub_of_finite_diff (K := K) hfin
  obtain ⟨c, hc⟩ := hbig.bound
  set C : ℝ := max c 0
  have hg : Tendsto (fun s : ℝ => (NumberField.Set.primeIdealZetaSum (K := K) A s
      - NumberField.Set.primeIdealZetaSum (K := K) B s)
      / NumberField.Set.primeIdealZetaSum (K := K) (univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    refine tendsto_bdd_div_atTop_nhds_zero (b := -C) (B := C) ?_ ?_
      (Commons.NumberTheory.NumberField.Set.tendsto_primeIdealZetaSum_univ_nhdsGT K)
    · filter_upwards [hc] with s hs
      have hs' : ‖NumberField.Set.primeIdealZetaSum (K := K) A s
          - NumberField.Set.primeIdealZetaSum (K := K) B s‖ ≤ C := by
        refine le_trans hs ?_
        rw [norm_one, mul_one]
        exact le_max_left _ _
      exact (abs_le.mp (by rwa [Real.norm_eq_abs] at hs')).1
    · filter_upwards [hc] with s hs
      have hs' : ‖NumberField.Set.primeIdealZetaSum (K := K) A s
          - NumberField.Set.primeIdealZetaSum (K := K) B s‖ ≤ C := by
        refine le_trans hs ?_
        rw [norm_one, mul_one]
        exact le_max_left _ _
      exact (abs_le.mp (by rwa [Real.norm_eq_abs] at hs')).2
  rw [NumberField.Set.HasDirichletDensity] at hA ⊢
  have heq : (fun s : ℝ => NumberField.Set.primeIdealZetaSum (K := K) A s
        / NumberField.Set.primeIdealZetaSum (K := K) (univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s
        - (NumberField.Set.primeIdealZetaSum (K := K) A s
          - NumberField.Set.primeIdealZetaSum (K := K) B s)
          / NumberField.Set.primeIdealZetaSum (K := K) (univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s)
      = fun s : ℝ => NumberField.Set.primeIdealZetaSum (K := K) B s
        / NumberField.Set.primeIdealZetaSum (K := K) (univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s := by
    funext s
    rw [← sub_div]
    congr 1
    ring
  rw [← heq]
  simpa using hA.sub hg

end NK.BauerGeneral
