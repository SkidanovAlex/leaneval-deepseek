import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Submission.Commons.NumberTheory.NumberField.DedekindZeta.log_eulerProduct_primeIdeal
import Submission.Commons.NumberTheory.NumberField.DedekindZeta.tendsto_re_nhdsGT_atTop
import Submission.Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Filter IsDedekindDomain Topology Set

namespace Commons.NumberTheory.NumberField.Set

section Aux

variable {K : Type*} [Field K] [NumberField K]

/-- For `s ≥ 1`, the Euler factor term of `𝔭` satisfies
`-log (1 - N𝔭^{-s}) ≤ 2 N𝔭^{-s}`.  This is the termwise inequality which converts the logarithmic
Euler product into a linear bound on the prime-ideal zeta sum. -/
lemma neg_log_one_sub_absNorm_rpow_le {s : ℝ} (hs : 1 ≤ s)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))
      ≤ 2 * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
  have hN : (2 : ℝ) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) :=
    Commons.NumberTheory.NumberField.DedekindZeta.two_le_absNorm_primeIdeal 𝔭
  have hx0 : 0 ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hxhalf : (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ 1 / 2 := by
    have h1 : (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hN (by linarith)
    have h2 : (2 : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h3 : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by
      rw [Real.rpow_neg_one]; norm_num
    calc (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) := h1
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) := h2
      _ = 1 / 2 := h3
  rw [← Real.log_inv (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))]
  exact Commons.Analysis.ExpLog.log_inv_one_sub_le_two hx0 (by linarith)

end Aux

/-- **Divergence of the prime-ideal zeta sum** (the analytic gateway for Dirichlet density).

For a number field `K`, the sum `∑_𝔭 N𝔭^{-s}` over all nonzero prime ideals tends to `+∞` as
`s → 1⁺`.  This is the statement that makes `NumberField.Set.HasDirichletDensity` a usable notion:
it says that the denominator of the defining ratio diverges like `log (1/(s-1))`.

Proof route: by the logarithmic Euler product
(`Commons.NumberField.DedekindZeta.log_eulerProduct_primeIdeal`)
we have `log ζ_K(s) = ∑_𝔭 -log (1 - N𝔭^{-s})`; by `tendsto_re_nhdsGT_atTop` the left hand side
tends to `+∞`; and termwise `-log (1 - x) ≤ 2x` for `0 ≤ x ≤ 1/2` turns this into
`∑_𝔭 N𝔭^{-s} ≥ (1/2) log ζ_K(s)`. -/
theorem tendsto_primeIdealZetaSum_univ_nhdsGT (K : Type*) [Field K] [NumberField K] :
    Filter.Tendsto
      (fun s : ℝ => NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s)
      (𝓝[>] 1) atTop := by
  -- Rewrite the sum over `univ` as a sum over all nonzero prime ideals.
  have hfun : (fun s : ℝ => NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s)
      = fun s : ℝ => ∑' 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
    funext s
    rw [NumberField.Set.primeIdealZetaSum_def,
      tsum_univ (f := fun 𝔭 : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K) => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))]
  rw [hfun]
  -- Lower bound: `(1/2) log (re ζ_K s) ≤ ∑_𝔭 N𝔭^{-s}` for `s > 1`.
  have hlower : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      (1 / 2) * Real.log ((NumberField.dedekindZeta K (s : ℂ)).re)
        ≤ ∑' 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
            (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : 1 < s := hs
    have hsle : 1 ≤ s := le_of_lt hs1
    have hlog :=
      Commons.NumberTheory.NumberField.DedekindZeta.log_eulerProduct_primeIdeal K hs1
    have hterm : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))
          ≤ 2 * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) :=
      fun 𝔭 => neg_log_one_sub_absNorm_rpow_le hsle 𝔭
    have hsumm₁ : Summable (fun 𝔭 : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K) =>
        -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))) :=
      Commons.NumberTheory.NumberField.DedekindZeta.summable_log_one_sub_primeIdeal hs1
    have hsumm₂ : Summable (fun 𝔭 : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K) =>
        2 * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) :=
      (summable_primeIdealZetaSum hs1).mul_left 2
    have hsum := Summable.tsum_le_tsum hterm hsumm₁ hsumm₂
    rw [hlog, tsum_mul_left] at hsum
    linarith
  -- The lower bound tends to `+∞`.
  have hcomp : Tendsto (fun s : ℝ => Real.log ((NumberField.dedekindZeta K (s : ℂ)).re))
      (𝓝[>] (1 : ℝ)) atTop :=
    Real.tendsto_log_atTop.comp
      (Commons.NumberTheory.NumberField.DedekindZeta.tendsto_re_nhdsGT_atTop K)
  have hF : Tendsto (fun s : ℝ =>
      (1 / 2) * Real.log ((NumberField.dedekindZeta K (s : ℂ)).re)) (𝓝[>] (1 : ℝ)) atTop :=
    Tendsto.const_mul_atTop (by norm_num) hcomp
  exact tendsto_atTop_mono' _ hlower hF

end Commons.NumberTheory.NumberField.Set
