import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.ExpLog.log_one_sub_le
import Submission.Commons.Analysis.Real.log_one_sub_upper
import Submission.Commons.NumberTheory.NumberField.DedekindZeta.log_eulerProduct_primeIdeal
import Submission.Commons.NumberTheory.NumberField.DedekindZeta.tendsto_log_add_log_sub_one
import Submission.Commons.NumberTheory.NumberField.DedekindZeta.tendsto_re_nhdsGT_atTop
import Submission.Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Set

open Filter IsDedekindDomain Topology Set Asymptotics
open scoped BigOperators

section Helpers

variable {K : Type*} [Field K] [NumberField K]

/-- The elementary pointwise estimate behind the logarithmic comparison of the prime-ideal zeta
sum: for `0 ≤ x ≤ 1/2`, `x + log (1 - x)` is of size at most `2 x²`. -/
private lemma abs_add_log_one_sub_le_two_sq {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    |x + Real.log (1 - x)| ≤ 2 * x ^ 2 := by
  have hxlt : x < 1 := by linarith
  have hupper : x + Real.log (1 - x) ≤ 2 * x ^ 2 := by
    have h := Commons.Analysis.Real.log_one_sub_upper h0 hxlt
    nlinarith [sq_nonneg x]
  have hlower : -(2 * x ^ 2) ≤ x + Real.log (1 - x) := by
    rcases eq_or_lt_of_le h0 with hzero | hpos
    · subst hzero; norm_num
    · have hle := Commons.Analysis.ExpLog.log_one_sub_le hpos hxlt
      have h1x : 0 < 1 - x := by linarith
      have hinv : 1 / (1 - x) ≤ 2 := by
        rw [div_le_iff₀ h1x]; linarith
      have hx2le : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
        calc x ^ 2 / (1 - x) = x ^ 2 * (1 / (1 - x)) := by ring
          _ ≤ x ^ 2 * 2 := mul_le_mul_of_nonneg_left hinv (sq_nonneg x)
          _ = 2 * x ^ 2 := by ring
      have key : x - x / (1 - x) = -(x ^ 2 / (1 - x)) := by
        field_simp
        ring
      linarith
  rw [abs_le]
  exact ⟨hlower, hupper⟩

/-- The (nonnegative) value `N𝔭^{-s}` is at most `1/2` when `s ≥ 1`. -/
private lemma rpow_neg_absNorm_le_half {s : ℝ} (hs : 1 ≤ s)
    (𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) :=
    DedekindZeta.two_le_absNorm_primeIdeal 𝔭
  have h1 : (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by linarith)
  have h2' : (2 : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by
    rw [Real.rpow_neg_one]; norm_num
  calc (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) := h1
    _ ≤ (2 : ℝ) ^ (-1 : ℝ) := h2'
    _ = 1 / 2 := h3

/-- The prime-ideal zeta sum over all nonzero prime ideals is the `tsum` over the full
`HeightOneSpectrum`. -/
lemma primeIdealZetaSum_univ_eq_tsum (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) s
      = ∑' 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K),
          (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
  rw [NumberField.Set.primeIdealZetaSum_def]
  exact tsum_univ (fun 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
    (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))

end Helpers

/-- **The total prime-ideal zeta sum grows like `log (1/(s-1))`.**

For a number field `K`, `∑_𝔭 N𝔭^{-s} - log (1/(s-1))` stays bounded as `s → 1⁺`; equivalently
`∑_𝔭 N𝔭^{-s} = log (1/(s-1)) + O(1)`.  This sharpens
`Commons.NumberField.Set.tendsto_primeIdealZetaSum_univ_nhdsGT` and is what one actually uses when
comparing densities in a finite extension (which is where the `O(1)` errors must cancel).

Route: `log ζ_K(s) = ∑_𝔭 -log (1 - N𝔭^{-s})`
(`Commons.NumberField.DedekindZeta.log_eulerProduct_primeIdeal`),
`log ζ_K(s) + log (s-1) → log (Res_{s=1} ζ_K)`
(`Commons.NumberField.DedekindZeta.tendsto_log_add_log_sub_one`), and the difference
`∑_𝔭 (N𝔭^{-s} + log (1 - N𝔭^{-s}))` converges. -/
theorem isBigO_primeIdealZetaSum_sub_log (K : Type*) [Field K] [NumberField K] :
    (fun s : ℝ => NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s
        - Real.log (1 / (s - 1)))
      =O[𝓝[>] 1] (fun _ : ℝ => (1 : ℝ)) := by
  classical
  -- The uniform bound `C` for the "remainder" series `∑_𝔭 (N𝔭^{-s} + log (1 - N𝔭^{-s}))`.
  set C : ℝ := ∑' 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K),
      2 * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-2 : ℝ) with hCdef
  have hCsum : Summable (fun 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      2 * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-2 : ℝ)) :=
    (Commons.NumberTheory.NumberField.Set.summable_primeIdealNorm K
      (by norm_num : (1 : ℝ) < 2)).mul_left 2
  have hrem : ∀ s : ℝ, 1 < s →
      ‖∑' 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K),
          ((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
            + Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)))‖ ≤ C := by
    intro s hs
    have hs1 : (1 : ℝ) ≤ s := le_of_lt hs
    have hpt : ∀ 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K),
        ‖(Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
            + Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))‖
          ≤ 2 * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-2 : ℝ) := by
      intro 𝔭
      rw [Real.norm_eq_abs]
      have h0 : 0 ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) :=
        Real.rpow_nonneg (le_of_lt (DedekindZeta.absNorm_primeIdeal_pos 𝔭)) _
      have hhalf := rpow_neg_absNorm_le_half hs1 𝔭
      refine (abs_add_log_one_sub_le_two_sq h0 hhalf).trans ?_
      have hbase : (1 : ℝ) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) :=
        le_trans (by norm_num) (DedekindZeta.two_le_absNorm_primeIdeal 𝔭)
      have hexp : -(2 * s) ≤ -2 := by linarith
      have hcomp := Real.rpow_le_rpow_of_exponent_le hbase hexp
      have hx0 : 0 ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) :=
        le_of_lt (DedekindZeta.absNorm_primeIdeal_pos 𝔭)
      have hsq : ((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) ^ 2
          = (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-(2 * s)) := by
        rw [← Real.rpow_mul_natCast hx0 (-s) 2]
        congr 1
        ring
      rw [hsq]
      linarith
    have hsumm_norm : Summable (fun 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        ‖(Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
            + Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hCsum
    calc ‖∑' 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K),
            ((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
              + Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)))‖
        ≤ ∑' 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K),
            ‖(Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
              + Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))‖ :=
          norm_tsum_le_tsum_norm hsumm_norm
      _ ≤ ∑' 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K),
            2 * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-2 : ℝ) :=
          Summable.tsum_le_tsum hpt hsumm_norm hCsum
      _ = C := by rw [hCdef]
  -- The bound for `log ζ_K(s) + log (s-1)`, which converges to `log Res`.
  set D : ℝ := |Real.log (NumberField.dedekindZeta_residue K)| + 1 with hDdef
  have hk : ∀ᶠ s : ℝ in 𝓝[>] 1,
      ‖Real.log ((NumberField.dedekindZeta K (s : ℂ)).re) + Real.log (s - 1)‖ ≤ D := by
    have ht := Commons.NumberTheory.NumberField.DedekindZeta.tendsto_log_add_log_sub_one K
    have hnorm := (continuous_norm.tendsto (Real.log (NumberField.dedekindZeta_residue K))).comp ht
    have hev := hnorm.eventually (eventually_lt_nhds (lt_add_one _))
    filter_upwards [hev] with s hs
    simp only [Function.comp_apply, Real.norm_eq_abs] at hs
    rw [hDdef, Real.norm_eq_abs]
    linarith [abs_nonneg (Real.log (NumberField.dedekindZeta_residue K))]
  -- Eventually the identity `∑_𝔭 N𝔭^{-s} - log(1/(s-1)) = remainder + (log ζ + log(s-1))`.
  have hident : ∀ᶠ s : ℝ in 𝓝[>] 1,
      (NumberField.Set.primeIdealZetaSum
          (Set.univ : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) s
        - Real.log (1 / (s - 1)))
      = (∑' 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K),
            ((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
              + Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))))
        + (Real.log ((NumberField.dedekindZeta K (s : ℂ)).re) + Real.log (s - 1)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs1 : 1 < s := Set.mem_Ioi.mp hs
    have hxs : Summable (fun 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) :=
      Commons.NumberTheory.NumberField.Set.summable_primeIdealNorm K hs1
    have hgs := DedekindZeta.summable_log_one_sub_primeIdeal (K := K) hs1
    have hsub : (∑' 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K),
            ((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
              + Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))))
        = (∑' 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K),
              (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))
          - ∑' 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K),
              -Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) := by
      rw [← hxs.tsum_sub hgs]
      exact tsum_congr (fun 𝔭 => by ring)
    have hlog := Commons.NumberTheory.NumberField.DedekindZeta.log_eulerProduct_primeIdeal K hs1
    rw [primeIdealZetaSum_univ_eq_tsum K s, hsub, hlog, one_div, Real.log_inv]
    ring
  refine IsBigO.of_bound (C + D) ?_
  filter_upwards [self_mem_nhdsWithin, hident, hk] with s hs hid hks
  rw [norm_one, mul_one, hid]
  calc ‖(∑' 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K),
            ((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
              + Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))))
          + (Real.log ((NumberField.dedekindZeta K (s : ℂ)).re) + Real.log (s - 1))‖
      ≤ ‖∑' 𝔭 : HeightOneSpectrum (NumberField.RingOfIntegers K),
            ((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
              + Real.log (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)))‖
        + ‖Real.log ((NumberField.dedekindZeta K (s : ℂ)).re) + Real.log (s - 1)‖ :=
        norm_add_le _ _
    _ ≤ C + D := add_le_add (hrem s (Set.mem_Ioi.mp hs)) hks

end Commons.NumberTheory.NumberField.Set
