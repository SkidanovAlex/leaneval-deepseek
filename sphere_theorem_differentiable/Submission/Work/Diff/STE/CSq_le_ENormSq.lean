import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.fourierCoeff_pdVec
import Submission.Work.Diff.STE.wt_pow_le_monomialSum
import Submission.Work.Diff.STE.integral_fourierExp
import Submission.Work.Diff.STE.bessel_continuous
import Submission.Work.Diff.STE.wt_pow_le_wordSum
import Submission.Work.Diff.STE.fourierCoeff_pdVec_normSq
import Submission.Work.Diff.STE.continuous_pdVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `CSq k (fourierCoeff f) ≤ C (ENormSq k f + ENormSq 0 f)`: Sobolev comparison on the torus

Layer A of the STE Fourier toolkit (design note `DESIGN.md`, step 2).  For a `Cᵏ`, `1`-periodic
function `f` on `ι → ℝ`, the weighted `ℓ²`-norm of its Fourier coefficients is bounded by the
physical-space `Hᵏ` energy:

  `CSq k (fourierCoeff f) = Σ_m ⟨m⟩^{2k} ‖û(m)‖² ≤ 2^k (ENormSq k f + ENormSq 0 f)`,

where `ENormSq k f = Σ_{l : Fin k → ι} ∫_{unitCube} ‖∂^{l} f‖²` is the sum of the `L²` norms of
all `k`-fold partial derivatives.  The extra term `ENormSq 0 f` is *not* redundant: it pays for
the constant term `1` in `wt m ^ k = (1 + Σᵢ mᵢ²)^k`, which is what makes the bound uniform in
`m` (at `m = 0` every derivative weight vanishes).

## The argument

Everything is a termwise comparison of nonnegative families followed by Bessel's inequality.

* Weight comparison (`wt_pow_le_wordSum`): the `k`-th power of the weight of the *undifferentiated*
  coefficient is dominated by `2^k` times `1 +` the word sum of `k` derivative multipliers,
  `wt m ^ k ≤ 2^k (1 + Σ_{l : Fin k → ι} ∏_{i} (2π m_{l i})²)`.
* Fourier coefficients of derivatives (`fourierCoeff_pdVec`, `fourierCoeff_pdVec_normSq`,
  `continuous_pdVec`): `∂^l` is the multiplier `∏_i 2πi m_{l i}`, so
  `(∏_i (2π m_{l i})²) ‖û(m)‖² = ‖\widehat{∂^l f}(m)‖²`, and `∂^l f` is continuous.
* Bessel's inequality (`bessel_continuous`): for continuous `g`,
  `Σ_m ‖ĝ(m)‖² ≤ ∫_{unitCube} ‖g‖²`.

Summing the pointwise comparison over `m` and using Bessel for `g = f` and for each `g = ∂^l f`
gives the claim with `C = 2 ^ k`.
-/

noncomputable section

namespace Work.Diff.STE

open BigOperators MeasureTheory

/-- `ENormSq 0` is the `L²`-norm squared on the cube: there is exactly one `0`-fold derivative,
namely `f` itself, and the empty product of directions contributes a single term. -/
lemma ENormSq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℂ) :
    ENormSq 0 f = ∫ x in unitCube (ι := ι), ‖f x‖ ^ 2 := by
  simp [ENormSq, pdVec, pdList]

/-- **Sobolev comparison on the torus.**  There is a constant `C` (namely `2 ^ k`) such that for
every `Cᵏ`, `1`-periodic `f`

  `CSq k (fourierCoeff f) ≤ C * (ENormSq k f + ENormSq 0 f)`.

See the module docstring for the proof. -/
theorem CSq_le_ENormSq {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : (ι → ℝ) → ℂ), ContDiff ℝ k f → Work.Diff.STE.Periodic1 f →
      Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff f)
        ≤ C * (Work.Diff.STE.ENormSq k f + Work.Diff.STE.ENormSq 0 f) := by
  refine ⟨2 ^ k, by positivity, fun f hf hper => ?_⟩
  have hcontf : Continuous f := hf.continuous
  -- Bessel for `f` itself
  have hbase : Summable (fun m : ι → ℤ => ‖fourierCoeff f m‖ ^ 2) :=
    (bessel_continuous f hcontf).1
  have hbase_le : (∑' m : ι → ℤ, ‖fourierCoeff f m‖ ^ 2) ≤ ∫ x in unitCube, ‖f x‖ ^ 2 :=
    (bessel_continuous f hcontf).2
  -- Bessel for the iterated derivatives
  have hderiv : ∀ l : Fin k → ι,
      Summable (fun m : ι → ℤ => ‖fourierCoeff (pdVec k l f) m‖ ^ 2) :=
    fun l => (bessel_continuous (pdVec k l f) (continuous_pdVec k l f hf)).1
  have hderiv_le : ∀ l : Fin k → ι, (∑' m : ι → ℤ, ‖fourierCoeff (pdVec k l f) m‖ ^ 2)
      ≤ ∫ x in unitCube, ‖pdVec k l f x‖ ^ 2 :=
    fun l => (bessel_continuous (pdVec k l f) (continuous_pdVec k l f hf)).2
  have hsum_l : Summable (fun m : ι → ℤ =>
      ∑ l : Fin k → ι, ‖fourierCoeff (pdVec k l f) m‖ ^ 2) :=
    summable_sum (fun l _ => hderiv l)
  -- the pointwise weight comparison
  have hpt : ∀ m : ι → ℤ, wt m ^ k * ‖fourierCoeff f m‖ ^ 2
      ≤ 2 ^ k * ‖fourierCoeff f m‖ ^ 2
        + 2 ^ k * ∑ l : Fin k → ι, ‖fourierCoeff (pdVec k l f) m‖ ^ 2 := by
    intro m
    have h1 := wt_pow_le_wordSum k m
    have h2 : ∀ l : Fin k → ι,
        (∏ i, (2 * Real.pi * ((m (l i) : ℤ) : ℝ)) ^ 2) * ‖fourierCoeff f m‖ ^ 2
        = ‖fourierCoeff (pdVec k l f) m‖ ^ 2 :=
      fun l => (fourierCoeff_pdVec_normSq k l f hf hper m).symm
    calc wt m ^ k * ‖fourierCoeff f m‖ ^ 2
        ≤ (2 ^ k * (1 + ∑ l : Fin k → ι,
            ∏ i, (2 * Real.pi * ((m (l i) : ℤ) : ℝ)) ^ 2)) * ‖fourierCoeff f m‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = 2 ^ k * ‖fourierCoeff f m‖ ^ 2
            + 2 ^ k * ((∑ l : Fin k → ι,
                ∏ i, (2 * Real.pi * ((m (l i) : ℤ) : ℝ)) ^ 2) * ‖fourierCoeff f m‖ ^ 2) := by
          ring
      _ = 2 ^ k * ‖fourierCoeff f m‖ ^ 2
            + 2 ^ k * ∑ l : Fin k → ι,
                ((∏ i, (2 * Real.pi * ((m (l i) : ℤ) : ℝ)) ^ 2) * ‖fourierCoeff f m‖ ^ 2) := by
          rw [Finset.sum_mul]
      _ = 2 ^ k * ‖fourierCoeff f m‖ ^ 2
            + 2 ^ k * ∑ l : Fin k → ι, ‖fourierCoeff (pdVec k l f) m‖ ^ 2 := by
          simp only [h2]
  -- the majorant family is summable, hence so is the weighted family
  have hmaj : Summable (fun m : ι → ℤ => 2 ^ k * ‖fourierCoeff f m‖ ^ 2
      + 2 ^ k * ∑ l : Fin k → ι, ‖fourierCoeff (pdVec k l f) m‖ ^ 2) :=
    (hbase.mul_left _).add (hsum_l.mul_left _)
  have hLHS : Summable (fun m : ι → ℤ => wt m ^ k * ‖fourierCoeff f m‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (pow_nonneg (wt_pos m).le k) (sq_nonneg _))
      hpt hmaj
  have hkey := hLHS.tsum_le_tsum hpt hmaj
  -- interchange the (finite) sum over derivative directions with the coefficient sum
  have hswap : (∑' m : ι → ℤ, ∑ l : Fin k → ι, ‖fourierCoeff (pdVec k l f) m‖ ^ 2)
      = ∑ l : Fin k → ι, ∑' m : ι → ℤ, ‖fourierCoeff (pdVec k l f) m‖ ^ 2 :=
    Summable.tsum_finsetSum (s := Finset.univ) (fun l _ => hderiv l)
  have heval : (∑' m : ι → ℤ, (2 ^ k * ‖fourierCoeff f m‖ ^ 2
        + 2 ^ k * ∑ l : Fin k → ι, ‖fourierCoeff (pdVec k l f) m‖ ^ 2))
      = 2 ^ k * (∑' m : ι → ℤ, ‖fourierCoeff f m‖ ^ 2)
        + 2 ^ k * ∑ l : Fin k → ι, ∑' m : ι → ℤ, ‖fourierCoeff (pdVec k l f) m‖ ^ 2 := by
    rw [Summable.tsum_add (hbase.mul_left _) (hsum_l.mul_left _), tsum_mul_left, tsum_mul_left]
    rw [hswap]
  have hfinal : (∑ l : Fin k → ι, ∑' m : ι → ℤ, ‖fourierCoeff (pdVec k l f) m‖ ^ 2)
      ≤ ENormSq k f := by
    calc ∑ l : Fin k → ι, ∑' m : ι → ℤ, ‖fourierCoeff (pdVec k l f) m‖ ^ 2
        ≤ ∑ l : Fin k → ι, ∫ x in unitCube, ‖pdVec k l f x‖ ^ 2 :=
          Finset.sum_le_sum (fun l _ => hderiv_le l)
      _ = ENormSq k f := rfl
  calc CSq k (fourierCoeff f)
      = ∑' m : ι → ℤ, wt m ^ k * ‖fourierCoeff f m‖ ^ 2 := rfl
    _ ≤ ∑' m : ι → ℤ, (2 ^ k * ‖fourierCoeff f m‖ ^ 2
          + 2 ^ k * ∑ l : Fin k → ι, ‖fourierCoeff (pdVec k l f) m‖ ^ 2) := hkey
    _ = 2 ^ k * (∑' m : ι → ℤ, ‖fourierCoeff f m‖ ^ 2)
        + 2 ^ k * ∑ l : Fin k → ι, ∑' m : ι → ℤ, ‖fourierCoeff (pdVec k l f) m‖ ^ 2 := heval
    _ ≤ 2 ^ k * (∫ x in unitCube, ‖f x‖ ^ 2) + 2 ^ k * ENormSq k f :=
        add_le_add (mul_le_mul_of_nonneg_left hbase_le (by positivity))
          (mul_le_mul_of_nonneg_left hfinal (by positivity))
    _ = 2 ^ k * (ENormSq k f + ENormSq 0 f) := by rw [ENormSq_zero]; ring

end Work.Diff.STE
