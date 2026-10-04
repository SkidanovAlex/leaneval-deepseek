import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.Lead.coeff_decay_of_BNorm_le
import Submission.Work.Diff.STE.Lead.coeffFun_bound_and_decay
import Submission.Work.Diff.STE.Lead.CoeffRepr
import Submission.Work.Diff.STE.Lead.Rper_contDiff
import Submission.Work.Diff.STE.Lead.transfer_tendsto
import Submission.Work.Diff.STE.Lead.fourierCoeff_le_sqrt_BNorm
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.Lead.Squeeze.CSq_tendsto_zero_of_lipschitz_decay
import Submission.Work.Diff.STE.Lead.coeff_lipschitz_limit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `D.BNorm k (U σ - U t) → 0` as `σ → t` (in `[0,τ₀)`) from Lipschitz coefficients

The limit section `U` of the Galerkin scheme is obtained coefficientwise; the Lipschitz-in-time
bound `hLip` (uniform in the Galerkin index `m`) on the coefficients of the approximants `u m` and
the *uniform* convergence `hconv` of those coefficients to those of `U` upgrade to a Lipschitz
bound for the coefficients of `U` itself.  Together with the uniform decay of the coefficients of
`U` (from the uniform `BNorm` bound `hUB`) this gives, component by component, convergence of the
weighted `ℓ²` masses `CSq k` of the *difference* of the coefficient families, hence — because
`D.BNorm` is the finite sum of those masses over the charts and the frame indices — convergence of
`D.BNorm k (U σ - U t)` to `0`.

## Contents

* `coeff_decay_of_BNorm_le_Ico`: the uniform (in `t`) weighted decay `‖û‖ ⟨μ⟩^M ≤ √(B (2M))` of the
  coefficients of `U t`, which is the decay input of the squeeze below;
* `BNorm_sub_eq_sum_coeff`: `D.BNorm k (X - Y)` as the triple sum of the weighted `ℓ²` masses of
  the differences of the Fourier coefficient families (additivity of the coefficient functional);
* `BNorm_continuous_of_coeff_lipschitz`: the target.
-/

namespace Work.Diff.STE.Lead

open Filter
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## Uniform weighted decay of the coefficients of the limit section -/

/-- **Uniform (in `t`) weighted decay of the Fourier coefficients of `U t`.**  A single Fourier
coefficient of a periodised localised component is dominated by the weighted `ℓ²` mass
`CSq (2M) ≤ D.BNorm (2M) ≤ B (2M)`, with no dependence on the point `t ∈ [0,τ₀)` of the section, so
`‖û(μ)‖ ⟨μ⟩^M ≤ √(B (2M))` uniformly. -/
lemma coeff_decay_of_BNorm_le_Ico
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (τ₀ : ℝ) (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hsmU : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, Work.Diff.STE.D.ChartData (I := I) (M := M) (U t))
    (B : ℕ → ℝ) (hB : ∀ k : ℕ, 0 ≤ B k)
    (hUB : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k : ℕ, D.BNorm k (U t) ≤ B k) :
    ∀ M₀ : ℕ, ∀ t ∈ Set.Ico (0 : ℝ) τ₀,
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖ * (Work.Diff.STE.wt μ) ^ M₀
        ≤ Real.sqrt (B (2 * M₀)) := by
  intro M₀ t ht i a b μ
  obtain ⟨hsm, hper⟩ := Rper_contDiff_and_periodic (I := I) (M := M) D (U t) (hsmU t ht) i a b
  have hsumm : Summable (fun k : Fin (Module.finrank ℝ E) → ℤ =>
      (Work.Diff.STE.wt k) ^ (2 * M₀)
        * ‖Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) k‖ ^ 2) :=
    Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff _ hsm hper (2 * M₀)
  -- a single summand is dominated by the whole nonnegative series
  have hterm : (Work.Diff.STE.wt μ) ^ (2 * M₀)
      * ‖Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖ ^ 2
      ≤ Work.Diff.STE.CSq (2 * M₀) (Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b)) := by
    have h := Summable.le_tsum hsumm μ (fun j _ =>
      mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos j)) _) (sq_nonneg _))
    simpa only [Work.Diff.STE.CSq, mul_comm] using h
  -- the single component mass is dominated by the composite norm
  have hBN : Work.Diff.STE.CSq (2 * M₀) (Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b))
      ≤ D.BNorm (2 * M₀) (U t) := by
    change Work.Diff.STE.CSq (2 * M₀) (Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b))
      ≤ ∑ i' : ι₀, ∑ a' : Fin (Module.finrank ℝ E),
          ∑ b' : Fin (Module.finrank ℝ E),
          Work.Diff.STE.CSq (2 * M₀) (Work.Diff.STE.fourierCoeff (D.Rper i' (U t) a' b'))
    exact Work.Diff.STE.sum3_single_le
      (fun i' a' b' => Work.Diff.STE.CSq (2 * M₀)
        (Work.Diff.STE.fourierCoeff (D.Rper i' (U t) a' b')))
      (fun i' a' b' => Work.Diff.STE.CSq_nonneg (2 * M₀) _) i a b
  rw [Real.le_sqrt (mul_nonneg (norm_nonneg _)
    (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos μ)) _)) (hB (2 * M₀))]
  rw [mul_pow, ← pow_mul, Nat.mul_comm M₀ 2, mul_comm]
  exact le_trans hterm (le_trans hBN (hUB t ht (2 * M₀)))

/-! ## `BNorm` of a difference as a sum of masses of coefficient differences -/

/-- **Additivity of the composite norm.**  `D.BNorm k (X - Y)` is the triple sum, over the charts
and the two frame indices, of the weighted `ℓ²` masses `CSq k` of the *differences* of the Fourier
coefficient families of the periodised localised components.  The only input is that the
coefficient functional is additive in the section (`Rper_fourierCoeff_sub`, whose hypotheses are
supplied by `R_contDiff_of_chartData` from the chart-smoothness of `X`, `Y` and `X - Y`). -/
lemma BNorm_sub_eq_sum_coeff
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (X Y : Work.Diff.STE.Bil (I := I) (M := M)) (k : ℕ)
    (hX : Work.Diff.STE.D.ChartData (I := I) (M := M) X)
    (hY : Work.Diff.STE.D.ChartData (I := I) (M := M) Y) :
    D.BNorm k (X - Y) = ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E), Work.Diff.STE.CSq k
        (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
          Work.Diff.STE.fourierCoeff (D.Rper i X a b) μ
            - Work.Diff.STE.fourierCoeff (D.Rper i Y a b) μ) := by
  have hXY : Work.Diff.STE.D.ChartData (I := I) (M := M) (X - Y) :=
    Work.Diff.STE.Lead.ChartData_sub X Y hX hY
  simp only [Work.Diff.STE.B3Data.BNorm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ =>
    Finset.sum_congr rfl (fun b _ => ?_)))
  refine congrArg (Work.Diff.STE.CSq k) (funext fun μ => ?_)
  exact Work.Diff.STE.Lead.Rper_fourierCoeff_sub D X Y i a b μ
    (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D (X - Y) hXY i a b)
    (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D X hX i a b)
    (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D Y hY i a b)

/-! ## The target -/

theorem BNorm_continuous_of_coeff_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (τ₀ : ℝ) (B : ℕ → ℝ) (hB : ∀ j : ℕ, 0 ≤ B j) (L : ℝ) (hL : 0 ≤ L)
    (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : ∀ (m : ℕ) (t : ℝ), Work.Diff.STE.D.ChartData (I := I) (M := M) (u m t))
    (hsmU : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, Work.Diff.STE.D.ChartData (I := I) (M := M) (U t))
    (huB : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ k : ℕ, D.BNorm k (u m t) ≤ B k)
    (hUB : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k : ℕ, D.BNorm k (U t) ≤ B k)
    (hLip : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ)
      (m : ℕ), ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ t' ∈ Set.Ico (0 : ℝ) τ₀,
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ
        - Work.Diff.STE.fourierCoeff (D.Rper i (u m t') a b) μ‖ ≤ L * |t - t'|)
    (hconv : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      TendstoUniformlyOn
        (fun (m : ℕ) (t : ℝ) => Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ)
        (fun (t : ℝ) => Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ)
        Filter.atTop (Set.Ico (0 : ℝ) τ₀)) :
    ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k : ℕ,
      Filter.Tendsto (fun σ : ℝ => D.BNorm k (U σ - U t))
        (nhdsWithin t (Set.Ico (0 : ℝ) τ₀)) (nhds 0) := by
  intro t ht k
  -- Lipschitz in time for the coefficients of the limit section
  have hlipU := coeff_lipschitz_limit (I := I) (M := M) D τ₀ L u U hLip hconv
  -- uniform weighted decay of the coefficients of the limit section
  have hdecU := coeff_decay_of_BNorm_le_Ico (I := I) (M := M) D τ₀ U hsmU B hB hUB
  -- componentwise convergence of the weighted `ℓ²` masses of the coefficient differences
  have key : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Filter.Tendsto (fun σ : ℝ => Work.Diff.STE.CSq k
          (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
            Work.Diff.STE.fourierCoeff (D.Rper i (U σ) a b) μ
              - Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ))
        (nhdsWithin t (Set.Ico (0 : ℝ) τ₀)) (nhds 0) := by
    intro i a b
    refine Squeeze.CSq_tendsto_zero_of_lipschitz_decay
      (b := fun σ μ => Work.Diff.STE.fourierCoeff (D.Rper i (U σ) a b) μ
        - Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ)
      (s := Set.Ico (0 : ℝ) τ₀) (t := t) k L hL ?_ ?_
    · intro σ hσ μ
      exact hlipU i a b μ σ hσ t ht
    · intro M₀
      refine ⟨2 * Real.sqrt (B (2 * M₀)), mul_nonneg (by norm_num) (Real.sqrt_nonneg _), ?_⟩
      intro σ hσ μ
      have h1 := hdecU M₀ σ hσ i a b μ
      have h2 := hdecU M₀ t ht i a b μ
      have hwt : (0 : ℝ) ≤ (Work.Diff.STE.wt μ) ^ M₀ :=
        pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos μ)) _
      calc ‖Work.Diff.STE.fourierCoeff (D.Rper i (U σ) a b) μ
              - Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖ * (Work.Diff.STE.wt μ) ^ M₀
          ≤ (‖Work.Diff.STE.fourierCoeff (D.Rper i (U σ) a b) μ‖
              + ‖Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖)
              * (Work.Diff.STE.wt μ) ^ M₀ :=
            mul_le_mul_of_nonneg_right (norm_sub_le _ _) hwt
        _ = ‖Work.Diff.STE.fourierCoeff (D.Rper i (U σ) a b) μ‖ * (Work.Diff.STE.wt μ) ^ M₀
              + ‖Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖
                * (Work.Diff.STE.wt μ) ^ M₀ := by ring
        _ ≤ Real.sqrt (B (2 * M₀)) + Real.sqrt (B (2 * M₀)) := add_le_add h1 h2
        _ = 2 * Real.sqrt (B (2 * M₀)) := by ring
  -- `D.BNorm` of the difference is the triple sum of the componentwise masses
  have hev : (fun σ : ℝ => D.BNorm k (U σ - U t)) =ᶠ[nhdsWithin t (Set.Ico (0 : ℝ) τ₀)]
      (fun σ : ℝ => ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E), Work.Diff.STE.CSq k
          (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
            Work.Diff.STE.fourierCoeff (D.Rper i (U σ) a b) μ
              - Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ)) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact BNorm_sub_eq_sum_coeff (I := I) (M := M) D (U σ) (U t) k (hsmU σ hσ) (hsmU t ht)
  have hsum : Filter.Tendsto (fun σ : ℝ => ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
      ∑ b : Fin (Module.finrank ℝ E), Work.Diff.STE.CSq k
        (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
          Work.Diff.STE.fourierCoeff (D.Rper i (U σ) a b) μ
            - Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ))
      (nhdsWithin t (Set.Ico (0 : ℝ) τ₀)) (nhds 0) := by
    have h0 := tendsto_finsetSum (Finset.univ : Finset ι₀) (fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin (Module.finrank ℝ E))) (fun a _ =>
        tendsto_finsetSum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun b _ => key i a b)))
    simpa using h0
  exact hsum.congr' hev.symm

end Work.Diff.STE.Lead
