/-
# Reduction of Bourgain's polynomial ergodic theorem to a discrete ℓᵖ estimate

This file isolates the *transference* half of Bourgain's proof.  The two theorems below
take as hypothesis a purely discrete (counting-measure) ℓᵖ estimate for the polynomial
density kernel `k_N(j) = (1/N) · #{i < N : P(i) = j}` and transfer it, via Calderón's
transference principle, to an estimate for the ergodic averages
`A_N f x = (1/N) ∑_{i<N} f (T^[P(i)] x)`.

The remaining (analytic) input is exactly the discrete ℓᵖ maximal / short-variation
estimate for polynomial Weyl kernels, which is the content of the circle method.
-/
import ChallengeDeps
import Submission.PolynomialKernel
import Submission.Commons.Dynamics.Transference.calderon_transference_maximal
import Submission.Commons.Dynamics.Transference.calderon_transference_variation
import Submission.Commons.Analysis.Oscillation.ae_tendsto_of_block_difference

open LeanEval.Dynamics.BourgainErgodic
open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Submission

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The polynomial ergodic average along the exponents `P(0), P(1), …, P(N-1)`,
written with the value of `P` read as a natural number. -/
noncomputable def polyAvg (P : Polynomial ℤ) (T : X → X) (f : X → ℝ) (N : ℕ) (x : X) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, f (T^[(P.eval (i : ℤ)).toNat] x)

theorem polyAvg_eq_kernel (P : Polynomial ℤ) (T : X → X) (f : X → ℝ) (N : ℕ) (x : X) :
    polyAvg P T f N x
      = ∑ j ∈ Finset.range (polySupport P N), polyKernel P N j * f (T^[j] x) :=
  (sum_polyKernel_mul_orbit P N f T x).symm

/-- **Transference of the discrete maximal inequality.**  If the polynomial density
kernels satisfy the discrete ℓᵖ maximal inequality on `ℤ` with constant `C`, then the
ergodic maximal function of the polynomial averages is bounded on `L^p(μ)` with
constant `2C`. -/
theorem ergodic_polynomial_maximal [IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) (P : Polynomial ℤ)
    {p : ℝ} (hp : 1 ≤ p) {C : ℝ} (hC : 0 ≤ C)
    (hℓp : ∀ g : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n, (⨆ (N : ℕ),
          ‖∑ j ∈ Finset.range (polySupport P N), polyKernel P N j * g (n + j)‖ₑ) ^ p
            ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ n, ‖g n‖ₑ ^ p ∂Measure.count)
    {f : X → ℝ} (hf : Measurable f) (hfp : ∫⁻ x, ‖f x‖ₑ ^ p ∂μ < ⊤) :
    ∫⁻ x, (⨆ (N : ℕ), ‖polyAvg P T f N x‖ₑ) ^ p ∂μ
      ≤ ENNReal.ofReal ((2 * C) ^ p) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  have h := Commons.Dynamics.Transference.calderon_transference_maximal (μ := μ) hT hp hC
    (J := polySupport P) (k := polyKernel P)
    (fun N j hj => polyKernel_eq_zero_of_support P N j hj)
    (fun N => sum_abs_polyKernel_le_one P N) hℓp hf hfp
  have hcongr : ∀ x : X, (⨆ (N : ℕ),
        ‖∑ j ∈ Finset.range (polySupport P N), polyKernel P N j * f (T^[j] x)‖ₑ)
      = ⨆ (N : ℕ), ‖polyAvg P T f N x‖ₑ :=
    fun x => iSup_congr (fun N => by rw [polyAvg_eq_kernel])
  calc ∫⁻ x, (⨆ (N : ℕ), ‖polyAvg P T f N x‖ₑ) ^ p ∂μ
      = ∫⁻ x, (⨆ (N : ℕ),
          ‖∑ j ∈ Finset.range (polySupport P N), polyKernel P N j * f (T^[j] x)‖ₑ) ^ p ∂μ :=
        lintegral_congr (fun x => by rw [hcongr x])
    _ ≤ ENNReal.ofReal ((2 * C) ^ p) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := h

/-- **Transference of the discrete short-variation inequality.**  If the polynomial
density kernels satisfy the discrete ℓᵖ short-variation inequality on `ℤ` with constant
`C` (over the dyadic blocks `[t M, t (M+1))`), then so do the ergodic polynomial
averages, with constant `2C`. -/
theorem ergodic_polynomial_short_variation [IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) (P : Polynomial ℤ)
    {t : ℕ → ℕ} (hmono : Monotone t)
    {p : ℝ} (hp : 1 ≤ p) {C : ℝ} (hC : 0 ≤ C)
    (hℓp : ∀ (M₀ : ℕ) (g : ℕ → ℝ), (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n, ‖∑ M ∈ Finset.range M₀, ∑ N ∈ Finset.Icc (t M) (t (M + 1) - 1),
          |(∑ j ∈ Finset.range (polySupport P (N + 1)), polyKernel P (N + 1) j * g (n + j))
            - (∑ j ∈ Finset.range (polySupport P N), polyKernel P N j * g (n + j))|‖ₑ ^ p
            ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ n, ‖g n‖ₑ ^ p ∂Measure.count)
    {f : X → ℝ} (hf : Measurable f) (hfp : ∫⁻ x, ‖f x‖ₑ ^ p ∂μ < ⊤) :
    ∀ M₀ : ℕ,
      ∫⁻ x, ‖∑ M ∈ Finset.range M₀, ∑ N ∈ Finset.Icc (t M) (t (M + 1) - 1),
          |polyAvg P T f (N + 1) x - polyAvg P T f N x|‖ₑ ^ p ∂μ
        ≤ ENNReal.ofReal ((2 * C) ^ p) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  have h := Commons.Dynamics.Transference.calderon_transference_variation (μ := μ) hT hmono
    hp hC (J := polySupport P) (k := polyKernel P)
    (fun N j hj => polyKernel_eq_zero_of_support P N j hj)
    (fun N => sum_abs_polyKernel_le_one P N) hℓp hf hfp
  intro M₀
  have hcongr : ∀ x : X,
      ‖∑ M ∈ Finset.range M₀, ∑ N ∈ Finset.Icc (t M) (t (M + 1) - 1),
          |(∑ j ∈ Finset.range (polySupport P (N + 1)), polyKernel P (N + 1) j * f (T^[j] x))
            - (∑ j ∈ Finset.range (polySupport P N), polyKernel P N j * f (T^[j] x))|‖ₑ
        = ‖∑ M ∈ Finset.range M₀, ∑ N ∈ Finset.Icc (t M) (t (M + 1) - 1),
          |polyAvg P T f (N + 1) x - polyAvg P T f N x|‖ₑ := by
    intro x
    congr 1
    refine Finset.sum_congr rfl (fun M _ => Finset.sum_congr rfl (fun N _ => ?_))
    rw [polyAvg_eq_kernel, polyAvg_eq_kernel]
  calc ∫⁻ x, ‖∑ M ∈ Finset.range M₀, ∑ N ∈ Finset.Icc (t M) (t (M + 1) - 1),
          |polyAvg P T f (N + 1) x - polyAvg P T f N x|‖ₑ ^ p ∂μ
      = ∫⁻ x, ‖∑ M ∈ Finset.range M₀, ∑ N ∈ Finset.Icc (t M) (t (M + 1) - 1),
          |(∑ j ∈ Finset.range (polySupport P (N + 1)), polyKernel P (N + 1) j * f (T^[j] x))
            - (∑ j ∈ Finset.range (polySupport P N), polyKernel P N j * f (T^[j] x))|‖ₑ ^ p ∂μ :=
        lintegral_congr (fun x => by rw [hcongr x])
    _ ≤ ENNReal.ofReal ((2 * C) ^ p) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := h M₀


/-- **Assembly step.**  Given the discrete short-variation inequality for the polynomial
density kernel, and a.e. convergence of the polynomial ergodic averages along a lacunary
subsequence `t`, the full polynomial ergodic averages converge a.e. -/
theorem ergodic_polynomial_ae_of_discrete [IsProbabilityMeasure μ]
    {T : X → X} (hT : MeasurePreserving T μ μ) (P : Polynomial ℤ)
    {t : ℕ → ℕ} (hmono : Monotone t) (ht : Tendsto t atTop atTop)
    {q : ℝ} (hq : 1 ≤ q) {C : ℝ} (hC : 0 ≤ C)
    (hℓp : ∀ (M₀ : ℕ) (g : ℕ → ℝ), (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n, ‖∑ M ∈ Finset.range M₀, ∑ N ∈ Finset.Icc (t M) (t (M + 1) - 1),
          |(∑ j ∈ Finset.range (polySupport P (N + 1)), polyKernel P (N + 1) j * g (n + j))
            - (∑ j ∈ Finset.range (polySupport P N), polyKernel P N j * g (n + j))|‖ₑ ^ q
            ∂Measure.count
        ≤ ENNReal.ofReal (C ^ q) * ∫⁻ n, ‖g n‖ₑ ^ q ∂Measure.count)
    {f : X → ℝ} (hf : Measurable f) (hfp : ∫⁻ x, ‖f x‖ₑ ^ q ∂μ < ⊤)
    (hlac : ∀ᵐ x ∂μ, ∃ L : ℝ, Tendsto (fun n => polyAvg P T f (t n) x) atTop (𝓝 L)) :
    ∃ F : X → ℝ, ∀ᵐ x ∂μ, Tendsto (fun N => polyAvg P T f N x) atTop (𝓝 (F x)) := by
  have hvar := ergodic_polynomial_short_variation (μ := μ) hT P hmono hq hC hℓp hf hfp
  -- Select the a.e. limit along the lacunary subsequence.
  classical
  obtain ⟨L, hL⟩ : ∃ L : X → ℝ, ∀ᵐ x ∂μ,
      Tendsto (fun n => polyAvg P T f (t n) x) atTop (𝓝 (L x)) := by
    refine ⟨fun x => if h : ∃ L : ℝ, Tendsto (fun n => polyAvg P T f (t n) x) atTop (𝓝 L)
      then h.choose else 0, ?_⟩
    filter_upwards [hlac] with x hx
    rw [dif_pos hx]
    exact hx.choose_spec
  have hmeas : ∀ n : ℕ, Measurable (fun x : X => polyAvg P T f n x) := by
    intro n
    simp only [polyAvg]
    exact measurable_const.mul (Finset.measurable_sum _ (fun i _ =>
      hf.comp (hT.measurable.iterate _)))
  have hKtop : ENNReal.ofReal ((2 * C) ^ q) * ∫⁻ x, ‖f x‖ₑ ^ q ∂μ < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfp
  have hbd : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ M₀ : ℕ,
      ∫⁻ x, ‖∑ M ∈ Finset.range M₀, ∑ N ∈ Finset.Icc (t M) (t (M + 1) - 1),
          |polyAvg P T f (N + 1) x - polyAvg P T f N x|‖ₑ ^ q ∂μ ≤ K :=
    ⟨_, hKtop, fun M₀ => hvar M₀⟩
  exact ⟨L, Commons.Analysis.Oscillation.ae_tendsto_of_block_difference (μ := μ)
    (u := fun N x => polyAvg P T f N x) (t := t) (L := L) hq hmono ht hmeas hL hbd⟩

end Submission
