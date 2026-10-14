import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.Auxiliary.integral_mul_div_eq_neg_inner_gradient
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.tendsto_lamb_decay
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.PressureOn.weakDiv_timeDeriv
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn

noncomputable section

/-! ## 2. `⟨D, ΔW⟩ = 0` for test fields `W` -/


/-! ## 3. The pointwise identity `Φ = ∇q + c` (mollified approximation) -/

/-- **The constant.**  There is a constant vector `c` with `⟨D, ψ⟩ = ⟪c, ∫ψ⟫` for every test field
`ψ`.  The mean-zero part comes from the mollified pair (smooth setting), the value of `c` from
`cᵢ = ⟨D, θ eᵢ⟩` for a fixed test function `θ` with `∫θ = 1`. -/
theorem exists_const_Dpair (q : R3 → ℝ) (Φ : R3 → R3) (hq : Continuous q)
    (hΦ : Continuous Φ)
    (hq0 : Filter.Tendsto q (Filter.cocompact R3) (nhds 0))
    (hΦ0 : Filter.Tendsto Φ (Filter.cocompact R3) (nhds 0))
    (hdiv : ∀ φ : R3 → ℝ, (∀ n : ℕ, ContDiff ℝ n φ) → HasCompactSupport φ →
      ∫ x, inner ℝ (Φ x) (gradient φ x) = -∫ x, q x * laplaceTrace φ x)
    (hcurl : ∀ ψ : R3 → R3, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      ∫ x, inner ℝ (Φ x) (FiniteTimeSingularity.vorticity ψ x) = 0) :
    ∃ c : R3, ∀ ψ : R3 → R3, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      Dpair q Φ ψ = inner ℝ c (∫ x, ψ x) := by
  exact MollAux.exists_const_Dpair_aux q Φ hq hΦ hq0 hΦ0 hdiv hcurl

/-- **The constant vanishes.**  If `⟨D, ψ⟩ = ⟪c, ∫ψ⟫` for all test fields `ψ` and `Φ`, `q` both
tend to `0` at infinity, then `c = 0`.  Indeed for the spreading test functions
`θ_ρ(x) = ρ⁻³θ(x/ρ)` (`∫θ = 1`) one has `cᵢ = ⟪c, ∫θ_ρeᵢ⟫ = ⟨D, θ_ρeᵢ⟩ = ∫Φᵢθ_ρ + ∫q∂ᵢθ_ρ → 0`
as `ρ → ∞`, by dominated convergence and the decay of `Φ` and `q`. -/
theorem const_eq_zero_of_decay (q : R3 → ℝ) (Φ : R3 → R3) (hq : Continuous q) (hΦ : Continuous Φ)
    (hq0 : Filter.Tendsto q (Filter.cocompact R3) (nhds 0))
    (hΦ0 : Filter.Tendsto Φ (Filter.cocompact R3) (nhds 0))
    (c : R3) (hc : ∀ ψ : R3 → R3, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      Dpair q Φ ψ = inner ℝ c (∫ x, ψ x)) :
    c = 0 := by
  exact Weyl.const_eq_zero_of_decay q Φ hq hΦ hq0 hΦ0 c hc

/-! ## 4. From the weak identity to the pointwise derivative -/

/-- The standard basis vector `e i` is a unit vector for the inner product, so that
`⟪v, e i⟫ = v i`. -/
theorem inner_e_eq (v : R3) (i : Fin 3) : inner ℝ v (FiniteTimeSingularity.e i) = v i := by
  rw [PiLp.inner_apply]
  simp only [FiniteTimeSingularity.e]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The divergence of `k • e i` is the partial derivative `v ↦ (fderiv k v) (e i)`. -/
theorem div_smul_e (k : R3 → ℝ) (hk : ∀ n : ℕ, ContDiff ℝ n k) (i : Fin 3) (x : R3) :
    FiniteTimeSingularity.div (fun y => k y • FiniteTimeSingularity.e i) x
      = (fderiv ℝ k x) (FiniteTimeSingularity.e i) := by
  rw [FiniteTimeSingularity.div]
  rw [fderiv_smul_const ((hk 1).differentiable (by norm_num) x)]
  exact LinearMap.trace_smulRight _ _

/-- **The weak gradient.**  If `⟨D, ψ⟩ = 0` for every test field `ψ`, then for every test function
`k` and every coordinate direction `i`, `∫ k Φᵢ = -∫ q ∂ᵢk`, i.e. `∂ᵢq = Φᵢ` as distributions. -/
theorem weak_gradient (q : R3 → ℝ) (Φ : R3 → R3)
    (h : ∀ ψ : R3 → R3, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ → Dpair q Φ ψ = 0)
    (i : Fin 3) (k : R3 → ℝ) (hk : ∀ n : ℕ, ContDiff ℝ n k) (hkc : HasCompactSupport k) :
    ∫ x, k x * Φ x i = -∫ x, q x * (fderiv ℝ k x) (FiniteTimeSingularity.e i) := by
  have hsm : ∀ n : ℕ, ContDiff ℝ n (fun y : R3 => k y • FiniteTimeSingularity.e i) :=
    fun n => (hk n).smul_const _
  have hcs : HasCompactSupport (fun y : R3 => k y • FiniteTimeSingularity.e i) :=
    hkc.mono (by
      intro y hy
      simp only [Function.mem_support] at hy ⊢
      intro hk
      exact hy (by simp [hk]))
  have h0 := h _ hsm hcs
  -- rewrite both terms of the pairing
  have h1 : ∫ x, inner ℝ (Φ x) (k x • FiniteTimeSingularity.e i) = ∫ x, k x * Φ x i := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [real_inner_smul_right, inner_e_eq]
  have h2 : ∫ x, q x * FiniteTimeSingularity.div (fun y : R3 => k y • FiniteTimeSingularity.e i) x
      = ∫ x, q x * (fderiv ℝ k x) (FiniteTimeSingularity.e i) := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [div_smul_e k hk i x]
  have hkey : Dpair q Φ (fun y : R3 => k y • FiniteTimeSingularity.e i)
      = (∫ x, k x * Φ x i)
        + (∫ x, q x * (fderiv ℝ k x) (FiniteTimeSingularity.e i)) := by
    rw [Dpair_apply]
    exact congrArg₂ (· + ·) h1 h2
  rw [hkey] at h0
  linarith [h0]

/-! ## 5. The theorem -/

theorem weyl_pair (q : R3 → ℝ) (Φ : R3 → R3) (hq : Continuous q) (hΦ : Continuous Φ)
    (hq0 : Filter.Tendsto q (Filter.cocompact R3) (nhds 0))
    (hΦ0 : Filter.Tendsto Φ (Filter.cocompact R3) (nhds 0))
    (hdiv : ∀ φ : R3 → ℝ, (∀ n : ℕ, ContDiff ℝ n φ) → HasCompactSupport φ →
      ∫ x, inner ℝ (Φ x) (gradient φ x) = -∫ x, q x * laplaceTrace φ x)
    (hcurl : ∀ ψ : R3 → R3, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      ∫ x, inner ℝ (Φ x) (FiniteTimeSingularity.vorticity ψ x) = 0) :
    ∀ x, HasFDerivAt q (innerSL ℝ (Φ x)) x := by
  -- Step 1: the constant `c` with `⟨D, ψ⟩ = ⟪c, ∫ψ⟫` for all test fields.
  obtain ⟨c, hc⟩ := exists_const_Dpair q Φ hq hΦ hq0 hΦ0 hdiv hcurl
  -- Step 2: the decay of `Φ` and `q` forces `c = 0`.
  have hc0 : c = 0 := const_eq_zero_of_decay q Φ hq hΦ hq0 hΦ0 c hc
  -- Step 3: hence `⟨D, ψ⟩ = 0` for all test fields.
  have hzero : ∀ ψ : R3 → R3, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      Dpair q Φ ψ = 0 := by
    intro ψ hψ hψc
    rw [hc ψ hψ hψc, hc0]
    simp
  -- Step 4: `∂ᵢq = Φᵢ` weakly.
  have hgrad : ∀ i : Fin 3, ∀ k : R3 → ℝ, (∀ n : ℕ, ContDiff ℝ n k) → HasCompactSupport k →
      ∫ x, k x * Φ x i = -∫ x, q x * (fderiv ℝ k x) (FiniteTimeSingularity.e i) :=
    fun i => weak_gradient q Φ hzero i
  -- Step 5: upgrade the weak gradient to the pointwise Fréchet derivative.
  exact Auxiliary.hasFDerivAt_of_weakGrad q Φ hq hΦ hgrad

end

end Work.FTS.PressureOn
