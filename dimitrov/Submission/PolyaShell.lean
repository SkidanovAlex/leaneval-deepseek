import Mathlib
import Submission.PolyaCore
import Submission.BranchX
import Submission.StarGeom

/-!
# E2: the Pólya/Hankel shell (conditional on the capacity hypothesis `HedgehogBound`)

This module develops the analytic shell that converts the *capacity
hypothesis* `Submission.PolyaCore.HedgehogBound (conjugateValues α)`
(monic-polynomial control of the `ε`-fattened hedgehog of branch points,
which is Dubinin's inequality — the deep input E1, not proved here) together
with the analytic data of `Submission.BranchX.exists_laurent_branch`
(holomorphic `g` off the hedgehog with integer Laurent data `Σ (a k) X⁻ᵏ` at
infinity) into the eventual vanishing of the integer Hankel determinants

    hankelDet a k = 0     for all large k,

which is exactly `Submission.EngineAlg.HankelInput α hα` (the input of the
verified algebraic tail `no_hankelInput` that completes the engine).

## The shape of the argument (Pólya's estimate)

1. (E0, verified in PolyaCore)  `hankelDet a k = det (momentMatrix k a p)`
   for any monic `p : Fin k → ℂ[X]` of degrees `0..k−1`.
2. (E2a, this module)  For `ρ > R` and every `m`, the Laurent coefficient is
   the circle moment
   `a (m+1) = (2πi)⁻¹ · ∮_{|X|=ρ} g(X) X^m dX`
   (partial sums converge uniformly on the circle — proved here from the
   analyticity of the Taylor data; the finite-sum case is proved below).
   Hence by linearity, for any polynomials `pᵢ, pⱼ`:
   `momentPair a pᵢ pⱼ = (2πi)⁻¹ ∮_{|X|=ρ} g(X) pᵢ(X) pⱼ(X) X⁻¹ dX`.
3. (E2b)  Cauchy deformation: `g` is holomorphic off the hedgehog `star S`,
   and `pᵢ pⱼ X⁻¹` is holomorphic off `{0} ⊂ star S`, so the circle at
   radius `ρ` can be deformed to the boundary `∂(FatStar S ε)` of the
   `ε`-fattened hedgehog (rectangle/grid Cauchy theorem), where the
   polynomials are small by `HedgehogBound`.
4. (E2c)  Entry bounds + `Matrix.det_le` + integrality ⟹ `hankelDet a k = 0`
   eventually.

VERIFIED in this module (E2a + E2a-2, zero sorries): the circle-moment
layer is complete.  The monomial moments (`= 0` off `k = m+1`, `= 2πi` at the
critical index), the finite-truncation moments
`∮ z^m·Σ_{k≤N}(a k)z⁻ᵏ = 2πi·a(m+1)` for every `N ≥ m+1`, and — passing to
the limit — the Laurent moment `∮ z^m·g = 2πi·a(m+1)` (E2a).  The
uniform-convergence hypothesis of the last step is DISCHARGED (E2a-2) from
the analyticity data: the diagonal coefficients of the Cauchy power series
equal `w^k·taylorCoeff f k` (`cauchyPowerSeries_diag_eq_taylorCoeff`), the
Taylor partial sums of an analytic `f` converge uniformly on circles strictly
inside its ball (`taylorSums_tendstoUniformlyOn_sphere`), the transfer
`w = X⁻¹` and multiplication by `z^m` preserve uniform convergence, and the
final statement `circleIntegral_moment_laurent` derives the circle moment of
`g X = f (X⁻¹)` purely from `f`'s differentiability on `ball 0 ρ₀`
(`ρ⁻¹ < ρ₀`) and its Taylor coefficients.

Still to be proved (future sessions): (E2b) the Cauchy deformation of the
circle `|X| = ρ` to the boundary of the fattened hedgehog `FatStar S ε`
through `ℂ ∖ star S` (rectangle/grid Cauchy theorem); (E2c) the entry bounds
with `HedgehogBound` + `Matrix.det_le` + integrality, giving
`hankelDet a k = 0` eventually; these assemble `hankel_eventually_zero_of_
hedgehog : HedgehogBound S → hankel_eventually_zero`.  This module is NOT
imported by the engine yet.
-/

noncomputable section

open scoped Polynomial Real Topology Complex ENNReal NNReal Interval
open Filter

open Polynomial
open Submission.Kronecker
open Submission.PolyaCore

namespace Submission.PolyaShell

/-! ## E2a: circle moments of the Laurent data -/

/-- For `z ≠ 0`, `z^m · (z⁻¹)^k = z^(m−k)` (integer powers). -/
lemma zpow_sub_of_mul_inv_pow {z : ℂ} (hz : z ≠ 0) (m k : ℕ) :
    z ^ ((m : ℤ) - (k : ℤ)) = z ^ m * (z⁻¹) ^ k := by
  calc
    z ^ ((m : ℤ) - (k : ℤ)) = z ^ (m : ℤ) * (z ^ (k : ℤ))⁻¹ := by
      rw [zpow_sub₀ hz, div_eq_mul_inv]
    _ = z ^ m * (z ^ k)⁻¹ := by
      simp [zpow_natCast]
    _ = z ^ m * (z⁻¹) ^ k := by rw [inv_pow]

/-- A point on the circle `sphere 0 ρ` with `0 < ρ` is nonzero. -/
lemma ne_zero_of_mem_sphere_zero {ρ : ℝ} (hρ : 0 < ρ) {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) ρ) :
    z ≠ 0 := by
  intro hz0
  have hnorm : ‖z‖ = ρ := (mem_sphere_zero_iff_norm.mp hz)
  rw [hz0, norm_zero] at hnorm
  linarith

/-- For `k ≠ m + 1`: `∮ z^m (z⁻¹)^k = 0` on the circle of radius `ρ > 0`. -/
lemma circleIntegral_mul_inv_pow_zero {ρ : ℝ} (hρ : 0 < ρ) {m k : ℕ} (hk : k ≠ m + 1) :
    (∮ z in C((0 : ℂ), ρ), z ^ m * (z⁻¹) ^ k) = 0 := by
  have hn : (m : ℤ) - (k : ℤ) ≠ (-1 : ℤ) := by
    intro h
    have hz1 : (k : ℤ) = (m : ℤ) + 1 := by omega
    apply hk
    exact_mod_cast hz1
  have hEq : Set.EqOn (fun z : ℂ => z ^ m * (z⁻¹) ^ k)
      (fun z : ℂ => (z - 0) ^ ((m : ℤ) - (k : ℤ))) (Metric.sphere (0 : ℂ) ρ) := by
    intro z hz_sphere
    change z ^ m * (z⁻¹) ^ k = (z - 0) ^ ((m : ℤ) - (k : ℤ))
    simpa [sub_zero] using (zpow_sub_of_mul_inv_pow (ne_zero_of_mem_sphere_zero hρ hz_sphere) m k).symm
  calc
    (∮ z in C((0 : ℂ), ρ), z ^ m * (z⁻¹) ^ k)
        = ∮ z in C((0 : ℂ), ρ), (z - 0) ^ ((m : ℤ) - (k : ℤ)) :=
          circleIntegral.integral_congr hρ.le hEq
    _ = 0 := circleIntegral.integral_sub_zpow_of_ne hn (0 : ℂ) (0 : ℂ) ρ

/-- The critical monomial moment: `∮ z^m (z⁻¹)^(m+1) = 2πi`. -/
lemma circleIntegral_mul_inv_pow_crit {ρ : ℝ} (hρ : 0 < ρ) (m : ℕ) :
    (∮ z in C((0 : ℂ), ρ), z ^ m * (z⁻¹) ^ (m + 1)) = 2 * π * Complex.I := by
  have hEq : Set.EqOn (fun z : ℂ => z ^ m * (z⁻¹) ^ (m + 1))
      (fun z : ℂ => (z - 0) ^ (-1 : ℤ)) (Metric.sphere (0 : ℂ) ρ) := by
    intro z hz_sphere
    have hpow : (m : ℤ) - (((m + 1 : ℕ) : ℤ)) = (-1 : ℤ) := by omega
    change z ^ m * (z⁻¹) ^ (m + 1) = (z - 0) ^ (-1 : ℤ)
    simpa [hpow, sub_zero] using
      (zpow_sub_of_mul_inv_pow (ne_zero_of_mem_sphere_zero hρ hz_sphere) m (m + 1)).symm
  calc
    (∮ z in C((0 : ℂ), ρ), z ^ m * (z⁻¹) ^ (m + 1))
        = ∮ z in C((0 : ℂ), ρ), (z - 0) ^ (-1 : ℤ) :=
          circleIntegral.integral_congr hρ.le hEq
    _ = 2 * π * Complex.I := by
      simpa using (circleIntegral.integral_sub_inv_of_mem_ball (c := (0 : ℂ)) (w := (0 : ℂ))
        (R := ρ) (by simpa using hρ))

/-- **E2a (finite sums).**  The circle moment of the truncated Laurent data
`S_{m+1}(z) := Σ_{k=0}^{m+1} (a k) z⁻ᵏ`: `∮ z^m · S_{m+1}(z) = 2πi · a (m+1)`. -/
lemma term_continuous (a : ℕ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (m k : ℕ) :
    ContinuousOn (fun z : ℂ => (a k) * (z ^ m * (z⁻¹) ^ k)) (Metric.sphere (0 : ℂ) ρ) := by
  have hcont_id : ContinuousOn (fun z : ℂ => z) (Metric.sphere (0 : ℂ) ρ) := continuousOn_id
  have hcont_inv : ContinuousOn (fun z : ℂ => z⁻¹) (Metric.sphere (0 : ℂ) ρ) :=
    hcont_id.inv₀ (fun z hz => ne_zero_of_mem_sphere_zero hρ hz)
  exact (continuousOn_const.mul ((hcont_id.pow m).mul (hcont_inv.pow k)))

theorem circleIntegral_moment_fin (a : ℕ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (m : ℕ) :
    (∮ z in C((0 : ℂ), ρ),
        z ^ m * (∑ k ∈ Finset.range (m + 2), (a k) * (z⁻¹) ^ k)) =
      2 * π * Complex.I * a (m + 1) := by
  classical
  have hdist : (fun z : ℂ => z ^ m * (∑ k ∈ Finset.range (m + 2), (a k) * (z⁻¹) ^ k))
      = fun z : ℂ => ∑ k ∈ Finset.range (m + 2), (a k) * (z ^ m * (z⁻¹) ^ k) := by
    funext z
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hdist]
  have hsum : (∮ z in C((0 : ℂ), ρ), ∑ k ∈ Finset.range (m + 2), (a k) * (z ^ m * (z⁻¹) ^ k))
      = ∑ k ∈ Finset.range (m + 2),
          ∮ z in C((0 : ℂ), ρ), (a k) * (z ^ m * (z⁻¹) ^ k) := by
    exact circleIntegral.integral_fun_sum (s := Finset.range (m + 2))
      (f := fun (k : ℕ) (z : ℂ) => (a k) * (z ^ m * (z⁻¹) ^ k)) (c := (0 : ℂ)) (R := ρ)
        (by intro k hk; exact (ContinuousOn.circleIntegrable hρ.le (term_continuous a hρ m k)))
  rw [hsum]
  have hsingle : (∑ k ∈ Finset.range (m + 2),
        (∮ z in C((0 : ℂ), ρ), (a k) * (z ^ m * (z⁻¹) ^ k))) =
      (∮ z in C((0 : ℂ), ρ), (a (m + 1)) * (z ^ m * (z⁻¹) ^ (m + 1))) := by
    apply Finset.sum_eq_single (m + 1)
    · intro k hk hkne
      rw [circleIntegral.integral_const_mul]
      rw [circleIntegral_mul_inv_pow_zero hρ hkne]
      ring
    · intro hknot
      exfalso
      exact hknot (Finset.mem_range.mpr (by omega))
  rw [hsingle]
  rw [circleIntegral.integral_const_mul]
  rw [circleIntegral_mul_inv_pow_crit hρ m]
  ring


/-- **E2a (finite sums, general level).**  The circle moment of the truncated
Laurent data `S_N(z) := Σ_{k=0}^{N} (a k) z⁻ᵏ` with `m + 1 ≤ N`:
`∮ z^m · S_N(z) = 2πi · a (m+1)` — independent of `N`. -/
theorem circleIntegral_moment_fin_general (a : ℕ → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (m N : ℕ) (hN : m + 1 ≤ N) :
    (∮ z in C((0 : ℂ), ρ),
        z ^ m * (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k)) =
      2 * π * Complex.I * a (m + 1) := by
  classical
  have hdist : (fun z : ℂ => z ^ m * (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k))
      = fun z : ℂ => ∑ k ∈ Finset.range (N + 1), (a k) * (z ^ m * (z⁻¹) ^ k) := by
    funext z
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hdist]
  have hsum : (∮ z in C((0 : ℂ), ρ), ∑ k ∈ Finset.range (N + 1), (a k) * (z ^ m * (z⁻¹) ^ k))
      = ∑ k ∈ Finset.range (N + 1),
          ∮ z in C((0 : ℂ), ρ), (a k) * (z ^ m * (z⁻¹) ^ k) := by
    exact circleIntegral.integral_fun_sum (s := Finset.range (N + 1))
      (f := fun (k : ℕ) (z : ℂ) => (a k) * (z ^ m * (z⁻¹) ^ k)) (c := (0 : ℂ)) (R := ρ)
        (by intro k hk; exact (ContinuousOn.circleIntegrable hρ.le (term_continuous a hρ m k)))
  rw [hsum]
  have hsingle : (∑ k ∈ Finset.range (N + 1),
        (∮ z in C((0 : ℂ), ρ), (a k) * (z ^ m * (z⁻¹) ^ k))) =
      (∮ z in C((0 : ℂ), ρ), (a (m + 1)) * (z ^ m * (z⁻¹) ^ (m + 1))) := by
    apply Finset.sum_eq_single (m + 1)
    · intro k hk hkne
      rw [circleIntegral.integral_const_mul]
      rw [circleIntegral_mul_inv_pow_zero hρ hkne]
      ring
    · intro hknot
      exfalso
      exact hknot (Finset.mem_range.mpr (by omega))
  rw [hsingle]
  rw [circleIntegral.integral_const_mul]
  rw [circleIntegral_mul_inv_pow_crit hρ m]
  ring


/-- **E2a (Laurent moment, given uniform convergence).**  If the truncated
Laurent sums `S_N(z) = Σ_{k=0}^{N} (a k) z⁻ᵏ` times `z^m` converge uniformly on
the circle `|z| = ρ` to `z^m · g z`, then the circle moment of `g` is the
Laurent coefficient: `∮ z^m · g z = 2πi · a (m+1)`. -/
lemma circleIntegral_moment_of_uniform {a : ℕ → ℂ} {g : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (m : ℕ)
    (hcont : ∀ᶠ N in atTop, ContinuousOn
        (fun z : ℂ => z ^ m * (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k))
        (Metric.sphere (0 : ℂ) ρ))
    (huni : TendstoUniformlyOn
        (fun (N : ℕ) (z : ℂ) => z ^ m * (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k))
        (fun z : ℂ => z ^ m * g z) atTop (Metric.sphere (0 : ℂ) ρ)) :
    (∮ z in C((0 : ℂ), ρ), z ^ m * g z) = 2 * π * Complex.I * a (m + 1) := by
  classical
  have hT : Tendsto (fun N : ℕ =>
        (∮ z in C((0 : ℂ), ρ), z ^ m * (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k)))
      atTop (𝓝 (∮ z in C((0 : ℂ), ρ), z ^ m * g z)) := by
    simpa using (TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn
      (f := fun (N : ℕ) (z : ℂ) => z ^ m * (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k))
      (g := fun z : ℂ => z ^ m * g z) (c := (0 : ℂ)) (R := ρ) hρ.le hcont huni)
  have hconst : (fun N : ℕ =>
        (∮ z in C((0 : ℂ), ρ), z ^ m * (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k)))
      =ᶠ[atTop] fun _ : ℕ => 2 * π * Complex.I * a (m + 1) := by
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨m + 1, ?_⟩
    intro N hN
    exact circleIntegral_moment_fin_general a hρ m N hN
  have hT2 : Tendsto (fun _ : ℕ => 2 * π * Complex.I * a (m + 1))
      atTop (𝓝 (∮ z in C((0 : ℂ), ρ), z ^ m * g z)) := hT.congr' hconst
  have hT3 : Tendsto (fun _ : ℕ => 2 * π * Complex.I * a (m + 1))
      atTop (𝓝 (2 * π * Complex.I * a (m + 1))) := tendsto_const_nhds
  exact tendsto_nhds_unique hT2 hT3


open Submission.SqrtTaylor

lemma cauchyPowerSeries_diag_eq_taylorCoeff (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hd : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) R)) (k : ℕ) (w : ℂ) :
    cauchyPowerSeries f (0 : ℂ) R k (fun _ : Fin k => w) = taylorCoeff f k * w ^ k := by
  classical
  rw [cauchyPowerSeries_apply]
  have hEq : Set.EqOn
      (fun z : ℂ => (w / (z - 0)) ^ k • (z - 0)⁻¹ • f z)
      (fun z : ℂ => w ^ k • ((1 / (z - 0) ^ (k + 1)) • f z))
      (Metric.sphere (0 : ℂ) R) := by
    intro z hz
    have hzne : z ≠ 0 := by
      have hnorm : ‖z‖ = R := (mem_sphere_zero_iff_norm.mp hz)
      intro hz0
      rw [hz0, norm_zero] at hnorm
      linarith
    have hz0 : (z - 0 : ℂ) = z := by simp
    simp only [smul_eq_mul]
    rw [hz0]
    field_simp [hzne]
    rw [div_pow]
    field_simp [hzne, pow_ne_zero k hzne]
    ring
  have hInt : (∮ z in C((0 : ℂ), R), (w / (z - 0)) ^ k • (z - 0)⁻¹ • f z)
      = (∮ z in C((0 : ℂ), R), w ^ k • ((1 / (z - 0) ^ (k + 1)) • f z)) := by
    exact circleIntegral.integral_congr hR.le hEq
  rw [hInt]
  simp only [circleIntegral.integral_smul]
  rw [DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul hR k hd]
  rw [taylorCoeff]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_assoc]
  field_simp [Complex.two_pi_I_ne_zero,
    (by exact_mod_cast (Nat.factorial_ne_zero k) : ((k.factorial : ℕ) : ℂ) ≠ 0)]

/-- Cauchy partial sums equal the Taylor partial sums. -/
lemma cauchyPartialSum_eq_taylor (f : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hd : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) R)) (n : ℕ) (w : ℂ) :
    (cauchyPowerSeries f (0 : ℂ) R).partialSum n w =
      ∑ k ∈ Finset.range n, taylorCoeff f k * w ^ k := by
  classical
  simp [FormalMultilinearSeries.partialSum, cauchyPowerSeries_diag_eq_taylorCoeff f R hR hd]

/-- shift invariance for uniform convergence on `ℕ`. -/
lemma tendstoUniformlyOn_shift_add (u : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (s : Set ℂ) (c : ℕ)
    (h : TendstoUniformlyOn u f atTop s) :
    TendstoUniformlyOn (fun n y => u (n + c) y) f atTop s := by
  unfold TendstoUniformlyOn at h ⊢
  intro U hU
  have hP : ∀ᶠ n in atTop, ∀ x ∈ s, (f x, u n x) ∈ U := h U hU
  rw [Filter.eventually_atTop] at hP
  rcases hP with ⟨N, hN⟩
  rw [Filter.eventually_atTop]
  refine ⟨N, ?_⟩
  intro n hn y hy
  exact hN (n + c) (by omega) y hy

/-- Taylor partial sums of an analytic function converge uniformly on a circle
strictly inside the ball of analyticity. -/
lemma taylorSums_tendstoUniformlyOn_sphere (f : ℂ → ℂ) {ρ₀ r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) ρ₀)) (hr0 : 0 ≤ r) (hrρ : r < ρ₀) :
    TendstoUniformlyOn
      (fun (N : ℕ) (w : ℂ) => ∑ k ∈ Finset.range (N + 1), taylorCoeff f k * w ^ k)
      f atTop (Metric.sphere (0 : ℂ) r) := by
  classical
  rcases exists_between hrρ with ⟨Rr, hrR, hRρ⟩
  have hRpos : 0 < Rr := by linarith
  have hRge : 0 ≤ Rr := le_of_lt hRpos
  have hclosed : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) Rr) :=
    hf.mono (Metric.closedBall_subset_ball hRρ)
  let Rnn : ℝ≥0 := ⟨Rr, hRge⟩
  have hF : HasFPowerSeriesOnBall f (cauchyPowerSeries f (0 : ℂ) Rnn) (0 : ℂ) Rnn := by
    exact DifferentiableOn.hasFPowerSeriesOnBall (c := (0 : ℂ)) hclosed hRpos
  rcases exists_between hrR with ⟨Rr', hrR', hR'R⟩
  have hR'ge : 0 ≤ Rr' := by linarith
  let r' : ℝ≥0 := ⟨Rr', hR'ge⟩
  have hU : TendstoUniformlyOn
      (fun (n : ℕ) (y : ℂ) => (cauchyPowerSeries f (0 : ℂ) Rnn).partialSum n (y - 0)) f atTop
      (Metric.ball (0 : ℂ) Rr') := by
    exact hF.tendstoUniformlyOn' (show (r' : ℝ≥0∞) < (Rnn : ℝ≥0∞) from ENNReal.coe_lt_coe.mpr hR'R)
  have hsphere : Metric.sphere (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) Rr' := by
    intro w hw
    have hnorm : ‖w‖ = r := (mem_sphere_zero_iff_norm.mp hw)
    exact (Metric.mem_ball).mpr (by rw [dist_eq_norm, sub_zero]; linarith)
  have hUs : TendstoUniformlyOn
      (fun (n : ℕ) (y : ℂ) => (cauchyPowerSeries f (0 : ℂ) Rnn).partialSum n (y - 0)) f atTop
      (Metric.sphere (0 : ℂ) r) := hU.mono hsphere
  have hId : ∀ n : ℕ, Set.EqOn
      (fun y : ℂ => (cauchyPowerSeries f (0 : ℂ) Rnn).partialSum n (y - 0))
      (fun y : ℂ => ∑ k ∈ Finset.range n, taylorCoeff f k * y ^ k)
      (Metric.sphere (0 : ℂ) r) := by
    intro n y hy
    change (cauchyPowerSeries f (0 : ℂ) (Rnn : ℝ)).partialSum n (y - 0) =
      ∑ k ∈ Finset.range n, taylorCoeff f k * y ^ k
    rw [sub_zero]
    exact cauchyPartialSum_eq_taylor f Rr hRpos hclosed n y
  have hUt : TendstoUniformlyOn
      (fun (n : ℕ) (w : ℂ) => ∑ k ∈ Finset.range n, taylorCoeff f k * w ^ k)
      f atTop (Metric.sphere (0 : ℂ) r) := by
    refine hUs.congr ?_
    filter_upwards with n
    exact hId n
  simpa using (tendstoUniformlyOn_shift_add
    (fun (n : ℕ) (w : ℂ) => ∑ k ∈ Finset.range n, taylorCoeff f k * w ^ k) f
    (Metric.sphere (0 : ℂ) r) 1 hUt)


/-- Multiplying by `z^m` preserves uniform convergence on the circle `|z| = ρ`. -/
lemma mul_pow_tendstoUniformlyOn_sphere {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (m : ℕ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hF : TendstoUniformlyOn F f atTop (Metric.sphere (0 : ℂ) ρ)) :
    TendstoUniformlyOn (fun n z => z ^ m * F n z) (fun z => z ^ m * f z) atTop
      (Metric.sphere (0 : ℂ) ρ) := by
  rw [Metric.tendstoUniformlyOn_iff] at hF ⊢
  intro ε hε
  have hF' : ∀ᶠ n in atTop, ∀ x ∈ Metric.sphere (0 : ℂ) ρ,
      dist (f x) (F n x) < ε / (2 * (ρ ^ m + 1)) := hF (ε / (2 * (ρ ^ m + 1))) (by positivity)
  filter_upwards [hF'] with n hn z hz
  have hnorm : ‖z‖ = ρ := (mem_sphere_zero_iff_norm.mp hz)
  have hden : 0 < ρ ^ m + 1 := by positivity
  have hdiv : ρ ^ m / (ρ ^ m + 1) ≤ 1 := by
    rw [div_le_iff₀ hden]
    linarith
  calc
    dist (z ^ m * f z) (z ^ m * F n z) = ‖z ^ m * f z - z ^ m * F n z‖ := by rw [dist_eq_norm]
    _ = ‖z ^ m * (f z - F n z)‖ := by congr 1; ring
    _ = ‖z ^ m‖ * ‖f z - F n z‖ := norm_mul _ _
    _ = ‖z ^ m‖ * dist (f z) (F n z) := by rw [dist_eq_norm]
    _ ≤ ρ ^ m * (ε / (2 * (ρ ^ m + 1))) := by
      exact mul_le_mul (by rw [norm_pow, hnorm]) (le_of_lt (hn z hz)) dist_nonneg
        (pow_nonneg hρ m)
    _ ≤ ε / 2 := by
      calc
        ρ ^ m * (ε / (2 * (ρ ^ m + 1))) = (ε / 2) * (ρ ^ m / (ρ ^ m + 1)) := by
          field_simp [hden.ne', (by norm_num : (2 : ℝ) ≠ 0)]
        _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hdiv (by positivity)
        _ = ε / 2 := by ring
    _ < ε := by linarith



/-- X-side uniform convergence of the Laurent partial sums `Σ (a k) (X⁻¹)ᵏ`
on the circle `|X| = ρ` (i.e. `|w| = ρ⁻¹` in the w-plane), from the analyticity
of `f` on `ball 0 ρ₀` (`ρ⁻¹ < ρ₀`) and `g X = f (X⁻¹)`. -/
lemma laurentSums_tendstoUniformlyOn_sphere {a : ℕ → ℂ} {f g : ℂ → ℂ} {ρ₀ : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) ρ₀))
    (ha : ∀ k : ℕ, Submission.SqrtTaylor.taylorCoeff f k = a k)
    (hg : ∀ X : ℂ, X ≠ 0 → g X = f (X⁻¹)) {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ρ⁻¹ < ρ₀) :
    TendstoUniformlyOn
      (fun (N : ℕ) (X : ℂ) => ∑ k ∈ Finset.range (N + 1), (a k) * (X⁻¹) ^ k)
      g atTop (Metric.sphere (0 : ℂ) ρ) := by
  -- w-side: uniform convergence on the circle |w| = ρ⁻¹ of Σ taylorCoeff·w^k → f
  have hW : TendstoUniformlyOn
      (fun (N : ℕ) (w : ℂ) => ∑ k ∈ Finset.range (N + 1),
          Submission.SqrtTaylor.taylorCoeff f k * w ^ k)
      f atTop (Metric.sphere (0 : ℂ) ρ⁻¹) := by
    exact taylorSums_tendstoUniformlyOn_sphere f hf (inv_nonneg.mpr hρpos.le) hρ
  have hWa : TendstoUniformlyOn
      (fun (N : ℕ) (w : ℂ) => ∑ k ∈ Finset.range (N + 1), (a k) * w ^ k)
      f atTop (Metric.sphere (0 : ℂ) ρ⁻¹) := by
    refine hW.congr ?_
    filter_upwards with N
    intro w hw
    apply Finset.sum_congr rfl
    intro k hk
    rw [ha k]
  rw [Metric.tendstoUniformlyOn_iff] at hWa ⊢
  intro ε hε
  have hWa' : ∀ᶠ N in atTop, ∀ w ∈ Metric.sphere (0 : ℂ) ρ⁻¹,
      dist (f w) (∑ k ∈ Finset.range (N + 1), (a k) * w ^ k) < ε := hWa ε hε
  filter_upwards [hWa'] with N hN X hX
  have hXne : X ≠ 0 := ne_zero_of_mem_sphere_zero hρpos hX
  have hXinv : X⁻¹ ∈ Metric.sphere (0 : ℂ) ρ⁻¹ := by
    rw [mem_sphere_zero_iff_norm]
    rw [norm_inv]
    have hnorm : ‖X‖ = ρ := (mem_sphere_zero_iff_norm.mp hX)
    rw [hnorm]
  calc
    dist (g X) (∑ k ∈ Finset.range (N + 1), (a k) * (X⁻¹) ^ k)
        = dist (f (X⁻¹)) (∑ k ∈ Finset.range (N + 1), (a k) * (X⁻¹) ^ k) := by
            rw [hg X hXne]
    _ < ε := hN (X⁻¹) hXinv




/-- **E2a-2 discharge.**  Given the analyticity data (f differentiable on
`ball 0 ρ₀` with Taylor coefficients `a`, and `g X = f (X⁻¹)`), the circle
moment of `g` on `|X| = ρ` (`ρ⁻¹ < ρ₀`) is the Laurent coefficient:
`∮ z^m · g z = 2πi · a (m+1)`. -/
lemma circleIntegral_moment_laurent {a : ℕ → ℂ} {f g : ℂ → ℂ} {ρ₀ : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) ρ₀))
    (ha : ∀ k : ℕ, Submission.SqrtTaylor.taylorCoeff f k = a k)
    (hg : ∀ X : ℂ, X ≠ 0 → g X = f (X⁻¹)) {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ρ⁻¹ < ρ₀) (m : ℕ) :
    (∮ z in C((0 : ℂ), ρ), z ^ m * g z) = 2 * π * Complex.I * a (m + 1) := by
  have hU : TendstoUniformlyOn
      (fun (N : ℕ) (z : ℂ) => z ^ m * (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k))
      (fun z : ℂ => z ^ m * g z) atTop (Metric.sphere (0 : ℂ) ρ) :=
    mul_pow_tendstoUniformlyOn_sphere m hρpos.le
      (laurentSums_tendstoUniformlyOn_sphere (a := a) (f := f) (g := g) hf ha hg hρpos hρ)
  have hcont : ∀ᶠ N in atTop, ContinuousOn
      (fun z : ℂ => z ^ m * (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k))
      (Metric.sphere (0 : ℂ) ρ) := by
    filter_upwards with N
    have hterm : ∀ k ∈ Finset.range (N + 1),
        ContinuousOn (fun z : ℂ => (a k) * (z ^ m * (z⁻¹) ^ k)) (Metric.sphere (0 : ℂ) ρ) := by
      intro k hk
      exact term_continuous a hρpos m k
    have hsumcont : ContinuousOn
        (fun z : ℂ => ∑ k ∈ Finset.range (N + 1), (a k) * (z ^ m * (z⁻¹) ^ k))
        (Metric.sphere (0 : ℂ) ρ) := continuousOn_finsetSum (Finset.range (N + 1)) hterm
    have hEq : (fun z : ℂ => z ^ m * (∑ k ∈ Finset.range (N + 1), (a k) * (z⁻¹) ^ k))
        = fun z : ℂ => ∑ k ∈ Finset.range (N + 1), (a k) * (z ^ m * (z⁻¹) ^ k) := by
      funext z
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hEq]
    exact hsumcont
  exact circleIntegral_moment_of_uniform hρpos m hcont hU




/-! ## E2b foundation: the integrand and per-cell Cauchy facts

The Pólya/Hankel shell must express the moment pairings
`momentPair a pᵢ pⱼ = (2πi)⁻¹ ∮_{|X|=ρ} g(X) pᵢ(X) pⱼ(X) X⁻¹ dX` (from E2a)
as integrals over a contour that hugs the hedgehog `star S` within the
distance where `HedgehogBound` controls the polynomials, by the Cauchy
theorem (deformation through `ℂ ∖ star S`, where `g` is holomorphic).

This section records the *per-cell* facts that the deformation is built from:
the integrand `X ↦ g X · (p.eval X) · (q.eval X) · X⁻¹` is holomorphic on
`(star S)ᶜ`, so on any rectangle whose closed interior avoids the hedgehog
the rectangle-boundary integral (Mathlib's Cauchy-Goursat) vanishes; and the
big circle `|X| = ρ` lies in `(star S)ᶜ` once it encloses the hedgehog.
-/

/-- The integrand `g·p·q·X⁻¹` is holomorphic off the hedgehog: `g` is
holomorphic off the hedgehog (`BranchX`), polynomial evaluations are entire,
and `X⁻¹` is holomorphic off `0 ∈ star S`. -/
lemma integrand_differentiableOn_star_compl {S : Finset ℂ} (hSne : S.Nonempty)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (Submission.XTransfer.star S)ᶜ)
    (p q : ℂ[X]) :
    DifferentiableOn ℂ (fun X : ℂ => g X * (p.eval X) * (q.eval X) * (X⁻¹))
      (Submission.XTransfer.star S)ᶜ := by
  have h0 : (0 : ℂ) ∈ Submission.XTransfer.star S := Submission.XTransfer.zero_mem_star hSne
  have hsub : (Submission.XTransfer.star S)ᶜ ⊆ {x : ℂ | x ≠ 0} := by
    intro x hx hx0
    exact hx (by simpa [hx0] using h0)
  have hg1 : DifferentiableOn ℂ (fun X : ℂ => g X * p.eval X)
      (Submission.XTransfer.star S)ᶜ :=
    hg.mul (p.differentiable.differentiableOn.mono (Set.subset_univ _))
  have hq : DifferentiableOn ℂ (fun X : ℂ => q.eval X)
      (Submission.XTransfer.star S)ᶜ :=
    q.differentiable.differentiableOn.mono (Set.subset_univ _)
  have hi : DifferentiableOn ℂ (fun X : ℂ => X⁻¹)
      (Submission.XTransfer.star S)ᶜ :=
    (differentiableOn_inv : DifferentiableOn ℂ (fun X : ℂ => X⁻¹) {x : ℂ | x ≠ 0}).mono hsub
  exact ((hg1.mul hq).mul hi)

/-- **Per-cell Cauchy fact.**  The boundary integral of a function `h` that is
holomorphic off the hedgehog vanishes on every rectangle whose closed interior
avoids the hedgehog (so `h` is holomorphic on the whole closed rectangle). -/
lemma rect_boundary_integral_eq_zero_of_star_compl {S : Finset ℂ}
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (z w : ℂ) (hR : ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) ⊆ (Submission.XTransfer.star S)ᶜ) :
    (∫ x : ℝ in z.re..w.re, h (x + z.im * Complex.I)) -
        (∫ x : ℝ in z.re..w.re, h (x + w.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in z.im..w.im, h (Complex.re w + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in z.im..w.im, h (Complex.re z + y * Complex.I)) = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_differentiableOn h z w (hh.mono hR)

/-- The circle `|X| = ρ` avoids the hedgehog as soon as it encloses it. -/
lemma sphere_subset_star_compl {S : Finset ℂ} {ρ : ℝ}
    (hρ : ∀ X ∈ Submission.XTransfer.star S, ‖X‖ < ρ) :
    Metric.sphere (0 : ℂ) ρ ⊆ (Submission.XTransfer.star S)ᶜ := by
  intro X hX hXs
  have hnorm : ‖X‖ = ρ := (mem_sphere_zero_iff_norm.mp hX)
  have hle : ‖X‖ < ρ := hρ X hXs
  rw [hnorm] at hle
  linarith


/-- The pulled-back integrand `w ↦ h (exp w) * exp w` is complex
differentiable on a w-rectangle whose exp-image avoids the hedgehog. -/
lemma pulledBack_differentiableOn_rect {S : Finset ℂ} {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ) (a b c d : ℝ)
    (hR : ∀ w ∈ ([[a, b]] ×ℂ [[c, d]]), Complex.exp w ∈ (Submission.XTransfer.star S)ᶜ) :
    DifferentiableOn ℂ (fun w : ℂ => h (Complex.exp w) * Complex.exp w)
      ([[a, b]] ×ℂ [[c, d]]) := by
  have hopen : IsOpen (Submission.XTransfer.star S)ᶜ :=
    Submission.XTransfer.isClosed_star S |>.isOpen_compl
  intro w hw
  have hw' : Complex.exp w ∈ (Submission.XTransfer.star S)ᶜ := hR w hw
  have hh_at : DifferentiableAt ℂ h (Complex.exp w) :=
    hh.differentiableAt (hopen.mem_nhds hw')
  have he : DifferentiableAt ℂ (fun z : ℂ => h (Complex.exp z)) w :=
    hh_at.comp w Complex.differentiableAt_exp
  have he' : DifferentiableAt ℂ Complex.exp w := Complex.differentiableAt_exp
  exact (he.mul he').differentiableWithinAt

/-- **Sector (exp-pullback) Cauchy.**  If `h` is holomorphic off the hedgehog
and the exp-image of the w-rectangle avoids it, then the boundary integral of
the pulled-back 1-form `h(exp w)·exp w·dw` over the rectangle vanishes. -/
lemma sector_cauchy_of_star_compl {S : Finset ℂ} {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ) (a b c d : ℝ)
    (hR : ∀ w ∈ ([[a, b]] ×ℂ [[c, d]]), Complex.exp w ∈ (Submission.XTransfer.star S)ᶜ) :
    (∫ x : ℝ in a..b, h (Complex.exp (x + c * Complex.I)) * Complex.exp (x + c * Complex.I)) -
      (∫ x : ℝ in a..b, h (Complex.exp (x + d * Complex.I)) * Complex.exp (x + d * Complex.I)) +
      Complex.I • (∫ y : ℝ in c..d, h (Complex.exp (b + y * Complex.I)) * Complex.exp (b + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in c..d, h (Complex.exp (a + y * Complex.I)) * Complex.exp (a + y * Complex.I)) = 0 := by
  let F : ℂ → ℂ := fun w => h (Complex.exp w) * Complex.exp w
  have hF : DifferentiableOn ℂ F ([[a, b]] ×ℂ [[c, d]]) := by
    simpa [F] using (pulledBack_differentiableOn_rect (S := S) (h := h) hh a b c d hR)
  simpa [F] using
    (Complex.integral_boundary_rect_eq_zero_of_differentiableOn F (Complex.mk a c) (Complex.mk b d) hF)




/-- **Annular-sector cell Cauchy under a gap hypothesis.**  If `h` is
holomorphic off the hedgehog and no spike endpoint `z²`, `z⁴` (`z ∈ S`) points
into the closed angular range `[c, d] ⊆ (-π, π]`, then the boundary integral
of the pulled-back 1-form `h(exp w)·exp w` vanishes on every w-rectangle
`[[a,b]] ×ℂ [[c,d]]` — the per-cell identity of the E2b telescoping sum for
the angular gaps between consecutive spike directions. -/
lemma sector_cell_boundary_integral_eq_zero {S : Finset ℂ} (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (a b : ℝ) {c d : ℝ} (hc : c < d) (hcl : -π < c) (hdu : d ≤ π)
    (hno : ∀ z ∈ S,
      Complex.arg (z ^ 2) ∉ Set.Icc c d ∧ Complex.arg (z ^ 4) ∉ Set.Icc c d) :
    (∫ x : ℝ in a..b, h (Complex.exp (x + c * Complex.I)) * Complex.exp (x + c * Complex.I)) -
      (∫ x : ℝ in a..b, h (Complex.exp (x + d * Complex.I)) * Complex.exp (x + d * Complex.I)) +
      Complex.I • (∫ y : ℝ in c..d, h (Complex.exp (b + y * Complex.I)) * Complex.exp (b + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in c..d, h (Complex.exp (a + y * Complex.I)) * Complex.exp (a + y * Complex.I)) = 0 := by
  apply sector_cauchy_of_star_compl hh a b c d
  intro w hw
  have hne : Complex.exp w ∉ Submission.XTransfer.star S :=
    Submission.StarGeom.expRect_avoids_star (S := S) hS0 (xmin := a) (xmax := b)
      hc hcl hdu hno w hw
  simpa using hne


end Submission.PolyaShell

end
