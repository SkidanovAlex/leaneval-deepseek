import Mathlib
import Submission.Commons.NumberTheory.Linnik.partialFraction_eq
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound

open Complex DirichletCharacter Metric Filter
open scoped Real BigOperators Topology

set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-! # `completedLFunction_logDeriv_re_regular_bound`

The "regular" lower bound for the real part of the logarithmic derivative of a
completed Dirichlet L-function on the region `1 < σ ≤ 5/4`, `|τ| ≥ 1`:

    ∃ C > 0, ∀ σ τ, 1 < σ → σ ≤ 5/4 → 1 ≤ |τ| →
      Re (Λ′/Λ)(ψ, σ + iτ) ≥ -C·(log(M·(|τ|+2)) + 1).

**Reduction.**  If `ψ` is primitive and non-trivial, then `Λ = completedLFunction ψ`
is entire with `Λ(0) ≠ 0`, and all of its zeros lie in the critical strip
`0 < Re ρ < 1` (`zerosInStrip`).  The Hadamard partial-fraction expansion
(`Commons.NumberTheory.Linnik.partialFraction_eq`)

    Λ′(s)/Λ(s) - Λ′(0)/Λ(0) = lim_{R→∞} Σ_{|u| ≤ R} ord_Λ(u)·(1/(s-u) + 1/u)

then shows that on `Re s > 1` the real part of `Λ′/Λ(s)` is bounded below by the
*constant* `Re(Λ′/Λ(0)) ≥ -‖Λ′/Λ(0)‖`: every partial-fraction summand is nonnegative
for `Re s > 1`, since for a zero `ρ = β + iγ` with `0 < β < 1` we have

    Re(1/(s-ρ)) = (σ-β)/|s-ρ|² ≥ 0,     Re(1/ρ) = β/|ρ|² ≥ 0.

A constant lower bound is certainly compatible with the claimed bound
`-C·(log(M(|τ|+2)) + 1)`, which is at least `-C`.
-/

/-- Real part of a finite sum. -/
private lemma re_finset_sum {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ S, f i).re = ∑ i ∈ S, (f i).re := by
  classical
  refine Finset.induction_on S ?base ?step
  · simp
  · intro a A' ha ih
    rw [Finset.sum_insert ha, Complex.add_re, Finset.sum_insert ha, ih]

/-- For `Re z ≥ 0`, the real part of `1/z` is nonnegative. -/
private lemma one_div_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) : 0 ≤ (1 / z).re := by
  rw [one_div, Complex.inv_re]
  exact div_nonneg hz (Complex.normSq_nonneg z)

/-- **Nonnegativity of the partial-fraction sums on `Re s > 1`.**

For a primitive non-trivial character and `Re s > 1`, every summand of the divisor sum
`Σ_u ord_Λ(u)·(1/(s-u) + 1/u)` has nonnegative real part, because `ord_Λ(u) ≥ 0` and,
when `ord_Λ(u) ≠ 0`, the point `u` is a zero of `Λ` and hence satisfies
`0 < Re u < 1 < Re s`. -/
private lemma pf_sum_re_nonneg {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {s : ℂ} (hs : (1 : ℝ) < s.re) (R : ℝ) :
    0 ≤ ((∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u))).re := by
  classical
  let d : ℂ → ℤ := fun u => MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
      (Metric.closedBall 0 R) u
  have hAn : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) (Metric.closedBall 0 R) :=
    fun z _ => (differentiable_completedLFunction hχ).analyticAt z
  have hsupp : (Function.support d).Finite := by
    dsimp [d]
    exact MeromorphicOn.divisor_support_finite_of_subset
      (f := DirichletCharacter.completedLFunction χ)
      (U := Metric.closedBall 0 R) (V := Metric.closedBall 0 R)
      hAn.meromorphicOn (isCompact_closedBall (0 : ℂ) R) (fun z hz => hz)
  let S : Finset ℂ := hsupp.toFinset
  have hS_mem : ∀ u : ℂ, u ∈ S ↔ d u ≠ 0 := by
    intro u
    dsimp [S]
    rw [Set.Finite.mem_toFinset]
    rfl
  have hsub : Function.support (fun u : ℂ =>
      ((d u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)) ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    exact (hS_mem u).mpr (fun hd0 => hu (by simp [hd0]))
  rw [finsum_eq_sum_of_support_subset (fun u : ℂ =>
    ((d u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)) hsub]
  rw [re_finset_sum]
  apply Finset.sum_nonneg
  intro u huS
  have hdu : d u ≠ 0 := (hS_mem u).mp huS
  have hzu : DirichletCharacter.completedLFunction χ u = 0 :=
    Commons.Analysis.Complex.zero_of_divisor_ne_zero hAn (u := u) (by simpa [d] using hdu)
  have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hχprim hzu
  have hdnn : (0 : ℝ) ≤ ((d u : ℤ) : ℝ) := by
    simpa [d] using (Commons.Analysis.Complex.divisor_nonneg_on_closedBall hAn u)
  have hK : 0 ≤ (1 / (s - u) + 1 / u).re := by
    rw [Complex.add_re]
    refine add_nonneg (one_div_re_nonneg ?_) (one_div_re_nonneg ?_)
    · rw [Complex.sub_re]; linarith [hstrip.2]
    · linarith [hstrip.1]
  have hterm : 0 ≤ (((d u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)).re := by
    rw [Complex.mul_re]
    have hdre : (((d u : ℤ) : ℂ).re) = ((d u : ℤ) : ℝ) := by simp
    have hdim : (((d u : ℤ) : ℂ).im) = 0 := by simp
    rw [hdre, hdim, zero_mul, sub_zero]
    exact mul_nonneg hdnn hK
  exact hterm

/-- **Constant lower bound.**  For a primitive non-trivial character `χ mod M`, the real part
of the logarithmic derivative of the completed L-function `Λ = completedLFunction χ` is
bounded below by a constant on the half-plane `Re s > 1`.

This is the Hadamard partial-fraction argument: `Λ(0) ≠ 0`, all zeros of `Λ` lie in
`0 < Re ρ < 1`, and for `Re s > 1` each partial-fraction summand
`1/(s-ρ) + 1/ρ` has nonnegative real part. -/
lemma completedLFunction_logDeriv_re_lower {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, (1 : ℝ) < s.re →
      -C ≤ (logDeriv (DirichletCharacter.completedLFunction χ) s).re := by
  classical
  let B : ℂ := logDeriv (DirichletCharacter.completedLFunction χ) 0
  let C : ℝ := ‖B‖ + 1
  have hCpos : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hCpos, ?_⟩
  intro s hs
  -- `Λ s ≠ 0` since zeros lie in the strip `0 < Re < 1`.
  have hΛs : DirichletCharacter.completedLFunction χ s ≠ 0 := by
    intro hz
    have hstrip := Commons.NumberTheory.Linnik.completedL_zero_strip χ hχ hχprim hz
    linarith [hstrip.2]
  -- the Hadamard partial-fraction expansion at `s`
  have hpf := Commons.NumberTheory.Linnik.partialFraction_eq χ hχ hχprim s hΛs
  -- the divisor sums have nonnegative real part, hence so does their limit
  have hLlim : Tendsto (fun R : ℝ =>
      ((∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u))).re) atTop
      (𝓝 ((deriv (DirichletCharacter.completedLFunction χ) s /
        DirichletCharacter.completedLFunction χ s -
        deriv (DirichletCharacter.completedLFunction χ) 0 /
        DirichletCharacter.completedLFunction χ 0).re)) :=
    Complex.continuous_re.tendsto _ |>.comp hpf
  have hnn : 0 ≤ (deriv (DirichletCharacter.completedLFunction χ) s /
        DirichletCharacter.completedLFunction χ s -
        deriv (DirichletCharacter.completedLFunction χ) 0 /
        DirichletCharacter.completedLFunction χ 0).re := by
    have hmem := isClosed_Ici.mem_of_tendsto hLlim
      (Eventually.of_forall (fun R => pf_sum_re_nonneg χ hχ hχprim hs R))
    simpa using hmem
  -- the two real-part identities
  have hlog : (logDeriv (DirichletCharacter.completedLFunction χ) s).re =
      (deriv (DirichletCharacter.completedLFunction χ) s /
        DirichletCharacter.completedLFunction χ s).re := by
    rw [logDeriv_apply]
  have hB : -(‖B‖) ≤ (deriv (DirichletCharacter.completedLFunction χ) 0 /
        DirichletCharacter.completedLFunction χ 0).re := by
    have hBeq : B = deriv (DirichletCharacter.completedLFunction χ) 0 /
        DirichletCharacter.completedLFunction χ 0 := by
      simp only [B, logDeriv_apply]
    rw [← hBeq]
    linarith [Complex.abs_re_le_norm B, neg_abs_le B.re]
  rw [hlog]
  have hsub : (deriv (DirichletCharacter.completedLFunction χ) s /
        DirichletCharacter.completedLFunction χ s).re =
      (deriv (DirichletCharacter.completedLFunction χ) s /
        DirichletCharacter.completedLFunction χ s -
        deriv (DirichletCharacter.completedLFunction χ) 0 /
        DirichletCharacter.completedLFunction χ 0).re +
      (deriv (DirichletCharacter.completedLFunction χ) 0 /
        DirichletCharacter.completedLFunction χ 0).re := by
    rw [Complex.sub_re]
    ring
  rw [hsub]
  dsimp [C]
  linarith

theorem completedLFunction_logDeriv_re_regular_bound {M : ℕ} [NeZero M]
    (ψ : DirichletCharacter ℂ M) (hψ : ψ ≠ 1) (hψprim : ψ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ τ : ℝ, 1 < σ → σ ≤ 5 / 4 → 1 ≤ |τ| →
      (logDeriv (DirichletCharacter.completedLFunction ψ) ((σ : ℂ) + Complex.I * (τ : ℂ))).re ≥
      - C * (Real.log ((M : ℝ) * (|τ| + 2)) + 1) := by
  obtain ⟨C0, hC0pos, hcore⟩ := completedLFunction_logDeriv_re_lower ψ hψ hψprim
  refine ⟨max C0 1, lt_of_lt_of_le zero_lt_one (le_max_right C0 1), ?_⟩
  intro σ τ hσ1 _hσ2 hτ
  have hs : (1 : ℝ) < ((σ : ℂ) + Complex.I * (τ : ℂ)).re := by
    simpa using hσ1
  have hb := hcore ((σ : ℂ) + Complex.I * (τ : ℂ)) hs
  -- the logarithmic factor is at least `1`
  have hL1 : (1 : ℝ) ≤ Real.log ((M : ℝ) * (|τ| + 2)) + 1 := by
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by
      have hMn : 1 ≤ M := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne M))
      exact_mod_cast hMn
    have ht2 : (2 : ℝ) ≤ |τ| + 2 := by linarith [abs_nonneg τ]
    have hprod : (3 : ℝ) ≤ (M : ℝ) * (|τ| + 2) := by
      have h3 : (3 : ℝ) = 1 * 3 := by ring
      rw [h3]
      exact mul_le_mul hM1 (by linarith) (by norm_num) (by linarith)
    have hlog : 0 < Real.log ((M : ℝ) * (|τ| + 2)) := Real.log_pos (by linarith)
    linarith
  have hCm0 : (0 : ℝ) ≤ max C0 1 := le_trans (le_of_lt hC0pos) (le_max_left C0 1)
  have hmul : max C0 1 ≤ (max C0 1) * (Real.log ((M : ℝ) * (|τ| + 2)) + 1) :=
    le_mul_of_one_le_right hCm0 hL1
  have hC0le : C0 ≤ max C0 1 := le_max_left C0 1
  rw [neg_mul]
  linarith

end Commons.NumberTheory.DirichletCharacter
