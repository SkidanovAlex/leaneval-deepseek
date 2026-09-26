import Mathlib
import Submission.Work.Modular.Basic
import Submission.Work.Modular.E2_qExpansion_coeff

/-!
# Ramanujan's differential identity `D E₄ = (E₂ E₄ - E₆)/3`

We prove that the normalized derivative `D = (2πi)⁻¹ d/dτ` of the weight-four Eisenstein
series `E₄ = 1 + 240 ∑ σ₃(n) qⁿ` is `(E₂ E₄ - E₆)/3`, where `E₂ = 1 - 24 ∑ σ₁(n) qⁿ` and
`E₆ = 1 - 504 ∑ σ₅(n) qⁿ`.

## Proof outline

The Serre derivative `∂₄E₄ = D E₄ - (4/12)E₂E₄` is slash-invariant of weight `6` (Mathlib's
`Derivative.serreDerivative_slash_invariant`), so the function

`g = ∂₄E₄ + E₆/3 = D E₄ - (E₂E₄ - E₆)/3`

is a weight-`6` modular form for `SL(2, ℤ)`: it is slash-invariant, holomorphic, and bounded
at the cusp `i∞` (the latter because the `q`-series of `D E₄`, `E₂E₄`, `E₆` are all
absolutely convergent, see `serreFun_hasSum`).  Its `q`-expansion has vanishing constant
term: termwise differentiation multiplies the `m`-th `q`-coefficient of `E₄` by `m`
(`qSeries_normalizedDeriv`), so the constant term of `D E₄` is `0`, while
`E₂E₄ - E₆` has constant term `1·1 - 1 = 0`.  Hence the `q`-expansion of `g` has order
`≥ 1 > 6/12 = 0`, and the Sturm bound `ModularForm.sturm_bound_levelOne` gives `g = 0`,
which is the identity.
-/

namespace Work.Modular

open UpperHalfPlane ModularForm EisensteinSeries
open scoped Manifold MatrixGroups ModularForm Topology

/-! ## An analytic tool: `D` multiplies the `m`-th `q`-coefficient by `m` -/

/-- Summability of `m ↦ (m+1)^M ρ^m` for `0 < ρ < 1`. -/
private lemma add_one_pow_mul_geometric (M : ℕ) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Summable fun m : ℕ => ((m : ℝ) + 1) ^ M * ρ ^ m := by
  have hbase : Summable fun n : ℕ => (n : ℝ) ^ M * ρ ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one M (by rwa [Real.norm_eq_abs, abs_of_pos hρ0])
  have hshift : Summable fun n : ℕ => ((n : ℝ) + 1) ^ M * ρ ^ (n + 1) := by
    simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hbase
  have h := hshift.mul_left (ρ⁻¹)
  refine h.congr (fun n => ?_)
  rw [pow_succ]
  field_simp

/-- **`D` acts on a `q`-series by multiplying the `m`-th coefficient by `m`.**  If a function
`f` on the upper half plane is given by an absolutely convergent `q`-expansion
`f τ = ∑ m, c m • q(τ)^m` with `q(τ) = exp (2π i τ)`, and the coefficients have at most
polynomial growth, then `D f = (2πi)⁻¹ d/dτ` is given by the termwise-differentiated series
`D f τ = ∑ m, (m * c m) • q(τ)^m`; in particular its constant term is `0`. -/
theorem qSeries_normalizedDeriv {c : ℕ → ℂ} {C : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (hc : ∀ m : ℕ, ‖c m‖ ≤ C * ((m : ℝ) + 1) ^ N) :
    ∀ τ : ℍ, HasSum (fun m : ℕ ↦ ((m : ℂ) * c m) • Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (Derivative.normalizedDerivOfComplex
        (fun τ : ℍ ↦ ∑' m : ℕ, c m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) τ) := by
  intro τ
  have him : ((τ:ℂ)).im = τ.im := rfl
  set ε : ℝ := τ.im / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith [τ.im_pos]
  set r : ℝ := Real.exp (-(2 * Real.pi * ε)) with hr
  have hr0 : 0 < r := by rw [hr]; exact Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    have h : 0 < 2 * Real.pi * ε := by positivity
    linarith
  set u : ℕ → ℝ := fun m => 2 * Real.pi * (m:ℝ) * C * ((m:ℝ)+1)^N * r^m with hu
  have hu' : Summable u := by
    have h1 : Summable fun m : ℕ => (2 * Real.pi * C) * (((m:ℝ)+1)^(N+1) * r^m) :=
      (add_one_pow_mul_geometric (N+1) hr0 hr1).mul_left (2 * Real.pi * C)
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) h1
    · rw [hu]
      have hm0 : (0:ℝ) ≤ (m:ℝ) + 1 := add_nonneg (Nat.cast_nonneg m) zero_le_one
      have hmn : (0:ℝ) ≤ ((m:ℝ)+1)^N := pow_nonneg hm0 N
      have hrm : (0:ℝ) ≤ r^m := pow_nonneg hr0.le m
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
        (Nat.cast_nonneg m)) hC) hmn) hrm
    · rw [hu]
      have hm0 : (0:ℝ) ≤ (m:ℝ) + 1 := add_nonneg (Nat.cast_nonneg m) zero_le_one
      have hm1 : (m:ℝ) ≤ (m:ℝ) + 1 := le_add_of_nonneg_right zero_le_one
      have hmn : (0:ℝ) ≤ ((m:ℝ)+1)^N := pow_nonneg hm0 N
      have hrm : (0:ℝ) ≤ r^m := pow_nonneg hr0.le m
      have h2πC : (0:ℝ) ≤ 2 * Real.pi * C := by positivity
      have h5 : (m:ℝ) * ((m:ℝ)+1)^N ≤ ((m:ℝ)+1)^N * ((m:ℝ)+1) := by
        calc (m:ℝ) * ((m:ℝ)+1)^N = ((m:ℝ)+1)^N * (m:ℝ) := by ring
          _ ≤ ((m:ℝ)+1)^N * ((m:ℝ)+1) := mul_le_mul_of_nonneg_left hm1 hmn
      calc 2 * Real.pi * (m:ℝ) * C * ((m:ℝ)+1)^N * r^m
          = (2 * Real.pi * C) * ((m:ℝ) * ((m:ℝ)+1)^N * r^m) := by ring
        _ ≤ (2 * Real.pi * C) * (((m:ℝ)+1)^(N+1) * r^m) := by
            calc (2 * Real.pi * C) * ((m:ℝ) * ((m:ℝ)+1)^N * r^m)
                = (2 * Real.pi * C) * r^m * ((m:ℝ) * ((m:ℝ)+1)^N) := by ring
              _ ≤ (2 * Real.pi * C) * r^m * (((m:ℝ)+1)^N * ((m:ℝ)+1)) :=
                  mul_le_mul_of_nonneg_left h5 (mul_nonneg h2πC hrm)
              _ = (2 * Real.pi * C) * (((m:ℝ)+1)^(N+1) * r^m) := by rw [pow_succ]; ring
  have hmem : (τ:ℂ) ∈ {w : ℂ | ε < w.im} := by
    show ε < ((τ:ℂ)).im
    rw [hε, him]; linarith [τ.im_pos]
  have hρ1 : ‖Function.Periodic.qParam 1 (τ:ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hρ0 : 0 < ‖Function.Periodic.qParam 1 (τ:ℂ)‖ := by
    rw [Function.Periodic.norm_qParam]; exact Real.exp_pos _
  have hsum0 : Summable fun m : ℕ => c m * Function.Periodic.qParam 1 (τ:ℂ) ^ m := by
    refine Summable.of_norm_bounded ((add_one_pow_mul_geometric N hρ0 hρ1).mul_left C) (fun m => ?_)
    rw [norm_mul, norm_pow]
    calc ‖c m‖ * ‖Function.Periodic.qParam 1 (τ:ℂ)‖ ^ m
        ≤ (C * ((m:ℝ)+1)^N) * ‖Function.Periodic.qParam 1 (τ:ℂ)‖^m :=
          mul_le_mul_of_nonneg_right (hc m) (by positivity)
      _ = C * (((m:ℝ)+1)^N * ‖Function.Periodic.qParam 1 (τ:ℂ)‖^m) := by ring
  have hbound : ∀ (m : ℕ) (w : ℂ), ε < w.im →
      ‖c m * ((m:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) * Function.Periodic.qParam 1 w ^ m)‖ ≤ u m := by
    intro m w hw
    have hm0 : (0:ℝ) ≤ (m:ℝ) + 1 := add_nonneg (Nat.cast_nonneg m) zero_le_one
    have hq : ‖Function.Periodic.qParam 1 w‖ ≤ r := by
      rw [Function.Periodic.norm_qParam, hr, Real.exp_le_exp]
      rw [div_one]
      have h : 2 * Real.pi * ε ≤ 2 * Real.pi * w.im := by
        have h2 : 0 < 2 * Real.pi := by positivity
        nlinarith [hw]
      linarith
    have hconst : ‖(m:ℂ) * (2 * (Real.pi:ℂ) * Complex.I)‖ = 2 * Real.pi * m := by
      simp only [norm_mul, Complex.norm_natCast, Complex.norm_I, Complex.norm_real, mul_one,
        Real.norm_of_nonneg Real.pi_pos.le]
      norm_num
      ring
    rw [hu]
    calc ‖c m * ((m:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) * Function.Periodic.qParam 1 w ^ m)‖
        = ‖c m‖ * (‖(m:ℂ) * (2 * (Real.pi:ℂ) * Complex.I)‖ * ‖Function.Periodic.qParam 1 w‖ ^ m) := by
          rw [norm_mul, norm_mul, norm_pow]
      _ = ‖c m‖ * ((2 * Real.pi * m) * ‖Function.Periodic.qParam 1 w‖^m) := by rw [hconst]
      _ ≤ (C * ((m:ℝ)+1)^N) * ((2 * Real.pi * m) * r^m) := by
          refine mul_le_mul (hc m) ?_ ?_ ?_
          · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hq m) (by positivity)
          · exact mul_nonneg (by positivity) (pow_nonneg (norm_nonneg _) m)
          · exact mul_nonneg hC (pow_nonneg hm0 N)
      _ = 2 * Real.pi * (m:ℝ) * C * ((m:ℝ)+1)^N * r^m := by ring
  have hderiv : HasDerivAt (fun w : ℂ => ∑' m : ℕ, c m * Function.Periodic.qParam 1 w ^ m)
      (∑' m : ℕ, c m * ((m:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) * Function.Periodic.qParam 1 (τ:ℂ)^m)) (τ:ℂ) := by
    refine hasDerivAt_tsum_of_isPreconnected (u := u) (t := {w : ℂ | ε < w.im})
      (g := fun m w => c m * Function.Periodic.qParam 1 w ^ m)
      (g' := fun m w => c m * ((m:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) * Function.Periodic.qParam 1 w ^ m))
      hu' ?_ ?_ ?_ ?_ hmem hsum0 hmem
    · exact isOpen_lt continuous_const Complex.continuous_im
    · exact (convex_halfSpace_im_gt ε).isPreconnected
    · intro m w hw
      have hQ : HasDerivAt (fun z : ℂ => Function.Periodic.qParam 1 z)
          (2 * (Real.pi : ℂ) * Complex.I * Function.Periodic.qParam 1 w) w := by
        have h1 := ((hasDerivAt_id w).const_mul (2 * (Real.pi : ℂ) * Complex.I)).cexp
        have h2 : (fun z : ℂ => Function.Periodic.qParam 1 z)
            = fun z : ℂ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z) := by
          funext z; simp [Function.Periodic.qParam, div_one, mul_assoc]
        have h3 : Function.Periodic.qParam 1 w = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) := by
          simp [Function.Periodic.qParam, div_one, mul_assoc]
        rw [h2, h3]
        simpa [mul_assoc, mul_comm, mul_left_comm] using h1
      have hkey : (m : ℂ) * Function.Periodic.qParam 1 w ^ (m - 1)
            * (2 * (Real.pi : ℂ) * Complex.I * Function.Periodic.qParam 1 w)
          = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * Function.Periodic.qParam 1 w ^ m := by
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm; simp
        · have hq : Function.Periodic.qParam 1 w ^ (m - 1) * Function.Periodic.qParam 1 w
              = Function.Periodic.qParam 1 w ^ m := by
            rw [← pow_succ, Nat.sub_add_cancel hm]
          calc (m : ℂ) * Function.Periodic.qParam 1 w ^ (m - 1)
                * (2 * (Real.pi : ℂ) * Complex.I * Function.Periodic.qParam 1 w)
              = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
                  * (Function.Periodic.qParam 1 w ^ (m - 1) * Function.Periodic.qParam 1 w) := by ring
            _ = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * Function.Periodic.qParam 1 w ^ m := by rw [hq]
      have h3 := (hQ.pow m).const_mul (c m)
      rw [hkey] at h3
      exact h3
    · intro m w hw
      exact hbound m w hw
  have hsum_g' : Summable fun m : ℕ => c m *
      ((m:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) * Function.Periodic.qParam 1 (τ:ℂ)^m) :=
    Summable.of_norm_bounded hu' (fun m => hbound m (τ:ℂ) hmem)
  have hhas_g' : HasSum (fun m : ℕ => c m *
      ((m:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) * Function.Periodic.qParam 1 (τ:ℂ)^m))
      (deriv (fun w : ℂ => ∑' m : ℕ, c m * Function.Periodic.qParam 1 w ^ m) (τ:ℂ)) :=
    hderiv.deriv.symm ▸ hsum_g'.hasSum
  have h2 : HasSum (fun m : ℕ => (2 * (Real.pi:ℂ) * Complex.I)⁻¹ *
      (c m * ((m:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) * Function.Periodic.qParam 1 (τ:ℂ)^m)))
      ((2 * (Real.pi:ℂ) * Complex.I)⁻¹ * deriv (fun w : ℂ => ∑' m : ℕ, c m * Function.Periodic.qParam 1 w ^ m) (τ:ℂ)) :=
    hhas_g'.mul_left _
  have hsummand : ∀ m : ℕ, (2 * (Real.pi:ℂ) * Complex.I)⁻¹ *
      (c m * ((m:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) * Function.Periodic.qParam 1 (τ:ℂ)^m))
      = ((m : ℂ) * c m) • Function.Periodic.qParam 1 (τ:ℂ)^m := by
    intro m
    rw [smul_eq_mul]
    have hne : (2 * (Real.pi:ℂ) * Complex.I) ≠ 0 := by
      simp [Complex.I_ne_zero, Real.pi_ne_zero]
    field_simp
  rw [show (fun m : ℕ => (2 * (Real.pi:ℂ) * Complex.I)⁻¹ *
        (c m * ((m:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) * Function.Periodic.qParam 1 (τ:ℂ)^m)))
      = fun m : ℕ => ((m : ℂ) * c m) • Function.Periodic.qParam 1 (τ:ℂ)^m from funext hsummand] at h2
  have hOp : {w : ℂ | 0 < w.im} ∈ 𝓝 ((τ:ℂ)) :=
    IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_im) τ.im_pos
  have hcomp : (fun τ : ℍ => ∑' m : ℕ, c m * Function.Periodic.qParam 1 (τ:ℂ)^m) ∘ UpperHalfPlane.ofComplex
      =ᶠ[𝓝 ((τ:ℂ))] fun w : ℂ => ∑' m : ℕ, c m * Function.Periodic.qParam 1 w ^ m := by
    filter_upwards [hOp] with w hw
    simp only [Function.comp_apply]
    have hw' : ((UpperHalfPlane.ofComplex w : ℍ) : ℂ) = w := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    simp only [hw']
  have hG : (fun τ : ℍ => ∑' m : ℕ, c m • Function.Periodic.qParam 1 (τ:ℂ)^m)
      = fun τ : ℍ => ∑' m : ℕ, c m * Function.Periodic.qParam 1 (τ:ℂ)^m := by
    funext τ; exact tsum_congr (fun m => smul_eq_mul _ _)
  rw [hG]
  have hD : Derivative.normalizedDerivOfComplex
        (fun τ : ℍ => ∑' m : ℕ, c m * Function.Periodic.qParam 1 (τ:ℂ)^m) τ
      = (2 * (Real.pi:ℂ) * Complex.I)⁻¹ *
        deriv ((fun τ : ℍ => ∑' m : ℕ, c m * Function.Periodic.qParam 1 (τ:ℂ)^m) ∘ UpperHalfPlane.ofComplex) (τ:ℂ) := rfl
  rw [hD, Filter.EventuallyEq.deriv_eq hcomp]
  exact h2

/-! ## The `q`-expansions of the Eisenstein series `E₄` and `E₆` -/

/-- The `q`-expansion of a normalized Eisenstein series `E k`, as a convergent series. -/
private theorem hasSum_qExpansion_E {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (τ : ℍ) :
    HasSum (fun m : ℕ ↦
      (if m = 0 then 1 else -(2 * k / bernoulli k : ℂ) * ((ArithmeticFunction.sigma (k - 1) m : ℕ) : ℂ))
        • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (E hk τ) := by
  set β : ℂ := -(2 * k / bernoulli k : ℂ)
  have hS : Summable fun n : ℕ ↦ (ArithmeticFunction.sigma (k - 1) (n + 1) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ↑τ) ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr (summable_sigma_mul_cexp_pow (by omega) τ)
  rw [← hasSum_nat_add_iff' 1]
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, smul_eq_mul,
    Finset.range_one, ite_mul, one_mul, Finset.sum_singleton, pow_zero]
  have hval : E hk τ - 1 = β * ∑' n : ℕ,
      (ArithmeticFunction.sigma (k - 1) (n + 1)) * Complex.exp (2 * Real.pi * Complex.I * ↑τ) ^ (n + 1) := by
    have h := q_expansion_bernoulli hk hk2 τ
    simp_rw [zpow_natCast] at h
    rw [h, ← tsum_pnat_eq_tsum_succ (f := fun n ↦
      (ArithmeticFunction.sigma (k - 1) n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ↑τ) ^ n)]
    ring
  rw [hval]
  convert! (hS.mul_left β).hasSum using 1
  · grind [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  · rw [tsum_mul_left]

/-- `q`-expansion coefficients of `E₄`. -/
private noncomputable def qc4 : ℕ → ℂ :=
  fun m => if m = 0 then 1 else (240 : ℂ) * ((ArithmeticFunction.sigma 3 m : ℕ) : ℂ)

/-- `q`-expansion coefficients of `E₂`. -/
private noncomputable def qc2 : ℕ → ℂ :=
  fun m => if m = 0 then 1 else (-24 : ℂ) * ((ArithmeticFunction.sigma 1 m : ℕ) : ℂ)

/-- `q`-expansion coefficients of `E₆`. -/
private noncomputable def qc6 : ℕ → ℂ :=
  fun m => if m = 0 then 1 else (-504 : ℂ) * ((ArithmeticFunction.sigma 5 m : ℕ) : ℂ)

private lemma qc4_growth (m : ℕ) : ‖qc4 m‖ ≤ 240 * ((m : ℝ) + 1) ^ 4 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [qc4]
  · simp only [qc4, hm, ↓reduceIte, norm_mul, Complex.norm_natCast]
    have h1 : ((ArithmeticFunction.sigma 3 m : ℕ) : ℝ) ≤ (m:ℝ)^4 := by
      exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 3 m
    have h2 : (m : ℝ) ^ 4 ≤ ((m : ℝ) + 1) ^ 4 :=
      pow_le_pow_left₀ (Nat.cast_nonneg m) (by linarith) 4
    norm_num
    exact h1.trans h2

private lemma E4_hasSum_qExpansion (τ : ℍ) :
    HasSum (fun m : ℕ ↦ qc4 m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (E4 τ) := by
  have h := hasSum_qExpansion_E (k := 4) (by norm_num) ⟨2, rfl⟩ τ
  simp only [show bernoulli 4 = -1 / 30 by decide +kernel] at h
  norm_num at h
  simpa [qc4, ModularForm.E₄] using h

private lemma E6_hasSum_qExpansion (τ : ℍ) :
    HasSum (fun m : ℕ ↦ qc6 m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (E6 τ) := by
  have h := hasSum_qExpansion_E (k := 6) (by norm_num) ⟨3, rfl⟩ τ
  simp only [show bernoulli 6 = 1 / 42 by decide +kernel] at h
  norm_num at h
  simpa [qc6, ModularForm.E₆] using h

private lemma E2_hasSum_qExpansion (τ : ℍ) :
    HasSum (fun m : ℕ ↦ qc2 m • Function.Periodic.qParam 1 (τ : ℂ) ^ m) (E2 τ) := by
  have h := EisensteinSeries.hasSum_qExpansion_E2 τ
  simpa [qc2, Function.Periodic.qParam, div_one, mul_assoc] using h

/-! ## The weight-six modular form `∂₄E₄ + E₆/3` -/

/-- The function `∂₄E₄ + E₆/3 = D E₄ - (E₂E₄ - E₆)/3`, which we show to be zero. -/
noncomputable def serreFun : ℍ → ℂ :=
  Derivative.serreDerivative (4 : ℂ) E4 + (1 / 3 : ℂ) • E6

/-- `serreFun` written with the normalized derivative, in the exact shape in which it will be
evaluated. -/
private lemma serreFun_eq_fun : serreFun
    = (Derivative.normalizedDerivOfComplex E4) - (1 / 3 : ℂ) • (E2 * E4) + (1 / 3 : ℂ) • E6 := by
  funext z
  have h : (4 : ℂ) * 12⁻¹ = (1 / 3 : ℂ) := by norm_num
  simp only [serreFun, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
    Derivative.serreDerivative_apply, h]
  ring

/-- The `q`-expansion of the normalized derivative of `E₄`: termwise differentiation multiplies the
`m`-th coefficient of the `q`-expansion of `E₄` by `m`. -/
private lemma hasSum_deriv_E4 (τ : ℍ) :
    HasSum (fun m : ℕ ↦ ((m : ℂ) * qc4 m) • Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (Derivative.normalizedDerivOfComplex E4 τ) := by
  have hE4eq : (E4 : ℍ → ℂ)
      = fun τ : ℍ ↦ ∑' m : ℕ, qc4 m • Function.Periodic.qParam 1 (τ : ℂ) ^ m := by
    funext τ; exact (E4_hasSum_qExpansion τ).tsum_eq.symm
  have h := qSeries_normalizedDeriv (c := qc4) (C := 240) (N := 4) (by norm_num) qc4_growth τ
  rwa [← hE4eq] at h

/-- `q(τ) = exp (2πi τ)` is periodic of period `1`. -/
private lemma qParam_one_add_one (z : ℂ) :
    Function.Periodic.qParam 1 (z + 1) = Function.Periodic.qParam 1 z := by
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [show 2 * ↑Real.pi * Complex.I * (z + 1)
      = 2 * ↑Real.pi * Complex.I * z + (1 : ℤ) * (2 * ↑Real.pi * Complex.I) by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private lemma periodic_deriv_E4 :
    Function.Periodic ((Derivative.normalizedDerivOfComplex E4) ∘ UpperHalfPlane.ofComplex) 1 := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + 1).im := by simpa using hw
    have h1 : ((UpperHalfPlane.ofComplex w : ℍ) : ℂ) = w := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    have h2 : ((UpperHalfPlane.ofComplex (w + 1) : ℍ) : ℂ) = w + 1 := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw']
    simp only [Function.comp_apply]
    rw [← (hasSum_deriv_E4 (UpperHalfPlane.ofComplex (w + 1))).tsum_eq,
      ← (hasSum_deriv_E4 (UpperHalfPlane.ofComplex w)).tsum_eq]
    exact tsum_congr (fun m => by rw [h1, h2, qParam_one_add_one])
  · have hw0 : w.im ≤ 0 := le_of_not_gt hw
    have hw' : (w + 1).im ≤ 0 := by simpa using hw0
    simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_nonpos hw',
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hw0]

private lemma mdiff_deriv_E4 : MDiff (Derivative.normalizedDerivOfComplex E4) :=
  Derivative.normalizedDerivOfComplex_mdifferentiable (ModularFormClass.holo ModularForm.E₄)

private lemma bounded_deriv_E4 : IsBoundedAtImInfty (Derivative.normalizedDerivOfComplex E4) :=
  UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion one_pos hasSum_deriv_E4

private lemma analytic_deriv_E4 :
    AnalyticAt ℂ (cuspFunction 1 (Derivative.normalizedDerivOfComplex E4)) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero one_pos periodic_deriv_E4 mdiff_deriv_E4
    bounded_deriv_E4

/-- The constant term of the `q`-expansion of `D E₄` vanishes. -/
private lemma coeff_zero_deriv_E4 :
    (qExpansion 1 (Derivative.normalizedDerivOfComplex E4)).coeff 0 = 0 := by
  have h := qExpansion_coeff_unique_plain (c := fun m : ℕ => (m : ℂ) * qc4 m)
    (f := Derivative.normalizedDerivOfComplex E4) one_pos analytic_deriv_E4 hasSum_deriv_E4 0
  rw [← h]
  simp

private lemma analytic_E2 : AnalyticAt ℂ (cuspFunction 1 E2) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero one_pos E2_periodic_one E2_mdifferentiable
    EisensteinSeries.isBoundedAtImInfty_E2

private lemma analytic_E4 : AnalyticAt ℂ (cuspFunction 1 (E4 : ℍ → ℂ)) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E₄) one_mem_strictPeriods_SL)
    (ModularFormClass.holo ModularForm.E₄) (ModularFormClass.bdd_at_infty ModularForm.E₄)

private lemma analytic_E6 : AnalyticAt ℂ (cuspFunction 1 (E6 : ℍ → ℂ)) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex (ModularForm.E₆) one_mem_strictPeriods_SL)
    (ModularFormClass.holo ModularForm.E₆) (ModularFormClass.bdd_at_infty ModularForm.E₆)

private lemma coeff_zero_E4 : (qExpansion 1 (E4 : ℍ → ℂ)).coeff 0 = 1 := by
  have h := EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) ⟨2, rfl⟩
  simpa [ModularForm.E₄] using h

private lemma coeff_zero_E6 : (qExpansion 1 (E6 : ℍ → ℂ)).coeff 0 = 1 := by
  have h := EisensteinSeries.E_qExpansion_coeff_zero (k := 6) (by norm_num) ⟨3, rfl⟩
  simpa [ModularForm.E₆] using h

private lemma bounded_serreFun : IsBoundedAtImInfty serreFun := by
  have hD : IsBoundedAtImInfty (Derivative.normalizedDerivOfComplex E4) := bounded_deriv_E4
  have h2 : IsBoundedAtImInfty (E2 : ℍ → ℂ) := EisensteinSeries.isBoundedAtImInfty_E2
  have h4 : IsBoundedAtImInfty (E4 : ℍ → ℂ) := ModularFormClass.bdd_at_infty ModularForm.E₄
  have h6 : IsBoundedAtImInfty ((1 / 3 : ℂ) • (E6 : ℍ → ℂ)) :=
    Filter.BoundedAtFilter.smul (1 / 3) (ModularFormClass.bdd_at_infty ModularForm.E₆)
  have h24 : IsBoundedAtImInfty ((1 / 3 : ℂ) • (E2 * E4 : ℍ → ℂ)) :=
    Filter.BoundedAtFilter.smul (1 / 3) (Filter.BoundedAtFilter.mul h2 h4)
  have h := Filter.BoundedAtFilter.add
    (Filter.BoundedAtFilter.add hD (Filter.BoundedAtFilter.neg h24)) h6
  rw [serreFun_eq_fun]
  exact h

/-! ## The Sturm bound argument -/

private lemma serreFun_slash (γ : GL (Fin 2) ℝ) (hγ : γ ∈ 𝒮ℒ) :
    serreFun ∣[(6 : ℤ)] γ = serreFun := by
  obtain ⟨γ₀, rfl⟩ := MonoidHom.mem_range.mp hγ
  have hmem : (Matrix.SpecialLinearGroup.mapGL ℝ γ₀) ∈ 𝒮ℒ :=
    MonoidHom.mem_range.mpr ⟨γ₀, rfl⟩
  have h4inv : (E4 : ℍ → ℂ) ∣[(4 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ₀) = E4 :=
    SlashInvariantFormClass.slash_action_eq (ModularForm.E₄) _ hmem
  have hS : Derivative.serreDerivative (4 : ℂ) (E4 : ℍ → ℂ)
        ∣[(6 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ₀)
      = Derivative.serreDerivative (4 : ℂ) (E4 : ℍ → ℂ) := by
    have h := Derivative.serreDerivative_slash_invariant (k := 4) (F := (E4 : ℍ → ℂ))
      (ModularFormClass.holo ModularForm.E₄) (γ := γ₀) h4inv
    exact h
  have hE : ((1 / 3 : ℂ) • (E6 : ℍ → ℂ))
        ∣[(6 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ₀) = (1 / 3 : ℂ) • E6 := by
    rw [smul_slash]
    simp only [SlashInvariantFormClass.slash_action_eq (ModularForm.E₆) _ hmem, σ,
      Subgroup.HasDetOne.det_eq hmem]
    norm_num
  simp only [serreFun, SlashAction.add_slash, hS, hE]

private lemma serreFun_mdiff : MDiff serreFun := by
  have h1 : MDiff (Derivative.serreDerivative (4 : ℂ) (E4 : ℍ → ℂ)) :=
    Derivative.serreDerivative_mdifferentiable 4 (ModularFormClass.holo ModularForm.E₄)
  have h2 : MDiff ((1 / 3 : ℂ) • (E6 : ℍ → ℂ)) :=
    MDifferentiable.const_smul (1 / 3) (ModularFormClass.holo ModularForm.E₆)
  exact h1.add h2

/-- The weight-`6` modular form `∂₄E₄ + E₆/3`. -/
private noncomputable def serreForm : ModularForm 𝒮ℒ 6 where
  toFun := serreFun
  slash_action_eq' := serreFun_slash
  holo' := serreFun_mdiff
  bdd_at_cusps' := by
    intro c hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    change IsBoundedAtImInfty (serreFun ∣[(6 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ))
    rw [serreFun_slash _ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)]
    exact bounded_serreFun

private lemma serreForm_coe : (serreForm : ℍ → ℂ) = serreFun := rfl

/-- The `q`-expansion of the weight-six form `∂₄E₄ + E₆/3` has vanishing constant term. -/
private lemma serreForm_qExpansion_coeff_zero :
    (qExpansion 1 (serreForm : ℍ → ℂ)).coeff 0 = 0 := by
  rw [serreForm_coe, serreFun_eq_fun]
  have hD : AnalyticAt ℂ (cuspFunction 1 (Derivative.normalizedDerivOfComplex E4)) 0 :=
    analytic_deriv_E4
  have h2 : AnalyticAt ℂ (cuspFunction 1 (E2 : ℍ → ℂ)) 0 := analytic_E2
  have h4 : AnalyticAt ℂ (cuspFunction 1 (E4 : ℍ → ℂ)) 0 := analytic_E4
  have h6 : AnalyticAt ℂ (cuspFunction 1 (E6 : ℍ → ℂ)) 0 := analytic_E6
  have h24 : AnalyticAt ℂ (cuspFunction 1 (E2 * E4 : ℍ → ℂ)) 0 := by
    rw [cuspFunction_mul h2.continuousAt h4.continuousAt]
    exact h2.mul h4
  have hs24 : AnalyticAt ℂ (cuspFunction 1 ((1 / 3 : ℂ) • (E2 * E4 : ℍ → ℂ))) 0 := by
    rw [cuspFunction_smul h24.continuousAt]
    exact h24.const_smul (c := (1 / 3 : ℂ))
  have hs6 : AnalyticAt ℂ (cuspFunction 1 ((1 / 3 : ℂ) • (E6 : ℍ → ℂ))) 0 := by
    rw [cuspFunction_smul h6.continuousAt]
    exact h6.const_smul (c := (1 / 3 : ℂ))
  have hsub : AnalyticAt ℂ
      (cuspFunction 1 ((Derivative.normalizedDerivOfComplex E4) - (1 / 3 : ℂ) • (E2 * E4 : ℍ → ℂ))) 0 := by
    rw [cuspFunction_sub hD.continuousAt hs24.continuousAt]
    exact hD.sub hs24
  rw [qExpansion_add hsub hs6, qExpansion_sub hD hs24, qExpansion_smul h24 (1 / 3),
    qExpansion_smul h6 (1 / 3), qExpansion_mul h2 h4]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, PowerSeries.coeff_mul,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  rw [coeff_zero_deriv_E4, E2_qExpansion_coeff 0, coeff_zero_E4, coeff_zero_E6]
  norm_num

private lemma serreForm_eq_zero : serreForm = 0 := by
  refine ModularForm.sturm_bound_levelOne (f := serreForm) ?_
  have hle : (1 : ℕ∞) ≤ (qExpansion 1 (serreForm : ℍ → ℂ)).order := by
    refine PowerSeries.nat_le_order _ 1 ?_
    intro i hi
    obtain rfl : i = 0 := by omega
    exact serreForm_qExpansion_coeff_zero
  have h0 : (((6 : ℤ).toNat / 12 : ℕ) : ℕ∞) = 0 := by norm_num
  rw [h0]
  exact lt_of_lt_of_le (by norm_num) hle

/-- Ramanujan's identity `D E₄ = (E₂ E₄ - E₆)/3`.

A suggested route, using only Mathlib plus the level-one Sturm bound: the Serre derivative
`∂₄ E₄ = D E₄ - (4/12) E₂ E₄` is slash-invariant of weight `6`
(`Derivative.serreDerivative_slash_invariant`), so `H := D E₄ - (E₂ E₄ - E₆)/3 = ∂₄E₄ + E₆/3`
is a weight-`6` level-one modular form; its `q`-expansion has order at least `1` (all constant
terms cancel since `D` lowers the `q`-order and `E₂(∞) = E₄(∞) = E₆(∞) = 1`), and `1 > 6/12`, so
`ModularForm.sturm_bound_levelOne` gives `H = 0`. -/
theorem ramanujan_E4 :
    Derivative.normalizedDerivOfComplex E4 = fun z : ℍ => (E2 z * E4 z - E6 z) / 3 := by
  funext z
  have hz : serreFun z = 0 := by
    have h : (serreForm : ℍ → ℂ) z = 0 := by
      have h' : serreForm = 0 := serreForm_eq_zero
      have h2 := congr_fun (congrArg (fun f : ModularForm 𝒮ℒ 6 => (f : ℍ → ℂ)) h') z
      simpa using h2
    rwa [serreForm_coe] at h
  rw [serreFun_eq_fun] at hz
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at hz
  rw [div_eq_mul_inv]
  linear_combination hz

end Work.Modular
