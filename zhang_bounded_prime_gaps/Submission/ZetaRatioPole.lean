import Mathlib
import Submission.ZetaWN
import Submission.ZetaResidueUniform
import Submission.UniformPole

open scoped BigOperators Topology
open Filter

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-!
# P8 (41) for one coordinate: the `ζ_WN`-ratio at the pole

The heart of Polymath8a's Lemma 4.1 (display (41)) is the evaluation of the
modified-zeta ratio at the sieve's points `1 + (1+iξ)/log x`:

    ζ_WN(1+(2+iξ+iξ')/log x) / (ζ_WN(1+(1+iξ)/log x)·ζ_WN(1+(1+iξ')/log x))
      = (1 + o(1)) · (1+iξ)(1+iξ')·N / ((2+iξ+iξ')·B(x)·φ(N)) ,

uniformly for `|ξ|, |ξ'| ≤ √(log x)`, where `B(x) = (φ(W)/W)·log x` and
`q = WN`, `(W,N) = 1`.  The input is the *uniform* per-modulus residue bound
`zetaWN_residue_uniform_local` (`Submission.ZetaResidueUniform`):
`ζ_q(1+z)·z·(q/φ(q)) = 1 + O(‖z‖)` for `‖z‖ ≤ δ_q`.  Writing
`η(z) := ζ_q(1+z)·z·(q/φ(q)) = 1 + O(‖z‖)` one has

    ζ_q(1+z) = η(z)·φ(q)/(q z) ,

so the ratio becomes `η(z₃)/(η(z₁)η(z₂))·(q z₁ z₂)/(φ(q) z₃)`, and the scalar
identity `q·z₁·z₂·P = φ(q)·z₃` with `P = poleFactor W N ξ ξ' x` shows that the
whole expression is `η(z₃)/(η(z₁)η(z₂)) = 1 + O(‖z₁‖+‖z₂‖+‖z₃‖)`, uniformly
`→ 1` on the cube.  All kernel-verified, zero `sorry`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The Fourier pole factor of P8 (41) for one coordinate pair `(ξ, ξ')`:
`(2+iξ+iξ')·B(x)·φ(N) / ((1+iξ)(1+iξ')·N)` with `B(x) = (φ(W)/W)·log x`. -/
noncomputable def poleFactor (W N : ℕ) (ξ ξ' : ℝ) (x : ℕ) : ℂ :=
  (((2 : ℂ) + (ξ + ξ') * Complex.I) *
    ((((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ)) * (N.totient : ℂ))) /
  (((1 : ℂ) + ξ * Complex.I) * ((1 : ℂ) + ξ' * Complex.I) * (N : ℂ))

/-- Norm bound for the sum of the two truncated points `z₁ + z₂` on the cube. -/
lemma logZ_add_norm_le (ξ ξ' : ℝ) (x : ℕ)
    (hξ : |ξ| ≤ Real.sqrt (Real.log (x : ℝ)))
    (hξ' : |ξ'| ≤ Real.sqrt (Real.log (x : ℝ))) (h1 : 1 ≤ Real.log (x : ℝ)) :
    ‖logZ ξ x + logZ ξ' x‖ ≤
      2 * ((Real.log (x : ℝ))⁻¹ + (Real.sqrt (Real.log (x : ℝ)))⁻¹) := by
  calc
    ‖logZ ξ x + logZ ξ' x‖ ≤ ‖logZ ξ x‖ + ‖logZ ξ' x‖ := norm_add_le _ _
    _ ≤ ((Real.log (x : ℝ))⁻¹ + (Real.sqrt (Real.log (x : ℝ)))⁻¹) +
          ((Real.log (x : ℝ))⁻¹ + (Real.sqrt (Real.log (x : ℝ)))⁻¹) :=
        add_le_add (logZ_norm_le_sum_inv ξ x hξ h1) (logZ_norm_le_sum_inv ξ' x hξ' h1)
    _ = 2 * ((Real.log (x : ℝ))⁻¹ + (Real.sqrt (Real.log (x : ℝ)))⁻¹) := by ring

/-- The scalar identity behind (41): `q·z₁·z₂·P = φ(q)·(z₁+z₂)` for
`q = WN`, `z₁ = logZ ξ x`, `z₂ = logZ ξ' x` and `P = poleFactor W N ξ ξ' x`. -/
lemma poleFactor_scalar (W N : ℕ) (hW : W ≠ 0) (hN : N ≠ 0) (hcop : W.Coprime N)
    (ξ ξ' : ℝ) (x : ℕ) (hlog : Real.log (x : ℝ) ≠ 0) :
    (((W * N : ℕ)) : ℂ) * logZ ξ x * logZ ξ' x * poleFactor W N ξ ξ' x =
      ((W * N).totient : ℂ) * (logZ ξ x + logZ ξ' x) := by
  have hWc : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hφmul : ((W * N).totient : ℂ) = (W.totient : ℂ) * (N.totient : ℂ) := by
    rw [Nat.totient_mul hcop, Nat.cast_mul]
  have hL : (Real.log (x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog
  have h1ξ : (1 : ℂ) + ξ * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have h1ξ' : (1 : ℂ) + ξ' * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have h2 : (2 : ℂ) + (ξ + ξ') * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have h1ξb : (1 : ℂ) + Complex.I * ξ ≠ 0 := by rw [mul_comm]; exact h1ξ
  have h1ξb' : (1 : ℂ) + Complex.I * ξ' ≠ 0 := by rw [mul_comm]; exact h1ξ'
  rw [hφmul]
  simp only [poleFactor, logZ, Nat.cast_mul]
  field_simp [hWc, hNc, hL, h1ξ, h1ξ', h1ξb, h1ξb', h2]
  ring_nf

/-- **P8 (41), single coordinate (modified-zeta side).**  For coprime `W, N ≠ 0`
there is `x₀` and a vanishing error `ε` such that for all `x ≥ x₀` and all
`ξ, ξ'` in the truncation cube,

    ‖ ζ_WN(1+(z₁+z₂)) / (ζ_WN(1+z₁)·ζ_WN(1+z₂)) · P − 1 ‖ ≤ ε(x) ,
    z₁ := (1+iξ)/log x ,  z₂ := (1+iξ')/log x ,
    P := (2+iξ+iξ')·B(x)·φ(N) / ((1+iξ)(1+iξ')·N) ,  B(x) = (φ(W)/W)·log x . -/
theorem zetaWN_ratio_pole_uniform (W N : ℕ) (hW : W ≠ 0) (hN : N ≠ 0)
    (hcop : W.Coprime N) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ x : ℕ, x₀ ≤ x → ∀ ξ ξ' : ℝ,
        |ξ| ≤ Real.sqrt (Real.log (x : ℝ)) → |ξ'| ≤ Real.sqrt (Real.log (x : ℝ)) →
        ‖zetaWN (W * N) (1 + (logZ ξ x + logZ ξ' x)) /
            (zetaWN (W * N) (1 + logZ ξ x) * zetaWN (W * N) (1 + logZ ξ' x)) *
            poleFactor W N ξ ξ' x - 1‖ ≤ ε x := by
  classical
  have hq : W * N ≠ 0 := mul_ne_zero hW hN
  rcases zetaWN_residue_uniform_local (W * N) hq with
    ⟨Cq, hCq0, δq, hδq0, hδq12, hres⟩
  let M : ℝ := max 1 (max ((4 / δq) ^ 2) ((16 * Cq) ^ 2))
  let x₀ : ℕ := Nat.ceil (Real.exp M) + 1
  let ε : ℕ → ℝ := fun x : ℕ =>
    10 * Cq * ((Real.log (x : ℝ))⁻¹ + (Real.sqrt (Real.log (x : ℝ)))⁻¹)
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    dsimp [ε]
    have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h1o : Tendsto (fun x : ℕ => (Real.log (x : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hlog
    have hsqrt : Tendsto (fun x : ℕ => Real.sqrt (Real.log (x : ℝ))) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp hlog
    have h2o : Tendsto (fun x : ℕ => (Real.sqrt (Real.log (x : ℝ)))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hsqrt
    simpa using (Tendsto.const_mul (10 * Cq) (h1o.add h2o))
  refine ⟨x₀, ε, hε0, ?_⟩
  intro x hxx ξ ξ' hξ hξ'
  have hxexp : Real.exp M < (x : ℝ) := by
    have h1 : Real.exp M < ((Nat.ceil (Real.exp M) + 1 : ℕ) : ℝ) := by
      have h1' : Real.exp M ≤ (Nat.ceil (Real.exp M) : ℕ) := Nat.le_ceil (Real.exp M)
      have h2 : ((Nat.ceil (Real.exp M) : ℕ) : ℝ) < ((Nat.ceil (Real.exp M) + 1 : ℕ) : ℝ) := by
        norm_num
      exact h1'.trans_lt h2
    have hle : ((Nat.ceil (Real.exp M) + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxx
    exact h1.trans_le hle
  have hlogM : M ≤ Real.log (x : ℝ) := by
    have hm := Real.log_lt_log (Real.exp_pos M) hxexp
    have : M < Real.log (x : ℝ) := by simpa [Real.log_exp] using hm
    exact le_of_lt this
  have hL1 : 1 ≤ Real.log (x : ℝ) := le_trans (le_max_left _ _) hlogM
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hL4 : (4 / δq) ^ 2 ≤ Real.log (x : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hlogM
  have hL16 : (16 * Cq) ^ 2 ≤ Real.log (x : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hlogM
  -- abbreviations for the exponent sum and errors
  set ϱ : ℝ := (Real.log (x : ℝ))⁻¹ + (Real.sqrt (Real.log (x : ℝ)))⁻¹ with hϱdef
  have hϱle : (Real.log (x : ℝ))⁻¹ + (Real.sqrt (Real.log (x : ℝ)))⁻¹ ≤
      2 / Real.sqrt (Real.log (x : ℝ)) := by
    have hsqrt_ge1 : 1 ≤ Real.sqrt (Real.log (x : ℝ)) := by
      have h := Real.sqrt_le_sqrt hL1
      rwa [Real.sqrt_one] at h
    have hLpos' : 0 < Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_pos.2 hLpos
    have h1 : (Real.log (x : ℝ))⁻¹ ≤ (Real.sqrt (Real.log (x : ℝ)))⁻¹ := by
      rw [inv_le_inv₀ hLpos hLpos']
      calc Real.sqrt (Real.log (x : ℝ)) ≤ Real.sqrt (Real.log (x : ℝ)) ^ 2 := by
            nlinarith [hsqrt_ge1]
        _ = Real.log (x : ℝ) := Real.sq_sqrt hLpos.le
    have h2 : 2 / Real.sqrt (Real.log (x : ℝ)) =
        (Real.sqrt (Real.log (x : ℝ)))⁻¹ + (Real.sqrt (Real.log (x : ℝ)))⁻¹ := by
      rw [div_eq_mul_inv]; ring
    linarith [h1, h2]
  have hϱδ : ϱ ≤ δq / 2 := by
    have hLpos' : 0 < Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_pos.2 hLpos
    have hsqrtL_ge : 4 / δq ≤ Real.sqrt (Real.log (x : ℝ)) := by
      have h := Real.sqrt_le_sqrt hL4
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)] at h
      exact h
    have h1 : 2 / Real.sqrt (Real.log (x : ℝ)) ≤ δq / 2 := by
      rw [div_le_iff₀ hLpos']
      calc (2 : ℝ) = (δq / 2) * (4 / δq) := by field_simp <;> norm_num
        _ ≤ (δq / 2) * Real.sqrt (Real.log (x : ℝ)) :=
            mul_le_mul_of_nonneg_left hsqrtL_ge (by linarith)
    exact hϱle.trans h1
  have hϱC : Cq * ϱ ≤ 1 / 8 := by
    have hLpos' : 0 < Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_pos.2 hLpos
    have hsqrtCq_ge : 16 * Cq ≤ Real.sqrt (Real.log (x : ℝ)) := by
      have h := Real.sqrt_le_sqrt hL16
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)] at h
      exact h
    have h1 : Cq * (2 / Real.sqrt (Real.log (x : ℝ))) ≤ 1 / 8 := by
      rw [← mul_div_assoc, div_le_iff₀ hLpos']
      calc Cq * 2 = (1 / 8 : ℝ) * (16 * Cq) := by ring
        _ ≤ (1 / 8) * Real.sqrt (Real.log (x : ℝ)) :=
            mul_le_mul_of_nonneg_left hsqrtCq_ge (by norm_num)
    have h2 : Cq * ϱ ≤ Cq * (2 / Real.sqrt (Real.log (x : ℝ))) :=
      mul_le_mul_of_nonneg_left (by rw [hϱdef]; exact hϱle) hCq0.le
    linarith [h1, h2]
  have hϱ0 : 0 ≤ ϱ := by
    rw [hϱdef]
    have h1 : 0 ≤ (Real.log (x : ℝ))⁻¹ := inv_nonneg.mpr hLpos.le
    have h2 : 0 ≤ (Real.sqrt (Real.log (x : ℝ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    linarith
  -- norm bounds for the three points
  have hnorm1 : ‖logZ ξ x‖ ≤ ϱ := by rw [hϱdef]; exact logZ_norm_le_sum_inv ξ x hξ hL1
  have hnorm2 : ‖logZ ξ' x‖ ≤ ϱ := by rw [hϱdef]; exact logZ_norm_le_sum_inv ξ' x hξ' hL1
  have hnorm3 : ‖logZ ξ x + logZ ξ' x‖ ≤ 2 * ϱ := by
    rw [hϱdef]; exact logZ_add_norm_le ξ ξ' x hξ hξ' hL1
  -- nonvanishing
  have hξnz : (1 : ℂ) + ξ * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re] at this
  have hξnz' : (1 : ℂ) + ξ' * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re] at this
  have h3nz : (2 : ℂ) + (ξ + ξ') * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re] at this
  have hlogC : (Real.log (x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hLpos.ne'
  have hz1nz : logZ ξ x ≠ 0 := by
    dsimp [logZ]; exact div_ne_zero hξnz hlogC
  have hz2nz : logZ ξ' x ≠ 0 := by
    dsimp [logZ]; exact div_ne_zero hξnz' hlogC
  have hz3nz : logZ ξ x + logZ ξ' x ≠ 0 := by
    have hEq : logZ ξ x + logZ ξ' x =
        ((2 : ℂ) + (ξ + ξ') * Complex.I) / (Real.log (x : ℝ) : ℂ) := by
      dsimp [logZ]; rw [← add_div]; congr 1; ring
    rw [hEq]; exact div_ne_zero h3nz hlogC
  have hqC : ((W * N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hq
  have hφqC : (((W * N).totient : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)).ne'
  -- the η's
  set η : ℂ → ℂ := fun z => zetaWN (W * N) (1 + z) * z *
    (((W * N : ℕ) : ℂ) / ((W * N).totient : ℂ)) with hηdef
  have hz1δ : ‖logZ ξ x‖ ≤ δq := hnorm1.trans (by linarith [hϱδ, hδq0])
  have hz2δ : ‖logZ ξ' x‖ ≤ δq := hnorm2.trans (by linarith [hϱδ, hδq0])
  have hz3δ : ‖logZ ξ x + logZ ξ' x‖ ≤ δq := hnorm3.trans (by linarith [hϱδ, hδq0])
  have he1 : ‖η (logZ ξ x) - 1‖ ≤ Cq * ϱ := by
    rw [hηdef]
    dsimp only
    exact (hres (logZ ξ x) hz1nz hz1δ).trans (mul_le_mul_of_nonneg_left hnorm1 hCq0.le)
  have he2 : ‖η (logZ ξ' x) - 1‖ ≤ Cq * ϱ := by
    rw [hηdef]
    dsimp only
    exact (hres (logZ ξ' x) hz2nz hz2δ).trans (mul_le_mul_of_nonneg_left hnorm2 hCq0.le)
  have he3 : ‖η (logZ ξ x + logZ ξ' x) - 1‖ ≤ 2 * (Cq * ϱ) := by
    rw [hηdef]
    dsimp only
    calc ‖zetaWN (W * N) (1 + (logZ ξ x + logZ ξ' x)) * (logZ ξ x + logZ ξ' x) *
            ((W * N : ℕ) / (W * N).totient) - 1‖
        ≤ Cq * ‖logZ ξ x + logZ ξ' x‖ := hres (logZ ξ x + logZ ξ' x) hz3nz hz3δ
      _ ≤ Cq * (2 * ϱ) := mul_le_mul_of_nonneg_left hnorm3 hCq0.le
      _ = 2 * (Cq * ϱ) := by ring
  have he1' : ‖η (logZ ξ x) - 1‖ ≤ 1 / 8 := he1.trans hϱC
  have he2' : ‖η (logZ ξ' x) - 1‖ ≤ 1 / 8 := he2.trans hϱC
  have he3' : ‖η (logZ ξ x + logZ ξ' x) - 1‖ ≤ 1 / 2 := by
    have : 2 * (Cq * ϱ) ≤ 1 / 2 := by linarith [hϱC]
    exact he3.trans this
  have hη1nz : η (logZ ξ x) ≠ 0 := by
    intro h
    have h1 : ‖η (logZ ξ x) - 1‖ = 1 := by rw [h]; norm_num
    linarith
  have hη2nz : η (logZ ξ' x) ≠ 0 := by
    intro h
    have h1 : ‖η (logZ ξ' x) - 1‖ = 1 := by rw [h]; norm_num
    linarith
  have hη3nz : η (logZ ξ x + logZ ξ' x) ≠ 0 := by
    intro h
    have h1 : ‖η (logZ ξ x + logZ ξ' x) - 1‖ = 1 := by rw [h]; norm_num
    linarith
  -- ζ-values in terms of η
  have hζ1 : zetaWN (W * N) (1 + logZ ξ x) =
      η (logZ ξ x) * (((W * N).totient : ℂ) / (((W * N : ℕ) : ℂ) * logZ ξ x)) := by
    rw [hηdef]
    dsimp only
    field_simp [hz1nz, hqC, hφqC]
  have hζ2 : zetaWN (W * N) (1 + logZ ξ' x) =
      η (logZ ξ' x) * (((W * N).totient : ℂ) / (((W * N : ℕ) : ℂ) * logZ ξ' x)) := by
    rw [hηdef]
    dsimp only
    field_simp [hz2nz, hqC, hφqC]
  have hζ3 : zetaWN (W * N) (1 + (logZ ξ x + logZ ξ' x)) =
      η (logZ ξ x + logZ ξ' x) *
        (((W * N).totient : ℂ) / (((W * N : ℕ) : ℂ) * (logZ ξ x + logZ ξ' x))) := by
    rw [hηdef]
    dsimp only
    field_simp [hz3nz, hqC, hφqC]
  -- the multiplicative identity
  have hkey := poleFactor_scalar W N hW hN hcop ξ ξ' x hLpos.ne'
  have hmain : (zetaWN (W * N) (1 + (logZ ξ x + logZ ξ' x)) /
        (zetaWN (W * N) (1 + logZ ξ x) * zetaWN (W * N) (1 + logZ ξ' x)) *
        poleFactor W N ξ ξ' x) * (η (logZ ξ x) * η (logZ ξ' x)) =
      η (logZ ξ x + logZ ξ' x) := by
    rw [hζ1, hζ2, hζ3]
    have hstep : (η (logZ ξ x + logZ ξ' x) *
            (((W * N).totient : ℂ) / (((W * N : ℕ) : ℂ) * (logZ ξ x + logZ ξ' x)))) /
        ((η (logZ ξ x) * (((W * N).totient : ℂ) / (((W * N : ℕ) : ℂ) * logZ ξ x))) *
          (η (logZ ξ' x) * (((W * N).totient : ℂ) / (((W * N : ℕ) : ℂ) * logZ ξ' x)))) *
        poleFactor W N ξ ξ' x * (η (logZ ξ x) * η (logZ ξ' x)) =
        η (logZ ξ x + logZ ξ' x) *
          ((((W * N : ℕ) : ℂ) * logZ ξ x * logZ ξ' x * poleFactor W N ξ ξ' x) /
            (((W * N).totient : ℂ) * (logZ ξ x + logZ ξ' x))) := by
      field_simp [hz1nz, hz2nz, hz3nz, hqC, hφqC, hη1nz, hη2nz, hη3nz]
    rw [hstep, hkey]
    field_simp [hφqC, hz3nz]
  have hG : zetaWN (W * N) (1 + (logZ ξ x + logZ ξ' x)) /
        (zetaWN (W * N) (1 + logZ ξ x) * zetaWN (W * N) (1 + logZ ξ' x)) *
        poleFactor W N ξ ξ' x =
      η (logZ ξ x + logZ ξ' x) / (η (logZ ξ x) * η (logZ ξ' x)) := by
    rw [eq_div_iff (mul_ne_zero hη1nz hη2nz)]
    exact hmain
  rw [hG]
  -- the norm bound
  have hsplit : η (logZ ξ x + logZ ξ' x) - η (logZ ξ x) * η (logZ ξ' x) =
      (η (logZ ξ x + logZ ξ' x) - 1) - (η (logZ ξ x) - 1) - (η (logZ ξ' x) - 1) -
        (η (logZ ξ x) - 1) * (η (logZ ξ' x) - 1) := by ring
  have htri : ‖(η (logZ ξ x + logZ ξ' x) - 1) - (η (logZ ξ x) - 1) - (η (logZ ξ' x) - 1) -
      (η (logZ ξ x) - 1) * (η (logZ ξ' x) - 1)‖ ≤
      ‖η (logZ ξ x + logZ ξ' x) - 1‖ + ‖η (logZ ξ x) - 1‖ + ‖η (logZ ξ' x) - 1‖ +
        ‖η (logZ ξ x) - 1‖ * ‖η (logZ ξ' x) - 1‖ := by
    have hA : ‖(η (logZ ξ x + logZ ξ' x) - 1) - (η (logZ ξ x) - 1) - (η (logZ ξ' x) - 1) -
        (η (logZ ξ x) - 1) * (η (logZ ξ' x) - 1)‖ ≤
        ‖(η (logZ ξ x + logZ ξ' x) - 1) - (η (logZ ξ x) - 1) - (η (logZ ξ' x) - 1)‖ +
          ‖(η (logZ ξ x) - 1) * (η (logZ ξ' x) - 1)‖ := norm_sub_le _ _
    have hB : ‖(η (logZ ξ x + logZ ξ' x) - 1) - (η (logZ ξ x) - 1) - (η (logZ ξ' x) - 1)‖ ≤
        ‖(η (logZ ξ x + logZ ξ' x) - 1) - (η (logZ ξ x) - 1)‖ + ‖η (logZ ξ' x) - 1‖ :=
      norm_sub_le _ _
    have hC : ‖(η (logZ ξ x + logZ ξ' x) - 1) - (η (logZ ξ x) - 1)‖ ≤
        ‖η (logZ ξ x + logZ ξ' x) - 1‖ + ‖η (logZ ξ x) - 1‖ := norm_sub_le _ _
    have hD : ‖(η (logZ ξ x) - 1) * (η (logZ ξ' x) - 1)‖ =
        ‖η (logZ ξ x) - 1‖ * ‖η (logZ ξ' x) - 1‖ := norm_mul _ _
    linarith [hA, hB, hC, hD.le, hD.ge]
  have hDbound : ‖η (logZ ξ x + logZ ξ' x) - η (logZ ξ x) * η (logZ ξ' x)‖ ≤
      4 * Cq * ϱ + (Cq * ϱ) * (Cq * ϱ) := by
    rw [hsplit]
    calc ‖(η (logZ ξ x + logZ ξ' x) - 1) - (η (logZ ξ x) - 1) - (η (logZ ξ' x) - 1) -
          (η (logZ ξ x) - 1) * (η (logZ ξ' x) - 1)‖
        ≤ ‖η (logZ ξ x + logZ ξ' x) - 1‖ + ‖η (logZ ξ x) - 1‖ + ‖η (logZ ξ' x) - 1‖ +
          ‖η (logZ ξ x) - 1‖ * ‖η (logZ ξ' x) - 1‖ := htri
      _ ≤ 2 * (Cq * ϱ) + Cq * ϱ + Cq * ϱ + (Cq * ϱ) * (Cq * ϱ) := by
          have h12 : ‖η (logZ ξ x) - 1‖ * ‖η (logZ ξ' x) - 1‖ ≤ (Cq * ϱ) * (Cq * ϱ) :=
            mul_le_mul he1 he2 (norm_nonneg _) (mul_nonneg hCq0.le hϱ0)
          linarith [he1, he2, he3, h12]
      _ = 4 * Cq * ϱ + (Cq * ϱ) * (Cq * ϱ) := by ring
  have hη1ge : (7 / 8 : ℝ) ≤ ‖η (logZ ξ x)‖ := by
    have h := abs_norm_sub_norm_le (η (logZ ξ x)) 1
    simp only [norm_one] at h
    have h2 : |‖η (logZ ξ x)‖ - 1| ≤ 1 / 8 := h.trans he1'
    linarith [(abs_le.mp h2).1]
  have hη2ge : (7 / 8 : ℝ) ≤ ‖η (logZ ξ' x)‖ := by
    have h := abs_norm_sub_norm_le (η (logZ ξ' x)) 1
    simp only [norm_one] at h
    have h2 : |‖η (logZ ξ' x)‖ - 1| ≤ 1 / 8 := h.trans he2'
    linarith [(abs_le.mp h2).1]
  have hden : (1 / 2 : ℝ) ≤ ‖η (logZ ξ x) * η (logZ ξ' x)‖ := by
    rw [norm_mul]
    nlinarith [hη1ge, hη2ge]
  have hne : η (logZ ξ x) * η (logZ ξ' x) ≠ 0 := mul_ne_zero hη1nz hη2nz
  have hdiv : η (logZ ξ x + logZ ξ' x) / (η (logZ ξ x) * η (logZ ξ' x)) - 1 =
      (η (logZ ξ x + logZ ξ' x) - η (logZ ξ x) * η (logZ ξ' x)) /
        (η (logZ ξ x) * η (logZ ξ' x)) := by
    field_simp [hne]
  rw [hdiv, norm_div]
  have hεeq : ε x = 10 * Cq * ϱ := by rw [hϱdef]
  have hstep1 : ‖η (logZ ξ x + logZ ξ' x) - η (logZ ξ x) * η (logZ ξ' x)‖ /
        ‖η (logZ ξ x) * η (logZ ξ' x)‖ ≤
      (4 * Cq * ϱ + (Cq * ϱ) * (Cq * ϱ)) / (1 / 2) :=
    div_le_div₀ (by nlinarith [hCq0, hϱ0]) hDbound (by norm_num) hden
  have hstep2 : (4 * Cq * ϱ + (Cq * ϱ) * (Cq * ϱ)) / (1 / 2) ≤ ε x := by
    rw [hεeq, div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)]
    have hx0 : 0 ≤ Cq * ϱ := mul_nonneg hCq0.le hϱ0
    have hx1 : (Cq * ϱ) * (Cq * ϱ) ≤ Cq * ϱ := by nlinarith [hϱC, hx0]
    nlinarith [hx1]
  linarith

end Commons.NumberTheory.MaynardSieve
