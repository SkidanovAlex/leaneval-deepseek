import Mathlib
import Submission.PoleAsymptotic
import Submission.ZetaWN
import Submission.XiTruncation
import Submission.ZetaResidueUniform

open scoped BigOperators Topology
open Filter
open Commons.NumberTheory.MaynardSieve

/-!
# Uniform pole asymptotic — verified assembly of the family hypothesis

Input (a) of the ξ-truncation of P8 Lemma 4.1 is the family hypothesis
`UniformPoleAsymptotic W N` (`Submission/XiTruncation.lean`): the pole
asymptotic of P8 (41) holds uniformly for `|ξ| ≤ √(log x)`.  This module
carries the FULLY VERIFIED assembly of that hypothesis for every coprime
`W, N ≠ 0`, in three layers:

  * scalar identities — `logZ_scalar_identity` and `zetaWN_residue_expr_eq`
    (for `q := W·N`, `B(x) := φ(W)/W·log x`, `z := logZ ξ x = (1+iξ)/log x`:
    `z·(q/φ(q)) = (1+iξ)·N/(B(x)·φ(N))`, and the matching equality of the
    two ζ_q-residue expressions);
  * norm estimates — `logZ_norm_le_ratio` (`‖z‖ ≤ (1+√L)/L` via
    `‖c‖ ≤ 1+|ξ| ≤ 1+√L` and `‖(L:ℂ)‖ = L`), `logZ_norm_le_sum_inv`
    (`‖z‖ ≤ L⁻¹ + (√L)⁻¹`), and `sum_inv_le_delta`
    (from `δ ≤ 1/2` and `(2/δ)² ≤ L` get `L⁻¹ + (√L)⁻¹ ≤ δ`);
  * the theorem `uniformPoleAsymptotic_of_residue W N hW hN hcop` — rcases
    `zetaWN_residue_uniform_local (W·N)` (δq ≤ 1/2), take
    `M := max 1 ((2/δq)²)`, `x₀ := ⌈exp M⌉ + 1`,
    `ε(x) := Cq·((log x)⁻¹ + (√(log x))⁻¹)` (`→ 0`), bound
    `‖z‖ ≤ δq` from `(2/δq)² ≤ log x`, apply the residue bound and rewrite
    through `zetaWN_residue_expr_eq` — proving `UniformPoleAsymptotic W N`.

All kernel-verified (field_simp/ring_nf/nlinarith/simp/omega only), zero
`sorry`.  `Submission/XiTruncation.lean` documents the remaining inputs
(b) crude `|K| ≤ C·log³x` bound and the final truncation theorem of
step (iii), which consume this hypothesis together with the Schwartz decay
inputs already proved there.
-/


namespace Commons.NumberTheory.MaynardSieve

lemma logZ_scalar_identity (W N : ℕ) (hW : W ≠ 0) (hN : N ≠ 0)
    (hcop : W.Coprime N) (ξ : ℝ) (x : ℕ) (hlog : Real.log (x : ℝ) ≠ 0) :
    logZ ξ x * (((W * N : ℕ) : ℂ) / ((W * N).totient : ℂ)) =
      ((1 : ℂ) + ξ * Complex.I) * (N : ℂ) /
        ((((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ)) * (N.totient : ℂ)) := by
  have hWc : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hφW : (W.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hW)).ne'
  have hφN : (N.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN)).ne'
  have hφmul : ((W * N).totient : ℂ) = (W.totient : ℂ) * (N.totient : ℂ) := by
    rw [Nat.totient_mul hcop, Nat.cast_mul]
  have hlogC : (Real.log (x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog
  dsimp [logZ]
  rw [hφmul]
  field_simp [hWc, hNc, hφW, hφN, hlogC]
  rw [Nat.cast_mul]
  ring

lemma zetaWN_residue_expr_eq (W N : ℕ) (hW : W ≠ 0) (hN : N ≠ 0)
    (hcop : W.Coprime N) (ξ : ℝ) (x : ℕ) (hlog : Real.log (x : ℝ) ≠ 0) :
    zetaWN (W * N) (1 + logZ ξ x) * logZ ξ x * (((W * N : ℕ) : ℂ) / ((W * N).totient : ℂ)) =
      zetaWN (W * N) (1 + logZ ξ x) * ((1 : ℂ) + ξ * Complex.I) * (N : ℂ) /
        ((((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ)) * (N.totient : ℂ)) := by
  calc
    zetaWN (W * N) (1 + logZ ξ x) * logZ ξ x * (((W * N : ℕ) : ℂ) / ((W * N).totient : ℂ))
        = zetaWN (W * N) (1 + logZ ξ x) *
            (logZ ξ x * (((W * N : ℕ) : ℂ) / ((W * N).totient : ℂ))) := by ring
    _ = zetaWN (W * N) (1 + logZ ξ x) * (((1 : ℂ) + ξ * Complex.I) * (N : ℂ) /
          ((((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ)) * (N.totient : ℂ))) := by
            rw [logZ_scalar_identity W N hW hN hcop ξ x hlog]
    _ = zetaWN (W * N) (1 + logZ ξ x) * ((1 : ℂ) + ξ * Complex.I) * (N : ℂ) /
          ((((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ)) * (N.totient : ℂ)) := by ring



lemma logZ_norm_le_ratio (ξ : ℝ) (x : ℕ) (hxi : |ξ| ≤ Real.sqrt (Real.log (x : ℝ)))
    (h1 : 1 ≤ Real.log (x : ℝ)) :
    ‖logZ ξ x‖ ≤ (1 + Real.sqrt (Real.log (x : ℝ))) / Real.log (x : ℝ) := by
  dsimp [logZ]
  have hL0 : 0 < Real.log (x : ℝ) := by linarith
  have hnormL : ‖(Real.log (x : ℝ) : ℂ)‖ = Real.log (x : ℝ) := by
    have hn : ‖(Real.log (x : ℝ) : ℂ)‖ = |Real.log (x : ℝ)| := by
      let y : ℝ := Real.log (x : ℝ)
      have hy : ‖(y : ℂ)‖ = |y| := by simp
      simpa [y] using hy
    rw [hn, abs_of_nonneg hL0.le]
  have hdiv : ‖(((1 : ℂ) + ξ * Complex.I) / (Real.log (x : ℝ) : ℂ))‖ =
      ‖((1 : ℂ) + ξ * Complex.I)‖ / Real.log (x : ℝ) := by
    rw [norm_div, hnormL]
  rw [hdiv]
  have hc : ‖((1 : ℂ) + ξ * Complex.I)‖ ≤ 1 + Real.sqrt (Real.log (x : ℝ)) := by
    have h1n := norm_add_le (1 : ℂ) (ξ * Complex.I)
    have h1n' : ‖(1 : ℂ) + ξ * Complex.I‖ ≤ 1 + ‖ξ * Complex.I‖ := by
      simpa using h1n
    have h3 : ‖ξ * Complex.I‖ ≤ |ξ| := by
      have hmul : ‖ξ * Complex.I‖ = |ξ| * ‖Complex.I‖ := by
        rw [norm_mul]
        simp
      rw [hmul]
      simp
    nlinarith [h1n', h3, hxi]
  exact div_le_div_of_nonneg_right hc hL0.le

lemma logZ_norm_le_sum_inv (ξ : ℝ) (x : ℕ) (hxi : |ξ| ≤ Real.sqrt (Real.log (x : ℝ)))
    (h1 : 1 ≤ Real.log (x : ℝ)) :
    ‖logZ ξ x‖ ≤ (Real.log (x : ℝ))⁻¹ + (Real.sqrt (Real.log (x : ℝ)))⁻¹ := by
  have hL0 : 0 < Real.log (x : ℝ) := by linarith
  have hr := logZ_norm_le_ratio ξ x hxi h1
  have hfrac : (1 + Real.sqrt (Real.log (x : ℝ))) / Real.log (x : ℝ) =
      (Real.log (x : ℝ))⁻¹ + (Real.sqrt (Real.log (x : ℝ)))⁻¹ := by
    have hrt : Real.sqrt (Real.log (x : ℝ)) ≠ 0 := (Real.sqrt_pos.2 hL0).ne'
    have hL : Real.log (x : ℝ) ≠ 0 := hL0.ne'
    field_simp [hL, hrt]
    ring_nf
    rw [Real.sq_sqrt hL0.le]
  rwa [← hfrac]

lemma sum_inv_le_delta {δ L : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2)
    (hL1 : 1 ≤ L) (hLδ : (2 / δ) ^ 2 ≤ L) : L⁻¹ + (Real.sqrt L)⁻¹ ≤ δ := by
  have hL0 : 0 < L := by linarith
  have hA0 : 0 ≤ 2 / δ := by positivity
  have hApos : 0 < 2 / δ := by positivity
  have h4 : (4 : ℝ) ≤ 2 / δ := by
    rw [le_div_iff₀ hδ0]
    nlinarith [hδ12]
  have hA1 : 1 ≤ 2 / δ := by linarith
  have hA_le_A2 : 2 / δ ≤ (2 / δ) ^ 2 := by
    simpa [pow_two] using (mul_le_mul_of_nonneg_left hA1 hA0)
  have hA_le_L : 2 / δ ≤ L := le_trans hA_le_A2 hLδ
  have hδ2 : (δ / 2 : ℝ) = (2 / δ)⁻¹ := by
    field_simp [hδ0.ne']
  have h1inv : L⁻¹ ≤ δ / 2 := by
    have hinv : L⁻¹ ≤ (2 / δ)⁻¹ := (inv_le_inv₀ hL0 hApos).mpr hA_le_L
    rwa [hδ2]
  have hsqrtA : 2 / δ ≤ Real.sqrt L := by
    have hsqrt_sq : Real.sqrt ((2 / δ) ^ 2) = 2 / δ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hA0]
    rw [← hsqrt_sq]
    exact Real.sqrt_le_sqrt hLδ
  have h2inv : (Real.sqrt L)⁻¹ ≤ δ / 2 := by
    have hsqrt_pos : 0 < Real.sqrt L := Real.sqrt_pos.2 hL0
    have hinv : (Real.sqrt L)⁻¹ ≤ (2 / δ)⁻¹ := (inv_le_inv₀ hsqrt_pos hApos).mpr hsqrtA
    rwa [hδ2]
  nlinarith [h1inv, h2inv]

/-- **Input (a) of the ξ-truncation, closed:** the family hypothesis
`UniformPoleAsymptotic W N` (P8 (41) uniform over `|ξ| ≤ √(log x)`) holds for
every coprime `W, N ≠ 0`.  Composition: rcases
`zetaWN_residue_uniform_local (W·N)` with `δq ≤ 1/2`; take
`M := max 1 ((2/δq)²)`, `x₀ := ⌈exp M⌉ + 1`,
`ε(x) := Cq·((log x)⁻¹ + (√(log x))⁻¹)` (`→ 0`); for `x ≥ x₀` and
`|ξ| ≤ √(log x)` bound `‖logZ ξ x‖ ≤ (log x)⁻¹ + (√(log x))⁻¹ ≤ δq`
(`logZ_norm_le_sum_inv` from the norm-division ratio bound, then
`sum_inv_le_delta` from `(2/δq)² ≤ log x`), apply the residue bound
`≤ Cq·‖logZ ξ x‖ ≤ ε x`, and rewrite through `zetaWN_residue_expr_eq` into
the `UniformPoleAsymptotic` expression. -/
theorem uniformPoleAsymptotic_of_residue (W N : ℕ) (hW : W ≠ 0) (hN : N ≠ 0)
    (hcop : W.Coprime N) : UniformPoleAsymptotic W N := by
  classical
  rcases zetaWN_residue_uniform_local (W * N) (mul_ne_zero hW hN) with ⟨Cq, hCq0, δq, hδq0, hδq12, hδres⟩
  let M : ℝ := max 1 ((2 / δq) ^ 2)
  let x₀ : ℕ := Nat.ceil (Real.exp M) + 1
  let ε : ℕ → ℝ := fun x : ℕ => Cq * ((Real.log (x : ℝ))⁻¹ + (Real.sqrt (Real.log (x : ℝ)))⁻¹)
  have hM1 : 1 ≤ M := by dsimp [M]; exact le_max_left _ _
  have hM2 : (2 / δq) ^ 2 ≤ M := by dsimp [M]; exact le_max_right _ _
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
    simpa using (Tendsto.const_mul Cq (h1o.add h2o))
  refine ⟨x₀, ε, hε0, ?_⟩
  intro x hxx ξ hxi
  have hxexp : Real.exp M < (x : ℝ) := by
    have h1 : Real.exp M < ((Nat.ceil (Real.exp M) + 1 : ℕ) : ℝ) := by
      have h1' : Real.exp M ≤ (Nat.ceil (Real.exp M) : ℕ) := Nat.le_ceil (Real.exp M)
      have h2 : ((Nat.ceil (Real.exp M) : ℕ) : ℝ) < ((Nat.ceil (Real.exp M) + 1 : ℕ) : ℝ) := by norm_num
      exact h1'.trans_lt h2
    have hle : ((Nat.ceil (Real.exp M) + 1 : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxx
    exact h1.trans_le hle
  have hlogM : M ≤ Real.log (x : ℝ) := by
    have hm := Real.log_lt_log (Real.exp_pos M) hxexp
    have : M < Real.log (x : ℝ) := by simpa [Real.log_exp] using hm
    exact le_of_lt this
  have hlog1 : 1 ≤ Real.log (x : ℝ) := le_trans hM1 hlogM
  have htpos : 0 < Real.log (x : ℝ) := by linarith
  have hlogδ : (2 / δq) ^ 2 ≤ Real.log (x : ℝ) := le_trans hM2 hlogM
  have hc0 : ((1 : ℂ) + ξ * Complex.I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re] at hre
  have hlogC : (Real.log (x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
  have hz0 : logZ ξ x ≠ 0 := by
    dsimp [logZ]
    exact div_ne_zero hc0 hlogC
  have hnz : ‖logZ ξ x‖ ≤ (Real.log (x : ℝ))⁻¹ + (Real.sqrt (Real.log (x : ℝ)))⁻¹ :=
    logZ_norm_le_sum_inv ξ x hxi hlog1
  have hzδ : ‖logZ ξ x‖ ≤ δq :=
    hnz.trans (sum_inv_le_delta hδq0 hδq12 hlog1 hlogδ)
  have hb0 := hδres (logZ ξ x) hz0 hzδ
  have hEq := zetaWN_residue_expr_eq W N hW hN hcop ξ x htpos.ne'
  have hb : ‖zetaWN (W * N) (1 + logZ ξ x) * ((1 : ℂ) + ξ * Complex.I) * (N : ℂ) /
        ((((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ)) * (N.totient : ℂ)) - 1‖ ≤
      Cq * ‖logZ ξ x‖ := by
    rw [← hEq]
    exact hb0
  have hCm : Cq * ‖logZ ξ x‖ ≤ ε x := by
    dsimp [ε]
    exact mul_le_mul_of_nonneg_left hnz (le_of_lt hCq0)
  exact hb.trans hCm

end Commons.NumberTheory.MaynardSieve
