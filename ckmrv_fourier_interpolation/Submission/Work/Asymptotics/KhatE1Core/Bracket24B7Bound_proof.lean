import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Bracket24BCoeffs

/-!
# The `E(z)^7`-coefficient bound `Bracket24B7Bound`

The coefficient `Bracket24B7` of `Sh τ z · Bracket24 ℓ τ z` (module
`Submission.Work.Asymptotics.KhatE1Core.Bracket24BCoeffs`) is a `τ`-only combination of the
`j(τ)`-monomials

  `Δ j⁰, Δ j¹, Δ j²,  E₄E₆ψ₂ j⁰, E₄E₆ψ₂ j¹, E₄E₆ψ₂ j²,  E₄²ψ₄ j⁰, E₄²ψ₄ j¹, E₄²ψ₄ j²`.

Since `‖j(τ)‖ ≍ ‖q(τ)‖⁻¹` on the funnel, the two `j²`-monomials in `ψ₂`, `ψ₄` are *a priori*
one power of `‖q‖` too big.  The whole point of the coefficient is that they are not: the
combination `2016Δ − (7/4)E₄E₆ψ₂ + (7/4)E₄²ψ₄ = 2016Δ + (7/4)(ψ₄E₈ − ψ₂E₁₀)` is the
near-identity of `psi4E8_sub_psi2E10_funnel`, i.e. is `O(‖q(τ)‖ (scale τ)^N)`, which cancels
one of the two `‖q‖⁻¹`-factors coming from `j²` exactly.

So the coefficient is organised as

  `B₇ = π⁻¹ ( Δ(c₀ + c₁ j) + E₄E₆ψ₂(d₀ + d₁ j) + E₄²ψ₄(e₀ + e₁ j)
              + j² (2016Δ + (7/4)(ψ₄E₈ − ψ₂E₁₀)) )`,

and each of the four groups satisfies a bound `C ‖q‖^n (scale τ)^N (1+t)^M` with `n ≥ −1`,
with the last group using `‖j²‖ ≤ C‖q‖⁻²` against the `O(‖q‖)` near-identity.

The relevant bookkeeping is a variant `BoundQ` of the `Bound` calculus of
`KhatE1/Bracket24E2_defs` in which the `‖q‖`-exponent is an *integer* (so that `‖q‖⁻¹` and
`‖q‖⁻²` are allowed), and the atom bounds are those already proved in the workspace
(`DeltaFun_funnel_le`, `E4_funnel_bounds`, `Funnel24.norm_E6_funnel`, `psi_scale_funnel`,
`Funnel24.norm_j_funnel`, `psi4E8_sub_psi2E10_funnel`).
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-- Bounds of the shape `C · ‖q(τ)‖^n · (scale τ)^N · (1+t)^M` on the funnel strip, with
*integer* exponent `n` (so that `j(τ)`-atoms of size `‖q‖⁻¹` are admissible). -/
def BoundQ (f : UpperHalfPlane → UpperHalfPlane → ℂ) (n : ℤ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
      0 ≤ z.re → z.re ≤ 1 → z.im = t →
      ‖f τ z‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N
        * (1 + t) ^ M

section Basic

variable {τ z : UpperHalfPlane} {t : ℝ}

lemma one_le_one_add_t' (hτ : Work.Asymptotics.Funnel τ) (ht : τ.im + 1 ≤ t) :
    (1 : ℝ) ≤ 1 + t := by
  have := hτ.2; linarith

lemma norm_q_le_one' (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Kernels.qParamFun τ‖ ≤ 1 := by
  rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
  nlinarith [Real.pi_pos, hτ.2]

lemma norm_q_pos' (τ : UpperHalfPlane) : 0 < ‖Work.Kernels.qParamFun τ‖ :=
  norm_pos_iff.mpr (Work.Asymptotics.qParamFun_ne_zero' τ)

/-- For `0 < a ≤ 1`, the map `n ↦ a^n` is antitone. -/
lemma zpow_le_zpow_of_le_one {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {m n : ℤ}
    (h : n ≤ m) : a ^ m ≤ a ^ n := by
  have h1 : 1 ≤ a⁻¹ := (one_le_inv₀ ha0).mpr ha1
  have h2 := zpow_le_zpow_right₀ (a := a⁻¹) h1 (show -m ≤ -n by omega)
  simpa only [inv_zpow, inv_inv, zpow_neg] using h2

/-- Product monotonicity for four nonnegative factors. -/
lemma mul4_le' {a b c d a' b' c' d' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (hd : d ≤ d') (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d) :
    a * b * c * d ≤ a' * b' * c' * d' := by
  have hb' : 0 ≤ b' := le_trans hb0 hb
  have hd' : 0 ≤ d' := le_trans hd0 hd
  have h1' : a * b ≤ a' * b' := mul_le_mul ha hb hb0 (le_trans ha0 ha)
  have h2' : c * d ≤ c' * d' := mul_le_mul hc hd hd0 (le_trans hc0 hc)
  calc a * b * c * d = (a * b) * (c * d) := by ring
    _ ≤ (a' * b') * (c' * d') := mul_le_mul h1' h2' (mul_nonneg hc0 hd0)
        (mul_nonneg (le_trans ha0 ha) hb')
    _ = a' * b' * c' * d' := by ring

end Basic

/-! ## The `BoundQ` calculus -/

section Calculus

theorem BoundQ.congr {f g : UpperHalfPlane → UpperHalfPlane → ℂ} {n : ℤ} (h : BoundQ f n)
    (hfg : ∀ τ z, f τ z = g τ z) : BoundQ g n := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  exact ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => by
    rw [← hfg τ z]; exact hb τ z t hF ht hz0 hz1 hzim⟩

theorem BoundQ.mono {f : UpperHalfPlane → UpperHalfPlane → ℂ} {n m : ℤ} (h : m ≤ n)
    (hf : BoundQ f n) : BoundQ f m := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := hf
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hq0 : 0 < ‖Work.Kernels.qParamFun τ‖ := norm_q_pos' τ
  have hqn : ‖Work.Kernels.qParamFun τ‖ ^ n ≤ ‖Work.Kernels.qParamFun τ‖ ^ m :=
    zpow_le_zpow_of_le_one hq0 (norm_q_le_one' hF) h
  refine le_trans (hb τ z t hF ht hz0 hz1 hzim) ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hqn hC.le)
    (Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N))
    (Real.rpow_nonneg (le_trans zero_le_one (one_le_one_add_t' hF ht)) M)

theorem BoundQ.add {f g : UpperHalfPlane → UpperHalfPlane → ℂ} {m n : ℤ}
    (hf : BoundQ f m) (hg : BoundQ g n) :
    BoundQ (fun τ z => f τ z + g τ z) (min m n) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb1⟩ := hf
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hg
  refine ⟨C1 + C2 + 1, max N1 N2, max M1 M2, by linarith, le_trans hN1 (le_max_left _ _),
    le_trans hM1 (le_max_left _ _), fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hq0 : 0 < ‖Work.Kernels.qParamFun τ‖ := norm_q_pos' τ
  have hq1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := norm_q_le_one' hF
  have hs0 : (0:ℝ) ≤ Work.Kernels.scale τ := le_of_lt (Work.Kernels.scale_pos τ)
  have hu0 : (0:ℝ) ≤ 1 + t := le_trans zero_le_one (one_le_one_add_t' hF ht)
  have hA0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ (min m n)
        * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) :=
    mul_nonneg (mul_nonneg (zpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hs0 _))
      (Real.rpow_nonneg hu0 _)
  have e1 : ‖f τ z‖ ≤ C1 * (‖Work.Kernels.qParamFun τ‖ ^ (min m n)
        * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)) := by
    refine le_trans (hb1 τ z t hF ht hz0 hz1 hzim) ?_
    calc C1 * ‖Work.Kernels.qParamFun τ‖ ^ m * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
        ≤ C1 * ‖Work.Kernels.qParamFun τ‖ ^ (min m n) * (Work.Kernels.scale τ) ^ (max N1 N2)
            * (1 + t) ^ (max M1 M2) :=
          mul4_le' (le_refl C1)
            (zpow_le_zpow_of_le_one hq0 hq1 (min_le_left _ _))
            (Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ) (le_max_left _ _))
            (Real.rpow_le_rpow_of_exponent_le (one_le_one_add_t' hF ht) (le_max_left _ _))
            hC1.le (zpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hs0 _)
            (Real.rpow_nonneg hu0 _)
      _ = C1 * (‖Work.Kernels.qParamFun τ‖ ^ (min m n)
            * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)) := by ring
  have e2 : ‖g τ z‖ ≤ C2 * (‖Work.Kernels.qParamFun τ‖ ^ (min m n)
        * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)) := by
    refine le_trans (hb2 τ z t hF ht hz0 hz1 hzim) ?_
    calc C2 * ‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2
        ≤ C2 * ‖Work.Kernels.qParamFun τ‖ ^ (min m n) * (Work.Kernels.scale τ) ^ (max N1 N2)
            * (1 + t) ^ (max M1 M2) :=
          mul4_le' (le_refl C2)
            (zpow_le_zpow_of_le_one hq0 hq1 (min_le_right _ _))
            (Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ) (le_max_right _ _))
            (Real.rpow_le_rpow_of_exponent_le (one_le_one_add_t' hF ht) (le_max_right _ _))
            hC2.le (zpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hs0 _)
            (Real.rpow_nonneg hu0 _)
      _ = C2 * (‖Work.Kernels.qParamFun τ‖ ^ (min m n)
            * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)) := by ring
  refine le_trans (le_trans (norm_add_le _ _) (add_le_add e1 e2)) ?_
  calc C1 * (‖Work.Kernels.qParamFun τ‖ ^ (min m n) * (Work.Kernels.scale τ) ^ (max N1 N2)
          * (1 + t) ^ (max M1 M2))
        + C2 * (‖Work.Kernels.qParamFun τ‖ ^ (min m n) * (Work.Kernels.scale τ) ^ (max N1 N2)
          * (1 + t) ^ (max M1 M2))
      = (C1 + C2) * (‖Work.Kernels.qParamFun τ‖ ^ (min m n)
          * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)) := by ring
    _ ≤ (C1 + C2 + 1) * (‖Work.Kernels.qParamFun τ‖ ^ (min m n)
          * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)) :=
        mul_le_mul_of_nonneg_right (by linarith) hA0
    _ = (C1 + C2 + 1) * ‖Work.Kernels.qParamFun τ‖ ^ (min m n)
          * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) := by ring

theorem BoundQ.mul {f g : UpperHalfPlane → UpperHalfPlane → ℂ} {m n : ℤ}
    (hf : BoundQ f m) (hg : BoundQ g n) :
    BoundQ (fun τ z => f τ z * g τ z) (m + n) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb1⟩ := hf
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hg
  refine ⟨C1 * C2, N1 + N2, M1 + M2, mul_pos hC1 hC2, add_nonneg hN1 hN2, add_nonneg hM1 hM2,
    fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hq0 : 0 < ‖Work.Kernels.qParamFun τ‖ := norm_q_pos' τ
  have hqne : ‖Work.Kernels.qParamFun τ‖ ≠ 0 := ne_of_gt hq0
  have hS0 : 0 < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  have hU0 : 0 < 1 + t := lt_of_lt_of_le one_pos (one_le_one_add_t' hF ht)
  have hkey : (C1 * ‖Work.Kernels.qParamFun τ‖ ^ m * (Work.Kernels.scale τ) ^ N1
        * (1 + t) ^ M1)
      * (C2 * ‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2)
      = C1 * C2 * ‖Work.Kernels.qParamFun τ‖ ^ (m + n)
        * (Work.Kernels.scale τ) ^ (N1 + N2) * (1 + t) ^ (M1 + M2) := by
    rw [zpow_add₀ hqne, Real.rpow_add hS0, Real.rpow_add hU0]; ring
  rw [norm_mul]
  calc ‖f τ z‖ * ‖g τ z‖
      ≤ (C1 * ‖Work.Kernels.qParamFun τ‖ ^ m * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1)
        * (C2 * ‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N2
            * (1 + t) ^ M2) :=
        mul_le_mul (hb1 τ z t hF ht hz0 hz1 hzim) (hb2 τ z t hF ht hz0 hz1 hzim)
          (norm_nonneg _)
          (mul_nonneg (mul_nonneg (mul_nonneg hC1.le (zpow_nonneg (norm_nonneg _) _))
            (Real.rpow_nonneg (le_of_lt hS0) _)) (Real.rpow_nonneg (le_of_lt hU0) _))
    _ = C1 * C2 * ‖Work.Kernels.qParamFun τ‖ ^ (m + n)
        * (Work.Kernels.scale τ) ^ (N1 + N2) * (1 + t) ^ (M1 + M2) := hkey

theorem BoundQ.const_mul (c : ℂ) {f : UpperHalfPlane → UpperHalfPlane → ℂ} {n : ℤ}
    (hf : BoundQ f n) : BoundQ (fun τ z => c * f τ z) n := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := hf
  refine ⟨‖c‖ * C + 1, N, M, by positivity, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hQ0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ n := zpow_nonneg (norm_nonneg _) n
  have hS0 : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ N :=
    Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N
  have hU0 : (0:ℝ) ≤ (1 + t) ^ M :=
    Real.rpow_nonneg (le_trans zero_le_one (one_le_one_add_t' hF ht)) M
  rw [norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_left (hb τ z t hF ht hz0 hz1 hzim) (norm_nonneg _)) ?_
  calc ‖c‖ * (C * ‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
      = (‖c‖ * C) * (‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N
          * (1 + t) ^ M) := by ring
    _ ≤ (‖c‖ * C + 1) * (‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N
          * (1 + t) ^ M) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (mul_nonneg hQ0 hS0) hU0)
    _ = (‖c‖ * C + 1) * ‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N
          * (1 + t) ^ M := by ring

theorem BoundQ.const (c : ℂ) : BoundQ (fun _ _ => c) 0 := by
  refine ⟨‖c‖ + 1, 0, 0, by positivity, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  rw [zpow_zero, Real.rpow_zero, Real.rpow_zero, mul_one, mul_one, mul_one]
  linarith [norm_nonneg c]

end Calculus

/-! ## The atom bounds on the funnel -/

section Atoms

theorem BoundQ.DeltaFun :
    BoundQ (fun τ _ => Work.Kernels.DeltaFun τ) 1 := by
  refine ⟨2, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h : ‖Work.Kernels.DeltaFun τ‖ ≤ 2 * ‖Work.Kernels.qParamFun τ‖ :=
    Work.Asymptotics.DeltaFun_funnel_le τ hF
  simpa only [zpow_one, Real.rpow_zero, mul_one] using h

theorem BoundQ.E4Fun : BoundQ (fun τ _ => Work.Kernels.E4Fun τ) 0 := by
  refine ⟨3 / 2, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h : ‖Work.Kernels.E4Fun τ‖ ≤ 3 / 2 := (Work.FunnelNumerics.E4_funnel_bounds).1 τ hF
  simpa only [zpow_zero, Real.rpow_zero, mul_one] using h

theorem BoundQ.E6Fun : BoundQ (fun τ _ => Work.Kernels.E6Fun τ) 0 := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.Funnel24.norm_E6_funnel
  exact ⟨C, 0, 0, hC, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim =>
    by simpa only [zpow_zero, Real.rpow_zero, mul_one] using hb τ hF⟩

theorem BoundQ.psi2 (ℓ : Work.Kernels.LogLambdaData) :
    BoundQ (fun τ _ => Work.Kernels.psi2 ℓ τ) 0 := by
  obtain ⟨C, N, hC, hN, hb⟩ := Work.Asymptotics.psi_scale_funnel ℓ
  exact ⟨C, N, 0, hC, hN, le_rfl, fun τ z t hF ht hz0 hz1 hzim =>
    by simpa only [zpow_zero, Real.rpow_zero, mul_one] using (hb τ hF).1⟩

theorem BoundQ.psi4 (ℓ : Work.Kernels.LogLambdaData) :
    BoundQ (fun τ _ => Work.Kernels.psi4 ℓ τ) 0 := by
  obtain ⟨C, N, hC, hN, hb⟩ := Work.Asymptotics.psi_scale_funnel ℓ
  exact ⟨C, N, 0, hC, hN, le_rfl, fun τ z t hF ht hz0 hz1 hzim =>
    by simpa only [zpow_zero, Real.rpow_zero, mul_one] using (hb τ hF).2⟩

theorem BoundQ.jInvariantFun :
    BoundQ (fun τ _ => Work.Kernels.jInvariantFun τ) (-1) := by
  refine ⟨27 / 4, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h : ‖Work.Kernels.jInvariantFun τ‖ ≤ 27 / 4 * Real.exp (2 * Real.pi * τ.im) :=
    Work.Asymptotics.Funnel24.norm_j_funnel τ hF
  have hq : ‖Work.Kernels.qParamFun τ‖ ^ (-1 : ℤ) = Real.exp (2 * Real.pi * τ.im) := by
    rw [zpow_neg_one, Work.Asymptotics.norm_qParamFun, ← Real.exp_neg, neg_neg]
  simpa only [hq, Real.rpow_zero, mul_one] using h

/-- `ψ₄E₈ − ψ₂E₁₀ = O(‖q(τ)‖ scale^N)` on the funnel (`psi4E8_sub_psi2E10_funnel`). -/
theorem BoundQ.theta24 (ℓ : Work.Kernels.LogLambdaData) :
    BoundQ (fun τ _ => Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
      - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ) 1 := by
  obtain ⟨C, N, hC, hN, hb⟩ := Work.Asymptotics.psi4E8_sub_psi2E10_funnel ℓ
  refine ⟨C, N, 0, hC, hN, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h := hb τ hF
  have heq : C * ‖Work.Kernels.qParamFun τ‖ ^ (1 : ℤ) * (Work.Kernels.scale τ) ^ N
        * (1 + t) ^ (0 : ℝ) = C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ := by
    rw [zpow_one, Real.rpow_zero, mul_one]; ring
  rw [heq]
  exact h

end Atoms

/-! ## The main bound -/

/-- **`Bracket24B7Bound`.** -/
theorem Bracket24B7Bound_proof (ℓ : Work.Kernels.LogLambdaData) :
    Work.Asymptotics.KhatE1Core.Bracket24B7Bound ℓ := by
  have hG1 : BoundQ (fun τ _ => Work.Kernels.DeltaFun τ *
      ((3260696276992 / 45 : ℂ) + (-137141696 : ℂ) * Work.Kernels.jInvariantFun τ)) (-1) := by
    have hΔ : BoundQ (fun τ _ => Work.Kernels.DeltaFun τ) 1 := BoundQ.DeltaFun
    have h1 : BoundQ (fun _ _ => (3260696276992 / 45 : ℂ)) 0 := BoundQ.const _
    have h2 : BoundQ (fun τ _ => (-137141696 : ℂ) * Work.Kernels.jInvariantFun τ) (-1) :=
      BoundQ.const_mul _ BoundQ.jInvariantFun
    have h3 : BoundQ (fun τ _ => (3260696276992 / 45 : ℂ)
        + (-137141696 : ℂ) * Work.Kernels.jInvariantFun τ) (-1) :=
      (h1.add h2).mono (le_min (by norm_num) le_rfl)
    exact (hΔ.mul h3).mono (by norm_num)
  have hG2 : BoundQ (fun τ _ =>
      (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.psi2 ℓ τ) *
      ((-68654784 : ℂ) + (2139479 / 18 : ℂ) * Work.Kernels.jInvariantFun τ)) (-1) := by
    have h4 : BoundQ (fun τ _ => Work.Kernels.E4Fun τ) 0 := BoundQ.E4Fun
    have h6 : BoundQ (fun τ _ => Work.Kernels.E6Fun τ) 0 := BoundQ.E6Fun
    have hp : BoundQ (fun τ _ => Work.Kernels.psi2 ℓ τ) 0 := BoundQ.psi2 ℓ
    have h46 : BoundQ (fun τ _ => Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ) 0 :=
      (h4.mul h6).mono (le_min le_rfl le_rfl)
    have hE : BoundQ (fun τ _ =>
        Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.psi2 ℓ τ) 0 :=
      (h46.mul hp).mono (le_min le_rfl le_rfl)
    have h1 : BoundQ (fun _ _ => (-68654784 : ℂ)) 0 := BoundQ.const _
    have h2 : BoundQ (fun τ _ => (2139479 / 18 : ℂ) * Work.Kernels.jInvariantFun τ) (-1) :=
      BoundQ.const_mul _ BoundQ.jInvariantFun
    have h3 : BoundQ (fun τ _ => (-68654784 : ℂ)
        + (2139479 / 18 : ℂ) * Work.Kernels.jInvariantFun τ) (-1) :=
      (h1.add h2).mono (le_min (by norm_num) le_rfl)
    exact (hE.mul h3).mono (by norm_num)
  have hG3 : BoundQ (fun τ _ =>
      (Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.psi4 ℓ τ) *
      ((136472992 : ℂ) + (-2157623 / 18 : ℂ) * Work.Kernels.jInvariantFun τ)) (-1) := by
    have h4 : BoundQ (fun τ _ => Work.Kernels.E4Fun τ) 0 := BoundQ.E4Fun
    have hp : BoundQ (fun τ _ => Work.Kernels.psi4 ℓ τ) 0 := BoundQ.psi4 ℓ
    have h44 : BoundQ (fun τ _ => Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ) 0 :=
      (h4.mul h4).mono (le_min le_rfl le_rfl)
    have hE : BoundQ (fun τ _ =>
        Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.psi4 ℓ τ) 0 :=
      (h44.mul hp).mono (le_min le_rfl le_rfl)
    have h1 : BoundQ (fun _ _ => (136472992 : ℂ)) 0 := BoundQ.const _
    have h2 : BoundQ (fun τ _ => (-2157623 / 18 : ℂ) * Work.Kernels.jInvariantFun τ) (-1) :=
      BoundQ.const_mul _ BoundQ.jInvariantFun
    have h3 : BoundQ (fun τ _ => (136472992 : ℂ)
        + (-2157623 / 18 : ℂ) * Work.Kernels.jInvariantFun τ) (-1) :=
      (h1.add h2).mono (le_min (by norm_num) le_rfl)
    exact (hE.mul h3).mono (by norm_num)
  have hG4 : BoundQ (fun τ _ =>
      (Work.Kernels.jInvariantFun τ * Work.Kernels.jInvariantFun τ) *
      ((2016 : ℂ) * Work.Kernels.DeltaFun τ + (7 / 4 : ℂ) *
        (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
          - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ))) (-1) := by
    have hj : BoundQ (fun τ _ => Work.Kernels.jInvariantFun τ) (-1) := BoundQ.jInvariantFun
    have hj2 : BoundQ (fun τ _ =>
        Work.Kernels.jInvariantFun τ * Work.Kernels.jInvariantFun τ) (-2) :=
      (hj.mul hj).mono (by norm_num)
    have hΔ : BoundQ (fun τ _ => Work.Kernels.DeltaFun τ) 1 := BoundQ.DeltaFun
    have hD : BoundQ (fun τ _ => (2016 : ℂ) * Work.Kernels.DeltaFun τ) 1 :=
      BoundQ.const_mul _ hΔ
    have hT : BoundQ (fun τ _ => (7 / 4 : ℂ) *
        (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
          - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)) 1 :=
      BoundQ.const_mul _ (BoundQ.theta24 ℓ)
    have hin : BoundQ (fun τ _ =>
        (2016 : ℂ) * Work.Kernels.DeltaFun τ + (7 / 4 : ℂ) *
          (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
            - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)) 1 :=
      (hD.add hT).mono (le_min le_rfl le_rfl)
    exact (hj2.mul hin).mono (by norm_num)
  have hsum : BoundQ (fun τ z =>
      (Work.Kernels.DeltaFun τ *
          ((3260696276992 / 45 : ℂ) + (-137141696 : ℂ) * Work.Kernels.jInvariantFun τ))
      + ((Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.psi2 ℓ τ) *
          ((-68654784 : ℂ) + (2139479 / 18 : ℂ) * Work.Kernels.jInvariantFun τ))
      + ((Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.psi4 ℓ τ) *
          ((136472992 : ℂ) + (-2157623 / 18 : ℂ) * Work.Kernels.jInvariantFun τ))
      + ((Work.Kernels.jInvariantFun τ * Work.Kernels.jInvariantFun τ) *
          ((2016 : ℂ) * Work.Kernels.DeltaFun τ + (7 / 4 : ℂ) *
            (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
              - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)))) (-1) :=
    (((hG1.add hG2).add hG3).add hG4).mono
      (le_min (le_min (le_min le_rfl le_rfl) le_rfl) le_rfl)
  have hfinal : BoundQ (fun τ z => ((Real.pi : ℂ)) ^ (-1 : ℤ) *
      ((Work.Kernels.DeltaFun τ *
          ((3260696276992 / 45 : ℂ) + (-137141696 : ℂ) * Work.Kernels.jInvariantFun τ))
      + ((Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.psi2 ℓ τ) *
          ((-68654784 : ℂ) + (2139479 / 18 : ℂ) * Work.Kernels.jInvariantFun τ))
      + ((Work.Kernels.E4Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.psi4 ℓ τ) *
          ((136472992 : ℂ) + (-2157623 / 18 : ℂ) * Work.Kernels.jInvariantFun τ))
      + ((Work.Kernels.jInvariantFun τ * Work.Kernels.jInvariantFun τ) *
          ((2016 : ℂ) * Work.Kernels.DeltaFun τ + (7 / 4 : ℂ) *
            (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
              - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ))))) (-1) :=
    BoundQ.const_mul _ hsum
  have hmain : BoundQ (fun τ z => Bracket24B7 ℓ τ z) (-1) :=
    hfinal.congr (fun τ z => by
      simp only [Bracket24B7, Work.Kernels.E8Fun, Work.Kernels.E10Fun]
      ring)
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := hmain
  exact ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => by
    have h := hb τ z t hF ht hz0 hz1 hzim
    rwa [zpow_neg_one] at h⟩

end

end Work.Asymptotics.KhatE1Core
