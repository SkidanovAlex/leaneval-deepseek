import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.KdevA4
import Submission.Work.Asymptotics.KhatE1Core.KdevA4j
import Submission.Work.Asymptotics.KhatE1.KdevA4Book
import Submission.Work.Asymptotics.KhatE1.KdevA4plusBound
import Submission.Work.Asymptotics.KhatE1Core.E1combo8_second_order
import Submission.Work.Asymptotics.KhatE1Core.psi_second_order
import Submission.Work.Asymptotics.KhatE1Core.jq_second_order
import Submission.Work.Asymptotics.KhatE1.E1combo8FirstOrderBound
import Submission.Work.Asymptotics.KhatE1Core.KdevA4j0_bound

set_option maxHeartbeats 4000000

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-!
# The sharp funnel bound for the `E(z)^4`-coefficient `KdevA4`

`KdevA4 = (3456π)⁻¹·KdevA4num` is the `E(z)^4`-coefficient of the sharp funnel residual
(`KhatE1Core/KdevA4.lean`).  The goal of this file is the funnel estimate

  `‖KdevA4 ℓ τ z‖ ≤ C (scale τ)^N (1+t)^M`   (`Funnel τ`, `-1 ≤ z.re ≤ 2`, `z.im = t ≥ τ.im+1`).

The proof proceeds by the `j`-decomposition `KdevA4num = A₂j² + A₁j + A₀` of
`KhatE1Core/KdevA4j.lean` (`j = jInvariantFun τ`).  With `q = qParamFun τ` and `jq = j·q`
bounded on the funnel, 

  `KdevA4num = q⁻²·[(jq)²(A₂ + qA₁) + q(jq)(1 - jq)A₁ + q²A₀]`,

so it suffices that `A₂ + qA₁ = O((scale τ)^N(1+‖z‖)^M ‖q‖²)`, `A₁,A₀ = O(...)`.  The first
of these is the sharp cancellation of the `e⁴`-coefficient: with the second-order cusp
expansions of `E₂,E₄,E₆,ψ₂,ψ₄` the combination `A₂ + qA₁` has vanishing `q⁰`- and
`q¹`-coefficients (verified symbolically), and the residual is an explicit polynomial.

Everything is organised through the two-variable calculus `BigZ k F`
(`F = O((scale τ)^N (1+‖z‖)^M ‖q‖^k)` on the funnel).
-/

/-! ## §1  The two-variable `O((scale τ)^N (1+‖z‖)^M ‖q‖^k)` calculus -/

/-- `BigZ k F` records that `F τ z = O((scale τ)^N (1 + ‖z‖)^M ‖q(τ)‖^k)` for some `N, M ≥ 0`
and some constant, uniformly on the funnel `Funnel τ` and for all `z`. -/
private def BigZ (k : ℕ) (F : ℍ → ℍ → ℂ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ τ z : ℍ, Work.Asymptotics.Funnel τ →
      ‖F τ z‖ ≤ C * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ M
        * ‖Work.Kernels.qParamFun τ‖ ^ k

private lemma qn_nonneg (τ : ℍ) : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _

private lemma qn_le_one (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Kernels.qParamFun τ‖ ≤ 1 := by
  rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
  have := hτ.2
  nlinarith [Real.pi_pos]

private lemma qn_pow_nonneg (τ : ℍ) (k : ℕ) : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ k :=
  pow_nonneg (qn_nonneg τ) k

private lemma qn_pow_le_one (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) (k : ℕ) :
    ‖Work.Kernels.qParamFun τ‖ ^ k ≤ 1 :=
  pow_le_one₀ (qn_nonneg τ) (qn_le_one τ hτ)

private lemma qn_pow_mono (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) {k l : ℕ} (h : l ≤ k) :
    ‖Work.Kernels.qParamFun τ‖ ^ k ≤ ‖Work.Kernels.qParamFun τ‖ ^ l :=
  pow_le_pow_of_le_one (qn_nonneg τ) (qn_le_one τ hτ) h

private lemma sc_pos (τ : ℍ) : (0 : ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ

private lemma sc_ge_one (τ : ℍ) : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ

private lemma zf_pos (z : ℍ) : (0 : ℝ) < 1 + ‖(z : ℂ)‖ := by positivity

private lemma zf_ge_one (z : ℍ) : (1 : ℝ) ≤ 1 + ‖(z : ℂ)‖ :=
  le_add_of_nonneg_right (norm_nonneg _)

private lemma sc_rpow_nonneg (τ : ℍ) (N : ℝ) :
    (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N := Real.rpow_nonneg (sc_pos τ).le N

private lemma zf_rpow_nonneg (z : ℍ) (M : ℝ) :
    (0 : ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ M := Real.rpow_nonneg (zf_pos z).le M

private lemma sc_rpow_add (τ : ℍ) (N M : ℝ) :
    (Work.Kernels.scale τ) ^ (N + M)
      = (Work.Kernels.scale τ) ^ N * (Work.Kernels.scale τ) ^ M :=
  Real.rpow_add (sc_pos τ) N M

private lemma zf_rpow_add (z : ℍ) (N M : ℝ) :
    (1 + ‖(z : ℂ)‖) ^ (N + M)
      = (1 + ‖(z : ℂ)‖) ^ N * (1 + ‖(z : ℂ)‖) ^ M :=
  Real.rpow_add (zf_pos z) N M

private lemma sc_rpow_le (τ : ℍ) {N N' : ℝ} (h : N ≤ N') :
    (Work.Kernels.scale τ) ^ N ≤ (Work.Kernels.scale τ) ^ N' :=
  Real.rpow_le_rpow_of_exponent_le (sc_ge_one τ) h

private lemma zf_rpow_le (z : ℍ) {M M' : ℝ} (h : M ≤ M') :
    (1 + ‖(z : ℂ)‖) ^ M ≤ (1 + ‖(z : ℂ)‖) ^ M' :=
  Real.rpow_le_rpow_of_exponent_le (zf_ge_one z) h

/-- Product of three monotone bounds. -/
private lemma mul3_le {a b c A B C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : a ≤ A) (h2 : b ≤ B) (h3 : c ≤ C) : a * b * c ≤ A * B * C := by
  have hA : 0 ≤ A := le_trans ha h1
  have hB : 0 ≤ B := le_trans hb h2
  exact mul_le_mul (mul_le_mul h1 h2 hb hA) h3 hc (mul_nonneg hA hB)

/-- Product of four monotone bounds. -/
private lemma mul4_le {a b c d A B C D : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (h1 : a ≤ A) (h2 : b ≤ B) (h3 : c ≤ C) (h4 : d ≤ D) :
    a * b * c * d ≤ A * B * C * D := by
  have hA : 0 ≤ A := le_trans ha h1
  have hB : 0 ≤ B := le_trans hb h2
  have hC : 0 ≤ C := le_trans hc h3
  have h3' : a * b * c ≤ A * B * C := mul3_le ha hb hc h1 h2 h3
  exact mul_le_mul h3' h4 hd (mul_nonneg (mul_nonneg hA hB) hC)

/-- Product of five monotone bounds. -/
private lemma mul5_le {a b c d e A B C D E : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (h1 : a ≤ A) (h2 : b ≤ B) (h3 : c ≤ C) (h4 : d ≤ D)
    (h5 : e ≤ E) : a * b * c * d * e ≤ A * B * C * D * E := by
  have hA : 0 ≤ A := le_trans ha h1
  have hB : 0 ≤ B := le_trans hb h2
  have hC : 0 ≤ C := le_trans hc h3
  have hD : 0 ≤ D := le_trans hd h4
  have h4' : a * b * c * d ≤ A * B * C * D := mul4_le ha hb hc hd h1 h2 h3 h4
  exact mul_le_mul h4' h5 he (mul_nonneg (mul_nonneg (mul_nonneg hA hB) hC) hD)

/-- Monotonicity of the profile `(scale τ)^N (1+‖z‖)^M ‖q‖^k`. -/
private lemma prof_le (τ z : ℍ) (hτ : Work.Asymptotics.Funnel τ) {N N' M M' : ℝ} {k k' : ℕ}
    (hN : N ≤ N') (hM : M ≤ M') (hk : k' ≤ k) :
    (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ M * ‖Work.Kernels.qParamFun τ‖ ^ k
      ≤ (Work.Kernels.scale τ) ^ N' * (1 + ‖(z : ℂ)‖) ^ M'
          * ‖Work.Kernels.qParamFun τ‖ ^ k' :=
  mul3_le (sc_rpow_nonneg τ N) (zf_rpow_nonneg z M) (qn_pow_nonneg τ k)
    (sc_rpow_le τ hN) (zf_rpow_le z hM) (qn_pow_mono τ hτ hk)

private lemma BigZ.mono {k l : ℕ} {F : ℍ → ℍ → ℂ} (h : BigZ k F) (hl : l ≤ k) : BigZ l F := by
  obtain ⟨C, N, M, hC, hN, hM, hF⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun τ z hτ => ?_⟩
  refine le_trans (hF τ z hτ) ?_
  have hp := prof_le τ z hτ (N := N) (N' := N) (M := M) (M' := M) (k := k) (k' := l)
    le_rfl le_rfl hl
  calc C * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ M * ‖Work.Kernels.qParamFun τ‖ ^ k
      = C * ((Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ M
          * ‖Work.Kernels.qParamFun τ‖ ^ k) := by ring
    _ ≤ C * ((Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ M
          * ‖Work.Kernels.qParamFun τ‖ ^ l) :=
        mul_le_mul_of_nonneg_left hp hC.le
    _ = C * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ M
          * ‖Work.Kernels.qParamFun τ‖ ^ l := by ring

private lemma BigZ.congr {k : ℕ} {F G : ℍ → ℍ → ℂ} (h : BigZ k F)
    (hFG : ∀ τ z, F τ z = G τ z) : BigZ k G := by
  obtain ⟨C, N, M, hC, hN, hM, hF⟩ := h
  exact ⟨C, N, M, hC, hN, hM, fun τ z hτ => by rw [← hFG τ z]; exact hF τ z hτ⟩

private lemma BigZ.add {k l : ℕ} {F G : ℍ → ℍ → ℂ} (hF : BigZ k F) (hG : BigZ l G) :
    BigZ (min k l) (fun τ z => F τ z + G τ z) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, h1⟩ := hF
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, h2⟩ := hG
  refine ⟨C1 + C2, N1 + N2, M1 + M2, by linarith, by linarith, by linarith, fun τ z hτ => ?_⟩
  have e1 := h1 τ z hτ
  have e2 := h2 τ z hτ
  have p1 : C1 * (Work.Kernels.scale τ) ^ N1 * (1 + ‖(z : ℂ)‖) ^ M1
        * ‖Work.Kernels.qParamFun τ‖ ^ k
      ≤ C1 * (Work.Kernels.scale τ) ^ (N1 + N2) * (1 + ‖(z : ℂ)‖) ^ (M1 + M2)
        * ‖Work.Kernels.qParamFun τ‖ ^ (min k l) := by
    have hp := prof_le τ z hτ (N := N1) (N' := N1 + N2) (M := M1) (M' := M1 + M2)
      (k := k) (k' := min k l) (by linarith) (by linarith) (min_le_left k l)
    calc C1 * (Work.Kernels.scale τ) ^ N1 * (1 + ‖(z : ℂ)‖) ^ M1 * ‖Work.Kernels.qParamFun τ‖ ^ k
        = C1 * ((Work.Kernels.scale τ) ^ N1 * (1 + ‖(z : ℂ)‖) ^ M1
            * ‖Work.Kernels.qParamFun τ‖ ^ k) := by ring
      _ ≤ C1 * ((Work.Kernels.scale τ) ^ (N1 + N2) * (1 + ‖(z : ℂ)‖) ^ (M1 + M2)
            * ‖Work.Kernels.qParamFun τ‖ ^ (min k l)) := mul_le_mul_of_nonneg_left hp hC1.le
      _ = C1 * (Work.Kernels.scale τ) ^ (N1 + N2) * (1 + ‖(z : ℂ)‖) ^ (M1 + M2)
            * ‖Work.Kernels.qParamFun τ‖ ^ (min k l) := by ring
  have p2 : C2 * (Work.Kernels.scale τ) ^ N2 * (1 + ‖(z : ℂ)‖) ^ M2
        * ‖Work.Kernels.qParamFun τ‖ ^ l
      ≤ C2 * (Work.Kernels.scale τ) ^ (N1 + N2) * (1 + ‖(z : ℂ)‖) ^ (M1 + M2)
        * ‖Work.Kernels.qParamFun τ‖ ^ (min k l) := by
    have hp := prof_le τ z hτ (N := N2) (N' := N1 + N2) (M := M2) (M' := M1 + M2)
      (k := l) (k' := min k l) (by linarith) (by linarith) (min_le_right k l)
    calc C2 * (Work.Kernels.scale τ) ^ N2 * (1 + ‖(z : ℂ)‖) ^ M2 * ‖Work.Kernels.qParamFun τ‖ ^ l
        = C2 * ((Work.Kernels.scale τ) ^ N2 * (1 + ‖(z : ℂ)‖) ^ M2
            * ‖Work.Kernels.qParamFun τ‖ ^ l) := by ring
      _ ≤ C2 * ((Work.Kernels.scale τ) ^ (N1 + N2) * (1 + ‖(z : ℂ)‖) ^ (M1 + M2)
            * ‖Work.Kernels.qParamFun τ‖ ^ (min k l)) := mul_le_mul_of_nonneg_left hp hC2.le
      _ = C2 * (Work.Kernels.scale τ) ^ (N1 + N2) * (1 + ‖(z : ℂ)‖) ^ (M1 + M2)
            * ‖Work.Kernels.qParamFun τ‖ ^ (min k l) := by ring
  calc ‖F τ z + G τ z‖ ≤ ‖F τ z‖ + ‖G τ z‖ := norm_add_le _ _
    _ ≤ C1 * (Work.Kernels.scale τ) ^ (N1 + N2) * (1 + ‖(z : ℂ)‖) ^ (M1 + M2)
          * ‖Work.Kernels.qParamFun τ‖ ^ (min k l)
        + C2 * (Work.Kernels.scale τ) ^ (N1 + N2) * (1 + ‖(z : ℂ)‖) ^ (M1 + M2)
          * ‖Work.Kernels.qParamFun τ‖ ^ (min k l) := add_le_add (le_trans e1 p1) (le_trans e2 p2)
    _ = (C1 + C2) * (Work.Kernels.scale τ) ^ (N1 + N2) * (1 + ‖(z : ℂ)‖) ^ (M1 + M2)
          * ‖Work.Kernels.qParamFun τ‖ ^ (min k l) := by ring

private lemma BigZ.neg {k : ℕ} {F : ℍ → ℍ → ℂ} (h : BigZ k F) : BigZ k (fun τ z => -F τ z) := by
  obtain ⟨C, N, M, hC, hN, hM, hF⟩ := h
  exact ⟨C, N, M, hC, hN, hM, fun τ z hτ => by rw [norm_neg]; exact hF τ z hτ⟩

private lemma BigZ.sub {k l : ℕ} {F G : ℍ → ℍ → ℂ} (hF : BigZ k F) (hG : BigZ l G) :
    BigZ (min k l) (fun τ z => F τ z - G τ z) := by
  exact BigZ.congr (BigZ.add hF (BigZ.neg hG)) (fun τ z => by ring)

private lemma BigZ.mul {k l : ℕ} {F G : ℍ → ℍ → ℂ} (hF : BigZ k F) (hG : BigZ l G) :
    BigZ (k + l) (fun τ z => F τ z * G τ z) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, h1⟩ := hF
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, h2⟩ := hG
  refine ⟨C1 * C2, N1 + N2, M1 + M2, by positivity, by linarith, by linarith, fun τ z hτ => ?_⟩
  have e1 := h1 τ z hτ
  have e2 := h2 τ z hτ
  have h0 : (0 : ℝ) ≤ C1 * (Work.Kernels.scale τ) ^ N1 * (1 + ‖(z : ℂ)‖) ^ M1
      * ‖Work.Kernels.qParamFun τ‖ ^ k :=
    mul_nonneg (mul_nonneg (mul_nonneg hC1.le (sc_rpow_nonneg τ N1)) (zf_rpow_nonneg z M1))
      (qn_pow_nonneg τ k)
  rw [norm_mul]
  calc ‖F τ z‖ * ‖G τ z‖
      ≤ (C1 * (Work.Kernels.scale τ) ^ N1 * (1 + ‖(z : ℂ)‖) ^ M1
            * ‖Work.Kernels.qParamFun τ‖ ^ k)
        * (C2 * (Work.Kernels.scale τ) ^ N2 * (1 + ‖(z : ℂ)‖) ^ M2
            * ‖Work.Kernels.qParamFun τ‖ ^ l) := mul_le_mul e1 e2 (norm_nonneg _) h0
    _ = (C1 * C2) * (Work.Kernels.scale τ) ^ (N1 + N2) * (1 + ‖(z : ℂ)‖) ^ (M1 + M2)
          * ‖Work.Kernels.qParamFun τ‖ ^ (k + l) := by
        rw [sc_rpow_add, zf_rpow_add, pow_add]
        ring

private lemma BigZ.const_mul (c : ℂ) {k : ℕ} {F : ℍ → ℍ → ℂ} (h : BigZ k F) :
    BigZ k (fun τ z => c * F τ z) := by
  obtain ⟨C, N, M, hC, hN, hM, hF⟩ := h
  refine ⟨(‖c‖ + 1) * C, N, M, by positivity, hN, hM, fun τ z hτ => ?_⟩
  have e := hF τ z hτ
  have h0 : (0 : ℝ) ≤ C * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ M
      * ‖Work.Kernels.qParamFun τ‖ ^ k :=
    mul_nonneg (mul_nonneg (mul_nonneg hC.le (sc_rpow_nonneg τ N)) (zf_rpow_nonneg z M))
      (qn_pow_nonneg τ k)
  rw [norm_mul]
  calc ‖c‖ * ‖F τ z‖ ≤ ‖c‖ * (C * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ M
        * ‖Work.Kernels.qParamFun τ‖ ^ k) := mul_le_mul_of_nonneg_left e (norm_nonneg _)
    _ ≤ (‖c‖ + 1) * (C * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ M
        * ‖Work.Kernels.qParamFun τ‖ ^ k) := mul_le_mul_of_nonneg_right (by linarith) h0
    _ = ((‖c‖ + 1) * C) * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ M
        * ‖Work.Kernels.qParamFun τ‖ ^ k := by ring

private lemma BigZ.pow {k : ℕ} {F : ℍ → ℍ → ℂ} (h : BigZ k F) (n : ℕ) :
    BigZ (k * n) (fun τ z => F τ z ^ n) := by
  induction n with
  | zero =>
      refine ⟨1, 0, 0, one_pos, le_rfl, le_rfl, fun τ z _ => ?_⟩
      simp
  | succ n ih =>
      have h2 := BigZ.mul ih h
      have h3 : BigZ (k * n + k) (fun τ z => F τ z ^ n * F τ z) := h2
      rw [show k * (n + 1) = k * n + k by ring]
      exact BigZ.congr h3 (fun τ z => by ring)

private lemma BigZ.zero (k : ℕ) : BigZ k (fun _ _ => (0 : ℂ)) :=
  ⟨1, 0, 0, one_pos, le_rfl, le_rfl, fun τ z _ => by simp⟩

private lemma BigZ.const (c : ℂ) : BigZ 0 (fun _ _ => c) :=
  ⟨‖c‖ + 1, 0, 0, by positivity, le_rfl, le_rfl, fun τ z _ => by
    simp only [Real.rpow_zero, pow_zero, mul_one]
    linarith⟩

private lemma BigZ.q_atom (k : ℕ) : BigZ k (fun τ _ => Work.Kernels.qParamFun τ ^ k) :=
  ⟨1, 0, 0, one_pos, le_rfl, le_rfl, fun τ z _ => by
    simp only [Real.rpow_zero, pow_zero, mul_one, one_mul, norm_pow]
    exact le_rfl⟩

private lemma BigZ.z_atom : BigZ 0 (fun _ z : ℍ => (z : ℂ)) :=
  ⟨1, 0, 1, one_pos, le_rfl, zero_le_one, fun τ z _ => by
    simp only [Real.rpow_zero, Real.rpow_one, pow_zero, mul_one, one_mul]
    linarith [norm_nonneg (z : ℂ)]⟩

private lemma BigZ.of_bdd {F : ℍ → ℍ → ℂ} {C : ℝ} (hC : 0 < C)
    (h : ∀ τ z : ℍ, Work.Asymptotics.Funnel τ → ‖F τ z‖ ≤ C) : BigZ 0 F :=
  ⟨C, 0, 0, hC, le_rfl, le_rfl, fun τ z hτ => by
    simp only [Real.rpow_zero, pow_zero, mul_one]
    exact h τ z hτ⟩

private lemma BigZ.of_big {k : ℕ} {f : ℍ → ℂ} (h : Work.Asymptotics.KhatE1Core.Big k f) :
    BigZ k (fun τ _ => f τ) := by
  obtain ⟨C, N, hC, hN, hf⟩ := h
  refine ⟨C, N, 0, hC, hN, le_rfl, fun τ z hτ => ?_⟩
  rw [Real.rpow_zero, mul_one]
  exact hf τ hτ



/-! ## §2  The atoms and their `q`-expansions on the funnel -/

open Work.Asymptotics.KhatE1Core (Big)

/-- The nome. -/
private def qF (τ : ℍ) : ℂ := Work.Kernels.qParamFun τ

/-- `Λ = πiτ + cuspC ℓ`. -/
private def LamF (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ

/-- An abbreviation for `Xc ℓ z = πiz + cuspC ℓ`. -/
private def XcF (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) : ℂ :=
  (Real.pi : ℂ) * Complex.I * (z : ℂ) + Work.Asymptotics.Compact.cuspC ℓ

private def E2F (τ : ℍ) : ℂ := Work.Kernels.E2Fun τ
private def E4F (τ : ℍ) : ℂ := Work.Kernels.E4Fun τ
private def E6F (τ : ℍ) : ℂ := Work.Kernels.E6Fun τ
private def XF (τ : ℍ) : ℂ := Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ
private def psi2F (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ := Work.Kernels.psi2 ℓ τ
private def psi4F (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ := Work.Kernels.psi4 ℓ τ
private def jF (τ : ℍ) : ℂ := Work.Kernels.jInvariantFun τ

private lemma cuspC_norm_le (ℓ : Work.Kernels.LogLambdaData) :
    ‖Work.Asymptotics.Compact.cuspC ℓ‖ ≤ 4 := by
  have hc : Work.Asymptotics.Compact.cuspC ℓ = 4 * (Real.log 2 : ℂ) :=
    Work.Asymptotics.CuspL_eq ℓ
  rw [hc]
  have h0 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  linarith

private lemma pi_norm : ‖(Real.pi : ℂ)‖ = Real.pi := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- `Λ = πiτ + cuspC ℓ` is `O(scale τ)`. -/
private lemma LamF_big (ℓ : Work.Kernels.LogLambdaData) :
    Big 0 (fun τ => LamF ℓ τ) := by
  have h := kdevA4_cuspLin_le ℓ
  refine ⟨Real.pi + 4 + 1, 1, by positivity, by norm_num, ?_⟩
  intro τ hτ
  simp only []
  have hcc := cuspC_norm_le ℓ
  have h1 : LamF ℓ τ = (Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ :=
    rfl
  rw [h1, Real.rpow_one, pow_zero, mul_one]
  refine le_trans (h τ) ?_
  have h0 : (0 : ℝ) < Work.Kernels.scale τ := sc_pos τ
  nlinarith [Real.pi_pos, hcc, h0]

/-- The `z`-atom `Xc ℓ z = πiz + cuspC ℓ` is `O(1 + ‖z‖)`. -/
private lemma Xc_bigZ (ℓ : Work.Kernels.LogLambdaData) :
    BigZ 0 (fun _ z => XcF ℓ z) := by
  refine ⟨Real.pi + 4 + 1, 0, 1, by positivity, le_rfl, zero_le_one, fun τ z hτ => ?_⟩
  have hz : (0 : ℝ) ≤ ‖(z : ℂ)‖ := norm_nonneg _
  simp only [Real.rpow_zero, Real.rpow_one, pow_zero, mul_one, one_mul]
  have h1 : ‖XcF ℓ z‖ ≤ Real.pi * ‖(z : ℂ)‖ + 4 := by
    have h2 : XcF ℓ z = (Real.pi : ℂ) * Complex.I * (z : ℂ) + Work.Asymptotics.Compact.cuspC ℓ :=
      rfl
    rw [h2]
    refine le_trans (norm_add_le _ _) ?_
    have h3 : ‖(Real.pi : ℂ) * Complex.I * (z : ℂ)‖ = Real.pi * ‖(z : ℂ)‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, pi_norm]
    rw [h3]
    linarith [cuspC_norm_le ℓ]
  calc ‖XcF ℓ z‖ ≤ Real.pi * ‖(z : ℂ)‖ + 4 := h1
    _ ≤ (Real.pi + 4 + 1) * (1 + ‖(z : ℂ)‖) := by nlinarith [Real.pi_pos, hz]

/-! ### Atom bounds (`BigZ 0`) -/

private lemma E2_bigZ : BigZ 0 (fun τ _ => E2F τ) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E2Fun_bound
  exact BigZ.of_bdd hC (fun τ z hτ => h τ (le_trans (by norm_num) hτ.2))

private lemma E4_bigZ : BigZ 0 (fun τ _ => E4F τ) := by
  refine BigZ.of_bdd (C := 3 / 2) (by norm_num) (fun τ z hτ => ?_)
  exact Work.FunnelNumerics.E4_funnel_bounds.1 τ hτ

private lemma E6_bigZ : BigZ 0 (fun τ _ => E6F τ) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E6Fun_bound
  exact BigZ.of_bdd hC (fun τ z hτ => h τ (le_trans (by norm_num) hτ.2))

private lemma invE4_bigZ : BigZ 0 (fun τ _ => (E4F τ)⁻¹) :=
  BigZ.of_bdd (C := 2) (by norm_num) (fun τ z hτ => Work.Asymptotics.funnel_E4_inv_le τ hτ)

private lemma invE4_big : Big 0 (fun τ => (E4F τ)⁻¹) :=
  Big.of_bdd (C := 2) (by norm_num) (fun τ hτ => Work.Asymptotics.funnel_E4_inv_le τ hτ)

private lemma X_bigZ : BigZ 0 (fun τ _ => XF τ) := by
  refine BigZ.congr (BigZ.mul E6_bigZ invE4_bigZ) (fun τ z => ?_)
  rw [XF, E6F, E4F, div_eq_mul_inv]

private lemma qF_big (k : ℕ) : Big k (fun τ => qF τ ^ k) := by
  refine ⟨1, 0, one_pos, le_rfl, ?_⟩
  intro τ hτ
  simp only []
  simp only [qF, norm_pow, Real.rpow_zero, mul_one, one_mul]
  exact le_rfl

private lemma one_sub_cq_big (c : ℂ) : Big 0 (fun τ => (1 : ℂ) - c * qF τ) := by
  refine Big.congr (Big.sub Big.one (Big.const_mul c (qF_big 1))) (fun τ => ?_)
  ring

private lemma two_lam_big (ℓ : Work.Kernels.LogLambdaData) :
    Big 0 (fun τ => 2 * LamF ℓ τ) := Big.const_mul 2 (LamF_big ℓ)

/-- `ψ₂ - 2Λ = O(‖q‖ scale^N)`. -/
private lemma psi2_sub_big (ℓ : Work.Kernels.LogLambdaData) :
    Big 1 (fun τ => psi2F ℓ τ - 2 * LamF ℓ τ) := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.KhatE1Core.psi_individual_first_order ℓ
  refine ⟨C, N, hC, hN, ?_⟩
  intro τ hτ
  simp only []
  have h1 := (h τ hτ).1
  have h2 : psi2F ℓ τ - 2 * LamF ℓ τ
      = Work.Kernels.psi2 ℓ τ - 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
          + Work.Asymptotics.Compact.cuspC ℓ) := by
    rw [psi2F, LamF]
  rw [h2]
  simpa using h1

/-- `ψ₄ - 2Λ = O(‖q‖ scale^N)`. -/
private lemma psi4_sub_big (ℓ : Work.Kernels.LogLambdaData) :
    Big 1 (fun τ => psi4F ℓ τ - 2 * LamF ℓ τ) := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.KhatE1Core.psi_individual_first_order ℓ
  refine ⟨C, N, hC, hN, ?_⟩
  intro τ hτ
  simp only []
  have h1 := (h τ hτ).2
  have h2 : psi4F ℓ τ - 2 * LamF ℓ τ
      = Work.Kernels.psi4 ℓ τ - 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
          + Work.Asymptotics.Compact.cuspC ℓ) := by
    rw [psi4F, LamF]
  rw [h2]
  simpa using h1

private lemma psi2_bigZ (ℓ : Work.Kernels.LogLambdaData) : BigZ 0 (fun τ _ => psi2F ℓ τ) := by
  refine BigZ.congr (BigZ.add ((BigZ.of_big (psi2_sub_big ℓ)).mono (k := 1) (l := 0) (by norm_num))
    (BigZ.of_big (two_lam_big ℓ))) (fun τ z => ?_)
  ring

private lemma psi4_bigZ (ℓ : Work.Kernels.LogLambdaData) : BigZ 0 (fun τ _ => psi4F ℓ τ) := by
  refine BigZ.congr (BigZ.add ((BigZ.of_big (psi4_sub_big ℓ)).mono (k := 1) (l := 0) (by norm_num))
    (BigZ.of_big (two_lam_big ℓ))) (fun τ z => ?_)
  ring

/-! ## §3  The explicit `q`-polynomials of the cancellation -/

/-- The `q⁰`-approximant of `E₂`. -/
private def E2x (q : ℂ) : ℂ := 1 - 24 * q

/-- The `q⁰`-approximant of `E₄`. -/
private def E4x (q : ℂ) : ℂ := 1 + 240 * q

/-- The `q⁰`-approximant of `E₆`. -/
private def E6x (q : ℂ) : ℂ := 1 - 504 * q

/-- The `q⁰`-approximant of `E₆/E₄`. -/
private def Xx (q : ℂ) : ℂ := 1 - 744 * q

/-- The `q¹`-approximant of `ψ₂`. -/
private def psi2x (L q : ℂ) : ℂ := 2 * L + (48 * L + 408) * q

/-- The `q¹`-approximant of `ψ₄`. -/
private def psi4x (L q : ℂ) : ℂ := 2 * L - (288 * L + 744) * q

private noncomputable def RmF (q z tau cc : ℂ) : ℂ :=
  -59719680 + 2804170752 * cc - (343056384 * Complex.I * tau * (Real.pi : ℂ)) + 1021870080 * z * tau * (Real.pi : ℂ)^2 + 581603328 * z^2 * (Real.pi : ℂ)^2 + 183748608 * Complex.I * z^2 * tau * (Real.pi : ℂ)^3 + 246183100416 * q + 28962717696 * q * cc + 28962717696 * Complex.I * q * tau * (Real.pi : ℂ) - (11466178560 * q * z * tau * (Real.pi : ℂ)^2) - (7652081664 * q * z^2 * (Real.pi : ℂ)^2) - (4570546176 * Complex.I * q * z^2 * tau * (Real.pi : ℂ)^3) + 30608326656 * Complex.I * q^2 * z^2 * tau * (Real.pi : ℂ)^3

private noncomputable def QdF (q a pp z tau : ℂ) : ℂ :=
  1152 * pp + 576 * z^2 * (Real.pi : ℂ)^2 * a + 96 * Complex.I * z^2 * tau * (Real.pi : ℂ)^3 * a^2 - (811008 * q * pp) - (428544 * q * z^2 * (Real.pi : ℂ)^2 * a) - (71424 * Complex.I * q * z^2 * tau * (Real.pi : ℂ)^3 * a^2)

private noncomputable def QpF (q : ℂ) : ℂ :=
  1152 - (1668096 * q) + 603389952 * q^2

private noncomputable def QsF (q : ℂ) : ℂ :=
  576 - (847872 * q)

private noncomputable def AlF (q z tau : ℂ) : ℂ :=
  96 * Complex.I * z^2 * tau * (Real.pi : ℂ)^3 - (142848 * Complex.I * q * z^2 * tau * (Real.pi : ℂ)^3) + 53139456 * Complex.I * q^2 * z^2 * tau * (Real.pi : ℂ)^3

private noncomputable def BeF (q z tau : ℂ) : ℂ :=
  576 * z^2 * (Real.pi : ℂ)^2 - (857088 * q * z^2 * (Real.pi : ℂ)^2) + 318836736 * q^2 * z^2 * (Real.pi : ℂ)^2

private noncomputable def GaF (q z tau : ℂ) : ℂ :=
  -3456 * Complex.I * tau * (Real.pi : ℂ) + 1152 * z * tau * (Real.pi : ℂ)^2 + 96 * Complex.I * z^2 * tau * (Real.pi : ℂ)^3 + 3400704 * Complex.I * q * tau * (Real.pi : ℂ) - (1161216 * q * z * tau * (Real.pi : ℂ)^2) - (99072 * Complex.I * q * z^2 * tau * (Real.pi : ℂ)^3)

private noncomputable def DeF (q z cc : ℂ) : ℂ :=
  -3456 * cc - (576 * z^2 * (Real.pi : ℂ)^2) - (41472 * q) + 5971968 * q * cc + 1009152 * q * z^2 * (Real.pi : ℂ)^2

private noncomputable def EpF (q z tau : ℂ) : ℂ :=
  -1152 * z * tau * (Real.pi : ℂ)^2 - (192 * Complex.I * z^2 * tau * (Real.pi : ℂ)^3) + 1990656 * q * z * tau * (Real.pi : ℂ)^2 + 336384 * Complex.I * q * z^2 * tau * (Real.pi : ℂ)^3


/-! The powers of `I` needed to reduce the scalar monomials of the cancellation. -/

private lemma Isq : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq

private lemma Icube : (Complex.I : ℂ) ^ 3 = -Complex.I := by
  rw [pow_succ, Isq]
  ring

private lemma Ifour : (Complex.I : ℂ) ^ 4 = 1 := by
  have h : (Complex.I : ℂ) ^ 4 = ((Complex.I : ℂ) ^ 2) ^ 2 := by ring
  rw [h, Isq]
  norm_num

/-! ## §4  The sharp cancellation identity for `A₂ + q·A₁` -/

private theorem Psi2_decomp (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hτ : Work.Asymptotics.Funnel τ) :
    Work.Asymptotics.KhatE1Core.KdevA4j2 ℓ τ z
        + qF τ * Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z
      = (qF τ) ^ 2 * RmF (qF τ) (z : ℂ) (τ : ℂ) (Work.Asymptotics.Compact.cuspC ℓ)
        + (XF τ - Xx (qF τ)) * QdF (qF τ) (E2F τ) (psi2F ℓ τ) (z : ℂ) (τ : ℂ)
        + (psi2F ℓ τ - psi2x (LamF ℓ τ) (qF τ)) * QpF (qF τ)
        + (psi4F ℓ τ - psi4x (LamF ℓ τ) (qF τ)) * QsF (qF τ)
        + AlF (qF τ) (z : ℂ) (τ : ℂ)
            * ((E2F τ - E2x (qF τ)) * (E2F τ + E2x (qF τ)))
        + BeF (qF τ) (z : ℂ) (τ : ℂ) * (E2F τ - E2x (qF τ))
        + GaF (qF τ) (z : ℂ) (τ : ℂ) * (E6F τ - E6x (qF τ))
        + DeF (qF τ) (z : ℂ) (Work.Asymptotics.Compact.cuspC ℓ) * (E4F τ - E4x (qF τ))
        + EpF (qF τ) (z : ℂ) (τ : ℂ)
            * ((E2F τ - E2x (qF τ)) * E4F τ + E2x (qF τ) * (E4F τ - E4x (qF τ))) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hE4 : E4F τ ≠ 0 := Work.Asymptotics.funnel_E4_ne_zero τ hτ
  set Xv : ℂ := Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ with hXv
  have hXF : XF τ = Xv := by rw [XF, hXv]
  have hX1 : Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ = Xv := hXv.symm
  have hdiv : ∀ a b c : ℂ, a * b / c = a * (b / c) := by
    intro a b c
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hX2 : Work.Kernels.psi2 ℓ τ * Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ
      = Work.Kernels.psi2 ℓ τ * Xv := by
    rw [hdiv, ← hXv]
  rw [Work.Asymptotics.KhatE1Core.KdevA4j2, Work.Asymptotics.KhatE1Core.KdevA4j1,
    Work.Asymptotics.KhatE1Core.Phi4j2, Work.Asymptotics.KhatE1Core.Phi4j1,
    Work.Asymptotics.KhatE1Core.BRj2, Work.Asymptotics.KhatE1Core.BRj1,
    Work.Asymptotics.KhatE1Core.tailC_scalar, hXF, hX1, hX2,
    RmF, QdF, QpF, QsF, AlF, BeF, GaF, DeF, EpF,
    Xx, E2x, E4x, E6x, psi2x, psi4x, E2F, E4F, E6F, psi2F, psi4F, LamF, qF,
    Work.Asymptotics.Compact.Xc]
  field_simp
  ring_nf
  simp only [Isq, Icube, Ifour]
  try ring_nf
  try ring_nf

/-! ## §5  Bounds for the multipliers and the cancellation identity -/

/-- A monomial `C * q^a * z^b * τ^l * (cuspC ℓ)^m` is `BigZ 0`. -/
private lemma monZ (ℓ : Work.Kernels.LogLambdaData) (C : ℂ) (a b l m : ℕ) :
    BigZ 0 (fun τ z => C * qF τ ^ a * (z : ℂ) ^ b * (τ : ℂ) ^ l
      * (Work.Asymptotics.Compact.cuspC ℓ) ^ m) := by
  refine ⟨‖C‖ * 4 ^ m + 1, ((a + l : ℕ) : ℝ), (b : ℝ), by positivity, by positivity,
    by positivity, ?_⟩
  intro τ z hτ
  simp only [Real.rpow_zero, pow_zero, mul_one, Real.rpow_natCast]
  have hq1 : ‖qF τ‖ ≤ 1 := qn_le_one τ hτ
  have hq0 : (0 : ℝ) ≤ ‖qF τ‖ := qn_nonneg τ
  have hz0 : (0 : ℝ) ≤ ‖(z : ℂ)‖ := norm_nonneg _
  have hz1 : ‖(z : ℂ)‖ ≤ 1 + ‖(z : ℂ)‖ := by linarith
  have ht : ‖(τ : ℂ)‖ ≤ Work.Kernels.scale τ := Work.Kernels.coe_norm_le_scale τ
  have hcc : ‖Work.Asymptotics.Compact.cuspC ℓ‖ ≤ 4 := cuspC_norm_le ℓ
  have hcc0 : (0 : ℝ) ≤ ‖Work.Asymptotics.Compact.cuspC ℓ‖ := norm_nonneg _
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := sc_ge_one τ
  have hs0 : (0 : ℝ) < Work.Kernels.scale τ := sc_pos τ
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, norm_pow]
  have e1 : ‖qF τ‖ ^ a ≤ 1 := pow_le_one₀ hq0 hq1
  have e2 : ‖(z : ℂ)‖ ^ b ≤ (1 + ‖(z : ℂ)‖) ^ b :=
    pow_le_pow_left₀ hz0 hz1 b
  have e3 : ‖(τ : ℂ)‖ ^ l ≤ (Work.Kernels.scale τ) ^ l := pow_le_pow_left₀ (norm_nonneg _) ht l
  have e4 : ‖Work.Asymptotics.Compact.cuspC ℓ‖ ^ m ≤ 4 ^ m := pow_le_pow_left₀ hcc0 hcc m
  have step1 : ‖C‖ * ‖qF τ‖ ^ a * ‖(z : ℂ)‖ ^ b * ‖(τ : ℂ)‖ ^ l
        * ‖Work.Asymptotics.Compact.cuspC ℓ‖ ^ m
      ≤ ‖C‖ * 1 * (1 + ‖(z : ℂ)‖) ^ b * (Work.Kernels.scale τ) ^ l * 4 ^ m :=
    mul5_le (norm_nonneg _) (pow_nonneg hq0 a) (pow_nonneg hz0 b) (pow_nonneg (norm_nonneg _) l)
      (pow_nonneg hcc0 m) (le_refl ‖C‖) e1 e2 e3 e4
  have step2 : (Work.Kernels.scale τ) ^ l ≤ (Work.Kernels.scale τ) ^ (a + l) :=
    pow_le_pow_right₀ hs1 (Nat.le_add_left l a)
  refine le_trans step1 ?_
  calc ‖C‖ * 1 * (1 + ‖(z : ℂ)‖) ^ b * (Work.Kernels.scale τ) ^ l * 4 ^ m
      ≤ ‖C‖ * 1 * (1 + ‖(z : ℂ)‖) ^ b * (Work.Kernels.scale τ) ^ (a + l) * 4 ^ m :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left step2 (by positivity)) (by positivity)
    _ = ‖C‖ * 4 ^ m * (Work.Kernels.scale τ) ^ (a + l) * (1 + ‖(z : ℂ)‖) ^ b := by ring
    _ ≤ (‖C‖ * 4 ^ m + 1) * (Work.Kernels.scale τ) ^ (a + l) * (1 + ‖(z : ℂ)‖) ^ b := by
        have h0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ (a + l) * (1 + ‖(z : ℂ)‖) ^ b :=
          mul_nonneg (pow_nonneg (le_of_lt hs0) _) (pow_nonneg (by positivity) _)
        nlinarith [h0]
private lemma RmF_bigZ (ℓ : Work.Kernels.LogLambdaData) :
    BigZ 0 (fun τ z => RmF (qF τ) (z : ℂ) (τ : ℂ) (Work.Asymptotics.Compact.cuspC ℓ)) := by
  have m1 : BigZ 0 (fun τ z => (-59719680 : ℂ) * qF τ ^ 0 * (z : ℂ) ^ 0 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((-59719680 : ℂ)) 0 0 0 0) (fun τ z => by ring)
  have m2 : BigZ 0 (fun τ z => (2804170752 : ℂ) * qF τ ^ 0 * (z : ℂ) ^ 0 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 1) :=
    BigZ.congr (monZ ℓ ((2804170752 : ℂ)) 0 0 0 1) (fun τ z => by ring)
  have m3 : BigZ 0 (fun τ z => ((-343056384 : ℂ) * Complex.I) * (Real.pi : ℂ) * qF τ ^ 0 * (z : ℂ) ^ 0 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ (((-343056384 : ℂ) * Complex.I) * (Real.pi : ℂ)) 0 0 1 0) (fun τ z => by ring)
  have m4 : BigZ 0 (fun τ z => (1021870080 : ℂ) * (Real.pi : ℂ)^2 * qF τ ^ 0 * (z : ℂ) ^ 1 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((1021870080 : ℂ) * (Real.pi : ℂ)^2) 0 1 1 0) (fun τ z => by ring)
  have m5 : BigZ 0 (fun τ z => (581603328 : ℂ) * (Real.pi : ℂ)^2 * qF τ ^ 0 * (z : ℂ) ^ 2 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((581603328 : ℂ) * (Real.pi : ℂ)^2) 0 2 0 0) (fun τ z => by ring)
  have m6 : BigZ 0 (fun τ z => ((183748608 : ℂ) * Complex.I) * (Real.pi : ℂ)^3 * qF τ ^ 0 * (z : ℂ) ^ 2 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ (((183748608 : ℂ) * Complex.I) * (Real.pi : ℂ)^3) 0 2 1 0) (fun τ z => by ring)
  have m7 : BigZ 0 (fun τ z => (246183100416 : ℂ) * qF τ ^ 1 * (z : ℂ) ^ 0 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((246183100416 : ℂ)) 1 0 0 0) (fun τ z => by ring)
  have m8 : BigZ 0 (fun τ z => (28962717696 : ℂ) * qF τ ^ 1 * (z : ℂ) ^ 0 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 1) :=
    BigZ.congr (monZ ℓ ((28962717696 : ℂ)) 1 0 0 1) (fun τ z => by ring)
  have m9 : BigZ 0 (fun τ z => ((28962717696 : ℂ) * Complex.I) * (Real.pi : ℂ) * qF τ ^ 1 * (z : ℂ) ^ 0 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ (((28962717696 : ℂ) * Complex.I) * (Real.pi : ℂ)) 1 0 1 0) (fun τ z => by ring)
  have m10 : BigZ 0 (fun τ z => (-11466178560 : ℂ) * (Real.pi : ℂ)^2 * qF τ ^ 1 * (z : ℂ) ^ 1 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((-11466178560 : ℂ) * (Real.pi : ℂ)^2) 1 1 1 0) (fun τ z => by ring)
  have m11 : BigZ 0 (fun τ z => (-7652081664 : ℂ) * (Real.pi : ℂ)^2 * qF τ ^ 1 * (z : ℂ) ^ 2 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((-7652081664 : ℂ) * (Real.pi : ℂ)^2) 1 2 0 0) (fun τ z => by ring)
  have m12 : BigZ 0 (fun τ z => ((-4570546176 : ℂ) * Complex.I) * (Real.pi : ℂ)^3 * qF τ ^ 1 * (z : ℂ) ^ 2 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ (((-4570546176 : ℂ) * Complex.I) * (Real.pi : ℂ)^3) 1 2 1 0) (fun τ z => by ring)
  have m13 : BigZ 0 (fun τ z => ((30608326656 : ℂ) * Complex.I) * (Real.pi : ℂ)^3 * qF τ ^ 2 * (z : ℂ) ^ 2 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ (((30608326656 : ℂ) * Complex.I) * (Real.pi : ℂ)^3) 2 2 1 0) (fun τ z => by ring)
  exact BigZ.congr (BigZ.add (BigZ.add (BigZ.add (BigZ.add (BigZ.add (BigZ.add (BigZ.add (BigZ.add (BigZ.add (BigZ.add (BigZ.add (BigZ.add (m1) m2) m3) m4) m5) m6) m7) m8) m9) m10) m11) m12) m13) (fun τ z => by rw [RmF]; ring)

private lemma QpF_bigZ (ℓ : Work.Kernels.LogLambdaData) :
    BigZ 0 (fun τ z => QpF (qF τ)) := by
  have m1 : BigZ 0 (fun τ z => (1152 : ℂ) * qF τ ^ 0 * (z : ℂ) ^ 0 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((1152 : ℂ)) 0 0 0 0) (fun τ z => by ring)
  have m2 : BigZ 0 (fun τ z => (-1668096 : ℂ) * qF τ ^ 1 * (z : ℂ) ^ 0 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((-1668096 : ℂ)) 1 0 0 0) (fun τ z => by ring)
  have m3 : BigZ 0 (fun τ z => (603389952 : ℂ) * qF τ ^ 2 * (z : ℂ) ^ 0 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((603389952 : ℂ)) 2 0 0 0) (fun τ z => by ring)
  exact BigZ.congr (BigZ.add (BigZ.add (m1) m2) m3) (fun τ z => by rw [QpF]; ring)

private lemma QsF_bigZ (ℓ : Work.Kernels.LogLambdaData) :
    BigZ 0 (fun τ z => QsF (qF τ)) := by
  have m1 : BigZ 0 (fun τ z => (576 : ℂ) * qF τ ^ 0 * (z : ℂ) ^ 0 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((576 : ℂ)) 0 0 0 0) (fun τ z => by ring)
  have m2 : BigZ 0 (fun τ z => (-847872 : ℂ) * qF τ ^ 1 * (z : ℂ) ^ 0 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((-847872 : ℂ)) 1 0 0 0) (fun τ z => by ring)
  exact BigZ.congr (BigZ.add (m1) m2) (fun τ z => by rw [QsF]; ring)

private lemma AlF_bigZ (ℓ : Work.Kernels.LogLambdaData) :
    BigZ 0 (fun τ z => AlF (qF τ) (z : ℂ) (τ : ℂ)) := by
  have m1 : BigZ 0 (fun τ z => ((96 : ℂ) * Complex.I) * (Real.pi : ℂ)^3 * qF τ ^ 0 * (z : ℂ) ^ 2 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ (((96 : ℂ) * Complex.I) * (Real.pi : ℂ)^3) 0 2 1 0) (fun τ z => by ring)
  have m2 : BigZ 0 (fun τ z => ((-142848 : ℂ) * Complex.I) * (Real.pi : ℂ)^3 * qF τ ^ 1 * (z : ℂ) ^ 2 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ (((-142848 : ℂ) * Complex.I) * (Real.pi : ℂ)^3) 1 2 1 0) (fun τ z => by ring)
  have m3 : BigZ 0 (fun τ z => ((53139456 : ℂ) * Complex.I) * (Real.pi : ℂ)^3 * qF τ ^ 2 * (z : ℂ) ^ 2 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ (((53139456 : ℂ) * Complex.I) * (Real.pi : ℂ)^3) 2 2 1 0) (fun τ z => by ring)
  exact BigZ.congr (BigZ.add (BigZ.add (m1) m2) m3) (fun τ z => by rw [AlF]; ring)

private lemma BeF_bigZ (ℓ : Work.Kernels.LogLambdaData) :
    BigZ 0 (fun τ z => BeF (qF τ) (z : ℂ) (τ : ℂ)) := by
  have m1 : BigZ 0 (fun τ z => (576 : ℂ) * (Real.pi : ℂ)^2 * qF τ ^ 0 * (z : ℂ) ^ 2 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((576 : ℂ) * (Real.pi : ℂ)^2) 0 2 0 0) (fun τ z => by ring)
  have m2 : BigZ 0 (fun τ z => (-857088 : ℂ) * (Real.pi : ℂ)^2 * qF τ ^ 1 * (z : ℂ) ^ 2 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((-857088 : ℂ) * (Real.pi : ℂ)^2) 1 2 0 0) (fun τ z => by ring)
  have m3 : BigZ 0 (fun τ z => (318836736 : ℂ) * (Real.pi : ℂ)^2 * qF τ ^ 2 * (z : ℂ) ^ 2 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((318836736 : ℂ) * (Real.pi : ℂ)^2) 2 2 0 0) (fun τ z => by ring)
  exact BigZ.congr (BigZ.add (BigZ.add (m1) m2) m3) (fun τ z => by rw [BeF]; ring)

private lemma GaF_bigZ (ℓ : Work.Kernels.LogLambdaData) :
    BigZ 0 (fun τ z => GaF (qF τ) (z : ℂ) (τ : ℂ)) := by
  have m1 : BigZ 0 (fun τ z => ((-3456 : ℂ) * Complex.I) * (Real.pi : ℂ) * qF τ ^ 0 * (z : ℂ) ^ 0 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ (((-3456 : ℂ) * Complex.I) * (Real.pi : ℂ)) 0 0 1 0) (fun τ z => by ring)
  have m2 : BigZ 0 (fun τ z => (1152 : ℂ) * (Real.pi : ℂ)^2 * qF τ ^ 0 * (z : ℂ) ^ 1 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((1152 : ℂ) * (Real.pi : ℂ)^2) 0 1 1 0) (fun τ z => by ring)
  have m3 : BigZ 0 (fun τ z => ((96 : ℂ) * Complex.I) * (Real.pi : ℂ)^3 * qF τ ^ 0 * (z : ℂ) ^ 2 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ (((96 : ℂ) * Complex.I) * (Real.pi : ℂ)^3) 0 2 1 0) (fun τ z => by ring)
  have m4 : BigZ 0 (fun τ z => ((3400704 : ℂ) * Complex.I) * (Real.pi : ℂ) * qF τ ^ 1 * (z : ℂ) ^ 0 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ (((3400704 : ℂ) * Complex.I) * (Real.pi : ℂ)) 1 0 1 0) (fun τ z => by ring)
  have m5 : BigZ 0 (fun τ z => (-1161216 : ℂ) * (Real.pi : ℂ)^2 * qF τ ^ 1 * (z : ℂ) ^ 1 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((-1161216 : ℂ) * (Real.pi : ℂ)^2) 1 1 1 0) (fun τ z => by ring)
  have m6 : BigZ 0 (fun τ z => ((-99072 : ℂ) * Complex.I) * (Real.pi : ℂ)^3 * qF τ ^ 1 * (z : ℂ) ^ 2 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ (((-99072 : ℂ) * Complex.I) * (Real.pi : ℂ)^3) 1 2 1 0) (fun τ z => by ring)
  exact BigZ.congr (BigZ.add (BigZ.add (BigZ.add (BigZ.add (BigZ.add (m1) m2) m3) m4) m5) m6) (fun τ z => by rw [GaF]; ring)

private lemma DeF_bigZ (ℓ : Work.Kernels.LogLambdaData) :
    BigZ 0 (fun τ z => DeF (qF τ) (z : ℂ) (Work.Asymptotics.Compact.cuspC ℓ)) := by
  have m1 : BigZ 0 (fun τ z => (-3456 : ℂ) * qF τ ^ 0 * (z : ℂ) ^ 0 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 1) :=
    BigZ.congr (monZ ℓ ((-3456 : ℂ)) 0 0 0 1) (fun τ z => by ring)
  have m2 : BigZ 0 (fun τ z => (-576 : ℂ) * (Real.pi : ℂ)^2 * qF τ ^ 0 * (z : ℂ) ^ 2 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((-576 : ℂ) * (Real.pi : ℂ)^2) 0 2 0 0) (fun τ z => by ring)
  have m3 : BigZ 0 (fun τ z => (-41472 : ℂ) * qF τ ^ 1 * (z : ℂ) ^ 0 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((-41472 : ℂ)) 1 0 0 0) (fun τ z => by ring)
  have m4 : BigZ 0 (fun τ z => (5971968 : ℂ) * qF τ ^ 1 * (z : ℂ) ^ 0 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 1) :=
    BigZ.congr (monZ ℓ ((5971968 : ℂ)) 1 0 0 1) (fun τ z => by ring)
  have m5 : BigZ 0 (fun τ z => (1009152 : ℂ) * (Real.pi : ℂ)^2 * qF τ ^ 1 * (z : ℂ) ^ 2 * (τ : ℂ) ^ 0 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((1009152 : ℂ) * (Real.pi : ℂ)^2) 1 2 0 0) (fun τ z => by ring)
  exact BigZ.congr (BigZ.add (BigZ.add (BigZ.add (BigZ.add (m1) m2) m3) m4) m5) (fun τ z => by rw [DeF]; ring)

private lemma EpF_bigZ (ℓ : Work.Kernels.LogLambdaData) :
    BigZ 0 (fun τ z => EpF (qF τ) (z : ℂ) (τ : ℂ)) := by
  have m1 : BigZ 0 (fun τ z => (-1152 : ℂ) * (Real.pi : ℂ)^2 * qF τ ^ 0 * (z : ℂ) ^ 1 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((-1152 : ℂ) * (Real.pi : ℂ)^2) 0 1 1 0) (fun τ z => by ring)
  have m2 : BigZ 0 (fun τ z => ((-192 : ℂ) * Complex.I) * (Real.pi : ℂ)^3 * qF τ ^ 0 * (z : ℂ) ^ 2 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ (((-192 : ℂ) * Complex.I) * (Real.pi : ℂ)^3) 0 2 1 0) (fun τ z => by ring)
  have m3 : BigZ 0 (fun τ z => (1990656 : ℂ) * (Real.pi : ℂ)^2 * qF τ ^ 1 * (z : ℂ) ^ 1 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ ((1990656 : ℂ) * (Real.pi : ℂ)^2) 1 1 1 0) (fun τ z => by ring)
  have m4 : BigZ 0 (fun τ z => ((336384 : ℂ) * Complex.I) * (Real.pi : ℂ)^3 * qF τ ^ 1 * (z : ℂ) ^ 2 * (τ : ℂ) ^ 1 * (Work.Asymptotics.Compact.cuspC ℓ) ^ 0) :=
    BigZ.congr (monZ ℓ (((336384 : ℂ) * Complex.I) * (Real.pi : ℂ)^3) 1 2 1 0) (fun τ z => by ring)
  exact BigZ.congr (BigZ.add (BigZ.add (BigZ.add (m1) m2) m3) m4) (fun τ z => by rw [EpF]; ring)


private lemma BigZ.tau_atom : BigZ 0 (fun τ _ : ℍ => (τ : ℂ)) := by
  refine ⟨1, 1, 0, one_pos, by norm_num, le_rfl, fun τ z hτ => ?_⟩
  simp only [Real.rpow_zero, Real.rpow_one, pow_zero, mul_one, one_mul]
  exact Work.Kernels.coe_norm_le_scale τ

private lemma BigZ.q_atom' : BigZ 1 (fun τ _ : ℍ => qF τ) := by
  refine ⟨1, 0, 0, one_pos, le_rfl, le_rfl, fun τ z _ => ?_⟩
  simp only [Real.rpow_zero, pow_zero, mul_one, one_mul, qF, norm_pow, pow_one]
  exact le_rfl

/-- `QdF`, the `δX`-multiplier, is `BigZ 0`. -/
private lemma QdF_bigZ (ℓ : Work.Kernels.LogLambdaData) :
    BigZ 0 (fun τ z => QdF (qF τ) (E2F τ) (psi2F ℓ τ) (z : ℂ) (τ : ℂ)) := by
  have hz2 : BigZ 0 (fun _ z : ℍ => (z : ℂ) ^ 2) := BigZ.pow BigZ.z_atom 2
  have hE2 : BigZ 0 (fun τ _ : ℍ => E2F τ) := E2_bigZ
  have hE22 : BigZ 0 (fun τ _ : ℍ => E2F τ ^ 2) := BigZ.pow E2_bigZ 2
  have hpsi : BigZ 0 (fun τ _ : ℍ => psi2F ℓ τ) := psi2_bigZ ℓ
  have htau : BigZ 0 (fun τ _ : ℍ => (τ : ℂ)) := BigZ.tau_atom
  have hq : BigZ 1 (fun τ _ : ℍ => qF τ) := BigZ.q_atom'
  have m1 : BigZ 0 (fun τ _ : ℍ => (1152 : ℂ) * psi2F ℓ τ) :=
    BigZ.const_mul 1152 hpsi
  have m2 : BigZ 0 (fun τ z : ℍ => 576 * (z : ℂ) ^ 2 * (Real.pi : ℂ) ^ 2 * E2F τ) := by
    refine BigZ.congr (BigZ.const_mul (576 * (Real.pi : ℂ) ^ 2)
      (BigZ.mul hz2 hE2)) (fun τ z => by ring)
  have m3 : BigZ 0 (fun τ z : ℍ =>
      96 * Complex.I * (z : ℂ) ^ 2 * (τ : ℂ) * (Real.pi : ℂ) ^ 3 * E2F τ ^ 2) := by
    refine BigZ.congr (BigZ.const_mul (96 * Complex.I * (Real.pi : ℂ) ^ 3)
      (BigZ.mul (BigZ.mul hz2 htau) hE22)) (fun τ z => by ring)
  have m4 : BigZ 1 (fun τ _ : ℍ => 811008 * qF τ * psi2F ℓ τ) := by
    refine BigZ.congr (BigZ.const_mul 811008 (BigZ.mul hq hpsi)) (fun τ z => by ring)
  have m5 : BigZ 1 (fun τ z : ℍ =>
      428544 * qF τ * (z : ℂ) ^ 2 * (Real.pi : ℂ) ^ 2 * E2F τ) := by
    refine BigZ.congr (BigZ.const_mul (428544 * (Real.pi : ℂ) ^ 2)
      (BigZ.mul (BigZ.mul hq hz2) hE2)) (fun τ z => by ring)
  have m6 : BigZ 1 (fun τ z : ℍ =>
      71424 * Complex.I * qF τ * (z : ℂ) ^ 2 * (τ : ℂ) * (Real.pi : ℂ) ^ 3 * E2F τ ^ 2) := by
    refine BigZ.congr (BigZ.const_mul (71424 * Complex.I * (Real.pi : ℂ) ^ 3)
      (BigZ.mul (BigZ.mul (BigZ.mul hq hz2) htau) hE22)) (fun τ z => by ring)
  refine BigZ.congr (BigZ.sub (BigZ.add (BigZ.add m1 m2) m3)
    (BigZ.add m4 (BigZ.add m5 m6))) (fun τ z => ?_)
  rw [QdF]
  ring


/-! ### The atom remainders -/

private lemma rE2_big : Big 2 (fun τ => E2F τ - (1 - 24 * qF τ)) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.MFix.E2Fun_two_term
  refine ⟨C, 0, hC, le_rfl, ?_⟩
  intro τ hτ
  simp only []
  have h1 := h τ (Work.Asymptotics.Funnel.im_one hτ)
  have h2 : E2F τ - (1 - 24 * qF τ) = Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ := by
    rw [E2F, qF]; ring
  rw [h2, Real.rpow_zero, mul_one]
  simpa using h1

private lemma rE4_big : Big 2 (fun τ => E4F τ - (1 + 240 * qF τ)) := by
  obtain ⟨C, hC, h⟩ := Work.Residues.E4FunSecondOrder
  refine ⟨C, 0, hC, le_rfl, ?_⟩
  intro τ hτ
  simp only []
  have h1 := h τ (Work.Asymptotics.Funnel.im_one hτ)
  have h2 : E4F τ - (1 + 240 * qF τ) = Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ := by
    rw [E4F, qF]; ring
  rw [h2, Real.rpow_zero, mul_one]
  simpa using h1

private lemma rE6_big : Big 2 (fun τ => E6F τ - (1 - 504 * qF τ)) := by
  obtain ⟨C, hC, h⟩ := Work.Residues.E6FunSecondOrder
  refine ⟨C, 0, hC, le_rfl, ?_⟩
  intro τ hτ
  simp only []
  have h1 := h τ (Work.Asymptotics.Funnel.im_one hτ)
  have h2 : E6F τ - (1 - 504 * qF τ) = Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ := by
    rw [E6F, qF]; ring
  rw [h2, Real.rpow_zero, mul_one]
  simpa using h1

/-- `E₄ - 1 = O(‖q‖ scale^N)`. -/
private lemma E4_sub_one_big : Big 1 (fun τ => E4F τ - 1) := by
  refine Big.congr (Big.add (rE4_big.mono (l := 1) (by norm_num))
    ((Big.const_mul 240 (qF_big 1)).mono (l := 1) (by norm_num))) (fun τ => by ring)

private lemma rInvE4_big : Big 2 (fun τ => (E4F τ)⁻¹ - (1 - 240 * qF τ)) := by
  have hnum : Big 2 (fun τ => -(E4F τ - 1 - 240 * qF τ) + 240 * qF τ * (E4F τ - 1)) := by
    have h1 : Big 2 (fun τ => -(E4F τ - 1 - 240 * qF τ)) :=
      Big.congr (rE4_big.neg) (fun τ => by ring)
    have h2 : Big 2 (fun τ => 240 * qF τ * (E4F τ - 1)) :=
      Big.congr ((Big.mul (Big.const_mul 240 (qF_big 1)) E4_sub_one_big).mono (l := 2)
        (by norm_num)) (fun τ => by ring)
    exact Big.add h1 h2
  refine Big.congr_on (Big.mul hnum invE4_big) (fun τ hτ => ?_)
  have hne : E4F τ ≠ 0 := Work.Asymptotics.funnel_E4_ne_zero τ hτ
  have hfield : (E4F τ)⁻¹ - (1 - 240 * qF τ)
      = (-(E4F τ - 1 - 240 * qF τ) + 240 * qF τ * (E4F τ - 1)) * (E4F τ)⁻¹ := by
    field_simp
    ring
  rw [hfield]

private lemma rX_big : Big 2 (fun τ => XF τ - (1 - 744 * qF τ)) := by
  have h1 : Big 2 (fun τ => (E6F τ - (1 - 504 * qF τ)) * (E4F τ)⁻¹) :=
    (Big.mul rE6_big invE4_big).mono (l := 2) (by norm_num)
  have h2 : Big 2 (fun τ => (1 - 504 * qF τ) * ((E4F τ)⁻¹ - (1 - 240 * qF τ))) :=
    (Big.mul (one_sub_cq_big 504) rInvE4_big).mono (l := 2) (by norm_num)
  have h3 : Big 2 (fun τ => 120960 * qF τ ^ 2) := Big.const_mul 120960 (qF_big 2)
  refine Big.congr_on (Big.add (Big.add h1 h2) h3) (fun τ hτ => ?_)
  have hne : E4F τ ≠ 0 := Work.Asymptotics.funnel_E4_ne_zero τ hτ
  rw [XF, E6F, E4F]
  field_simp
  ring_nf

private lemma rpsi2_big (ℓ : Work.Kernels.LogLambdaData) :
    Big 2 (fun τ => psi2F ℓ τ - (2 * LamF ℓ τ + (48 * LamF ℓ τ + 408) * qF τ)) := by
  obtain ⟨C, N, hC, hN, h2⟩ := Work.Asymptotics.KhatE1Core.psi_second_order ℓ
  have h3 : Big 3 (fun τ => psi2F ℓ τ - 2 * LamF ℓ τ - (48 * LamF ℓ τ + 408) * qF τ
      - (48 * LamF ℓ τ + 2636) * qF τ ^ 2) := by
    refine ⟨C, N, hC, hN, ?_⟩
    intro τ hτ
    simp only []
    have h := (h2 τ hτ).1
    have he : psi2F ℓ τ - 2 * LamF ℓ τ - (48 * LamF ℓ τ + 408) * qF τ
        - (48 * LamF ℓ τ + 2636) * qF τ ^ 2
        = Work.Kernels.psi2 ℓ τ
          - 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
          - (48 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
              + 408) * Work.Kernels.qParamFun τ
          - (48 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
              + 2636) * Work.Kernels.qParamFun τ ^ 2 := by
      rw [psi2F, LamF, qF]
    rw [he]
    exact h
  have htail : Big 2 (fun τ => (48 * LamF ℓ τ + 2636) * qF τ ^ 2) :=
    Big.congr (Big.mul (Big.add (Big.const_mul 48 (LamF_big ℓ)) (Big.const 2636)) (qF_big 2))
      (fun τ => by ring)
  refine Big.congr (Big.add (h3.mono (l := 2) (by norm_num)) htail) (fun τ => ?_)
  ring

private lemma rpsi4_big (ℓ : Work.Kernels.LogLambdaData) :
    Big 2 (fun τ => psi4F ℓ τ - (2 * LamF ℓ τ - (288 * LamF ℓ τ + 744) * qF τ)) := by
  obtain ⟨C, N, hC, hN, h4⟩ := Work.Asymptotics.KhatE1Core.psi_second_order ℓ
  have h3 : Big 3 (fun τ => psi4F ℓ τ - 2 * LamF ℓ τ + (288 * LamF ℓ τ + 744) * qF τ
      + (1824 * LamF ℓ τ + 25972) * qF τ ^ 2) := by
    refine ⟨C, N, hC, hN, ?_⟩
    intro τ hτ
    simp only []
    have h := (h4 τ hτ).2
    have he : psi4F ℓ τ - 2 * LamF ℓ τ + (288 * LamF ℓ τ + 744) * qF τ
        + (1824 * LamF ℓ τ + 25972) * qF τ ^ 2
        = Work.Kernels.psi4 ℓ τ
          - 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
          + (288 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
              + 744) * Work.Kernels.qParamFun τ
          + (1824 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
              + 25972) * Work.Kernels.qParamFun τ ^ 2 := by
      rw [psi4F, LamF, qF]
    rw [he]
    exact h
  have htail : Big 2 (fun τ => -(1824 * LamF ℓ τ + 25972) * qF τ ^ 2) :=
    Big.congr (Big.mul (Big.neg (Big.add (Big.const_mul 1824 (LamF_big ℓ)) (Big.const 25972)))
      (qF_big 2)) (fun τ => by ring)
  refine Big.congr (Big.add (h3.mono (l := 2) (by norm_num)) htail) (fun τ => ?_)
  ring

private lemma jq_sub_one_big : Big 1 (fun τ => jF τ * qF τ - 1) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.KhatE1Core.jq_second_order
  have h1 : Big 2 (fun τ => jF τ * qF τ - 1 - 744 * qF τ) := by
    refine ⟨C, 0, hC, le_rfl, ?_⟩
    intro τ hτ
    simp only []
    have hh := h τ (by have := hτ.2; linarith)
    have he : jF τ * qF τ - 1 - 744 * qF τ
        = Work.Kernels.jInvariantFun τ * Work.Kernels.qParamFun τ - 1
          - 744 * Work.Kernels.qParamFun τ := by
      rw [jF, qF]
    rw [he, Real.rpow_zero, mul_one]
    simpa using hh
  refine Big.congr (Big.add (h1.mono (l := 1) (by norm_num))
    ((Big.const_mul 744 (qF_big 1)).mono (l := 1) (by norm_num))) (fun τ => by ring)

private lemma jq_bigZ : BigZ 0 (fun τ _ => jF τ * qF τ) := by
  refine BigZ.congr (BigZ.add (BigZ.of_big (jq_sub_one_big.mono (l := 0) (by norm_num)))
    (BigZ.of_big Big.one)) (fun τ z => ?_)
  ring

/-! ### The `x`-atoms are `BigZ 0` -/

private lemma E2x_bigZ : BigZ 0 (fun τ _ : ℍ => E2x (qF τ)) := by
  have h : Big 0 (fun τ => (1 : ℂ) - 24 * qF τ) := by
    have h2 : Big 1 (fun τ => 24 * qF τ) := by
      simpa using Big.const_mul 24 (qF_big 1)
    exact Big.congr (Big.sub Big.one h2) (fun τ => by ring)
  exact BigZ.congr (BigZ.of_big h) (fun τ z => by rw [E2x])

private lemma E4x_bigZ : BigZ 0 (fun τ _ : ℍ => E4x (qF τ)) := by
  have h : Big 0 (fun τ => (1 : ℂ) + 240 * qF τ) := by
    have h2 : Big 1 (fun τ => 240 * qF τ) := by
      simpa using Big.const_mul 240 (qF_big 1)
    exact Big.congr (Big.add Big.one h2) (fun τ => by ring)
  exact BigZ.congr (BigZ.of_big h) (fun τ z => by rw [E4x])

private lemma E6x_bigZ : BigZ 0 (fun τ _ : ℍ => E6x (qF τ)) := by
  have h : Big 0 (fun τ => (1 : ℂ) - 504 * qF τ) := by
    have h2 : Big 1 (fun τ => 504 * qF τ) := by
      simpa using Big.const_mul 504 (qF_big 1)
    exact Big.congr (Big.sub Big.one h2) (fun τ => by ring)
  exact BigZ.congr (BigZ.of_big h) (fun τ z => by rw [E6x])

private lemma psi2x_bigZ (ℓ : Work.Kernels.LogLambdaData) :
    BigZ 0 (fun τ _ : ℍ => psi2x (LamF ℓ τ) (qF τ)) := by
  have h : Big 0 (fun τ => psi2x (LamF ℓ τ) (qF τ)) := by
    have h1 : Big 0 (fun τ => 2 * LamF ℓ τ) := two_lam_big ℓ
    have h2 : Big 0 (fun τ => (48 * LamF ℓ τ + 408) * qF τ) :=
      Big.congr ((Big.mul (Big.add (Big.const_mul 48 (LamF_big ℓ)) (Big.const 408))
        (qF_big 1)).mono (l := 0) (by norm_num)) (fun τ => by ring)
    exact Big.congr (Big.add h1 h2) (fun τ => by rw [psi2x])
  exact BigZ.of_big h

private lemma psi4x_bigZ (ℓ : Work.Kernels.LogLambdaData) :
    BigZ 0 (fun τ _ : ℍ => psi4x (LamF ℓ τ) (qF τ)) := by
  have h : Big 0 (fun τ => psi4x (LamF ℓ τ) (qF τ)) := by
    have h1 : Big 0 (fun τ => 2 * LamF ℓ τ) := two_lam_big ℓ
    refine Big.congr (Big.sub h1 ((Big.mul (Big.add (Big.const_mul 288 (LamF_big ℓ))
      (Big.const 744)) (qF_big 1)).mono (l := 0) (by norm_num))) (fun τ => by rw [psi4x]; ring)
  exact BigZ.of_big h

/-! ### The sharp bound for `A₂ + q·A₁` -/

private lemma Psi2_bigZ (ℓ : Work.Kernels.LogLambdaData) :
    BigZ 2 (fun τ z => Work.Asymptotics.KhatE1Core.KdevA4j2 ℓ τ z
      + qF τ * Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z) := by
  have hr2 : BigZ 2 (fun τ _ : ℍ => E2F τ - E2x (qF τ)) := BigZ.of_big rE2_big
  have hr4 : BigZ 2 (fun τ _ : ℍ => E4F τ - E4x (qF τ)) := BigZ.of_big rE4_big
  have hr6 : BigZ 2 (fun τ _ : ℍ => E6F τ - E6x (qF τ)) := BigZ.of_big rE6_big
  have hrX : BigZ 2 (fun τ _ : ℍ => XF τ - Xx (qF τ)) := BigZ.of_big rX_big
  have hrp2 : BigZ 2 (fun τ _ : ℍ => psi2F ℓ τ - psi2x (LamF ℓ τ) (qF τ)) :=
    BigZ.of_big (rpsi2_big ℓ)
  have hrp4 : BigZ 2 (fun τ _ : ℍ => psi4F ℓ τ - psi4x (LamF ℓ τ) (qF τ)) :=
    BigZ.of_big (rpsi4_big ℓ)
  have t1 : BigZ 2 (fun τ z => (qF τ) ^ 2 * RmF (qF τ) (z : ℂ) (τ : ℂ)
      (Work.Asymptotics.Compact.cuspC ℓ)) :=
    BigZ.mul (BigZ.pow BigZ.q_atom' 2) (RmF_bigZ ℓ)
  have t2 : BigZ 2 (fun τ z => (XF τ - Xx (qF τ))
      * QdF (qF τ) (E2F τ) (psi2F ℓ τ) (z : ℂ) (τ : ℂ)) :=
    BigZ.mul hrX (QdF_bigZ ℓ)
  have t3 : BigZ 2 (fun τ z => (psi2F ℓ τ - psi2x (LamF ℓ τ) (qF τ)) * QpF (qF τ)) :=
    BigZ.mul hrp2 (QpF_bigZ ℓ)
  have t4 : BigZ 2 (fun τ z => (psi4F ℓ τ - psi4x (LamF ℓ τ) (qF τ)) * QsF (qF τ)) :=
    BigZ.mul hrp4 (QsF_bigZ ℓ)
  have t5 : BigZ 2 (fun τ z => AlF (qF τ) (z : ℂ) (τ : ℂ)
      * ((E2F τ - E2x (qF τ)) * (E2F τ + E2x (qF τ)))) :=
    BigZ.mul (AlF_bigZ ℓ) (BigZ.mul hr2 (BigZ.add E2_bigZ E2x_bigZ))
  have t6 : BigZ 2 (fun τ z => BeF (qF τ) (z : ℂ) (τ : ℂ) * (E2F τ - E2x (qF τ))) :=
    BigZ.mul (BeF_bigZ ℓ) hr2
  have t7 : BigZ 2 (fun τ z => GaF (qF τ) (z : ℂ) (τ : ℂ) * (E6F τ - E6x (qF τ))) :=
    BigZ.mul (GaF_bigZ ℓ) hr6
  have t8 : BigZ 2 (fun τ z => DeF (qF τ) (z : ℂ) (Work.Asymptotics.Compact.cuspC ℓ)
      * (E4F τ - E4x (qF τ))) :=
    BigZ.mul (DeF_bigZ ℓ) hr4
  have t9 : BigZ 2 (fun τ z => EpF (qF τ) (z : ℂ) (τ : ℂ)
      * ((E2F τ - E2x (qF τ)) * E4F τ + E2x (qF τ) * (E4F τ - E4x (qF τ)))) :=
    BigZ.mul (EpF_bigZ ℓ) (BigZ.add (BigZ.mul hr2 E4_bigZ) (BigZ.mul E2x_bigZ hr4))
  have h9 : BigZ 2 (fun τ z =>
      (qF τ) ^ 2 * RmF (qF τ) (z : ℂ) (τ : ℂ) (Work.Asymptotics.Compact.cuspC ℓ)
      + (XF τ - Xx (qF τ)) * QdF (qF τ) (E2F τ) (psi2F ℓ τ) (z : ℂ) (τ : ℂ)
      + (psi2F ℓ τ - psi2x (LamF ℓ τ) (qF τ)) * QpF (qF τ)
      + (psi4F ℓ τ - psi4x (LamF ℓ τ) (qF τ)) * QsF (qF τ)
      + AlF (qF τ) (z : ℂ) (τ : ℂ)
          * ((E2F τ - E2x (qF τ)) * (E2F τ + E2x (qF τ)))
      + BeF (qF τ) (z : ℂ) (τ : ℂ) * (E2F τ - E2x (qF τ))
      + GaF (qF τ) (z : ℂ) (τ : ℂ) * (E6F τ - E6x (qF τ))
      + DeF (qF τ) (z : ℂ) (Work.Asymptotics.Compact.cuspC ℓ) * (E4F τ - E4x (qF τ))
      + EpF (qF τ) (z : ℂ) (τ : ℂ)
          * ((E2F τ - E2x (qF τ)) * E4F τ + E2x (qF τ) * (E4F τ - E4x (qF τ)))) :=
    BigZ.add (BigZ.add (BigZ.add (BigZ.add (BigZ.add (BigZ.add (BigZ.add (BigZ.add t1 t2) t3)
      t4) t5) t6) t7) t8) t9
  obtain ⟨C, N, M, hC, hN, hM, h9b⟩ := h9
  refine ⟨C, N, M, hC, hN, hM, fun τ z hτ => ?_⟩
  simp only []
  rw [Psi2_decomp ℓ τ z hτ]
  exact h9b τ z hτ

/-! ## §6  The `j¹`-coefficient, and the assembly -/

private lemma A1_bigZ (ℓ : Work.Kernels.LogLambdaData) :
    BigZ 0 (fun τ z => Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z) := by
  have hPhi : BigZ 0 (fun τ z => Work.Asymptotics.KhatE1Core.Phi4j1 ℓ τ z) := by
    have m1 : BigZ 0 (fun τ _ : ℍ => 984 * E6F τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ)) := by
      refine BigZ.congr (BigZ.const_mul (984 * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)))
        (BigZ.mul E6_bigZ BigZ.tau_atom)) (fun τ z => by ring)
    have m2 : BigZ 0 (fun τ z : ℍ => (-2016) * (z : ℂ) * E6F τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ)) := by
      refine BigZ.congr (BigZ.const_mul ((-2016) * (6 * Complex.I / (Real.pi : ℂ)))
        (BigZ.mul (BigZ.mul BigZ.z_atom E6_bigZ) BigZ.tau_atom)) (fun τ z => by ring)
    have m3 : BigZ 0 (fun τ z : ℍ => 3456 * (z : ℂ) * E4F τ * (6 * Complex.I / (Real.pi : ℂ)) * (τ : ℂ) * E2F τ) := by
      refine BigZ.congr (BigZ.const_mul (3456 * (6 * Complex.I / (Real.pi : ℂ)))
        (BigZ.mul (BigZ.mul (BigZ.mul BigZ.z_atom E4_bigZ) BigZ.tau_atom) E2_bigZ))
        (fun τ z => by ring)
    have m4 : BigZ 0 (fun τ z : ℍ => (-1728) * (z : ℂ) * E4F τ * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ))) := by
      refine BigZ.congr (BigZ.const_mul ((-1728) * (6 * Complex.I / (Real.pi : ℂ)) * (6 * Complex.I / (Real.pi : ℂ)))
        (BigZ.mul BigZ.z_atom E4_bigZ)) (fun τ z => by ring)
    have m5 : BigZ 0 (fun τ z : ℍ => 744 * (z : ℂ) ^ 2 * (τ : ℂ) * E2F τ ^ 2 * XF τ) := by
      refine BigZ.congr (BigZ.const_mul 744
        (BigZ.mul (BigZ.mul (BigZ.mul (BigZ.pow BigZ.z_atom 2) BigZ.tau_atom)
          (BigZ.pow E2_bigZ 2)) X_bigZ)) (fun τ z => by ring)
    have m6 : BigZ 0 (fun τ z : ℍ => (-744) * (z : ℂ) ^ 2 * (6 * Complex.I / (Real.pi : ℂ)) * E2F τ * XF τ) := by
      refine BigZ.congr (BigZ.const_mul ((-744) * (6 * Complex.I / (Real.pi : ℂ)))
        (BigZ.mul (BigZ.mul (BigZ.pow BigZ.z_atom 2) E2_bigZ) X_bigZ)) (fun τ z => by ring)
    have m7 : BigZ 0 (fun τ z : ℍ => 1032 * (z : ℂ) ^ 2 * E6F τ * (τ : ℂ)) := by
      refine BigZ.congr (BigZ.const_mul 1032
        (BigZ.mul (BigZ.mul (BigZ.pow BigZ.z_atom 2) E6_bigZ) BigZ.tau_atom))
        (fun τ z => by ring)
    have m8 : BigZ 0 (fun τ z : ℍ => (-3504) * (z : ℂ) ^ 2 * E4F τ * (τ : ℂ) * E2F τ) := by
      refine BigZ.congr (BigZ.const_mul (-3504)
        (BigZ.mul (BigZ.mul (BigZ.mul (BigZ.pow BigZ.z_atom 2) E4_bigZ) BigZ.tau_atom)
          E2_bigZ)) (fun τ z => by ring)
    have m9 : BigZ 0 (fun τ z : ℍ => 1752 * (z : ℂ) ^ 2 * E4F τ * (6 * Complex.I / (Real.pi : ℂ))) := by
      refine BigZ.congr (BigZ.const_mul (1752 * (6 * Complex.I / (Real.pi : ℂ)))
        (BigZ.mul (BigZ.pow BigZ.z_atom 2) E4_bigZ)) (fun τ z => by ring)
    refine BigZ.congr (BigZ.add (BigZ.add (BigZ.add (BigZ.add (BigZ.add (BigZ.add (BigZ.add
      (BigZ.add m1 m2) m3) m4) m5) m6) m7) m8) m9) (fun τ z => ?_)
    rw [Work.Asymptotics.KhatE1Core.Phi4j1, E6F, E4F, E2F, XF]
    ring
  have hBR : BigZ 0 (fun τ z => Work.Asymptotics.KhatE1Core.BRj1 ℓ τ z) := by
    have m1 : BigZ 0 (fun τ _ : ℍ => (-811008) * psi2F ℓ τ * XF τ) := by
      refine BigZ.congr (BigZ.const_mul (-811008) (BigZ.mul (psi2_bigZ ℓ) X_bigZ))
        (fun τ z => by ring)
    have m2 : BigZ 0 (fun τ _ : ℍ => (-847872) * psi4F ℓ τ) :=
      BigZ.const_mul (-847872) (psi4_bigZ ℓ)
    have m3 : BigZ 0 (fun τ _ : ℍ => (-41472) * E4F τ) := BigZ.const_mul (-41472) E4_bigZ
    have m4 : BigZ 0 (fun τ z : ℍ => 5971968 * XcF ℓ z * E4F τ) :=
      BigZ.congr (BigZ.const_mul 5971968 (BigZ.mul (Xc_bigZ ℓ) E4_bigZ)) (fun τ z => by ring)
    refine BigZ.congr (BigZ.add (BigZ.add (BigZ.add m1 m2) m3) m4) (fun τ z => ?_)
    rw [Work.Asymptotics.KhatE1Core.BRj1, XcF, Work.Asymptotics.Compact.Xc, psi2F, psi4F, E4F, XF]
    ring
  refine BigZ.congr (BigZ.add (BigZ.const_mul (((3456 : ℂ) * (Real.pi : ℂ))
    * (Work.Asymptotics.Compact.tailC)⁻¹) hPhi) hBR) (fun τ z => ?_)
  rw [Work.Asymptotics.KhatE1Core.KdevA4j1]

/-- `Δ ≠ 0` on the funnel. -/
private lemma DeltaFun_ne_zero (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) :
    Work.Kernels.DeltaFun τ ≠ 0 := by
  obtain ⟨cd, hcd, hd⟩ := Work.Asymptotics.exists_Delta_Funnel_lower
  intro h0
  have h1 : cd * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖ := by
    rw [Work.Asymptotics.norm_qParamFun]
    exact hd τ hτ
  rw [h0, norm_zero] at h1
  have h2 : 0 < cd * ‖Work.Kernels.qParamFun τ‖ :=
    mul_pos hcd (norm_pos_iff.mpr (Work.Asymptotics.qParamFun_ne_zero' τ))
  linarith

private lemma one_le_one_add_t {τ : ℍ} {t : ℝ} (ht : τ.im + 1 ≤ t) : (1 : ℝ) ≤ 1 + t := by
  have := τ.im_pos
  linarith


private lemma sc_pow_mul (τ : ℍ) (a b : ℝ) :
    (Work.Kernels.scale τ) ^ a * (Work.Kernels.scale τ) ^ b
      = (Work.Kernels.scale τ) ^ (a + b) := (sc_rpow_add τ a b).symm

private lemma zf_pow_mul (z : ℍ) (a b : ℝ) :
    (1 + ‖(z : ℂ)‖) ^ a * (1 + ‖(z : ℂ)‖) ^ b = (1 + ‖(z : ℂ)‖) ^ (a + b) :=
  (zf_rpow_add z a b).symm

/-- The sharp funnel bound for `KdevA4num = 3456π·KdevA4`. -/
private theorem KdevA4num_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.KdevA4num ℓ τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨Cp, Np, Mp, hCp, hNp, hMp, hPb⟩ := Psi2_bigZ ℓ
  obtain ⟨Ca, Na, Ma, hCa, hNa, hMa, hAb⟩ := A1_bigZ ℓ
  obtain ⟨Cj, Nj, Mj, hCj, hNj, hMj, hJb⟩ := jq_bigZ
  obtain ⟨Cr, Nr, hCr, hNr, hrb⟩ := jq_sub_one_big
  obtain ⟨C0, N0, M0, hC0, hN0, hM0, h0b⟩ := Work.Asymptotics.KhatE1Core.KdevA4j0_bound ℓ
  set N : ℝ := Nj + Nj + Mj + Mj + Np + Na + Nr + N0 + Mp + Ma + M0 + 100 with hN
  have hNge : (0 : ℝ) ≤ N := by
    rw [hN]; linarith [hNj, hNp, hNa, hNr, hN0, hMj, hMp, hMa, hM0]
  have hN1 : Nj + Nj + Np ≤ N := by
    rw [hN]; linarith [hNj, hNp, hNa, hNr, hN0, hMj, hMp, hMa, hM0]
  have hN2 : Nj + Nr + Na ≤ N := by
    rw [hN]; linarith [hNj, hNp, hNa, hNr, hN0, hMj, hMp, hMa, hM0]
  have hN3 : N0 ≤ N := by
    rw [hN]; linarith [hNj, hNp, hNa, hNr, hN0, hMj, hMp, hMa, hM0]
  have hN4 : Mj + Mj + Mp ≤ N := by
    rw [hN]; linarith [hNj, hNp, hNa, hNr, hN0, hMj, hMp, hMa, hM0]
  have hN5 : Mj + Ma ≤ N := by
    rw [hN]; linarith [hNj, hNp, hNa, hNr, hN0, hMj, hMp, hMa, hM0]
  have hN6 : M0 ≤ N := by
    rw [hN]; linarith [hNj, hNp, hNa, hNr, hN0, hMj, hMp, hMa, hM0]
  have hN7 : (0 : ℝ) ≤ Nj + Nj + Np := by linarith [hNj, hNp]
  have hN8 : (0 : ℝ) ≤ Nj + Nr + Na := by linarith [hNj, hNr, hNa]
  have hN9 : (0 : ℝ) ≤ Mj + Mj + Mp := by linarith [hMj, hMp]
  have hN10 : (0 : ℝ) ≤ Mj + Ma := by linarith [hMj, hMa]
  refine ⟨(Cj ^ 2 * Cp + Cj * Cr * Ca + C0) * 3 ^ N + 1, N, N, by positivity, hNge, hNge, ?_⟩
  intro τ z t hτ ht hz1 hz2 hzt
  have hT1 : (1 : ℝ) ≤ 1 + t := one_le_one_add_t ht
  have hTn : (0 : ℝ) ≤ 1 + t := le_trans zero_le_one hT1
  have hsc0 : (0 : ℝ) < Work.Kernels.scale τ := sc_pos τ
  have hqf0 : (0 : ℝ) ≤ ‖qF τ‖ := qn_nonneg τ
  have hzf0 : (0 : ℝ) < 1 + ‖(z : ℂ)‖ := zf_pos z
  have hzf3 : 1 + ‖(z : ℂ)‖ ≤ 3 * (1 + t) := by
    have hzle : ‖(z : ℂ)‖ ≤ 2 * (1 + t) := kdevA4_norm_z_le z t hz1 hz2 hzt
    linarith
  have h31 : (1 : ℝ) ≤ 3 * (1 + t) := by linarith
  have raise : ∀ {A e e' : ℝ}, 0 ≤ A → 0 ≤ e → 0 ≤ e' → e ≤ N → e' ≤ N →
      A * ((Work.Kernels.scale τ) ^ e * (1 + ‖(z : ℂ)‖) ^ e')
        ≤ A * (3 ^ N * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N) := by
    intro A e e' hA he he' heN he'N
    have hs : (Work.Kernels.scale τ) ^ e ≤ (Work.Kernels.scale τ) ^ N := sc_rpow_le τ heN
    have hz1' : (1 + ‖(z : ℂ)‖) ^ e' ≤ (3 * (1 + t)) ^ e' :=
      Real.rpow_le_rpow hzf0.le hzf3 he'
    have hz2' : (3 * (1 + t)) ^ e' ≤ (3 * (1 + t)) ^ N :=
      Real.rpow_le_rpow_of_exponent_le h31 he'N
    have hprod : (Work.Kernels.scale τ) ^ e * (1 + ‖(z : ℂ)‖) ^ e'
        ≤ (Work.Kernels.scale τ) ^ N * (3 * (1 + t)) ^ N :=
      mul_le_mul hs (le_trans hz1' hz2') (Real.rpow_nonneg hzf0.le e') (sc_rpow_nonneg τ N)
    calc A * ((Work.Kernels.scale τ) ^ e * (1 + ‖(z : ℂ)‖) ^ e')
        ≤ A * ((Work.Kernels.scale τ) ^ N * (3 * (1 + t)) ^ N) :=
          mul_le_mul_of_nonneg_left hprod hA
      _ = A * (3 ^ N * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N) := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hTn]
          ring
  have hPs := hPb τ z hτ
  have hAs := hAb τ z hτ
  have hJs := hJb τ z hτ
  have hRs := hrb τ hτ
  have h0s := h0b τ z t hτ ht hz1 hz2 hzt
  simp only [pow_zero, mul_one] at hJs
  simp only [pow_one] at hRs
  simp only [pow_zero, mul_one] at hAs
  have hJ0 : (0 : ℝ) ≤ Cj * (Work.Kernels.scale τ) ^ Nj * (1 + ‖(z : ℂ)‖) ^ Mj :=
    mul_nonneg (mul_nonneg hCj.le (sc_rpow_nonneg τ Nj)) (zf_rpow_nonneg z Mj)
  have hq2 : (0 : ℝ) ≤ ‖qF τ‖ ^ 2 := pow_nonneg hqf0 2
  have hdecomp : (qF τ) ^ 2 * Work.Asymptotics.KhatE1Core.KdevA4num ℓ τ z
      = (jF τ * qF τ) ^ 2
          * (Work.Asymptotics.KhatE1Core.KdevA4j2 ℓ τ z
              + qF τ * Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z)
        - qF τ * (jF τ * qF τ) * (jF τ * qF τ - 1)
            * Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z
        + (qF τ) ^ 2 * Work.Asymptotics.KhatE1Core.KdevA4j0 ℓ τ z := by
    rw [Work.Asymptotics.KhatE1Core.KdevA4num_eq_jdecomp ℓ τ z
      (DeltaFun_ne_zero τ hτ) (Work.Asymptotics.funnel_E4_ne_zero τ hτ)]
    simp only [jF, qF]
    ring
  have hqa : ‖jF τ * qF τ‖ ≤ Cj * (Work.Kernels.scale τ) ^ Nj * (1 + ‖(z : ℂ)‖) ^ Mj := hJs
  -- ## term 1
  have t1 : ‖(jF τ * qF τ) ^ 2
        * (Work.Asymptotics.KhatE1Core.KdevA4j2 ℓ τ z
            + qF τ * Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z)‖
      ≤ Cj ^ 2 * Cp * 3 ^ N * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N * ‖qF τ‖ ^ 2 := by
    have e1 : ‖(jF τ * qF τ) ^ 2
          * (Work.Asymptotics.KhatE1Core.KdevA4j2 ℓ τ z
              + qF τ * Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z)‖
        = ‖(jF τ * qF τ) ^ 2‖
          * ‖Work.Asymptotics.KhatE1Core.KdevA4j2 ℓ τ z
              + qF τ * Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z‖ := norm_mul _ _
    have e2 : ‖(jF τ * qF τ) ^ 2‖ = ‖jF τ * qF τ‖ ^ 2 := norm_pow _ _
    have e3 : ‖jF τ * qF τ‖ ^ 2 = ‖jF τ * qF τ‖ * ‖jF τ * qF τ‖ := pow_two _
    have heq : (Cj * (Work.Kernels.scale τ) ^ Nj * (1 + ‖(z : ℂ)‖) ^ Mj)
          * (Cj * (Work.Kernels.scale τ) ^ Nj * (1 + ‖(z : ℂ)‖) ^ Mj)
          * (Cp * (Work.Kernels.scale τ) ^ Np * (1 + ‖(z : ℂ)‖) ^ Mp * ‖qF τ‖ ^ 2)
        = (Cj ^ 2 * Cp * ((Work.Kernels.scale τ) ^ (Nj + Nj + Np)
            * (1 + ‖(z : ℂ)‖) ^ (Mj + Mj + Mp))) * ‖qF τ‖ ^ 2 := by
      rw [show (Cj * (Work.Kernels.scale τ) ^ Nj * (1 + ‖(z : ℂ)‖) ^ Mj)
            * (Cj * (Work.Kernels.scale τ) ^ Nj * (1 + ‖(z : ℂ)‖) ^ Mj)
            * (Cp * (Work.Kernels.scale τ) ^ Np * (1 + ‖(z : ℂ)‖) ^ Mp * ‖qF τ‖ ^ 2)
          = Cj ^ 2 * Cp * ((Work.Kernels.scale τ) ^ Nj * (Work.Kernels.scale τ) ^ Nj
              * (Work.Kernels.scale τ) ^ Np)
            * ((1 + ‖(z : ℂ)‖) ^ Mj * (1 + ‖(z : ℂ)‖) ^ Mj * (1 + ‖(z : ℂ)‖) ^ Mp)
            * ‖qF τ‖ ^ 2 from by ring]
      rw [sc_pow_mul, sc_pow_mul, zf_pow_mul, zf_pow_mul]
      ring
    calc ‖(jF τ * qF τ) ^ 2
            * (Work.Asymptotics.KhatE1Core.KdevA4j2 ℓ τ z
                + qF τ * Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z)‖
        = ‖jF τ * qF τ‖ * ‖jF τ * qF τ‖
          * ‖Work.Asymptotics.KhatE1Core.KdevA4j2 ℓ τ z
              + qF τ * Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z‖ := by rw [e1, e2, e3]
      _ ≤ (Cj * (Work.Kernels.scale τ) ^ Nj * (1 + ‖(z : ℂ)‖) ^ Mj)
            * (Cj * (Work.Kernels.scale τ) ^ Nj * (1 + ‖(z : ℂ)‖) ^ Mj)
            * (Cp * (Work.Kernels.scale τ) ^ Np * (1 + ‖(z : ℂ)‖) ^ Mp * ‖qF τ‖ ^ 2) :=
          mul_le_mul (mul_le_mul hqa hqa (norm_nonneg _) hJ0) hPs (norm_nonneg _) (by positivity)
      _ = (Cj ^ 2 * Cp * ((Work.Kernels.scale τ) ^ (Nj + Nj + Np)
            * (1 + ‖(z : ℂ)‖) ^ (Mj + Mj + Mp))) * ‖qF τ‖ ^ 2 := heq
      _ ≤ (Cj ^ 2 * Cp * (3 ^ N * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N)) * ‖qF τ‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_right
            (raise (A := Cj ^ 2 * Cp) (e := Nj + Nj + Np) (e' := Mj + Mj + Mp)
              (by positivity) hN7 hN9 hN1 hN4) hq2
      _ = Cj ^ 2 * Cp * 3 ^ N * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N * ‖qF τ‖ ^ 2 := by
          ring
  -- ## term 3
  have t3 : ‖(qF τ) ^ 2 * Work.Asymptotics.KhatE1Core.KdevA4j0 ℓ τ z‖
      ≤ C0 * 3 ^ N * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N * ‖qF τ‖ ^ 2 := by
    have e1 : ‖(qF τ) ^ 2 * Work.Asymptotics.KhatE1Core.KdevA4j0 ℓ τ z‖
        = ‖(qF τ) ^ 2‖ * ‖Work.Asymptotics.KhatE1Core.KdevA4j0 ℓ τ z‖ := norm_mul _ _
    have e2 : ‖(qF τ) ^ 2‖ = ‖qF τ‖ ^ 2 := norm_pow _ _
    have hT : (1 + t) ^ M0 ≤ (1 + t) ^ N := Real.rpow_le_rpow_of_exponent_le hT1 hN6
    have hsN : (Work.Kernels.scale τ) ^ N0 ≤ (Work.Kernels.scale τ) ^ N := sc_rpow_le τ hN3
    have hmid : C0 * (Work.Kernels.scale τ) ^ N0 * (1 + t) ^ M0
        ≤ C0 * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsN hC0.le) hT
        (Real.rpow_nonneg hTn M0) (by positivity)
    have h3 : (1 : ℝ) ≤ 3 ^ N := Real.one_le_rpow (by norm_num) hNge
    have hfin : C0 * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N
        ≤ C0 * 3 ^ N * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N := by
      have h0 : (0 : ℝ) ≤ C0 * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N := by positivity
      nlinarith [h3, h0, hC0.le]
    calc ‖(qF τ) ^ 2 * Work.Asymptotics.KhatE1Core.KdevA4j0 ℓ τ z‖
        = ‖qF τ‖ ^ 2 * ‖Work.Asymptotics.KhatE1Core.KdevA4j0 ℓ τ z‖ := by rw [e1, e2]
      _ ≤ ‖qF τ‖ ^ 2 * (C0 * (Work.Kernels.scale τ) ^ N0 * (1 + t) ^ M0) :=
          mul_le_mul_of_nonneg_left h0s hq2
      _ ≤ ‖qF τ‖ ^ 2 * (C0 * 3 ^ N * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N) :=
          mul_le_mul_of_nonneg_left (le_trans hmid hfin) hq2
      _ = C0 * 3 ^ N * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N * ‖qF τ‖ ^ 2 := by ring
  -- ## term 2
  have t2 : ‖qF τ * (jF τ * qF τ) * (jF τ * qF τ - 1)
        * Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z‖
      ≤ Cj * Cr * Ca * 3 ^ N * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N * ‖qF τ‖ ^ 2 := by
    have hA0 : (0 : ℝ) ≤ Ca * (Work.Kernels.scale τ) ^ Na * (1 + ‖(z : ℂ)‖) ^ Ma :=
      mul_nonneg (mul_nonneg hCa.le (sc_rpow_nonneg τ Na)) (zf_rpow_nonneg z Ma)
    have e1 : ‖qF τ * (jF τ * qF τ) * (jF τ * qF τ - 1)
          * Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z‖
        = ‖qF τ * (jF τ * qF τ) * (jF τ * qF τ - 1)‖
          * ‖Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z‖ := norm_mul _ _
    have e2 : ‖qF τ * (jF τ * qF τ) * (jF τ * qF τ - 1)‖
        = ‖qF τ * (jF τ * qF τ)‖ * ‖jF τ * qF τ - 1‖ := norm_mul _ _
    have e3 : ‖qF τ * (jF τ * qF τ)‖ = ‖qF τ‖ * ‖jF τ * qF τ‖ := norm_mul _ _
    have h1 : ‖qF τ‖ * ‖jF τ * qF τ‖ * ‖jF τ * qF τ - 1‖
        ≤ ‖qF τ‖ * (Cj * (Work.Kernels.scale τ) ^ Nj * (1 + ‖(z : ℂ)‖) ^ Mj)
            * (Cr * (Work.Kernels.scale τ) ^ Nr * ‖qF τ‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hqa hqf0) hRs (norm_nonneg _) (by positivity)
    have heq : (‖qF τ‖ * (Cj * (Work.Kernels.scale τ) ^ Nj * (1 + ‖(z : ℂ)‖) ^ Mj)
            * (Cr * (Work.Kernels.scale τ) ^ Nr * ‖qF τ‖))
          * (Ca * (Work.Kernels.scale τ) ^ Na * (1 + ‖(z : ℂ)‖) ^ Ma)
        = (Cj * Cr * Ca * ((Work.Kernels.scale τ) ^ (Nj + Nr + Na)
            * (1 + ‖(z : ℂ)‖) ^ (Mj + Ma))) * (‖qF τ‖ * ‖qF τ‖) := by
      rw [show (‖qF τ‖ * (Cj * (Work.Kernels.scale τ) ^ Nj * (1 + ‖(z : ℂ)‖) ^ Mj)
              * (Cr * (Work.Kernels.scale τ) ^ Nr * ‖qF τ‖))
            * (Ca * (Work.Kernels.scale τ) ^ Na * (1 + ‖(z : ℂ)‖) ^ Ma)
          = Cj * Cr * Ca * ((Work.Kernels.scale τ) ^ Nj * (Work.Kernels.scale τ) ^ Nr
              * (Work.Kernels.scale τ) ^ Na)
            * ((1 + ‖(z : ℂ)‖) ^ Mj * (1 + ‖(z : ℂ)‖) ^ Ma)
            * (‖qF τ‖ * ‖qF τ‖) from by ring]
      rw [sc_pow_mul, sc_pow_mul, zf_pow_mul]
      ring
    calc ‖qF τ * (jF τ * qF τ) * (jF τ * qF τ - 1)
            * Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z‖
        = ‖qF τ‖ * ‖jF τ * qF τ‖ * ‖jF τ * qF τ - 1‖
          * ‖Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z‖ := by rw [e1, e2, e3]
      _ ≤ (‖qF τ‖ * (Cj * (Work.Kernels.scale τ) ^ Nj * (1 + ‖(z : ℂ)‖) ^ Mj)
            * (Cr * (Work.Kernels.scale τ) ^ Nr * ‖qF τ‖))
          * (Ca * (Work.Kernels.scale τ) ^ Na * (1 + ‖(z : ℂ)‖) ^ Ma) :=
          mul_le_mul h1 hAs (norm_nonneg _) (by positivity)
      _ = (Cj * Cr * Ca * ((Work.Kernels.scale τ) ^ (Nj + Nr + Na)
            * (1 + ‖(z : ℂ)‖) ^ (Mj + Ma))) * (‖qF τ‖ * ‖qF τ‖) := heq
      _ ≤ (Cj * Cr * Ca * (3 ^ N * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N))
            * (‖qF τ‖ * ‖qF τ‖) := by
          refine mul_le_mul_of_nonneg_right
            (raise (A := Cj * Cr * Ca) (e := Nj + Nr + Na) (e' := Mj + Ma)
              (by positivity) hN8 hN10 hN2 hN5) (mul_nonneg hqf0 hqf0)
      _ = Cj * Cr * Ca * 3 ^ N * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N * ‖qF τ‖ ^ 2 := by
          ring
  -- ## assembly
  have hq2ne : (0 : ℝ) < ‖qF τ‖ ^ 2 := pow_pos (by
    rw [norm_pos_iff]; exact Work.Asymptotics.qParamFun_ne_zero' τ) 2
  have hsum : ‖(qF τ) ^ 2 * Work.Asymptotics.KhatE1Core.KdevA4num ℓ τ z‖
      ≤ ((Cj ^ 2 * Cp + Cj * Cr * Ca + C0) * 3 ^ N + 1)
        * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N * ‖qF τ‖ ^ 2 := by
    have hP0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N * (1 + t) ^ N * ‖qF τ‖ ^ 2 := by
      positivity
    have hK : (0 : ℝ) ≤ (Cj ^ 2 * Cp + Cj * Cr * Ca + C0) * 3 ^ N := by positivity
    rw [hdecomp]
    calc ‖(jF τ * qF τ) ^ 2
            * (Work.Asymptotics.KhatE1Core.KdevA4j2 ℓ τ z
                + qF τ * Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z)
          - qF τ * (jF τ * qF τ) * (jF τ * qF τ - 1)
              * Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z
          + (qF τ) ^ 2 * Work.Asymptotics.KhatE1Core.KdevA4j0 ℓ τ z‖
        ≤ ‖(jF τ * qF τ) ^ 2
              * (Work.Asymptotics.KhatE1Core.KdevA4j2 ℓ τ z
                  + qF τ * Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z) -
            qF τ * (jF τ * qF τ) * (jF τ * qF τ - 1)
              * Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z‖
          + ‖(qF τ) ^ 2 * Work.Asymptotics.KhatE1Core.KdevA4j0 ℓ τ z‖ := norm_add_le _ _
      _ ≤ (‖(jF τ * qF τ) ^ 2
              * (Work.Asymptotics.KhatE1Core.KdevA4j2 ℓ τ z
                  + qF τ * Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z)‖
            + ‖qF τ * (jF τ * qF τ) * (jF τ * qF τ - 1)
                * Work.Asymptotics.KhatE1Core.KdevA4j1 ℓ τ z‖)
          + ‖(qF τ) ^ 2 * Work.Asymptotics.KhatE1Core.KdevA4j0 ℓ τ z‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (Cj ^ 2 * Cp * 3 ^ N * ((Work.Kernels.scale τ) ^ N * (1 + t) ^ N * ‖qF τ‖ ^ 2)
            + Cj * Cr * Ca * 3 ^ N * ((Work.Kernels.scale τ) ^ N * (1 + t) ^ N * ‖qF τ‖ ^ 2))
          + C0 * 3 ^ N * ((Work.Kernels.scale τ) ^ N * (1 + t) ^ N * ‖qF τ‖ ^ 2) := by
          refine add_le_add (add_le_add ?_ ?_) ?_
          · simpa only [mul_assoc] using t1
          · simpa only [mul_assoc] using t2
          · simpa only [mul_assoc] using t3
      _ = (Cj ^ 2 * Cp + Cj * Cr * Ca + C0) * 3 ^ N
            * ((Work.Kernels.scale τ) ^ N * (1 + t) ^ N * ‖qF τ‖ ^ 2) := by ring
      _ ≤ ((Cj ^ 2 * Cp + Cj * Cr * Ca + C0) * 3 ^ N + 1)
            * ((Work.Kernels.scale τ) ^ N * (1 + t) ^ N * ‖qF τ‖ ^ 2) := by
          nlinarith [hP0, hK]
      _ = ((Cj ^ 2 * Cp + Cj * Cr * Ca + C0) * 3 ^ N + 1)
            * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N * ‖qF τ‖ ^ 2 := by ring
  rw [norm_mul, norm_pow] at hsum
  have hcomm : ((Cj ^ 2 * Cp + Cj * Cr * Ca + C0) * 3 ^ N + 1)
        * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N * ‖qF τ‖ ^ 2
      = ‖qF τ‖ ^ 2 * (((Cj ^ 2 * Cp + Cj * Cr * Ca + C0) * 3 ^ N + 1)
          * (Work.Kernels.scale τ) ^ N * (1 + t) ^ N) := by ring
  rw [hcomm] at hsum
  exact le_of_mul_le_mul_left hsum hq2ne

/-- **The sharp funnel bound for the `E(z)^4`-coefficient of the sharp funnel residual.** -/
theorem KdevA4Sharp (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.KdevA4 ℓ τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := KdevA4num_bound ℓ
  refine ⟨‖(((3456 : ℂ) * (Real.pi : ℂ))⁻¹)‖ * C + 1, N, M, by positivity, hN, hM, ?_⟩
  intro τ z t hτ ht hz1 hz2 hzt
  have h := hb τ z t hτ ht hz1 hz2 hzt
  have hTn : (0 : ℝ) ≤ 1 + t := le_trans zero_le_one (one_le_one_add_t ht)
  have h0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N * (1 + t) ^ M :=
    mul_nonneg (sc_rpow_nonneg τ N) (Real.rpow_nonneg hTn M)
  have hsplit : Work.Asymptotics.KhatE1Core.KdevA4 ℓ τ z
      = (((3456 : ℂ) * (Real.pi : ℂ))⁻¹) * Work.Asymptotics.KhatE1Core.KdevA4num ℓ τ z := rfl
  rw [hsplit, norm_mul]
  calc ‖(((3456 : ℂ) * (Real.pi : ℂ))⁻¹)‖ * ‖Work.Asymptotics.KhatE1Core.KdevA4num ℓ τ z‖
      ≤ ‖(((3456 : ℂ) * (Real.pi : ℂ))⁻¹)‖ * (C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ ≤ (‖(((3456 : ℂ) * (Real.pi : ℂ))⁻¹)‖ * C + 1)
          * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
        nlinarith [h0, norm_nonneg (((3456 : ℂ) * (Real.pi : ℂ))⁻¹), hC.le]

end
end Work.Asymptotics.KhatE1
