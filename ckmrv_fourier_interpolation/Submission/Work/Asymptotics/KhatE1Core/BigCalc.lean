import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Kernels.Kernels

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-!
# A calculus of `O((scale τ)^N ‖q(τ)‖^k)` on the funnel

`Big k f` records that `f` is `O((scale τ)^N ‖q(τ)‖^k)` for some `N ≥ 0` and some constant,
uniformly on the funnel `Funnel τ` (`τ ∈ DomainD`, `2 ≤ τ.im`).  Here `q(τ) = qParamFun τ`
satisfies `‖q(τ)‖ = e^{-2π τ.im} ≤ 1` on the funnel, while `scale τ = 1 + (τ.im)⁻¹ + ‖τ‖ ≥ 1`,
which makes the exponents behave as expected in `Big.add`/`Big.mul`.

This is the bookkeeping device for the second-order `τ`-atom algebra of the funnel bracket:
the smallness of each explicit atom combination is proved coefficient by coefficient and
recorded as a `Big` statement, and the `E(z)^k`-coefficient bounds follow from the closure
properties below.
-/

/-- `Big k f`: `f = O((scale τ)^N ‖q(τ)‖^k)` on the funnel. -/
def Big (k : ℕ) (f : ℍ → ℂ) : Prop :=
  ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
    ‖f τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ k

namespace Big

lemma qnorm_le_one (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Kernels.qParamFun τ‖ ≤ 1 := by
  rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
  have := hτ.2
  nlinarith [Real.pi_pos]

lemma qnorm_nonneg (τ : ℍ) : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _

lemma scale_pos (τ : ℍ) : (0 : ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ

lemma one_le_scale (τ : ℍ) : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ

lemma nonneg_scale (τ : ℍ) (N : ℝ) : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N :=
  Real.rpow_nonneg (scale_pos τ).le N

lemma nonneg_q (τ : ℍ) (k : ℕ) : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ k :=
  pow_nonneg (qnorm_nonneg τ) k

lemma scale_pow_le {N N' : ℝ} (τ : ℍ) (h : N ≤ N') :
    (Work.Kernels.scale τ) ^ N ≤ (Work.Kernels.scale τ) ^ N' :=
  Real.rpow_le_rpow_of_exponent_le (one_le_scale τ) h

lemma qpow_le_of_le {k l : ℕ} (τ : ℍ) (hτ : Work.Asymptotics.Funnel τ) (h : k ≤ l) :
    ‖Work.Kernels.qParamFun τ‖ ^ l ≤ ‖Work.Kernels.qParamFun τ‖ ^ k :=
  pow_le_pow_of_le_one (qnorm_nonneg τ) (qnorm_le_one τ hτ) h

lemma scale_rpow_add (τ : ℍ) (N M : ℝ) :
    (Work.Kernels.scale τ) ^ (N + M)
      = (Work.Kernels.scale τ) ^ N * (Work.Kernels.scale τ) ^ M :=
  Real.rpow_add (scale_pos τ) N M

/-- Monotonicity in the exponent `k`. -/
lemma mono {k l : ℕ} {f : ℍ → ℂ} (h : Big k f) (hl : l ≤ k) : Big l f := by
  obtain ⟨C, N, hC, hN, hf⟩ := h
  refine ⟨C, N, hC, hN, fun τ hτ => ?_⟩
  refine le_trans (hf τ hτ) ?_
  exact mul_le_mul_of_nonneg_left (qpow_le_of_le τ hτ hl) (mul_nonneg hC.le (nonneg_scale τ N))

/-- A uniform bound gives `Big 0`. -/
lemma of_bdd {f : ℍ → ℂ} {C : ℝ} (hC : 0 < C)
    (h : ∀ τ : ℍ, Work.Asymptotics.Funnel τ → ‖f τ‖ ≤ C) : Big 0 f :=
  ⟨C, 0, hC, le_rfl, fun τ hτ => by simpa using h τ hτ⟩

/-- A uniform `(scale τ)^N` bound gives `Big 0`. -/
lemma of_scale {f : ℍ → ℂ} {C N : ℝ} (hC : 0 < C) (hN : 0 ≤ N)
    (h : ∀ τ : ℍ, Work.Asymptotics.Funnel τ → ‖f τ‖ ≤ C * (Work.Kernels.scale τ) ^ N) :
    Big 0 f :=
  ⟨C, N, hC, hN, fun τ hτ => by simpa using h τ hτ⟩

lemma zero (k : ℕ) : Big k (fun _ : ℍ => (0 : ℂ)) :=
  ⟨1, 0, one_pos, le_rfl, fun τ _ => by simp⟩

lemma const (c : ℂ) : Big 0 (fun _ : ℍ => c) :=
  ⟨‖c‖ + 1, 0, by positivity, le_rfl, fun τ _ => by
    rw [Real.rpow_zero, pow_zero, mul_one, mul_one]
    linarith⟩

lemma one : Big 0 (fun _ : ℍ => (1 : ℂ)) := const 1

lemma congr {k : ℕ} {f g : ℍ → ℂ} (h : Big k f) (hfg : ∀ τ, f τ = g τ) : Big k g := by
  obtain ⟨C, N, hC, hN, hf⟩ := h
  exact ⟨C, N, hC, hN, fun τ hτ => by rw [← hfg τ]; exact hf τ hτ⟩

lemma congr_on {k : ℕ} {f g : ℍ → ℂ} (h : Big k f)
    (hfg : ∀ τ : ℍ, Work.Asymptotics.Funnel τ → f τ = g τ) : Big k g := by
  obtain ⟨C, N, hC, hN, hf⟩ := h
  exact ⟨C, N, hC, hN, fun τ hτ => by rw [← hfg τ hτ]; exact hf τ hτ⟩

lemma neg {k : ℕ} {f : ℍ → ℂ} (h : Big k f) : Big k (fun τ => -f τ) := by
  obtain ⟨C, N, hC, hN, hf⟩ := h
  exact ⟨C, N, hC, hN, fun τ hτ => by rw [norm_neg]; exact hf τ hτ⟩

lemma const_mul (c : ℂ) {k : ℕ} {f : ℍ → ℂ} (h : Big k f) :
    Big k (fun τ => c * f τ) := by
  obtain ⟨C, N, hC, hN, hf⟩ := h
  refine ⟨(‖c‖ + 1) * C, N, by positivity, hN, fun τ hτ => ?_⟩
  rw [norm_mul]
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ k := nonneg_q τ k
  have hs0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N := nonneg_scale τ N
  calc ‖c‖ * ‖f τ‖
      ≤ (‖c‖ + 1) * (C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ k) :=
        mul_le_mul (by linarith) (hf τ hτ) (norm_nonneg (f τ)) (by positivity)
    _ = (‖c‖ + 1) * C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ k := by ring

lemma add {k l : ℕ} {f g : ℍ → ℂ} (hf : Big k f) (hg : Big l g) :
    Big (min k l) (fun τ => f τ + g τ) := by
  obtain ⟨C1, N1, hC1, hN1, hf⟩ := hf
  obtain ⟨C2, N2, hC2, hN2, hg⟩ := hg
  refine ⟨C1 + C2, N1 + N2, by positivity, by positivity, fun τ hτ => ?_⟩
  have h1 := hf τ hτ
  have h2 := hg τ hτ
  have hs0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ (N1 + N2) := nonneg_scale τ _
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ min k l := nonneg_q τ _
  have hqk : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ k := nonneg_q τ k
  have hql : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ l := nonneg_q τ l
  have hA1 : (0 : ℝ) ≤ C1 * (Work.Kernels.scale τ) ^ (N1 + N2) :=
    mul_nonneg hC1.le hs0
  have hA2 : (0 : ℝ) ≤ C2 * (Work.Kernels.scale τ) ^ (N1 + N2) :=
    mul_nonneg hC2.le hs0
  have e1 : C1 * (Work.Kernels.scale τ) ^ N1 * ‖Work.Kernels.qParamFun τ‖ ^ k
      ≤ C1 * (Work.Kernels.scale τ) ^ (N1 + N2) * ‖Work.Kernels.qParamFun τ‖ ^ min k l := by
    have hs : (Work.Kernels.scale τ) ^ N1 ≤ (Work.Kernels.scale τ) ^ (N1 + N2) :=
      scale_pow_le τ (by linarith)
    have hq : ‖Work.Kernels.qParamFun τ‖ ^ k ≤ ‖Work.Kernels.qParamFun τ‖ ^ min k l :=
      qpow_le_of_le τ hτ (min_le_left k l)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hs hC1.le) hq hqk hA1
  have e2 : C2 * (Work.Kernels.scale τ) ^ N2 * ‖Work.Kernels.qParamFun τ‖ ^ l
      ≤ C2 * (Work.Kernels.scale τ) ^ (N1 + N2) * ‖Work.Kernels.qParamFun τ‖ ^ min k l := by
    have hs : (Work.Kernels.scale τ) ^ N2 ≤ (Work.Kernels.scale τ) ^ (N1 + N2) :=
      scale_pow_le τ (by linarith)
    have hq : ‖Work.Kernels.qParamFun τ‖ ^ l ≤ ‖Work.Kernels.qParamFun τ‖ ^ min k l :=
      qpow_le_of_le τ hτ (min_le_right k l)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hs hC2.le) hq hql hA2
  calc ‖f τ + g τ‖ ≤ ‖f τ‖ + ‖g τ‖ := norm_add_le _ _
    _ ≤ C1 * (Work.Kernels.scale τ) ^ (N1 + N2) * ‖Work.Kernels.qParamFun τ‖ ^ min k l
        + C2 * (Work.Kernels.scale τ) ^ (N1 + N2) * ‖Work.Kernels.qParamFun τ‖ ^ min k l :=
        add_le_add (le_trans h1 e1) (le_trans h2 e2)
    _ = (C1 + C2) * (Work.Kernels.scale τ) ^ (N1 + N2)
          * ‖Work.Kernels.qParamFun τ‖ ^ min k l := by ring

lemma sub {k l : ℕ} {f g : ℍ → ℂ} (hf : Big k f) (hg : Big l g) :
    Big (min k l) (fun τ => f τ - g τ) :=
  Big.congr (add hf (neg hg)) (fun τ => by simp [sub_eq_add_neg])

lemma mul {k l : ℕ} {f g : ℍ → ℂ} (hf : Big k f) (hg : Big l g) :
    Big (k + l) (fun τ => f τ * g τ) := by
  obtain ⟨C1, N1, hC1, hN1, hf⟩ := hf
  obtain ⟨C2, N2, hC2, hN2, hg⟩ := hg
  refine ⟨C1 * C2, N1 + N2, by positivity, by positivity, fun τ hτ => ?_⟩
  have h1 := hf τ hτ
  have h2 := hg τ hτ
  have hs0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N2 := nonneg_scale τ N2
  have hs1 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N1 := nonneg_scale τ N1
  have hqk : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ k := nonneg_q τ k
  have hql : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ l := nonneg_q τ l
  have hmain : (0 : ℝ) ≤ C1 * (Work.Kernels.scale τ) ^ N1 * ‖Work.Kernels.qParamFun τ‖ ^ k :=
    mul_nonneg (mul_nonneg hC1.le hs1) hqk
  have hstep := mul_le_mul h1 h2 (norm_nonneg (g τ)) hmain
  have hfac : (C1 * (Work.Kernels.scale τ) ^ N1 * ‖Work.Kernels.qParamFun τ‖ ^ k)
        * (C2 * (Work.Kernels.scale τ) ^ N2 * ‖Work.Kernels.qParamFun τ‖ ^ l)
      = (C1 * C2) * ((Work.Kernels.scale τ) ^ (N1 + N2)) * (‖Work.Kernels.qParamFun τ‖ ^ (k + l)) := by
    rw [scale_rpow_add, pow_add]
    ring
  rw [norm_mul]
  exact le_trans hstep (le_of_eq hfac)

lemma pow {k : ℕ} {f : ℍ → ℂ} (hf : Big k f) (n : ℕ) : Big (k * n) (fun τ => f τ ^ n) := by
  induction n with
  | zero => simpa using (Big.one : Big (k * 0) (fun _ : ℍ => (1 : ℂ)))
  | succ n ih =>
      have h : Big (k * n + k) (fun τ => f τ ^ n * f τ) := mul ih hf
      have h' : Big (k * (n + 1)) (fun τ => f τ ^ n * f τ) := by
        rwa [show k * n + k = k * (n + 1) by ring] at h
      simpa [pow_succ] using h'

end Big

end

end Work.Asymptotics.KhatE1Core
