import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Sm1Split
import Submission.Work.Asymptotics.KhatE1Core.Sm1RefCoeffs
import Submission.Work.Asymptotics.KhatE1Core.DSm4Bound
import Submission.Work.Asymptotics.KhatE1Core.InvE4cubeFourthOrder
import Submission.Work.Asymptotics.KhatE1Core.KPlusQ1
import Submission.Work.Asymptotics.KhatE1Core.Bracket24B7Bound_proof
import Submission.Work.Asymptotics.KhatE1Core.KPlus24Split
import Submission.Work.Asymptotics.KhatE1Core.dSm3_bound
import Submission.Work.Asymptotics.KhatE1Core.DSm5Bound
import Submission.Work.Asymptotics.K24F_sm_sum_bound
import Submission.Work.Asymptotics.K24FZ
import Submission.Work.Asymptotics.K24FBase

/-!
# The `dSm1` row of the `K₊` deviation sum

`dSm1` is the `Sm1`-deviation of `KPlus24Split`,

  `dSm1 = j(τ)·dPhi − (dE4c·Q₁·(q·Δ_ref − 1) + E4Ref³·Q₁·(q·Donly) + dE4c·Q₁·(q·Donly))
            − (E4Ref³·dPhi·Δ_ref + dE4c·W1'·Δ_ref + E4Ref³·W1'·Donly + dE4c·W1'·Donly)`

with `q = qParamFun z` and `Δ_ref = DeltaInvRef z = q⁻¹ + 24` (the `DqRef`-truncated reference
of `Δ(z)⁻¹`).  Together with `dSm2, …, dSm5` it is one of the five rows of
`dKPlusSum = Σ_{i≤5} dSm_i`, and the one row that had not been bounded.

## The bound

  `‖dSm1 τ z‖ ≤ C (scale τ)^N (1+t)^M ‖q(z)‖²`

on the funnel strip `Funnel τ`, `τ.im + 1 ≤ t = z.im`, `0 ≤ z.re ≤ 1`.

Since `‖q(z)‖ ≤ ‖q(τ)‖` on the strip, this implies both normal forms needed downstream:

* (the plan's) `‖dSm1‖ ≤ C (scale τ)^N (1+t)^M (‖q(τ)‖⁻¹ ‖q(z)‖³ + ‖q(z)‖²)`;
* (the `E(z)²`-coefficient form of the split route)
  `‖dSm1‖ ≤ C (scale τ)^N (1+t)^M ‖q(τ)‖ ‖q(z)‖`, i.e. `dSm1 / E(z)² = O(‖q(τ)‖)`.

The second is `dSm1_row_bound_qt` below.

## Method

A *two-exponent* bookkeeping: `Bound2 f n k` means
`‖f τ z‖ ≤ C ‖q(τ)‖^n (scale τ)^N (1+t)^M ‖q(z)‖^k`, with `n`, `k` **integers**, so that the
`q(z)⁻¹` of `DeltaInvRef` and the `‖q(τ)‖⁻¹` of `j(τ)` are admissible.  Sums take the `min` of
the exponents, products their sum, and the two exponents are linked by `‖q(z)‖ ≤ ‖q(τ)‖` on the
strip (`Bound2.shift` trades one power of `‖q(τ)‖` for one of `‖q(z)‖`; it is used exactly once,
on `j(τ)·dPhi`, where `j` contributes `‖q(τ)‖⁻¹` and `dPhi = O(‖q(z)‖³)`).

Every atom is an existing proved funnel bound: `tau_atom_bounds_D` (`r₀, r₁, r₂, R₀, j`),
`q1_le` (`Q₁`), `zS0_norm`, `dE4_bound`, `dE2S_bound`, `dE14_bound`, `InvE4cubeFourthOrder`
(`dI4`), `dE4c_bound`, `Donly_leading`, `phi_sub_phiref_le`.  The eight summands of `dSm1` all
land at the exponents `(0, 2)`.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

/-! ## The two-exponent bound calculus -/

/-- `Bound2 f n k`: `‖f τ z‖ ≤ C ‖q(τ)‖^n (scale τ)^N (1+t)^M ‖q(z)‖^k` on the funnel strip. -/
def Bound2 (f : UpperHalfPlane → UpperHalfPlane → ℂ) (n k : ℤ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
      0 ≤ z.re → z.re ≤ 1 → z.im = t →
      ‖f τ z‖ ≤ C * (‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N
        * (1 + t) ^ M * ‖Work.Kernels.qParamFun z‖ ^ k)

section Basic

lemma qz_norm_le_one {τ z : UpperHalfPlane} {t : ℝ} (hF : Work.Asymptotics.Funnel τ)
    (ht : τ.im + 1 ≤ t) (hz : z.im = t) : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
  rw [Work.Asymptotics.norm_qParamFun, hz, Real.exp_le_one_iff]
  nlinarith [Real.pi_pos, hF.2]

lemma qz_norm_le_qt {τ z : UpperHalfPlane} {t : ℝ} (hF : Work.Asymptotics.Funnel τ)
    (ht : τ.im + 1 ≤ t) (hz : z.im = t) :
    ‖Work.Kernels.qParamFun z‖ ≤ ‖Work.Kernels.qParamFun τ‖ := by
  rw [Work.Asymptotics.norm_qParamFun, Work.Asymptotics.norm_qParamFun, hz]
  exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, ht])

lemma scale_nonneg (τ : UpperHalfPlane) : (0 : ℝ) ≤ Work.Kernels.scale τ :=
  (Work.Kernels.scale_pos τ).le

lemma one_add_t_nonneg {τ : UpperHalfPlane} {t : ℝ} (hF : Work.Asymptotics.Funnel τ)
    (ht : τ.im + 1 ≤ t) : (0 : ℝ) ≤ 1 + t := by
  have := hF.2; linarith

/-- Nonnegativity of the dominating monomial. -/
lemma Bound2.Pnn {τ z : UpperHalfPlane} {t : ℝ} (hF : Work.Asymptotics.Funnel τ)
    (ht : τ.im + 1 ≤ t) (n : ℤ) (N M : ℝ) (k : ℤ) :
    (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
      * ‖Work.Kernels.qParamFun z‖ ^ k :=
  mul_nonneg (mul_nonneg (mul_nonneg (zpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (scale_nonneg τ) _))
      (Real.rpow_nonneg (one_add_t_nonneg hF ht) _))
    (zpow_nonneg (norm_nonneg _) _)

end Basic

/-! ## The calculus -/

/-- Pure re-association shape, stated with *abstract* variables so that `ring` never meets a
`Real.rpow` atom: `C (1 * s^N * u^M * b^k) = C s^N u^M b^k`. -/
lemma Bound2.shape1 (C s u b : ℝ) (N M : ℝ) (k : ℤ) :
    C * (1 * s ^ N * u ^ M * b ^ k) = C * s ^ N * u ^ M * b ^ k := by ring

lemma Bound2.congr {f g : UpperHalfPlane → UpperHalfPlane → ℂ} {n k : ℤ} (h : Bound2 f n k)
    (hfg : ∀ τ z, f τ z = g τ z) : Bound2 g n k := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  exact ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => by
    rw [← hfg τ z]; exact hb τ z t hF ht hz0 hz1 hzim⟩

lemma Bound2.const (c : ℂ) : Bound2 (fun (_ _ : UpperHalfPlane) => c) 0 0 := by
  refine ⟨max ‖c‖ 1, 0, 0, lt_of_lt_of_le zero_lt_one (le_max_right _ _), le_rfl, le_rfl,
    fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h0 : ‖Work.Kernels.qParamFun τ‖ ^ (0 : ℤ) * (Work.Kernels.scale τ) ^ (0 : ℝ)
      * (1 + t) ^ (0 : ℝ) * ‖Work.Kernels.qParamFun z‖ ^ (0 : ℤ) = 1 := by
    simp only [zpow_zero, Real.rpow_zero, mul_one]
  rw [h0, mul_one]
  exact le_max_left _ _

lemma Bound2.neg {f : UpperHalfPlane → UpperHalfPlane → ℂ} {n k : ℤ} (h : Bound2 f n k) :
    Bound2 (fun τ z => -f τ z) n k := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  exact ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => by
    rw [norm_neg]; exact hb τ z t hF ht hz0 hz1 hzim⟩

lemma Bound2.cmul (c : ℂ) {f : UpperHalfPlane → UpperHalfPlane → ℂ} {n k : ℤ}
    (h : Bound2 f n k) : Bound2 (fun τ z => c * f τ z) n k := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨max ‖c‖ 1 * C, N, M, by positivity, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hP := Bound2.Pnn (z := z) hF ht n N M k
  calc ‖c * f τ z‖ = ‖c‖ * ‖f τ z‖ := norm_mul _ _
    _ ≤ ‖c‖ * (C * (‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N
          * (1 + t) ^ M * ‖Work.Kernels.qParamFun z‖ ^ k)) :=
        mul_le_mul_of_nonneg_left (hb τ z t hF ht hz0 hz1 hzim) (norm_nonneg _)
    _ = (‖c‖ * C) * (‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N
          * (1 + t) ^ M * ‖Work.Kernels.qParamFun z‖ ^ k) := by ring
    _ ≤ (max ‖c‖ 1 * C) * (‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N
          * (1 + t) ^ M * ‖Work.Kernels.qParamFun z‖ ^ k) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hC.le) hP

lemma Bound2.mono {f : UpperHalfPlane → UpperHalfPlane → ℂ} {n k n' k' : ℤ}
    (h : Bound2 f n k) (hn : n' ≤ n) (hk : k' ≤ k) : Bound2 f n' k' := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hqp : (0 : ℝ) < ‖Work.Kernels.qParamFun τ‖ := norm_q_pos' τ
  have hzp : (0 : ℝ) < ‖Work.Kernels.qParamFun z‖ := norm_q_pos' z
  have ha : ‖Work.Kernels.qParamFun τ‖ ^ n ≤ ‖Work.Kernels.qParamFun τ‖ ^ n' :=
    zpow_le_zpow_of_le_one hqp (norm_q_le_one' hF) hn
  have hb' : ‖Work.Kernels.qParamFun z‖ ^ k ≤ ‖Work.Kernels.qParamFun z‖ ^ k' :=
    zpow_le_zpow_of_le_one hzp (qz_norm_le_one hF ht hzim) hk
  refine le_trans (hb τ z t hF ht hz0 hz1 hzim) ?_
  have hP : ‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ‖Work.Kernels.qParamFun z‖ ^ k
      ≤ ‖Work.Kernels.qParamFun τ‖ ^ n' * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ‖Work.Kernels.qParamFun z‖ ^ k' :=
    mul4_le' ha (le_refl _) (le_refl _) hb' (zpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (scale_nonneg τ) _) (Real.rpow_nonneg (one_add_t_nonneg hF ht) _)
      (zpow_nonneg (norm_nonneg _) _)
  exact mul_le_mul_of_nonneg_left hP hC.le

lemma Bound2.add {f g : UpperHalfPlane → UpperHalfPlane → ℂ} {m n k l : ℤ}
    (hf : Bound2 f m k) (hg : Bound2 g n l) :
    Bound2 (fun τ z => f τ z + g τ z) (min m n) (min k l) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb1⟩ := hf
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hg
  refine ⟨C1 + C2, max N1 N2, max M1 M2, by linarith,
    le_trans hN1 (le_max_left _ _), le_trans hM1 (le_max_left _ _), ?_⟩
  intro τ z t hF ht hz0 hz1 hzim
  have hqp : (0 : ℝ) < ‖Work.Kernels.qParamFun τ‖ := norm_q_pos' τ
  have hzp : (0 : ℝ) < ‖Work.Kernels.qParamFun z‖ := norm_q_pos' z
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hu1 : (1 : ℝ) ≤ 1 + t := one_le_one_add_t' hF ht
  have hP1 : ‖Work.Kernels.qParamFun τ‖ ^ m * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
        * ‖Work.Kernels.qParamFun z‖ ^ k
      ≤ ‖Work.Kernels.qParamFun τ‖ ^ (min m n) * (Work.Kernels.scale τ) ^ (max N1 N2)
        * (1 + t) ^ (max M1 M2) * ‖Work.Kernels.qParamFun z‖ ^ (min k l) :=
    mul4_le' (zpow_le_zpow_of_le_one hqp (norm_q_le_one' hF) (min_le_left _ _))
      (Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _))
      (Real.rpow_le_rpow_of_exponent_le hu1 (le_max_left _ _))
      (zpow_le_zpow_of_le_one hzp (qz_norm_le_one hF ht hzim) (min_le_left _ _))
      (zpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (scale_nonneg τ) _)
      (Real.rpow_nonneg (one_add_t_nonneg hF ht) _) (zpow_nonneg (norm_nonneg _) _)
  have hP2 : ‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2
        * ‖Work.Kernels.qParamFun z‖ ^ l
      ≤ ‖Work.Kernels.qParamFun τ‖ ^ (min m n) * (Work.Kernels.scale τ) ^ (max N1 N2)
        * (1 + t) ^ (max M1 M2) * ‖Work.Kernels.qParamFun z‖ ^ (min k l) :=
    mul4_le' (zpow_le_zpow_of_le_one hqp (norm_q_le_one' hF) (min_le_right _ _))
      (Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _))
      (Real.rpow_le_rpow_of_exponent_le hu1 (le_max_right _ _))
      (zpow_le_zpow_of_le_one hzp (qz_norm_le_one hF ht hzim) (min_le_right _ _))
      (zpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (scale_nonneg τ) _)
      (Real.rpow_nonneg (one_add_t_nonneg hF ht) _) (zpow_nonneg (norm_nonneg _) _)
  calc ‖f τ z + g τ z‖ ≤ ‖f τ z‖ + ‖g τ z‖ := norm_add_le _ _
    _ ≤ C1 * (‖Work.Kernels.qParamFun τ‖ ^ m * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
          * ‖Work.Kernels.qParamFun z‖ ^ k)
        + C2 * (‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2
          * ‖Work.Kernels.qParamFun z‖ ^ l) :=
        add_le_add (hb1 τ z t hF ht hz0 hz1 hzim) (hb2 τ z t hF ht hz0 hz1 hzim)
    _ ≤ C1 * (‖Work.Kernels.qParamFun τ‖ ^ (min m n) * (Work.Kernels.scale τ) ^ (max N1 N2)
          * (1 + t) ^ (max M1 M2) * ‖Work.Kernels.qParamFun z‖ ^ (min k l))
        + C2 * (‖Work.Kernels.qParamFun τ‖ ^ (min m n) * (Work.Kernels.scale τ) ^ (max N1 N2)
          * (1 + t) ^ (max M1 M2) * ‖Work.Kernels.qParamFun z‖ ^ (min k l)) :=
        add_le_add (mul_le_mul_of_nonneg_left hP1 hC1.le)
          (mul_le_mul_of_nonneg_left hP2 hC2.le)
    _ = (C1 + C2) * (‖Work.Kernels.qParamFun τ‖ ^ (min m n)
          * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
          * ‖Work.Kernels.qParamFun z‖ ^ (min k l)) := by ring

lemma Bound2.sub {f g : UpperHalfPlane → UpperHalfPlane → ℂ} {m n k l : ℤ}
    (hf : Bound2 f m k) (hg : Bound2 g n l) :
    Bound2 (fun τ z => f τ z - g τ z) (min m n) (min k l) :=
  (hf.add hg.neg).congr (fun τ z => by ring)

lemma Bound2.mul {f g : UpperHalfPlane → UpperHalfPlane → ℂ} {m n k l : ℤ}
    (hf : Bound2 f m k) (hg : Bound2 g n l) :
    Bound2 (fun τ z => f τ z * g τ z) (m + n) (k + l) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb1⟩ := hf
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hg
  refine ⟨C1 * C2, N1 + N2, M1 + M2, by positivity, add_nonneg hN1 hN2, add_nonneg hM1 hM2, ?_⟩
  intro τ z t hF ht hz0 hz1 hzim
  have hqp : (0 : ℝ) < ‖Work.Kernels.qParamFun τ‖ := norm_q_pos' τ
  have hzp : (0 : ℝ) < ‖Work.Kernels.qParamFun z‖ := norm_q_pos' z
  have hs : (0 : ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  have hu : (0 : ℝ) < 1 + t := by have := hF.2; linarith
  have hP1 := hb1 τ z t hF ht hz0 hz1 hzim
  calc ‖f τ z * g τ z‖ = ‖f τ z‖ * ‖g τ z‖ := norm_mul _ _
    _ ≤ (C1 * (‖Work.Kernels.qParamFun τ‖ ^ m * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
          * ‖Work.Kernels.qParamFun z‖ ^ k))
        * (C2 * (‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2
          * ‖Work.Kernels.qParamFun z‖ ^ l)) :=
        mul_le_mul hP1 (hb2 τ z t hF ht hz0 hz1 hzim) (norm_nonneg _)
          (le_trans (norm_nonneg _) hP1)
    _ = C1 * C2 * ((‖Work.Kernels.qParamFun τ‖ ^ m * (Work.Kernels.scale τ) ^ N1
          * (1 + t) ^ M1 * ‖Work.Kernels.qParamFun z‖ ^ k)
          * (‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N2
            * (1 + t) ^ M2 * ‖Work.Kernels.qParamFun z‖ ^ l)) := by ring
    _ = C1 * C2 * (‖Work.Kernels.qParamFun τ‖ ^ (m + n) * (Work.Kernels.scale τ) ^ (N1 + N2)
          * (1 + t) ^ (M1 + M2) * ‖Work.Kernels.qParamFun z‖ ^ (k + l)) := by
        rw [show (‖Work.Kernels.qParamFun τ‖ ^ m * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
              * ‖Work.Kernels.qParamFun z‖ ^ k)
              * (‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N2
                * (1 + t) ^ M2 * ‖Work.Kernels.qParamFun z‖ ^ l)
            = (‖Work.Kernels.qParamFun τ‖ ^ m * ‖Work.Kernels.qParamFun τ‖ ^ n)
              * ((Work.Kernels.scale τ) ^ N1 * (Work.Kernels.scale τ) ^ N2)
              * ((1 + t) ^ M1 * (1 + t) ^ M2)
              * (‖Work.Kernels.qParamFun z‖ ^ k * ‖Work.Kernels.qParamFun z‖ ^ l) by ring,
          ← zpow_add₀ (ne_of_gt hqp) m n, ← zpow_add₀ (ne_of_gt hzp) k l,
          ← Real.rpow_add hs N1 N2, ← Real.rpow_add hu M1 M2]

lemma Bound2.shift {f : UpperHalfPlane → UpperHalfPlane → ℂ} {m k : ℤ} (h : Bound2 f m k) :
    Bound2 f (m + 1) (k - 1) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hqp : (0 : ℝ) < ‖Work.Kernels.qParamFun τ‖ := norm_q_pos' τ
  have hzp : (0 : ℝ) < ‖Work.Kernels.qParamFun z‖ := norm_q_pos' z
  have hle : ‖Work.Kernels.qParamFun z‖ ≤ ‖Work.Kernels.qParamFun τ‖ :=
    qz_norm_le_qt hF ht hzim
  have hsk : ‖Work.Kernels.qParamFun z‖ ^ k
      = ‖Work.Kernels.qParamFun z‖ ^ (k - 1) * ‖Work.Kernels.qParamFun z‖ := by
    conv_lhs => rw [show k = (k - 1) + 1 from by ring]
    rw [zpow_add₀ (ne_of_gt hzp) (k - 1) 1, zpow_one]
  have hqm : ‖Work.Kernels.qParamFun τ‖ ^ (m + 1)
      = ‖Work.Kernels.qParamFun τ‖ ^ m * ‖Work.Kernels.qParamFun τ‖ := by
    rw [zpow_add₀ (ne_of_gt hqp) m 1, zpow_one]
  have hmid : ‖Work.Kernels.qParamFun z‖ ^ (k - 1) * ‖Work.Kernels.qParamFun z‖
      ≤ ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖ ^ (k - 1) := by
    calc ‖Work.Kernels.qParamFun z‖ ^ (k - 1) * ‖Work.Kernels.qParamFun z‖
        ≤ ‖Work.Kernels.qParamFun z‖ ^ (k - 1) * ‖Work.Kernels.qParamFun τ‖ :=
          mul_le_mul_of_nonneg_left hle (zpow_nonneg (norm_nonneg _) _)
      _ = ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖ ^ (k - 1) := by ring
  have key : ‖Work.Kernels.qParamFun τ‖ ^ m * ‖Work.Kernels.qParamFun z‖ ^ k
      ≤ ‖Work.Kernels.qParamFun τ‖ ^ (m + 1) * ‖Work.Kernels.qParamFun z‖ ^ (k - 1) := by
    rw [hsk]
    calc ‖Work.Kernels.qParamFun τ‖ ^ m
          * (‖Work.Kernels.qParamFun z‖ ^ (k - 1) * ‖Work.Kernels.qParamFun z‖)
        ≤ ‖Work.Kernels.qParamFun τ‖ ^ m
          * (‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖ ^ (k - 1)) :=
          mul_le_mul_of_nonneg_left hmid (zpow_nonneg (norm_nonneg _) m)
      _ = ‖Work.Kernels.qParamFun τ‖ ^ (m + 1) * ‖Work.Kernels.qParamFun z‖ ^ (k - 1) := by
          rw [hqm]; ring
  refine le_trans (hb τ z t hF ht hz0 hz1 hzim) ?_
  calc C * (‖Work.Kernels.qParamFun τ‖ ^ m * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ‖Work.Kernels.qParamFun z‖ ^ k)
      = C * ((Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * (‖Work.Kernels.qParamFun τ‖ ^ m * ‖Work.Kernels.qParamFun z‖ ^ k)) := by ring
    _ ≤ C * ((Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * (‖Work.Kernels.qParamFun τ‖ ^ (m + 1) * ‖Work.Kernels.qParamFun z‖ ^ (k - 1))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left key
            (mul_nonneg (Real.rpow_nonneg (scale_nonneg τ) _)
              (Real.rpow_nonneg (one_add_t_nonneg hF ht) _))) hC.le
    _ = C * (‖Work.Kernels.qParamFun τ‖ ^ (m + 1) * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ‖Work.Kernels.qParamFun z‖ ^ (k - 1)) := by ring

/-- Build a `Bound2` statement at `(0, K)` from a raw bound
`C (scale τ)^N (1+t)^M ‖q(z)‖^K`. -/
lemma Bound2.of_le_qz {f : UpperHalfPlane → UpperHalfPlane → ℂ} {K : ℕ} {C N M : ℝ}
    (hC : 0 < C) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (h : ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
      0 ≤ z.re → z.re ≤ 1 → z.im = t →
      ‖f τ z‖ ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ‖Work.Kernels.qParamFun z‖ ^ K) : Bound2 f 0 (K : ℤ) := by
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hsimp : C * (‖Work.Kernels.qParamFun τ‖ ^ (0 : ℤ) * (Work.Kernels.scale τ) ^ N
      * (1 + t) ^ M * ‖Work.Kernels.qParamFun z‖ ^ (K : ℤ))
      = C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ‖Work.Kernels.qParamFun z‖ ^ K := by
    rw [show ‖Work.Kernels.qParamFun τ‖ ^ (0 : ℤ) = (1 : ℝ) from zpow_zero _,
      Bound2.shape1 C (Work.Kernels.scale τ) (1 + t) (‖Work.Kernels.qParamFun z‖) N M (K : ℤ)]
    simp only [zpow_natCast]
  rw [hsimp]
  exact h τ z t hF ht hz0 hz1 hzim

/-! ## The atoms -/

theorem Bound2_j : Bound2 (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) =>
    Work.Kernels.jInvariantFun τ) (-1) 0 := by
  obtain ⟨D, hD24, hb⟩ := Work.Asymptotics.K24F.tau_atom_bounds_D
  refine ⟨D, 0, 0, by linarith, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hj : ‖Work.Kernels.jInvariantFun τ‖ ≤ D * Real.exp (2 * Real.pi * τ.im) :=
    (hb τ hF).2.2.2.2.1
  have hexp : Real.exp (2 * Real.pi * τ.im) = (‖Work.Kernels.qParamFun τ‖)⁻¹ := by
    rw [Work.Asymptotics.norm_qParamFun, ← Real.exp_neg]
    ring_nf
  rw [hexp] at hj
  simpa only [zpow_zero, zpow_neg_one, Real.rpow_zero, mul_one, one_mul] using hj

theorem Bound2_r0 : Bound2 (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) =>
    Work.Asymptotics.K24F.r0 τ) 0 0 := by
  obtain ⟨D, hD24, hb⟩ := Work.Asymptotics.K24F.tau_atom_bounds_D
  refine ⟨D, 1, 0, by linarith, by norm_num, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  simpa only [zpow_zero, Real.rpow_one, Real.rpow_zero, mul_one, one_mul] using (hb τ hF).1

theorem Bound2_r1 : Bound2 (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) =>
    Work.Asymptotics.K24F.r1 τ) 0 0 := by
  obtain ⟨D, hD24, hb⟩ := Work.Asymptotics.K24F.tau_atom_bounds_D
  refine ⟨D, 1, 0, by linarith, by norm_num, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  simpa only [zpow_zero, Real.rpow_one, Real.rpow_zero, mul_one, one_mul] using (hb τ hF).2.2.2.1

theorem Bound2_r2 : Bound2 (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) =>
    Work.Asymptotics.K24F.r2 τ) 0 0 := by
  obtain ⟨D, hD24, hb⟩ := Work.Asymptotics.K24F.tau_atom_bounds_D
  refine ⟨D, 1, 0, by linarith, by norm_num, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  simpa only [zpow_zero, Real.rpow_one, Real.rpow_zero, mul_one, one_mul] using (hb τ hF).2.1

theorem Bound2_R0 : Bound2 (fun (τ : UpperHalfPlane) (_ : UpperHalfPlane) =>
    Work.Asymptotics.K24F.R0 τ) 0 0 := by
  obtain ⟨D, hD24, hb⟩ := Work.Asymptotics.K24F.tau_atom_bounds_D
  refine ⟨D, 1, 0, by linarith, by norm_num, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  simpa only [zpow_zero, Real.rpow_one, Real.rpow_zero, mul_one, one_mul] using (hb τ hF).2.2.1

theorem Bound2_Q1 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
    Work.Asymptotics.K24F.Q1 τ z) 0 0 := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.K24Fsm.q1_le
  refine ⟨C, 1, 0, hC, by norm_num, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hz3 : (3 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  simpa only [zpow_zero, Real.rpow_one, Real.rpow_zero, mul_one, one_mul] using hb τ z hF hz3

theorem Bound2_S0 : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
    Work.Asymptotics.K24F.S0 z) 0 0 := by
  refine ⟨3, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hz1' : (1 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  simpa only [zpow_zero, Real.rpow_zero, mul_one] using Work.Asymptotics.K24F.zS0_norm z hz1'

theorem Bound2_E4Ref : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) => E4Ref z) 0 0 := by
  refine ⟨2401, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hz1' : (1 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  simpa only [zpow_zero, Real.rpow_zero, mul_one] using norm_E4Ref_le hz1'

theorem Bound2_E4Ref3 : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
    E4Ref z ^ 3) 0 0 :=
  ((Bound2_E4Ref.mul Bound2_E4Ref).mul Bound2_E4Ref).congr (fun τ z => by ring)

theorem Bound2_E2SRef : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
    E2SRef z) 0 0 := by
  refine ⟨99, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hz1' : (1 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  simpa only [zpow_zero, Real.rpow_zero, mul_one] using norm_E2SRef_le hz1'

theorem Bound2_E14Ref : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
    E14Ref z) 0 0 := by
  have hmain : ∀ z : UpperHalfPlane, 1 ≤ z.im → ‖E14Ref z‖ ≤ 196657 := by
    intro z hz
    set q := Work.Kernels.qParamFun z with hq
    have hq1 : ‖q‖ ≤ 1 := by
      rw [hq, Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
      nlinarith [Real.pi_pos, hz]
    have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg _
    have hq2 : ‖q‖ ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
    have hkey : E14Ref z = 1 - 24 * q - 196632 * q ^ 2 := by simp only [E14Ref, hq]
    rw [hkey]
    have h2 : ‖(196632 : ℂ) * q ^ 2‖ = 196632 * ‖q‖ ^ 2 := by rw [norm_mul, norm_pow]; norm_num
    have h4 : ‖(24 : ℂ) * q‖ = 24 * ‖q‖ := by rw [norm_mul]; norm_num
    have h1 := norm_sub_le ((1 : ℂ) - 24 * q) ((196632 : ℂ) * q ^ 2)
    have h0 := norm_sub_le (1 : ℂ) ((24 : ℂ) * q)
    rw [h2] at h1
    rw [h4, norm_one] at h0
    linarith
  exact Bound2.of_le_qz (K := 0) (C := 196657) (N := 0) (M := 0) (by norm_num) le_rfl le_rfl
    (fun τ z t hF ht hz0 hz1 hzim => by
      have hz1' : (1 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
      simpa using hmain z hz1')

theorem Bound2_I4Ref : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) => I4Ref z) 0 0 := by
  have hmain : ∀ z : UpperHalfPlane, 1 ≤ z.im → ‖I4Ref z‖ ≤ 339841 := by
    intro z hz
    set q := Work.Kernels.qParamFun z with hq
    have hq1 : ‖q‖ ≤ 1 := by
      rw [hq, Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
      nlinarith [Real.pi_pos, hz]
    have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg _
    have hq2 : ‖q‖ ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
    have hkey : I4Ref z = 1 - 720 * q + 339120 * q ^ 2 := by simp only [I4Ref, hq]
    rw [hkey]
    have h2 : ‖(339120 : ℂ) * q ^ 2‖ = 339120 * ‖q‖ ^ 2 := by rw [norm_mul, norm_pow]; norm_num
    have h4 : ‖(720 : ℂ) * q‖ = 720 * ‖q‖ := by rw [norm_mul]; norm_num
    have h1 := norm_add_le ((1 : ℂ) - 720 * q) ((339120 : ℂ) * q ^ 2)
    have h0 := norm_sub_le (1 : ℂ) ((720 : ℂ) * q)
    rw [h2] at h1
    rw [h4, norm_one] at h0
    linarith
  exact Bound2.of_le_qz (K := 0) (C := 339841) (N := 0) (M := 0) (by norm_num) le_rfl le_rfl
    (fun τ z t hF ht hz0 hz1 hzim => by
      have hz1' : (1 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
      simpa using hmain z hz1')

theorem Bound2_dE4 : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) => dE4 z) 0 3 := by
  obtain ⟨C, hC, hb⟩ := dE4_bound
  exact Bound2.of_le_qz (K := 3) (C := C) (N := 0) (M := 0) hC le_rfl le_rfl
    (fun τ z t hF ht hz0 hz1 hzim => by
      have hz1' : (1 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
      simpa using hb z hz1')

theorem Bound2_dE2S : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) => dE2S z) 0 3 := by
  obtain ⟨C, hC, hb⟩ := dE2S_bound
  exact Bound2.of_le_qz (K := 3) (C := C) (N := 0) (M := 0) hC le_rfl le_rfl
    (fun τ z t hF ht hz0 hz1 hzim => by
      have hz1' : (1 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
      simpa using hb z hz1')

theorem Bound2_dE14 : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) => dE14 z) 0 3 := by
  obtain ⟨C, hC, hb⟩ := dE14_bound
  exact Bound2.of_le_qz (K := 3) (C := C) (N := 0) (M := 0) hC le_rfl le_rfl
    (fun τ z t hF ht hz0 hz1 hzim => by
      have hz1' : (1 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
      simpa using hb z hz1')

theorem Bound2_dI4 : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) => dI4 z) 0 3 := by
  obtain ⟨C, hC, hb⟩ := InvE4cubeFourthOrder
  exact Bound2.of_le_qz (K := 3) (C := C) (N := 0) (M := 0) hC le_rfl le_rfl
    (fun τ z t hF ht hz0 hz1 hzim => by
      have hz3 : (3 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
      have h := hb z hz3
      have hd : dI4 z = (Work.Kernels.E4Fun z)⁻¹ ^ 3
          - (1 - 720 * Work.Kernels.qParamFun z
              + 339120 * Work.Kernels.qParamFun z ^ 2) := by
        simp only [dI4, I4Ref]
      rw [hd]
      simpa using h)

theorem Bound2_dE4c : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) => dE4c z) 0 3 := by
  obtain ⟨C, hC, hb⟩ := dE4c_bound
  exact Bound2.of_le_qz (K := 3) (C := C) (N := 0) (M := 0) hC le_rfl le_rfl
    (fun τ z t hF ht hz0 hz1 hzim => by
      have hz1' : (1 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
      simpa using hb z hz1')

theorem Bound2_E2S : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
    Work.Kernels.E2S z) 0 0 := by
  obtain ⟨C, hC, hb⟩ := dE2S_bound
  refine ⟨99 + C, 0, 0, by positivity, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  dsimp only
  have hz1' : (1 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  have h1 : ‖E2SRef z‖ ≤ 99 := norm_E2SRef_le hz1'
  have h2 : ‖dE2S z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := hb z hz1'
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := qz_norm_le_one hF ht hzim
  have hq3 : ‖Work.Kernels.qParamFun z‖ ^ 3 ≤ 1 := pow_le_one₀ hq0 hq1
  rw [E2S_ref_split z]
  refine le_trans (norm_add_le _ _) ?_
  simp only [zpow_zero, Real.rpow_zero, mul_one, one_mul]
  nlinarith [h1, h2, hq3, hC.le, hq0]

theorem Bound2_qparam : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
    Work.Kernels.qParamFun z) 0 1 := by
  refine ⟨1, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  dsimp only
  simp only [zpow_zero, zpow_one, Real.rpow_zero, mul_one, one_mul]
  exact le_rfl

theorem Bound2_Donly : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) => Donly z) 0 1 := by
  obtain ⟨C, hC, hb⟩ := Donly_leading
  refine ⟨C + 324, 0, 0, by positivity, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  dsimp only
  have hz1' : (1 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  have h1 : ‖Donly z - 324 * Work.Kernels.qParamFun z‖
      ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 2 := hb z hz1'
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := qz_norm_le_one hF ht hzim
  have h324 : ‖(324 : ℂ) * Work.Kernels.qParamFun z‖ = 324 * ‖Work.Kernels.qParamFun z‖ := by
    rw [norm_mul]; norm_num
  have he : Donly z = (Donly z - 324 * Work.Kernels.qParamFun z)
      + 324 * Work.Kernels.qParamFun z := by ring
  rw [he]
  refine le_trans (norm_add_le _ _) ?_
  rw [h324]
  simp only [zpow_zero, zpow_one, Real.rpow_zero, mul_one, one_mul]
  have hb2b : ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ ‖Work.Kernels.qParamFun z‖ := by
    nlinarith [hq0, hq1]
  have hCb : C * ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ C * ‖Work.Kernels.qParamFun z‖ :=
    mul_le_mul_of_nonneg_left hb2b hC.le
  linarith [h1, hCb]

theorem Bound2_DeltaInvRef : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
    DeltaInvRef z) 0 (-1) := by
  refine ⟨25, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  dsimp only
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := qz_norm_le_one hF ht hzim
  have hpos : (0 : ℝ) < ‖Work.Kernels.qParamFun z‖ := norm_q_pos' z
  have hinv : (1 : ℝ) ≤ (‖Work.Kernels.qParamFun z‖)⁻¹ := (one_le_inv₀ hpos).mpr hq1
  have hkey : DeltaInvRef z = (Work.Kernels.qParamFun z)⁻¹ + 24 := by
    simp only [DeltaInvRef]
  rw [hkey]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_inv, show ‖(24 : ℂ)‖ = (24 : ℝ) from by norm_num]
  simp only [zpow_zero, zpow_neg_one, Real.rpow_zero, mul_one, one_mul]
  have h24 : (24 : ℝ) ≤ 24 * (‖Work.Kernels.qParamFun z‖)⁻¹ := by nlinarith [hinv]
  linarith

/-! ## The composed atoms -/

theorem Bound2_dQ2 : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) => dQ2 z) 0 3 := by
  have h1 : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
      (2 : ℂ) * E2SRef z * dE2S z) 0 3 :=
    ((Bound2.const (2 : ℂ)).mul Bound2_E2SRef).mul Bound2_dE2S
  have h2 : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
      dE2S z * dE2S z) 0 6 := Bound2_dE2S.mul Bound2_dE2S
  have h2' := h2.mono (le_refl (0 : ℤ)) (by norm_num : (3 : ℤ) ≤ 6)
  exact (h1.add h2').congr (fun τ z => by simp only [dQ2]; ring)

theorem Bound2_dQ4 : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) => dQ4 z) 0 3 := by
  have h1 : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) => (6 : ℂ) * dE4 z) 0 3 :=
    (Bound2.const (6 : ℂ)).mul Bound2_dE4
  have h2 : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
      (12 : ℂ) * E2SRef z * dE2S z) 0 3 :=
    ((Bound2.const (12 : ℂ)).mul Bound2_E2SRef).mul Bound2_dE2S
  have h3 : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) =>
      (6 : ℂ) * (dE2S z * dE2S z)) 0 6 :=
    (Bound2.const (6 : ℂ)).mul (Bound2_dE2S.mul Bound2_dE2S)
  have h3' := h3.mono (le_refl (0 : ℤ)) (by norm_num : (3 : ℤ) ≤ 6)
  exact ((h1.sub h2).sub h3').congr (fun τ z => by simp only [dQ4]; ring)

theorem Bound2_dPfun : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) => dPfun τ z) 0 3 := by
  have h1 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      (Work.Asymptotics.K24F.r0 τ + Work.Asymptotics.K24F.r2 τ) * dQ4 z) 0 3 :=
    (Bound2_r0.add Bound2_r2).mul Bound2_dQ4
  have h2 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      ((-12 : ℂ) * Work.Asymptotics.K24F.R0 τ
        + 8640 * Work.Asymptotics.K24F.r1 τ) * dE4 z) 0 3 :=
    ((Bound2_R0.cmul (-12)).add (Bound2_r1.cmul 8640)).mul Bound2_dE4
  have h3 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      ((12 : ℂ) * Work.Asymptotics.K24F.R0 τ
        - 12096 * Work.Asymptotics.K24F.r1 τ) * dQ2 z) 0 3 :=
    (((Bound2_R0.cmul 12).add (Bound2_r1.cmul (-12096))).mul Bound2_dQ2).congr
      (fun τ z => by ring)
  exact ((h1.add h2).add h3).congr (fun τ z => by
    simp only [dPfun]
    rw [← Work.Asymptotics.K24F.r1_mul_j τ]
    ring)

theorem Bound2_dVfun : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) => dVfun τ z) 0 3 :=
  (((Bound2.const (-3456 : ℂ)).mul Bound2_r1).mul
    ((Bound2_dE14.mul Bound2_E2S).add (Bound2_E14Ref.mul Bound2_dE2S))).congr
    (fun τ z => by simp only [dVfun])

theorem Bound2_VfunRef : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
    VfunRef τ z) 0 0 :=
  ((((Bound2.const (-3456 : ℂ)).mul Bound2_r1).mul Bound2_E14Ref).mul Bound2_E2SRef).congr
    (fun τ z => by simp only [VfunRef])

theorem Bound2_dPhi : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) => dPhi τ z) 0 3 :=
  (Bound2.sub Bound2_dPfun
    (Bound2.add (Bound2.add (Bound2_VfunRef.mul Bound2_dI4)
        (Bound2_dVfun.mul Bound2_I4Ref))
      (Bound2_dVfun.mul Bound2_dI4))).congr
    (fun τ z => by simp only [dPhi])

theorem Bound2_Phi_sub_Phiref : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
    Work.Asymptotics.K24F.Phi τ z - Work.Asymptotics.K24F.Phiref τ z) 0 1 := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.phi_sub_phiref_le
  refine Bound2.of_le_qz (K := 1) (C := C) (N := 1) (M := 0) hC (by norm_num) le_rfl ?_
  intro τ z t hF ht hz0 hz1 hzim
  have hz3 : (3 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  have h := hb τ z hF hz3
  rw [show Work.Kernels.scale τ ^ (1 : ℝ) = Work.Kernels.scale τ from Real.rpow_one _]
  simpa using h

theorem Bound2_PhiRef_sub_Phiref : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
    PhiRef τ z - Work.Asymptotics.K24F.Phiref τ z) 0 1 := by
  have h := Bound2_Phi_sub_Phiref.sub Bound2_dPhi
  exact h.congr (fun τ z => by
    rw [Phi_eq_ref_add τ z]; ring)

theorem Bound2_W0' : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) => W0' τ z) 0 1 :=
  (Bound2_PhiRef_sub_Phiref.sub (Bound2_qparam.mul Bound2_Q1)).congr
    (fun τ z => by simp only [W0'])

theorem Bound2_W1' : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) => W1' τ z) 0 1 :=
  (Bound2_W0'.add Bound2_dPhi).congr (fun τ z => (W1'_eq τ z).symm)

/-! ## `dSm1` -/

theorem Bound2_dSm1 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) => dSm1 τ z) 0 2 := by
  have hA : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      Work.Kernels.jInvariantFun τ * dPhi τ z) 0 2 := (Bound2_j.mul Bound2_dPhi).shift
  have hB1 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      dE4c z * Work.Asymptotics.K24F.Q1 τ z
        * (Work.Kernels.qParamFun z * DeltaInvRef z - 1)) 0 3 :=
    (Bound2_dE4c.mul Bound2_Q1).mul
      ((Bound2_qparam.mul Bound2_DeltaInvRef).sub (Bound2.const 1))
  have hB2 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      E4Ref z ^ 3 * Work.Asymptotics.K24F.Q1 τ z
        * (Work.Kernels.qParamFun z * Donly z)) 0 2 :=
    (Bound2_E4Ref3.mul Bound2_Q1).mul (Bound2_qparam.mul Bound2_Donly)
  have hB3 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      dE4c z * Work.Asymptotics.K24F.Q1 τ z
        * (Work.Kernels.qParamFun z * Donly z)) 0 5 :=
    (Bound2_dE4c.mul Bound2_Q1).mul (Bound2_qparam.mul Bound2_Donly)
  have hB3' := hB3.mono (le_refl (0 : ℤ)) (by norm_num : (2 : ℤ) ≤ 5)
  have hC1 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      E4Ref z ^ 3 * dPhi τ z * DeltaInvRef z) 0 2 :=
    (Bound2_E4Ref3.mul Bound2_dPhi).mul Bound2_DeltaInvRef
  have hC2 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      dE4c z * W1' τ z * DeltaInvRef z) 0 3 :=
    (Bound2_dE4c.mul Bound2_W1').mul Bound2_DeltaInvRef
  have hC3 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      E4Ref z ^ 3 * W1' τ z * Donly z) 0 2 :=
    (Bound2_E4Ref3.mul Bound2_W1').mul Bound2_Donly
  have hC4 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      dE4c z * W1' τ z * Donly z) 0 5 :=
    (Bound2_dE4c.mul Bound2_W1').mul Bound2_Donly
  have hC4' := hC4.mono (le_refl (0 : ℤ)) (by norm_num : (2 : ℤ) ≤ 5)
  exact ((hA.sub (hB1.add (hB2.add hB3'))).sub
    (hC1.add (hC2.add (hC3.add hC4')))).congr
    (fun τ z => by simp only [dSm1]; ring)

/-- **The `dSm1` row bound, `‖q(z)‖²` form.** -/
theorem dSm1_row_bound :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖dSm1 τ z‖ ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ :=
    (Bound2_dSm1 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) => dSm1 τ z) 0 2)
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h := hb τ z t hF ht hz0 hz1 hzim
  have hconv : C * (‖Work.Kernels.qParamFun τ‖ ^ (0 : ℤ) * (Work.Kernels.scale τ) ^ N
      * (1 + t) ^ M * ‖Work.Kernels.qParamFun z‖ ^ (2 : ℤ))
      = C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
    rw [show ‖Work.Kernels.qParamFun τ‖ ^ (0 : ℤ) = (1 : ℝ) from zpow_zero _,
      Bound2.shape1 C (Work.Kernels.scale τ) (1 + t) (‖Work.Kernels.qParamFun z‖) N M (2 : ℤ)]
    rfl
  rw [hconv] at h
  exact h

/-- **The `dSm1` row bound, `‖q(τ)‖·‖q(z)‖` form** (what the `E(z)²`-coefficient part of the
split route needs, since `‖q(z)‖ = ‖Ept z‖²`). -/
theorem dSm1_row_bound_qt :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖dSm1 τ z‖ ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖ := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ :=
    (Bound2_dSm1 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) => dSm1 τ z) 0 2)
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h := hb τ z t hF ht hz0 hz1 hzim
  have hconv : C * (‖Work.Kernels.qParamFun τ‖ ^ (0 : ℤ) * (Work.Kernels.scale τ) ^ N
      * (1 + t) ^ M * ‖Work.Kernels.qParamFun z‖ ^ (2 : ℤ))
      = C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
    rw [show ‖Work.Kernels.qParamFun τ‖ ^ (0 : ℤ) = (1 : ℝ) from zpow_zero _,
      Bound2.shape1 C (Work.Kernels.scale τ) (1 + t) (‖Work.Kernels.qParamFun z‖) N M (2 : ℤ)]
    rfl
  rw [hconv] at h
  have hqz0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hle : ‖Work.Kernels.qParamFun z‖ ≤ ‖Work.Kernels.qParamFun τ‖ :=
    qz_norm_le_qt hF ht hzim
  have hsc : (0 : ℝ) ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M :=
    mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (scale_nonneg τ) _))
      (Real.rpow_nonneg (one_add_t_nonneg hF ht) _)
  calc ‖dSm1 τ z‖ ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ‖Work.Kernels.qParamFun z‖ ^ 2 := h
    _ ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * (‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖) := by
        refine mul_le_mul_of_nonneg_left ?_ hsc
        nlinarith [hle, hqz0]
    _ = C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖ := by ring

/-! ## The `dSm2` row (and its atoms)

`dSm2 = -j(τ)·Φ_ref·dDq - E4Ref³·Φ_ref·Donly - dE4c·Φ_ref·Donly` (`Sm2Split.lean`).  The
first summand carries the `‖q(τ)‖⁻¹` of `j(τ)` times the `q(z)³` of `dDq`, and the other two are
`O(q(z))` resp. `O(q(z)⁴)` (the `Δ⁻¹`-deviation `Donly` is `O(q(z))`), so the row is
`O(‖q(τ)‖⁻¹ ‖q(z)‖)`. -/

/-- `Φ_ref = O(scale τ)` on the funnel strip. -/
theorem Bound2_Phiref : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
    Work.Asymptotics.K24F.Phiref τ z) 0 0 := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.K24Fsm.phiref_le
  refine Bound2.of_le_qz (K := 0) (C := C) (N := 1) (M := 0) hC (by norm_num) le_rfl ?_
  intro τ z t hF ht hz0 hz1 hzim
  have hz3 : (3 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
  rw [Real.rpow_one, Real.rpow_zero, mul_one]
  simpa using hb τ z hF hz3

/-- `dDq = Δ(z)/q(z) - (1 - 24q + 252q²) = O(q(z)³)`. -/
theorem Bound2_dDq : Bound2 (fun (_ : UpperHalfPlane) (z : UpperHalfPlane) => dDq z) 0 3 := by
  obtain ⟨C, hC, hb⟩ := dDq_bound
  exact Bound2.of_le_qz (K := 3) (C := C) (N := 0) (M := 0) hC le_rfl le_rfl
    (fun τ z t hF ht hz0 hz1 hzim => by
      have hz1' : (1 : ℝ) ≤ z.im := by have := hF.2; rw [hzim]; linarith
      simpa using hb z hz1')

/-- **The `dSm2` row, `(-1, 1)` form.** -/
theorem Bound2_dSm2 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) => dSm2 τ z) (-1) 1 := by
  have h1 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      Work.Kernels.jInvariantFun τ * Work.Asymptotics.K24F.Phiref τ z * dDq z) (-1) 3 :=
    (Bound2_j.mul Bound2_Phiref).mul Bound2_dDq
  have h2 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      E4Ref z ^ 3 * Work.Asymptotics.K24F.Phiref τ z * Donly z) 0 1 :=
    (Bound2_E4Ref3.mul Bound2_Phiref).mul Bound2_Donly
  have h3 : Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) =>
      dE4c z * Work.Asymptotics.K24F.Phiref τ z * Donly z) 0 4 :=
    (Bound2_dE4c.mul Bound2_Phiref).mul Bound2_Donly
  exact (h1.neg.sub (h2.add h3)).congr (fun τ z => by simp only [dSm2])

/-- **The `dSm2` row bound.** -/
theorem dSm2_row_bound :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖dSm2 τ z‖ ≤ C * (‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ N
          * (1 + t) ^ M * ‖Work.Kernels.qParamFun z‖ := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := Bound2_dSm2
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h := hb τ z t hF ht hz0 hz1 hzim
  rw [show ‖Work.Kernels.qParamFun τ‖ ^ (-1 : ℤ) = (‖Work.Kernels.qParamFun τ‖)⁻¹
      from zpow_neg_one _] at h
  rw [show ‖Work.Kernels.qParamFun z‖ ^ (1 : ℤ) = ‖Work.Kernels.qParamFun z‖
      from zpow_one _] at h
  simpa only [mul_assoc] using h

/-! ## The remaining `K₊` rows in `Bound2` form

The rows `dSm3`, `dSm4`, `dSm5` were already bounded in the workspace (`dSm3_bound`,
`DSm4Bound.dSm4_bound`, `DSm5Bound.dSm5_bound`); here we convert those statements to the
`Bound2` normal form and assemble the whole deviation sum

  `dKPlusSum = dSm1 + dSm2 + dSm3 + dSm4 + dSm5`
  (`KPlus24Split.lean`), whose bound is the `K₊`-half input of the `E(z)`-split of
  `Bracket24TailCore`. -/

/-- Shape conversion: `C a^n s^N u^M b^k` (the `Bound2` normal form) against the ordering
`C s^N u^M a^n b^k` used by the raw row statements. -/
lemma Bound2.shapeC (C a s u b : ℝ) (N M : ℝ) (k : ℤ) :
    C * (a ^ (-1 : ℤ) * s ^ N * u ^ M * b ^ k) = C * s ^ N * u ^ M * a⁻¹ * b ^ k := by
  rw [zpow_neg_one]
  ring

/-- Shape conversion against the ordering `C a⁻¹ b^k s^N u^M` of `dSm5_bound`. -/
lemma Bound2.shapeD (C a s u b : ℝ) (N M : ℝ) (k : ℤ) :
    C * (a ^ (-1 : ℤ) * s ^ N * u ^ M * b ^ k) = C * a⁻¹ * b ^ k * s ^ N * u ^ M := by
  rw [zpow_neg_one]
  ring

theorem Bound2_dSm3 :
    Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) => dSm3 τ z) (-1) 3 := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := dSm3_bound
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  rw [Bound2.shapeC C (‖Work.Kernels.qParamFun τ‖) (Work.Kernels.scale τ) (1 + t)
    (‖Work.Kernels.qParamFun z‖) N M (3 : ℤ)]
  exact hb τ z t hF ht hz0 hz1 hzim

theorem Bound2_dSm4 (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) => dSm4 τ z) 0 3 := by
  obtain ⟨C, N, hC, hN, hb⟩ := dSm4_bound ℓ
  refine ⟨C, N, 0, hC, hN, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h := hb τ z t hF ht hz0 hz1 hzim
  rw [show ‖Work.Kernels.qParamFun τ‖ ^ (0 : ℤ) = (1 : ℝ) from zpow_zero _,
    show (1 + t) ^ (0 : ℝ) = (1 : ℝ) from Real.rpow_zero _]
  simp only [one_mul, mul_one]
  rw [← mul_assoc]
  exact h

theorem Bound2_dSm5 (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) => dSm5 τ z) (-1) 3 := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := dSm5_bound ℓ
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  rw [Bound2.shapeD C (‖Work.Kernels.qParamFun τ‖) (Work.Kernels.scale τ) (1 + t)
    (‖Work.Kernels.qParamFun z‖) N M (3 : ℤ)]
  exact hb τ z t hF ht hz0 hz1 hzim

/-- **The whole `K₊` deviation sum** `dKPlusSum = dSm1 + … + dSm5`. -/
theorem Bound2_dKPlusSum (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun (τ : UpperHalfPlane) (z : UpperHalfPlane) => dKPlusSum τ z) (-1) 1 := by
  have h := (((Bound2_dSm1.add Bound2_dSm2).add Bound2_dSm3).add (Bound2_dSm4 ℓ)).add
    (Bound2_dSm5 ℓ)
  exact h.congr (fun τ z => by simp only [dKPlusSum])

/-- **The `K₊` deviation-sum bound**: `‖dKPlusSum τ z‖ ≤ C ‖q(τ)‖⁻¹ (scale τ)^N (1+t)^M ‖q(z)‖`. -/
theorem dKPlusSum_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖dKPlusSum τ z‖ ≤ C * (‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ N
          * (1 + t) ^ M * ‖Work.Kernels.qParamFun z‖ := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := Bound2_dKPlusSum ℓ
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h := hb τ z t hF ht hz0 hz1 hzim
  rw [show ‖Work.Kernels.qParamFun τ‖ ^ (-1 : ℤ) = (‖Work.Kernels.qParamFun τ‖)⁻¹
      from zpow_neg_one _] at h
  rw [show ‖Work.Kernels.qParamFun z‖ ^ (1 : ℤ) = ‖Work.Kernels.qParamFun z‖
      from zpow_one _] at h
  simpa only [mul_assoc] using h

end

end Work.Asymptotics.KhatE1Core
