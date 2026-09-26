import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.Kaxis24_pair_gate

set_option maxHeartbeats 4000000

namespace Work.Asymptotics

open UpperHalfPlane

noncomputable section

/-!
# Exponential decay of the `e^{2πt}`-row `G_{1,j}` of the cusp expansion on the funnel

The coefficient functions `Gcusp ℓ d 1 j` of the cusp-`i∞` expansion of the CKMRV kernel
multiply `e^{2πt}` in `Aexp`, so they must be exponentially small for `Aexp` to be polynomially
bounded.  This file proves the quantitative form

  `∃ C N, 0 < C ∧ 0 ≤ N ∧ ∀ τ j, Funnel τ → ‖Gcusp ℓ d 1 j τ‖ ≤ C (scale τ)^N e^{-2π Im τ}`.

The mechanism: the `q⁰`-parts of the explicit combinations cancel algebraically, so each term is
`O(q_τ)` up to a polynomial factor in `τ`.  The `ψ₂, ψ₄` combination is the near-identity
`Work.Asymptotics.psi4E8_sub_psi2E10_funnel`; the polynomial part reduces to the identities
`E₂E₄ - E₆ = a + b + ab - c`, `E₂E₆ - E₄² = a + c + ac - 2b - b²` (`a = E₂-1`, `b = E₄-1`,
`c = E₆-1`), `E₄³ - E₂E₄E₆ = -E₄(E₂E₆-E₄²)` and
`7E₄³+5E₆²-12E₂E₄E₆ = 7·1728·Δ - 12E₆(E₂E₄-E₆)`.
-/

/-! ## Elementary helpers -/

private lemma qnorm_le_one {τ : ℍ} (hτ : Funnel τ) :
    ‖Work.Kernels.qParamFun τ‖ ≤ 1 := by
  rw [norm_qParamFun, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by nlinarith [hτ.2, Real.pi_pos])

private lemma sq_le_self {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : r ^ 2 ≤ r := by
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]

private lemma scale_le_scale_rpow {τ : ℍ} {N : ℝ} (hN : 1 ≤ N) :
    Work.Kernels.scale τ ≤ Work.Kernels.scale τ ^ N := by
  have h1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  simpa using Real.rpow_le_rpow_of_exponent_le h1 hN

/-- A product `a^i b^j c^k` (`i + j + k ≥ 1`) of three quantities bounded by `A r` is bounded by
`A^{i+j+k} r`, provided `0 ≤ r ≤ 1`. -/
private lemma norm_monom_le {a b c : ℂ} {A : ℝ} (hA : 0 ≤ A) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ha : ‖a‖ ≤ A * r) (hb : ‖b‖ ≤ A * r) (hc : ‖c‖ ≤ A * r)
    (i j k : ℕ) (hijk : 1 ≤ i + j + k) :
    ‖a ^ i * b ^ j * c ^ k‖ ≤ A ^ (i + j + k) * r := by
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow]
  have hAr : (0 : ℝ) ≤ A * r := mul_nonneg hA hr0
  have h1 : ‖a‖ ^ i ≤ (A * r) ^ i := pow_le_pow_left₀ (norm_nonneg a) ha i
  have h2 : ‖b‖ ^ j ≤ (A * r) ^ j := pow_le_pow_left₀ (norm_nonneg b) hb j
  have h3 : ‖c‖ ^ k ≤ (A * r) ^ k := pow_le_pow_left₀ (norm_nonneg c) hc k
  calc ‖a‖ ^ i * ‖b‖ ^ j * ‖c‖ ^ k
      ≤ (A * r) ^ i * (A * r) ^ j * (A * r) ^ k :=
        mul_le_mul (mul_le_mul h1 h2 (pow_nonneg (norm_nonneg b) j) (pow_nonneg hAr i)) h3
          (pow_nonneg (norm_nonneg c) k) (mul_nonneg (pow_nonneg hAr i) (pow_nonneg hAr j))
    _ = (A * r) ^ (i + j + k) := by rw [← pow_add, ← pow_add]
    _ = A ^ (i + j + k) * r ^ (i + j + k) := by rw [mul_pow]
    _ ≤ A ^ (i + j + k) * r := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hA _)
        simpa using pow_le_pow_of_le_one hr0 hr1 hijk

/-- `E₂E₄ - E₆ = O(q_τ)`: the `q⁰`-part `1 - 1` cancels. -/
private lemma norm_C4_le {e2 e4 e6 : ℂ} {A r : ℝ} (hA : 0 ≤ A) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (h2 : ‖e2 - 1‖ ≤ A * r) (h4 : ‖e4 - 1‖ ≤ A * r) (h6 : ‖e6 - 1‖ ≤ A * r) :
    ‖e2 * e4 - e6‖ ≤ (3 * A + A ^ 2) * r := by
  have key : e2 * e4 - e6
      = (e2 - 1) + (e4 - 1) + (e2 - 1) * (e4 - 1) - (e6 - 1) := by ring
  rw [key]
  have h12 : ‖(e2 - 1) * (e4 - 1)‖ ≤ A ^ 2 * r := by
    simpa using norm_monom_le hA hr0 hr1 h2 h4 h6 1 1 0 (by norm_num)
  have hsum : ‖(e2 - 1) + (e4 - 1) + (e2 - 1) * (e4 - 1)‖
      ≤ ‖e2 - 1‖ + ‖e4 - 1‖ + ‖(e2 - 1) * (e4 - 1)‖ := by
    refine le_trans (norm_add_le ((e2 - 1) + (e4 - 1)) ((e2 - 1) * (e4 - 1))) ?_
    have := norm_add_le (e2 - 1) (e4 - 1)
    linarith
  calc ‖(e2 - 1) + (e4 - 1) + (e2 - 1) * (e4 - 1) - (e6 - 1)‖
      ≤ ‖(e2 - 1) + (e4 - 1) + (e2 - 1) * (e4 - 1)‖ + ‖e6 - 1‖ := norm_sub_le _ _
    _ ≤ (‖e2 - 1‖ + ‖e4 - 1‖ + ‖(e2 - 1) * (e4 - 1)‖) + ‖e6 - 1‖ := by linarith
    _ ≤ (A * r + A * r + A ^ 2 * r) + A * r := by linarith
    _ = (3 * A + A ^ 2) * r := by ring

/-- `E₂E₆ - E₄² = O(q_τ)`. -/
private lemma norm_C5_le {e2 e4 e6 : ℂ} {A r : ℝ} (hA : 0 ≤ A) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (h2 : ‖e2 - 1‖ ≤ A * r) (h4 : ‖e4 - 1‖ ≤ A * r) (h6 : ‖e6 - 1‖ ≤ A * r) :
    ‖e2 * e6 - e4 ^ 2‖ ≤ (4 * A + 2 * A ^ 2) * r := by
  have key : e2 * e6 - e4 ^ 2
      = (e2 - 1) + (e6 - 1) + (e2 - 1) * (e6 - 1) - 2 * (e4 - 1) - (e4 - 1) ^ 2 := by ring
  rw [key]
  have h12 : ‖(e2 - 1) * (e6 - 1)‖ ≤ A ^ 2 * r := by
    simpa using norm_monom_le hA hr0 hr1 h2 h4 h6 1 0 1 (by norm_num)
  have h42 : ‖(e4 - 1) ^ 2‖ ≤ A ^ 2 * r := by
    simpa using norm_monom_le hA hr0 hr1 h2 h4 h6 0 2 0 (by norm_num)
  have hsum1 : ‖(e2 - 1) + (e6 - 1) + (e2 - 1) * (e6 - 1)‖
      ≤ ‖e2 - 1‖ + ‖e6 - 1‖ + ‖(e2 - 1) * (e6 - 1)‖ := by
    refine le_trans (norm_add_le ((e2 - 1) + (e6 - 1)) ((e2 - 1) * (e6 - 1))) ?_
    have := norm_add_le (e2 - 1) (e6 - 1)
    linarith
  have htwo : ‖(2 : ℂ) * (e4 - 1)‖ = 2 * ‖e4 - 1‖ := by rw [norm_mul, Complex.norm_ofNat]
  calc ‖(e2 - 1) + (e6 - 1) + (e2 - 1) * (e6 - 1) - 2 * (e4 - 1) - (e4 - 1) ^ 2‖
      ≤ ‖(e2 - 1) + (e6 - 1) + (e2 - 1) * (e6 - 1) - 2 * (e4 - 1)‖ + ‖(e4 - 1) ^ 2‖ :=
        norm_sub_le _ _
    _ ≤ (‖(e2 - 1) + (e6 - 1) + (e2 - 1) * (e6 - 1)‖ + ‖(2 : ℂ) * (e4 - 1)‖)
          + ‖(e4 - 1) ^ 2‖ := by
        have := norm_sub_le ((e2 - 1) + (e6 - 1) + (e2 - 1) * (e6 - 1)) (2 * (e4 - 1))
        linarith
    _ ≤ (‖e2 - 1‖ + ‖e6 - 1‖ + ‖(e2 - 1) * (e6 - 1)‖ + 2 * ‖e4 - 1‖)
          + ‖(e4 - 1) ^ 2‖ := by rw [htwo]; linarith
    _ ≤ (A * r + A * r + A ^ 2 * r + 2 * (A * r)) + A ^ 2 * r := by linarith
    _ = (4 * A + 2 * A ^ 2) * r := by ring

/-! ## The main theorem -/

theorem Gcusp_one_exp_small_funnel (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (τ : UpperHalfPlane) (j : Fin 2), Work.Asymptotics.Funnel τ →
        ‖Work.Asymptotics.Gcusp ℓ d 1 j τ‖
          ≤ C * (Work.Kernels.scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by
  rcases hd with rfl | rfl
  · -- `d = 8`: the whole `i = 1` row vanishes.
    refine ⟨1, 0, one_pos, le_refl 0, ?_⟩
    intro τ j hτ
    have h8 : Gcusp ℓ 8 1 j τ = Gcusp8 ℓ 1 j τ := by
      simp only [Gcusp, if_true]
    have hzero : Gcusp8 ℓ 1 j τ = 0 := by
      simp only [Gcusp8, if_true]
    rw [h8, hzero, norm_zero]
    have h1 : (0 : ℝ) ≤ Work.Kernels.scale τ ^ (0 : ℝ) * Real.exp (-(2 * Real.pi * τ.im)) :=
      mul_nonneg (ft_scale_rpow_nonneg τ 0) (Real.exp_pos _).le
    linarith [h1]
  · -- `d = 24`
    obtain ⟨C2, hC2pos, hC2⟩ := E2Fun_two_term
    obtain ⟨C6, hC6pos, hC6⟩ := E6Fun_two_term
    obtain ⟨Cψ, Nψ, hCψpos, hNψ, hψ⟩ := psi4E8_sub_psi2E10_funnel ℓ
    obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 24 + C2 + 20000 + 504 + C6 := ⟨_, rfl⟩
    have hA0 : 0 ≤ A := by rw [hAdef]; linarith
    have hE2 : ∀ τ : ℍ, Funnel τ → ‖Work.Kernels.E2Fun τ - 1‖
        ≤ A * ‖Work.Kernels.qParamFun τ‖ := by
      intro τ hτ
      have h := hC2 τ (Funnel.im_one hτ)
      have hr0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
      have hr1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := qnorm_le_one hτ
      have hr2 : ‖Work.Kernels.qParamFun τ‖ ^ 2 ≤ ‖Work.Kernels.qParamFun τ‖ :=
        sq_le_self hr0 hr1
      have key : Work.Kernels.E2Fun τ - 1
          = (Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ)
            - 24 * Work.Kernels.qParamFun τ := by ring
      rw [key]
      have h24 : ‖(24 : ℂ) * Work.Kernels.qParamFun τ‖
          = 24 * ‖Work.Kernels.qParamFun τ‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h1 : ‖(Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ)
            - 24 * Work.Kernels.qParamFun τ‖
          ≤ C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2 + 24 * ‖Work.Kernels.qParamFun τ‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [h24]; linarith
      refine le_trans h1 ?_
      have h2 : C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2 ≤ C2 * ‖Work.Kernels.qParamFun τ‖ :=
        mul_le_mul_of_nonneg_left hr2 hC2pos.le
      have h3 : (C2 + 24) * ‖Work.Kernels.qParamFun τ‖ ≤ A * ‖Work.Kernels.qParamFun τ‖ := by
        refine mul_le_mul_of_nonneg_right ?_ hr0
        rw [hAdef]; linarith
      calc C2 * ‖Work.Kernels.qParamFun τ‖ ^ 2 + 24 * ‖Work.Kernels.qParamFun τ‖
          ≤ C2 * ‖Work.Kernels.qParamFun τ‖ + 24 * ‖Work.Kernels.qParamFun τ‖ := by linarith
        _ = (C2 + 24) * ‖Work.Kernels.qParamFun τ‖ := by ring
        _ ≤ A * ‖Work.Kernels.qParamFun τ‖ := h3
    have hE4 : ∀ τ : ℍ, Funnel τ → ‖Work.Kernels.E4Fun τ - 1‖
        ≤ A * ‖Work.Kernels.qParamFun τ‖ := by
      intro τ hτ
      have h := E4Fun_sub_one_explicit (w := τ) (Funnel.im_one hτ)
      have hr0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
      refine le_trans h ?_
      refine mul_le_mul_of_nonneg_right ?_ hr0
      rw [hAdef]; linarith
    have hE6 : ∀ τ : ℍ, Funnel τ → ‖Work.Kernels.E6Fun τ - 1‖
        ≤ A * ‖Work.Kernels.qParamFun τ‖ := by
      intro τ hτ
      have h := hC6 τ (Funnel.im_one hτ)
      have hr0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
      have hr1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := qnorm_le_one hτ
      have hr2 : ‖Work.Kernels.qParamFun τ‖ ^ 2 ≤ ‖Work.Kernels.qParamFun τ‖ :=
        sq_le_self hr0 hr1
      have key : Work.Kernels.E6Fun τ - 1
          = (Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ)
            - 504 * Work.Kernels.qParamFun τ := by ring
      rw [key]
      have h504 : ‖(504 : ℂ) * Work.Kernels.qParamFun τ‖
          = 504 * ‖Work.Kernels.qParamFun τ‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h1 : ‖(Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ)
            - 504 * Work.Kernels.qParamFun τ‖
          ≤ C6 * ‖Work.Kernels.qParamFun τ‖ ^ 2 + 504 * ‖Work.Kernels.qParamFun τ‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [h504]; linarith
      refine le_trans h1 ?_
      have h2 : C6 * ‖Work.Kernels.qParamFun τ‖ ^ 2 ≤ C6 * ‖Work.Kernels.qParamFun τ‖ :=
        mul_le_mul_of_nonneg_left hr2 hC6pos.le
      have h3 : (C6 + 504) * ‖Work.Kernels.qParamFun τ‖ ≤ A * ‖Work.Kernels.qParamFun τ‖ := by
        refine mul_le_mul_of_nonneg_right ?_ hr0
        rw [hAdef]; linarith
      calc C6 * ‖Work.Kernels.qParamFun τ‖ ^ 2 + 504 * ‖Work.Kernels.qParamFun τ‖
          ≤ C6 * ‖Work.Kernels.qParamFun τ‖ + 504 * ‖Work.Kernels.qParamFun τ‖ := by linarith
        _ = (C6 + 504) * ‖Work.Kernels.qParamFun τ‖ := by ring
        _ ≤ A * ‖Work.Kernels.qParamFun τ‖ := h3
    -- the constants
    obtain ⟨C4b, hC4def⟩ : ∃ C : ℝ, C = 3 * A + A ^ 2 := ⟨_, rfl⟩
    obtain ⟨C5b, hC5def⟩ : ∃ C : ℝ, C = 4 * A + 2 * A ^ 2 := ⟨_, rfl⟩
    have hC4b0 : 0 ≤ C4b := by rw [hC4def]; nlinarith [hA0, sq_nonneg A]
    have hC5b0 : 0 ≤ C5b := by rw [hC5def]; nlinarith [hA0, sq_nonneg A]
    obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = max 1 Nψ := ⟨_, rfl⟩
    have hN0 : 0 ≤ N := by rw [hNdef]; exact le_trans zero_le_one (le_max_left _ _)
    have hN1 : 1 ≤ N := by rw [hNdef]; exact le_max_left _ _
    have hNNψ : Nψ ≤ N := by rw [hNdef]; exact le_max_right _ _
    obtain ⟨Pc, hPcdef⟩ : ∃ P : ℝ, P = (1 / 288) * (1 + A) ^ 2 * (C4b + C5b)
        + 14 * (1 + A) := ⟨_, rfl⟩
    have hPc0 : 0 ≤ Pc := by
      rw [hPcdef]
      have h1 : (0 : ℝ) ≤ (1 / 288) * ((1 + A) ^ 2 * (C4b + C5b)) :=
        mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (add_nonneg hC4b0 hC5b0))
      have h2 : (0 : ℝ) ≤ 14 * (1 + A) := by linarith
      linarith [h1, h2]
    obtain ⟨t2c, ht2cdef⟩ : ∃ t : ℝ, t = (1 + A) * C5b / (48 * Real.pi) := ⟨_, rfl⟩
    obtain ⟨t3c, ht3cdef⟩ : ∃ t : ℝ, t = 2 * ‖cuspL ℓ - 22‖ / Real.pi := ⟨_, rfl⟩
    obtain ⟨t4c, ht4cdef⟩ : ∃ t : ℝ, t = Cψ / (1152 * Real.pi) := ⟨_, rfl⟩
    have ht2c0 : 0 ≤ t2c := by
      rw [ht2cdef]
      exact div_nonneg (mul_nonneg (by linarith [hA0]) hC5b0) (by positivity)
    have ht3c0 : 0 ≤ t3c := by
      rw [ht3cdef]
      exact div_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) Real.pi_pos.le
    have ht4c0 : 0 ≤ t4c := by
      rw [ht4cdef]
      exact div_nonneg hCψpos.le (by positivity)
    obtain ⟨C10, hC10def⟩ : ∃ C : ℝ, C = Pc / 2 + t2c + t3c + t4c := ⟨_, rfl⟩
    obtain ⟨C11, hC11def⟩ : ∃ C : ℝ, C = (1 / 3456) * ((7 * 1728 * 2 + 12 * (1 + A) * C4b)
        + 2 * Real.pi * C4b * C5b) := ⟨_, rfl⟩
    -- ## the `(1,0)`-estimate
    have h10 : ∀ τ : ℍ, Funnel τ → ‖Gcusp ℓ 24 1 0 τ‖
        ≤ C10 * Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖ := by
      intro τ hτ
      have hr0 : 0 ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
      have hr1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := qnorm_le_one hτ
      have h2 := hE2 τ hτ
      have h4 := hE4 τ hτ
      have h6 := hE6 τ hτ
      have he2 : ‖Work.Kernels.E2Fun τ‖ ≤ 1 + A * ‖Work.Kernels.qParamFun τ‖ := by
        have h := norm_add_le (Work.Kernels.E2Fun τ - 1) (1 : ℂ)
        rw [norm_one] at h
        have heq : Work.Kernels.E2Fun τ = (Work.Kernels.E2Fun τ - 1) + 1 := by ring
        rw [heq]; linarith
      have he4 : ‖Work.Kernels.E4Fun τ‖ ≤ 1 + A * ‖Work.Kernels.qParamFun τ‖ := by
        have h := norm_add_le (Work.Kernels.E4Fun τ - 1) (1 : ℂ)
        rw [norm_one] at h
        have heq : Work.Kernels.E4Fun τ = (Work.Kernels.E4Fun τ - 1) + 1 := by ring
        rw [heq]; linarith
      have he6 : ‖Work.Kernels.E6Fun τ‖ ≤ 1 + A * ‖Work.Kernels.qParamFun τ‖ := by
        have h := norm_add_le (Work.Kernels.E6Fun τ - 1) (1 : ℂ)
        rw [norm_one] at h
        have heq : Work.Kernels.E6Fun τ = (Work.Kernels.E6Fun τ - 1) + 1 := by ring
        rw [heq]; linarith
      have hC4 : ‖Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ‖
          ≤ C4b * ‖Work.Kernels.qParamFun τ‖ := by
        rw [hC4def]; exact norm_C4_le hA0 hr0 hr1 h2 h4 h6
      have hC5 : ‖Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ - Work.Kernels.E4Fun τ ^ 2‖
          ≤ C5b * ‖Work.Kernels.qParamFun τ‖ := by
        rw [hC5def]; exact norm_C5_le hA0 hr0 hr1 h2 h4 h6
      have hΔ : ‖Work.Kernels.DeltaFun τ‖ ≤ 2 * ‖Work.Kernels.qParamFun τ‖ :=
        DeltaFun_funnel_le τ hτ
      have h1Ar : 1 + A * ‖Work.Kernels.qParamFun τ‖ ≤ 1 + A := by nlinarith [hr0, hr1, hA0]
      have h1Ar0 : (0 : ℝ) ≤ 1 + A * ‖Work.Kernels.qParamFun τ‖ := by positivity
      -- the `P` factor
      obtain ⟨W, hWdef⟩ : ∃ W : ℂ, W = Work.Kernels.E4Fun τ
          * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ)
          - Work.Kernels.E2Fun τ
            * (Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ - Work.Kernels.E4Fun τ ^ 2) :=
        ⟨_, rfl⟩
      have hWb : ‖W‖ ≤ (1 + A) * ((C4b + C5b) * ‖Work.Kernels.qParamFun τ‖) := by
        have h1 : ‖Work.Kernels.E4Fun τ
              * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ)‖
            ≤ (1 + A * ‖Work.Kernels.qParamFun τ‖) * (C4b * ‖Work.Kernels.qParamFun τ‖) := by
          rw [norm_mul]
          exact mul_le_mul he4 hC4 (norm_nonneg _) (by positivity)
        have h2 : ‖Work.Kernels.E2Fun τ
              * (Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ - Work.Kernels.E4Fun τ ^ 2)‖
            ≤ (1 + A * ‖Work.Kernels.qParamFun τ‖) * (C5b * ‖Work.Kernels.qParamFun τ‖) := by
          rw [norm_mul]
          exact mul_le_mul he2 hC5 (norm_nonneg _) (by positivity)
        rw [hWdef]
        refine le_trans (norm_sub_le _ _) ?_
        refine le_trans (add_le_add h1 h2) ?_
        rw [show (1 + A * ‖Work.Kernels.qParamFun τ‖) * (C4b * ‖Work.Kernels.qParamFun τ‖)
              + (1 + A * ‖Work.Kernels.qParamFun τ‖) * (C5b * ‖Work.Kernels.qParamFun τ‖)
            = (1 + A * ‖Work.Kernels.qParamFun τ‖)
              * ((C4b + C5b) * ‖Work.Kernels.qParamFun τ‖) from by ring]
        exact mul_le_mul_of_nonneg_right h1Ar (by positivity)
      have hI288 : ‖(Complex.I / 288 : ℂ)‖ = 1 / 288 := by
        rw [norm_div, Complex.norm_I, Complex.norm_ofNat]
      have hI7 : ‖(7 : ℂ) * Complex.I‖ = 7 := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
      have hsplitW : (Complex.I / 288) * (Work.Kernels.E4Fun τ * W)
          - (7 * Complex.I) * (Work.Kernels.E2Fun τ * Work.Kernels.DeltaFun τ)
          = -(Complex.I / 288)
              * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ
                  + Work.Kernels.E2Fun τ ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
              + (Complex.I / 144) * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ ^ 3)
              - 7 * Complex.I * (Work.Kernels.E2Fun τ * Work.Kernels.DeltaFun τ) := by
        rw [hWdef]; ring
      have hbd : (1 / 288) * (‖Work.Kernels.E4Fun τ‖ * ‖W‖)
            + 7 * (‖Work.Kernels.E2Fun τ‖ * ‖Work.Kernels.DeltaFun τ‖)
          ≤ ((1 / 288) * (1 + A) ^ 2 * (C4b + C5b) + 14 * (1 + A))
            * ‖Work.Kernels.qParamFun τ‖ := by
        have hb1 : ‖Work.Kernels.E4Fun τ‖ * ‖W‖
            ≤ (1 + A) * ((1 + A) * ((C4b + C5b) * ‖Work.Kernels.qParamFun τ‖)) := by
          calc ‖Work.Kernels.E4Fun τ‖ * ‖W‖
              ≤ (1 + A * ‖Work.Kernels.qParamFun τ‖)
                * ((1 + A) * ((C4b + C5b) * ‖Work.Kernels.qParamFun τ‖)) :=
                mul_le_mul he4 hWb (norm_nonneg _) (by positivity)
            _ ≤ (1 + A) * ((1 + A) * ((C4b + C5b) * ‖Work.Kernels.qParamFun τ‖)) :=
                mul_le_mul_of_nonneg_right h1Ar (by positivity)
        have hb2 : ‖Work.Kernels.E2Fun τ‖ * ‖Work.Kernels.DeltaFun τ‖
            ≤ (1 + A) * (2 * ‖Work.Kernels.qParamFun τ‖) := by
          calc ‖Work.Kernels.E2Fun τ‖ * ‖Work.Kernels.DeltaFun τ‖
              ≤ (1 + A * ‖Work.Kernels.qParamFun τ‖) * (2 * ‖Work.Kernels.qParamFun τ‖) :=
                mul_le_mul he2 hΔ (norm_nonneg _) (by positivity)
            _ ≤ (1 + A) * (2 * ‖Work.Kernels.qParamFun τ‖) :=
                mul_le_mul_of_nonneg_right h1Ar (by positivity)
        have ha := mul_le_mul_of_nonneg_left hb1 (by norm_num : (0 : ℝ) ≤ 1 / 288)
        have hb := mul_le_mul_of_nonneg_left hb2 (by norm_num : (0 : ℝ) ≤ 7)
        have heq : (1 / 288) * ((1 + A) * ((1 + A) * ((C4b + C5b) * ‖Work.Kernels.qParamFun τ‖)))
              + 7 * ((1 + A) * (2 * ‖Work.Kernels.qParamFun τ‖))
            = ((1 / 288) * (1 + A) ^ 2 * (C4b + C5b) + 14 * (1 + A))
              * ‖Work.Kernels.qParamFun τ‖ := by ring
        linarith [ha, hb, heq]
      have hP : ‖-(Complex.I / 288)
            * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ
                + Work.Kernels.E2Fun τ ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
            + (Complex.I / 144) * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ ^ 3)
            - 7 * Complex.I * (Work.Kernels.E2Fun τ * Work.Kernels.DeltaFun τ)‖
          ≤ Pc * ‖Work.Kernels.qParamFun τ‖ := by
        have hd1 : ‖(Complex.I / 288) * (Work.Kernels.E4Fun τ * W)‖
            = (1 / 288) * (‖Work.Kernels.E4Fun τ‖ * ‖W‖) := by
          simp only [norm_mul, hI288]
        have hd2 : ‖(7 * Complex.I) * (Work.Kernels.E2Fun τ * Work.Kernels.DeltaFun τ)‖
            = 7 * (‖Work.Kernels.E2Fun τ‖ * ‖Work.Kernels.DeltaFun τ‖) := by
          simp only [norm_mul, hI7]
        rw [hPcdef, ← hsplitW]
        calc ‖(Complex.I / 288) * (Work.Kernels.E4Fun τ * W)
              - (7 * Complex.I) * (Work.Kernels.E2Fun τ * Work.Kernels.DeltaFun τ)‖
            ≤ ‖(Complex.I / 288) * (Work.Kernels.E4Fun τ * W)‖
              + ‖(7 * Complex.I) * (Work.Kernels.E2Fun τ * Work.Kernels.DeltaFun τ)‖ :=
              norm_sub_le _ _
          _ = (1 / 288) * (‖Work.Kernels.E4Fun τ‖ * ‖W‖)
              + 7 * (‖Work.Kernels.E2Fun τ‖ * ‖Work.Kernels.DeltaFun τ‖) := by
              rw [hd1, hd2]
          _ ≤ _ := hbd
      -- the `ψ`-combination
      have hψb : ‖Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
            - Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2‖
          ≤ Cψ * Work.Kernels.scale τ ^ Nψ * ‖Work.Kernels.qParamFun τ‖ := by
        have h := hψ τ hτ
        have heq : Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
              - Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2
            = -(Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ) := by
          simp only [Work.Kernels.E8Fun, Work.Kernels.E10Fun]; ring
        rw [heq, norm_neg]; exact h
      have h3 : ‖Work.Kernels.E4Fun τ ^ 3
            - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ‖
          ≤ (1 + A) * C5b * ‖Work.Kernels.qParamFun τ‖ := by
        have hid : Work.Kernels.E4Fun τ ^ 3
              - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ
            = -(Work.Kernels.E4Fun τ * (Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ
                - Work.Kernels.E4Fun τ ^ 2)) := by ring
        rw [hid, norm_neg, norm_mul]
        calc ‖Work.Kernels.E4Fun τ‖ * ‖Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ
              - Work.Kernels.E4Fun τ ^ 2‖
            ≤ (1 + A * ‖Work.Kernels.qParamFun τ‖) * (C5b * ‖Work.Kernels.qParamFun τ‖) :=
              mul_le_mul he4 hC5 (norm_nonneg _) (by positivity)
          _ ≤ (1 + A) * (C5b * ‖Work.Kernels.qParamFun τ‖) :=
              mul_le_mul_of_nonneg_right h1Ar (by positivity)
          _ = (1 + A) * C5b * ‖Work.Kernels.qParamFun τ‖ := by ring
      have hred := Gcusp24_one_zero_reduced ℓ τ
      have hG : Gcusp ℓ 24 1 0 τ = Gcusp24 ℓ 1 0 τ := by
        simp only [Gcusp, if_neg (by norm_num : ¬ ((24 : ℕ) = 8))]
      have htP : ‖(τ : ℂ) * (-(Complex.I / 288)
              * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ
                + Work.Kernels.E2Fun τ ^ 2 * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
            + (Complex.I / 144) * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ ^ 3)
            - 7 * Complex.I * (Work.Kernels.E2Fun τ * Work.Kernels.DeltaFun τ))‖
          ≤ Work.Kernels.scale τ * (Pc * ‖Work.Kernels.qParamFun τ‖) := by
        rw [norm_mul]
        exact mul_le_mul (Work.Kernels.coe_norm_le_scale τ) hP (norm_nonneg _)
          (Work.Kernels.scale_pos τ).le
      have hpi48 : ‖(48 * (Real.pi : ℂ))‖ = 48 * Real.pi := by
        rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
      have hT2 : ‖(Work.Kernels.E4Fun τ ^ 3
            - Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
            / (48 * (Real.pi : ℂ))‖ ≤ t2c * ‖Work.Kernels.qParamFun τ‖ := by
        have h := div_le_div_of_nonneg_right h3 (show (0 : ℝ) ≤ 48 * Real.pi by positivity)
        rw [ht2cdef, norm_div, hpi48]
        refine le_trans h ?_
        exact le_of_eq (by ring)
      have hT3 : ‖Work.Kernels.DeltaFun τ * (cuspL ℓ - 22) / (Real.pi : ℂ)‖
          ≤ t3c * ‖Work.Kernels.qParamFun τ‖ := by
        have hpir : ‖(Real.pi : ℂ)‖ = Real.pi := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        have hd : ‖Work.Kernels.DeltaFun τ * (cuspL ℓ - 22) / (Real.pi : ℂ)‖
            = ‖Work.Kernels.DeltaFun τ‖ * ‖cuspL ℓ - 22‖ / Real.pi := by
          simp only [norm_div, norm_mul, hpir]
        have h : ‖Work.Kernels.DeltaFun τ‖ * ‖cuspL ℓ - 22‖ / Real.pi
            ≤ (2 * ‖Work.Kernels.qParamFun τ‖) * ‖cuspL ℓ - 22‖ / Real.pi :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hΔ (norm_nonneg _))
            Real.pi_pos.le
        rw [ht3cdef, hd]
        refine le_trans h ?_
        exact le_of_eq (by ring)
      have hpi1152 : ‖(1152 * (Real.pi : ℂ))‖ = 1152 * Real.pi := by
        rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
      have hT4 : ‖(Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
              - Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2)
            / (1152 * (Real.pi : ℂ))‖
          ≤ (t4c * Work.Kernels.scale τ ^ N) * ‖Work.Kernels.qParamFun τ‖ := by
        have hsc2 : Work.Kernels.scale τ ^ Nψ ≤ Work.Kernels.scale τ ^ N :=
          Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ) hNNψ
        have e1 : ‖Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
              - Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2‖ / (1152 * Real.pi)
            ≤ (Cψ * Work.Kernels.scale τ ^ Nψ * ‖Work.Kernels.qParamFun τ‖)
                / (1152 * Real.pi) :=
          div_le_div_of_nonneg_right hψb (by positivity)
        have e2 : (Cψ * Work.Kernels.scale τ ^ Nψ * ‖Work.Kernels.qParamFun τ‖)
              / (1152 * Real.pi)
            = (Cψ / (1152 * Real.pi) * Work.Kernels.scale τ ^ Nψ)
              * ‖Work.Kernels.qParamFun τ‖ := by ring
        have e3 : (Cψ / (1152 * Real.pi) * Work.Kernels.scale τ ^ Nψ)
              * ‖Work.Kernels.qParamFun τ‖
            ≤ (Cψ / (1152 * Real.pi) * Work.Kernels.scale τ ^ N)
              * ‖Work.Kernels.qParamFun τ‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsc2 (by positivity)) hr0
        have e4 : (Cψ / (1152 * Real.pi) * Work.Kernels.scale τ ^ N)
              * ‖Work.Kernels.qParamFun τ‖
            = (t4c * Work.Kernels.scale τ ^ N) * ‖Work.Kernels.qParamFun τ‖ := by
          rw [ht4cdef]
        have hd : ‖(Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
              - Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2)
            / (1152 * (Real.pi : ℂ))‖
            = ‖Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
              - Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2‖ / (1152 * Real.pi) := by
          simp only [norm_div, hpi1152]
        rw [hd]
        linarith [e1, e2, e3, e4]
      have hnorm2 : ‖2 * Gcusp24 ℓ 1 0 τ‖ = 2 * ‖Gcusp24 ℓ 1 0 τ‖ := by
        rw [norm_mul, Complex.norm_ofNat]
      -- assembly
      have hub : 2 * ‖Gcusp24 ℓ 1 0 τ‖
          ≤ (Pc + t2c + t3c + t4c) * (Work.Kernels.scale τ ^ N
              * ‖Work.Kernels.qParamFun τ‖) := by
        have hscN1 : (1 : ℝ) ≤ Work.Kernels.scale τ ^ N :=
          le_trans (Work.Kernels.one_le_scale τ) (scale_le_scale_rpow hN1)
        have hmulS : Work.Kernels.scale τ * ‖Work.Kernels.qParamFun τ‖
            ≤ Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖ :=
          mul_le_mul_of_nonneg_right (scale_le_scale_rpow hN1) hr0
        have hmul1 : (1 : ℝ) * ‖Work.Kernels.qParamFun τ‖
            ≤ Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖ :=
          mul_le_mul_of_nonneg_right hscN1 hr0
        have hPcs : Work.Kernels.scale τ * (Pc * ‖Work.Kernels.qParamFun τ‖)
            ≤ Pc * (Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖) := by
          calc Work.Kernels.scale τ * (Pc * ‖Work.Kernels.qParamFun τ‖)
              = Pc * (Work.Kernels.scale τ * ‖Work.Kernels.qParamFun τ‖) := by ring
            _ ≤ Pc * (Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖) :=
                mul_le_mul_of_nonneg_left hmulS hPc0
        have ht2s : t2c * ‖Work.Kernels.qParamFun τ‖
            ≤ t2c * (Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖) := by
          calc t2c * ‖Work.Kernels.qParamFun τ‖
              = t2c * (1 * ‖Work.Kernels.qParamFun τ‖) := by ring
            _ ≤ t2c * (Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖) :=
                mul_le_mul_of_nonneg_left hmul1 ht2c0
        have ht3s : t3c * ‖Work.Kernels.qParamFun τ‖
            ≤ t3c * (Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖) := by
          calc t3c * ‖Work.Kernels.qParamFun τ‖
              = t3c * (1 * ‖Work.Kernels.qParamFun τ‖) := by ring
            _ ≤ t3c * (Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖) :=
                mul_le_mul_of_nonneg_left hmul1 ht3c0
        have ht4s : (t4c * Work.Kernels.scale τ ^ N) * ‖Work.Kernels.qParamFun τ‖
            ≤ t4c * (Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖) :=
          le_of_eq (by ring)
        rw [← hnorm2, hred]
        refine le_trans (norm_add_le _ _) ?_
        refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
        refine le_trans (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) ?_
        refine le_trans (add_le_add (add_le_add (add_le_add htP hT2) le_rfl) le_rfl) ?_
        refine le_trans (add_le_add (add_le_add le_rfl hT3) le_rfl) ?_
        refine le_trans (add_le_add le_rfl hT4) ?_
        calc ((Work.Kernels.scale τ * (Pc * ‖Work.Kernels.qParamFun τ‖)
                + t2c * ‖Work.Kernels.qParamFun τ‖) + t3c * ‖Work.Kernels.qParamFun τ‖)
              + (t4c * Work.Kernels.scale τ ^ N) * ‖Work.Kernels.qParamFun τ‖
            ≤ ((Pc * (Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖)
                + t2c * (Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖))
                + t3c * (Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖))
              + t4c * (Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖) :=
              add_le_add (add_le_add (add_le_add hPcs ht2s) ht3s) ht4s
          _ = (Pc + t2c + t3c + t4c) * (Work.Kernels.scale τ ^ N
                * ‖Work.Kernels.qParamFun τ‖) := by ring
      have hscaleN : (0 : ℝ) ≤ Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖ :=
        mul_nonneg (ft_scale_rpow_nonneg τ N) hr0
      have hub2 : (Pc + t2c + t3c + t4c) * (Work.Kernels.scale τ ^ N
            * ‖Work.Kernels.qParamFun τ‖) ≤ 2 * C10 * (Work.Kernels.scale τ ^ N
            * ‖Work.Kernels.qParamFun τ‖) := by
        have ht0 : 0 ≤ t2c + t3c + t4c := by linarith
        refine mul_le_mul_of_nonneg_right ?_ hscaleN
        rw [hC10def]
        linarith
      have h1 : 2 * ‖Gcusp24 ℓ 1 0 τ‖
          ≤ 2 * (C10 * Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖) := by
        refine le_trans hub ?_
        refine le_trans hub2 ?_
        exact le_of_eq (by ring)
      rw [hG]
      linarith [h1]
    -- ## the `(1,1)`-estimate
    have h11 : ∀ τ : ℍ, Funnel τ → ‖Gcusp ℓ 24 1 1 τ‖
        ≤ C11 * Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖ := by
      intro τ hτ
      have hr0 : 0 ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
      have hr1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := qnorm_le_one hτ
      have h2 := hE2 τ hτ
      have h4 := hE4 τ hτ
      have h6 := hE6 τ hτ
      have he6 : ‖Work.Kernels.E6Fun τ‖ ≤ 1 + A * ‖Work.Kernels.qParamFun τ‖ := by
        have h := norm_add_le (Work.Kernels.E6Fun τ - 1) (1 : ℂ)
        rw [norm_one] at h
        have heq : Work.Kernels.E6Fun τ = (Work.Kernels.E6Fun τ - 1) + 1 := by ring
        rw [heq]; linarith
      have hC4 : ‖Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ‖
          ≤ C4b * ‖Work.Kernels.qParamFun τ‖ := by
        rw [hC4def]; exact norm_C4_le hA0 hr0 hr1 h2 h4 h6
      have hC5 : ‖Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ - Work.Kernels.E4Fun τ ^ 2‖
          ≤ C5b * ‖Work.Kernels.qParamFun τ‖ := by
        rw [hC5def]; exact norm_C5_le hA0 hr0 hr1 h2 h4 h6
      have hΔ : ‖Work.Kernels.DeltaFun τ‖ ≤ 2 * ‖Work.Kernels.qParamFun τ‖ :=
        DeltaFun_funnel_le τ hτ
      have hA24 : ‖A24 τ‖ ≤ C4b * C5b * ‖Work.Kernels.qParamFun τ‖ := by
        have heq : A24 τ = (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ)
            * (Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ - Work.Kernels.E4Fun τ ^ 2) := by
          simp only [A24]
        rw [heq, norm_mul]
        calc ‖Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ‖
              * ‖Work.Kernels.E2Fun τ * Work.Kernels.E6Fun τ - Work.Kernels.E4Fun τ ^ 2‖
            ≤ (C4b * ‖Work.Kernels.qParamFun τ‖) * (C5b * ‖Work.Kernels.qParamFun τ‖) :=
              mul_le_mul hC4 hC5 (norm_nonneg _) (by positivity)
          _ = C4b * C5b * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by ring
          _ ≤ C4b * C5b * ‖Work.Kernels.qParamFun τ‖ :=
              mul_le_mul_of_nonneg_left (sq_le_self hr0 hr1) (by positivity)
      have hD : Work.Kernels.DeltaFun τ
          = (Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2) / 1728 := by
        rw [Work.Kernels.DeltaFun, CuspForm.coe_discriminant]
        exact ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
      have h7 : ‖7 * Work.Kernels.E4Fun τ ^ 3 + 5 * Work.Kernels.E6Fun τ ^ 2
            - 12 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)‖
          ≤ (7 * 1728 * 2 + 12 * (1 + A) * C4b) * ‖Work.Kernels.qParamFun τ‖ := by
        have hid : 7 * Work.Kernels.E4Fun τ ^ 3 + 5 * Work.Kernels.E6Fun τ ^ 2
              - 12 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
            = 7 * (1728 * Work.Kernels.DeltaFun τ)
              - 12 * (Work.Kernels.E6Fun τ
                  * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ)) := by
          rw [hD]; ring
        rw [hid]
        have h1Ar : 1 + A * ‖Work.Kernels.qParamFun τ‖ ≤ 1 + A := by nlinarith [hr0, hr1, hA0]
        have h1 : ‖(7 : ℂ) * (1728 * Work.Kernels.DeltaFun τ)‖
            ≤ 7 * (1728 * (2 * ‖Work.Kernels.qParamFun τ‖)) := by
          have e1 : ‖(7 : ℂ) * (1728 * Work.Kernels.DeltaFun τ)‖
              = 7 * ‖(1728 : ℂ) * Work.Kernels.DeltaFun τ‖ := by
            rw [norm_mul, Complex.norm_ofNat]
          have e2 : ‖(1728 : ℂ) * Work.Kernels.DeltaFun τ‖
              ≤ 1728 * (2 * ‖Work.Kernels.qParamFun τ‖) := by
            rw [norm_mul, Complex.norm_ofNat]
            exact mul_le_mul_of_nonneg_left hΔ (by norm_num)
          calc ‖(7 : ℂ) * (1728 * Work.Kernels.DeltaFun τ)‖
              = 7 * ‖(1728 : ℂ) * Work.Kernels.DeltaFun τ‖ := e1
            _ ≤ 7 * (1728 * (2 * ‖Work.Kernels.qParamFun τ‖)) :=
                mul_le_mul_of_nonneg_left e2 (by norm_num)
        have hb : ‖Work.Kernels.E6Fun τ
              * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ)‖
            ≤ (1 + A) * (C4b * ‖Work.Kernels.qParamFun τ‖) := by
          rw [norm_mul]
          calc ‖Work.Kernels.E6Fun τ‖
                * ‖Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ‖
              ≤ (1 + A * ‖Work.Kernels.qParamFun τ‖) * (C4b * ‖Work.Kernels.qParamFun τ‖) :=
                mul_le_mul he6 hC4 (norm_nonneg _) (by positivity)
            _ ≤ (1 + A) * (C4b * ‖Work.Kernels.qParamFun τ‖) :=
                mul_le_mul_of_nonneg_right h1Ar (by positivity)
        have h2 : ‖(12 : ℂ) * (Work.Kernels.E6Fun τ
              * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ - Work.Kernels.E6Fun τ))‖
            ≤ 12 * ((1 + A) * (C4b * ‖Work.Kernels.qParamFun τ‖)) := by
          rw [norm_mul, Complex.norm_ofNat]
          exact mul_le_mul_of_nonneg_left hb (by norm_num)
        refine le_trans (norm_sub_le _ _) ?_
        refine le_trans (add_le_add h1 h2) ?_
        exact le_of_eq (by ring)
      have hG : Gcusp ℓ 24 1 1 τ = Gcusp24 ℓ 1 1 τ := by
        simp only [Gcusp, if_neg (by norm_num : ¬ ((24 : ℕ) = 8))]
      have hI3456 : ‖(Complex.I / 3456 : ℂ)‖ = 1 / 3456 := by
        rw [norm_div, Complex.norm_I, Complex.norm_ofNat]
      have hF : ‖F24 τ‖ ≤ ((7 * 1728 * 2 + 12 * (1 + A) * C4b)
            + 2 * Real.pi * C4b * C5b) * Work.Kernels.scale τ ^ N
            * ‖Work.Kernels.qParamFun τ‖ := by
        have hid : F24 τ = 7 * Work.Kernels.E4Fun τ ^ 3 + 5 * Work.Kernels.E6Fun τ ^ 2
            - 12 * (Work.Kernels.E2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
            - 2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * A24 τ := rfl
        rw [hid]
        have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        have hPI : ‖(2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) * A24 τ‖
            = 2 * Real.pi * ‖(τ : ℂ)‖ * ‖A24 τ‖ := by
          simp only [norm_mul, Complex.norm_ofNat, Complex.norm_I, hpi, mul_one]
        refine le_trans (norm_sub_le _ _) ?_
        rw [hPI]
        have htaun : ‖(τ : ℂ)‖ ≤ Work.Kernels.scale τ := Work.Kernels.coe_norm_le_scale τ
        have hA24b : 2 * Real.pi * ‖(τ : ℂ)‖ * ‖A24 τ‖
            ≤ 2 * Real.pi * C4b * C5b * Work.Kernels.scale τ
              * ‖Work.Kernels.qParamFun τ‖ := by
          have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
          calc 2 * Real.pi * ‖(τ : ℂ)‖ * ‖A24 τ‖
              = (2 * Real.pi * ‖(τ : ℂ)‖) * ‖A24 τ‖ := by ring
            _ ≤ (2 * Real.pi * Work.Kernels.scale τ) * (C4b * C5b
                  * ‖Work.Kernels.qParamFun τ‖) :=
                mul_le_mul (mul_le_mul_of_nonneg_left htaun h2pi) hA24 (norm_nonneg _)
                  (mul_nonneg h2pi (Work.Kernels.scale_pos τ).le)
            _ = 2 * Real.pi * C4b * C5b * Work.Kernels.scale τ
                * ‖Work.Kernels.qParamFun τ‖ := by ring
        have hscN1 : (1 : ℝ) ≤ Work.Kernels.scale τ ^ N :=
          le_trans (Work.Kernels.one_le_scale τ) (scale_le_scale_rpow hN1)
        have hmul1 : (1 : ℝ) * ‖Work.Kernels.qParamFun τ‖
            ≤ Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖ :=
          mul_le_mul_of_nonneg_right hscN1 hr0
        have hsum7 : (7 * 1728 * 2 + 12 * (1 + A) * C4b) * ‖Work.Kernels.qParamFun τ‖
            ≤ (7 * 1728 * 2 + 12 * (1 + A) * C4b)
              * (Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖) := by
          calc (7 * 1728 * 2 + 12 * (1 + A) * C4b) * ‖Work.Kernels.qParamFun τ‖
              = (7 * 1728 * 2 + 12 * (1 + A) * C4b)
                * (1 * ‖Work.Kernels.qParamFun τ‖) := by ring
            _ ≤ (7 * 1728 * 2 + 12 * (1 + A) * C4b)
                * (Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖) :=
                mul_le_mul_of_nonneg_left hmul1 (by positivity)
        have hsumPI : 2 * Real.pi * C4b * C5b * Work.Kernels.scale τ
              * ‖Work.Kernels.qParamFun τ‖
            ≤ 2 * Real.pi * C4b * C5b * (Work.Kernels.scale τ ^ N
              * ‖Work.Kernels.qParamFun τ‖) := by
          have hcore : Work.Kernels.scale τ * ‖Work.Kernels.qParamFun τ‖
              ≤ Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖ :=
            mul_le_mul_of_nonneg_right (scale_le_scale_rpow hN1) hr0
          calc 2 * Real.pi * C4b * C5b * Work.Kernels.scale τ * ‖Work.Kernels.qParamFun τ‖
              = (2 * Real.pi * C4b * C5b)
                * (Work.Kernels.scale τ * ‖Work.Kernels.qParamFun τ‖) := by ring
            _ ≤ (2 * Real.pi * C4b * C5b)
                * (Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖) :=
                mul_le_mul_of_nonneg_left hcore (by positivity)
        refine le_trans (add_le_add (le_trans h7 hsum7) (le_trans hA24b hsumPI)) ?_
        exact le_of_eq (by ring)
      rw [hG, Gcusp24_one_one ℓ τ, norm_mul, hI3456]
      calc (1 / 3456) * ‖F24 τ‖
          ≤ (1 / 3456) * (((7 * 1728 * 2 + 12 * (1 + A) * C4b)
            + 2 * Real.pi * C4b * C5b) * Work.Kernels.scale τ ^ N
            * ‖Work.Kernels.qParamFun τ‖) :=
            mul_le_mul_of_nonneg_left hF (by norm_num)
        _ = C11 * Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖ := by
            rw [hC11def]; ring
    -- ## combine the two rows
    refine ⟨|max C10 C11| + 1, N, by positivity, hN0, ?_⟩
    intro τ j hτ
    fin_cases j
    · rw [← norm_qParamFun τ]
      refine le_trans (h10 τ hτ) ?_
      have hc : C10 ≤ |max C10 C11| + 1 := by
        linarith [le_max_left C10 C11, le_abs_self (max C10 C11)]
      have hsN : (0 : ℝ) ≤ Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖ :=
        mul_nonneg (ft_scale_rpow_nonneg τ N) (norm_nonneg _)
      calc C10 * Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖
          = C10 * (Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖) := by ring
        _ ≤ (|max C10 C11| + 1) * (Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖) :=
            mul_le_mul_of_nonneg_right hc hsN
        _ = (|max C10 C11| + 1) * Work.Kernels.scale τ ^ N
            * ‖Work.Kernels.qParamFun τ‖ := by ring
    · rw [← norm_qParamFun τ]
      refine le_trans (h11 τ hτ) ?_
      have hc : C11 ≤ |max C10 C11| + 1 := by
        linarith [le_max_right C10 C11, le_abs_self (max C10 C11)]
      have hsN : (0 : ℝ) ≤ Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖ :=
        mul_nonneg (ft_scale_rpow_nonneg τ N) (norm_nonneg _)
      calc C11 * Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖
          = C11 * (Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖) := by ring
        _ ≤ (|max C10 C11| + 1) * (Work.Kernels.scale τ ^ N * ‖Work.Kernels.qParamFun τ‖) :=
            mul_le_mul_of_nonneg_right hc hsN
        _ = (|max C10 C11| + 1) * Work.Kernels.scale τ ^ N
            * ‖Work.Kernels.qParamFun τ‖ := by ring

end

end Work.Asymptotics
