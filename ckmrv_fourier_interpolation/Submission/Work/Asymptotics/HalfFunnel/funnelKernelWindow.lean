import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.funnelKernelTail
import Submission.Work.Asymptotics.HalfFunnel.funnelPreDeclash
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.HalfFunnel.KaxisWindowPoly

namespace Work.Asymptotics.HalfFunnel

open UpperHalfPlane Work.Kernels Work.Asymptotics

noncomputable section

/-
# The CKMRV kernel below the pole on the funnel: `‖K - 𝒢‖` is polynomially bounded

On the funnel `{τ ∈ 𝒟 : 2 ≤ Im τ}` and in the window `1 ≤ t ≤ Im τ - 1` (i.e. keeping distance
`≥ 1` from the pole height `t = Im τ`), the difference between the CKMRV kernel `Kaxis (Kfun ℓ d)`
and its cusp-`i∞` non-decaying part `Aexp (Gcusp ℓ d)` is bounded by a *polynomial* in
`(scale τ, t)`.

## Why this is not a consequence of the imported funnel estimates

* `funnelKernelPre` bounds `‖Kaxis‖` on the same window only by `C (scale τ)^N (1+t)^M e^{2πt}`
  for `d = 24` (the `e^{2πt}` comes from `1/Δ(z)^e`); the true kernel is *much* smaller there.
* `funnelKernelTail` applies only for `t ≥ Im τ + 1`.
* `funnelKernelSpike` covers `|t - Im τ| ≤ 1` and subtracts the poles.

## What makes it true (two ingredients)

1. `Gcusp ℓ d 1 j` is *exponentially small* on the funnel: the `q⁰`-parts of the explicit
   combinations cancel (`-(i/288)(p0 E14 + p2 E10) + (i/144) p1 E4³ = 0` and
   `p0 E14 + p2 E10 - 2 p1 E4³ = 0` at `E2 = E4 = E6 = 1`), leaving `O(scale τ^N e^{-2π Im τ})`
   (numerically `|Gcusp 24 1 0(iT)| = T e^{-2πT}`, `|Gcusp 24 1 1(iT)| = e^{-2πT}` exactly;
   use the theta conventions `θ00 = 1 + 2Σ e^{πi n²τ}`, `θ10 = 2Σ e^{πi(n+1/2)²τ}` — the script
   `_mine/chk_gcusp.py` uses the `θ(0|2τ)` conventions and therefore gets a spurious `e^{-πt}`).
   Hence `e^{2πt}‖G 1 j‖ ≤ O(scale τ^N)` on the whole window, so `Aexp` — and in particular its
   *polynomial* part `G 0 0 + i t G 0 1` — is polynomially bounded.
2. `Kaxis` is polynomially bounded (indeed `K ≈ e^{2πt}G 1 0 + O(poly)`): the poles of
   `z ↦ K(τ,z)` of height in `[1, Im τ - 1]` are a positive distance from the contour, and the
   translate poles at height `Im τ` are at distance `min(|Re τ ∓ 1|, ...)` — for `t ≤ Im τ - 1`
   the pole `z = τ ∓ 1` is at distance `≥ 1` in the imaginary direction.

Suggested route: use the *cleared* kernel `KfunClear = growthPrefactor · Kfun` (moderate growth,
`Work.Asymptotics.KClear_mg2`) together with the *algebraic cancellation* of the `e^{2πt}`-row of
the explicit formula (`Compact.Gcoef`, `Compact.Gfun`, `Work.Asymptotics.Gcusp_eq_Gcoef`), or a
maximum-principle argument in the pole-free strip `1 ≤ Im z ≤ Im τ - 1`; note that
`cusp_expansion_of_kernel` is *not* applicable (its threshold is `(scale τ)^{N₀}`),
and `TailBound` is false on `𝒟`.

Keep the import list: `Submission.Work.Asymptotics.funnelKernelTail` and
`Submission.Work.Asymptotics.HalfFunnel.funnelPreDeclash` cannot be combined with
`Submission.Work.Asymptotics.funnelKernelPre`/`KernelBoundAux` (name clash on
`Work.Asymptotics.continuous_scale`).
-/

/-! ## Helpers -/

/-- Monotonicity of the model bound `C S^N T^M` in the exponents, for `S, T ≥ 1` and `C ≥ 0`. -/
private theorem bound_mono {S T C N1 N2 M1 M2 : ℝ} (hS : 1 ≤ S) (hT : 1 ≤ T) (hC : 0 ≤ C)
    (hN : N1 ≤ N2) (hM : M1 ≤ M2) : C * S ^ N1 * T ^ M1 ≤ C * S ^ N2 * T ^ M2 := by
  have hS0 : (0:ℝ) ≤ S := le_trans zero_le_one hS
  have hT0 : (0:ℝ) ≤ T := le_trans zero_le_one hT
  have hs : S ^ N1 ≤ S ^ N2 := Real.rpow_le_rpow_of_exponent_le hS hN
  have ht : T ^ M1 ≤ T ^ M2 := Real.rpow_le_rpow_of_exponent_le hT hM
  calc C * S ^ N1 * T ^ M1 = (C * S ^ N1) * T ^ M1 := by ring
    _ ≤ (C * S ^ N2) * T ^ M2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hs hC) ht (Real.rpow_nonneg hT0 _)
          (mul_nonneg hC (Real.rpow_nonneg hS0 _))
    _ = C * S ^ N2 * T ^ M2 := by ring

/-- `‖(c:ℂ) * I * z‖ = c * ‖z‖` for `c ≥ 0`. -/
private lemma norm_ofReal_I_mul {c : ℝ} (hc : 0 ≤ c) (z : ℂ) :
    ‖(c : ℂ) * Complex.I * z‖ = c * ‖z‖ := by
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hc]

/-- `Gcusp ℓ 8` has vanishing `i = 1` row. -/
private lemma Gcusp_eight_one (ℓ : Work.Kernels.LogLambdaData) (j : Fin 2)
    (τ : UpperHalfPlane) : Work.Asymptotics.Gcusp ℓ 8 1 j τ = 0 := by
  rw [Work.Asymptotics.Gcusp, if_pos rfl]
  fin_cases j <;> simp [Work.Asymptotics.Gcusp8]

/-! ## The `d = 8` case -/

/-- **`funnelKernelWindow` in dimension `8`.**  Since `Gcusp ℓ 8 1 j = 0`, the cusp model
`Aexp (Gcusp ℓ 8) τ t = 𝒢_{0,0}(τ) + it𝒢_{0,1}(τ)` is of moderate growth, and the kernel itself
is polynomially bounded on the window by `funnelPreDeclash` (whose exponential factor is `1` in
dimension `8`). -/
theorem funnelKernelWindow_eight (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        1 ≤ t → t ≤ τ.im - 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 8) τ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 8) τ t‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨Ck, Nk, Mk, hCk, hNk, hMk, hkb⟩ :=
    (Work.Asymptotics.HalfFunnel.funnelPreDeclash ℓ 8 (Or.inl rfl)).1
  obtain ⟨a0, n0, ha0, hn0, hb0⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale _ _).mp (Work.Asymptotics.GcuspInP ℓ 8 0 0)
  obtain ⟨a1, n1, ha1, hn1, hb1⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale _ _).mp (Work.Asymptotics.GcuspInP ℓ 8 0 1)
  set N : ℝ := max Nk (max n0 n1 + 1) with hNdef
  set M : ℝ := max Mk 0 with hMdef
  refine ⟨Ck + a0 + a1, N, M, by positivity, ?_, ?_, ?_⟩
  · rw [hNdef]; exact le_max_of_le_left hNk
  · rw [hMdef]; exact le_max_of_le_right (by norm_num)
  · intro τ t hτ hτ2 ht1 htwin
    have hscale1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hscalepos : (0 : ℝ) < Work.Kernels.scale τ := lt_of_lt_of_le zero_lt_one hscale1
    have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht1
    have hT1 : (1:ℝ) ≤ 1 + t := by linarith
    have htT : t ≤ τ.im := by linarith
    have htS : t ≤ Work.Kernels.scale τ :=
      le_trans (le_trans htT (Work.Kernels.im_le_coe_norm τ))
        (Work.Kernels.coe_norm_le_scale τ)
    have hN1 : Nk ≤ N := by rw [hNdef]; exact le_max_left _ _
    have hN2 : max n0 n1 + 1 ≤ N := by rw [hNdef]; exact le_max_right _ _
    have hM1 : Mk ≤ M := by rw [hMdef]; exact le_max_left _ _
    have hM0 : (0:ℝ) ≤ M := by rw [hMdef]; exact le_max_right _ _
    -- kernel
    have hK : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 8) τ t‖
        ≤ Ck * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
      refine le_trans (hkb τ t hτ hτ2 ht1 htwin) ?_
      simpa using bound_mono hscale1 hT1 hCk.le hN1 hM1
    -- model
    have hAeq : Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 8) τ t
        = Work.Asymptotics.Gcusp ℓ 8 0 0 τ
          + (t : ℂ) * Complex.I * (Work.Asymptotics.Gcusp ℓ 8 0 1 τ) := by
      simp only [Work.Asymptotics.Aexp, Gcusp_eight_one ℓ 0 τ, Gcusp_eight_one ℓ 1 τ]
      ring
    have hA : ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 8) τ t‖
        ≤ (a0 + a1) * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
      rw [hAeq]
      have h1 : ‖Work.Asymptotics.Gcusp ℓ 8 0 0 τ‖ ≤ a0 * (Work.Kernels.scale τ) ^ n0 :=
        hb0 τ hτ
      have h2 : ‖(t : ℂ) * Complex.I * (Work.Asymptotics.Gcusp ℓ 8 0 1 τ)‖
          = t * ‖Work.Asymptotics.Gcusp ℓ 8 0 1 τ‖ := norm_ofReal_I_mul ht0 _
      have h3 : t * ‖Work.Asymptotics.Gcusp ℓ 8 0 1 τ‖
          ≤ Work.Kernels.scale τ * (a1 * (Work.Kernels.scale τ) ^ n1) :=
        mul_le_mul htS (hb1 τ hτ) (norm_nonneg _) (le_trans zero_le_one hscale1)
      have h4 : Work.Kernels.scale τ * (a1 * (Work.Kernels.scale τ) ^ n1)
          = a1 * (Work.Kernels.scale τ) ^ (n1 + 1) := by
        rw [Real.rpow_add_one (ne_of_gt hscalepos)]; ring
      have h5 : a1 * (Work.Kernels.scale τ) ^ (n1 + 1)
          ≤ a1 * (Work.Kernels.scale τ) ^ (max n0 n1 + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ ha1
        exact Real.rpow_le_rpow_of_exponent_le hscale1 (by linarith [le_max_right n0 n1])
      have h6 : a0 * (Work.Kernels.scale τ) ^ n0
          ≤ a0 * (Work.Kernels.scale τ) ^ (max n0 n1 + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ ha0
        exact Real.rpow_le_rpow_of_exponent_le hscale1 (by linarith [le_max_left n0 n1])
      have h7 : (a0 + a1) * (Work.Kernels.scale τ) ^ (max n0 n1 + 1)
          ≤ (a0 + a1) * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
        have h1' := bound_mono hscale1 hT1 (by positivity : (0:ℝ) ≤ a0 + a1) hN2 hM0
        calc (a0 + a1) * (Work.Kernels.scale τ) ^ (max n0 n1 + 1)
            = (a0 + a1) * (Work.Kernels.scale τ) ^ (max n0 n1 + 1) * (1 + t) ^ (0:ℝ) := by
              rw [Real.rpow_zero, mul_one]
          _ ≤ (a0 + a1) * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := h1'
      calc ‖Work.Asymptotics.Gcusp ℓ 8 0 0 τ
              + (t : ℂ) * Complex.I * (Work.Asymptotics.Gcusp ℓ 8 0 1 τ)‖
          ≤ ‖Work.Asymptotics.Gcusp ℓ 8 0 0 τ‖
              + ‖(t : ℂ) * Complex.I * (Work.Asymptotics.Gcusp ℓ 8 0 1 τ)‖ := norm_add_le _ _
        _ ≤ a0 * (Work.Kernels.scale τ) ^ n0 + a1 * (Work.Kernels.scale τ) ^ (n1 + 1) := by
            rw [h2]; exact add_le_add h1 (le_trans h3 (le_of_eq h4))
        _ ≤ (a0 + a1) * (Work.Kernels.scale τ) ^ (max n0 n1 + 1) := by
            have := h6; have := h5
            nlinarith [h5, h6,
              Real.rpow_nonneg (by positivity : (0:ℝ) ≤ Work.Kernels.scale τ) (max n0 n1 + 1)]
        _ ≤ (a0 + a1) * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := h7
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 8) τ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 8) τ t‖
        ≤ ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 8) τ t‖
            + ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 8) τ t‖ := norm_sub_le _ _
      _ ≤ Ck * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            + (a0 + a1) * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := add_le_add hK hA
      _ = (Ck + a0 + a1) * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by ring

def Aleading (τ : UpperHalfPlane) : ℂ :=
  (E2Fun τ * E4Fun τ - E6Fun τ) * (E2Fun τ * E6Fun τ - E4Fun τ ^ 2)
def Fleading (τ : UpperHalfPlane) : ℂ :=
  7 * E4Fun τ ^ 3 + 5 * E6Fun τ ^ 2
    - 12 * (E2Fun τ * E4Fun τ * E6Fun τ)
    - 2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) * Aleading τ

set_option maxHeartbeats 2000000 in
lemma Fleading_qParam_bound (ℓ : LogLambdaData) : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ →
    ‖Fleading τ‖ ≤ C * (scale τ) ^ (1:ℝ) * ‖qParamFun τ‖ := by
  obtain ⟨C2, hC2pos, hC2⟩ := E2Fun_two_term
  obtain ⟨C4, hC4pos, hC4⟩ := Work.Residues.E4FunSecondOrder
  obtain ⟨C6, hC6pos, hC6⟩ := Work.Residues.E6FunSecondOrder
  have hC2nn : (0:ℝ) ≤ C2 := hC2pos.le
  have hC4nn : (0:ℝ) ≤ C4 := hC4pos.le
  have hC6nn : (0:ℝ) ≤ C6 := hC6pos.le
  set K : ℝ := C2 + C4 + C6 + 504 + 1 with hKdef
  have hK1 : (1:ℝ) ≤ K := by rw [hKdef]; linarith
  have hKpos : (0:ℝ) < K := lt_of_lt_of_le zero_lt_one hK1
  have hKnn : (0:ℝ) ≤ K := hKpos.le
  have hK24 : (C2 + 24 : ℝ) ≤ K := by rw [hKdef]; linarith
  have hK240 : (C4 + 240 : ℝ) ≤ K := by rw [hKdef]; linarith
  have hK504 : (C6 + 504 : ℝ) ≤ K := by rw [hKdef]; linarith
  have hKC2 : C2 ≤ K := by rw [hKdef]; linarith
  have hKC4 : C4 ≤ K := by rw [hKdef]; linarith
  have hKC6 : C6 ≤ K := by rw [hKdef]; linarith
  set MM : ℝ := 2 * Real.pi * ((3 * K + K ^ 2) * (4 * K + 2 * K ^ 2)) with hMM
  set Cc : ℝ := 3456 + 23 * K + 62 * K ^ 2 + 19 * K ^ 3 + MM with hCc
  refine ⟨Cc, by rw [hCc]; positivity, fun τ hτ => ?_⟩
  have hτ2 : 2 ≤ τ.im := hτ.2
  have hτ1 : 1 ≤ τ.im := by linarith
  have hsc : (1:ℝ) ≤ scale τ := Work.Kernels.one_le_scale τ
  set Q : ℂ := qParamFun τ with hQ
  set q : ℝ := ‖Q‖ with hq
  have hqnn : 0 ≤ q := norm_nonneg _
  have hqeq : q = Real.exp (-(2*Real.pi*τ.im)) := by rw [hq, hQ, norm_qParamFun]
  have hq1 : q ≤ 1 := by
    rw [hqeq, Real.exp_le_one_iff]; nlinarith [Real.pi_pos]
  have hqle : q ^ 2 ≤ q := by nlinarith
  have hqle3 : q ^ 3 ≤ q := by nlinarith
  have hd2 : ‖E2Fun τ - 1 + 24 * Q‖ ≤ C2 * q ^ 2 := by rw [hQ, hq]; exact hC2 τ hτ1
  have hd4 : ‖E4Fun τ - 1 - 240 * Q‖ ≤ C4 * q ^ 2 := by rw [hQ, hq]; exact hC4 τ hτ1
  have hd6 : ‖E6Fun τ - 1 + 504 * Q‖ ≤ C6 * q ^ 2 := by rw [hQ, hq]; exact hC6 τ hτ1
  have hq2 : ‖(24:ℂ) * Q‖ = 24 * q := by rw [norm_mul, Complex.norm_ofNat, hq]
  have hq4 : ‖(240:ℂ) * Q‖ = 240 * q := by rw [norm_mul, Complex.norm_ofNat, hq]
  have hq6 : ‖(504:ℂ) * Q‖ = 504 * q := by rw [norm_mul, Complex.norm_ofNat, hq]
  have hx : ‖E4Fun τ - 1‖ ≤ K * q := by
    have hsplit : E4Fun τ - 1 = (E4Fun τ - 1 - 240 * Q) + 240 * Q := by ring
    have h3 : ‖(E4Fun τ - 1 - 240 * Q) + 240 * Q‖ ≤ C4 * q ^ 2 + 240 * q := by
      refine le_trans (norm_add_le _ _) ?_
      rw [hq4]; exact add_le_add hd4 le_rfl
    rw [hsplit]
    have h4 : C4 * q ^ 2 ≤ C4 * q := mul_le_mul_of_nonneg_left hqle hC4nn
    have h5 : (C4 + 240) * q ≤ K * q := mul_le_mul_of_nonneg_right hK240 hqnn
    have h6 : C4 * q ^ 2 + 240 * q ≤ K * q := by nlinarith
    linarith
  have hy : ‖E6Fun τ - 1‖ ≤ K * q := by
    have hsplit : E6Fun τ - 1 = (E6Fun τ - 1 + 504 * Q) - 504 * Q := by ring
    have h3 : ‖(E6Fun τ - 1 + 504 * Q) - 504 * Q‖ ≤ C6 * q ^ 2 + 504 * q := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [hq6]; exact add_le_add hd6 le_rfl
    rw [hsplit]
    have h4 : C6 * q ^ 2 ≤ C6 * q := mul_le_mul_of_nonneg_left hqle hC6nn
    have h5 : (C6 + 504) * q ≤ K * q := mul_le_mul_of_nonneg_right hK504 hqnn
    have h6 : C6 * q ^ 2 + 504 * q ≤ K * q := by nlinarith
    linarith
  have hu : ‖E2Fun τ - 1‖ ≤ K * q := by
    have hsplit : E2Fun τ - 1 = (E2Fun τ - 1 + 24 * Q) - 24 * Q := by ring
    have h3 : ‖(E2Fun τ - 1 + 24 * Q) - 24 * Q‖ ≤ C2 * q ^ 2 + 24 * q := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [hq2]; exact add_le_add hd2 le_rfl
    rw [hsplit]
    have h4 : C2 * q ^ 2 ≤ C2 * q := mul_le_mul_of_nonneg_left hqle hC2nn
    have h5 : (C2 + 24) * q ≤ K * q := mul_le_mul_of_nonneg_right hK24 hqnn
    have h6 : C2 * q ^ 2 + 24 * q ≤ K * q := by nlinarith
    linarith
  set x : ℂ := E4Fun τ - 1 with hxdef
  set y : ℂ := E6Fun τ - 1 with hydef
  set u : ℂ := E2Fun τ - 1 with hudef
  set d2 : ℂ := E2Fun τ - 1 + 24 * Q with hd2def
  set d4 : ℂ := E4Fun τ - 1 - 240 * Q with hd4def
  set d6 : ℂ := E6Fun τ - 1 + 504 * Q with hd6def
  have hE2r : E2Fun τ = 1 + u := by rw [hudef]; ring
  have hE4r : E4Fun τ = 1 + x := by rw [hxdef]; ring
  have hE6r : E6Fun τ = 1 + y := by rw [hydef]; ring
  have hd2r : d2 = u + 24 * Q := by rw [hd2def, hudef]
  have hd4r : d4 = x - 240 * Q := by rw [hd4def, hxdef]
  have hd6r : d6 = y + 504 * Q := by rw [hd6def, hydef]
  -- the two factors of A
  have hA : Aleading τ = ((1+u)*(1+x)-(1+y)) * ((1+u)*(1+y)-(1+x)^2) := by
    rw [Aleading, hE2r, hE4r, hE6r]
  have hKq2 : (K*q)*(K*q) ≤ K^2 * q := by nlinarith [hqnn, hqle, sq_nonneg K, hK1]
  have hKq3 : (K*q)*(K*q)*(K*q) ≤ K^3 * q := by
    have h2 : (K*q)*(K*q)*(K*q) = ((K*q)*(K*q))*(K*q) := by ring
    rw [h2]
    have h3 : ((K*q)*(K*q))*(K*q) ≤ (K^2*q)*(K*q) :=
      mul_le_mul_of_nonneg_right hKq2 (by positivity)
    have h4 : (K^2*q)*(K*q) ≤ K^3*q := by
      have : (K^2*q)*(K*q) = K^3*q^2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hqle (by positivity)
    exact le_trans h3 h4
  have hfac1 : ‖(1+u)*(1+x)-(1+y)‖ ≤ (3*K + K^2) * q := by
    have h1 : (1+u)*(1+x)-(1+y) = u + x - y + u*x := by ring
    rw [h1]
    have h2 : ‖u + x - y + u*x‖ ≤ ‖u‖ + ‖x‖ + ‖y‖ + ‖u*x‖ := by
      calc ‖u + x - y + u*x‖ = ‖(u + x - y) + u*x‖ := by
            rw [show u + x - y + u*x = (u + x - y) + u*x from by ring]
        _ ≤ ‖u + x - y‖ + ‖u*x‖ := norm_add_le _ _
        _ ≤ (‖u + x‖ + ‖y‖) + ‖u*x‖ := by
            have := norm_sub_le (u+x) y; linarith
        _ ≤ ((‖u‖ + ‖x‖) + ‖y‖) + ‖u*x‖ := by
            have := norm_add_le u x; linarith
        _ = ‖u‖ + ‖x‖ + ‖y‖ + ‖u*x‖ := by ring
    have hmul : ‖u * x‖ ≤ K^2 * q := by
      rw [norm_mul]
      have h3 := mul_le_mul hu hx (norm_nonneg x) (by positivity : (0:ℝ) ≤ K*q)
      linarith [h3, hKq2]
    have hsum : ‖u‖ + ‖x‖ + ‖y‖ + ‖u*x‖ ≤ (K*q)+(K*q)+(K*q) + K^2*q := by linarith
    have heq : (K*q)+(K*q)+(K*q) + K^2*q = (3*K + K^2)*q := by ring
    linarith [h2, hsum, heq.le, heq.ge]
  have hfac2 : ‖(1+u)*(1+y)-(1+x)^2‖ ≤ (4*K + 2*K^2) * q := by
    have h1 : (1+u)*(1+y)-(1+x)^2 = u + y - 2*x + u*y - x^2 := by ring
    rw [h1]
    have hx2 : ‖x^2‖ ≤ (K*q)*(K*q) := by
      have h := pow_le_pow_left₀ (norm_nonneg x) hx 2
      rw [norm_pow]
      rwa [show (K*q)^2 = (K*q)*(K*q) from by ring] at h
    have huy : ‖u * y‖ ≤ (K*q)*(K*q) := by
      rw [norm_mul]
      exact mul_le_mul hu hy (norm_nonneg y) (by positivity)
    have h2 : ‖u + y - 2*x + u*y - x^2‖ ≤ ‖u‖ + ‖y‖ + 2*‖x‖ + ‖u*y‖ + ‖x^2‖ := by
      have e2 : ‖(2:ℂ)*x‖ = 2*‖x‖ := by rw [norm_mul, Complex.norm_ofNat]
      calc ‖u + y - 2*x + u*y - x^2‖ = ‖(u + y - 2*x + u*y) + (-(x^2))‖ := by
            rw [show u + y - 2*x + u*y - x^2 = (u + y - 2*x + u*y) + (-(x^2)) from by ring]
        _ ≤ ‖u + y - 2*x + u*y‖ + ‖-(x^2)‖ := norm_add_le _ _
        _ = ‖u + y - 2*x + u*y‖ + ‖x^2‖ := by rw [norm_neg]
        _ ≤ (‖u + y - 2*x‖ + ‖u*y‖) + ‖x^2‖ := by
            have := norm_add_le (u + y - 2*x) (u*y); linarith
        _ ≤ ((‖u+y‖ + 2*‖x‖) + ‖u*y‖) + ‖x^2‖ := by
            have := norm_sub_le (u+y) (2*x); rw [e2] at this; linarith
        _ ≤ (((‖u‖+‖y‖) + 2*‖x‖) + ‖u*y‖) + ‖x^2‖ := by
            have := norm_add_le u y; linarith
        _ = ‖u‖ + ‖y‖ + 2*‖x‖ + ‖u*y‖ + ‖x^2‖ := by ring
    have hA : ‖u‖ + ‖y‖ + 2*‖x‖ ≤ 4*(K*q) := by
      have h3 : 2*‖x‖ ≤ 2*(K*q) := by linarith
      linarith
    have hB : ‖u*y‖ + ‖x^2‖ ≤ 2*(K^2*q) := by nlinarith [huy, hx2, hKq2]
    have heq : 4*(K*q) + 2*(K^2*q) = (4*K + 2*K^2)*q := by ring
    linarith [h2, hA, hB, heq.le, heq.ge]
  -- the four blocks
  set DL : ℂ := 9*d4 - 2*d6 - 12*d2 with hDLdef
  set DE : ℂ := 21*x^2 + 5*y^2 - 12*(u*x+u*y+x*y) with hDEdef
  set DC : ℂ := 7*x^3 - 12*(u*x*y) with hDCdef
  set DD : ℂ := 2*(Real.pi : ℂ)*Complex.I*(τ : ℂ)
      *(((1+u)*(1+x)-(1+y)) * ((1+u)*(1+y)-(1+x)^2)) with hDDdef
  set R : ℂ := ((DL + DE) + DC) + (-DD) with hRdef
  have hd2b : ‖d2‖ ≤ K * q^2 := le_trans hd2 (mul_le_mul_of_nonneg_right hKC2 (sq_nonneg q))
  have hd4b : ‖d4‖ ≤ K * q^2 := le_trans hd4 (mul_le_mul_of_nonneg_right hKC4 (sq_nonneg q))
  have hd6b : ‖d6‖ ≤ K * q^2 := le_trans hd6 (mul_le_mul_of_nonneg_right hKC6 (sq_nonneg q))
  have hF : Fleading τ = 3456*Q + R := by
    rw [hRdef, hDLdef, hDEdef, hDCdef, hDDdef, Fleading, hA, hE2r, hE4r, hE6r, hd2r, hd4r, hd6r]
    ring
  -- the four individual bounds
  have hd2q : ‖d2‖ ≤ K * q := by
    have h : K * q^2 ≤ K * q := mul_le_mul_of_nonneg_left hqle hKnn
    linarith [hd2b]
  have hd4q : ‖d4‖ ≤ K * q := by
    have h : K * q^2 ≤ K * q := mul_le_mul_of_nonneg_left hqle hKnn
    linarith [hd4b]
  have hd6q : ‖d6‖ ≤ K * q := by
    have h : K * q^2 ≤ K * q := mul_le_mul_of_nonneg_left hqle hKnn
    linarith [hd6b]
  have hDLb : ‖DL‖ ≤ 23 * K * q := by
    have t1 : ‖DL‖ ≤ 9*‖d4‖ + 2*‖d6‖ + 12*‖d2‖ := by
      rw [hDLdef]
      have a := norm_sub_le ((9:ℂ)*d4 - (2:ℂ)*d6) ((12:ℂ)*d2)
      have b := norm_sub_le ((9:ℂ)*d4) ((2:ℂ)*d6)
      have ea : ‖((12:ℂ)*d2)‖ = 12*‖d2‖ := by rw [norm_mul, Complex.norm_ofNat]
      have eb : ‖((9:ℂ)*d4)‖ = 9*‖d4‖ := by rw [norm_mul, Complex.norm_ofNat]
      have ec : ‖((2:ℂ)*d6)‖ = 2*‖d6‖ := by rw [norm_mul, Complex.norm_ofNat]
      rw [ea] at a
      rw [eb, ec] at b
      linarith
    have heq : 9*(K*q) + 2*(K*q) + 12*(K*q) = 23*K*q := by ring
    linarith [t1, hd4q, hd6q, hd2q, heq.le, heq.ge]
  have hDEb : ‖DE‖ ≤ 62 * K^2 * q := by
    have t1 : ‖DE‖ ≤ 21*‖x^2‖ + 5*‖y^2‖ + 12*(‖u*x‖ + ‖u*y‖ + ‖x*y‖) := by
      rw [hDEdef]
      have a := norm_sub_le ((21:ℂ)*x^2 + (5:ℂ)*y^2) ((12:ℂ)*(u*x+u*y+x*y))
      have b := norm_add_le ((21:ℂ)*x^2) ((5:ℂ)*y^2)
      have c := norm_add_le (u*x + u*y) (x*y)
      have d := norm_add_le (u*x) (u*y)
      have ea : ‖((12:ℂ)*(u*x+u*y+x*y))‖ = 12*‖u*x+u*y+x*y‖ := by
        rw [norm_mul, Complex.norm_ofNat]
      have eb : ‖((21:ℂ)*x^2)‖ = 21*‖x^2‖ := by rw [norm_mul, Complex.norm_ofNat]
      have ec : ‖((5:ℂ)*y^2)‖ = 5*‖y^2‖ := by rw [norm_mul, Complex.norm_ofNat]
      rw [ea] at a
      rw [eb, ec] at b
      linarith
    have hxx : ‖x^2‖ ≤ (K*q)*(K*q) := by
      have h := pow_le_pow_left₀ (norm_nonneg x) hx 2
      rw [norm_pow]
      rwa [show (K*q)^2 = (K*q)*(K*q) from by ring] at h
    have hyy : ‖y^2‖ ≤ (K*q)*(K*q) := by
      have h := pow_le_pow_left₀ (norm_nonneg y) hy 2
      rw [norm_pow]
      rwa [show (K*q)^2 = (K*q)*(K*q) from by ring] at h
    have hu1 : ‖u*x‖ ≤ (K*q)*(K*q) := by
      rw [norm_mul]; exact mul_le_mul hu hx (norm_nonneg x) (by positivity)
    have hu2 : ‖u*y‖ ≤ (K*q)*(K*q) := by
      rw [norm_mul]; exact mul_le_mul hu hy (norm_nonneg y) (by positivity)
    have hxy : ‖x*y‖ ≤ (K*q)*(K*q) := by
      rw [norm_mul]; exact mul_le_mul hx hy (norm_nonneg y) (by positivity)
    have heq : 21*((K*q)*(K*q)) + 5*((K*q)*(K*q))
        + 12*((K*q)*(K*q) + (K*q)*(K*q) + (K*q)*(K*q)) = 62 * ((K*q)*(K*q)) := by ring
    have hfin : 62 * ((K*q)*(K*q)) ≤ 62 * K^2 * q := by
      have h := hKq2; nlinarith
    linarith [t1, hxx, hyy, hu1, hu2, hxy, heq.le, heq.ge, hfin]
  have hDCb : ‖DC‖ ≤ 19 * K^3 * q := by
    have t1 : ‖DC‖ ≤ 7*‖x^3‖ + 12*‖u*x*y‖ := by
      rw [hDCdef]
      have a := norm_sub_le ((7:ℂ)*x^3) ((12:ℂ)*(u*x*y))
      have e1 : ‖((7:ℂ)*x^3)‖ = 7*‖x^3‖ := by rw [norm_mul, Complex.norm_ofNat]
      have e2 : ‖((12:ℂ)*(u*x*y))‖ = 12*‖u*x*y‖ := by rw [norm_mul, Complex.norm_ofNat]
      rw [e1, e2] at a
      exact a
    have hxxx : ‖x^3‖ ≤ (K*q)*(K*q)*(K*q) := by
      have h := pow_le_pow_left₀ (norm_nonneg x) hx 3
      rw [norm_pow]
      rwa [show (K*q)^3 = (K*q)*(K*q)*(K*q) from by ring] at h
    have huxy : ‖u*x*y‖ ≤ (K*q)*(K*q)*(K*q) := by
      have h1 : ‖u*x‖ ≤ (K*q)*(K*q) := by
        rw [norm_mul]; exact mul_le_mul hu hx (norm_nonneg x) (by positivity)
      have h := mul_le_mul h1 hy (norm_nonneg y) (by positivity)
      rw [norm_mul]
      exact h
    have heq : 7*((K*q)*(K*q)*(K*q)) + 12*((K*q)*(K*q)*(K*q))
        = 19*((K*q)*(K*q)*(K*q)) := by ring
    have hfin : 19*((K*q)*(K*q)*(K*q)) ≤ 19 * K^3 * q := by
      have h := hKq3; nlinarith
    linarith [t1, hxxx, huxy, heq.le, heq.ge, hfin]
  have hDDb : ‖DD‖ ≤ MM*‖(τ:ℂ)‖*q := by
    have hprod : ‖((1+u)*(1+x)-(1+y)) * ((1+u)*(1+y)-(1+x)^2)‖
        ≤ ((3*K+K^2)*q) * ((4*K+2*K^2)*q) := by
      rw [norm_mul]
      exact mul_le_mul hfac1 hfac2 (norm_nonneg _) (by positivity)
    rw [hDDdef]
    have hnorm : ‖2*(Real.pi : ℂ)*Complex.I*(τ : ℂ)
        *(((1+u)*(1+x)-(1+y)) * ((1+u)*(1+y)-(1+x)^2))‖
        = 2*Real.pi*‖(τ:ℂ)‖*‖((1+u)*(1+x)-(1+y)) * ((1+u)*(1+y)-(1+x)^2)‖ := by
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
      try ring
    rw [hnorm]
    have h2 : ((3*K+K^2)*q) * ((4*K+2*K^2)*q) ≤ (3*K+K^2)*(4*K+2*K^2)*q := by
      have h : ((3*K+K^2)*q) * ((4*K+2*K^2)*q) = (3*K+K^2)*(4*K+2*K^2)*q^2 := by ring
      rw [h]
      exact mul_le_mul_of_nonneg_left hqle (by positivity)
    rw [hMM]
    calc 2*Real.pi*‖(τ:ℂ)‖*‖((1+u)*(1+x)-(1+y)) * ((1+u)*(1+y)-(1+x)^2)‖
        ≤ 2*Real.pi*‖(τ:ℂ)‖*(((3*K+K^2)*q) * ((4*K+2*K^2)*q)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ ≤ 2*Real.pi*‖(τ:ℂ)‖*((3*K+K^2)*(4*K+2*K^2)*q) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2*Real.pi*((3*K+K^2)*(4*K+2*K^2))*‖(τ:ℂ)‖*q := by ring
  have hRbound : ‖R‖ ≤ 23*K*q + 62*K^2*q + 19*K^3*q + MM*‖(τ:ℂ)‖*q := by
    have tR : ‖R‖ ≤ ‖DL‖ + ‖DE‖ + ‖DC‖ + ‖DD‖ := by
      rw [hRdef]
      have a := norm_add_le (DL + DE + DC) (-DD)
      have b := norm_add_le (DL + DE) DC
      have c := norm_add_le DL DE
      rw [norm_neg] at a
      linarith
    linarith [tR, hDLb, hDEb, hDCb, hDDb]
  -- final assembly
  have hWnn : (0:ℝ) ≤ MM := by rw [hMM]; positivity
  have htau : ‖(τ:ℂ)‖ ≤ scale τ := Work.Kernels.coe_norm_le_scale τ
  have ht : ‖(3456:ℂ)*Q + R‖ ≤ 3456*q + ‖R‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [show ‖(3456:ℂ)*Q‖ = 3456*q from by rw [norm_mul, Complex.norm_ofNat, hq]]
  have hfin : 3456*q + ‖R‖ ≤ Cc * (scale τ) ^ (1:ℝ) * q := by
    have h1 : MM*‖(τ:ℂ)‖*q ≤ MM*scale τ*q := by
      have h : ‖(τ:ℂ)‖*q ≤ scale τ*q := mul_le_mul_of_nonneg_right htau hqnn
      have h2 : MM*‖(τ:ℂ)‖*q = MM*(‖(τ:ℂ)‖*q) := by ring
      have h3 : MM*scale τ*q = MM*(scale τ*q) := by ring
      rw [h2, h3]; exact mul_le_mul_of_nonneg_left h hWnn
    have hqle_s : q ≤ scale τ * q := by nlinarith [hsc, hqnn]
    have hR' : ‖R‖ ≤ 23*K*q + 62*K^2*q + 19*K^3*q + MM*scale τ*q := by
      linarith [hRbound, h1]
    have e0 : 3456*q ≤ 3456*scale τ*q := by
      have h := mul_le_mul_of_nonneg_left hqle_s (by norm_num : (0:ℝ) ≤ 3456)
      calc 3456*q ≤ 3456*(scale τ*q) := h
        _ = 3456*scale τ*q := by ring
    have e2 : 23*K*q ≤ 23*K*scale τ*q := by
      have h := mul_le_mul_of_nonneg_left hqle_s (by positivity : (0:ℝ) ≤ 23*K)
      calc 23*K*q ≤ 23*K*(scale τ*q) := h
        _ = 23*K*scale τ*q := by ring
    have e3 : 62*K^2*q ≤ 62*K^2*scale τ*q := by
      have h := mul_le_mul_of_nonneg_left hqle_s (by positivity : (0:ℝ) ≤ 62*K^2)
      calc 62*K^2*q ≤ 62*K^2*(scale τ*q) := h
        _ = 62*K^2*scale τ*q := by ring
    have e4 : 19*K^3*q ≤ 19*K^3*scale τ*q := by
      have h := mul_le_mul_of_nonneg_left hqle_s (by positivity : (0:ℝ) ≤ 19*K^3)
      calc 19*K^3*q ≤ 19*K^3*(scale τ*q) := h
        _ = 19*K^3*scale τ*q := by ring
    have he : (3456 + 23*K + 62*K^2 + 19*K^3 + MM)*scale τ*q
        = 3456*scale τ*q + 23*K*scale τ*q + 62*K^2*scale τ*q + 19*K^3*scale τ*q
          + MM*scale τ*q := by ring
    have hfold : 3456*q + ‖R‖
        ≤ (3456 + 23*K + 62*K^2 + 19*K^3 + MM)*scale τ*q := by
      rw [he]; linarith [hR', e0, e2, e3, e4]
    rw [hCc, Real.rpow_one]
    linarith [ht, hfold]
  have hfold : ‖Fleading τ‖ ≤ Cc * (scale τ) ^ (1:ℝ) * q := by
    rw [hF]
    linarith [ht, hfin]
  rwa [hq] at hfold


/-! ## The `cuspC` bound and the `E2` bound -/

lemma cuspC_bound (ℓ : LogLambdaData) : ∃ C : ℝ, 0 < C ∧ ‖Work.Asymptotics.Compact.cuspC ℓ‖ ≤ C := by
  obtain ⟨C0, hC0pos, hC0⟩ := Work.Asymptotics.Compact.cuspC_spec ℓ
  obtain ⟨α, β, γ, hα, hβ, hγ, hL⟩ := ℓ.memP
  set z0 : ℍ := (⟨(2:ℂ)*Complex.I, by simp⟩ : ℍ) with hz0
  have h2 : (1:ℝ) ≤ z0.im := by rw [hz0]; simp
  have hLb : ‖ℓ.L z0‖ ≤ α * ((z0.im)⁻¹ ^ β + ‖((z0:ℍ):ℂ)‖ ^ γ) := hL z0 (Set.mem_univ _)
  have hE : ‖Work.Residues.Ept z0‖ ≤ 1 := by
    rw [Work.Residues.norm_Ept]
    rw [Real.exp_le_one_iff]; rw [hz0]; simp [Real.pi_pos.le]
  have hE2 : ‖(Work.Residues.Ept z0)^2‖ ≤ 1 := by
    rw [norm_pow]; have h0 := norm_nonneg (Work.Residues.Ept z0); nlinarith
  set B : ℝ := α * ((z0.im)⁻¹ ^ β + ‖((z0:ℍ):ℂ)‖ ^ γ) + Real.pi * ‖((z0:ℍ):ℂ)‖ + 8 + 12 + C0
    with hB
  refine ⟨B, ?_, ?_⟩
  · rw [hB]; positivity
  · set X : ℂ := ℓ.L z0 - ((Real.pi:ℂ)*Complex.I*((z0:ℍ):ℂ) + Work.Asymptotics.Compact.cuspC ℓ
        - 8*Work.Residues.Ept z0 + 12*(Work.Residues.Ept z0)^2) with hX
    set Y : ℂ := ℓ.L z0 - (Real.pi:ℂ)*Complex.I*((z0:ℍ):ℂ) with hY
    have hXY : Work.Asymptotics.Compact.cuspC ℓ
        = Y - X + (8*(Work.Residues.Ept z0) - 12*(Work.Residues.Ept z0)^2) := by
      rw [hX, hY]; ring
    rw [hXY, hB]
    have hXb : ‖X‖ ≤ C0 := by
      rw [hX]
      refine le_trans (hC0 z0 h2) ?_
      have h3 : ‖Work.Residues.Ept z0‖ ^ 3 ≤ 1 :=
        pow_le_one₀ (norm_nonneg (Work.Residues.Ept z0)) hE
      exact mul_le_of_le_one_right hC0pos.le h3
    have hYb : ‖Y‖ ≤ α * ((z0.im)⁻¹ ^ β + ‖((z0:ℍ):ℂ)‖ ^ γ) + Real.pi * ‖((z0:ℍ):ℂ)‖ := by
      rw [hY]
      have h := norm_sub_le (ℓ.L z0) ((Real.pi:ℂ)*Complex.I*((z0:ℍ):ℂ))
      have hpi : ‖(Real.pi:ℂ)*Complex.I*((z0:ℍ):ℂ)‖ = Real.pi * ‖((z0:ℍ):ℂ)‖ := by
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
      rw [hpi] at h
      linarith [h, hLb]
    have htri : ‖Y - X + (8*(Work.Residues.Ept z0) - 12*(Work.Residues.Ept z0)^2)‖
        ≤ ‖X‖ + ‖Y‖ + 20 := by
      have a := norm_add_le (Y - X) (8*(Work.Residues.Ept z0) - 12*(Work.Residues.Ept z0)^2)
      have b := norm_sub_le Y X
      have d := norm_sub_le ((8:ℂ)*(Work.Residues.Ept z0)) ((12:ℂ)*(Work.Residues.Ept z0)^2)
      have h1 : ‖(8:ℂ)*(Work.Residues.Ept z0)‖ = 8*‖Work.Residues.Ept z0‖ := by
        rw [norm_mul, Complex.norm_ofNat]
      have h2 : ‖(12:ℂ)*(Work.Residues.Ept z0)^2‖ = 12*‖(Work.Residues.Ept z0)^2‖ := by
        rw [norm_mul, Complex.norm_ofNat]
      rw [h1, h2] at d
      have h8 : 8*‖Work.Residues.Ept z0‖ ≤ 8 := by linarith
      have h12 : 12*‖(Work.Residues.Ept z0)^2‖ ≤ 12 := by linarith
      linarith [a, b, d, h8, h12]
    linarith [htri, hXb, hYb]

/-! ## The `i = 1` row of `Gcusp` is exponentially small on the funnel -/

lemma E2Fun_norm_bound : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖E2Fun τ‖ ≤ C := by
  obtain ⟨C2, hC2pos, hC2⟩ := E2Fun_two_term
  refine ⟨1 + 24 + C2, by positivity, fun τ hτ => ?_⟩
  have h := hC2 τ hτ
  have hQ : ‖qParamFun τ‖ ≤ 1 := by
    rw [norm_qParamFun, Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hτ]
  have hsplit : E2Fun τ = (E2Fun τ - 1 + 24 * qParamFun τ) + (1 - 24 * qParamFun τ) := by ring
  rw [hsplit]
  have h24 : ‖(24:ℂ) * qParamFun τ‖ = 24 * ‖qParamFun τ‖ := by rw [norm_mul, Complex.norm_ofNat]
  calc ‖(E2Fun τ - 1 + 24 * qParamFun τ) + (1 - 24 * qParamFun τ)‖
      ≤ ‖E2Fun τ - 1 + 24 * qParamFun τ‖ + (1 + 24 * ‖qParamFun τ‖) := by
        refine le_trans (norm_add_le _ _) ?_
        have h2 : ‖(1:ℂ) - 24 * qParamFun τ‖ ≤ 1 + 24 * ‖qParamFun τ‖ := by
          refine le_trans (norm_sub_le (1:ℂ) (24 * qParamFun τ)) ?_
          rw [h24]; norm_num
        linarith
    _ ≤ C2 * ‖qParamFun τ‖ ^ 2 + (1 + 24 * ‖qParamFun τ‖) := by linarith
    _ ≤ 1 + 24 + C2 := by
        have hQ2 : ‖qParamFun τ‖ ^ 2 ≤ 1 := by nlinarith [hQ, norm_nonneg (qParamFun τ)]
        nlinarith [hC2pos, hQ, hQ2, norm_nonneg (qParamFun τ)]

lemma DeltaFun_eq' (τ : UpperHalfPlane) : Work.Kernels.DeltaFun τ = (E4Fun τ^3 - E6Fun τ^2)/1728 := by
  rw [Work.Kernels.DeltaFun, CuspForm.coe_discriminant]
  exact ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
lemma phiVec_zero' (τ : UpperHalfPlane) : Work.Kernels.phiVec τ 0 = (τ : ℂ) := rfl
lemma phiVec_one' (τ : UpperHalfPlane) : Work.Kernels.phiVec τ 1
    = (τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ) := rfl
lemma phiVec_two' (τ : UpperHalfPlane) : Work.Kernels.phiVec τ 2
    = (τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ := rfl
lemma Gcusp24_one_one_eq (ℓ : LogLambdaData) (τ : UpperHalfPlane) :
    Gcusp ℓ 24 1 1 τ = (Complex.I / 3456) * Fleading τ := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Gcusp, if_neg (by norm_num : ¬ ((24 : ℕ) = 8))]
  unfold Gcusp24
  split_ifs with h1 h2 h3
  · exact absurd h1.1 (by decide)
  · exact absurd h2.1 (by decide)
  · exact absurd h3.2 (by decide)
  · simp only [phiVec_zero', phiVec_one', phiVec_two']
    rw [Fleading, Aleading, DeltaFun_eq' τ]
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
lemma Gcusp24_one_zero_eq (ℓ : LogLambdaData) (τ : UpperHalfPlane) :
    2 * Gcusp ℓ 24 1 0 τ = Fleading τ / (576 * (Real.pi : ℂ))
        + DeltaFun τ * ((cuspL ℓ - 4) / (Real.pi : ℂ)
            - Complex.I * ((τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)))
        + (psi2 ℓ τ * (E4Fun τ * E6Fun τ) - psi4 ℓ τ * E4Fun τ ^ 2) / (1152 * (Real.pi : ℂ)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Gcusp, if_neg (by norm_num : ¬ ((24 : ℕ) = 8))]
  unfold Gcusp24
  split_ifs with h1 h2 h3
  · exact absurd h1.1 (by decide)
  · exact absurd h2.1 (by decide)
  · simp only [phiVec_zero', phiVec_one', phiVec_two']
    rw [Fleading, Aleading, DeltaFun_eq' τ]
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  · exact absurd (by decide : (1 : Fin 2) = 1 ∧ (0 : Fin 2) = 0) h3
lemma cuspL_bound (ℓ : LogLambdaData) : ∃ C : ℝ, 0 < C ∧ ‖cuspL ℓ‖ ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := cuspC_bound ℓ
  exact ⟨C, hCpos, by rw [show cuspL ℓ = Work.Asymptotics.Compact.cuspC ℓ from rfl]; exact hC⟩

set_option maxHeartbeats 3000000 in
theorem GcuspRowOneExpSmall (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ : ℍ) (j : Fin 2),
      τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        ‖Gcusp ℓ d 1 j τ‖ ≤ C * (scale τ) ^ N * Real.exp (-(2 * Real.pi * τ.im)) := by
  rcases hd with h8 | h24
  · subst h8
    refine ⟨1, 0, one_pos, le_rfl, fun τ j _ _ => ?_⟩
    rw [show Gcusp ℓ 8 1 j τ = 0 from by
      rw [Gcusp, if_pos rfl]; fin_cases j <;> simp [Gcusp8]]
    rw [norm_zero, Real.rpow_zero, mul_one]
    exact mul_nonneg (by norm_num) (Real.exp_nonneg _)
  · subst h24
    obtain ⟨CF, hCFpos, hCF⟩ := Fleading_qParam_bound ℓ
    obtain ⟨Cψ, Nψ, hCψpos, hNψ, hψ⟩ := psi4E8_sub_psi2E10_funnel ℓ
    obtain ⟨Cc, hCcpos, hCc⟩ := cuspL_bound ℓ
    obtain ⟨CE2, hCE2pos, hE2⟩ := E2Fun_norm_bound
    set Cχ : ℝ := (Cc + 4) / Real.pi + (CE2 + 3 / Real.pi) with hCχ
    set K : ℝ := CF / (576 * Real.pi) + 2 * Cχ + Cψ / (1152 * Real.pi) with hK
    have hKnn : (0:ℝ) ≤ K := by rw [hK]; positivity
    set Nm : ℝ := max 1 (max 2 Nψ) with hNm
    have hN1 : (1:ℝ) ≤ Nm := by rw [hNm]; exact le_max_left _ _
    have hN2 : (2:ℝ) ≤ Nm := by
      rw [hNm]; exact le_trans (le_max_left 2 Nψ) (le_max_right 1 (max 2 Nψ))
    have hNψ : Nψ ≤ Nm := by
      rw [hNm]; exact le_trans (le_max_right 2 Nψ) (le_max_right 1 (max 2 Nψ))
    have hNmnn : (0:ℝ) ≤ Nm := le_trans zero_le_one hN1
    refine ⟨max (CF / 3456) (K / 2), Nm, lt_max_of_lt_left (by positivity),
      hNmnn, ?_⟩
    intro τ j hτD hτ2
    have hsc : (1:ℝ) ≤ scale τ := Work.Kernels.one_le_scale τ
    have htn : ‖(τ:ℂ)‖ ≤ scale τ := Work.Kernels.coe_norm_le_scale τ
    have hexp : (0:ℝ) < Real.exp (-(2 * Real.pi * τ.im)) := Real.exp_pos _
    have hexpnn : (0:ℝ) ≤ Real.exp (-(2 * Real.pi * τ.im)) := hexp.le
    have hSnn : (0:ℝ) ≤ (scale τ) ^ Nm := Real.rpow_nonneg (by linarith) _
    -- the four ingredient bounds, all in the `Nm` shape
    have hF : ‖Fleading τ‖ ≤ CF * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) := by
      have h := hCF τ ⟨hτD, hτ2⟩
      rw [norm_qParamFun] at h
      refine le_trans h ?_
      have hs : (scale τ) ^ (1:ℝ) ≤ (scale τ) ^ Nm :=
        Real.rpow_le_rpow_of_exponent_le hsc hN1
      have h1 : CF * (scale τ) ^ (1:ℝ) ≤ CF * (scale τ) ^ Nm :=
        mul_le_mul_of_nonneg_left hs hCFpos.le
      exact mul_le_mul_of_nonneg_right h1 hexpnn
    have hψτ : ‖psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ‖
        ≤ Cψ * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) := by
      have h := hψ τ ⟨hτD, hτ2⟩
      rw [norm_qParamFun] at h
      refine le_trans h ?_
      have hs : (scale τ) ^ Nψ ≤ (scale τ) ^ Nm :=
        Real.rpow_le_rpow_of_exponent_le hsc hNψ
      have h1 : Cψ * (scale τ) ^ Nψ ≤ Cψ * (scale τ) ^ Nm :=
        mul_le_mul_of_nonneg_left hs hCψpos.le
      exact mul_le_mul_of_nonneg_right h1 hexpnn
    have hΔ : ‖DeltaFun τ‖ ≤ 2 * Real.exp (-(2*Real.pi*τ.im)) :=
      DeltaFun_upper_sharp τ (by linarith)
    have hχ : ‖(cuspL ℓ - 4) / (Real.pi : ℂ)
        - Complex.I * ((τ:ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ))‖
        ≤ Cχ * scale τ := by
      have h1 : ‖(cuspL ℓ - 4) / (Real.pi : ℂ)‖ ≤ (Cc + 4) / Real.pi := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        refine div_le_div_of_nonneg_right ?_ Real.pi_pos.le
        refine le_trans (norm_sub_le (cuspL ℓ) 4) ?_
        rw [show ‖(4:ℂ)‖ = 4 from by norm_num]
        linarith [hCc]
      have h3 : ‖Complex.I * ((τ:ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ))‖
          ≤ (CE2 + 3 / Real.pi) * scale τ := by
        rw [norm_mul, Complex.norm_I, one_mul]
        have hE2b : ‖E2Fun τ‖ ≤ CE2 := hE2 τ (by linarith)
        have h4 : ‖(τ:ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)‖
            ≤ CE2 * scale τ + 3 / Real.pi := by
          refine le_trans (norm_sub_le ((τ:ℂ)*E2Fun τ) (3 * Complex.I / (Real.pi:ℂ))) ?_
          have h5 : ‖(τ:ℂ)*E2Fun τ‖ ≤ CE2 * scale τ := by
            rw [norm_mul]
            calc ‖(τ:ℂ)‖ * ‖E2Fun τ‖ ≤ scale τ * CE2 :=
                  mul_le_mul htn hE2b (norm_nonneg _) (by linarith)
              _ = CE2 * scale τ := by ring
          have h6 : ‖(3:ℂ) * Complex.I / (Real.pi:ℂ)‖ = 3 / Real.pi := by
            rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one,
              Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
          rw [h6]; linarith
        have h7 : CE2 * scale τ + 3 / Real.pi ≤ (CE2 + 3 / Real.pi) * scale τ := by
          have h8 : 3 / Real.pi ≤ (3 / Real.pi) * scale τ := by
            have h := mul_le_mul_of_nonneg_left hsc (by positivity : (0:ℝ) ≤ 3/Real.pi)
            calc 3 / Real.pi = 3 / Real.pi * 1 := by ring
              _ ≤ 3 / Real.pi * scale τ := h
          have h9 : CE2 * scale τ ≤ CE2 * scale τ := le_rfl
          nlinarith [h8, h9, hsc, hCE2pos, Real.pi_pos]
        linarith [h4, h7]
      have h11 : Cχ * scale τ = ((Cc + 4) / Real.pi) * scale τ + (CE2 + 3 / Real.pi) * scale τ := by
        rw [hCχ]; ring
      have h12 : (Cc + 4) / Real.pi ≤ ((Cc + 4) / Real.pi) * scale τ := by
        have h := mul_le_mul_of_nonneg_left hsc (by positivity : (0:ℝ) ≤ (Cc + 4) / Real.pi)
        calc (Cc + 4) / Real.pi = (Cc + 4) / Real.pi * 1 := by ring
          _ ≤ (Cc + 4) / Real.pi * scale τ := h
      rw [h11]
      refine le_trans (norm_sub_le _ _) ?_
      linarith [h1, h3, h12]
    -- per-term bounds in the `Nm` shape
    have ha : ‖Fleading τ / (576 * (Real.pi:ℂ) : ℂ)‖
        ≤ CF / (576 * Real.pi) * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) := by
      rw [norm_div, show ‖(576:ℂ) * (Real.pi:ℂ)‖ = 576 * Real.pi from by
        rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]]
      have hden : (0:ℝ) < 576 * Real.pi := by positivity
      calc ‖Fleading τ‖ / (576 * Real.pi)
          ≤ (CF * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im))) / (576 * Real.pi) :=
            div_le_div_of_nonneg_right hF hden.le
        _ = CF / (576 * Real.pi) * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) := by ring
    have hb : ‖DeltaFun τ * ((cuspL ℓ - 4) / (Real.pi : ℂ)
          - Complex.I * ((τ:ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)))‖
        ≤ 2 * Cχ * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) := by
      rw [norm_mul]
      calc ‖DeltaFun τ‖ * ‖(cuspL ℓ - 4) / (Real.pi : ℂ)
            - Complex.I * ((τ:ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ))‖
          ≤ (2 * Real.exp (-(2*Real.pi*τ.im))) * (Cχ * scale τ) :=
            mul_le_mul hΔ hχ (norm_nonneg _) (by positivity)
        _ ≤ 2 * Cχ * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) := by
            have hCχnn : (0:ℝ) ≤ Cχ := by rw [hCχ]; positivity
            have hs : scale τ ≤ (scale τ) ^ Nm := by
              have h := Real.rpow_le_rpow_of_exponent_le hsc hN1
              rwa [Real.rpow_one] at h
            have hs' : 2 * Real.exp (-(2*Real.pi*τ.im)) * Cχ * scale τ
                ≤ 2 * Real.exp (-(2*Real.pi*τ.im)) * Cχ * (scale τ) ^ Nm :=
              mul_le_mul_of_nonneg_left hs (by positivity)
            have heq : 2 * Real.exp (-(2*Real.pi*τ.im)) * Cχ * (scale τ) ^ Nm
                = 2 * Cχ * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) := by ring
            have heq2 : 2 * Real.exp (-(2*Real.pi*τ.im)) * (Cχ * scale τ)
                = 2 * Real.exp (-(2*Real.pi*τ.im)) * Cχ * scale τ := by ring
            linarith [hs', heq.le, heq.ge, heq2.le, heq2.ge]
    have hc : ‖(psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) / (1152 * (Real.pi:ℂ) : ℂ)‖
        ≤ Cψ / (1152 * Real.pi) * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) := by
      rw [norm_div, show ‖(1152:ℂ) * (Real.pi:ℂ)‖ = 1152 * Real.pi from by
        rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]]
      have hnum : ‖psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ‖
          = ‖psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ‖ := by
        rw [show psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ
          = -(psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ) from by ring, norm_neg]
      rw [hnum]
      have hden : (0:ℝ) < 1152 * Real.pi := by positivity
      calc ‖psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ‖ / (1152 * Real.pi)
          ≤ (Cψ * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im))) / (1152 * Real.pi) :=
            div_le_div_of_nonneg_right hψτ hden.le
        _ = Cψ / (1152 * Real.pi) * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) := by ring
    -- per-case
    have hcase0 : ‖Gcusp ℓ 24 1 (0:Fin 2) τ‖
        ≤ max (CF / 3456) (K / 2) * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) := by
      have hid : Gcusp ℓ 24 1 0 τ = (Fleading τ / (576 * (Real.pi:ℂ))
          + DeltaFun τ * ((cuspL ℓ - 4) / (Real.pi : ℂ)
              - Complex.I * ((τ:ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)))
          + (psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) / (1152 * (Real.pi:ℂ))) / 2 := by
        rw [eq_div_iff (by norm_num : (2:ℂ) ≠ 0), mul_comm (Gcusp ℓ 24 1 0 τ) 2]
        have h := Gcusp24_one_zero_eq ℓ τ
        simp only [E10Fun, E8Fun] at h ⊢
        exact h
      set blk : ℂ := Fleading τ / (576 * (Real.pi:ℂ))
          + DeltaFun τ * ((cuspL ℓ - 4) / (Real.pi : ℂ)
              - Complex.I * ((τ:ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)))
          + (psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) / (1152 * (Real.pi:ℂ)) with hblk
      have hblkb : ‖blk‖ ≤ K * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) := by
        have htri : ‖blk‖ ≤ ‖Fleading τ / (576 * (Real.pi:ℂ) : ℂ)‖
            + ‖DeltaFun τ * ((cuspL ℓ - 4) / (Real.pi : ℂ)
              - Complex.I * ((τ:ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)))‖
            + ‖(psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) / (1152 * (Real.pi:ℂ) : ℂ)‖ := by
          rw [hblk]
          have a := norm_add_le (Fleading τ / (576 * (Real.pi:ℂ))
            + DeltaFun τ * ((cuspL ℓ - 4) / (Real.pi : ℂ)
              - Complex.I * ((τ:ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ))))
            ((psi2 ℓ τ * E10Fun τ - psi4 ℓ τ * E8Fun τ) / (1152 * (Real.pi:ℂ)))
          have b := norm_add_le (Fleading τ / (576 * (Real.pi:ℂ)))
            (DeltaFun τ * ((cuspL ℓ - 4) / (Real.pi : ℂ)
              - Complex.I * ((τ:ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ))))
          linarith
        rw [hK]
        have heq : CF / (576 * Real.pi) * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im))
            + 2 * Cχ * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im))
            + Cψ / (1152 * Real.pi) * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im))
            = (CF / (576 * Real.pi) + 2 * Cχ + Cψ / (1152 * Real.pi))
              * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) := by ring
        linarith [htri, ha, hb, hc, heq.le, heq.ge]
      rw [hid, norm_div, show ‖(2:ℂ)‖ = 2 from by norm_num]
      have hK2 : K / 2 ≤ max (CF / 3456) (K / 2) := le_max_right _ _
      calc ‖blk‖ / 2 ≤ (K * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im))) / 2 :=
            div_le_div_of_nonneg_right hblkb (by norm_num)
        _ = (K / 2) * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) := by ring
        _ ≤ max (CF / 3456) (K / 2) * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK2 hSnn) hexpnn
    have hcase1 : ‖Gcusp ℓ 24 1 (1:Fin 2) τ‖
        ≤ max (CF / 3456) (K / 2) * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) := by
      have hid : Gcusp ℓ 24 1 1 τ = (Complex.I / 3456) * Fleading τ := Gcusp24_one_one_eq ℓ τ
      rw [hid, norm_mul]
      have hI : ‖(Complex.I / 3456 : ℂ)‖ = 1 / 3456 := by
        rw [norm_div, Complex.norm_I]; norm_num
      rw [hI]
      have hmid : (1/3456 : ℝ) * ‖Fleading τ‖
          ≤ CF / 3456 * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) := by
        have h2 : (1/3456 : ℝ) * ‖Fleading τ‖
            ≤ (1/3456) * (CF * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im))) :=
          mul_le_mul_of_nonneg_left hF (by norm_num)
        have h3 : (1/3456 : ℝ) * (CF * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)))
            = CF / 3456 * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) := by ring
        linarith [h2, h3.le, h3.ge]
      have hmax : CF / 3456 ≤ max (CF / 3456) (K / 2) := le_max_left _ _
      calc (1/3456 : ℝ) * ‖Fleading τ‖
          ≤ CF / 3456 * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) := hmid
        _ ≤ max (CF / 3456) (K / 2) * (scale τ) ^ Nm * Real.exp (-(2*Real.pi*τ.im)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmax hSnn) hexpnn
    fin_cases j
    · simpa using hcase0
    · simpa using hcase1

/-! ## The `d = 24` case: the `i = 1` row of `Gcusp` is exponentially small -/

/-
The content of this section is `GcuspRowOneExpSmall`: on the funnel, the `i = 1` row of the
cusp coefficients `Gcusp ℓ 24` is not merely polynomially bounded but *exponentially small*,
`‖Gcusp ℓ 24 1 j τ‖ ≤ C (scale τ)^N e^{-2π Im τ}`.  This is the ingredient that makes the cusp
model `Aexp (Gcusp ℓ 24) τ t` polynomially bounded on the window `1 ≤ t ≤ Im τ - 1`: the
`e^{2πt}`-terms of `Aexp` carry the coefficient row `Gcusp 1 j`, and
`e^{2πt} e^{-2π Im τ} ≤ e^{-2π}`.

The two entries are the explicit combinations
* `Gcusp ℓ 24 1 1 τ = (i/3456)·Fleading τ`, where
  `Fleading = 7E₄³ + 5E₆² - 12E₂E₄E₆ - 2πiτ·𝔸` and `𝔸 = (E₂E₄-E₆)(E₂E₆-E₄²)`: expanding around
  the cusp (`E₂,E₄,E₆ → 1`) kills the constant terms (`7+5-12 = 0`, and `𝔸 = O(q²)`), leaving
  `Fleading = 3456q + O(q²) = O(q)`;
* `2·Gcusp ℓ 24 1 0 τ = Fleading/(576π) + Δ(τ)[(c_L-4)/π - i(τE₂-3i/π)]
  + (ψ₂E₁₀-ψ₄E₈)/(1152π)`, where the last term is exponentially small by
  `psi4E8_sub_psi2E10_funnel`.
-/

theorem funnelKernelWindow (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → 1 ≤ t → t ≤ τ.im - 1 → ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  rcases hd with h8 | h24
  · subst h8
    exact funnelKernelWindow_eight ℓ
  · subst h24
    obtain ⟨Ck, Nk, Mk, hCk, hNk, hMk, hkb⟩ := KaxisWindowPoly ℓ 24 (Or.inr rfl)
    obtain ⟨CA, NA, hCApos, hNA, hArow⟩ := GcuspRowOneExpSmall ℓ 24 (Or.inr rfl)
    obtain ⟨a0, n0, ha0, hn0, hb0⟩ :=
      (Work.Kernels.moderateGrowthOn_iff_scale _ _).mp (Work.Asymptotics.GcuspInP ℓ 24 0 0)
    obtain ⟨a1, n1, ha1, hn1, hb1⟩ :=
      (Work.Kernels.moderateGrowthOn_iff_scale _ _).mp (Work.Asymptotics.GcuspInP ℓ 24 0 1)
    set Na : ℝ := max (max n0 (n1 + 1)) (NA + 1) with hNa
    have hNa0 : (0:ℝ) ≤ Na := by
      rw [hNa]
      exact le_trans (le_trans hn0 (le_max_left _ _)) (le_max_left _ _)
    have hn0Na : n0 ≤ Na := by rw [hNa]; exact le_trans (le_max_left n0 (n1+1)) (le_max_left _ _)
    have hn1Na : n1 + 1 ≤ Na := by rw [hNa]; exact le_trans (le_max_right n0 (n1+1)) (le_max_left _ _)
    have hNANa : NA + 1 ≤ Na := by rw [hNa]; exact le_max_right _ _
    refine ⟨Ck + (a0 + a1 + 2 * CA), max (max Nk Na) 0, max Mk 0, by positivity,
      le_max_of_le_right (by norm_num), le_max_of_le_right (by norm_num), ?_⟩
    intro τ t hτD hτ2 ht1 htwin
    have hsc : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hsc0 : (0:ℝ) < Work.Kernels.scale τ := lt_of_lt_of_le zero_lt_one hsc
    have hT1 : (1:ℝ) ≤ 1 + t := by linarith
    have ht0 : (0:ℝ) ≤ t := le_trans zero_le_one ht1
    have hts : t ≤ Work.Kernels.scale τ :=
      le_trans (le_trans htwin (by linarith))
        (le_trans (Work.Kernels.im_le_coe_norm τ) (Work.Kernels.coe_norm_le_scale τ))
    have hSnn : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ (max (max Nk Na) 0) :=
      Real.rpow_nonneg hsc0.le _
    have hTm : (1:ℝ) ≤ (1 + t) ^ (max Mk 0) := Real.one_le_rpow hT1 (le_max_right _ _)
    have hK : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) τ t‖
        ≤ Ck * (Work.Kernels.scale τ) ^ (max (max Nk Na) 0) * (1 + t) ^ (max Mk 0) := by
      refine le_trans (hkb τ t hτD hτ2 ht1 htwin) ?_
      exact bound_mono hsc hT1 hCk.le (le_trans (le_max_left Nk Na) (le_max_left _ _))
        (le_max_left Mk 0)
    have hexp : Real.exp (2 * Real.pi * t) * Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 := by
      rw [← Real.exp_add, Real.exp_le_one_iff]
      nlinarith [Real.pi_pos, htwin]
    have hcx : ‖Complex.exp (2 * Real.pi * t)‖ = Real.exp (2 * Real.pi * t) := by
      rw [Complex.norm_exp]; simp
    have hArow' : ∀ j : Fin 2, ‖Work.Asymptotics.Gcusp ℓ 24 1 j τ‖
        ≤ CA * (Work.Kernels.scale τ) ^ NA * Real.exp (-(2 * Real.pi * τ.im)) :=
      fun j => hArow τ j hτD hτ2
    have hAexp : ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) τ t‖
        ≤ (a0 + a1 + 2 * CA) * (Work.Kernels.scale τ) ^ Na := by
      have h00 := hb0 τ hτD
      have h01 := hb1 τ hτD
      have h10 := hArow' 0
      have h11 := hArow' 1
      have htz : ‖((t:ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖
          = t * ‖Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖ := norm_ofReal_I_mul ht0 _
      have htz' : ‖((t:ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 1 1 τ‖
          = t * ‖Work.Asymptotics.Gcusp ℓ 24 1 1 τ‖ := norm_ofReal_I_mul ht0 _
      have hsplit : Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) τ t
          = Work.Asymptotics.Gcusp ℓ 24 0 0 τ
            + ((t:ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 0 1 τ
            + (Complex.exp (2 * Real.pi * t)) * (Work.Asymptotics.Gcusp ℓ 24 1 0 τ
                + ((t:ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 1 1 τ) := by
        simp only [Work.Asymptotics.Aexp]
      rw [hsplit]
      have hb1' : ‖Work.Asymptotics.Gcusp ℓ 24 0 0 τ
            + ((t:ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 0 1 τ
            + (Complex.exp (2 * Real.pi * t)) * (Work.Asymptotics.Gcusp ℓ 24 1 0 τ
                + ((t:ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 1 1 τ)‖
          ≤ a0 * (Work.Kernels.scale τ) ^ n0 + a1 * (Work.Kernels.scale τ) ^ (n1 + 1)
            + 2 * CA * (Work.Kernels.scale τ) ^ (NA + 1) := by
        have htri1 := norm_add_le (Work.Asymptotics.Gcusp ℓ 24 0 0 τ
            + ((t:ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 0 1 τ)
          ((Complex.exp (2 * Real.pi * t)) * (Work.Asymptotics.Gcusp ℓ 24 1 0 τ
              + ((t:ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 1 1 τ))
        have htri2 := norm_add_le (Work.Asymptotics.Gcusp ℓ 24 0 0 τ)
          (((t:ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 0 1 τ)
        have htri3 := norm_add_le (Work.Asymptotics.Gcusp ℓ 24 1 0 τ)
          (((t:ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 1 1 τ)
        rw [htz] at htri2
        rw [htz'] at htri3
        have hA1 : t * ‖Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖ ≤ a1 * (Work.Kernels.scale τ) ^ (n1+1) := by
          calc t * ‖Work.Asymptotics.Gcusp ℓ 24 0 1 τ‖
              ≤ Work.Kernels.scale τ * (a1 * (Work.Kernels.scale τ) ^ n1) :=
                mul_le_mul hts h01 (norm_nonneg _) hsc0.le
            _ = a1 * (Work.Kernels.scale τ) ^ (n1+1) := by
                rw [Real.rpow_add_one (ne_of_gt hsc0)]; ring
        have hA2 : ‖(Complex.exp (2 * Real.pi * t)) * (Work.Asymptotics.Gcusp ℓ 24 1 0 τ
              + ((t:ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 1 1 τ)‖
            ≤ 2 * CA * (Work.Kernels.scale τ) ^ (NA + 1) := by
          rw [norm_mul, hcx]
          have hinner : ‖Work.Asymptotics.Gcusp ℓ 24 1 0 τ
              + ((t:ℂ) * Complex.I) * Work.Asymptotics.Gcusp ℓ 24 1 1 τ‖
              ≤ CA * (Work.Kernels.scale τ) ^ NA * Real.exp (-(2*Real.pi*τ.im))
                + t * (CA * (Work.Kernels.scale τ) ^ NA * Real.exp (-(2*Real.pi*τ.im))) := by
            have h1 : t * ‖Work.Asymptotics.Gcusp ℓ 24 1 1 τ‖
                ≤ t * (CA * (Work.Kernels.scale τ) ^ NA * Real.exp (-(2*Real.pi*τ.im))) :=
              mul_le_mul_of_nonneg_left h11 ht0
            linarith [htri3, h10, h1]
          have hstep : Real.exp (2*Real.pi*t) * (CA * (Work.Kernels.scale τ) ^ NA
                * Real.exp (-(2*Real.pi*τ.im))
                + t * (CA * (Work.Kernels.scale τ) ^ NA * Real.exp (-(2*Real.pi*τ.im))))
              ≤ 2 * CA * (Work.Kernels.scale τ) ^ (NA + 1) := by
            have hE : Real.exp (2*Real.pi*t) * Real.exp (-(2*Real.pi*τ.im)) ≤ 1 := hexp
            have hCAn : (0:ℝ) ≤ CA * (Work.Kernels.scale τ) ^ NA := by positivity
            have hE1 : Real.exp (2*Real.pi*t) * (CA * (Work.Kernels.scale τ) ^ NA
                * Real.exp (-(2*Real.pi*τ.im))) ≤ CA * (Work.Kernels.scale τ) ^ NA := by
              have he : Real.exp (2*Real.pi*t) * (CA * (Work.Kernels.scale τ) ^ NA
                  * Real.exp (-(2*Real.pi*τ.im)))
                  = (CA * (Work.Kernels.scale τ) ^ NA) * (Real.exp (2*Real.pi*t)
                    * Real.exp (-(2*Real.pi*τ.im))) := by ring
              rw [he]
              exact mul_le_of_le_one_right hCAn hE
            have hE2 : Real.exp (2*Real.pi*t) * (t * (CA * (Work.Kernels.scale τ) ^ NA
                * Real.exp (-(2*Real.pi*τ.im)))) ≤ t * (CA * (Work.Kernels.scale τ) ^ NA) := by
              have he : Real.exp (2*Real.pi*t) * (t * (CA * (Work.Kernels.scale τ) ^ NA
                  * Real.exp (-(2*Real.pi*τ.im))))
                  = (t * (CA * (Work.Kernels.scale τ) ^ NA)) * (Real.exp (2*Real.pi*t)
                    * Real.exp (-(2*Real.pi*τ.im))) := by ring
              rw [he]
              exact mul_le_of_le_one_right (by positivity) hE
            have hsum : (CA * (Work.Kernels.scale τ) ^ NA) + t * (CA * (Work.Kernels.scale τ) ^ NA)
                ≤ 2 * CA * (Work.Kernels.scale τ) ^ (NA + 1) := by
              have htS : t * (CA * (Work.Kernels.scale τ) ^ NA)
                  ≤ Work.Kernels.scale τ * (CA * (Work.Kernels.scale τ) ^ NA) :=
                mul_le_mul_of_nonneg_right hts hCAn
              have heq : Work.Kernels.scale τ * (CA * (Work.Kernels.scale τ) ^ NA)
                  = CA * (Work.Kernels.scale τ) ^ (NA + 1) := by
                rw [Real.rpow_add_one (ne_of_gt hsc0)]; ring
              have hceil : CA * (Work.Kernels.scale τ) ^ NA ≤ CA * (Work.Kernels.scale τ) ^ (NA+1) := by
                refine mul_le_mul_of_nonneg_left ?_ hCApos.le
                calc (Work.Kernels.scale τ) ^ NA = (Work.Kernels.scale τ) ^ NA * 1 := by ring
                  _ ≤ (Work.Kernels.scale τ) ^ NA * Work.Kernels.scale τ :=
                      mul_le_mul_of_nonneg_left hsc (Real.rpow_nonneg hsc0.le _)
                  _ = (Work.Kernels.scale τ) ^ (NA + 1) := by
                      rw [Real.rpow_add_one (ne_of_gt hsc0)]
              linarith [htS, heq.le, heq.ge, hceil]
            have hsplit' : Real.exp (2*Real.pi*t) * (CA * (Work.Kernels.scale τ) ^ NA
                  * Real.exp (-(2*Real.pi*τ.im))
                  + t * (CA * (Work.Kernels.scale τ) ^ NA * Real.exp (-(2*Real.pi*τ.im))))
                = Real.exp (2*Real.pi*t) * (CA * (Work.Kernels.scale τ) ^ NA
                    * Real.exp (-(2*Real.pi*τ.im)))
                  + Real.exp (2*Real.pi*t) * (t * (CA * (Work.Kernels.scale τ) ^ NA
                    * Real.exp (-(2*Real.pi*τ.im)))) := by ring
            rw [hsplit']; linarith [hE1, hE2, hsum]
          have hmul := mul_le_mul_of_nonneg_left hinner (Real.exp_nonneg (2*Real.pi*t))
          linarith [hmul, hstep]
        linarith [htri1, htri2, hA1, hA2, h00]
      have hNa_mono : a0 * (Work.Kernels.scale τ) ^ n0 + a1 * (Work.Kernels.scale τ) ^ (n1 + 1)
            + 2 * CA * (Work.Kernels.scale τ) ^ (NA + 1)
          ≤ (a0 + a1 + 2 * CA) * (Work.Kernels.scale τ) ^ Na := by
        have h1 : (Work.Kernels.scale τ) ^ n0 ≤ (Work.Kernels.scale τ) ^ Na :=
          Real.rpow_le_rpow_of_exponent_le hsc hn0Na
        have h2 : (Work.Kernels.scale τ) ^ (n1 + 1) ≤ (Work.Kernels.scale τ) ^ Na :=
          Real.rpow_le_rpow_of_exponent_le hsc hn1Na
        have h3 : (Work.Kernels.scale τ) ^ (NA + 1) ≤ (Work.Kernels.scale τ) ^ Na :=
          Real.rpow_le_rpow_of_exponent_le hsc hNANa
        have h4 : a0 * (Work.Kernels.scale τ) ^ n0 ≤ a0 * (Work.Kernels.scale τ) ^ Na :=
          mul_le_mul_of_nonneg_left h1 ha0
        have h5 : a1 * (Work.Kernels.scale τ) ^ (n1+1) ≤ a1 * (Work.Kernels.scale τ) ^ Na :=
          mul_le_mul_of_nonneg_left h2 ha1
        have h6 : 2 * CA * (Work.Kernels.scale τ) ^ (NA+1) ≤ 2 * CA * (Work.Kernels.scale τ) ^ Na :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        have hS : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ Na := Real.rpow_nonneg hsc0.le _
        nlinarith [h4, h5, h6, hS, ha0, ha1, hCApos]
      exact le_trans hb1' hNa_mono
    have hA : ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) τ t‖
        ≤ (a0 + a1 + 2 * CA) * (Work.Kernels.scale τ) ^ (max (max Nk Na) 0)
            * (1 + t) ^ (max Mk 0) := by
      have hs : (Work.Kernels.scale τ) ^ Na
          ≤ (Work.Kernels.scale τ) ^ (max (max Nk Na) 0) :=
        Real.rpow_le_rpow_of_exponent_le hsc (le_trans (le_max_right Nk Na) (le_max_left _ _))
      have hSnn' : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ (max (max Nk Na) 0) := Real.rpow_nonneg hsc0.le _
      have hstep1 : (a0 + a1 + 2 * CA) * (Work.Kernels.scale τ) ^ Na
          ≤ (a0 + a1 + 2 * CA) * (Work.Kernels.scale τ) ^ (max (max Nk Na) 0) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      have hstep2 : (a0 + a1 + 2 * CA) * (Work.Kernels.scale τ) ^ (max (max Nk Na) 0)
          ≤ (a0 + a1 + 2 * CA) * (Work.Kernels.scale τ) ^ (max (max Nk Na) 0)
            * (1 + t) ^ (max Mk 0) := by
        have hh : ((a0 + a1 + 2 * CA) * (Work.Kernels.scale τ) ^ (max (max Nk Na) 0)) * 1
            ≤ ((a0 + a1 + 2 * CA) * (Work.Kernels.scale τ) ^ (max (max Nk Na) 0))
              * (1 + t) ^ (max Mk 0) :=
          mul_le_mul_of_nonneg_left hTm (by positivity)
        calc (a0 + a1 + 2 * CA) * (Work.Kernels.scale τ) ^ (max (max Nk Na) 0)
            = ((a0 + a1 + 2 * CA) * (Work.Kernels.scale τ) ^ (max (max Nk Na) 0)) * 1 := by ring
          _ ≤ ((a0 + a1 + 2 * CA) * (Work.Kernels.scale τ) ^ (max (max Nk Na) 0))
                * (1 + t) ^ (max Mk 0) := hh
          _ = (a0 + a1 + 2 * CA) * (Work.Kernels.scale τ) ^ (max (max Nk Na) 0)
                * (1 + t) ^ (max Mk 0) := by ring
      exact le_trans hAexp (le_trans hstep1 hstep2)
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) τ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) τ t‖
        ≤ ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) τ t‖
            + ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) τ t‖ := norm_sub_le _ _
      _ ≤ Ck * (Work.Kernels.scale τ) ^ (max (max Nk Na) 0) * (1 + t) ^ (max Mk 0)
            + (a0 + a1 + 2 * CA) * (Work.Kernels.scale τ) ^ (max (max Nk Na) 0)
              * (1 + t) ^ (max Mk 0) := add_le_add hK hA
      _ = (Ck + (a0 + a1 + 2 * CA)) * (Work.Kernels.scale τ) ^ (max (max Nk Na) 0)
            * (1 + t) ^ (max Mk 0) := by ring

end

end Work.Asymptotics.HalfFunnel
