/-
# A weighted bound calculus on the spike circle

`SB f` records a bound `‖f τ ζ‖ ≤ C (S τ)^N` on the spike circle `‖ζ - τ‖ = 29/20`, for `τ`
in the funnel with `Im τ ≥ 3`.  For the `d = 24` kernel several factors are *exponentially*
large (e.g. `Δ(ζ)⁻¹ ≍ e^{2π Im ζ}`) and only their products with exponentially small
`τ`-factors are polynomially bounded.  To keep track of this we refine `SB` to a two-parameter
family

  `SBs H k f`  :  `‖f τ ζ‖ ≤ C (S τ)^N · tpar τ ^ k`   (`Im τ ≥ H`),

where `tpar τ = e^{-π Im τ}`.  The exponent `k` is additive under multiplication; a bound
`SBs H k f` with `k ≥ 0` and `H ≥ 3` gives back `SB f`, because `tpar τ ≤ 1`.
-/
import Mathlib
import Submission.Work.Asymptotics.SpikeCircle.SphereBoundAux
import Submission.Work.Asymptotics.SpikeCircle.divisorLowerDisc

noncomputable section
open UpperHalfPlane
open scoped Topology

namespace Work.Asymptotics.SpikeCircle

set_option maxHeartbeats 1000000

open Work.Kernels

/-- `SBs H k f` : on the spike circle with `Im τ ≥ H`, `‖f τ ζ‖ ≤ C (S τ)^N · tpar τ ^ k`. -/
def SBs (H k : ℝ) (f : ℍ → ℍ → ℂ) : Prop :=
  ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ ζ : ℍ, Funnel τ → ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 →
    H ≤ τ.im → ‖f τ ζ‖ ≤ C * (scale τ) ^ N * (Work.Residues.tpar τ) ^ k

lemma SBs.monoH {H H' k : ℝ} {f : ℍ → ℍ → ℂ} (h : SBs H k f) (hHH : H ≤ H') :
    SBs H' k f := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  exact ⟨C, N, hC, hN, fun τ ζ hτ hζ hH => hb τ ζ hτ hζ (le_trans hHH hH)⟩

lemma SBs.mono {H k k' : ℝ} {f : ℍ → ℍ → ℂ} (h : SBs H k f) (hkk : k' ≤ k) :
    SBs H k' f := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C, N, hC, hN, fun τ ζ hτ hζ hH => ?_⟩
  refine le_trans (hb τ ζ hτ hζ hH) ?_
  have ht0 : 0 < Work.Residues.tpar τ := Work.Residues.tpar_pos τ
  have ht1 : Work.Residues.tpar τ ≤ 1 := Work.Residues.tpar_le_one τ
  have hk : (Work.Residues.tpar τ) ^ k ≤ (Work.Residues.tpar τ) ^ k' :=
    Real.rpow_le_rpow_of_exponent_ge ht0 ht1 hkk
  exact mul_le_mul_of_nonneg_left hk (mul_nonneg hC.le (Real.rpow_nonneg (scale_pos τ).le N))

lemma SBs.congr {H k : ℝ} {f g : ℍ → ℍ → ℂ} (hf : SBs H k f)
    (h : ∀ τ ζ, f τ ζ = g τ ζ) : SBs H k g := by
  obtain ⟨C, N, hC, hN, hb⟩ := hf
  exact ⟨C, N, hC, hN, fun τ ζ hτ hζ hH => by rw [← h τ ζ]; exact hb τ ζ hτ hζ hH⟩

lemma SBs.add {H k : ℝ} {f g : ℍ → ℍ → ℂ} (hf : SBs H k f) (hg : SBs H k g) :
    SBs H k (fun τ ζ => f τ ζ + g τ ζ) := by
  obtain ⟨C1, N1, hC1, hN1, h1⟩ := hf
  obtain ⟨C2, N2, hC2, hN2, h2⟩ := hg
  refine ⟨C1 + C2, max N1 N2, by positivity, le_max_of_le_left hN1, fun τ ζ hτ hζ hH => ?_⟩
  have hs : (1 : ℝ) ≤ scale τ := one_le_scale τ
  have ht0 : (0 : ℝ) ≤ Work.Residues.tpar τ := Work.Residues.tpar_nonneg τ
  have htN : (0 : ℝ) ≤ (Work.Residues.tpar τ) ^ k := Real.rpow_nonneg ht0 k
  have hN1' : (scale τ) ^ N1 ≤ (scale τ) ^ max N1 N2 :=
    Real.rpow_le_rpow_of_exponent_le hs (le_max_left N1 N2)
  have hN2' : (scale τ) ^ N2 ≤ (scale τ) ^ max N1 N2 :=
    Real.rpow_le_rpow_of_exponent_le hs (le_max_right N1 N2)
  have e1 : C1 * (scale τ) ^ N1 * (Work.Residues.tpar τ) ^ k
      ≤ C1 * (scale τ) ^ max N1 N2 * (Work.Residues.tpar τ) ^ k :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN1' hC1.le) htN
  have e2 : C2 * (scale τ) ^ N2 * (Work.Residues.tpar τ) ^ k
      ≤ C2 * (scale τ) ^ max N1 N2 * (Work.Residues.tpar τ) ^ k :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN2' hC2.le) htN
  calc ‖f τ ζ + g τ ζ‖ ≤ ‖f τ ζ‖ + ‖g τ ζ‖ := norm_add_le _ _
    _ ≤ C1 * (scale τ) ^ N1 * (Work.Residues.tpar τ) ^ k
        + C2 * (scale τ) ^ N2 * (Work.Residues.tpar τ) ^ k :=
        add_le_add (h1 τ ζ hτ hζ hH) (h2 τ ζ hτ hζ hH)
    _ ≤ C1 * (scale τ) ^ max N1 N2 * (Work.Residues.tpar τ) ^ k
        + C2 * (scale τ) ^ max N1 N2 * (Work.Residues.tpar τ) ^ k := add_le_add e1 e2
    _ = (C1 + C2) * (scale τ) ^ max N1 N2 * (Work.Residues.tpar τ) ^ k := by ring

lemma SBs.neg {H k : ℝ} {f : ℍ → ℍ → ℂ} (hf : SBs H k f) :
    SBs H k (fun τ ζ => - f τ ζ) := by
  obtain ⟨C, N, hC, hN, hb⟩ := hf
  refine ⟨C, N, hC, hN, fun τ ζ hτ hζ hH => ?_⟩
  rw [norm_neg]; exact hb τ ζ hτ hζ hH

lemma SBs.sub {H k : ℝ} {f g : ℍ → ℍ → ℂ} (hf : SBs H k f) (hg : SBs H k g) :
    SBs H k (fun τ ζ => f τ ζ - g τ ζ) :=
  SBs.congr (SBs.add hf hg.neg) (fun τ ζ => by ring)

lemma SBs.const_mul (c : ℂ) {H k : ℝ} {f : ℍ → ℍ → ℂ} (hf : SBs H k f) :
    SBs H k (fun τ ζ => c * f τ ζ) := by
  obtain ⟨C, N, hC, hN, hb⟩ := hf
  refine ⟨‖c‖ * C + 1, N, by positivity, hN, fun τ ζ hτ hζ hH => ?_⟩
  have ht0 : (0 : ℝ) ≤ Work.Residues.tpar τ := Work.Residues.tpar_nonneg τ
  have h0 : (0 : ℝ) ≤ (Work.Residues.tpar τ) ^ k := Real.rpow_nonneg ht0 k
  have h0' : (0 : ℝ) ≤ (scale τ) ^ N := Real.rpow_nonneg (scale_pos τ).le N
  have hkey : (‖c‖ * C) * ((scale τ) ^ N * (Work.Residues.tpar τ) ^ k)
      ≤ (‖c‖ * C + 1) * ((scale τ) ^ N * (Work.Residues.tpar τ) ^ k) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg h0' h0)
  rw [norm_mul]
  calc ‖c‖ * ‖f τ ζ‖
      ≤ ‖c‖ * (C * (scale τ) ^ N * (Work.Residues.tpar τ) ^ k) :=
        mul_le_mul_of_nonneg_left (hb τ ζ hτ hζ hH) (norm_nonneg c)
    _ = (‖c‖ * C) * ((scale τ) ^ N * (Work.Residues.tpar τ) ^ k) := by ring
    _ ≤ (‖c‖ * C + 1) * ((scale τ) ^ N * (Work.Residues.tpar τ) ^ k) := hkey
    _ = (‖c‖ * C + 1) * (scale τ) ^ N * (Work.Residues.tpar τ) ^ k := by ring

lemma mul_four_eq (s t C1 C2 N1 N2 k l : ℝ) :
    (C1 * s ^ N1 * t ^ k) * (C2 * s ^ N2 * t ^ l)
      = C1 * C2 * (s ^ N1 * s ^ N2) * (t ^ k * t ^ l) := by ring

lemma SBs.mul {H k l : ℝ} {f g : ℍ → ℍ → ℂ} (hf : SBs H k f) (hg : SBs H l g) :
    SBs H (k + l) (fun τ ζ => f τ ζ * g τ ζ) := by
  obtain ⟨C1, N1, hC1, hN1, h1⟩ := hf
  obtain ⟨C2, N2, hC2, hN2, h2⟩ := hg
  refine ⟨C1 * C2 + 1, N1 + N2, by positivity, by positivity, fun τ ζ hτ hζ hH => ?_⟩
  have hspos : (0 : ℝ) < scale τ := scale_pos τ
  have ht0 : (0 : ℝ) ≤ Work.Residues.tpar τ := Work.Residues.tpar_nonneg τ
  have htpos : (0 : ℝ) < Work.Residues.tpar τ := Work.Residues.tpar_pos τ
  have hpos1 : (0 : ℝ) ≤ C1 * (scale τ) ^ N1 * (Work.Residues.tpar τ) ^ k :=
    mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg hspos.le N1)) (Real.rpow_nonneg ht0 k)
  have hEq : C1 * C2 * ((scale τ) ^ N1 * (scale τ) ^ N2)
        * ((Work.Residues.tpar τ) ^ k * (Work.Residues.tpar τ) ^ l)
      = C1 * C2 * (scale τ) ^ (N1 + N2) * (Work.Residues.tpar τ) ^ (k + l) := by
    rw [← Real.rpow_add hspos N1 N2, ← Real.rpow_add htpos k l]
  rw [norm_mul]
  calc ‖f τ ζ‖ * ‖g τ ζ‖
      ≤ (C1 * (scale τ) ^ N1 * (Work.Residues.tpar τ) ^ k)
          * (C2 * (scale τ) ^ N2 * (Work.Residues.tpar τ) ^ l) :=
        mul_le_mul (h1 τ ζ hτ hζ hH) (h2 τ ζ hτ hζ hH) (norm_nonneg _) hpos1
    _ = C1 * C2 * ((scale τ) ^ N1 * (scale τ) ^ N2)
          * ((Work.Residues.tpar τ) ^ k * (Work.Residues.tpar τ) ^ l) :=
        mul_four_eq (scale τ) (Work.Residues.tpar τ) C1 C2 N1 N2 k l
    _ = C1 * C2 * (scale τ) ^ (N1 + N2) * (Work.Residues.tpar τ) ^ (k + l) := hEq
    _ ≤ (C1 * C2 + 1) * (scale τ) ^ (N1 + N2) * (Work.Residues.tpar τ) ^ (k + l) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith)
            (Real.rpow_nonneg hspos.le _)) (Real.rpow_nonneg ht0 _)

lemma SBs.of_pointwise {H k : ℝ} {f g : ℍ → ℍ → ℂ} (hf : SBs H k f)
    (h : ∀ τ ζ : ℍ, Funnel τ → ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 → H ≤ τ.im → f τ ζ = g τ ζ) :
    SBs H k g := by
  obtain ⟨C, N, hC, hN, hb⟩ := hf
  exact ⟨C, N, hC, hN, fun τ ζ hτ hζ hH => by rw [← h τ ζ hτ hζ hH]; exact hb τ ζ hτ hζ hH⟩

/-- Normalise an `SBs` exponent that is a numeral expression down to `0`. -/
lemma SBs.mono0 {H k : ℝ} {f : ℍ → ℍ → ℂ} (h : SBs H k f) (hk : 0 ≤ k) : SBs H 0 f :=
  SBs.mono h hk

/-- An `SBs` bound with `k ≥ 0` yields a plain `C (S τ)^N` bound at the same threshold. -/
lemma SBs.to_bound {H k : ℝ} {f : ℍ → ℍ → ℂ} (h : SBs H k f) (hk : 0 ≤ k) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ ζ : ℍ, Funnel τ → ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20 →
      H ≤ τ.im → ‖f τ ζ‖ ≤ C * (scale τ) ^ N := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C, N, hC, hN, fun τ ζ hτ hζ hH => ?_⟩
  refine le_trans (hb τ ζ hτ hζ hH) ?_
  have ht0 : 0 < Work.Residues.tpar τ := Work.Residues.tpar_pos τ
  have ht1 : Work.Residues.tpar τ ≤ 1 := Work.Residues.tpar_le_one τ
  have hk1 : (Work.Residues.tpar τ) ^ k ≤ 1 := Real.rpow_le_one ht0.le ht1 hk
  have h1 : (0 : ℝ) ≤ C * (scale τ) ^ N := mul_nonneg hC.le (Real.rpow_nonneg (scale_pos τ).le N)
  calc C * (scale τ) ^ N * (Work.Residues.tpar τ) ^ k
      ≤ C * (scale τ) ^ N * 1 := mul_le_mul_of_nonneg_left hk1 h1
    _ = C * (scale τ) ^ N := by ring

/-- An `SB` bound is an `SBs H 0` bound for any `H ≥ 3`. -/
lemma SBs.of_SB {H : ℝ} {f : ℍ → ℍ → ℂ} (h : SB f) (hH : 3 ≤ H) : SBs H 0 f := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  refine ⟨C, N, hC, hN, fun τ ζ hτ hζ h3 => ?_⟩
  rw [Real.rpow_zero, mul_one]
  exact hb τ ζ hτ hζ (le_trans hH h3)

end Work.Asymptotics.SpikeCircle
