/-
# `Tref24 = O((scale τ)^N (1+t))` on the funnel contour

By `Compact.Tref24_eq` one has `Tref24 ℓ τ z = Ept z · R24 ℓ τ z` with
`R24 = Σ_{k=0}^{5} Ept z^k A_k`, `A_k = Xc ℓ z · R24_q_k + R24_p_k`; hence
`Tref24 = Σ_{k=0}^{5} Ept z^{k+1} A_k`, and it suffices to bound each coefficient `A_k` by
`C (scale τ)^N (1 + e^{2π Im τ}) (1+t)`: then
`‖Ept z^{k+1} A_k‖ ≤ ‖Ept z‖² ‖A_k‖ ≤ C (scale τ)^N (1+t)`, using
`e^{2π Im τ} ‖Ept z‖² ≤ e^{-2π}` and `‖Ept z‖ ≤ 1`.

The atom bounds themselves live in `Submission/Work/Asymptotics/KMinusFunnelAtoms.lean`.
-/
import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.KMinusFunnelAtoms
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Compact.kminus_tail_bounds

set_option maxHeartbeats 4000000

namespace Work.Asymptotics.Funnel24Tail

open UpperHalfPlane
open Work.Kernels
open Work.Residues (Ept)
open Work.Asymptotics.Funnel24

noncomputable section

/-! ## Elementary helpers -/

/-- `1 ≤ a * b * c` when `a, b, c ≥ 1`. -/
theorem one_le_prod_three {a b c : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    (1 : ℝ) ≤ a * b * c := by
  have h0a : (0 : ℝ) ≤ a := le_trans zero_le_one ha
  have h0b : (0 : ℝ) ≤ b := le_trans zero_le_one hb
  calc (1 : ℝ) = 1 * 1 * 1 := by ring
    _ ≤ a * b * c :=
        mul_le_mul (mul_le_mul ha hb (by norm_num) h0a) hc (by norm_num) (mul_nonneg h0a h0b)

/-- Sum bound for five terms. -/
theorem norm_five_sum_le {a b c d e : ℂ} {A B C D E : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ E) : ‖a + b + c + d + e‖ ≤ A + B + C + D + E := by
  have h1 : ‖a + b + c + d + e‖ ≤ ‖a + b + c + d‖ + ‖e‖ := norm_add_le _ _
  have h2 : ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
  have h3 : ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
  have h4 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
  linarith

/-- Sum bound for six terms. -/
theorem norm_six_sum_le {a b c d e f : ℂ} {A B C D E F : ℝ}
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ E)
    (hf : ‖f‖ ≤ F) : ‖a + b + c + d + e + f‖ ≤ A + B + C + D + E + F := by
  have h1 : ‖a + b + c + d + e + f‖ ≤ ‖a + b + c + d + e‖ + ‖f‖ := norm_add_le _ _
  have h2 : ‖a + b + c + d + e‖ ≤ ‖a + b + c + d‖ + ‖e‖ := norm_add_le _ _
  have h3 : ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
  have h4 : ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
  have h5 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
  linarith

/-- Sum bound for seven terms. -/
theorem norm_seven_sum_le {a b c d e f g : ℂ} {A B C D E F G : ℝ}
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ E)
    (hf : ‖f‖ ≤ F) (hg : ‖g‖ ≤ G) : ‖a + b + c + d + e + f + g‖ ≤ A + B + C + D + E + F + G := by
  have h1 : ‖a + b + c + d + e + f + g‖ ≤ ‖a + b + c + d + e + f‖ + ‖g‖ := norm_add_le _ _
  have h2 : ‖a + b + c + d + e + f‖ ≤ ‖a + b + c + d + e‖ + ‖f‖ := norm_add_le _ _
  have h3 : ‖a + b + c + d + e‖ ≤ ‖a + b + c + d‖ + ‖e‖ := norm_add_le _ _
  have h4 : ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
  have h5 : ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
  have h6 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
  linarith

/-- Sum bound for eight terms. -/
theorem norm_eight_sum_le {a b c d e f g h : ℂ} {A B C D E F G H : ℝ}
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) (he : ‖e‖ ≤ E)
    (hf : ‖f‖ ≤ F) (hg : ‖g‖ ≤ G) (hh : ‖h‖ ≤ H) :
    ‖a + b + c + d + e + f + g + h‖ ≤ A + B + C + D + E + F + G + H := by
  have h1 : ‖a + b + c + d + e + f + g + h‖ ≤ ‖a + b + c + d + e + f + g‖ + ‖h‖ := norm_add_le _ _
  have h2 : ‖a + b + c + d + e + f + g‖ ≤ ‖a + b + c + d + e + f‖ + ‖g‖ := norm_add_le _ _
  have h3 : ‖a + b + c + d + e + f‖ ≤ ‖a + b + c + d + e‖ + ‖f‖ := norm_add_le _ _
  have h4 : ‖a + b + c + d + e‖ ≤ ‖a + b + c + d‖ + ‖e‖ := norm_add_le _ _
  have h5 : ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
  have h6 : ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
  have h7 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
  linarith

/-! ## Lifting bounds to the uniform shape `C (scale τ)^N (1+e^{2π Im τ})(1+t)` -/

/-- `‖X‖ ≤ K (scale τ)^{Nk}` lifts to the uniform shape. -/
theorem lift0 {X : ℂ} {K Nk C N : ℝ} {τ : ℍ} {t : ℝ} (hK : K ≤ C) (hN : Nk ≤ N)
    (hK0 : 0 ≤ K) (hC0 : 0 ≤ C) (ht : 0 ≤ t) (hX : ‖X‖ ≤ K * (scale τ) ^ Nk) :
    ‖X‖ ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) := by
  have hsNk : (0 : ℝ) ≤ (scale τ) ^ Nk := scale_rpow_nonneg' τ Nk
  have hs : (scale τ) ^ Nk ≤ (scale τ) ^ N :=
    Real.rpow_le_rpow_of_exponent_le (one_le_scale τ) hN
  have h1 : K * (scale τ) ^ Nk ≤ C * (scale τ) ^ N := mul_le_mul hK hs hsNk hC0
  have hCN : (0 : ℝ) ≤ C * (scale τ) ^ N := mul_nonneg hC0 (scale_rpow_nonneg' τ N)
  have hE1 : (1 : ℝ) ≤ 1 + Real.exp (2 * Real.pi * τ.im) := by
    have := Real.exp_pos (2 * Real.pi * τ.im); linarith
  have ht1 : (1 : ℝ) ≤ 1 + t := by linarith
  have hb : (1 : ℝ) ≤ (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) := by
    simpa using mul_le_mul hE1 ht1 (by norm_num) (by linarith)
  calc ‖X‖ ≤ K * (scale τ) ^ Nk := hX
    _ ≤ C * (scale τ) ^ N := h1
    _ ≤ C * (scale τ) ^ N * ((1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) :=
        le_mul_of_one_le_right hCN hb
    _ = C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) := by ring

/-- `‖X‖ ≤ K (scale τ)^{Nk} e^{2π Im τ}` lifts to the uniform shape. -/
theorem liftE {X : ℂ} {K Nk C N : ℝ} {τ : ℍ} {t : ℝ} (hK : K ≤ C) (hN : Nk ≤ N)
    (hK0 : 0 ≤ K) (hC0 : 0 ≤ C) (ht : 0 ≤ t)
    (hX : ‖X‖ ≤ K * (scale τ) ^ Nk * Real.exp (2 * Real.pi * τ.im)) :
    ‖X‖ ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) := by
  have hsNk : (0 : ℝ) ≤ (scale τ) ^ Nk := scale_rpow_nonneg' τ Nk
  have hs : (scale τ) ^ Nk ≤ (scale τ) ^ N :=
    Real.rpow_le_rpow_of_exponent_le (one_le_scale τ) hN
  have hE1 : (1 : ℝ) ≤ 1 + Real.exp (2 * Real.pi * τ.im) := by
    have := Real.exp_pos (2 * Real.pi * τ.im); linarith
  have ht1 : (1 : ℝ) ≤ 1 + t := by linarith
  have hK0s : (0 : ℝ) ≤ K * (scale τ) ^ Nk := mul_nonneg hK0 hsNk
  have h1 : K * (scale τ) ^ Nk * Real.exp (2 * Real.pi * τ.im)
      ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) := by
    calc K * (scale τ) ^ Nk * Real.exp (2 * Real.pi * τ.im)
        ≤ K * (scale τ) ^ Nk * (1 + Real.exp (2 * Real.pi * τ.im)) :=
          mul_le_mul_of_nonneg_left (by linarith [Real.exp_pos (2 * Real.pi * τ.im)]) hK0s
      _ ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hK hs hsNk hC0) (by linarith)
  have hCN : (0 : ℝ) ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) :=
    mul_nonneg (mul_nonneg hC0 (scale_rpow_nonneg' τ N)) (by linarith)
  calc ‖X‖ ≤ K * (scale τ) ^ Nk * Real.exp (2 * Real.pi * τ.im) := hX
    _ ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) := h1
    _ ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) :=
        le_mul_of_one_le_right hCN ht1

/-- `‖X‖ ≤ K (1+t)` lifts to the uniform shape (`N ≥ 0`). -/
theorem liftT {X : ℂ} {K C N : ℝ} {τ : ℍ} {t : ℝ} (hK : K ≤ C) (hK0 : 0 ≤ K) (hC0 : 0 ≤ C)
    (hN : 0 ≤ N) (ht : 0 ≤ t) (hX : ‖X‖ ≤ K * (1 + t)) :
    ‖X‖ ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) := by
  have hsN1 : (1 : ℝ) ≤ (scale τ) ^ N := one_le_scale_rpow' τ hN
  have hsN0 : (0 : ℝ) ≤ (scale τ) ^ N := scale_rpow_nonneg' τ N
  have hE1 : (1 : ℝ) ≤ 1 + Real.exp (2 * Real.pi * τ.im) := by
    have := Real.exp_pos (2 * Real.pi * τ.im); linarith
  have ht1 : (1 : ℝ) ≤ 1 + t := by linarith
  have hkey : (1 : ℝ) ≤ (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) := by
    simpa using mul_le_mul hsN1 hE1 (by norm_num) hsN0
  have h1t : (0 : ℝ) ≤ 1 + t := by linarith
  have h2 : K * (1 + t) ≤ C * (1 + t) := mul_le_mul_of_nonneg_right hK h1t
  have h3 : C * (1 + t)
      ≤ C * ((scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im))) * (1 + t) := by
    have hc : C ≤ C * ((scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im))) := by
      have h := mul_le_mul_of_nonneg_left hkey hC0
      rwa [mul_one] at h
    exact mul_le_mul_of_nonneg_right hc h1t
  calc ‖X‖ ≤ K * (1 + t) := hX
    _ ≤ C * (1 + t) := h2
    _ ≤ C * ((scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im))) * (1 + t) := h3
    _ = C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) := by ring

/-- `‖X‖ ≤ K` (a constant) lifts to the uniform shape. -/
theorem liftC {X : ℂ} {K C N : ℝ} {τ : ℍ} {t : ℝ} (hK : K ≤ C) (hC0 : 0 ≤ C) (hN : 0 ≤ N)
    (ht : 0 ≤ t) (hX : ‖X‖ ≤ K) :
    ‖X‖ ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) := by
  have hsN1 : (1 : ℝ) ≤ (scale τ) ^ N := one_le_scale_rpow' τ hN
  have hE1 : (1 : ℝ) ≤ 1 + Real.exp (2 * Real.pi * τ.im) := by
    have := Real.exp_pos (2 * Real.pi * τ.im); linarith
  have ht1 : (1 : ℝ) ≤ 1 + t := by linarith
  have hb : (1 : ℝ) ≤ (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) :=
    one_le_prod_three hsN1 hE1 ht1
  calc ‖X‖ ≤ K := hX
    _ ≤ C := hK
    _ ≤ C * ((scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) :=
        le_mul_of_one_le_right hC0 hb
    _ = C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) := by ring

/-- `‖X‖ ≤ K (scale τ)^{Nk}` and `K ≤ C`, `Nk ≤ N` give `‖X‖ ≤ C (scale τ)^N`. -/
theorem dominate0 {X : ℂ} {K Nk C N : ℝ} {τ : ℍ} (hK : K ≤ C) (hN : Nk ≤ N)
    (hC : 0 ≤ C) (hX : ‖X‖ ≤ K * (scale τ) ^ Nk) : ‖X‖ ≤ C * (scale τ) ^ N :=
  le_trans hX (mul_le_mul hK (Real.rpow_le_rpow_of_exponent_le (one_le_scale τ) hN)
    (scale_rpow_nonneg' τ Nk) hC)

/-! ## A uniform atom bound on the funnel contour -/

/-- All the atoms of the coefficients `A_k` are bounded by
`C (scale τ)^N (1 + e^{2π Im τ}) (1+t)` on the funnel contour. -/
theorem atom_uniform_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      (‖psi2 ℓ τ * E10Fun τ‖
          ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) ∧
      (‖psi4 ℓ τ * E8Fun τ‖
          ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) ∧
      (‖DeltaFun τ‖
          ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) ∧
      (‖jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
          ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) ∧
      (‖jInvariantFun τ * (psi2 ℓ τ * E10Fun τ)‖
          ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) ∧
      (‖jInvariantFun τ * (psi4 ℓ τ * E8Fun τ)‖
          ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) ∧
      (‖jInvariantFun τ ^ 2 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
          ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) ∧
      (‖jInvariantFun τ * DeltaFun τ‖
          ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) ∧
      (‖Compact.Xc ℓ z‖
          ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) ∧
      (‖Compact.Xc ℓ z * DeltaFun τ‖
          ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) ∧
      (‖Compact.Xc ℓ z * (jInvariantFun τ * DeltaFun τ)‖
          ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) := by
  obtain ⟨Cp2, Np2, hCp2, hNp2, hp2⟩ := psi2E10_funnel ℓ
  obtain ⟨Cp4, Np4, hCp4, hNp4, hp4⟩ := psi4E8_funnel ℓ
  obtain ⟨Cjs, Njs, hCjs, hNjs, hjs⟩ := j_psi_sub_funnel ℓ
  obtain ⟨Cj2, Nj2, hCj2, hNj2, hj2⟩ := j_psi2E10_funnel ℓ
  obtain ⟨Cj4, Nj4, hCj4, hNj4, hj4⟩ := j_psi4E8_funnel ℓ
  obtain ⟨Cj2s, Nj2s, hCj2s, hNj2s, hj2s⟩ := j2_psi_sub_funnel ℓ
  set Cx : ℝ := Real.pi + ‖Compact.cuspC ℓ‖ with hCx
  set C : ℝ := 4 * Cx + Cp2 + Cp4 + Cjs + Cj2 + Cj4 + Cj2s + 4 with hCC
  set N : ℝ := Np2 + Np4 + Njs + Nj2 + Nj4 + Nj2s + 1 with hNN
  have hCx0 : (0 : ℝ) ≤ Cx := by rw [hCx]; linarith [Real.pi_pos, norm_nonneg (Compact.cuspC ℓ)]
  have hC0 : 0 < C := by
    rw [hCC]; linarith [hCx0, hCp2, hCp4, hCjs, hCj2, hCj4, hCj2s]
  have hN0 : 0 ≤ N := by
    rw [hNN]; linarith [hNp2, hNp4, hNjs, hNj2, hNj4, hNj2s]
  have hCp2C : Cp2 ≤ C := by
    rw [hCC]; linarith [hCx0, hCp4.le, hCjs.le, hCj2.le, hCj4.le, hCj2s.le]
  have hCp4C : Cp4 ≤ C := by
    rw [hCC]; linarith [hCx0, hCp2.le, hCjs.le, hCj2.le, hCj4.le, hCj2s.le]
  have hCjsC : Cjs ≤ C := by
    rw [hCC]; linarith [hCx0, hCp2.le, hCp4.le, hCj2.le, hCj4.le, hCj2s.le]
  have hCj2C : Cj2 ≤ C := by
    rw [hCC]; linarith [hCx0, hCp2.le, hCp4.le, hCjs.le, hCj4.le, hCj2s.le]
  have hCj4C : Cj4 ≤ C := by
    rw [hCC]; linarith [hCx0, hCp2.le, hCp4.le, hCjs.le, hCj2.le, hCj2s.le]
  have hCj2sC : Cj2s ≤ C := by
    rw [hCC]; linarith [hCx0, hCp2.le, hCp4.le, hCjs.le, hCj2.le, hCj4.le]
  have hCxle : Cx ≤ C := by
    rw [hCC]; linarith [hCx0, hCp2.le, hCp4.le, hCjs.le, hCj2.le, hCj4.le, hCj2s.le]
  have h4Cx : 4 * Cx ≤ C := by
    rw [hCC]; linarith [hCx0, hCp2.le, hCp4.le, hCjs.le, hCj2.le, hCj4.le, hCj2s.le]
  have h2Cx : 2 * Cx ≤ C := by linarith [h4Cx, hCx0]
  have h27Cx : (27 / 8) * Cx ≤ C := by linarith [h4Cx, hCx0]
  have h4C : (4 : ℝ) ≤ C := by
    rw [hCC]; linarith [hCx0, hCp2.le, hCp4.le, hCjs.le, hCj2.le, hCj4.le, hCj2s.le]
  have h2C : (2 : ℝ) ≤ C := by linarith [h4C]
  have h27C : (27 / 8 : ℝ) ≤ C := by linarith [h4C]
  have hNp2N : Np2 ≤ N := by rw [hNN]; linarith [hNp4, hNjs, hNj2, hNj4, hNj2s]
  have hNp4N : Np4 ≤ N := by rw [hNN]; linarith [hNp2, hNjs, hNj2, hNj4, hNj2s]
  have hNjsN : Njs ≤ N := by rw [hNN]; linarith [hNp2, hNp4, hNj2, hNj4, hNj2s]
  have hNj2N : Nj2 ≤ N := by rw [hNN]; linarith [hNp2, hNp4, hNjs, hNj4, hNj2s]
  have hNj4N : Nj4 ≤ N := by rw [hNN]; linarith [hNp2, hNp4, hNjs, hNj2, hNj2s]
  have hNj2sN : Nj2s ≤ N := by rw [hNN]; linarith [hNp2, hNp4, hNjs, hNj2, hNj4]
  refine ⟨C, N, hC0, hN0, fun τ z t hτ ht hz => ?_⟩
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : (1 : ℝ) ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have ht0 : (0 : ℝ) ≤ t := by linarith [hτ.2]
  have hΔ : ‖DeltaFun τ‖ ≤ 2 := by
    have h := norm_Delta_funnel τ hτ
    have hv : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, τ.im_pos]
    linarith
  have hjD : ‖jInvariantFun τ * DeltaFun τ‖ ≤ 27 / 8 := norm_j_mul_Delta_funnel τ hτ
  have hXc : ‖Compact.Xc ℓ z‖ ≤ Cx * (1 + t) := by
    rw [hCx]
    have h := Compact.kaux_norm_Xc_le ℓ z
    have hzc : ‖(z : ℂ)‖ = t := ft_norm_coe hz ht0
    rw [hzc] at h
    exact h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lift0 hCp2C hNp2N hCp2.le hC0.le ht0 (hp2 τ hτ)
  · exact lift0 hCp4C hNp4N hCp4.le hC0.le ht0 (hp4 τ hτ)
  · exact liftC h2C hC0.le hN0 ht0 (le_trans hΔ (by norm_num))
  · exact lift0 hCjsC hNjsN hCjs.le hC0.le ht0 (hjs τ hτ)
  · exact liftE hCj2C hNj2N hCj2.le hC0.le ht0 (hj2 τ hτ)
  · exact liftE hCj4C hNj4N hCj4.le hC0.le ht0 (hj4 τ hτ)
  · exact liftE hCj2sC hNj2sN hCj2s.le hC0.le ht0 (hj2s τ hτ)
  · exact liftC h27C hC0.le hN0 ht0 hjD
  · exact liftT hCxle hCx0 hC0.le hN0 ht0 hXc
  · have h2 := mul_le_mul hXc hΔ (norm_nonneg _) (mul_nonneg hCx0 (by linarith))
    have hkey : ‖Compact.Xc ℓ z * DeltaFun τ‖ ≤ (2 * Cx) * (1 + t) := by
      calc ‖Compact.Xc ℓ z * DeltaFun τ‖ ≤ ‖Compact.Xc ℓ z‖ * ‖DeltaFun τ‖ := norm_mul_le _ _
        _ ≤ (Cx * (1 + t)) * 2 := h2
        _ = (2 * Cx) * (1 + t) := by ring
    exact liftT h2Cx (mul_nonneg (by norm_num) hCx0) hC0.le hN0 ht0 hkey
  · have h2 := mul_le_mul hXc hjD (norm_nonneg _) (mul_nonneg hCx0 (by linarith))
    have hkey : ‖Compact.Xc ℓ z * (jInvariantFun τ * DeltaFun τ)‖ ≤ ((27 / 8) * Cx) * (1 + t) := by
      calc ‖Compact.Xc ℓ z * (jInvariantFun τ * DeltaFun τ)‖
          ≤ ‖Compact.Xc ℓ z‖ * ‖jInvariantFun τ * DeltaFun τ‖ := norm_mul_le _ _
        _ ≤ (Cx * (1 + t)) * (27 / 8) := h2
        _ = ((27 / 8) * Cx) * (1 + t) := by ring
    exact liftT h27Cx (mul_nonneg (by norm_num) hCx0) hC0.le hN0 ht0 hkey

/-! ## The `Xc`-free coefficient `R24_p0` -/

theorem R24_p0_bound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, Funnel τ →
      ‖Compact.R24_p0 ℓ τ‖ ≤ C * (scale τ) ^ N := by
  obtain ⟨Cp2, Np2, hCp2, hNp2, hp2⟩ := psi2E10_funnel ℓ
  obtain ⟨Cp4, Np4, hCp4, hNp4, hp4⟩ := psi4E8_funnel ℓ
  obtain ⟨Cjs, Njs, hCjs, hNjs, hjs⟩ := j_psi_sub_funnel ℓ
  set C0 : ℝ := Cp2 + Cp4 + Cjs + 4 with hCC
  set C : ℝ := (29568 + 15744 + 20570112 + 24 + 27648) * C0 + 1 with hCC'
  set N : ℝ := Np2 + Np4 + Njs + 1 with hNN
  have hC00 : 0 < C0 := by rw [hCC]; linarith [hCp2, hCp4, hCjs]
  have hC0' : (0 : ℝ) ≤ C0 := hC00.le
  have hC0 : 0 < C := by rw [hCC']; linarith [hC00]
  have h4C : (4 : ℝ) ≤ C0 := by rw [hCC]; linarith [hCp2.le, hCp4.le, hCjs.le]
  have hN0 : 0 ≤ N := by rw [hNN]; linarith [hNp2, hNp4, hNjs]
  have hCp2C : Cp2 ≤ C0 := by rw [hCC]; linarith [hCp4.le, hCjs.le]
  have hCp4C : Cp4 ≤ C0 := by rw [hCC]; linarith [hCp2.le, hCjs.le]
  have hCjsC : Cjs ≤ C0 := by rw [hCC]; linarith [hCp2.le, hCp4.le]
  have hNp2N : Np2 ≤ N := by rw [hNN]; linarith [hNp4, hNjs]
  have hNp4N : Np4 ≤ N := by rw [hNN]; linarith [hNp2, hNjs]
  have hNjsN : Njs ≤ N := by rw [hNN]; linarith [hNp2, hNp4]
  refine ⟨C, N, hC0, hN0, fun τ hτ => ?_⟩
  have hs1 : (1 : ℝ) ≤ (scale τ) ^ N := one_le_scale_rpow' τ hN0
  have hs0 : (0 : ℝ) ≤ (scale τ) ^ N := scale_rpow_nonneg' τ N
  have h1 : ‖psi4 ℓ τ * E8Fun τ‖ ≤ C0 * (scale τ) ^ N :=
    dominate0 hCp4C hNp4N hC0' (hp4 τ hτ)
  have h2 : ‖psi2 ℓ τ * E10Fun τ‖ ≤ C0 * (scale τ) ^ N :=
    dominate0 hCp2C hNp2N hC0' (hp2 τ hτ)
  have h3 : ‖jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)‖
      ≤ C0 * (scale τ) ^ N := dominate0 hCjsC hNjsN hC0' (hjs τ hτ)
  have h4 : ‖DeltaFun τ‖ ≤ C0 * (scale τ) ^ N := by
    have h := norm_Delta_funnel τ hτ
    have hv : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, τ.im_pos]
    calc ‖DeltaFun τ‖ ≤ 2 := by linarith
      _ ≤ C0 := by linarith [h4C]
      _ ≤ C0 * (scale τ) ^ N := le_mul_of_one_le_right hC0' hs1
  have h5 : ‖jInvariantFun τ * DeltaFun τ‖ ≤ C0 * (scale τ) ^ N := by
    have h := norm_j_mul_Delta_funnel τ hτ
    calc ‖jInvariantFun τ * DeltaFun τ‖ ≤ 27 / 8 := h
      _ ≤ C0 := by linarith [h4C]
      _ ≤ C0 * (scale τ) ^ N := le_mul_of_one_le_right hC0' hs1
  rw [show Compact.R24_p0 ℓ τ
    = (-29568 : ℂ) * (psi4 ℓ τ * E8Fun τ) + (15744 : ℂ) * (psi2 ℓ τ * E10Fun τ)
      + (-20570112 : ℂ) * (DeltaFun τ)
      + (24 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))
      + (27648 : ℂ) * (jInvariantFun τ * DeltaFun τ) by
    simp only [Compact.R24_p0]; ring]
  have b1 : ‖(-29568 : ℂ) * (psi4 ℓ τ * E8Fun τ)‖ ≤ 29568 * (C0 * (scale τ) ^ N) := by
    rw [norm_mul, show ‖(-29568 : ℂ)‖ = 29568 by norm_num]
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  have b2 : ‖(15744 : ℂ) * (psi2 ℓ τ * E10Fun τ)‖ ≤ 15744 * (C0 * (scale τ) ^ N) := by
    rw [norm_mul, show ‖(15744 : ℂ)‖ = 15744 by norm_num]
    exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  have b3 : ‖(-20570112 : ℂ) * (DeltaFun τ)‖ ≤ 20570112 * (C0 * (scale τ) ^ N) := by
    rw [norm_mul, show ‖(-20570112 : ℂ)‖ = 20570112 by norm_num]
    exact mul_le_mul_of_nonneg_left h4 (by norm_num)
  have b4 : ‖(24 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))‖
      ≤ 24 * (C0 * (scale τ) ^ N) := by
    rw [norm_mul, show ‖(24 : ℂ)‖ = 24 by norm_num]
    exact mul_le_mul_of_nonneg_left h3 (by norm_num)
  have b5 : ‖(27648 : ℂ) * (jInvariantFun τ * DeltaFun τ)‖ ≤ 27648 * (C0 * (scale τ) ^ N) := by
    rw [norm_mul, show ‖(27648 : ℂ)‖ = 27648 by norm_num]
    exact mul_le_mul_of_nonneg_left h5 (by norm_num)
  refine le_trans (norm_five_sum_le b1 b2 b3 b4 b5) ?_
  rw [show 29568 * (C0 * (scale τ) ^ N) + 15744 * (C0 * (scale τ) ^ N)
        + 20570112 * (C0 * (scale τ) ^ N) + 24 * (C0 * (scale τ) ^ N)
        + 27648 * (C0 * (scale τ) ^ N)
      = (29568 + 15744 + 20570112 + 24 + 27648) * (C0 * (scale τ) ^ N) from by ring]
  have hKsub : (29568 + 15744 + 20570112 + 24 + 27648) * C0 ≤ C := by
    rw [hCC']; linarith
  calc (29568 + 15744 + 20570112 + 24 + 27648) * (C0 * (scale τ) ^ N)
      = ((29568 + 15744 + 20570112 + 24 + 27648) * C0) * (scale τ) ^ N := by ring
    _ ≤ C * (scale τ) ^ N := mul_le_mul_of_nonneg_right hKsub hs0

/-! ## The five coefficient bounds -/

/-- The five coefficient bounds `‖A_k‖ ≤ C (scale τ)^N (1+e^{2π Im τ})(1+t)` for `k ≥ 1`. -/
theorem coeff_bounds (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      (‖Compact.Xc ℓ z * Compact.R24_q1 ℓ τ + Compact.R24_p1 ℓ τ‖
        ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) ∧
      (‖Compact.Xc ℓ z * Compact.R24_q2 ℓ τ + Compact.R24_p2 ℓ τ‖
        ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) ∧
      (‖Compact.Xc ℓ z * Compact.R24_q3 ℓ τ + Compact.R24_p3 ℓ τ‖
        ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) ∧
      (‖Compact.Xc ℓ z * Compact.R24_q4 ℓ τ + Compact.R24_p4 ℓ τ‖
        ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) ∧
      (‖Compact.Xc ℓ z * Compact.R24_q5 ℓ τ + Compact.R24_p5 ℓ τ‖
        ≤ C * (scale τ) ^ N * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) := by
  obtain ⟨Ca, Na, hCa, hNa, hunif⟩ := atom_uniform_bound ℓ
  set C : ℝ := (2 * 10 ^ 10) * Ca + 1 with hCC
  refine ⟨C, Na, by rw [hCC]; linarith [hCa], hNa, fun τ z t hτ ht hz => ?_⟩
  obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11⟩ := hunif τ z t hτ ht hz
  have ht0 : (0 : ℝ) ≤ t := by linarith [hτ.2]
  have ht1 : (0 : ℝ) ≤ 1 + t := by linarith
  have hE0 : (0 : ℝ) ≤ Real.exp (2 * Real.pi * τ.im) := (Real.exp_pos _).le
  have h1E1 : (0 : ℝ) ≤ 1 + Real.exp (2 * Real.pi * τ.im) := by linarith
  have hsN0 : (0 : ℝ) ≤ (scale τ) ^ Na := scale_rpow_nonneg' τ Na
  set Y : ℝ := Ca * (scale τ) ^ Na * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) with hY
  have hY0 : (0 : ℝ) ≤ Y := by
    rw [hY]; exact mul_nonneg (mul_nonneg (mul_nonneg hCa.le hsN0) h1E1) ht1
  have fin : ∀ {X : ℝ}, X ≤ 2 * 10 ^ 10 →
      X * Y ≤ C * (scale τ) ^ Na * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) := by
    intro X hX
    have h1 : X * Ca ≤ (2 * 10 ^ 10) * Ca := mul_le_mul_of_nonneg_right hX hCa.le
    have h2 : X * Ca ≤ C := by rw [hCC]; linarith
    have h3 : (0 : ℝ) ≤ (scale τ) ^ Na * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) :=
      mul_nonneg (mul_nonneg hsN0 h1E1) ht1
    calc X * Y = (X * Ca) * ((scale τ) ^ Na * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) := by
          rw [hY]; ring
      _ ≤ C * ((scale τ) ^ Na * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) :=
          mul_le_mul_of_nonneg_right h2 h3
      _ = C * (scale τ) ^ Na * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [show Compact.Xc ℓ z * Compact.R24_q1 ℓ τ + Compact.R24_p1 ℓ τ
        = (1990656 : ℂ) * (Compact.Xc ℓ z * DeltaFun τ)
          + (-896832 : ℂ) * (psi4 ℓ τ * E8Fun τ)
          + (-305856 : ℂ) * (psi2 ℓ τ * E10Fun τ)
          + (31850496 : ℂ) * (DeltaFun τ)
          + (2040 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))
          + (-312 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))
          + (-41472 : ℂ) * (jInvariantFun τ * DeltaFun τ)
          + (-1 : ℂ) * (jInvariantFun τ ^ 2 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)) by
      simp only [Compact.R24_q1, Compact.R24_p1]; ring]
    have b1 : ‖(1990656 : ℂ) * (Compact.Xc ℓ z * DeltaFun τ)‖ ≤ 1990656 * Y := by
      rw [norm_mul, show ‖(1990656 : ℂ)‖ = 1990656 by norm_num]
      exact mul_le_mul_of_nonneg_left ha10 (by norm_num)
    have b2 : ‖(-896832 : ℂ) * (psi4 ℓ τ * E8Fun τ)‖ ≤ 896832 * Y := by
      rw [norm_mul, show ‖(-896832 : ℂ)‖ = 896832 by norm_num]
      exact mul_le_mul_of_nonneg_left ha2 (by norm_num)
    have b3 : ‖(-305856 : ℂ) * (psi2 ℓ τ * E10Fun τ)‖ ≤ 305856 * Y := by
      rw [norm_mul, show ‖(-305856 : ℂ)‖ = 305856 by norm_num]
      exact mul_le_mul_of_nonneg_left ha1 (by norm_num)
    have b4 : ‖(31850496 : ℂ) * (DeltaFun τ)‖ ≤ 31850496 * Y := by
      rw [norm_mul, show ‖(31850496 : ℂ)‖ = 31850496 by norm_num]
      exact mul_le_mul_of_nonneg_left ha3 (by norm_num)
    have b5 : ‖(2040 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))‖ ≤ 2040 * Y := by
      rw [norm_mul, show ‖(2040 : ℂ)‖ = 2040 by norm_num]
      exact mul_le_mul_of_nonneg_left ha6 (by norm_num)
    have b6 : ‖(-312 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))‖ ≤ 312 * Y := by
      rw [norm_mul, show ‖(-312 : ℂ)‖ = 312 by norm_num]
      exact mul_le_mul_of_nonneg_left ha5 (by norm_num)
    have b7 : ‖(-41472 : ℂ) * (jInvariantFun τ * DeltaFun τ)‖ ≤ 41472 * Y := by
      rw [norm_mul, show ‖(-41472 : ℂ)‖ = 41472 by norm_num]
      exact mul_le_mul_of_nonneg_left ha8 (by norm_num)
    have b8 : ‖(-1 : ℂ) * (jInvariantFun τ ^ 2
          * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))‖ ≤ 1 * Y := by
      rw [norm_mul, show ‖(-1 : ℂ)‖ = 1 by norm_num]
      exact mul_le_mul_of_nonneg_left ha7 (by norm_num)
    refine le_trans (norm_eight_sum_le b1 b2 b3 b4 b5 b6 b7 b8) ?_
    rw [show 1990656 * Y + 896832 * Y + 305856 * Y + 31850496 * Y + 2040 * Y + 312 * Y
          + 41472 * Y + 1 * Y
        = (1990656 + 896832 + 305856 + 31850496 + 2040 + 312 + 41472 + 1) * Y from by ring]
    exact fin (by norm_num)
  · rw [show Compact.Xc ℓ z * Compact.R24_q2 ℓ τ + Compact.R24_p2 ℓ τ
        = (12616704 : ℂ) * (psi4 ℓ τ * E8Fun τ)
          + (-2663424 : ℂ) * (psi2 ℓ τ * E10Fun τ)
          + (-15925248 : ℂ) * (DeltaFun τ)
          + (-23424 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))
          + (9600 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))
          + (8 : ℂ) * (jInvariantFun τ ^ 2 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)) by
      simp only [Compact.R24_q2, Compact.R24_p2]; ring]
    have b1 : ‖(12616704 : ℂ) * (psi4 ℓ τ * E8Fun τ)‖ ≤ 12616704 * Y := by
      rw [norm_mul, show ‖(12616704 : ℂ)‖ = 12616704 by norm_num]
      exact mul_le_mul_of_nonneg_left ha2 (by norm_num)
    have b2 : ‖(-2663424 : ℂ) * (psi2 ℓ τ * E10Fun τ)‖ ≤ 2663424 * Y := by
      rw [norm_mul, show ‖(-2663424 : ℂ)‖ = 2663424 by norm_num]
      exact mul_le_mul_of_nonneg_left ha1 (by norm_num)
    have b3 : ‖(-15925248 : ℂ) * (DeltaFun τ)‖ ≤ 15925248 * Y := by
      rw [norm_mul, show ‖(-15925248 : ℂ)‖ = 15925248 by norm_num]
      exact mul_le_mul_of_nonneg_left ha3 (by norm_num)
    have b4 : ‖(-23424 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))‖ ≤ 23424 * Y := by
      rw [norm_mul, show ‖(-23424 : ℂ)‖ = 23424 by norm_num]
      exact mul_le_mul_of_nonneg_left ha6 (by norm_num)
    have b5 : ‖(9600 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))‖ ≤ 9600 * Y := by
      rw [norm_mul, show ‖(9600 : ℂ)‖ = 9600 by norm_num]
      exact mul_le_mul_of_nonneg_left ha5 (by norm_num)
    have b6 : ‖(8 : ℂ) * (jInvariantFun τ ^ 2
          * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))‖ ≤ 8 * Y := by
      rw [norm_mul, show ‖(8 : ℂ)‖ = 8 by norm_num]
      exact mul_le_mul_of_nonneg_left ha7 (by norm_num)
    refine le_trans (norm_six_sum_le b1 b2 b3 b4 b5 b6) ?_
    rw [show 12616704 * Y + 2663424 * Y + 15925248 * Y + 23424 * Y + 9600 * Y + 8 * Y
        = (12616704 + 2663424 + 15925248 + 23424 + 9600 + 8) * Y from by ring]
    exact fin (by norm_num)
  · rw [show Compact.Xc ℓ z * Compact.R24_q3 ℓ τ + Compact.R24_p3 ℓ τ
        = (-1433272320 : ℂ) * (Compact.Xc ℓ z * DeltaFun τ)
          + (1990656 : ℂ) * (Compact.Xc ℓ z * (jInvariantFun τ * DeltaFun τ))
          + (-49268736 : ℂ) * (psi4 ℓ τ * E8Fun τ)
          + (19408896 : ℂ) * (psi2 ℓ τ * E10Fun τ)
          + (23887872 : ℂ) * (DeltaFun τ)
          + (86976 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))
          + (-45504 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))
          + (-24 : ℂ) * (jInvariantFun τ ^ 2 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)) by
      simp only [Compact.R24_q3, Compact.R24_p3]; ring]
    have b1 : ‖(-1433272320 : ℂ) * (Compact.Xc ℓ z * DeltaFun τ)‖ ≤ 1433272320 * Y := by
      rw [norm_mul, show ‖(-1433272320 : ℂ)‖ = 1433272320 by norm_num]
      exact mul_le_mul_of_nonneg_left ha10 (by norm_num)
    have b2 : ‖(1990656 : ℂ) * (Compact.Xc ℓ z * (jInvariantFun τ * DeltaFun τ))‖
        ≤ 1990656 * Y := by
      rw [norm_mul, show ‖(1990656 : ℂ)‖ = 1990656 by norm_num]
      exact mul_le_mul_of_nonneg_left ha11 (by norm_num)
    have b3 : ‖(-49268736 : ℂ) * (psi4 ℓ τ * E8Fun τ)‖ ≤ 49268736 * Y := by
      rw [norm_mul, show ‖(-49268736 : ℂ)‖ = 49268736 by norm_num]
      exact mul_le_mul_of_nonneg_left ha2 (by norm_num)
    have b4 : ‖(19408896 : ℂ) * (psi2 ℓ τ * E10Fun τ)‖ ≤ 19408896 * Y := by
      rw [norm_mul, show ‖(19408896 : ℂ)‖ = 19408896 by norm_num]
      exact mul_le_mul_of_nonneg_left ha1 (by norm_num)
    have b5 : ‖(23887872 : ℂ) * (DeltaFun τ)‖ ≤ 23887872 * Y := by
      rw [norm_mul, show ‖(23887872 : ℂ)‖ = 23887872 by norm_num]
      exact mul_le_mul_of_nonneg_left ha3 (by norm_num)
    have b6 : ‖(86976 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))‖ ≤ 86976 * Y := by
      rw [norm_mul, show ‖(86976 : ℂ)‖ = 86976 by norm_num]
      exact mul_le_mul_of_nonneg_left ha6 (by norm_num)
    have b7 : ‖(-45504 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))‖ ≤ 45504 * Y := by
      rw [norm_mul, show ‖(-45504 : ℂ)‖ = 45504 by norm_num]
      exact mul_le_mul_of_nonneg_left ha5 (by norm_num)
    have b8 : ‖(-24 : ℂ) * (jInvariantFun τ ^ 2
          * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ))‖ ≤ 24 * Y := by
      rw [norm_mul, show ‖(-24 : ℂ)‖ = 24 by norm_num]
      exact mul_le_mul_of_nonneg_left ha7 (by norm_num)
    refine le_trans (norm_eight_sum_le b1 b2 b3 b4 b5 b6 b7 b8) ?_
    rw [show 1433272320 * Y + 1990656 * Y + 49268736 * Y + 19408896 * Y + 23887872 * Y
          + 86976 * Y + 45504 * Y + 24 * Y
        = (1433272320 + 1990656 + 49268736 + 19408896 + 23887872 + 86976 + 45504 + 24) * Y from by ring]
    exact fin (by norm_num)
  · rw [show Compact.Xc ℓ z * Compact.R24_q4 ℓ τ + Compact.R24_p4 ℓ τ
        = (72990720 : ℂ) * (psi4 ℓ τ * E8Fun τ)
          + (-72990720 : ℂ) * (psi2 ℓ τ * E10Fun τ)
          + (11466178560 : ℂ) * (DeltaFun τ)
          + (-101376 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))
          + (101376 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))
          + (-15925248 : ℂ) * (jInvariantFun τ * DeltaFun τ) by
      simp only [Compact.R24_q4, Compact.R24_p4]; ring]
    have b1 : ‖(72990720 : ℂ) * (psi4 ℓ τ * E8Fun τ)‖ ≤ 72990720 * Y := by
      rw [norm_mul, show ‖(72990720 : ℂ)‖ = 72990720 by norm_num]
      exact mul_le_mul_of_nonneg_left ha2 (by norm_num)
    have b2 : ‖(-72990720 : ℂ) * (psi2 ℓ τ * E10Fun τ)‖ ≤ 72990720 * Y := by
      rw [norm_mul, show ‖(-72990720 : ℂ)‖ = 72990720 by norm_num]
      exact mul_le_mul_of_nonneg_left ha1 (by norm_num)
    have b3 : ‖(11466178560 : ℂ) * (DeltaFun τ)‖ ≤ 11466178560 * Y := by
      rw [norm_mul, show ‖(11466178560 : ℂ)‖ = 11466178560 by norm_num]
      exact mul_le_mul_of_nonneg_left ha3 (by norm_num)
    have b4 : ‖(-101376 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))‖ ≤ 101376 * Y := by
      rw [norm_mul, show ‖(-101376 : ℂ)‖ = 101376 by norm_num]
      exact mul_le_mul_of_nonneg_left ha6 (by norm_num)
    have b5 : ‖(101376 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))‖ ≤ 101376 * Y := by
      rw [norm_mul, show ‖(101376 : ℂ)‖ = 101376 by norm_num]
      exact mul_le_mul_of_nonneg_left ha5 (by norm_num)
    have b6 : ‖(-15925248 : ℂ) * (jInvariantFun τ * DeltaFun τ)‖ ≤ 15925248 * Y := by
      rw [norm_mul, show ‖(-15925248 : ℂ)‖ = 15925248 by norm_num]
      exact mul_le_mul_of_nonneg_left ha8 (by norm_num)
    refine le_trans (norm_six_sum_le b1 b2 b3 b4 b5 b6) ?_
    rw [show 72990720 * Y + 72990720 * Y + 11466178560 * Y + 101376 * Y + 101376 * Y
          + 15925248 * Y
        = (72990720 + 72990720 + 11466178560 + 101376 + 101376 + 15925248) * Y from by ring]
    exact fin (by norm_num)
  · rw [show Compact.Xc ℓ z * Compact.R24_q5 ℓ τ + Compact.R24_p5 ℓ τ
        = (-656916480 : ℂ) * (psi4 ℓ τ * E8Fun τ)
          + (656916480 : ℂ) * (psi2 ℓ τ * E10Fun τ)
          + (-17199267840 : ℂ) * (DeltaFun τ)
          + (912384 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))
          + (-912384 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))
          + (23887872 : ℂ) * (jInvariantFun τ * DeltaFun τ) by
      simp only [Compact.R24_q5, Compact.R24_p5]; ring]
    have b1 : ‖(-656916480 : ℂ) * (psi4 ℓ τ * E8Fun τ)‖ ≤ 656916480 * Y := by
      rw [norm_mul, show ‖(-656916480 : ℂ)‖ = 656916480 by norm_num]
      exact mul_le_mul_of_nonneg_left ha2 (by norm_num)
    have b2 : ‖(656916480 : ℂ) * (psi2 ℓ τ * E10Fun τ)‖ ≤ 656916480 * Y := by
      rw [norm_mul, show ‖(656916480 : ℂ)‖ = 656916480 by norm_num]
      exact mul_le_mul_of_nonneg_left ha1 (by norm_num)
    have b3 : ‖(-17199267840 : ℂ) * (DeltaFun τ)‖ ≤ 17199267840 * Y := by
      rw [norm_mul, show ‖(-17199267840 : ℂ)‖ = 17199267840 by norm_num]
      exact mul_le_mul_of_nonneg_left ha3 (by norm_num)
    have b4 : ‖(912384 : ℂ) * (jInvariantFun τ * (psi4 ℓ τ * E8Fun τ))‖ ≤ 912384 * Y := by
      rw [norm_mul, show ‖(912384 : ℂ)‖ = 912384 by norm_num]
      exact mul_le_mul_of_nonneg_left ha6 (by norm_num)
    have b5 : ‖(-912384 : ℂ) * (jInvariantFun τ * (psi2 ℓ τ * E10Fun τ))‖ ≤ 912384 * Y := by
      rw [norm_mul, show ‖(-912384 : ℂ)‖ = 912384 by norm_num]
      exact mul_le_mul_of_nonneg_left ha5 (by norm_num)
    have b6 : ‖(23887872 : ℂ) * (jInvariantFun τ * DeltaFun τ)‖ ≤ 23887872 * Y := by
      rw [norm_mul, show ‖(23887872 : ℂ)‖ = 23887872 by norm_num]
      exact mul_le_mul_of_nonneg_left ha8 (by norm_num)
    refine le_trans (norm_six_sum_le b1 b2 b3 b4 b5 b6) ?_
    rw [show 656916480 * Y + 656916480 * Y + 17199267840 * Y + 912384 * Y + 912384 * Y
          + 23887872 * Y
        = (656916480 + 656916480 + 17199267840 + 912384 + 912384 + 23887872) * Y from by ring]
    exact fin (by norm_num)

/-! ## Assembly -/

/-- **`Tref24 = O((scale τ)^N (1+t))` on the funnel contour.** -/
theorem Tref24FunnelBound (ℓ : LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.Tref24 ℓ τ z‖ ≤ C * (scale τ) ^ N * (1 + t) := by
  obtain ⟨C0, N0, hC0, hN0, hp0⟩ := R24_p0_bound ℓ
  obtain ⟨Cc, Nc, hCc, hNc, hcoef⟩ := coeff_bounds ℓ
  set K : ℝ := 5 * (Cc * (1 + Real.exp (-(2 * Real.pi)))) + C0 + 1 with hK
  set N : ℝ := N0 + Nc + 1 with hNN
  have hEexp0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi)) := (Real.exp_pos _).le
  have hK0 : 0 < K := by rw [hK]; nlinarith [hCc, hC0, Real.exp_pos (-(2 * Real.pi))]
  have hN0' : 0 ≤ N := by rw [hNN]; linarith [hN0, hNc]
  have hN0N : N0 ≤ N := by rw [hNN]; linarith [hNc]
  have hNcN : Nc ≤ N := by rw [hNN]; linarith [hN0]
  refine ⟨K, N, hK0, hN0', fun τ z t hτ ht hz => ?_⟩
  obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ := hcoef τ z t hτ ht hz
  have hzim : z.im = t := ft_im_of_coe hz
  have hz1 : (1 : ℝ) ≤ z.im := by rw [hzim]; linarith [hτ.2]
  have ht0 : (0 : ℝ) ≤ t := by linarith [hτ.2]
  have ht1 : (1 : ℝ) ≤ 1 + t := by linarith
  have ha0 : (0 : ℝ) ≤ ‖Ept z‖ := norm_nonneg _
  have ha1 : ‖Ept z‖ ≤ 1 := norm_Ept_le_one' hz1
  have ha2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ ha0 ha1
  have hsN0 : (0 : ℝ) ≤ (scale τ) ^ N := scale_rpow_nonneg' τ N
  have hsN0N : (scale τ) ^ N0 ≤ (scale τ) ^ N :=
    Real.rpow_le_rpow_of_exponent_le (one_le_scale τ) hN0N
  have hsNcN : (scale τ) ^ Nc ≤ (scale τ) ^ N :=
    Real.rpow_le_rpow_of_exponent_le (one_le_scale τ) hNcN
  have hexp : Compact.Tref24 ℓ τ z
      = Ept z * Compact.R24_p0 ℓ τ
        + (Ept z) ^ 2 * (Compact.Xc ℓ z * Compact.R24_q1 ℓ τ + Compact.R24_p1 ℓ τ)
        + (Ept z) ^ 3 * (Compact.Xc ℓ z * Compact.R24_q2 ℓ τ + Compact.R24_p2 ℓ τ)
        + (Ept z) ^ 4 * (Compact.Xc ℓ z * Compact.R24_q3 ℓ τ + Compact.R24_p3 ℓ τ)
        + (Ept z) ^ 5 * (Compact.Xc ℓ z * Compact.R24_q4 ℓ τ + Compact.R24_p4 ℓ τ)
        + (Ept z) ^ 6 * (Compact.Xc ℓ z * Compact.R24_q5 ℓ τ + Compact.R24_p5 ℓ τ) := by
    rw [Compact.Tref24_eq, Compact.R24]
    simp only [Compact.R24_q0, Compact.R24_q2, Compact.R24_q4, Compact.R24_q5]
    ring
  -- the `E`-cum-`‖Ept z‖²` estimate
  have hEpt : ‖Ept z‖ ^ 2 * (1 + Real.exp (2 * Real.pi * τ.im)) ≤ 1 + Real.exp (-(2 * Real.pi)) := by
    have hexp' : Real.exp (2 * Real.pi * τ.im) * ‖Ept z‖ ^ 2 ≤ Real.exp (-(2 * Real.pi)) :=
      exp_im_mul_Ept_sq_le τ z t hτ ht hzim
    linarith [hexp', ha2]
  have hT0 : ‖Ept z * Compact.R24_p0 ℓ τ‖ ≤ C0 * (scale τ) ^ N * (1 + t) := by
    have h := hp0 τ hτ
    calc ‖Ept z * Compact.R24_p0 ℓ τ‖ ≤ ‖Ept z‖ * ‖Compact.R24_p0 ℓ τ‖ := norm_mul_le _ _
      _ ≤ 1 * (C0 * (scale τ) ^ N0) := mul_le_mul ha1 h (norm_nonneg _) (by norm_num)
      _ = C0 * (scale τ) ^ N0 := by ring
      _ ≤ C0 * (scale τ) ^ N := mul_le_mul_of_nonneg_left hsN0N hC0.le
      _ ≤ C0 * (scale τ) ^ N * (1 + t) := le_mul_of_one_le_right (mul_nonneg hC0.le hsN0) ht1
  have hstep : ∀ (A : ℂ), ‖A‖ ≤ Cc * (scale τ) ^ Nc * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) →
      ∀ (k : ℕ), 2 ≤ k →
      ‖(Ept z) ^ k * A‖ ≤ Cc * (1 + Real.exp (-(2 * Real.pi))) * (scale τ) ^ N * (1 + t) := by
    intro A hA k hk
    have hp : ‖(Ept z) ^ k‖ ≤ ‖Ept z‖ ^ 2 := by
      rw [norm_pow]
      exact pow_le_pow_of_le_one ha0 ha1 hk
    have hCc0 : (0 : ℝ) ≤ Cc := hCc.le
    have hshape0 : (0 : ℝ) ≤ (scale τ) ^ Nc * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) :=
      mul_nonneg (mul_nonneg (scale_rpow_nonneg' τ Nc)
        (by linarith [Real.exp_pos (2 * Real.pi * τ.im)])) (by linarith)
    have h1 : ‖(Ept z) ^ k * A‖
        ≤ ‖Ept z‖ ^ 2 * (Cc * (scale τ) ^ Nc * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) := by
      rw [norm_mul]
      exact mul_le_mul hp hA (norm_nonneg _) (pow_nonneg ha0 2)
    have h2 : ‖Ept z‖ ^ 2 * (Cc * (scale τ) ^ Nc * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t))
        ≤ Cc * (1 + Real.exp (-(2 * Real.pi))) * (scale τ) ^ Nc * (1 + t) := by
      have hfac : Cc * (scale τ) ^ Nc * (1 + t) ≥ 0 := mul_nonneg (mul_nonneg hCc0 (scale_rpow_nonneg' τ Nc)) (by linarith)
      calc ‖Ept z‖ ^ 2 * (Cc * (scale τ) ^ Nc * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t))
          = (Cc * (scale τ) ^ Nc * (1 + t)) * (‖Ept z‖ ^ 2 * (1 + Real.exp (2 * Real.pi * τ.im))) := by ring
        _ ≤ (Cc * (scale τ) ^ Nc * (1 + t)) * (1 + Real.exp (-(2 * Real.pi))) :=
            mul_le_mul_of_nonneg_left hEpt hfac
        _ = Cc * (1 + Real.exp (-(2 * Real.pi))) * (scale τ) ^ Nc * (1 + t) := by ring
    have h3 : Cc * (1 + Real.exp (-(2 * Real.pi))) * (scale τ) ^ Nc * (1 + t)
        ≤ Cc * (1 + Real.exp (-(2 * Real.pi))) * (scale τ) ^ N * (1 + t) := by
      have hc0 : (0 : ℝ) ≤ Cc * (1 + Real.exp (-(2 * Real.pi))) :=
        mul_nonneg hCc0 (by linarith [Real.exp_pos (-(2 * Real.pi))])
      have h1' : Cc * (1 + Real.exp (-(2 * Real.pi))) * (scale τ) ^ Nc
          ≤ Cc * (1 + Real.exp (-(2 * Real.pi))) * (scale τ) ^ N :=
        mul_le_mul_of_nonneg_left hsNcN hc0
      exact mul_le_mul_of_nonneg_right h1' (by linarith)
    exact le_trans h1 (le_trans h2 h3)
  have hb0 := hT0
  have hb1 : ‖(Ept z) ^ 2 * (Compact.Xc ℓ z * Compact.R24_q1 ℓ τ + Compact.R24_p1 ℓ τ)‖
      ≤ Cc * (1 + Real.exp (-(2 * Real.pi))) * (scale τ) ^ N * (1 + t) := hstep _ hc1 2 (by norm_num)
  have hb2 : ‖(Ept z) ^ 3 * (Compact.Xc ℓ z * Compact.R24_q2 ℓ τ + Compact.R24_p2 ℓ τ)‖
      ≤ Cc * (1 + Real.exp (-(2 * Real.pi))) * (scale τ) ^ N * (1 + t) := hstep _ hc2 3 (by norm_num)
  have hb3 : ‖(Ept z) ^ 4 * (Compact.Xc ℓ z * Compact.R24_q3 ℓ τ + Compact.R24_p3 ℓ τ)‖
      ≤ Cc * (1 + Real.exp (-(2 * Real.pi))) * (scale τ) ^ N * (1 + t) := hstep _ hc3 4 (by norm_num)
  have hb4 : ‖(Ept z) ^ 5 * (Compact.Xc ℓ z * Compact.R24_q4 ℓ τ + Compact.R24_p4 ℓ τ)‖
      ≤ Cc * (1 + Real.exp (-(2 * Real.pi))) * (scale τ) ^ N * (1 + t) := hstep _ hc4 5 (by norm_num)
  have hb5 : ‖(Ept z) ^ 6 * (Compact.Xc ℓ z * Compact.R24_q5 ℓ τ + Compact.R24_p5 ℓ τ)‖
      ≤ Cc * (1 + Real.exp (-(2 * Real.pi))) * (scale τ) ^ N * (1 + t) := hstep _ hc5 6 (by norm_num)
  rw [hexp]
  refine le_trans (norm_six_sum_le hb0 hb1 hb2 hb3 hb4 hb5) ?_
  rw [show C0 * (scale τ) ^ N * (1 + t)
        + Cc * (1 + Real.exp (-(2 * Real.pi))) * (scale τ) ^ N * (1 + t)
        + Cc * (1 + Real.exp (-(2 * Real.pi))) * (scale τ) ^ N * (1 + t)
        + Cc * (1 + Real.exp (-(2 * Real.pi))) * (scale τ) ^ N * (1 + t)
        + Cc * (1 + Real.exp (-(2 * Real.pi))) * (scale τ) ^ N * (1 + t)
        + Cc * (1 + Real.exp (-(2 * Real.pi))) * (scale τ) ^ N * (1 + t)
      = (5 * (Cc * (1 + Real.exp (-(2 * Real.pi)))) + C0) * (scale τ) ^ N * (1 + t) from by ring]
  have hle : 5 * (Cc * (1 + Real.exp (-(2 * Real.pi)))) + C0 ≤ K := by rw [hK]; linarith
  have hpos : (0 : ℝ) ≤ (scale τ) ^ N * (1 + t) := mul_nonneg hsN0 (by linarith)
  calc (5 * (Cc * (1 + Real.exp (-(2 * Real.pi)))) + C0) * (scale τ) ^ N * (1 + t)
      = (5 * (Cc * (1 + Real.exp (-(2 * Real.pi)))) + C0) * ((scale τ) ^ N * (1 + t)) := by ring
    _ ≤ K * ((scale τ) ^ N * (1 + t)) := mul_le_mul_of_nonneg_right hle hpos
    _ = K * (scale τ) ^ N * (1 + t) := by ring

end

end Work.Asymptotics.Funnel24Tail
