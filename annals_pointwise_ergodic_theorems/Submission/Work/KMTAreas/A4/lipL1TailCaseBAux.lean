import Mathlib
import Submission.Work.KMTAreas.A4.peluseLipUniform
import Submission.Work.KMTAreas.A4.smoothOpTailLe
import Submission.Work.KMTAreas.A4.shellLeWindow
import Submission.Work.KMTAreas.A4.lipWeightAbsMoment

/-!
# Area A4: case `B` of Proposition `lip` with the free window `A N^d`

Auxiliary module of `Submission.Work.KMTAreas.A4.lipL1TailCaseBA`.  It contains

* self-contained copies of the window bookkeeping of `A4/windowA.lean` (that module is not
  imported because its interface is being reworked; the copies here are `private`);
* the three arithmetic lemmas consumed by the tail estimate (`tailSub1`, `tailSub2`) and by the
  truncation loss (`fourQNle`);
* `lipL1TailCaseB_window`, the `N`-large case of Proposition `lip` of Krause--Mirek--Tao §5 with
  the support window `A N^d`, the honest `l^1` bound and the spatial tail clause, in the form in
  which `lipL1TailCaseBA` consumes it.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000000
set_option maxRecDepth 20000

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## Self-contained copies of the window bookkeeping of `A4/windowA.lean` -/

private theorem cbWin_real_lt_natAbs {B : ℕ} {x : ℤ} : (B : ℝ) < |(x : ℝ)| ↔ B < x.natAbs := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs]
  exact_mod_cast Iff.rfl

private theorem cbWin_natAbs_cast_real (x : ℤ) : ((x.natAbs : ℕ) : ℝ) = |(x : ℝ)| := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs]
  norm_num

private theorem cbWin_supportIn_natAbs_le {f : ℤ → ℂ} {M : ℕ} (h : SupportIn f M) {x : ℤ}
    (hx : f x ≠ 0) : x.natAbs ≤ M := by
  by_contra hc
  exact hx (h x (not_le.mp hc))

private theorem cbWin_card_Icc_diff_Icc_le (M W : ℕ) :
    ((Finset.Icc (-(M : ℤ)) (M : ℤ)) \ (Finset.Icc (-(W : ℤ)) (W : ℤ))).card ≤ 2 * (M - W) := by
  have hsub : (Finset.Icc (-(M : ℤ)) (M : ℤ)) \ (Finset.Icc (-(W : ℤ)) (W : ℤ))
      ⊆ Finset.Icc ((W : ℤ) + 1) (M : ℤ) ∪ Finset.Icc (-(M : ℤ)) (-((W : ℤ) + 1)) := by
    intro y hy
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hy
    rcases hy with ⟨⟨h1, h2⟩, h3⟩
    simp only [Finset.mem_union, Finset.mem_Icc]
    by_cases h5 : -(W : ℤ) ≤ y
    · left
      constructor <;> omega
    · right
      constructor <;> omega
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 : (Finset.Icc ((W : ℤ) + 1) (M : ℤ)).card ≤ M - W := by
    rw [Int.card_Icc]
    omega
  have h2 : (Finset.Icc (-(M : ℤ)) (-((W : ℤ) + 1))).card ≤ M - W := by
    rw [Int.card_Icc]
    omega
  omega

private noncomputable def cbWin (A : ℝ) (N d : ℕ) : ℕ := Nat.floor (A * (N : ℝ) ^ d)

private theorem cbWin_le (A : ℝ) (hA : 0 ≤ A) (N d : ℕ) :
    (cbWin A N d : ℝ) ≤ A * (N : ℝ) ^ d :=
  Nat.floor_le (mul_nonneg hA (pow_nonneg (by positivity) d))

private theorem le_cbWin (A : ℝ) {N d M : ℕ} (h : (M : ℝ) ≤ A * (N : ℝ) ^ d) :
    M ≤ cbWin A N d :=
  Nat.le_floor h

private theorem cbWin_lt_natAbs {A : ℝ} (hA : 0 ≤ A) {N d : ℕ} {x : ℤ}
    (h : A * (N : ℝ) ^ d < |(x : ℝ)|) : cbWin A N d < x.natAbs := by
  have h1 : (cbWin A N d : ℝ) ≤ A * (N : ℝ) ^ d := cbWin_le A hA N d
  rw [← cbWin_real_lt_natAbs]
  exact lt_of_le_of_lt h1 h

private theorem cbWin_master {T K N δ : ℝ} (hT1 : 1 ≤ T) (hNpos : 0 < N) (hδpos : 0 < δ)
    (hδle : δ ≤ 1) (hN : T * δ⁻¹ ^ K < N) {α A : ℝ} {j : ℕ} (hα0 : 0 ≤ α) (hj : 1 ≤ j)
    (hα : α ≤ T ^ j) (hA : A ≤ K * (j : ℝ)) : α * δ⁻¹ ^ A ≤ N ^ j := by
  have hδ0 : 0 < δ⁻¹ := inv_pos.mpr hδpos
  have hδ1 : (1 : ℝ) ≤ δ⁻¹ := (one_le_inv₀ hδpos).mpr hδle
  have hT0 : 0 ≤ T := le_trans zero_le_one hT1
  have h1 : δ⁻¹ ^ A ≤ δ⁻¹ ^ (K * (j : ℝ)) := Real.rpow_le_rpow_of_exponent_le hδ1 hA
  have h2 : δ⁻¹ ^ (K * (j : ℝ)) = ((δ⁻¹) ^ K) ^ j := by
    rw [Real.rpow_mul hδ0.le, Real.rpow_natCast]
  have h3 : δ⁻¹ ^ A ≤ ((δ⁻¹) ^ K) ^ j := by
    calc δ⁻¹ ^ A ≤ δ⁻¹ ^ (K * (j : ℝ)) := h1
      _ = ((δ⁻¹) ^ K) ^ j := h2
  calc α * δ⁻¹ ^ A ≤ T ^ j * δ⁻¹ ^ A :=
        mul_le_mul_of_nonneg_right hα (Real.rpow_nonneg hδ0.le A)
    _ ≤ T ^ j * ((δ⁻¹) ^ K) ^ j := mul_le_mul_of_nonneg_left h3 (pow_nonneg hT0 j)
    _ = (T * δ⁻¹ ^ K) ^ j := by rw [mul_pow]
    _ ≤ N ^ j := pow_le_pow_left₀ (mul_nonneg hT0 (Real.rpow_nonneg hδ0.le K)) hN.le j

private theorem cbWin_rpow_low {C K N δ P : ℝ} (hC : 0 < C) (hδpos : 0 < δ) (hδle : δ ≤ 1)
    (hN : C * δ⁻¹ ^ K < N) (hPK : P ≤ K) : C / N ≤ δ ^ P := by
  have hδinv_pos : 0 < δ⁻¹ := inv_pos.mpr hδpos
  have hδK : 0 < δ ^ K := Real.rpow_pos_of_pos hδpos K
  have hNpos : 0 < N :=
    lt_of_lt_of_le (mul_pos hC (Real.rpow_pos_of_pos hδinv_pos K)) hN.le
  have h2 : (C * δ⁻¹ ^ K) * δ ^ K < N * δ ^ K := mul_lt_mul_of_pos_right hN hδK
  have h3 : (C * δ⁻¹ ^ K) * δ ^ K = C := by
    rw [mul_assoc, ← Real.mul_rpow hδinv_pos.le hδpos.le, inv_mul_cancel₀ hδpos.ne',
      Real.one_rpow, mul_one]
  have h4 : C < N * δ ^ K := by rw [h3] at h2; exact h2
  have h5 : δ ^ K ≤ δ ^ P := Real.rpow_le_rpow_of_exponent_ge hδpos hδle hPK
  rw [div_le_iff₀ hNpos]
  have h6 : N * δ ^ K ≤ δ ^ P * N := by
    rw [mul_comm (δ ^ P) N]
    exact mul_le_mul_of_nonneg_left h5 hNpos.le
  exact le_trans h4.le h6

private theorem caseBrpow {Cc Kc N δ : ℝ} (h : Cc * (δ⁻¹) ^ Kc < N) :
    Cc * δ⁻¹ ^ (Kc : ℝ) < N := by
  simpa only [Real.rpow_natCast] using h
/-- First sub-case of the tail estimate. -/
private theorem tailSub1 {δ Cc C₀ Cm c₁ Kc K₀ : ℝ} {N : ℝ} {d u q : ℕ}
    (hδpos : 0 < δ) (hδle : δ ≤ 1) (hCc7 : 7 ≤ Cc) (hC₀pos : 0 < C₀)
    (hCmpos : 0 < Cm) (hc₁pos : 0 < c₁)
    (hN1 : (1 : ℝ) ≤ N) (hd1 : 1 ≤ d)
    (hcase : Cc * δ⁻¹ ^ (Kc : ℝ) < N)
    (hα : 8 * C₀ ^ 2 * Cm * c₁ ≤ Cc ^ d)
    (hA : K₀ + 2 * (u : ℝ) ≤ Kc * (d : ℝ))
    (hqle : (q : ℝ) ≤ C₀ * δ⁻¹ ^ K₀) :
    (q : ℝ) * (Cm / (δ ^ u / c₁)) ≤ δ ^ u * N ^ d / (8 * C₀) := by
  have hCcpos : 0 < Cc := by linarith
  have hCc1 : (1 : ℝ) ≤ Cc := by linarith
  have hδu : 0 < δ ^ u := pow_pos hδpos u
  have hδinv : (1 : ℝ) ≤ δ⁻¹ := by rw [one_le_inv₀ hδpos]; exact hδle
  rw [show (q : ℝ) * (Cm / (δ ^ u / c₁)) = (q : ℝ) * Cm * c₁ * (δ⁻¹) ^ u by
        rw [div_div_eq_mul_div, div_eq_mul_inv, inv_pow]
        ring]
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < 8 * C₀ * (δ⁻¹) ^ u)
  have hL : ((q : ℝ) * Cm * c₁ * (δ⁻¹) ^ u) * (8 * C₀ * (δ⁻¹) ^ u)
      = 8 * C₀ * (q : ℝ) * Cm * c₁ * ((δ⁻¹) ^ u * (δ⁻¹) ^ u) := by ring
  have hR : (δ ^ u * N ^ d / (8 * C₀)) * (8 * C₀ * (δ⁻¹) ^ u)
      = (δ ^ u * (δ⁻¹) ^ u) * N ^ d := by
    field_simp; try ring
  rw [hL, hR]
  have hδu' : δ ^ u * (δ⁻¹) ^ u = 1 := by
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hδpos.ne')]
  rw [hδu', one_mul]
  have h2 : (δ⁻¹) ^ u * (δ⁻¹) ^ u = (δ⁻¹) ^ (2 * u) := by
    rw [← pow_add]
    congr 1
    ring
  rw [h2]
  have h3 : (δ⁻¹) ^ K₀ * (δ⁻¹) ^ (2 * u) = δ⁻¹ ^ (K₀ + 2 * (u : ℝ)) := by
    rw [← Real.rpow_natCast (δ⁻¹) (2 * u), ← Real.rpow_add (inv_pos.mpr hδpos)]
    congr 1
    push_cast
    ring
  have h5 : 8 * C₀ ^ 2 * Cm * c₁ * δ⁻¹ ^ (K₀ + 2 * (u : ℝ)) ≤ N ^ d :=
    cbWin_master (T := Cc) (K := Kc) (N := N) (δ := δ) (α := 8 * C₀ ^ 2 * Cm * c₁)
      (A := K₀ + 2 * (u : ℝ)) (j := d) hCc1 (by linarith) hδpos hδle hcase
      (by positivity) hd1 hα hA
  have hnn : (0 : ℝ) ≤ 8 * C₀ * Cm * c₁ * (δ⁻¹) ^ (2 * u) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₀pos.le) hCmpos.le)
      hc₁pos.le) (pow_nonneg (inv_nonneg.mpr hδpos.le) _)
  calc 8 * C₀ * (q : ℝ) * Cm * c₁ * (δ⁻¹) ^ (2 * u)
      = 8 * C₀ * Cm * c₁ * (δ⁻¹) ^ (2 * u) * (q : ℝ) := by ring
    _ ≤ 8 * C₀ * Cm * c₁ * (δ⁻¹) ^ (2 * u) * (C₀ * δ⁻¹ ^ K₀) :=
          mul_le_mul_of_nonneg_left hqle hnn
    _ = 8 * C₀ ^ 2 * Cm * c₁ * ((δ⁻¹) ^ K₀ * (δ⁻¹) ^ (2 * u)) := by ring
    _ = 8 * C₀ ^ 2 * Cm * c₁ * δ⁻¹ ^ (K₀ + 2 * (u : ℝ)) := by rw [h3]
    _ ≤ N ^ d := h5

/-- Second sub-case of the tail estimate. -/
private theorem tailSub2 {δ Cc C₀ Cm : ℝ} {Kc : ℕ} {K₀ : ℝ} {N : ℝ} {d u q : ℕ}
    (hδpos : 0 < δ) (hδle : δ ≤ 1) (hCc7 : 7 ≤ Cc) (hC₀pos : 0 < C₀)
    (hCmpos : 0 < Cm) (hCcC₀ : C₀ ≤ Cc)
    (hN1 : (1 : ℝ) ≤ N) (hd2 : 2 ≤ d)
    (h16 : 16 * C₀ * Cm ≤ Cc) (hdel : Cc / N ≤ δ ^ u)
    (hqle : (q : ℝ) ≤ C₀ * δ⁻¹ ^ K₀) (hK₀Kc : K₀ ≤ (Kc : ℝ)) :
    (q : ℝ) * (Cm / (Cc / 2 * (δ⁻¹) ^ Kc / N)) ≤ δ ^ u * N ^ d / (8 * C₀) := by
  have hNpos : 0 < N := by linarith
  have hδinv : (1 : ℝ) ≤ δ⁻¹ := by rw [one_le_inv₀ hδpos]; exact hδle
  have hCcpos : 0 < Cc := by linarith
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd2
  rw [show (q : ℝ) * (Cm / (Cc / 2 * (δ⁻¹) ^ Kc / N))
      = 2 * N * Cm * ((q : ℝ) / (δ⁻¹) ^ Kc) / Cc by
        field_simp; try ring]
  have h2 : (q : ℝ) / (δ⁻¹) ^ Kc ≤ C₀ := by
    rw [div_le_iff₀ (pow_pos (inv_pos.mpr hδpos) Kc)]
    calc (q : ℝ) ≤ C₀ * δ⁻¹ ^ K₀ := hqle
      _ ≤ C₀ * (δ⁻¹) ^ Kc := by
          refine mul_le_mul_of_nonneg_left ?_ hC₀pos.le
          simpa only [Real.rpow_natCast] using
            Real.rpow_le_rpow_of_exponent_le hδinv hK₀Kc
  have h3 : 2 * N * Cm * ((q : ℝ) / (δ⁻¹) ^ Kc) / Cc ≤ 2 * C₀ * Cm * N / Cc := by
    have h4 : 2 * N * Cm * ((q : ℝ) / (δ⁻¹) ^ Kc) ≤ 2 * N * Cm * C₀ :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [show 2 * N * Cm * C₀ = 2 * C₀ * Cm * N by ring] at h4
    exact div_le_div_of_nonneg_right h4 (by linarith)
  have h6 : 2 * C₀ * Cm * N / Cc ≤ N ^ (d - 1) / 8 := by
    have h7 : (1 : ℝ) ≤ N ^ (d - 2) := one_le_pow₀ (by linarith)
    have h9 : N ^ (d - 1) = N ^ (d - 2) * N := by
      rw [← pow_succ, show d - 2 + 1 = d - 1 by omega]
    have hN0 : (0 : ℝ) ≤ N := by linarith
    have h16' : 16 * C₀ * Cm * N ≤ Cc * N := mul_le_mul_of_nonneg_right h16 hN0
    have hB : Cc * N ≤ Cc * (N ^ (d - 2) * N) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      calc N = 1 * N := by ring
        _ ≤ N ^ (d - 2) * N := mul_le_mul_of_nonneg_right h7 hN0
    rw [h9, div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 8)]
    calc (2 * C₀ * Cm * N) * 8 = 16 * C₀ * Cm * N := by ring
      _ ≤ Cc * N := h16'
      _ ≤ Cc * (N ^ (d - 2) * N) := hB
      _ = (N ^ (d - 2) * N) * Cc := by ring
  have h5' : C₀ / N * (N ^ d / (8 * C₀)) = N ^ (d - 1) / 8 := by
    have h11 : N ^ d = N ^ (d - 1) * N := by
      rw [← pow_succ, show d - 1 + 1 = d by omega]
    rw [h11]
    field_simp; try ring
  have h5 : C₀ / N * (N ^ d / (8 * C₀)) ≤ δ ^ u * N ^ d / (8 * C₀) := by
    have h0 : (0 : ℝ) ≤ N ^ d / (8 * C₀) :=
      div_nonneg (pow_nonneg (le_of_lt hNpos) d) (mul_nonneg (by norm_num) hC₀pos.le)
    have hCN : C₀ / N ≤ Cc / N := div_le_div_of_nonneg_right hCcC₀ (le_of_lt hNpos)
    calc C₀ / N * (N ^ d / (8 * C₀)) ≤ Cc / N * (N ^ d / (8 * C₀)) :=
          mul_le_mul_of_nonneg_right hCN h0
      _ ≤ δ ^ u * (N ^ d / (8 * C₀)) := mul_le_mul_of_nonneg_right hdel h0
      _ = δ ^ u * N ^ d / (8 * C₀) := by ring
  calc 2 * N * Cm * ((q : ℝ) / (δ⁻¹) ^ Kc) / Cc
      ≤ 2 * C₀ * Cm * N / Cc := h3
    _ ≤ N ^ (d - 1) / 8 := h6
    _ = C₀ / N * (N ^ d / (8 * C₀)) := h5'.symm
    _ ≤ δ ^ u * N ^ d / (8 * C₀) := h5

/-- The truncation-loss absorption. -/
private theorem fourQNle {δ Cc C₀ Kc K₀ : ℝ} {N : ℝ} {d u q N' : ℕ}
    (hδpos : 0 < δ) (hδle : δ ≤ 1) (hCc7 : 7 ≤ Cc) (hC₀pos : 0 < C₀)
    (hN1 : (1 : ℝ) ≤ N) (hd2 : 2 ≤ d)
    (hcase : Cc * δ⁻¹ ^ (Kc : ℝ) < N)
    (hα : 16 * C₀ ^ 2 ≤ Cc ^ (d - 1))
    (hA : K₀ + (u : ℝ) ≤ Kc * ((d - 1 : ℕ) : ℝ))
    (hqle : (q : ℝ) ≤ C₀ * δ⁻¹ ^ K₀) (hN'le : (N' : ℝ) ≤ N) :
    4 * ((q : ℝ) * (N' : ℝ)) ≤ δ ^ u * N ^ d / (4 * C₀) := by
  have hCc1 : (1 : ℝ) ≤ Cc := by linarith
  have hNpos : 0 < N := by linarith
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd2
  have hqN'R : (q : ℝ) * (N' : ℝ) ≤ C₀ * δ⁻¹ ^ K₀ * N := by
    calc (q : ℝ) * (N' : ℝ) ≤ (C₀ * δ⁻¹ ^ K₀) * (N' : ℝ) :=
          mul_le_mul_of_nonneg_right hqle (by positivity)
      _ ≤ (C₀ * δ⁻¹ ^ K₀) * N :=
          mul_le_mul_of_nonneg_left hN'le (by positivity)
      _ = C₀ * δ⁻¹ ^ K₀ * N := rfl
  have hj : 1 ≤ d - 1 := by omega
  have hZ : 16 * C₀ ^ 2 * δ⁻¹ ^ (K₀ + (u : ℝ)) ≤ N ^ (d - 1) :=
    cbWin_master (T := Cc) (K := Kc) (N := N) (δ := δ) (α := 16 * C₀ ^ 2)
      (A := K₀ + (u : ℝ)) (j := d - 1) hCc1 hNpos hδpos hδle hcase
      (by positivity) hj hα hA
  calc 4 * ((q : ℝ) * (N' : ℝ)) ≤ 4 * (C₀ * δ⁻¹ ^ K₀ * N) := by linarith
    _ = (16 * C₀ ^ 2 * δ⁻¹ ^ (K₀ + (u : ℝ))) * (δ ^ u * N / (4 * C₀)) := by
          rw [Real.rpow_add (x := δ⁻¹) (inv_pos.mpr hδpos), Real.rpow_natCast, inv_pow]
          field_simp; try ring
    _ ≤ N ^ (d - 1) * (δ ^ u * N / (4 * C₀)) := mul_le_mul_of_nonneg_right hZ (by positivity)
    _ = δ ^ u * N ^ d / (4 * C₀) := by
          have h11 : N ^ (d - 1) * N = N ^ d := by
            rw [← pow_succ, show d - 1 + 1 = d by omega]
          calc N ^ (d - 1) * (δ ^ u * N / (4 * C₀))
              = δ ^ u * (N ^ (d - 1) * N) / (4 * C₀) := by ring
            _ = δ ^ u * N ^ d / (4 * C₀) := by rw [h11]

private theorem cbStarDivNorm (z : ℂ) : ‖star z / (‖z‖ : ℂ)‖ = if z = 0 then 0 else 1 := by
  by_cases h : z = 0
  · rw [h]; simp
  · rw [if_neg h, norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg z)]
    exact div_self (by simpa using h)

private theorem cbStarDivMulSelf (z : ℂ) (h : z ≠ 0) :
    star z / (‖z‖ : ℂ) * z = (‖z‖ : ℂ) := by
  rw [div_mul_eq_mul_div, mul_comm (star z) z]
  have h1 : z * star z = ((‖z‖ * ‖z‖ : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [h1, ← Complex.ofReal_div]
  congr 1
  field_simp

theorem lipL1TailCaseB_window
    (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (ψ : SchwartzR)
    (Kw Cm C₀ K₀ : ℝ) (u Kc : ℕ) (K' c₁ c₂ Cc : ℝ) (A : ℝ)
    (hψint : ∫ y : ℝ, (ψ : ℝ → ℂ) y = 1)
    (hψsupp : ∀ s : ℝ, 1 < |s| → schFT ψ s = 0)
    (hKwpos : 0 < Kw)
    (hKw : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ {N' : ℕ}, 1 ≤ N' →
      ∑' m : ℤ, ‖lipWeight ψ ε N' m‖ ≤ Kw)
    (hCmpos : 0 < Cm)
    (hCm : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ {N' : ℕ}, 1 ≤ N' →
      ∑' m : ℤ, ‖lipWeight ψ ε N' m‖ * max 0 (|(m : ℝ)| - (N' : ℝ)) ≤ Cm / ε)
    (hC₀pos : 0 < C₀) (hK₀pos : 0 < K₀)
    (hu_ge : K₀ ≤ (u : ℝ)) (hu1 : 1 ≤ u)
    (hKcu : u ≤ Kc) (hKc2u : 2 * u ≤ Kc) (hKc3u : 3 * u ≤ Kc) (hKc4u : 4 * u ≤ Kc)
    (hKcpos : (0 : ℝ) < (Kc : ℝ)) (hKcK₀ : K₀ ≤ (Kc : ℝ))
    (hK'def : K' = 2 * A + 5 + 2 * C₀) (hK'pos : 0 < K') (hK'1 : 1 ≤ K')
    (hfour : 0 < 4 * C₀ * calcConst ψ * K')
    (hc₁pos : 0 < c₁) (hc₁1 : 1 ≤ c₁) (hc₁big : 4 * C₀ * calcConst ψ * K' ≤ c₁ ^ 10)
    (hc₂pos : 0 < c₂) (hc₂def : c₂ = 4 * C₀ ^ 2 * calcConst ψ * K')
    (hCcpos : 0 < Cc)
    (hCc2C₀ : 2 * C₀ ≤ Cc) (hCcC₀ : C₀ ≤ Cc) (hCc7 : 7 ≤ Cc)
    (hCcKw : 2 * C₀ * Kw * K' ≤ Cc) (hCcc₁c₂ : c₁ * c₂ ≤ Cc) (hCc2c₂ : 2 * c₂ ≤ Cc)
    (h4C₀Kw : 4 * C₀ * Kw ≤ Cc) (h4C₀KwK' : 4 * C₀ * Kw * K' ≤ Cc)
    (h16C₀₂Cmc₁ : 16 * C₀ ^ 2 * Cm * c₁ ≤ Cc) (h16C₀Cm : 16 * C₀ * Cm ≤ Cc)
    (h16C₀sq : 16 * C₀ ^ 2 ≤ Cc)
    (hA : 1 ≤ A) (ρ : ℝ) (hρpos : 0 < ρ) (hρle : ρ ≤ 1)
    (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ)
    (hN : 1 ≤ N) (hδpos : 0 < δ) (hδle : δ ≤ 1)
    (hN₀hi : (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree)
    (hfs : SupportIn f N₀) (hfb : ∀ x : ℤ, ‖f x‖ ≤ 1)
    (q N' : ℕ) (hq1 : 1 ≤ q) (hqle : (q : ℝ) ≤ C₀ * δ⁻¹ ^ K₀) (hN'1 : 1 ≤ N')
    (hN'le : N' ≤ N) (hN'lb : δ ^ K₀ * N ≤ C₀ * N')
    (hA1 : δ ^ K₀ * (N : ℝ) ^ P.natDegree ≤
      C₀ * ∑' x : ℤ, ‖(N' : ℂ)⁻¹ * ∑ m ∈ Finset.Icc 1 N', f (x + (q : ℤ) * (m : ℤ))‖)
    (hcaseB : Cc * (δ⁻¹) ^ Kc < N) :
    ∃ (F : ℤ → ℂ) (l : ℕ) (k : ℤ),
      (∀ x : ℤ, ‖F x‖ ≤ Cc * (δ⁻¹) ^ Kc) ∧
      Summable (fun x : ℤ => ‖F x‖) ∧
      (∑' x : ℤ, ‖F x‖ ≤ Cc * (δ⁻¹) ^ Kc * (N : ℝ) ^ P.natDegree) ∧
      (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)| then ‖F x‖ else 0)
        ≤ δ ^ Kc * (N : ℝ) ^ P.natDegree / 2) ∧
      FourierSupportIn F (majorArc ρ l k) ∧
      (2 : ℝ) ^ l ≤ Cc * (δ⁻¹) ^ Kc ∧
      (2 : ℝ) ^ k ≤ Cc * (δ⁻¹) ^ Kc / (N : ℝ) ∧
      δ ^ Kc * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair f F‖ := by
    classical
    have hD1 : (1 : ℝ) ≤ δ⁻¹ := by rw [one_le_inv₀ hδpos]; exact hδle
    have hDpos : 0 < δ⁻¹ := inv_pos.mpr hδpos
    have hA0 : (0 : ℝ) ≤ A := le_trans (by norm_num) hA
    have hcaseBrpow : Cc * δ⁻¹ ^ ((Kc : ℕ) : ℝ) < N := by simpa only [Real.rpow_natCast] using hcaseB
    have hanti : ∀ {m n : ℕ}, m ≤ n → δ ^ n ≤ δ ^ m := by
      intro m n hmn
      have h := Real.rpow_le_rpow_of_exponent_ge hδpos hδle
        (show (m : ℝ) ≤ (n : ℝ) by exact_mod_cast hmn)
      simpa [Real.rpow_natCast] using h
    have hδu_le : δ ^ u ≤ δ ^ K₀ := by
      have h2 := Real.rpow_le_rpow_of_exponent_ge hδpos hδle hu_ge
      simpa [Real.rpow_natCast] using h2
    have hD1u : (1 : ℝ) ≤ (δ⁻¹) ^ u := one_le_pow₀ hD1
    have hδinv_le : δ⁻¹ ^ K₀ ≤ (δ⁻¹) ^ u := by
      have h1 : 0 < δ ^ K₀ := Real.rpow_pos_of_pos hδpos K₀
      have h2 : 0 < δ ^ u := pow_pos hδpos u
      calc δ⁻¹ ^ K₀ = (δ ^ K₀)⁻¹ := Real.inv_rpow hδpos.le K₀
        _ ≤ (δ ^ u)⁻¹ := (inv_le_inv₀ h1 h2).mpr hδu_le
        _ = (δ⁻¹) ^ u := (inv_pow δ u).symm
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
    have hcoef : ((((N' : ℝ))⁻¹ : ℝ) : ℂ) = (N' : ℂ)⁻¹ := by
      norm_num [Complex.ofReal_inv]
    let Aavg : ℤ → ℂ := fun x => ((((N' : ℝ))⁻¹ : ℝ) : ℂ) *
      ∑ m ∈ Finset.Icc 1 N', f (x + (q : ℤ) * (m : ℤ))
    have hAle : δ ^ u * (N : ℝ) ^ P.natDegree / C₀ ≤ ellOne Aavg := by
      have h1 : δ ^ u * (N : ℝ) ^ P.natDegree ≤ δ ^ K₀ * (N : ℝ) ^ P.natDegree :=
        mul_le_mul_of_nonneg_right hδu_le (by positivity)
      have h3 : (∑' x : ℤ, ‖Aavg x‖)
          = ∑' x : ℤ, ‖(N' : ℂ)⁻¹ * ∑ m ∈ Finset.Icc 1 N',
              f (x + (q : ℤ) * (m : ℤ))‖ := by
        refine tsum_congr fun x => ?_
        change ‖((((N' : ℝ))⁻¹ : ℝ) : ℂ) * ∑ m ∈ Finset.Icc 1 N',
          f (x + (q : ℤ) * (m : ℤ))‖ = _
        rw [hcoef]
      have h2 : δ ^ K₀ * (N : ℝ) ^ P.natDegree ≤ C₀ * ellOne Aavg := by
        rw [ellOne, h3]; exact hA1
      rw [div_le_iff₀ hC₀pos]; linarith
    -- ### the support radius of the progression average
    have hAsupp : SupportIn Aavg (N₀ + q * N') := by
      intro x hx
      have hx' : N₀ + q * N' < x.natAbs := hx
      show ((((N' : ℝ))⁻¹ : ℝ) : ℂ) * ∑ m ∈ Finset.Icc 1 N',
        f (x + (q : ℤ) * (m : ℤ)) = 0
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun m hm => ?_)
      rw [Finset.mem_Icc] at hm
      have hfm : f (x + (q : ℤ) * (m : ℤ)) = 0 := by
        apply hfs
        have h1 : x.natAbs ≤ (x + (q : ℤ) * (m : ℤ)).natAbs + q * m := by
          have h2 := Int.natAbs_add_le (x + (q : ℤ) * (m : ℤ)) (-((q : ℤ) * (m : ℤ)))
          have h3 : x + (q : ℤ) * (m : ℤ) + -((q : ℤ) * (m : ℤ)) = x := by ring
          rw [h3] at h2
          have h4 : (-((q : ℤ) * (m : ℤ))).natAbs = q * m := by
            rw [Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
          rw [h4] at h2
          exact h2
        change N₀ + q * N' < x.natAbs at hx'
        have h5 : q * m ≤ q * N' := Nat.mul_le_mul_left q hm.2
        omega
      exact hfm
    have hAbd : ∀ x : ℤ, ‖Aavg x‖ ≤ 1 := by
      intro x
      have hN'pos : (0 : ℝ) < (N' : ℝ) := by exact_mod_cast hN'1
      have h1 : ‖((((N' : ℝ))⁻¹ : ℝ) : ℂ)‖ = ((N' : ℝ))⁻¹ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      change ‖((((N' : ℝ))⁻¹ : ℝ) : ℂ) * ∑ m ∈ Finset.Icc 1 N',
        f (x + (q : ℤ) * (m : ℤ))‖ ≤ 1
      rw [norm_mul, h1]
      have h2 : ‖∑ m ∈ Finset.Icc 1 N', f (x + (q : ℤ) * (m : ℤ))‖ ≤ (N' : ℝ) := by
        calc ‖∑ m ∈ Finset.Icc 1 N', f (x + (q : ℤ) * (m : ℤ))‖
            ≤ ∑ m ∈ Finset.Icc 1 N', ‖f (x + (q : ℤ) * (m : ℤ))‖ := norm_sum_le _ _
          _ ≤ ∑ _m ∈ Finset.Icc 1 N', (1 : ℝ) := Finset.sum_le_sum fun m _ => hfb _
          _ = ((Finset.Icc 1 N').card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          _ = (N' : ℝ) := by rw [Nat.card_Icc, Nat.add_sub_cancel]
      calc ((N' : ℝ))⁻¹ * ‖∑ m ∈ Finset.Icc 1 N', f (x + (q : ℤ) * (m : ℤ))‖
          ≤ ((N' : ℝ))⁻¹ * (N' : ℝ) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hN'pos)
    -- ### the window `D = ⌊A N^d⌋` and the cut-off dual function `G`
    set D : ℕ := cbWin A N P.natDegree with hDdef
    have hDle : (D : ℝ) ≤ A * (N : ℝ) ^ P.natDegree := cbWin_le A hA0 N _
    have hN₀D : N₀ ≤ D := le_cbWin A hN₀hi
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hqN'R : (q : ℝ) * (N' : ℝ) ≤ C₀ * δ⁻¹ ^ K₀ * (N : ℝ) := by
      calc (q : ℝ) * (N' : ℝ) ≤ (C₀ * δ⁻¹ ^ K₀) * (N' : ℝ) :=
            mul_le_mul_of_nonneg_right hqle (by positivity)
        _ ≤ (C₀ * δ⁻¹ ^ K₀) * (N : ℝ) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact_mod_cast hN'le
        _ = C₀ * δ⁻¹ ^ K₀ * (N : ℝ) := rfl
    have hC₀δN : C₀ * δ⁻¹ ^ K₀ ≤ (N : ℝ) := by
      have h3 : δ⁻¹ ^ K₀ ≤ (δ⁻¹) ^ Kc := by
        simpa only [Real.rpow_natCast] using
          Real.rpow_le_rpow_of_exponent_le hD1 hKcK₀
      calc C₀ * δ⁻¹ ^ K₀ ≤ Cc * δ⁻¹ ^ K₀ :=
            mul_le_mul_of_nonneg_right hCcC₀ (Real.rpow_nonneg hDpos.le K₀)
        _ ≤ Cc * (δ⁻¹) ^ Kc := mul_le_mul_of_nonneg_left h3 hCcpos.le
        _ ≤ (N : ℝ) := le_of_lt hcaseB
    have hqN'le : (q : ℝ) * (N' : ℝ) ≤ A * (N : ℝ) ^ P.natDegree := by
      calc (q : ℝ) * (N' : ℝ) ≤ C₀ * δ⁻¹ ^ K₀ * (N : ℝ) := hqN'R
        _ ≤ (N : ℝ) * (N : ℝ) := mul_le_mul hC₀δN le_rfl (by linarith) (by linarith)
        _ = (N : ℝ) ^ 2 := by ring
        _ ≤ (N : ℝ) ^ P.natDegree := pow_le_pow_right₀ (by linarith) (by omega)
        _ ≤ A * (N : ℝ) ^ P.natDegree := le_mul_of_one_le_left (by positivity) hA
    have hqN'nat : q * N' ≤ D := by
      rw [hDdef]
      apply Nat.le_floor
      push_cast
      exact hqN'le
    set MW : ℕ := D - q * N' with hMWdef
    have hMWle : MW ≤ D := by rw [hMWdef]; omega
    have hMWcast : (MW : ℤ) = (D : ℤ) - (q : ℤ) * (N' : ℤ) := by
      have h1 : (MW : ℤ) = ((D - q * N' : ℕ) : ℤ) := by rw [hMWdef]
      rw [h1, Nat.cast_sub hqN'nat]
      push_cast
      ring
    set W : Finset ℤ := Finset.Icc (-(MW : ℤ)) (MW : ℤ) with hWdef
    set G : ℤ → ℂ := fun y => if -((MW : ℤ)) ≤ y ∧ y ≤ (MW : ℤ) then
        star (Aavg y) / (‖Aavg y‖ : ℂ) else 0 with hGdef
    have hGsupp : SupportIn G MW := by
      intro y hy
      rw [hGdef]
      refine if_neg ?_
      rintro ⟨h2, h3⟩
      have h4 : (y.natAbs : ℤ) ≤ (MW : ℤ) := by
        rw [Int.natCast_natAbs]; exact abs_le.mpr ⟨h2, h3⟩
      omega
    have hGbd : ∀ y : ℤ, ‖G y‖ ≤ 1 := by
      intro y
      change ‖(if -((MW : ℤ)) ≤ y ∧ y ≤ (MW : ℤ) then
        star (Aavg y) / (‖Aavg y‖ : ℂ) else 0)‖ ≤ 1
      by_cases h : -((MW : ℤ)) ≤ y ∧ y ≤ (MW : ℤ)
      · rw [if_pos h, cbStarDivNorm]
        split <;> norm_num
      · rw [if_neg h]; simp
    have hGsum : Summable (fun y : ℤ => ‖G y‖) :=
      summable_of_ne_finset_zero (s := W) fun y hy => by
        have hy' : MW < y.natAbs := by
          simp only [hWdef, Finset.mem_Icc, not_and_or, not_le] at hy
          rcases hy with h | h <;> omega
        rw [hGsupp y hy', norm_zero]
    have hGone : ellOne G ≤ 2 * (MW : ℝ) + 1 := by
      simpa using ellOne_le_of_supportIn G MW hGsupp hGbd
    have hGzero : ∀ x : ℤ, x ∉ W → G x = 0 := by
      intro x hx
      apply hGsupp
      simp only [hWdef, Finset.mem_Icc, not_and_or, not_le] at hx
      rcases hx with h | h <;> omega
    have hGpairW : (∑' y : ℤ, G y * Aavg y) = ((∑ y ∈ W, ‖Aavg y‖ : ℝ) : ℂ) := by
      rw [tsum_eq_sum (s := W) ?_, Complex.ofReal_sum]
      · refine Finset.sum_congr rfl fun y hy => ?_
        change G y * Aavg y = ((‖Aavg y‖ : ℝ) : ℂ)
        rw [show G y = (if -((MW : ℤ)) ≤ y ∧ y ≤ (MW : ℤ) then
          star (Aavg y) / (‖Aavg y‖ : ℂ) else 0) from rfl, if_pos ?_]
        · by_cases h0 : Aavg y = 0
          · rw [h0]; simp
          · exact cbStarDivMulSelf (Aavg y) h0
        · rw [hWdef, Finset.mem_Icc] at hy; exact ⟨hy.1, hy.2⟩
      · intro y hy
        have hy' : MW < y.natAbs := by
          simp only [hWdef, Finset.mem_Icc, not_and_or, not_le] at hy
          rcases hy with h | h <;> omega
        rw [hGsupp y hy', zero_mul]
    have hMdW : 2 * (MW : ℝ) + 1 ≤ K' * (δ⁻¹) ^ u * (N : ℝ) ^ P.natDegree := by
      have h1 : (MW : ℝ) ≤ A * (N : ℝ) ^ P.natDegree :=
        le_trans (by exact_mod_cast hMWle) hDle
      have hd1 : (1 : ℝ) ≤ (N : ℝ) ^ P.natDegree := one_le_pow₀ hN1
      have h3 : (1 : ℝ) ≤ (δ⁻¹) ^ u := one_le_pow₀ hD1
      have h4 : 2 * (MW : ℝ) + 1 ≤ (2 * A + 5) * (N : ℝ) ^ P.natDegree := by
        nlinarith only [h1, hd1]
      have h5 : (2 * A + 5) * (N : ℝ) ^ P.natDegree ≤ K' * (N : ℝ) ^ P.natDegree := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hK'def]; linarith only [hC₀pos]
      have h6 : K' * (N : ℝ) ^ P.natDegree ≤ K' * (δ⁻¹) ^ u * (N : ℝ) ^ P.natDegree := by
        calc K' * (N : ℝ) ^ P.natDegree = K' * 1 * (N : ℝ) ^ P.natDegree := by ring
          _ ≤ K' * (δ⁻¹) ^ u * (N : ℝ) ^ P.natDegree :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hK'pos.le) (by positivity)
      linarith only [h4, h5, h6]
    have hAloss : ellOne Aavg - (∑ y ∈ W, ‖Aavg y‖) ≤ 4 * ((q : ℝ) * (N' : ℝ)) := by
      set s : Finset ℤ := Finset.Icc (-((N₀ + q * N' : ℕ) : ℤ)) ((N₀ + q * N' : ℕ) : ℤ) with hs
      have hAsum : ellOne Aavg = ∑ y ∈ s, ‖Aavg y‖ := by
        rw [ellOne]
        refine tsum_eq_sum fun y hy => ?_
        have hy3 : (((N₀ + q * N' : ℕ) : ℤ)) < (y.natAbs : ℤ) := by
          simp only [hs, Finset.mem_Icc, not_and_or, not_le] at hy
          rcases hy with h | h <;> omega
        have hy4 : (N₀ + q * N') < y.natAbs := by omega
        rw [hAsupp y hy4, norm_zero]
      have hcard : ((s \ W).card : ℝ) ≤ 4 * ((q : ℝ) * (N' : ℝ)) := by
        have h5 : (s \ W).card ≤ 4 * (q * N') := by
          rw [hs, hWdef]
          refine le_trans (cbWin_card_Icc_diff_Icc_le (N₀ + q * N') MW) ?_
          have h7 : N₀ + q * N' - MW ≤ 2 * (q * N') := by
            rw [hMWdef]
            omega
          omega
        calc ((s \ W).card : ℝ) ≤ ((4 * (q * N') : ℕ) : ℝ) := by exact_mod_cast h5
          _ = 4 * ((q : ℝ) * (N' : ℝ)) := by push_cast; ring
      have hsplit : (∑ y ∈ s, ‖Aavg y‖)
          = (∑ y ∈ s ∩ W, ‖Aavg y‖) + (∑ y ∈ s \ W, ‖Aavg y‖) := by
        have hu : s ∩ W ∪ (s \ W) = s := by
          ext x
          simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
          tauto
        have hd : Disjoint (s ∩ W) (s \ W) := by
          rw [Finset.disjoint_left]
          intro x hx hx'
          exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2
        calc (∑ y ∈ s, ‖Aavg y‖) = ∑ y ∈ s ∩ W ∪ (s \ W), ‖Aavg y‖ := by rw [hu]
          _ = (∑ y ∈ s ∩ W, ‖Aavg y‖) + (∑ y ∈ s \ W, ‖Aavg y‖) := Finset.sum_union hd
      have hb1 : (∑ y ∈ s ∩ W, ‖Aavg y‖) ≤ ∑ y ∈ W, ‖Aavg y‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right)
          (fun y _ _ => norm_nonneg _)
      have hb2 : (∑ y ∈ s \ W, ‖Aavg y‖) ≤ (s \ W).card := by
        have h6 : (∑ y ∈ s \ W, ‖Aavg y‖) ≤ ∑ _y ∈ s \ W, (1 : ℝ) :=
          Finset.sum_le_sum fun y _ => hAbd y
        simpa using h6
      have hbound : ellOne Aavg ≤ (∑ y ∈ W, ‖Aavg y‖) + 4 * ((q : ℝ) * (N' : ℝ)) := by
        calc ellOne Aavg = ∑ y ∈ s, ‖Aavg y‖ := hAsum
          _ = (∑ y ∈ s ∩ W, ‖Aavg y‖) + (∑ y ∈ s \ W, ‖Aavg y‖) := hsplit
          _ ≤ (∑ y ∈ W, ‖Aavg y‖) + 4 * ((q : ℝ) * (N' : ℝ)) :=
              add_le_add hb1 (le_trans hb2 hcard)
      linarith [hbound]
    have hα4 : 16 * C₀ ^ 2 ≤ Cc ^ (P.natDegree - 1) := by
      have hj : 1 ≤ P.natDegree - 1 := by omega
      have h1 : (1 : ℝ) ≤ Cc := by linarith only [hCc7]
      calc 16 * C₀ ^ 2 ≤ Cc := h16C₀sq
        _ = Cc ^ 1 := (pow_one Cc).symm
        _ ≤ Cc ^ (P.natDegree - 1) := pow_le_pow_right₀ h1 hj
    have hA4 : K₀ + (u : ℝ) ≤ Kc * ((P.natDegree - 1 : ℕ) : ℝ) := by
      have h1 : K₀ + (u : ℝ) ≤ (Kc : ℝ) := by
        have h2 : K₀ + (u : ℝ) ≤ 2 * (u : ℝ) := by linarith only [hu_ge]
        have h3 : ((2 * u : ℕ) : ℝ) ≤ (Kc : ℝ) := by exact_mod_cast hKc2u
        have h4 : (2 : ℝ) * (u : ℝ) = ((2 * u : ℕ) : ℝ) := by push_cast; ring
        linarith only [h2, h3, h4]
      have h4 : (1 : ℝ) ≤ ((P.natDegree - 1 : ℕ) : ℝ) := by
        rw [Nat.one_le_cast]; omega
      nlinarith only [h1, h4, hKcpos]
    have h4q : 4 * ((q : ℝ) * (N' : ℝ)) ≤ δ ^ u * (N : ℝ) ^ P.natDegree / (4 * C₀) :=
      fourQNle hδpos hδle hCc7 hC₀pos hN1 (by omega) hcaseBrpow hα4 hA4 hqle
        (by exact_mod_cast hN'le)

    -- the smoothing scale
    let mr : ℕ := u
    let ε : ℝ := min (δ ^ mr / c₁) (Cc / 2 * (δ⁻¹) ^ Kc / N)
    have hεpos : 0 < ε := by
      refine lt_min ?_ ?_
      · exact div_pos (pow_pos hδpos mr) hc₁pos
      · exact div_pos (mul_pos (by linarith [hCcpos]) (pow_pos hDpos Kc))
          (by exact_mod_cast hN)
    have hεlemr : ε ≤ δ ^ mr / c₁ := min_le_left _ _
    have hεle2 : ε ≤ Cc / 2 * (δ⁻¹) ^ Kc / N := min_le_right _ _
    have hεle1 : ε ≤ 1 := by
      refine le_trans hεlemr ?_
      rw [div_le_one hc₁pos]
      have h1 : δ ^ mr ≤ 1 := pow_le_one₀ hδpos.le hδle
      linarith
    have hε10 : ε ^ 10 ≤ δ ^ (2 * u) / (4 * C₀ * calcConst ψ * K') := by
      have h1 : ε ^ 10 ≤ (δ ^ mr / c₁) ^ 10 := pow_le_pow_left₀ hεpos.le hεlemr 10
      have h2 : (δ ^ mr / c₁) ^ 10 = δ ^ (10 * mr) / c₁ ^ 10 := by
        rw [div_pow, ← pow_mul, mul_comm]
      have h3 : δ ^ (10 * mr) ≤ δ ^ (2 * u) := by
        have := hanti (m := 2 * u) (n := 10 * mr) (by simp only [mr]; omega)
        simpa using this
      have h4 : δ ^ (2 * u) / c₁ ^ 10 ≤ δ ^ (2 * u) / (4 * C₀ * calcConst ψ * K') :=
        div_le_div_of_nonneg_left (by positivity) hfour (by simpa using hc₁big)
      calc ε ^ 10 ≤ (δ ^ mr / c₁) ^ 10 := h1
        _ = δ ^ (10 * mr) / c₁ ^ 10 := h2
        _ ≤ δ ^ (2 * u) / c₁ ^ 10 := div_le_div_of_nonneg_right h3 (by positivity)
        _ ≤ δ ^ (2 * u) / (4 * C₀ * calcConst ψ * K') := h4
    have hεN'ge : 4 * C₀ * calcConst ψ * K' * (δ ^ (2 * u))⁻¹ ≤ ε * (N' : ℝ) := by
      have hN'ge : δ ^ u * (N : ℝ) / C₀ ≤ (N' : ℝ) := by
        have h1 : δ ^ u * (N : ℝ) ≤ δ ^ K₀ * (N : ℝ) :=
          mul_le_mul_of_nonneg_right hδu_le (by positivity)
        rw [div_le_iff₀ hC₀pos]
        linarith [hN'lb]
      have hδ1 : (δ ^ (2 * u))⁻¹ ≤ δ ^ mr * δ ^ u * (δ ^ Kc)⁻¹ := by
        have hpu : 0 < δ ^ (2 * u) := pow_pos hδpos _
        have hpk : 0 < δ ^ Kc := pow_pos hδpos _
        rw [inv_le_iff_one_le_mul₀ hpu]
        rw [show (δ ^ mr * δ ^ u * (δ ^ Kc)⁻¹) * δ ^ (2 * u)
              = δ ^ (mr + u + 2 * u) / δ ^ Kc by
          rw [pow_add, pow_add, inv_eq_one_div]; ring]
        rw [one_le_div hpk]
        rw [show δ ^ (mr + u + 2 * u) = δ ^ (4 * u) by
          congr 1; simp only [mr]; omega]
        exact hanti hKc4u
      have hδ2 : (δ ^ (2 * u))⁻¹ ≤ (δ ^ Kc)⁻¹ * δ ^ u := by
        have hpu : 0 < δ ^ (2 * u) := pow_pos hδpos _
        have hpk : 0 < δ ^ Kc := pow_pos hδpos _
        rw [inv_le_iff_one_le_mul₀ hpu]
        rw [show ((δ ^ Kc)⁻¹ * δ ^ u) * δ ^ (2 * u) = δ ^ (u + 2 * u) / δ ^ Kc by
          rw [pow_add, inv_eq_one_div]; ring]
        rw [one_le_div hpk]
        rw [show δ ^ (u + 2 * u) = δ ^ (3 * u) by congr 1; omega]
        exact hanti hKc3u
      rcases le_total (δ ^ mr / c₁) (Cc / 2 * (δ⁻¹) ^ Kc / N) with hle | hle
      · have hεv : ε = δ ^ mr / c₁ := min_eq_left hle
        rw [hεv]
        have hcc : 4 * C₀ * calcConst ψ * K' ≤ Cc / (c₁ * C₀) := by
          rw [le_div_iff₀ (by positivity)]
          calc 4 * C₀ * calcConst ψ * K' * (c₁ * C₀) = c₁ * c₂ := by rw [hc₂def]; ring
            _ ≤ Cc := hCcc₁c₂
        have hstep : Cc / (c₁ * C₀) * (δ ^ mr * δ ^ u * (δ ^ Kc)⁻¹)
            ≤ (δ ^ mr / c₁) * (δ ^ u * (N : ℝ) / C₀) := by
          have h1 : δ ^ u * (Cc * (δ⁻¹) ^ Kc) / C₀ ≤ δ ^ u * (N : ℝ) / C₀ := by
            apply div_le_div_of_nonneg_right _ hC₀pos.le
            exact mul_le_mul_of_nonneg_left hcaseB.le (by positivity)
          calc Cc / (c₁ * C₀) * (δ ^ mr * δ ^ u * (δ ^ Kc)⁻¹)
              = (δ ^ mr / c₁) * (δ ^ u * (Cc * (δ⁻¹) ^ Kc) / C₀) := by
                rw [inv_pow]; field_simp; try ring
            _ ≤ (δ ^ mr / c₁) * (δ ^ u * (N : ℝ) / C₀) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
        calc 4 * C₀ * calcConst ψ * K' * (δ ^ (2 * u))⁻¹
            ≤ Cc / (c₁ * C₀) * (δ ^ mr * δ ^ u * (δ ^ Kc)⁻¹) :=
              mul_le_mul hcc hδ1 (by positivity) (by positivity)
          _ ≤ (δ ^ mr / c₁) * (δ ^ u * (N : ℝ) / C₀) := hstep
          _ ≤ (δ ^ mr / c₁) * (N' : ℝ) := mul_le_mul_of_nonneg_left hN'ge (by positivity)
      · have hεv : ε = Cc / 2 * (δ⁻¹) ^ Kc / N := min_eq_right hle
        rw [hεv]
        have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
        have hcc2 : 4 * C₀ * calcConst ψ * K' ≤ Cc / (2 * C₀) := by
          rw [le_div_iff₀ (by positivity)]
          calc 4 * C₀ * calcConst ψ * K' * (2 * C₀) = 2 * c₂ := by rw [hc₂def]; ring
            _ ≤ Cc := hCc2c₂
        have hstep : 4 * C₀ * calcConst ψ * K' * (δ ^ (2 * u))⁻¹
            ≤ Cc / 2 * (δ⁻¹) ^ Kc / N * (δ ^ u * (N : ℝ) / C₀) := by
          have h1 : (δ ^ (2 * u))⁻¹ ≤ (δ⁻¹) ^ Kc * δ ^ u := by
            rw [inv_pow]; exact hδ2
          have h2 : Cc / (2 * C₀) * (δ ^ (2 * u))⁻¹
              ≤ Cc / 2 * (δ⁻¹) ^ Kc / N * (δ ^ u * (N : ℝ) / C₀) := by
            have hrw : Cc / 2 * (δ⁻¹) ^ Kc / N * (δ ^ u * (N : ℝ) / C₀)
                = Cc / (2 * C₀) * ((δ⁻¹) ^ Kc * δ ^ u) := by
              field_simp; try ring
            rw [hrw]
            exact mul_le_mul_of_nonneg_left h1 (by positivity)
          calc 4 * C₀ * calcConst ψ * K' * (δ ^ (2 * u))⁻¹
              ≤ Cc / (2 * C₀) * (δ ^ (2 * u))⁻¹ :=
                mul_le_mul_of_nonneg_right hcc2 (by positivity)
            _ ≤ Cc / 2 * (δ⁻¹) ^ Kc / N * (δ ^ u * (N : ℝ) / C₀) := h2
        calc 4 * C₀ * calcConst ψ * K' * (δ ^ (2 * u))⁻¹
            ≤ Cc / 2 * (δ⁻¹) ^ Kc / N * (δ ^ u * (N : ℝ) / C₀) := hstep
          _ ≤ Cc / 2 * (δ⁻¹) ^ Kc / N * (N' : ℝ) := mul_le_mul_of_nonneg_left hN'ge (by positivity)
    have hεN'inv : (ε * (N' : ℝ))⁻¹ ≤ δ ^ (2 * u) / (4 * C₀ * calcConst ψ * K') := by
      have hXpos : 0 < δ ^ (2 * u) / (4 * C₀ * calcConst ψ * K') :=
        div_pos (pow_pos hδpos _) hfour
      have h1 : (δ ^ (2 * u) / (4 * C₀ * calcConst ψ * K'))⁻¹ ≤ ε * (N' : ℝ) := by
        rw [inv_div, div_eq_mul_inv]
        exact hεN'ge
      have h2 : 0 < ε * (N' : ℝ) := mul_pos hεpos (by exact_mod_cast hN'1)
      calc (ε * (N' : ℝ))⁻¹
          ≤ ((δ ^ (2 * u) / (4 * C₀ * calcConst ψ * K'))⁻¹)⁻¹ :=
            (inv_le_inv₀ h2 (inv_pos.mpr hXpos)).mpr h1
        _ = δ ^ (2 * u) / (4 * C₀ * calcConst ψ * K') := inv_inv _
    -- the smoothed progression and the weighted dual function
    let w : ℤ → ℂ := lipWeight ψ ε N'
    let F : ℤ → ℂ := smoothOp w G (q : ℤ)
    have hwsum : Summable (fun m : ℤ => ‖w m‖) := lipWeightSummable ψ hεpos hεle1 hN'1
    have hFbound := lipSmoothOpTsumLe hwsum hGsum (q : ℤ)
    have hFone : (∑' x : ℤ, ‖F x‖) ≤ Kw * (2 * (MW : ℝ) + 1) := by
      have h2 : (∑' m : ℤ, ‖w m‖) ≤ Kw := hKw hεpos hεle1 hN'1
      have h1 : (0 : ℝ) ≤ ∑' x : ℤ, ‖G x‖ := tsum_nonneg fun _ => norm_nonneg _
      have h0 : (0 : ℝ) ≤ ∑' m : ℤ, ‖w m‖ := tsum_nonneg fun _ => norm_nonneg _
      calc (∑' x : ℤ, ‖F x‖) ≤ (∑' m : ℤ, ‖w m‖) * (∑' x : ℤ, ‖G x‖) := hFbound.2
        _ ≤ Kw * (∑' x : ℤ, ‖G x‖) := mul_le_mul_of_nonneg_right h2 h1
        _ ≤ Kw * (2 * (MW : ℝ) + 1) := mul_le_mul_of_nonneg_left hGone hKwpos.le
    have hFsup : ∀ x : ℤ, ‖F x‖ ≤ Kw := by
      intro x
      have hsumm : Summable (fun m : ℤ => ‖w m * G (x - (q : ℤ) * m)‖) := by
        refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hwsum
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hGbd _)
      calc ‖F x‖ = ‖∑' m : ℤ, w m * G (x - (q : ℤ) * m)‖ := rfl
        _ ≤ ∑' m : ℤ, ‖w m * G (x - (q : ℤ) * m)‖ := norm_tsum_le_tsum_norm hsumm
        _ ≤ ∑' m : ℤ, ‖w m‖ := by
            refine Real.tsum_le_of_sum_le (fun m => norm_nonneg _) (fun s => ?_)
            refine le_trans (Finset.sum_le_sum (fun m _ => ?_))
              (hwsum.sum_le_tsum s (fun m _ => norm_nonneg _))
            rw [norm_mul]
            exact mul_le_of_le_one_right (norm_nonneg _) (hGbd _)
        _ ≤ Kw := hKw hεpos hεle1 hN'1
    -- the pointwise smoothing error
    have hpt : ∀ x : ℤ, ‖(∑' m : ℤ, w m * f (x + (q : ℤ) * (m : ℤ))) - Aavg x‖
        ≤ calcConst ψ * (ε ^ 10 + (ε * (N' : ℝ))⁻¹) := by
      intro x
      have hsm : (∑' m : ℤ, w m * f (x + (q : ℤ) * (m : ℤ)))
          = ε * ∑' m : ℤ, ((N' : ℝ)⁻¹ * ∑ m' ∈ Finset.Icc 1 N',
              (ψ : ℝ → ℂ) (ε * ((m : ℝ) - (m' : ℝ)))) * f (x + (q : ℤ) * (m : ℤ)) := by
        rw [← tsum_mul_left]
        refine tsum_congr fun m => ?_
        simp only [w, lipWeight]
        ring
      rw [hsm]
      simpa only [norm_sub_rev] using
        averaging_smooth ψ hψint hεpos hεle1 hN'1 f hfb (q : ℤ) x
    -- the dual correlation lower bound
    let Ψ : ℤ → ℂ := fun x => ∑' m : ℤ, w m * f (x + (q : ℤ) * (m : ℤ))
    have hFcorr : δ ^ u * (N : ℝ) ^ P.natDegree / (4 * C₀) ≤ ‖bilinPair f F‖ := by
      have hFpair : bilinPair f F = ∑' x : ℤ, G x * Ψ x := by
        show bilinPair f (fun y => ∑' m : ℤ, w m * G (y - (q : ℤ) * m)) = _
        exact bilinPair_smoothOp' (FinSupp.of_supportIn hfs) (FinSupp.of_supportIn hGsupp)
          (by positivity : (q : ℤ) ≠ 0) w
      have hsumm1 : Summable (fun x : ℤ => G x * Aavg x) :=
        summable_of_ne_finset_zero fun x hx => by rw [hGzero x hx, zero_mul]
      have hsumm2 : Summable (fun x : ℤ => G x * (Ψ x - Aavg x)) :=
        summable_of_ne_finset_zero fun x hx => by rw [hGzero x hx, zero_mul]
      have hsplit : (∑' x : ℤ, G x * Ψ x)
          = (∑' x : ℤ, G x * Aavg x) + ∑' x : ℤ, G x * (Ψ x - Aavg x) := by
        rw [← Summable.tsum_add hsumm1 hsumm2]
        exact tsum_congr fun x => by ring
      have hellA : (∑' x : ℤ, G x * Aavg x) = ((∑ y ∈ W, ‖Aavg y‖ : ℝ) : ℂ) := hGpairW
      have hKpt : calcConst ψ * (ε ^ 10 + (ε * (N' : ℝ))⁻¹) ≤ δ ^ (2 * u) / (2 * C₀ * K') := by
        have h5 : δ ^ (2*u) / (4 * C₀ * calcConst ψ * K') + δ ^ (2*u) / (4 * C₀ * calcConst ψ * K')
            = δ ^ (2*u) / (2 * C₀ * calcConst ψ * K') := by
          field_simp
          ring
        calc calcConst ψ * (ε ^ 10 + (ε * (N' : ℝ))⁻¹)
            ≤ calcConst ψ * (δ^(2*u)/(4*C₀*calcConst ψ*K') + δ^(2*u)/(4*C₀*calcConst ψ*K')) := by
              have h6 := hε10
              have h7 := hεN'inv
              nlinarith only [h6, h7, (calcConst_pos ψ).le]
          _ = δ ^ (2*u) / (2 * C₀ * K') := by
              rw [h5]
              field_simp [(calcConst_pos ψ).ne']
              try ring
      have herr : ‖∑' x : ℤ, G x * (Ψ x - Aavg x)‖
          ≤ δ ^ u * (N : ℝ) ^ P.natDegree / (2 * C₀) := by
        have hsumm3 : Summable (fun x : ℤ => ‖G x * (Ψ x - Aavg x)‖) :=
          summable_of_ne_finset_zero fun x hx => by rw [hGzero x hx, zero_mul, norm_zero]
        have hnorm : ‖∑' x : ℤ, G x * (Ψ x - Aavg x)‖
            ≤ ∑' x : ℤ, ‖G x * (Ψ x - Aavg x)‖ :=
          norm_tsum_le_tsum_norm (summable_of_ne_finset_zero fun x hx => by
            rw [hGzero x hx, zero_mul, norm_zero])
        have hstep : ∑' x : ℤ, ‖G x * (Ψ x - Aavg x)‖
            ≤ ∑' x : ℤ, ‖G x‖ * (calcConst ψ * (ε ^ 10 + (ε*(N':ℝ))⁻¹)) := by
          rw [tsum_eq_sum (s := W)
                (fun x hx => by rw [hGzero x hx, zero_mul, norm_zero]),
              tsum_eq_sum (s := W)
                (fun x hx => by rw [hGzero x hx, norm_zero, zero_mul])]
          exact Finset.sum_le_sum fun x _ => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hpt x) (norm_nonneg _)
        have hstep2 : ∑' x : ℤ, ‖G x‖ * (calcConst ψ * (ε ^ 10 + (ε*(N':ℝ))⁻¹))
            ≤ δ ^ u * (N : ℝ) ^ P.natDegree / (2 * C₀) := by
          have h2 : ∑' x : ℤ, ‖G x‖ * (calcConst ψ * (ε ^ 10 + (ε*(N':ℝ))⁻¹))
              = calcConst ψ * (ε ^ 10 + (ε*(N':ℝ))⁻¹) * ellOne G := by
            rw [ellOne, ← tsum_mul_left]
            exact tsum_congr fun x => by ring
          rw [h2]
          have hKpt0 : 0 ≤ calcConst ψ * (ε ^ 10 + (ε * (N' : ℝ))⁻¹) :=
            mul_nonneg (calcConst_pos ψ).le (by positivity)
          have h3 : calcConst ψ * (ε ^ 10 + (ε*(N':ℝ))⁻¹) * ellOne G
              ≤ calcConst ψ * (ε ^ 10 + (ε*(N':ℝ))⁻¹) * (2 * (MW:ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hGone hKpt0
          refine le_trans h3 ?_
          calc calcConst ψ * (ε ^ 10 + (ε*(N':ℝ))⁻¹) * (2 * (MW:ℝ) + 1)
              ≤ (δ ^ (2*u) / (2*C₀*K')) * (2 * (MW:ℝ) + 1) :=
                mul_le_mul_of_nonneg_right hKpt (by positivity)
            _ ≤ (δ ^ (2*u) / (2*C₀*K')) * (K' * (δ⁻¹)^u * (N:ℝ)^P.natDegree) :=
                mul_le_mul_of_nonneg_left hMdW (by positivity)
            _ = δ ^ u * (N:ℝ)^P.natDegree / (2*C₀) := by
                rw [inv_pow]
                field_simp
                ring
        exact le_trans hnorm (le_trans hstep hstep2)
      rw [hFpair, hsplit, hellA]
      have h2 : (∑ y ∈ W, ‖Aavg y‖) - ‖∑' x : ℤ, G x * (Ψ x - Aavg x)‖
          ≤ ‖(((∑ y ∈ W, ‖Aavg y‖ : ℝ)) : ℂ) + ∑' x : ℤ, G x * (Ψ x - Aavg x)‖ := by
        have h3 : ‖(((∑ y ∈ W, ‖Aavg y‖ : ℝ)) : ℂ)‖ = (∑ y ∈ W, ‖Aavg y‖) := by
          rw [Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun y _ => norm_nonneg _)]
        have h4 := norm_add_le ((((∑ y ∈ W, ‖Aavg y‖ : ℝ)) : ℂ) + (∑' x : ℤ, G x * (Ψ x - Aavg x)))
          (-(∑' x : ℤ, G x * (Ψ x - Aavg x)))
        rw [add_neg_cancel_right, norm_neg] at h4
        linarith only [h3, h4]
      have h8 : δ ^ u * (N : ℝ) ^ P.natDegree / C₀
          - δ ^ u * (N : ℝ) ^ P.natDegree / (4 * C₀)
          - δ ^ u * (N : ℝ) ^ P.natDegree / (2 * C₀)
          = δ ^ u * (N : ℝ) ^ P.natDegree / (4 * C₀) := by
        field_simp
        ring
      linarith [hAle, hAloss, h4q, herr, h2, h8]

    -- the dyadic scales and the Fourier support
    obtain ⟨l, hl1, hl2⟩ := lipExistsPowTwoGe hqpos
    obtain ⟨k, hk1, hk2⟩ := lipExistsZpowTwo hεpos
    have hQl : q ≤ 2 ^ l := by exact_mod_cast hl1
    have hl3 : (2 : ℝ) ^ l ≤ Cc * (δ⁻¹) ^ Kc := by
      have hmax : max (q : ℝ) 1 = (q : ℝ) := max_eq_left (by exact_mod_cast hq1)
      have h1 : (2 : ℝ) ^ l ≤ 2 * (q : ℝ) := by rw [hmax] at hl2; linarith [hl2]
      have h2 : 2 * (q : ℝ) ≤ 2 * (C₀ * δ⁻¹ ^ K₀) := by linarith [hqle]
      have h3 : 2 * (C₀ * δ⁻¹ ^ K₀) ≤ Cc * (δ⁻¹) ^ Kc := by
        calc 2 * (C₀ * δ⁻¹ ^ K₀) = (2 * C₀) * δ⁻¹ ^ K₀ := by ring
          _ ≤ (2 * C₀) * (δ⁻¹) ^ u := mul_le_mul_of_nonneg_left hδinv_le (by positivity)
          _ ≤ Cc * (δ⁻¹) ^ u := mul_le_mul_of_nonneg_right hCc2C₀ (by positivity)
          _ ≤ Cc * (δ⁻¹) ^ Kc :=
              mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD1 hKcu) hCcpos.le
      linarith
    have hk3 : (2 : ℝ) ^ k ≤ Cc * (δ⁻¹) ^ Kc / N := by
      have h2 : 2 * ε ≤ Cc * (δ⁻¹) ^ Kc / N := by
        calc 2 * ε ≤ 2 * (Cc / 2 * (δ⁻¹) ^ Kc / N) := by linarith [hεle2]
          _ = Cc * (δ⁻¹) ^ Kc / N := by ring
      linarith [hk2]
    have hsupp : FourierSupportIn F (majorArc ρ l k) := by
      intro ξ hξ
      obtain ⟨x, hx⟩ : ∃ x : ℝ, ((x : ℝ) : FreqCircle) = ξ :=
        ⟨(AddCircle.equivIco (1 : ℝ) 0 ξ).val, AddCircle.coe_equivIco⟩
      have hfar : ∀ n : ℤ, ε < |(q : ℝ) * x - (n : ℝ)| := by
        intro n
        by_contra hcon
        have hcon' : |(q : ℝ) * x - (n : ℝ)| ≤ ε := not_lt.mp hcon
        have hkq : ε ≤ (q : ℝ) * (2 : ℝ) ^ k := by
          calc ε ≤ (2 : ℝ) ^ k := hk1
            _ ≤ (q : ℝ) * (2 : ℝ) ^ k := by
                have hq1' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
                have h2k : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
                nlinarith only [hq1', h2k, hk1]
        have hmem := lipMemMajorArcOfClose hρpos hρle hq1 hQl hcon' hkq
        exact hξ (by rwa [← hx])
      have hzsmul : ((q : ℤ) • ξ) = (((q : ℝ) * x : ℝ) : FreqCircle) := by
        rw [← hx, ← AddCircle.coe_zsmul]
        congr 1
        rw [zsmul_eq_mul]; push_cast; ring
      have hvan : (ε : ℂ) * ∑' u : ℤ,
          ((ψ (ε * (u : ℝ)) : ℂ) * (fourier (-u) ((q : ℤ) • ξ) : ℂ)) = 0 := by
        rw [hzsmul]
        exact lipPoissonVanish ψ hψsupp hεpos hfar
      calc ZFourier F ξ
          = ZFourier G ξ * (∑' m : ℤ, w m * (fourier (-((q : ℤ) * m)) ξ : ℂ)) := by
            rw [show F = smoothOp w G (q : ℤ) from rfl,
              lipZFourierSmoothOp hwsum hGsum (q : ℤ) ξ]
        _ = ZFourier G ξ * ((N' : ℝ)⁻¹ * (∑ m' ∈ Finset.Icc 1 N',
              (fourier (-((q : ℤ) * (m' : ℤ))) ξ : ℂ)) * ((ε : ℂ) * ∑' u : ℤ,
              (ψ (ε * (u : ℝ)) : ℂ) * (fourier (-u) ((q : ℤ) • ξ) : ℂ))) := by
            rw [lipWeightMultiplierFactor ψ hεpos hN'1 (q : ℤ) ξ]
        _ = 0 := by rw [hvan]; ring
    -- ### the tail of `F` outside the ball of radius `A N^d`
    have hshell : ∀ m : ℤ, (∑' y : ℤ, (if D < (y + (q : ℤ) * m).natAbs then ‖G y‖ else 0))
        ≤ (q : ℝ) * max 0 (|(m : ℝ)| - (N' : ℝ)) := by
      intro m
      refine shellLeWindow ?_ ?_ hGbd
      · have h1 : ((q : ℤ) * (N' : ℤ)) = ((q * N' : ℕ) : ℤ) := by push_cast; ring
        rw [h1]
        exact_mod_cast hqN'nat
      · intro y hy
        have h1 : y.natAbs ≤ MW := cbWin_supportIn_natAbs_le hGsupp hy
        have h2 : |(y : ℤ)| ≤ (MW : ℤ) := by
          rw [← Int.natCast_natAbs]
          exact_mod_cast h1
        have h3 : -((MW : ℤ)) ≤ y ∧ y ≤ (MW : ℤ) := abs_le.mp h2
        rw [hMWcast] at h3
        exact ⟨by linarith [h3.1], h3.2⟩
    have hmom : (∑' m : ℤ, ‖w m‖ * max 0 (|(m : ℝ)| - (N' : ℝ))) ≤ Cm / ε :=
      hCm hεpos hεle1 hN'1
    have hCmSumm : Summable (fun m : ℤ => ‖w m‖ * max 0 (|(m : ℝ)| - (N' : ℝ))) := by
      obtain ⟨C, _hCpos, hCpt⟩ := lipWeightAbsMomentPointwise ψ
      refine Summable.of_nonneg_of_le
        (f := fun m : ℤ => C * (N' : ℝ)⁻¹ * ∑ y ∈ Finset.Icc 1 N',
          ε * jbDecay 12 (ε * ((m : ℝ) - (y : ℝ))) * |(m : ℝ) - (y : ℝ)|)
        (g := fun m : ℤ => ‖w m‖ * max 0 (|(m : ℝ)| - (N' : ℝ)))
        (fun m => mul_nonneg (norm_nonneg _) (le_max_left 0 _))
        (fun m => hCpt hεpos hεle1 hN'1 m) ?_
      exact (summable_finset_sum (Finset.Icc 1 N')
        (fun y _ => (summable_tsum_eps_jbDecay_weighted_shift (ε := ε) hεpos (y : ℤ)).1)).mul_left
          (C * (N' : ℝ)⁻¹)
    have hTailSum : (∑' m : ℤ, ‖w m‖ * (∑' y : ℤ,
          (if D < (y + (q : ℤ) * m).natAbs then ‖G y‖ else 0)))
        ≤ q * (Cm / ε) := by
      refine Real.tsum_le_of_sum_le (fun m => mul_nonneg (norm_nonneg _) ?_) (fun s => ?_)
      · exact tsum_nonneg fun y => by split <;> positivity
      · calc ∑ m ∈ s, ‖w m‖ * (∑' y : ℤ, (if D < (y + (q : ℤ) * m).natAbs then ‖G y‖ else 0))
            ≤ ∑ m ∈ s, ‖w m‖ * ((q : ℝ) * max 0 (|(m : ℝ)| - (N' : ℝ))) :=
              Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hshell m) (norm_nonneg _)
          _ = (q : ℝ) * ∑ m ∈ s, ‖w m‖ * max 0 (|(m : ℝ)| - (N' : ℝ)) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun m _ => by ring
          _ ≤ (q : ℝ) * (Cm / ε) :=
              mul_le_mul_of_nonneg_left
                (le_trans (Summable.sum_le_tsum s
                  (fun m _ => mul_nonneg (norm_nonneg _) (le_max_left 0 _)) hCmSumm) hmom)
                hqpos.le
    have hα1 : 8 * C₀ ^ 2 * Cm * c₁ ≤ Cc ^ P.natDegree := by
      have h1 : (1 : ℝ) ≤ Cc := by linarith only [hCc7]
      calc 8 * C₀ ^ 2 * Cm * c₁ ≤ 16 * C₀ ^ 2 * Cm * c₁ := by
              have hnn : (0 : ℝ) ≤ C₀ ^ 2 * Cm * c₁ :=
                mul_nonneg (mul_nonneg (sq_nonneg C₀) hCmpos.le) hc₁pos.le
              linarith only [hnn]
        _ ≤ Cc := h16C₀₂Cmc₁
        _ = Cc ^ 1 := (pow_one Cc).symm
        _ ≤ Cc ^ P.natDegree := pow_le_pow_right₀ h1 (by omega)
    have hA1q : K₀ + 2 * (u : ℝ) ≤ Kc * (P.natDegree : ℝ) := by
      have h1 : K₀ + 2 * (u : ℝ) ≤ 3 * (u : ℝ) := by linarith only [hu_ge]
      have h2 : (3 : ℝ) * (u : ℝ) = ((3 * u : ℕ) : ℝ) := by push_cast; ring
      have h3 : ((3 * u : ℕ) : ℝ) ≤ (Kc : ℝ) := by exact_mod_cast hKc3u
      have h4 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by
        rw [Nat.one_le_cast]; omega
      nlinarith only [h1, h2, h3, h4, hKcpos]
    have hdel : Cc / (N : ℝ) ≤ δ ^ u := by
      have h1 : Cc / (N : ℝ) ≤ δ ^ (u : ℝ) :=
        cbWin_rpow_low hCcpos hδpos hδle hcaseBrpow (by exact_mod_cast hKcu)
      simpa only [Real.rpow_natCast] using h1
    have hTailSmall : (∑' m : ℤ, ‖w m‖ * (∑' y : ℤ,
          (if D < (y + (q : ℤ) * m).natAbs then ‖G y‖ else 0)))
        ≤ δ ^ u * (N : ℝ) ^ P.natDegree / (8 * C₀) := by
      refine le_trans hTailSum ?_
      rcases le_total (δ ^ mr / c₁) (Cc / 2 * (δ⁻¹) ^ Kc / N) with hle | hle
      · have hεv : ε = δ ^ u / c₁ := by
          show min (δ ^ mr / c₁) (Cc / 2 * (δ⁻¹) ^ Kc / N) = δ ^ u / c₁
          rw [min_eq_left hle]
        rw [hεv]
        exact tailSub1 hδpos hδle hCc7 hC₀pos hCmpos hc₁pos hN1 (by omega) hcaseBrpow hα1 hA1q hqle
      · have hεv : ε = Cc / 2 * (δ⁻¹) ^ Kc / N := by
          show min (δ ^ mr / c₁) (Cc / 2 * (δ⁻¹) ^ Kc / N)
            = Cc / 2 * (δ⁻¹) ^ Kc / N
          rw [min_eq_right hle]
        rw [hεv]
        exact tailSub2 hδpos hδle hCc7 hC₀pos hCmpos hCcC₀ hN1 (by omega) h16C₀Cm hdel hqle hKcK₀
    have hTailOp : (∑' x : ℤ, (if D < x.natAbs then ‖F x‖ else 0))
        ≤ ∑' m : ℤ, ‖w m‖ * (∑' y : ℤ,
            (if D < (y + (q : ℤ) * m).natAbs then ‖G y‖ else 0)) := by
      have h := smoothOpTailLe hwsum hGsum (q : ℤ) D
      simpa only [F] using h
    -- ### the normalisation of `F`
    set lam : ℝ := 4 * C₀ * δ ^ (Kc - u) with hlamdef
    have hlampos : 0 < lam := by rw [hlamdef]; positivity
    have hlamnorm : ‖((lam : ℝ) : ℂ)‖ = lam := by
      rw [Complex.norm_real, Real.norm_of_nonneg hlampos.le]
    have hδsplit : δ ^ (Kc - u) * δ ^ u = δ ^ Kc := by
      rw [← pow_add, show Kc - u + u = Kc by omega]
    refine ⟨(((lam : ℝ)) : ℂ) • F, l, k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      show ‖(((lam : ℝ)) : ℂ) • F x‖ ≤ Cc * (δ⁻¹) ^ Kc
      rw [norm_smul, hlamnorm]
      have h1 : lam * Kw ≤ Cc * (δ⁻¹) ^ Kc := by
        have h2 : δ ^ (Kc - u) ≤ 1 := pow_le_one₀ hδpos.le hδle
        have h3 : (1 : ℝ) ≤ (δ⁻¹) ^ Kc := one_le_pow₀ hD1
        rw [hlamdef]
        calc 4 * C₀ * δ ^ (Kc - u) * Kw = 4 * C₀ * Kw * δ ^ (Kc - u) := by ring
          _ ≤ 4 * C₀ * Kw * 1 := mul_le_mul_of_nonneg_left h2
              (mul_nonneg (mul_nonneg (by norm_num) hC₀pos.le) hKwpos.le)
          _ = 4 * C₀ * Kw := by ring
          _ ≤ Cc := h4C₀Kw
          _ = Cc * 1 := by ring
          _ ≤ Cc * (δ⁻¹) ^ Kc := mul_le_mul_of_nonneg_left h3 hCcpos.le
      exact le_trans (mul_le_mul_of_nonneg_left (hFsup x) hlampos.le) h1
    · have h1 : Summable (fun x : ℤ => ‖F x‖) := (lipSmoothOpTsumLe hwsum hGsum (q : ℤ)).1
      refine (h1.mul_left lam).congr (fun x => ?_)
      show lam * ‖F x‖ = ‖(((lam : ℝ)) : ℂ) * F x‖
      rw [norm_mul, hlamnorm]
    · show (∑' x : ℤ, ‖(((lam : ℝ)) : ℂ) • F x‖)
          ≤ Cc * (δ⁻¹) ^ Kc * (N : ℝ) ^ P.natDegree
      have h1 : (∑' x : ℤ, ‖(((lam : ℝ)) : ℂ) • F x‖) = lam * ∑' x : ℤ, ‖F x‖ := by
        rw [← tsum_mul_left]
        exact tsum_congr fun x => by rw [norm_smul, hlamnorm]
      rw [h1]
      have h4 : δ ^ (Kc - u) * (δ⁻¹) ^ u ≤ 1 := by
        have h5 : δ ^ (Kc - u) * (δ⁻¹) ^ u = δ ^ (Kc - 2 * u) := by
          rw [show Kc - u = (Kc - 2 * u) + u by omega, pow_add, inv_pow]
          rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hδpos.ne'), mul_one]
        rw [h5]
        exact pow_le_one₀ hδpos.le hδle
      have h6 : (1 : ℝ) ≤ (δ⁻¹) ^ Kc := one_le_pow₀ hD1
      have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ P.natDegree := by positivity
      have h7 : lam * (Kw * (2 * (MW : ℝ) + 1))
          ≤ Cc * (δ⁻¹) ^ Kc * (N : ℝ) ^ P.natDegree := by
        have hMdW' : Kw * (2 * (MW : ℝ) + 1)
            ≤ Kw * (K' * (δ⁻¹) ^ u * (N : ℝ) ^ P.natDegree) :=
          mul_le_mul_of_nonneg_left hMdW hKwpos.le
        rw [hlamdef]
        calc 4 * C₀ * δ ^ (Kc - u) * (Kw * (2 * (MW : ℝ) + 1))
            ≤ 4 * C₀ * δ ^ (Kc - u)
                * (Kw * (K' * (δ⁻¹) ^ u * (N : ℝ) ^ P.natDegree)) :=
              mul_le_mul_of_nonneg_left hMdW' (by positivity)
          _ = (4 * C₀ * Kw * K') * (δ ^ (Kc - u) * (δ⁻¹) ^ u)
                * (N : ℝ) ^ P.natDegree := by ring
          _ ≤ (4 * C₀ * Kw * K') * 1 * (N : ℝ) ^ P.natDegree :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4
                (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₀pos.le) hKwpos.le)
                  hK'pos.le)) hN0
          _ = 4 * C₀ * Kw * K' * (N : ℝ) ^ P.natDegree := by ring
          _ ≤ Cc * (N : ℝ) ^ P.natDegree := mul_le_mul_of_nonneg_right h4C₀KwK' hN0
          _ ≤ Cc * (δ⁻¹) ^ Kc * (N : ℝ) ^ P.natDegree :=
              mul_le_mul_of_nonneg_right
                (by calc Cc = Cc * 1 := by ring
                      _ ≤ Cc * (δ⁻¹) ^ Kc := mul_le_mul_of_nonneg_left h6 hCcpos.le) hN0
      calc lam * (∑' x : ℤ, ‖F x‖) ≤ lam * (Kw * (2 * (MW : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hFone hlampos.le
        _ ≤ Cc * (δ⁻¹) ^ Kc * (N : ℝ) ^ P.natDegree := h7
    · -- 4. the spatial tail
      rw [show (∑' x : ℤ, (if A * (N : ℝ) ^ P.natDegree < |(x : ℝ)|
              then ‖((((lam : ℝ)) : ℂ) • F) x‖ else 0))
            = lam * (∑' x : ℤ, (if D < x.natAbs then ‖F x‖ else 0)) from ?_]
      · calc lam * (∑' x : ℤ, (if D < x.natAbs then ‖F x‖ else 0))
            ≤ lam * (∑' m : ℤ, ‖w m‖ * (∑' y : ℤ,
                (if D < (y + (q : ℤ) * m).natAbs then ‖G y‖ else 0))) :=
              mul_le_mul_of_nonneg_left hTailOp hlampos.le
          _ ≤ lam * (δ ^ u * (N : ℝ) ^ P.natDegree / (8 * C₀)) :=
              mul_le_mul_of_nonneg_left hTailSmall hlampos.le
          _ = δ ^ Kc * (N : ℝ) ^ P.natDegree / 2 := by
              rw [hlamdef]
              field_simp
              rw [show (4 : ℝ) * δ ^ (Kc - u) * δ ^ u * 2 = 8 * δ ^ Kc by
                calc (4 : ℝ) * δ ^ (Kc - u) * δ ^ u * 2
                    = 8 * (δ ^ (Kc - u) * δ ^ u) := by ring
                  _ = 8 * δ ^ Kc := by rw [hδsplit]]
      · rw [← tsum_mul_left]
        refine tsum_congr fun x => ?_
        have hiff : (A * (N : ℝ) ^ P.natDegree < |(x : ℝ)|) ↔ D < x.natAbs := by
          constructor
          · intro hx
            exact cbWin_lt_natAbs hA0 (by simpa [hDdef] using hx)
          · intro hx
            have h4 : (D + 1 : ℕ) ≤ x.natAbs := by omega
            have h5 : (D : ℝ) + 1 ≤ |(x : ℝ)| := by
              have h6 : (((D + 1 : ℕ) : ℝ)) ≤ ((x.natAbs : ℕ) : ℝ) := by exact_mod_cast h4
              rw [cbWin_natAbs_cast_real x] at h6
              push_cast at h6
              linarith
            have h2 : A * (N : ℝ) ^ P.natDegree < (D : ℝ) + 1 := by
              rw [hDdef]
              exact Nat.lt_floor_add_one (A * (N : ℝ) ^ P.natDegree)
            linarith
        by_cases hx : D < x.natAbs
        · rw [if_pos (hiff.mpr hx), if_pos hx, Pi.smul_apply, norm_smul, hlamnorm]
        · rw [if_neg (fun h => hx (hiff.mp h)), if_neg hx, mul_zero]
    · intro ξ hξ
      rw [ZFourier_smul, hsupp ξ hξ, mul_zero]
    · exact hl3
    · exact hk3
    · show δ ^ Kc * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair f ((((lam : ℝ)) : ℂ) • F)‖
      rw [lipBilinPairSmul, norm_mul, hlamnorm]
      have h1 : δ ^ Kc * (N : ℝ) ^ P.natDegree
          ≤ lam * (δ ^ u * (N : ℝ) ^ P.natDegree / (4 * C₀)) := by
        have hR : lam * (δ ^ u * (N : ℝ) ^ P.natDegree / (4 * C₀))
            = δ ^ Kc * (N : ℝ) ^ P.natDegree := by
          rw [hlamdef]
          calc 4 * C₀ * δ ^ (Kc - u) * (δ ^ u * (N : ℝ) ^ P.natDegree / (4 * C₀))
              = δ ^ (Kc - u) * δ ^ u * (N : ℝ) ^ P.natDegree := by
                field_simp; try ring
            _ = δ ^ Kc * (N : ℝ) ^ P.natDegree := by rw [hδsplit]
        rw [hR]
      calc δ ^ Kc * (N : ℝ) ^ P.natDegree
          ≤ lam * (δ ^ u * (N : ℝ) ^ P.natDegree / (4 * C₀)) := h1
        _ ≤ lam * ‖bilinPair f F‖ := mul_le_mul_of_nonneg_left hFcorr hlampos.le


end Work.KMTAreas.A4
