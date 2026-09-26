import Mathlib
import Submission.Work.Asymptotics.Kaxis_tile_aux
import Submission.Work.Asymptotics.Tile.tile_divisor_lower
import Submission.Work.Asymptotics.Xi8_eq
import Submission.Work.Asymptotics.Xi24_eq
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Asymptotics.KPlusFunnel.Atoms
import Submission.Work.Asymptotics.KPlus_slash_bound_funnel
import Submission.Work.Kernels.KernelFacts.KPlus_T2

set_option maxHeartbeats 1600000

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane Manifold

noncomputable section

open Work.Kernels

/-! ## Elementary glue -/

private lemma rpow_split {s : ℝ} (hs : 0 < s) (N M : ℝ) : s ^ (N + M) = s ^ N * s ^ M :=
  Real.rpow_add hs N M

private lemma rpow_succ {s : ℝ} (hs : 0 < s) (N : ℝ) : s ^ (N + 1) = s ^ N * s := by
  rw [rpow_split hs, Real.rpow_one]

private lemma exp_split {t : ℝ} (c d : ℝ) :
    Real.exp ((c + d) * (Real.pi / t))
      = Real.exp (c * (Real.pi / t)) * Real.exp (d * (Real.pi / t)) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- Product of two bounds (no exponential factors): the shape is inferred from the inputs. -/
private lemma mul_bound0 {u v : ℂ} {s : ℝ} (hs : 1 ≤ s) {A B N M : ℝ}
    (hu : ‖u‖ ≤ A * s ^ N) (hv : ‖v‖ ≤ B * s ^ M) : ‖u * v‖ ≤ A * B * s ^ (N + M) := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have h2 : (A * s ^ N) * (B * s ^ M) = A * B * s ^ (N + M) := by
    rw [rpow_split hs0]; ring
  rw [norm_mul]
  calc ‖u‖ * ‖v‖ ≤ (A * s ^ N) * (B * s ^ M) :=
        mul_le_mul hu hv (norm_nonneg _) (le_trans (norm_nonneg _) hu)
    _ = A * B * s ^ (N + M) := h2

/-- Product of two bounds with exponential factors `e^{c π/t}`. -/
private lemma mul_bound {u v : ℂ} {s : ℝ} (hs : 1 ≤ s) {A B N M c d t : ℝ}
    (hu : ‖u‖ ≤ A * s ^ N * Real.exp (c * (Real.pi / t)))
    (hv : ‖v‖ ≤ B * s ^ M * Real.exp (d * (Real.pi / t))) :
    ‖u * v‖ ≤ A * B * s ^ (N + M) * Real.exp ((c + d) * (Real.pi / t)) := by
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  have hA0 : 0 ≤ A * s ^ N * Real.exp (c * (Real.pi / t)) := le_trans (norm_nonneg _) hu
  have h2 : (A * s ^ N * Real.exp (c * (Real.pi / t))) * (B * s ^ M * Real.exp (d * (Real.pi / t)))
      = A * B * s ^ (N + M) * Real.exp ((c + d) * (Real.pi / t)) := by
    rw [rpow_split hs0, exp_split]
    ring
  rw [norm_mul]
  calc ‖u‖ * ‖v‖
      ≤ (A * s ^ N * Real.exp (c * (Real.pi / t))) * (B * s ^ M * Real.exp (d * (Real.pi / t))) :=
        mul_le_mul hu hv (norm_nonneg _) hA0
    _ = A * B * s ^ (N + M) * Real.exp ((c + d) * (Real.pi / t)) := h2

/-- `T`-invariance suffices for translation by `±1`. -/
private lemma vadd_ne_of_vadd_one {F : UpperHalfPlane → ℂ}
    (h : ∀ τ, F ((1 : ℝ) +ᵥ τ) = F τ) (τ : UpperHalfPlane) {n : ℤ} (hn : n = 1 ∨ n = -1) :
    F ((n : ℝ) +ᵥ τ) = F τ := by
  have hcast : (n : ℝ) = 1 ∨ (n : ℝ) = -1 := by
    rcases hn with h' | h' <;> simp [h']
  rcases hcast with hh | hh
  · rw [hh]; exact h τ
  · rw [hh]
    have h1 := h ((-1 : ℝ) +ᵥ τ)
    have h2 : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ := by rw [← add_vadd, add_neg_cancel, zero_vadd]
    rw [h2] at h1
    exact h1.symm

private lemma norm_int_one {n : ℤ} (hn : n = 1 ∨ n = -1) : ‖(((n : ℝ)) : ℂ)‖ = 1 := by
  have hcast : (n : ℝ) = 1 ∨ (n : ℝ) = -1 := by
    rcases hn with h' | h' <;> simp [h']
  rcases hcast with hh | hh <;> rw [hh] <;> norm_num

/-- `(n : ℝ) + w` has norm at most `2 * scale w` on the tiles. -/
private lemma coe_vadd_norm_le {w : UpperHalfPlane} {n : ℤ} (hn : n = 1 ∨ n = -1) {s : ℝ}
    (hs : s = scale w) : ‖(n : ℝ) + (w : ℂ)‖ ≤ 2 * s := by
  have h1 : ‖(n : ℝ) + (w : ℂ)‖ ≤ ‖(((n : ℝ)) : ℂ)‖ + ‖(w : ℂ)‖ := norm_add_le _ _
  rw [norm_int_one hn] at h1
  have h2 : ‖(w : ℂ)‖ ≤ s := by rw [hs]; exact Work.Kernels.coe_norm_le_scale w
  have h3 : (1 : ℝ) ≤ s := by rw [hs]; exact Work.Kernels.one_le_scale w
  linarith

private lemma two_pi_imS_le {w : UpperHalfPlane} (hw : w ∈ Work.Asymptotics.KEpsilon)
    {t : ℝ} (ht : 0 < t) (htle : t ≤ w.im / 2) :
    (2 * Real.pi) * (ModularGroup.S • w).im ≤ Real.pi / t := by
  have h4 : (ModularGroup.S • w).im ≤ 1 / 2 / t := Work.Asymptotics.tile_im_S_le hw ht htle
  rw [div_eq_mul_inv] at h4
  rw [div_eq_mul_inv]
  nlinarith [Real.pi_pos]

private lemma imagAxis_im' (t : ℝ) (ht : 0 < t) : (imagAxis t ht).im = t := by
  simp [Work.Kernels.imagAxis]

private lemma z_norm (t : ℝ) (ht : 0 < t) :
    ‖((imagAxis t⁻¹ (inv_pos.mpr ht) : UpperHalfPlane) : ℂ)‖ = t⁻¹ := by
  have hcoe : ((imagAxis t⁻¹ (inv_pos.mpr ht) : UpperHalfPlane) : ℂ)
      = ((t⁻¹ : ℝ) : ℂ) * Complex.I := rfl
  rw [hcoe, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (inv_pos.mpr ht).le]

private lemma qnorm_axis (t : ℝ) (ht : 0 < t) :
    ‖qParamFun (imagAxis t⁻¹ (inv_pos.mpr ht))‖ = Real.exp ((-2 : ℝ) * (Real.pi / t)) := by
  rw [Work.Asymptotics.norm_qParamFun, imagAxis_im', div_eq_mul_inv]
  congr 1
  ring

/-! ## The `τ`-atoms on the cusp-`±1` tiles -/

/-- **The `τ`-atoms on the cusp-`±1` tiles.**  For `τ = (±1) +ᵥ w`, `w` in the cusp-`0`
neighbourhood `E`, and `t ≤ Im w / 2`, the atoms `E₄, E₆, E₂, φ_{-2}, φ_0, φ_2, Φ₈, Δ` are
bounded by `(scale w)^N`, while `Δ(τ)⁻¹` and `j(τ)` are bounded by `(scale w)^N e^{π/t}`. -/
private lemma tile_atoms :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
          ‖E4Fun ((n : ℝ) +ᵥ w)‖ ≤ C * (scale w) ^ N ∧
          ‖E6Fun ((n : ℝ) +ᵥ w)‖ ≤ C * (scale w) ^ N ∧
          ‖E2Fun ((n : ℝ) +ᵥ w)‖ ≤ C * (scale w) ^ N ∧
          ‖phiVec ((n : ℝ) +ᵥ w) 0‖ ≤ C * (scale w) ^ N ∧
          ‖phiVec ((n : ℝ) +ᵥ w) 1‖ ≤ C * (scale w) ^ N ∧
          ‖phiVec ((n : ℝ) +ᵥ w) 2‖ ≤ C * (scale w) ^ N ∧
          ‖phi8 ((n : ℝ) +ᵥ w)‖ ≤ C * (scale w) ^ N ∧
          ‖DeltaFun ((n : ℝ) +ᵥ w)‖ ≤ C * (scale w) ^ N ∧
          ‖(DeltaFun ((n : ℝ) +ᵥ w))⁻¹‖ ≤ C * (scale w) ^ N * Real.exp (Real.pi / t) ∧
          ‖jInvariantFun ((n : ℝ) +ᵥ w)‖ ≤ C * (scale w) ^ N * Real.exp (Real.pi / t) := by
  obtain ⟨C4, N4, hC4, hN4, hb4⟩ := EtailE.E_bdd_E4.exists_bound_zero
  obtain ⟨C6, N6, hC6, hN6, hb6⟩ := EtailE.E_bdd_E6.exists_bound_zero
  obtain ⟨C2, N2, hC2, hN2, hb2⟩ := EtailE.E_bdd_E2.exists_bound_zero
  obtain ⟨CD, ND, hCD, hND, hbD⟩ := EtailE.E_bdd_Delta
  obtain ⟨Civ, Niv, hCiv, hNiv, hbiv⟩ := EtailE.E_bdd_invDelta
  obtain ⟨Cj, Nj, hCj, hNj, hbj⟩ := EtailE.E_bdd_j
  -- derived constants
  set C0 : ℝ := 2 * C2 + 3 with hC0def
  set N0 : ℝ := N2 + 1 with hN0def
  set C2' : ℝ := 2 * (C2 * C2) + 6 * C2 + 3 with hC2'def
  set N2' : ℝ := 2 * N2 + 1 with hN2'def
  set C8 : ℝ := C4 * (2 * C6 + 2 * (C0 * C4)) + C6 * C2' with hC8def
  set N8 : ℝ := (N4 + 1 + N6) + (N6 + N2') + (N4 + (1 + N6) + N0 + N4) + 1 with hN8def
  have hC0pos : 0 < C0 := by rw [hC0def]; linarith [hC2]
  have hN0nn : 0 ≤ N0 := by rw [hN0def]; linarith [hN2]
  have hC2'pos : 0 < C2' := by rw [hC2'def]; nlinarith [hC2]
  have hN2'nn : 0 ≤ N2' := by rw [hN2'def]; linarith [hN2]
  have hC8pos : 0 < C8 := by
    rw [hC8def]
    have h1 : (0 : ℝ) < 2 * C6 + 2 * (C0 * C4) := by positivity
    have h2 : (0 : ℝ) < C4 * (2 * C6 + 2 * (C0 * C4)) := mul_pos hC4 h1
    have h3 : (0 : ℝ) < C6 * C2' := mul_pos hC6 hC2'pos
    linarith
  have hN8nn : 0 ≤ N8 := by rw [hN8def]; linarith [hN4, hN6, hN0nn, hN2'nn]
  -- `φ₀`
  have hphi0t : ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖phiVec ((n : ℝ) +ᵥ w) 1‖ ≤ C0 * (scale w) ^ N0 := by
    intro w n hn hw
    set s : ℝ := scale w with hsdef
    have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; exact Work.Kernels.one_le_scale w
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs1
    have hE2b : ‖E2Fun w‖ ≤ C2 * s ^ N2 := by rw [hsdef]; exact hb2 w hw
    have hE2 : E2Fun ((n : ℝ) +ᵥ w) = E2Fun w :=
      vadd_ne_of_vadd_one Work.Kernels.E2Fun_vadd_one w hn
    have hle : ‖(n : ℝ) + (w : ℂ)‖ ≤ 2 * s := coe_vadd_norm_le hn hsdef
    have hcoe : phiVec ((n : ℝ) +ᵥ w) 1
        = ((((n : ℝ) +ᵥ w : UpperHalfPlane)) : ℂ) * E2Fun ((n : ℝ) +ᵥ w)
          - 3 * Complex.I / (Real.pi : ℂ) := rfl
    rw [hcoe, hE2, UpperHalfPlane.coe_vadd]
    have hnorm3 : ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 3 / Real.pi := by
      rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
    have hprod : ‖(n : ℝ) + (w : ℂ)‖ * ‖E2Fun w‖ ≤ 2 * C2 * s ^ (N2 + 1) := by
      have h := mul_le_mul hle hE2b (norm_nonneg _) (by positivity)
      refine le_trans h (le_of_eq ?_)
      rw [rpow_succ hs0]
      ring
    have h3le : 3 / Real.pi ≤ 3 * s ^ N0 := by
      have h1 : (1 : ℝ) ≤ s ^ N0 := Real.one_le_rpow hs1 hN0nn
      have h2 : (3 : ℝ) / Real.pi ≤ 3 := by rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
      linarith
    calc ‖((n : ℝ) + (w : ℂ)) * E2Fun w - 3 * Complex.I / (Real.pi : ℂ)‖
        ≤ ‖((n : ℝ) + (w : ℂ)) * E2Fun w‖ + ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ := norm_sub_le _ _
      _ = ‖(n : ℝ) + (w : ℂ)‖ * ‖E2Fun w‖ + 3 / Real.pi := by rw [norm_mul, hnorm3]
      _ ≤ 2 * C2 * s ^ (N2 + 1) + 3 * s ^ N0 := add_le_add hprod h3le
      _ = C0 * s ^ N0 := by rw [hC0def, hN0def]; ring
  -- `φ₂`
  have hphi2t : ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖phiVec ((n : ℝ) +ᵥ w) 2‖ ≤ C2' * (scale w) ^ N2' := by
    intro w n hn hw
    set s : ℝ := scale w with hsdef
    have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; exact Work.Kernels.one_le_scale w
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs1
    have hC2nn : (0 : ℝ) ≤ C2 := hC2.le
    have hE2b : ‖E2Fun w‖ ≤ C2 * s ^ N2 := by rw [hsdef]; exact hb2 w hw
    have hE2 : E2Fun ((n : ℝ) +ᵥ w) = E2Fun w :=
      vadd_ne_of_vadd_one Work.Kernels.E2Fun_vadd_one w hn
    have hle : ‖(n : ℝ) + (w : ℂ)‖ ≤ 2 * s := coe_vadd_norm_le hn hsdef
    have hcoe : phiVec ((n : ℝ) +ᵥ w) 2
        = ((((n : ℝ) +ᵥ w : UpperHalfPlane)) : ℂ) * E2Fun ((n : ℝ) +ᵥ w) ^ 2
          - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun ((n : ℝ) +ᵥ w) := rfl
    rw [hcoe, hE2, UpperHalfPlane.coe_vadd]
    have hnorm6 : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 6 / Real.pi := by
      rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
    have hsq : ‖E2Fun w ^ 2‖ ≤ C2 * C2 * s ^ (2 * N2) := by
      rw [norm_pow]
      have h2 : ‖E2Fun w‖ ^ 2 ≤ (C2 * s ^ N2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hE2b 2
      refine le_trans h2 (le_of_eq ?_)
      have hsN : (s ^ N2) ^ 2 = s ^ (2 * N2) := by
        rw [pow_two, ← rpow_split hs0, show N2 + N2 = 2 * N2 by ring]
      have hC2sq : C2 ^ 2 = C2 * C2 := by ring
      calc (C2 * s ^ N2) ^ 2 = C2 ^ 2 * (s ^ N2) ^ 2 := by rw [mul_pow]
        _ = C2 * C2 * s ^ (2 * N2) := by rw [hsN, hC2sq]
    have hstep1 : ‖(n : ℝ) + (w : ℂ)‖ * ‖E2Fun w ^ 2‖ ≤ 2 * (C2 * C2) * s ^ (2 * N2 + 1) := by
      have h := mul_le_mul hle hsq (norm_nonneg _) (by positivity)
      refine le_trans h (le_of_eq ?_)
      rw [rpow_succ hs0]
      ring
    have hstep2 : 6 / Real.pi * ‖E2Fun w‖ ≤ 6 * C2 * s ^ (2 * N2 + 1) := by
      have h6 : (6 : ℝ) / Real.pi ≤ 6 := by rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
      have hNle : s ^ N2 ≤ s ^ (2 * N2 + 1) :=
        Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)
      have h1 : 6 / Real.pi * ‖E2Fun w‖ ≤ 6 / Real.pi * (C2 * s ^ N2) :=
        mul_le_mul_of_nonneg_left hE2b (by positivity)
      have h2 : 6 / Real.pi * (C2 * s ^ N2) ≤ 6 * C2 * s ^ (2 * N2 + 1) := by
        have h3 : 6 / Real.pi * C2 ≤ 6 * C2 := mul_le_mul_of_nonneg_right h6 hC2nn
        calc 6 / Real.pi * (C2 * s ^ N2) = (6 / Real.pi * C2) * s ^ N2 := by ring
          _ ≤ (6 * C2) * s ^ (2 * N2 + 1) := by
              refine mul_le_mul h3 ?_ (Real.rpow_nonneg hs0.le _) (by positivity)
              exact hNle
          _ = 6 * C2 * s ^ (2 * N2 + 1) := by ring
      linarith [h1, h2]
    have h3le : 3 / Real.pi ≤ 3 * s ^ (2 * N2 + 1) := by
      have h1 : (1 : ℝ) ≤ s ^ (2 * N2 + 1) := Real.one_le_rpow hs1 (by linarith)
      have h2 : (3 : ℝ) / Real.pi ≤ 3 := by rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
      linarith
    have htot : ‖((n : ℝ) + (w : ℂ)) * E2Fun w ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun w‖
        ≤ (2 * (C2 * C2) + 6 * C2 + 3) * s ^ (2 * N2 + 1) := by
      have h1 : ‖((n : ℝ) + (w : ℂ)) * E2Fun w ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun w‖
          ≤ ‖(n : ℝ) + (w : ℂ)‖ * ‖E2Fun w ^ 2‖ + 6 / Real.pi * ‖E2Fun w‖ := by
        calc ‖((n : ℝ) + (w : ℂ)) * E2Fun w ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun w‖
            ≤ ‖((n : ℝ) + (w : ℂ)) * E2Fun w ^ 2‖
              + ‖(6 * Complex.I / (Real.pi : ℂ)) * E2Fun w‖ := norm_sub_le _ _
          _ = ‖(n : ℝ) + (w : ℂ)‖ * ‖E2Fun w ^ 2‖ + 6 / Real.pi * ‖E2Fun w‖ := by
              rw [norm_mul, norm_mul, hnorm6]
      calc ‖((n : ℝ) + (w : ℂ)) * E2Fun w ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun w‖
          ≤ ‖(n : ℝ) + (w : ℂ)‖ * ‖E2Fun w ^ 2‖ + 6 / Real.pi * ‖E2Fun w‖ := h1
        _ ≤ 2 * (C2 * C2) * s ^ (2 * N2 + 1) + 6 * C2 * s ^ (2 * N2 + 1) := add_le_add hstep1 hstep2
        _ ≤ (2 * (C2 * C2) + 6 * C2 + 3) * s ^ (2 * N2 + 1) := by
            have hpos : (0:ℝ) ≤ s ^ (2 * N2 + 1) := Real.rpow_nonneg hs0.le _
            linarith [h3le]
    rw [hC2'def, hN2'def]
    exact htot
  -- `Φ₈`
  have hphi8t : ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ‖phi8 ((n : ℝ) +ᵥ w)‖ ≤ C8 * (scale w) ^ N8 := by
    intro w n hn hw
    set s : ℝ := scale w with hsdef
    have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; exact Work.Kernels.one_le_scale w
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs1
    have hE4b : ‖E4Fun ((n : ℝ) +ᵥ w)‖ ≤ C4 * s ^ N4 := by
      rw [vadd_ne_of_vadd_one Work.Kernels.KernelFacts.E4Fun_vadd_one w hn, hsdef]
      exact hb4 w hw
    have hE6b : ‖E6Fun ((n : ℝ) +ᵥ w)‖ ≤ C6 * s ^ N6 := by
      rw [vadd_ne_of_vadd_one Work.Kernels.KernelFacts.E6Fun_vadd_one w hn, hsdef]
      exact hb6 w hw
    have h0b : ‖phiVec ((n : ℝ) +ᵥ w) 1‖ ≤ C0 * s ^ N0 := by
      have h := hphi0t w n hn hw
      rw [hsdef]; exact h
    have h2b : ‖phiVec ((n : ℝ) +ᵥ w) 2‖ ≤ C2' * s ^ N2' := by
      have h := hphi2t w n hn hw
      rw [hsdef]; exact h
    have hTb' : ‖(n : ℝ) + (w : ℂ)‖ ≤ 2 * s := coe_vadd_norm_le hn hsdef
    have hTb : ‖phiVec ((n : ℝ) +ᵥ w) 0‖ ≤ 2 * s := by
      have hcoe0 : phiVec ((n : ℝ) +ᵥ w) 0 = ((((n : ℝ) +ᵥ w : UpperHalfPlane)) : ℂ) := rfl
      rw [hcoe0, UpperHalfPlane.coe_vadd]
      exact hTb'
    have hd : phi8 ((n : ℝ) +ᵥ w)
        = E4Fun ((n : ℝ) +ᵥ w) * ((((n : ℝ) +ᵥ w : UpperHalfPlane)) * E6Fun ((n : ℝ) +ᵥ w)
            - 2 * phiVec ((n : ℝ) +ᵥ w) 1 * E4Fun ((n : ℝ) +ᵥ w))
          + E6Fun ((n : ℝ) +ᵥ w) * phiVec ((n : ℝ) +ᵥ w) 2 := by
      rw [phi8]
      simp only [show phiVec ((n : ℝ) +ᵥ w) 1 = phi0 ((n : ℝ) +ᵥ w) from rfl,
        show phiVec ((n : ℝ) +ᵥ w) 2 = phi2 ((n : ℝ) +ᵥ w) from rfl]
    rw [hd]
    -- `τ E₆`
    have hA : ‖((n : ℝ) +ᵥ w : UpperHalfPlane) * E6Fun ((n : ℝ) +ᵥ w)‖
        ≤ 2 * C6 * s ^ (1 + N6) := by
      rw [show ((((n : ℝ) +ᵥ w : UpperHalfPlane)) : ℂ) = (n : ℝ) + (w : ℂ) from
        UpperHalfPlane.coe_vadd _ _]
      exact mul_bound0 hs1
        (show ‖(n : ℝ) + (w : ℂ)‖ ≤ 2 * s ^ (1 : ℝ) by simpa [Real.rpow_one] using hTb') hE6b
    -- `2 φ₀ E₄`
    have hB : ‖2 * phiVec ((n : ℝ) +ᵥ w) 1 * E4Fun ((n : ℝ) +ᵥ w)‖
        ≤ 2 * (C0 * C4) * s ^ (N0 + N4) := by
      rw [show (2 : ℂ) * phiVec ((n : ℝ) +ᵥ w) 1 * E4Fun ((n : ℝ) +ᵥ w)
          = (2 : ℂ) * (phiVec ((n : ℝ) +ᵥ w) 1 * E4Fun ((n : ℝ) +ᵥ w)) by ring, norm_mul,
        Complex.norm_ofNat]
      calc (2 : ℝ) * ‖phiVec ((n : ℝ) +ᵥ w) 1 * E4Fun ((n : ℝ) +ᵥ w)‖
          ≤ 2 * (C0 * C4 * s ^ (N0 + N4)) :=
            mul_le_mul_of_nonneg_left (mul_bound0 hs1 h0b hE4b) (by norm_num)
        _ = 2 * (C0 * C4) * s ^ (N0 + N4) := by ring
    -- the bracket
    have hinner : ‖(((n : ℝ) +ᵥ w : UpperHalfPlane)) * E6Fun ((n : ℝ) +ᵥ w)
          - 2 * phiVec ((n : ℝ) +ᵥ w) 1 * E4Fun ((n : ℝ) +ᵥ w)‖
        ≤ (2 * C6 + 2 * (C0 * C4)) * s ^ (N4 + (1 + N6) + N0 + N4) := by
      have hNI : 1 + N6 ≤ N4 + (1 + N6) + N0 + N4 := by linarith [hN4, hN0nn]
      have hNI' : N0 + N4 ≤ N4 + (1 + N6) + N0 + N4 := by linarith [hN6]
      have e1 : 2 * C6 * s ^ (1 + N6) ≤ 2 * C6 * s ^ (N4 + (1 + N6) + N0 + N4) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 hNI) (by positivity)
      have e2 : 2 * (C0 * C4) * s ^ (N0 + N4) ≤ 2 * (C0 * C4) * s ^ (N4 + (1 + N6) + N0 + N4) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 hNI') (by positivity)
      calc ‖(((n : ℝ) +ᵥ w : UpperHalfPlane)) * E6Fun ((n : ℝ) +ᵥ w)
            - 2 * phiVec ((n : ℝ) +ᵥ w) 1 * E4Fun ((n : ℝ) +ᵥ w)‖
          ≤ ‖((n : ℝ) +ᵥ w : UpperHalfPlane) * E6Fun ((n : ℝ) +ᵥ w)‖
            + ‖2 * phiVec ((n : ℝ) +ᵥ w) 1 * E4Fun ((n : ℝ) +ᵥ w)‖ := norm_sub_le _ _
        _ ≤ 2 * C6 * s ^ (N4 + (1 + N6) + N0 + N4)
              + 2 * (C0 * C4) * s ^ (N4 + (1 + N6) + N0 + N4) :=
            add_le_add (le_trans hA e1) (le_trans hB e2)
        _ = (2 * C6 + 2 * (C0 * C4)) * s ^ (N4 + (1 + N6) + N0 + N4) := by ring
    -- `E₄ · bracket`
    have hmain : ‖E4Fun ((n : ℝ) +ᵥ w) * ((((n : ℝ) +ᵥ w : UpperHalfPlane)) * E6Fun ((n : ℝ) +ᵥ w)
          - 2 * phiVec ((n : ℝ) +ᵥ w) 1 * E4Fun ((n : ℝ) +ᵥ w))‖
        ≤ C4 * (2 * C6 + 2 * (C0 * C4)) * s ^ N8 := by
      rw [norm_mul]
      have h := mul_le_mul hE4b hinner (norm_nonneg _) (by positivity)
      refine le_trans h ?_
      rw [show C4 * s ^ N4 * ((2 * C6 + 2 * (C0 * C4)) * s ^ (N4 + (1 + N6) + N0 + N4))
          = C4 * (2 * C6 + 2 * (C0 * C4)) * (s ^ N4 * s ^ (N4 + (1 + N6) + N0 + N4)) by ring,
        ← rpow_split hs0]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine Real.rpow_le_rpow_of_exponent_le hs1 ?_
      rw [hN8def]; linarith [hN6, hN2'nn]
    -- `E₆ φ₂`
    have hsecond : ‖E6Fun ((n : ℝ) +ᵥ w) * phiVec ((n : ℝ) +ᵥ w) 2‖ ≤ C6 * C2' * s ^ N8 := by
      rw [norm_mul]
      have h := mul_le_mul hE6b h2b (norm_nonneg _) (by positivity)
      refine le_trans h ?_
      rw [show C6 * s ^ N6 * (C2' * s ^ N2') = C6 * C2' * (s ^ N6 * s ^ N2') by ring,
        ← rpow_split hs0]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine Real.rpow_le_rpow_of_exponent_le hs1 ?_
      rw [hN8def]; linarith [hN4, hN0nn]
    -- assemble
    calc ‖E4Fun ((n : ℝ) +ᵥ w) * ((((n : ℝ) +ᵥ w : UpperHalfPlane)) * E6Fun ((n : ℝ) +ᵥ w)
          - 2 * phiVec ((n : ℝ) +ᵥ w) 1 * E4Fun ((n : ℝ) +ᵥ w))
        + E6Fun ((n : ℝ) +ᵥ w) * phiVec ((n : ℝ) +ᵥ w) 2‖
        ≤ ‖E4Fun ((n : ℝ) +ᵥ w) * ((((n : ℝ) +ᵥ w : UpperHalfPlane)) * E6Fun ((n : ℝ) +ᵥ w)
              - 2 * phiVec ((n : ℝ) +ᵥ w) 1 * E4Fun ((n : ℝ) +ᵥ w))‖
            + ‖E6Fun ((n : ℝ) +ᵥ w) * phiVec ((n : ℝ) +ᵥ w) 2‖ := norm_add_le _ _
      _ ≤ C4 * (2 * C6 + 2 * (C0 * C4)) * s ^ N8 + C6 * C2' * s ^ N8 := add_le_add hmain hsecond
      _ = (C4 * (2 * C6 + 2 * (C0 * C4)) + C6 * C2') * s ^ N8 := by ring
      _ = C8 * s ^ N8 := by rw [hC8def]
  -- the uniform constants
  set C : ℝ := C4 + C6 + C2 + 2 + C0 + C2' + C8 + CD + Civ + Cj + 1 with hCdef
  set N : ℝ := N4 + N6 + N2 + 1 + N0 + N2' + N8 + ND + Niv + Nj + 1 with hNdef
  have hCfin : 0 < C := by
    rw [hCdef]; linarith [hC4, hC6, hC2, hC0pos, hC2'pos, hC8pos, hCD, hCiv, hCj]
  have hNfin : 0 ≤ N := by
    rw [hNdef]; linarith [hN4, hN6, hN2, hN0nn, hN2'nn, hN8nn, hND, hNiv, hNj]
  have hC4le : C4 ≤ C := by rw [hCdef]; linarith [hC6, hC2, hC0pos, hC2'pos, hC8pos, hCD, hCiv, hCj]
  have hC6le : C6 ≤ C := by rw [hCdef]; linarith [hC4, hC2, hC0pos, hC2'pos, hC8pos, hCD, hCiv, hCj]
  have hC2le : C2 ≤ C := by rw [hCdef]; linarith [hC4, hC6, hC0pos, hC2'pos, hC8pos, hCD, hCiv, hCj]
  have hC0le : C0 ≤ C := by rw [hCdef]; linarith [hC4, hC6, hC2, hC2'pos, hC8pos, hCD, hCiv, hCj]
  have hC2'le : C2' ≤ C := by rw [hCdef]; linarith [hC4, hC6, hC2, hC0pos, hC8pos, hCD, hCiv, hCj]
  have hC8le : C8 ≤ C := by rw [hCdef]; linarith [hC4, hC6, hC2, hC0pos, hC2'pos, hCD, hCiv, hCj]
  have hCDle : CD ≤ C := by rw [hCdef]; linarith [hC4, hC6, hC2, hC0pos, hC2'pos, hC8pos, hCiv, hCj]
  have hCivle : Civ ≤ C := by rw [hCdef]; linarith [hC4, hC6, hC2, hC0pos, hC2'pos, hC8pos, hCD, hCj]
  have hCjle : Cj ≤ C := by rw [hCdef]; linarith [hC4, hC6, hC2, hC0pos, hC2'pos, hC8pos, hCD, hCiv]
  have hN4le : N4 ≤ N := by rw [hNdef]; linarith [hN6, hN2, hN0nn, hN2'nn, hN8nn, hND, hNiv, hNj]
  have hN6le : N6 ≤ N := by rw [hNdef]; linarith [hN4, hN2, hN0nn, hN2'nn, hN8nn, hND, hNiv, hNj]
  have hN2le : N2 ≤ N := by rw [hNdef]; linarith [hN4, hN6, hN0nn, hN2'nn, hN8nn, hND, hNiv, hNj]
  have hN0le : N0 ≤ N := by rw [hNdef]; linarith [hN4, hN6, hN2, hN2'nn, hN8nn, hND, hNiv, hNj]
  have hN2'le : N2' ≤ N := by rw [hNdef]; linarith [hN4, hN6, hN2, hN0nn, hN8nn, hND, hNiv, hNj]
  have hN8le : N8 ≤ N := by rw [hNdef]; linarith [hN4, hN6, hN2, hN0nn, hN2'nn, hND, hNiv, hNj]
  have hNDle : ND ≤ N := by rw [hNdef]; linarith [hN4, hN6, hN2, hN0nn, hN2'nn, hN8nn, hNiv, hNj]
  have hNivle : Niv ≤ N := by rw [hNdef]; linarith [hN4, hN6, hN2, hN0nn, hN2'nn, hN8nn, hND, hNj]
  have hNjle : Nj ≤ N := by rw [hNdef]; linarith [hN4, hN6, hN2, hN0nn, hN2'nn, hN8nn, hND, hNiv]
  refine ⟨C, N, hCfin, hNfin, fun w n hn hw t ht htle => ?_⟩
  set s : ℝ := scale w with hsdef
  have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; exact Work.Kernels.one_le_scale w
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs1
  have hE4 : ‖E4Fun ((n : ℝ) +ᵥ w)‖ ≤ C * s ^ N := by
    have h0 : ‖E4Fun w‖ ≤ C4 * s ^ N4 := by rw [hsdef]; exact hb4 w hw
    rw [vadd_ne_of_vadd_one Work.Kernels.KernelFacts.E4Fun_vadd_one w hn]
    exact le_trans h0 (mul_le_mul hC4le (Real.rpow_le_rpow_of_exponent_le hs1 hN4le)
      (Real.rpow_nonneg hs0.le N4) hCfin.le)
  have hE6 : ‖E6Fun ((n : ℝ) +ᵥ w)‖ ≤ C * s ^ N := by
    have h0 : ‖E6Fun w‖ ≤ C6 * s ^ N6 := by rw [hsdef]; exact hb6 w hw
    rw [vadd_ne_of_vadd_one Work.Kernels.KernelFacts.E6Fun_vadd_one w hn]
    exact le_trans h0 (mul_le_mul hC6le (Real.rpow_le_rpow_of_exponent_le hs1 hN6le)
      (Real.rpow_nonneg hs0.le N6) hCfin.le)
  have hE2 : ‖E2Fun ((n : ℝ) +ᵥ w)‖ ≤ C * s ^ N := by
    have h0 : ‖E2Fun w‖ ≤ C2 * s ^ N2 := by rw [hsdef]; exact hb2 w hw
    rw [vadd_ne_of_vadd_one Work.Kernels.E2Fun_vadd_one w hn]
    exact le_trans h0 (mul_le_mul hC2le (Real.rpow_le_rpow_of_exponent_le hs1 hN2le)
      (Real.rpow_nonneg hs0.le N2) hCfin.le)
  have hTau : ‖phiVec ((n : ℝ) +ᵥ w) 0‖ ≤ C * s ^ N := by
    have hcoe0 : phiVec ((n : ℝ) +ᵥ w) 0 = ((((n : ℝ) +ᵥ w : UpperHalfPlane)) : ℂ) := rfl
    rw [hcoe0, UpperHalfPlane.coe_vadd]
    have hle : ‖(n : ℝ) + (w : ℂ)‖ ≤ 2 * s := coe_vadd_norm_le hn hsdef
    refine le_trans hle ?_
    have h2C : (2 : ℝ) ≤ C := by
      rw [hCdef]; linarith [hC4, hC6, hC2, hC0pos, hC2'pos, hC8pos, hCD, hCiv, hCj]
    have h1N : (1 : ℝ) ≤ N := by
      rw [hNdef]; linarith [hN4, hN6, hN2, hN0nn, hN2'nn, hN8nn, hND, hNiv, hNj]
    have h := mul_le_mul h2C (Real.rpow_le_rpow_of_exponent_le hs1 h1N)
      (Real.rpow_nonneg hs0.le 1) hCfin.le
    simpa [Real.rpow_one] using h
  have hPhi0 : ‖phiVec ((n : ℝ) +ᵥ w) 1‖ ≤ C * s ^ N := by
    have h0 : ‖phiVec ((n : ℝ) +ᵥ w) 1‖ ≤ C0 * s ^ N0 := by
      have h := hphi0t w n hn hw
      rw [hsdef]; exact h
    exact le_trans h0 (mul_le_mul hC0le (Real.rpow_le_rpow_of_exponent_le hs1 hN0le)
      (Real.rpow_nonneg hs0.le N0) hCfin.le)
  have hPhi2 : ‖phiVec ((n : ℝ) +ᵥ w) 2‖ ≤ C * s ^ N := by
    have h0 : ‖phiVec ((n : ℝ) +ᵥ w) 2‖ ≤ C2' * s ^ N2' := by
      have h := hphi2t w n hn hw
      rw [hsdef]; exact h
    exact le_trans h0 (mul_le_mul hC2'le (Real.rpow_le_rpow_of_exponent_le hs1 hN2'le)
      (Real.rpow_nonneg hs0.le N2') hCfin.le)
  have hPhi8 : ‖phi8 ((n : ℝ) +ᵥ w)‖ ≤ C * s ^ N := by
    have h0 : ‖phi8 ((n : ℝ) +ᵥ w)‖ ≤ C8 * s ^ N8 := by
      have h := hphi8t w n hn hw
      rw [hsdef]; exact h
    exact le_trans h0 (mul_le_mul hC8le (Real.rpow_le_rpow_of_exponent_le hs1 hN8le)
      (Real.rpow_nonneg hs0.le N8) hCfin.le)
  have hDelta : ‖DeltaFun ((n : ℝ) +ᵥ w)‖ ≤ C * s ^ N := by
    have h0 : ‖DeltaFun w‖ ≤ CD * s ^ ND := by
      have h2 : Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [hw.2, Real.pi_pos]
      have h3 : CD * s ^ ND * Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im) ≤ CD * s ^ ND := by
        have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ CD * s ^ ND)
        simpa using h4
      rw [hsdef]
      exact le_trans (hbD w hw) h3
    rw [vadd_ne_of_vadd_one Work.Kernels.KernelFacts.DeltaFun_vadd_one w hn]
    exact le_trans h0 (mul_le_mul hCDle (Real.rpow_le_rpow_of_exponent_le hs1 hNDle)
      (Real.rpow_nonneg hs0.le ND) hCfin.le)
  have hInvDelta : ‖(DeltaFun ((n : ℝ) +ᵥ w))⁻¹‖ ≤ C * s ^ N * Real.exp (Real.pi / t) := by
    have h0 : ‖(DeltaFun w)⁻¹‖ ≤ Civ * s ^ Niv * Real.exp (Real.pi / t) := by
      have h3 : (2 * Real.pi) * (ModularGroup.S • w).im ≤ Real.pi / t := two_pi_imS_le hw ht htle
      have h4 : Real.exp ((2 * Real.pi) * (ModularGroup.S • w).im) ≤ Real.exp (Real.pi / t) :=
        Real.exp_le_exp.mpr h3
      rw [hsdef]
      exact le_trans (hbiv w hw) (mul_le_mul_of_nonneg_left h4 (by positivity))
    rw [vadd_ne_of_vadd_one Work.Kernels.KernelFacts.DeltaFun_vadd_one w hn]
    exact le_trans h0 (mul_le_mul (mul_le_mul hCivle
      (Real.rpow_le_rpow_of_exponent_le hs1 hNivle) (Real.rpow_nonneg hs0.le Niv) hCfin.le)
      le_rfl (Real.exp_pos _).le (by positivity))
  have hJ : ‖jInvariantFun ((n : ℝ) +ᵥ w)‖ ≤ C * s ^ N * Real.exp (Real.pi / t) := by
    have h0 : ‖jInvariantFun w‖ ≤ Cj * s ^ Nj * Real.exp (Real.pi / t) := by
      have h3 : (2 * Real.pi) * (ModularGroup.S • w).im ≤ Real.pi / t := two_pi_imS_le hw ht htle
      have h4 : Real.exp ((2 * Real.pi) * (ModularGroup.S • w).im) ≤ Real.exp (Real.pi / t) :=
        Real.exp_le_exp.mpr h3
      rw [hsdef]
      exact le_trans (hbj w hw) (mul_le_mul_of_nonneg_left h4 (by positivity))
    rw [vadd_ne_of_vadd_one Work.Kernels.KernelFacts.jInvariantFun_vadd_one w hn]
    exact le_trans h0 (mul_le_mul (mul_le_mul hCjle
      (Real.rpow_le_rpow_of_exponent_le hs1 hNjle) (Real.rpow_nonneg hs0.le Nj) hCfin.le)
      le_rfl (Real.exp_pos _).le (by positivity))
  exact ⟨hE4, hE6, hE2, hTau, hPhi0, hPhi2, hPhi8, hDelta, hInvDelta, hJ⟩

/-- Weakening: monotone in the constant and the `scale w` exponent, with the exponential
coefficient reduced to `-1`. -/
private lemma weaken_bound {s : ℝ} (hs : 1 ≤ s) {t : ℝ} (ht : 0 < t)
    {A B N M c : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hNM : N ≤ M) (hc : c ≤ -1) :
    A * s ^ N * Real.exp (c * (Real.pi / t)) ≤ B * s ^ M * Real.exp (-(Real.pi / t)) := by
  have h1 : A * s ^ N ≤ B * s ^ M :=
    mul_le_mul hAB (Real.rpow_le_rpow_of_exponent_le hs hNM)
      (Real.rpow_nonneg (le_trans zero_le_one hs) N) (le_trans hA hAB)
  have h2 : Real.exp (c * (Real.pi / t)) ≤ Real.exp (-(Real.pi / t)) := by
    rw [Real.exp_le_exp]
    calc c * (Real.pi / t) ≤ (-1) * (Real.pi / t) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = -(Real.pi / t) := by ring
  have hB0 : 0 ≤ B * s ^ M := mul_nonneg (le_trans hA hAB) (Real.rpow_nonneg (le_trans zero_le_one hs) M)
  calc A * s ^ N * Real.exp (c * (Real.pi / t))
      = (A * s ^ N) * Real.exp (c * (Real.pi / t)) := by ring
    _ ≤ (B * s ^ M) * Real.exp (c * (Real.pi / t)) := mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ (B * s ^ M) * Real.exp (-(Real.pi / t)) := mul_le_mul_of_nonneg_left h2 hB0
    _ = B * s ^ M * Real.exp (-(Real.pi / t)) := by ring

/-- Multiply a bound by a positive constant and weaken it to the canonical shape. -/
private lemma const_weaken {s : ℝ} (hs : 1 ≤ s) {t : ℝ} (ht : 0 < t) {m K B : ℝ} {X : ℂ} {N M c : ℝ}
    (hm : 0 ≤ m) (hK : 0 ≤ K) (hX : ‖X‖ ≤ K * s ^ N * Real.exp (c * (Real.pi / t)))
    (hmK : m * K ≤ B) (hNM : N ≤ M) (hc : c ≤ -1) :
    ‖(m : ℂ) * X‖ ≤ B * s ^ M * Real.exp (-(Real.pi / t)) := by
  have hmK0 : 0 ≤ m * K := mul_nonneg hm hK
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hm]
  refine le_trans (mul_le_mul_of_nonneg_left hX hm) ?_
  rw [show m * (K * s ^ N * Real.exp (c * (Real.pi / t)))
      = (m * K) * s ^ N * Real.exp (c * (Real.pi / t)) by ring]
  exact weaken_bound hs ht hmK0 hmK hNM hc

private lemma sq_expansion (t : ℝ) (ht : 0 < t) :
    ‖qParamFun (imagAxis t⁻¹ (inv_pos.mpr ht))‖ ^ 2 = Real.exp ((-4 : ℝ) * (Real.pi / t)) := by
  rw [qnorm_axis t ht, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-! ## The numerator `Ξ₈` on the tile -/

private lemma Xi8_tile :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
          ‖Xi8 ((n : ℝ) +ᵥ w) (imagAxis t⁻¹ (inv_pos.mpr ht))‖
            ≤ C * (scale w) ^ N * Real.exp (-(Real.pi / t)) := by
  obtain ⟨Cg, Ng, hCg, hNg, hb⟩ := tile_atoms
  obtain ⟨CΔu, hCΔu, hΔup⟩ := delta_upper_third
  obtain ⟨Cσ, hCσ, hσ1, hσ2, hσ3, hσ4⟩ := ZAtomsThird.cusp_forms
  obtain ⟨B4, hB4, hE4zb⟩ := E4_bounded_third
  have T1 : ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
        ‖DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht)) / DeltaFun ((n : ℝ) +ᵥ w)
            * E4Fun ((n : ℝ) +ᵥ w) ^ 2 * phi8 ((n : ℝ) +ᵥ w)‖
          ≤ (CΔu * Cg * Cg * Cg * Cg) * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) := by
    intro w n hn hw t ht htle
    set s : ℝ := scale w with hsdef
    set τ : ℍ := (n : ℝ) +ᵥ w with hτdef
    set z : ℍ := imagAxis t⁻¹ (inv_pos.mpr ht) with hzdef
    have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; exact Work.Kernels.one_le_scale w
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs1
    have hz3 : (1 : ℝ) / 3 ≤ z.im := by
      rw [hzdef, imagAxis_im']
      have h1 : t ≤ 1 / 4 := by have h2 := Work.Asymptotics.tile_im_le_half hw; linarith
      have h3 : (4 : ℝ) ≤ t⁻¹ := by
        rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 4) ht]; simpa using h1
      linarith
    obtain ⟨hE4, hE6, hE2, hTau, hPhi0, hPhi2, hPhi8, hDelta, hInvDelta, hJ⟩ := hb w n hn hw t ht htle
    have hE4' : ‖E4Fun τ‖ ≤ Cg * s ^ Ng := by
      have h := hE4; rw [← hτdef, ← hsdef] at h; exact h
    have hPhi8' : ‖phi8 τ‖ ≤ Cg * s ^ Ng := by
      have h := hPhi8; rw [← hτdef, ← hsdef] at h; exact h
    have hInvD : ‖(DeltaFun τ)⁻¹‖ ≤ Cg * s ^ Ng * Real.exp (1 * (Real.pi / t)) := by
      have h := hInvDelta; rw [← hτdef, ← hsdef] at h; simpa using h
    have hΔz : ‖DeltaFun z‖ ≤ CΔu * s ^ (0 : ℝ) * Real.exp ((-2 : ℝ) * (Real.pi / t)) := by
      have h := hΔup z hz3
      rw [qnorm_axis t ht] at h
      rw [hsdef, Real.rpow_zero, mul_one]
      exact h
    have h4sq : ‖E4Fun τ ^ 2‖ ≤ Cg * Cg * s ^ (Ng + Ng) := by
      rw [norm_pow]
      have h2 : ‖E4Fun τ‖ ^ 2 ≤ (Cg * s ^ Ng) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hE4' 2
      refine le_trans h2 (le_of_eq ?_)
      have hsN : (s ^ Ng) ^ 2 = s ^ (Ng + Ng) := by rw [pow_two, rpow_split hs0]
      have hCsq : Cg ^ 2 = Cg * Cg := by ring
      calc (Cg * s ^ Ng) ^ 2 = Cg ^ 2 * (s ^ Ng) ^ 2 := by rw [mul_pow]
        _ = Cg * Cg * s ^ (Ng + Ng) := by rw [hsN, hCsq]
    have h4sqphi : ‖E4Fun τ ^ 2 * phi8 τ‖ ≤ (Cg * Cg) * Cg * s ^ ((Ng + Ng) + Ng) :=
      mul_bound0 hs1 h4sq hPhi8'
    have hfac : ‖(DeltaFun τ)⁻¹ * (E4Fun τ ^ 2 * phi8 τ)‖
        ≤ Cg * ((Cg * Cg) * Cg) * s ^ (Ng + ((Ng + Ng) + Ng))
          * Real.exp ((1 + 0) * (Real.pi / t)) :=
      mul_bound hs1 hInvD (by simpa using h4sqphi)
    have hraw : ‖DeltaFun z * ((DeltaFun τ)⁻¹ * (E4Fun τ ^ 2 * phi8 τ))‖
        ≤ CΔu * (Cg * (Cg * Cg * Cg)) * s ^ (0 + (Ng + (Ng + Ng + Ng)))
          * Real.exp ((-2 + (1 + 0)) * (Real.pi / t)) :=
      mul_bound hs1 hΔz hfac
    have htot : ‖DeltaFun z * ((DeltaFun τ)⁻¹ * (E4Fun τ ^ 2 * phi8 τ))‖
        ≤ (CΔu * Cg * Cg * Cg * Cg) * s ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) :=
      le_trans hraw (weaken_bound hs1 ht (by positivity) (le_of_eq (by ring_nf)) (by linarith [hNg]) (by norm_num))
    have hexpr : DeltaFun z / DeltaFun τ * E4Fun τ ^ 2 * phi8 τ
        = DeltaFun z * ((DeltaFun τ)⁻¹ * (E4Fun τ ^ 2 * phi8 τ)) := by
      rw [div_eq_mul_inv]; ring
    rw [hexpr]
    exact htot
  have T2 : ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
        ‖(((n : ℝ) +ᵥ w : UpperHalfPlane)) * E6Fun ((n : ℝ) +ᵥ w)
            * E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2
            * (E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) - E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2)‖
          ≤ (Cσ * B4 * B4 * Cg * Cg) * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) := by
    intro w n hn hw t ht htle
    set s : ℝ := scale w with hsdef
    set τ : ℍ := (n : ℝ) +ᵥ w with hτdef
    set z : ℍ := imagAxis t⁻¹ (inv_pos.mpr ht) with hzdef
    have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; exact Work.Kernels.one_le_scale w
    have hz3 : (1 : ℝ) / 3 ≤ z.im := by
      rw [hzdef, imagAxis_im']
      have h1 : t ≤ 1 / 4 := by have h2 := Work.Asymptotics.tile_im_le_half hw; linarith
      have h3 : (4 : ℝ) ≤ t⁻¹ := by
        rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 4) ht]; simpa using h1
      linarith
    obtain ⟨hE4, hE6, hE2, hTau, hPhi0, hPhi2, hPhi8, hDelta, hInvDelta, hJ⟩ := hb w n hn hw t ht htle
    have hE6' : ‖E6Fun τ‖ ≤ Cg * s ^ Ng := by
      have h := hE6; rw [← hτdef, ← hsdef] at h; exact h
    have hTauE : ‖(τ : ℂ)‖ ≤ Cg * s ^ Ng := by
      have h := hTau; rw [← hτdef, ← hsdef] at h
      have hcoe : phiVec τ 0 = (τ : ℂ) := rfl
      rwa [hcoe] at h
    have hE4z : ‖E4Fun z‖ ≤ B4 * s ^ (0 : ℝ) := by
      have h := hE4zb z hz3
      rw [hsdef, Real.rpow_zero, mul_one]
      exact h
    have hσz : ‖E4Fun z - E2Fun z ^ 2‖ ≤ Cσ * s ^ (0 : ℝ) * Real.exp ((-2 : ℝ) * (Real.pi / t)) := by
      have h := hσ1 z hz3
      rw [qnorm_axis t ht] at h
      rw [hsdef, Real.rpow_zero, mul_one]
      exact h
    have hE4zsq : ‖E4Fun z ^ 2‖ ≤ (B4 * B4) * s ^ (0 : ℝ) := by
      rw [norm_pow, hsdef, Real.rpow_zero, mul_one]
      have h := pow_le_pow_left₀ (norm_nonneg _) (hE4zb z hz3) 2
      simpa [pow_two] using h
    have hA : ‖(τ : ℂ) * E6Fun τ‖ ≤ Cg * Cg * s ^ (Ng + Ng) :=
      mul_bound0 hs1 hTauE hE6'
    have hB : ‖(τ : ℂ) * E6Fun τ * E4Fun z ^ 2‖ ≤ (Cg * Cg) * (B4 * B4) * s ^ ((Ng + Ng) + 0) :=
      mul_bound0 hs1 hA hE4zsq
    have hraw : ‖(τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)‖
        ≤ ((Cg * Cg) * (B4 * B4)) * Cσ * s ^ (((Ng + Ng) + 0) + 0)
          * Real.exp ((0 + (-2)) * (Real.pi / t)) :=
      mul_bound hs1 (by simpa using hB) hσz
    have htot : ‖(τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2)‖
        ≤ (Cσ * B4 * B4 * Cg * Cg) * s ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) :=
      le_trans hraw (weaken_bound hs1 ht (by positivity) (le_of_eq (by ring_nf)) (by linarith [hNg]) (by norm_num))
    rw [show (((n : ℝ) +ᵥ w : UpperHalfPlane)) * E6Fun ((n : ℝ) +ᵥ w)
          * E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2
          * (E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) - E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2)
        = (τ : ℂ) * E6Fun τ * E4Fun z ^ 2 * (E4Fun z - E2Fun z ^ 2) by
          rw [hτdef, hzdef, UpperHalfPlane.coe_vadd]]
    exact htot
  have T3 : ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
        ‖2 * phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w)
            * E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht))
            * (E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) * E6Fun (imagAxis t⁻¹ (inv_pos.mpr ht))
              - E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2)‖
          ≤ (2 * Cσ * B4 * Cg * Cg) * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) := by
    intro w n hn hw t ht htle
    set s : ℝ := scale w with hsdef
    set τ : ℍ := (n : ℝ) +ᵥ w with hτdef
    set z : ℍ := imagAxis t⁻¹ (inv_pos.mpr ht) with hzdef
    have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; exact Work.Kernels.one_le_scale w
    have hz3 : (1 : ℝ) / 3 ≤ z.im := by
      rw [hzdef, imagAxis_im']
      have h1 : t ≤ 1 / 4 := by have h2 := Work.Asymptotics.tile_im_le_half hw; linarith
      have h3 : (4 : ℝ) ≤ t⁻¹ := by
        rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 4) ht]; simpa using h1
      linarith
    obtain ⟨hE4, hE6, hE2, hTau, hPhi0, hPhi2, hPhi8, hDelta, hInvDelta, hJ⟩ := hb w n hn hw t ht htle
    have hE4' : ‖E4Fun τ‖ ≤ Cg * s ^ Ng := by
      have h := hE4; rw [← hτdef, ← hsdef] at h; exact h
    have hPhi0' : ‖phi0 τ‖ ≤ Cg * s ^ Ng := by
      have h := hPhi0; rw [← hτdef, ← hsdef] at h
      have hcoe : phiVec τ 1 = phi0 τ := rfl
      rwa [hcoe] at h
    have hE4z : ‖E4Fun z‖ ≤ B4 * s ^ (0 : ℝ) := by
      have h := hE4zb z hz3
      rw [hsdef, Real.rpow_zero, mul_one]
      exact h
    have hεz : ‖E2Fun z * E6Fun z - E4Fun z ^ 2‖
        ≤ Cσ * s ^ (0 : ℝ) * Real.exp ((-2 : ℝ) * (Real.pi / t)) := by
      have h := hσ2 z hz3
      rw [qnorm_axis t ht] at h
      rw [hsdef, Real.rpow_zero, mul_one]
      exact h
    have hA : ‖2 * phi0 τ * E4Fun τ‖ ≤ 2 * (Cg * Cg) * s ^ (Ng + Ng) := by
      rw [show (2 : ℂ) * phi0 τ * E4Fun τ = (2 : ℂ) * (phi0 τ * E4Fun τ) by ring, norm_mul,
        Complex.norm_ofNat]
      calc (2 : ℝ) * ‖phi0 τ * E4Fun τ‖ ≤ 2 * (Cg * Cg * s ^ (Ng + Ng)) :=
            mul_le_mul_of_nonneg_left (mul_bound0 hs1 hPhi0' hE4') (by norm_num)
        _ = 2 * (Cg * Cg) * s ^ (Ng + Ng) := by ring
    have hB : ‖2 * phi0 τ * E4Fun τ * E4Fun z‖
        ≤ (2 * (Cg * Cg)) * B4 * s ^ ((Ng + Ng) + 0) := by
      rw [show 2 * phi0 τ * E4Fun τ * E4Fun z = (2 * phi0 τ * E4Fun τ) * E4Fun z from rfl]
      exact mul_bound0 hs1 hA hE4z
    have hraw : ‖2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2)‖
        ≤ ((2 * (Cg * Cg)) * B4) * Cσ * s ^ (((Ng + Ng) + 0) + 0)
          * Real.exp ((0 + (-2)) * (Real.pi / t)) :=
      mul_bound hs1 (by simpa using hB) hεz
    have htot : ‖2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2)‖
        ≤ (2 * Cσ * B4 * Cg * Cg) * s ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) :=
      le_trans hraw (weaken_bound hs1 ht (by positivity) (le_of_eq (by ring_nf)) (by linarith [hNg]) (by norm_num))
    rw [show 2 * phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w)
          * E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht))
          * (E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) * E6Fun (imagAxis t⁻¹ (inv_pos.mpr ht))
            - E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2)
        = 2 * phi0 τ * E4Fun τ * E4Fun z * (E2Fun z * E6Fun z - E4Fun z ^ 2) by
          rw [hτdef, hzdef]]
    exact htot
  refine ⟨CΔu * Cg * Cg * Cg * Cg + Cσ * B4 * B4 * Cg * Cg + 2 * Cσ * B4 * Cg * Cg,
    4 * Ng + 1, by positivity, by linarith, ?_⟩
  intro w n hn hw t ht htle
  set U : ℂ := DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht)) / DeltaFun ((n : ℝ) +ᵥ w)
      * E4Fun ((n : ℝ) +ᵥ w) ^ 2 * phi8 ((n : ℝ) +ᵥ w) with hUdef
  set V : ℂ := (((n : ℝ) +ᵥ w : UpperHalfPlane)) * E6Fun ((n : ℝ) +ᵥ w)
      * E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2
      * (E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) - E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2) with hVdef
  set W : ℂ := 2 * phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w)
      * E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht))
      * (E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) * E6Fun (imagAxis t⁻¹ (inv_pos.mpr ht))
        - E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2) with hWdef
  have hΔne : DeltaFun ((n : ℝ) +ᵥ w) ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _
  have hΔzne : DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht)) ≠ 0 :=
    Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _
  have e1 : ‖U‖ ≤ (CΔu * Cg * Cg * Cg * Cg) * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) := by
    rw [hUdef]; exact T1 w n hn hw t ht htle
  have e2 : ‖V‖ ≤ (Cσ * B4 * B4 * Cg * Cg) * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) := by
    rw [hVdef]; exact T2 w n hn hw t ht htle
  have e3 : ‖W‖ ≤ (2 * Cσ * B4 * Cg * Cg) * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) := by
    rw [hWdef]; exact T3 w n hn hw t ht htle
  have hc := Xi8_cancelled ((n : ℝ) +ᵥ w) (imagAxis t⁻¹ (inv_pos.mpr ht)) hΔne hΔzne
  have hcU : Xi8 ((n : ℝ) +ᵥ w) (imagAxis t⁻¹ (inv_pos.mpr ht)) = U - V - W := by
    rw [hc, ← hUdef, ← hVdef, ← hWdef]
  rw [hcU]
  calc ‖U - V - W‖ ≤ ‖U - V‖ + ‖W‖ := norm_sub_le _ _
    _ ≤ (‖U‖ + ‖V‖) + ‖W‖ := by
        have h := norm_sub_le U V; linarith
    _ ≤ ((CΔu * Cg * Cg * Cg * Cg) * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t))
          + (Cσ * B4 * B4 * Cg * Cg) * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)))
        + (2 * Cσ * B4 * Cg * Cg) * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) := by
        linarith [e1, e2, e3]
    _ = (CΔu * Cg * Cg * Cg * Cg + Cσ * B4 * B4 * Cg * Cg + 2 * Cσ * B4 * Cg * Cg)
          * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) := by ring

/-! ## The numerator `Ξ₂₄` on the tile -/

private lemma Xi24_tile :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
          ‖Xi24 ((n : ℝ) +ᵥ w) (imagAxis t⁻¹ (inv_pos.mpr ht))‖
            ≤ C * (scale w) ^ N * Real.exp (-(Real.pi / t)) := by
  obtain ⟨Cg, Ng, hCg, hNg, hb⟩ := tile_atoms
  obtain ⟨Cσ, hCσ, hσ1, hσ2, hσ3, hσ4⟩ := ZAtomsThird.cusp_forms
  obtain ⟨B4, hB4, hE4zb⟩ := E4_bounded_third
  obtain ⟨Cjσ, hCjσ, hjzσ⟩ := jz_sigma_third
  obtain ⟨C2m1, hC2m1, h2m1⟩ := E2sq_sub_one_third
  obtain ⟨CE4m1, hCE4m1, hE4m1⟩ := E4_sub_one_third
  obtain ⟨cΔ, hcΔ, hΔlow⟩ := delta_lower_third
  have hNf : (0 : ℝ) ≤ 4 * Ng + 1 := by linarith
  have TA1 : ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
        ‖6 * E4Fun ((n : ℝ) +ᵥ w) * phi8 ((n : ℝ) +ᵥ w)
            * (E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) - E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2)
            * jInvariantFun ((n : ℝ) +ᵥ w)‖
          ≤ (6 * Cg * Cg * Cg * Cσ) * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) := by
    intro w n hn hw t ht htle
    set s : ℝ := scale w with hsdef
    set τ : ℍ := (n : ℝ) +ᵥ w with hτdef
    set z : ℍ := imagAxis t⁻¹ (inv_pos.mpr ht) with hzdef
    have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; exact Work.Kernels.one_le_scale w
    have hz3 : (1 : ℝ) / 3 ≤ z.im := by
      rw [hzdef, imagAxis_im']
      have h1 : t ≤ 1 / 4 := by have h2 := Work.Asymptotics.tile_im_le_half hw; linarith
      have h3 : (4 : ℝ) ≤ t⁻¹ := by rw [le_inv_comm₀ (by norm_num : (0:ℝ) < 4) ht]; simpa using h1
      linarith
    obtain ⟨hE4, hE6, hE2, hTau, hPhi0, hPhi2, hPhi8, hDelta, hInvDelta, hJ⟩ := hb w n hn hw t ht htle
    have hE4' : ‖E4Fun τ‖ ≤ Cg * s ^ Ng := by
      have h := hE4; rw [← hτdef, ← hsdef] at h; exact h
    have hPhi8' : ‖phi8 τ‖ ≤ Cg * s ^ Ng := by
      have h := hPhi8; rw [← hτdef, ← hsdef] at h; exact h
    have hJτ : ‖jInvariantFun τ‖ ≤ Cg * s ^ Ng * Real.exp (1 * (Real.pi / t)) := by
      have h := hJ; rw [← hτdef, ← hsdef] at h; simpa using h
    have hσz : ‖E4Fun z - E2Fun z ^ 2‖ ≤ Cσ * s ^ (0:ℝ) * Real.exp ((-2:ℝ) * (Real.pi / t)) := by
      have h := hσ1 z hz3
      rw [qnorm_axis t ht] at h
      rw [hsdef, Real.rpow_zero, mul_one]
      exact h
    have hE4phi8 : ‖E4Fun τ * phi8 τ‖ ≤ Cg * Cg * s ^ (Ng + Ng) := mul_bound0 hs1 hE4' hPhi8'
    have hz1 : ‖(E4Fun z - E2Fun z ^ 2) * jInvariantFun τ‖
        ≤ Cσ * Cg * s ^ (0 + Ng) * Real.exp ((-2 + 1) * (Real.pi / t)) := mul_bound hs1 hσz hJτ
    have hraw : ‖E4Fun τ * phi8 τ * ((E4Fun z - E2Fun z ^ 2) * jInvariantFun τ)‖
        ≤ (Cg * Cg) * (Cσ * Cg) * s ^ ((Ng + Ng) + (0 + Ng))
          * Real.exp ((0 + (-2 + 1)) * (Real.pi / t)) :=
      mul_bound hs1 (by simpa using hE4phi8) hz1
    have htot : ‖6 * E4Fun τ * phi8 τ * (E4Fun z - E2Fun z ^ 2) * jInvariantFun τ‖
        ≤ (6 * Cg * Cg * Cg * Cσ) * s ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) := by
      rw [show (6 : ℂ) * E4Fun τ * phi8 τ * (E4Fun z - E2Fun z ^ 2) * jInvariantFun τ
          = (6 : ℂ) * (E4Fun τ * phi8 τ * ((E4Fun z - E2Fun z ^ 2) * jInvariantFun τ)) by ring]
      exact const_weaken hs1 ht (by norm_num) (by positivity) hraw (le_of_eq (by ring_nf)) (by linarith) (by norm_num)
    rw [show 6 * E4Fun ((n : ℝ) +ᵥ w) * phi8 ((n : ℝ) +ᵥ w)
          * (E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) - E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2)
          * jInvariantFun ((n : ℝ) +ᵥ w)
        = 6 * E4Fun τ * phi8 τ * (E4Fun z - E2Fun z ^ 2) * jInvariantFun τ by rw [hτdef, hzdef]]
    exact htot
  have TA2 : ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
        ‖6 * E4Fun ((n : ℝ) +ᵥ w) * phi8 ((n : ℝ) +ᵥ w)
            * (288 - (E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) - E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2)
              * jInvariantFun (imagAxis t⁻¹ (inv_pos.mpr ht)))‖
          ≤ (6 * Cg * Cg * Cjσ) * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) := by
    intro w n hn hw t ht htle
    set s : ℝ := scale w with hsdef
    set τ : ℍ := (n : ℝ) +ᵥ w with hτdef
    set z : ℍ := imagAxis t⁻¹ (inv_pos.mpr ht) with hzdef
    have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; exact Work.Kernels.one_le_scale w
    have hz3 : (1 : ℝ) / 3 ≤ z.im := by
      rw [hzdef, imagAxis_im']
      have h1 : t ≤ 1 / 4 := by have h2 := Work.Asymptotics.tile_im_le_half hw; linarith
      have h3 : (4 : ℝ) ≤ t⁻¹ := by rw [le_inv_comm₀ (by norm_num : (0:ℝ) < 4) ht]; simpa using h1
      linarith
    obtain ⟨hE4, hE6, hE2, hTau, hPhi0, hPhi2, hPhi8, hDelta, hInvDelta, hJ⟩ := hb w n hn hw t ht htle
    have hE4' : ‖E4Fun τ‖ ≤ Cg * s ^ Ng := by
      have h := hE4; rw [← hτdef, ← hsdef] at h; exact h
    have hPhi8' : ‖phi8 τ‖ ≤ Cg * s ^ Ng := by
      have h := hPhi8; rw [← hτdef, ← hsdef] at h; exact h
    have h288 : ‖288 - (E4Fun z - E2Fun z ^ 2) * jInvariantFun z‖
        ≤ Cjσ * s ^ (0:ℝ) * Real.exp ((-2:ℝ) * (Real.pi / t)) := by
      have h := hjzσ z hz3
      rw [qnorm_axis t ht, mul_comm] at h
      rw [norm_sub_rev]
      rw [hsdef, Real.rpow_zero, mul_one]
      exact h
    have hE4phi8 : ‖E4Fun τ * phi8 τ‖ ≤ Cg * Cg * s ^ (Ng + Ng) := mul_bound0 hs1 hE4' hPhi8'
    have hraw : ‖E4Fun τ * phi8 τ * (288 - (E4Fun z - E2Fun z ^ 2) * jInvariantFun z)‖
        ≤ (Cg * Cg) * Cjσ * s ^ ((Ng + Ng) + 0) * Real.exp ((0 + (-2)) * (Real.pi / t)) :=
      mul_bound hs1 (by simpa using hE4phi8) h288
    have htot : ‖6 * E4Fun τ * phi8 τ * (288 - (E4Fun z - E2Fun z ^ 2) * jInvariantFun z)‖
        ≤ (6 * Cg * Cg * Cjσ) * s ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) := by
      rw [show (6 : ℂ) * E4Fun τ * phi8 τ * (288 - (E4Fun z - E2Fun z ^ 2) * jInvariantFun z)
          = (6 : ℂ) * (E4Fun τ * phi8 τ * (288 - (E4Fun z - E2Fun z ^ 2) * jInvariantFun z)) by ring]
      exact const_weaken hs1 ht (by norm_num) (by positivity) hraw (le_of_eq (by ring_nf)) (by linarith) (by norm_num)
    rw [show 6 * E4Fun ((n : ℝ) +ᵥ w) * phi8 ((n : ℝ) +ᵥ w)
          * (288 - (E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) - E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2)
            * jInvariantFun (imagAxis t⁻¹ (inv_pos.mpr ht)))
        = 6 * E4Fun τ * phi8 τ * (288 - (E4Fun z - E2Fun z ^ 2) * jInvariantFun z) by
          rw [hτdef, hzdef]]
    exact htot
  have TC : ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
        ‖1728 * phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w) ^ 3
            * (5 * (E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) - E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2)
              - 2 * (E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2 - 1))‖
          ≤ (1728 * Cg * Cg * Cg * Cg * (5 * Cσ + 2 * C2m1)) * (scale w) ^ (4 * Ng + 1)
              * Real.exp (-(Real.pi / t)) := by
    intro w n hn hw t ht htle
    set s : ℝ := scale w with hsdef
    set τ : ℍ := (n : ℝ) +ᵥ w with hτdef
    set z : ℍ := imagAxis t⁻¹ (inv_pos.mpr ht) with hzdef
    have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; exact Work.Kernels.one_le_scale w
    have hz3 : (1 : ℝ) / 3 ≤ z.im := by
      rw [hzdef, imagAxis_im']
      have h1 : t ≤ 1 / 4 := by have h2 := Work.Asymptotics.tile_im_le_half hw; linarith
      have h3 : (4 : ℝ) ≤ t⁻¹ := by rw [le_inv_comm₀ (by norm_num : (0:ℝ) < 4) ht]; simpa using h1
      linarith
    obtain ⟨hE4, hE6, hE2, hTau, hPhi0, hPhi2, hPhi8, hDelta, hInvDelta, hJ⟩ := hb w n hn hw t ht htle
    have hE4' : ‖E4Fun τ‖ ≤ Cg * s ^ Ng := by
      have h := hE4; rw [← hτdef, ← hsdef] at h; exact h
    have hPhi0' : ‖phi0 τ‖ ≤ Cg * s ^ Ng := by
      have h := hPhi0; rw [← hτdef, ← hsdef] at h
      have hcoe : phiVec τ 1 = phi0 τ := rfl
      rwa [hcoe] at h
    have hσz : ‖E4Fun z - E2Fun z ^ 2‖ ≤ Cσ * s ^ (0:ℝ) * Real.exp ((-2:ℝ) * (Real.pi / t)) := by
      have h := hσ1 z hz3
      rw [qnorm_axis t ht] at h
      rw [hsdef, Real.rpow_zero, mul_one]
      exact h
    have h2m1z : ‖E2Fun z ^ 2 - 1‖ ≤ C2m1 * s ^ (0:ℝ) * Real.exp ((-2:ℝ) * (Real.pi / t)) := by
      have h := h2m1 z hz3
      rw [qnorm_axis t ht] at h
      rw [hsdef, Real.rpow_zero, mul_one]
      exact h
    have hE4sq : ‖E4Fun τ ^ 2‖ ≤ Cg * Cg * s ^ (Ng + Ng) := by
      rw [norm_pow]
      have h2 : ‖E4Fun τ‖ ^ 2 ≤ (Cg * s ^ Ng) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hE4' 2
      refine le_trans h2 (le_of_eq ?_)
      have hsN : (s ^ Ng) ^ 2 = s ^ (Ng + Ng) := by
        rw [pow_two, rpow_split (lt_of_lt_of_le one_pos hs1)]
      have hCsq : Cg ^ 2 = Cg * Cg := by ring
      calc (Cg * s ^ Ng) ^ 2 = Cg ^ 2 * (s ^ Ng) ^ 2 := by rw [mul_pow]
        _ = Cg * Cg * s ^ (Ng + Ng) := by rw [hsN, hCsq]
    have hE4cub : ‖E4Fun τ ^ 3‖ ≤ Cg * Cg * Cg * s ^ ((Ng + Ng) + Ng) := by
      have h := mul_bound0 hs1 hE4sq hE4'
      rw [show E4Fun τ ^ 3 = E4Fun τ ^ 2 * E4Fun τ by ring]
      exact h
    have hφ0E4cub : ‖phi0 τ * E4Fun τ ^ 3‖
        ≤ Cg * (Cg * Cg * Cg) * s ^ (Ng + ((Ng + Ng) + Ng)) := mul_bound0 hs1 hPhi0' hE4cub
    have hz5 : ‖5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1)‖
        ≤ (5 * Cσ + 2 * C2m1) * s ^ (0:ℝ) * Real.exp ((-2:ℝ) * (Real.pi / t)) := by
      have h1 := mul_le_mul_of_nonneg_left hσz (by norm_num : (0:ℝ) ≤ 5)
      have h2 := mul_le_mul_of_nonneg_left h2m1z (by norm_num : (0:ℝ) ≤ 2)
      have hnorm5 : ‖(5 : ℂ) * (E4Fun z - E2Fun z ^ 2)‖ = 5 * ‖E4Fun z - E2Fun z ^ 2‖ := by
        rw [norm_mul, Complex.norm_ofNat]
      have hnorm2 : ‖(2 : ℂ) * (E2Fun z ^ 2 - 1)‖ = 2 * ‖E2Fun z ^ 2 - 1‖ := by
        rw [norm_mul, Complex.norm_ofNat]
      calc ‖(5 : ℂ) * (E4Fun z - E2Fun z ^ 2) - (2 : ℂ) * (E2Fun z ^ 2 - 1)‖
          ≤ ‖(5 : ℂ) * (E4Fun z - E2Fun z ^ 2)‖ + ‖(2 : ℂ) * (E2Fun z ^ 2 - 1)‖ := norm_sub_le _ _
        _ = 5 * ‖E4Fun z - E2Fun z ^ 2‖ + 2 * ‖E2Fun z ^ 2 - 1‖ := by rw [hnorm5, hnorm2]
        _ ≤ 5 * (Cσ * s ^ (0:ℝ) * Real.exp ((-2:ℝ) * (Real.pi / t)))
              + 2 * (C2m1 * s ^ (0:ℝ) * Real.exp ((-2:ℝ) * (Real.pi / t))) := add_le_add h1 h2
        _ ≤ (5 * Cσ + 2 * C2m1) * s ^ (0:ℝ) * Real.exp ((-2:ℝ) * (Real.pi / t)) := by
          apply le_of_eq; ring_nf
    have hraw : ‖phi0 τ * E4Fun τ ^ 3
          * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1))‖
        ≤ (Cg * (Cg * Cg * Cg)) * (5 * Cσ + 2 * C2m1) * s ^ ((Ng + ((Ng + Ng) + Ng)) + 0)
          * Real.exp ((0 + (-2)) * (Real.pi / t)) := mul_bound hs1 (by simpa using hφ0E4cub) hz5
    have htot : ‖1728 * phi0 τ * E4Fun τ ^ 3
          * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1))‖
        ≤ (1728 * Cg * Cg * Cg * Cg * (5 * Cσ + 2 * C2m1)) * s ^ (4 * Ng + 1)
            * Real.exp (-(Real.pi / t)) := by
      rw [show (1728 : ℂ) * phi0 τ * E4Fun τ ^ 3
            * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1))
          = (1728 : ℂ) * (phi0 τ * E4Fun τ ^ 3
            * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1))) by ring]
      exact const_weaken hs1 ht (by norm_num) (by positivity) hraw (le_of_eq (by ring_nf)) (by linarith) (by norm_num)
    rw [show 1728 * phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w) ^ 3
          * (5 * (E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) - E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2)
            - 2 * (E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2 - 1))
        = 1728 * phi0 τ * E4Fun τ ^ 3
          * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1)) by rw [hτdef, hzdef]]
    exact htot
  have TD : ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
        ‖1728 * (((n : ℝ) +ᵥ w : UpperHalfPlane)) * E4Fun ((n : ℝ) +ᵥ w) ^ 2
            * E6Fun ((n : ℝ) +ᵥ w) * (E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2 - 1)‖
          ≤ (1728 * Cg * Cg * Cg * Cg * C2m1) * (scale w) ^ (4 * Ng + 1)
              * Real.exp (-(Real.pi / t)) := by
    intro w n hn hw t ht htle
    set s : ℝ := scale w with hsdef
    set τ : ℍ := (n : ℝ) +ᵥ w with hτdef
    set z : ℍ := imagAxis t⁻¹ (inv_pos.mpr ht) with hzdef
    have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; exact Work.Kernels.one_le_scale w
    have hz3 : (1 : ℝ) / 3 ≤ z.im := by
      rw [hzdef, imagAxis_im']
      have h1 : t ≤ 1 / 4 := by have h2 := Work.Asymptotics.tile_im_le_half hw; linarith
      have h3 : (4 : ℝ) ≤ t⁻¹ := by rw [le_inv_comm₀ (by norm_num : (0:ℝ) < 4) ht]; simpa using h1
      linarith
    obtain ⟨hE4, hE6, hE2, hTau, hPhi0, hPhi2, hPhi8, hDelta, hInvDelta, hJ⟩ := hb w n hn hw t ht htle
    have hE4' : ‖E4Fun τ‖ ≤ Cg * s ^ Ng := by
      have h := hE4; rw [← hτdef, ← hsdef] at h; exact h
    have hE6' : ‖E6Fun τ‖ ≤ Cg * s ^ Ng := by
      have h := hE6; rw [← hτdef, ← hsdef] at h; exact h
    have hTauE : ‖(τ : ℂ)‖ ≤ Cg * s ^ Ng := by
      have h := hTau; rw [← hτdef, ← hsdef] at h
      have hcoe : phiVec τ 0 = (τ : ℂ) := rfl
      rwa [hcoe] at h
    have h2m1z : ‖E2Fun z ^ 2 - 1‖ ≤ C2m1 * s ^ (0:ℝ) * Real.exp ((-2:ℝ) * (Real.pi / t)) := by
      have h := h2m1 z hz3
      rw [qnorm_axis t ht] at h
      rw [hsdef, Real.rpow_zero, mul_one]
      exact h
    have hE4sq : ‖E4Fun τ ^ 2‖ ≤ Cg * Cg * s ^ (Ng + Ng) := by
      rw [norm_pow]
      have h2 : ‖E4Fun τ‖ ^ 2 ≤ (Cg * s ^ Ng) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hE4' 2
      refine le_trans h2 (le_of_eq ?_)
      have hsN : (s ^ Ng) ^ 2 = s ^ (Ng + Ng) := by
        rw [pow_two, rpow_split (lt_of_lt_of_le one_pos hs1)]
      have hCsq : Cg ^ 2 = Cg * Cg := by ring
      calc (Cg * s ^ Ng) ^ 2 = Cg ^ 2 * (s ^ Ng) ^ 2 := by rw [mul_pow]
        _ = Cg * Cg * s ^ (Ng + Ng) := by rw [hsN, hCsq]
    have hτE4 : ‖(τ : ℂ) * E4Fun τ ^ 2‖ ≤ Cg * (Cg * Cg) * s ^ (Ng + (Ng + Ng)) :=
      mul_bound0 hs1 hTauE hE4sq
    have hτE4E6 : ‖(τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ‖
        ≤ (Cg * (Cg * Cg)) * Cg * s ^ ((Ng + (Ng + Ng)) + Ng) := mul_bound0 hs1 hτE4 hE6'
    have hraw : ‖(τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1)‖
        ≤ ((Cg * (Cg * Cg)) * Cg) * C2m1 * s ^ (((Ng + (Ng + Ng)) + Ng) + 0)
          * Real.exp ((0 + (-2)) * (Real.pi / t)) :=
      mul_bound hs1 (by simpa using hτE4E6) h2m1z
    have htot : ‖1728 * (τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1)‖
        ≤ (1728 * Cg * Cg * Cg * Cg * C2m1) * s ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) := by
      rw [show (1728 : ℂ) * (τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1)
          = (1728 : ℂ) * ((τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1)) by ring]
      exact const_weaken hs1 ht (by norm_num) (by positivity) hraw (le_of_eq (by ring_nf)) (by linarith) (by norm_num)
    rw [show 1728 * (((n : ℝ) +ᵥ w : UpperHalfPlane)) * E4Fun ((n : ℝ) +ᵥ w) ^ 2
          * E6Fun ((n : ℝ) +ᵥ w) * (E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2 - 1)
        = 1728 * (τ : ℂ) * E4Fun τ ^ 2 * E6Fun τ * (E2Fun z ^ 2 - 1) by rw [hτdef, hzdef]]
    exact htot
  have TE : ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
        ‖1728 * phi2 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w) * E6Fun ((n : ℝ) +ᵥ w)
            * (E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) - 1)‖
          ≤ (1728 * Cg * Cg * Cg * CE4m1) * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) := by
    intro w n hn hw t ht htle
    set s : ℝ := scale w with hsdef
    set τ : ℍ := (n : ℝ) +ᵥ w with hτdef
    set z : ℍ := imagAxis t⁻¹ (inv_pos.mpr ht) with hzdef
    have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; exact Work.Kernels.one_le_scale w
    have hz3 : (1 : ℝ) / 3 ≤ z.im := by
      rw [hzdef, imagAxis_im']
      have h1 : t ≤ 1 / 4 := by have h2 := Work.Asymptotics.tile_im_le_half hw; linarith
      have h3 : (4 : ℝ) ≤ t⁻¹ := by rw [le_inv_comm₀ (by norm_num : (0:ℝ) < 4) ht]; simpa using h1
      linarith
    obtain ⟨hE4, hE6, hE2, hTau, hPhi0, hPhi2, hPhi8, hDelta, hInvDelta, hJ⟩ := hb w n hn hw t ht htle
    have hE4' : ‖E4Fun τ‖ ≤ Cg * s ^ Ng := by
      have h := hE4; rw [← hτdef, ← hsdef] at h; exact h
    have hE6' : ‖E6Fun τ‖ ≤ Cg * s ^ Ng := by
      have h := hE6; rw [← hτdef, ← hsdef] at h; exact h
    have hPhi2' : ‖phi2 τ‖ ≤ Cg * s ^ Ng := by
      have h := hPhi2; rw [← hτdef, ← hsdef] at h
      have hcoe : phiVec τ 2 = phi2 τ := rfl
      rwa [hcoe] at h
    have hE4m1z : ‖E4Fun z - 1‖ ≤ CE4m1 * s ^ (0:ℝ) * Real.exp ((-2:ℝ) * (Real.pi / t)) := by
      have h := hE4m1 z hz3
      rw [qnorm_axis t ht] at h
      rw [hsdef, Real.rpow_zero, mul_one]
      exact h
    have hφ2E4 : ‖phi2 τ * E4Fun τ‖ ≤ Cg * Cg * s ^ (Ng + Ng) := mul_bound0 hs1 hPhi2' hE4'
    have hφ2E4E6 : ‖phi2 τ * E4Fun τ * E6Fun τ‖ ≤ (Cg * Cg) * Cg * s ^ ((Ng + Ng) + Ng) :=
      mul_bound0 hs1 hφ2E4 hE6'
    have hraw : ‖phi2 τ * E4Fun τ * E6Fun τ * (E4Fun z - 1)‖
        ≤ ((Cg * Cg) * Cg) * CE4m1 * s ^ (((Ng + Ng) + Ng) + 0)
          * Real.exp ((0 + (-2)) * (Real.pi / t)) :=
      mul_bound hs1 (by simpa using hφ2E4E6) hE4m1z
    have htot : ‖1728 * phi2 τ * E4Fun τ * E6Fun τ * (E4Fun z - 1)‖
        ≤ (1728 * Cg * Cg * Cg * CE4m1) * s ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) := by
      rw [show (1728 : ℂ) * phi2 τ * E4Fun τ * E6Fun τ * (E4Fun z - 1)
          = (1728 : ℂ) * (phi2 τ * E4Fun τ * E6Fun τ * (E4Fun z - 1)) by ring]
      exact const_weaken hs1 ht (by norm_num) (by positivity) hraw (le_of_eq (by ring_nf)) (by linarith) (by norm_num)
    rw [show 1728 * phi2 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w) * E6Fun ((n : ℝ) +ᵥ w)
          * (E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) - 1)
        = 1728 * phi2 τ * E4Fun τ * E6Fun τ * (E4Fun z - 1) by rw [hτdef, hzdef]]
    exact htot
  have TF : ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
        ‖1728 * phi0 ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)
            * (5 * E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2
              - 7 * E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht))
                * E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2
              + 2 * E6Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) * E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)))
            * E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2 / DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht))‖
          ≤ (1728 * Cg * Cg * Cσ * (B4 * B4) * cΔ⁻¹) * (scale w) ^ (4 * Ng + 1)
              * Real.exp (-(Real.pi / t)) := by
    intro w n hn hw t ht htle
    set s : ℝ := scale w with hsdef
    set τ : ℍ := (n : ℝ) +ᵥ w with hτdef
    set z : ℍ := imagAxis t⁻¹ (inv_pos.mpr ht) with hzdef
    have hs1 : (1 : ℝ) ≤ s := by rw [hsdef]; exact Work.Kernels.one_le_scale w
    have hz3 : (1 : ℝ) / 3 ≤ z.im := by
      rw [hzdef, imagAxis_im']
      have h1 : t ≤ 1 / 4 := by have h2 := Work.Asymptotics.tile_im_le_half hw; linarith
      have h3 : (4 : ℝ) ≤ t⁻¹ := by rw [le_inv_comm₀ (by norm_num : (0:ℝ) < 4) ht]; simpa using h1
      linarith
    obtain ⟨hE4, hE6, hE2, hTau, hPhi0, hPhi2, hPhi8, hDelta, hInvDelta, hJ⟩ := hb w n hn hw t ht htle
    have hPhi0' : ‖phi0 τ‖ ≤ Cg * s ^ Ng := by
      have h := hPhi0; rw [← hτdef, ← hsdef] at h
      have hcoe : phiVec τ 1 = phi0 τ := rfl
      rwa [hcoe] at h
    have hDelta' : ‖DeltaFun τ‖ ≤ Cg * s ^ Ng := by
      have h := hDelta; rw [← hτdef, ← hsdef] at h; exact h
    have hφ0Δ : ‖phi0 τ * DeltaFun τ‖ ≤ Cg * Cg * s ^ (Ng + Ng) := mul_bound0 hs1 hPhi0' hDelta'
    have hcombo : ‖5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z‖
        ≤ Cσ * s ^ (0:ℝ) * Real.exp ((-4:ℝ) * (Real.pi / t)) := by
      have h := hσ4 z hz3
      rw [sq_expansion t ht] at h
      rw [hsdef, Real.rpow_zero, mul_one]
      exact h
    have hE4zsq : ‖E4Fun z ^ 2‖ ≤ (B4 * B4) * s ^ (0:ℝ) := by
      rw [norm_pow, hsdef, Real.rpow_zero, mul_one]
      have h := pow_le_pow_left₀ (norm_nonneg _) (hE4zb z hz3) 2
      simpa [pow_two] using h
    have hΔzi : ‖(DeltaFun z)⁻¹‖ ≤ cΔ⁻¹ * s ^ (0:ℝ) * Real.exp (2 * (Real.pi / t)) := by
      have h := hΔlow z hz3
      rw [qnorm_axis t ht] at h
      have hpos : 0 < cΔ * Real.exp ((-2:ℝ) * (Real.pi / t)) := mul_pos hcΔ (Real.exp_pos _)
      have hΔzpos : 0 < ‖DeltaFun z‖ := lt_of_lt_of_le hpos h
      rw [norm_inv, hsdef, Real.rpow_zero, mul_one]
      calc (‖DeltaFun z‖)⁻¹ ≤ (cΔ * Real.exp ((-2:ℝ) * (Real.pi / t)))⁻¹ :=
            (inv_le_inv₀ hΔzpos hpos).mpr h
        _ = cΔ⁻¹ * Real.exp (2 * (Real.pi / t)) := by
            rw [mul_inv, ← Real.exp_neg]
            congr 1
            ring_nf
    have hcomboE4 : ‖(5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
          * E4Fun z ^ 2‖
        ≤ Cσ * (B4 * B4) * s ^ ((0:ℝ) + 0) * Real.exp ((-4 + 0) * (Real.pi / t)) :=
      mul_bound hs1 hcombo (by simpa using hE4zsq)
    have hcomboE4Δ : ‖(5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
          * E4Fun z ^ 2 * (DeltaFun z)⁻¹‖
        ≤ (Cσ * (B4 * B4)) * cΔ⁻¹ * s ^ (((0:ℝ) + 0) + 0)
          * Real.exp (((-4 + 0) + 2) * (Real.pi / t)) :=
      mul_bound hs1 hcomboE4 hΔzi
    have hraw : ‖phi0 τ * DeltaFun τ
          * ((5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
            * E4Fun z ^ 2 * (DeltaFun z)⁻¹)‖
        ≤ (Cg * Cg) * ((Cσ * (B4 * B4)) * cΔ⁻¹) * s ^ ((Ng + Ng) + (((0:ℝ) + 0) + 0))
          * Real.exp ((0 + ((-4 + 0) + 2)) * (Real.pi / t)) :=
      mul_bound hs1 (by simpa using hφ0Δ) hcomboE4Δ
    have htot : ‖1728 * phi0 τ * DeltaFun τ
          * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
          * E4Fun z ^ 2 / DeltaFun z‖
        ≤ (1728 * Cg * Cg * Cσ * (B4 * B4) * cΔ⁻¹) * s ^ (4 * Ng + 1)
            * Real.exp (-(Real.pi / t)) := by
      rw [show (1728 : ℂ) * phi0 τ * DeltaFun τ
            * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
            * E4Fun z ^ 2 / DeltaFun z
          = (1728 : ℂ) * (phi0 τ * DeltaFun τ
            * ((5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
              * E4Fun z ^ 2 * (DeltaFun z)⁻¹)) by
          rw [div_eq_mul_inv]; ring]
      exact const_weaken hs1 ht (by norm_num) (by positivity) hraw (le_of_eq (by ring_nf)) (by linarith) (by norm_num)
    rw [show 1728 * phi0 ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)
          * (5 * E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2
            - 7 * E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) * E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2
            + 2 * E6Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) * E2Fun (imagAxis t⁻¹ (inv_pos.mpr ht)))
          * E4Fun (imagAxis t⁻¹ (inv_pos.mpr ht)) ^ 2 / DeltaFun (imagAxis t⁻¹ (inv_pos.mpr ht))
        = 1728 * phi0 τ * DeltaFun τ
          * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
          * E4Fun z ^ 2 / DeltaFun z by rw [hτdef, hzdef]]
    exact htot
  refine ⟨6 * Cg * Cg * Cg * Cσ + 6 * Cg * Cg * Cjσ
      + 1728 * Cg * Cg * Cg * Cg * (5 * Cσ + 2 * C2m1) + 1728 * Cg * Cg * Cg * Cg * C2m1
      + 1728 * Cg * Cg * Cg * CE4m1 + 1728 * Cg * Cg * Cσ * (B4 * B4) * cΔ⁻¹,
    4 * Ng + 1, by positivity, hNf, ?_⟩
  intro w n hn hw t ht htle
  set z : ℍ := imagAxis t⁻¹ (inv_pos.mpr ht) with hzdef
  set A1 : ℂ := 6 * E4Fun ((n : ℝ) +ᵥ w) * phi8 ((n : ℝ) +ᵥ w) * (E4Fun z - E2Fun z ^ 2)
      * jInvariantFun ((n : ℝ) +ᵥ w) with hA1def
  set A2 : ℂ := 6 * E4Fun ((n : ℝ) +ᵥ w) * phi8 ((n : ℝ) +ᵥ w)
      * (288 - (E4Fun z - E2Fun z ^ 2) * jInvariantFun z) with hA2def
  set C1 : ℂ := 1728 * phi0 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w) ^ 3
      * (5 * (E4Fun z - E2Fun z ^ 2) - 2 * (E2Fun z ^ 2 - 1)) with hC1def
  set D1 : ℂ := 1728 * (((n : ℝ) +ᵥ w : UpperHalfPlane)) * E4Fun ((n : ℝ) +ᵥ w) ^ 2
      * E6Fun ((n : ℝ) +ᵥ w) * (E2Fun z ^ 2 - 1) with hD1def
  set E1 : ℂ := 1728 * phi2 ((n : ℝ) +ᵥ w) * E4Fun ((n : ℝ) +ᵥ w) * E6Fun ((n : ℝ) +ᵥ w)
      * (E4Fun z - 1) with hE1def
  set F1 : ℂ := 1728 * phi0 ((n : ℝ) +ᵥ w) * DeltaFun ((n : ℝ) +ᵥ w)
      * (5 * E4Fun z ^ 2 - 7 * E4Fun z * E2Fun z ^ 2 + 2 * E6Fun z * E2Fun z)
      * E4Fun z ^ 2 / DeltaFun z with hF1def
  have hΔne : DeltaFun ((n : ℝ) +ᵥ w) ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _
  have hΔzne : DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _
  have hc := Xi24_cancelled ((n : ℝ) +ᵥ w) z hΔne hΔzne
  have hc24 : Xi24 ((n : ℝ) +ᵥ w) z = A1 + A2 + C1 + D1 + E1 - F1 := by
    rw [hc, hA1def, hA2def, hC1def, hD1def, hE1def, hF1def]
    ring
  rw [hc24]
  have e1 : ‖A1‖ ≤ (6 * Cg * Cg * Cg * Cσ) * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) := by
    rw [hA1def]; exact TA1 w n hn hw t ht htle
  have e2 : ‖A2‖ ≤ (6 * Cg * Cg * Cjσ) * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) := by
    rw [hA2def]; exact TA2 w n hn hw t ht htle
  have e3 : ‖C1‖ ≤ (1728 * Cg * Cg * Cg * Cg * (5 * Cσ + 2 * C2m1)) * (scale w) ^ (4 * Ng + 1)
      * Real.exp (-(Real.pi / t)) := by
    rw [hC1def]; exact TC w n hn hw t ht htle
  have e4 : ‖D1‖ ≤ (1728 * Cg * Cg * Cg * Cg * C2m1) * (scale w) ^ (4 * Ng + 1)
      * Real.exp (-(Real.pi / t)) := by
    rw [hD1def]; exact TD w n hn hw t ht htle
  have e5 : ‖E1‖ ≤ (1728 * Cg * Cg * Cg * CE4m1) * (scale w) ^ (4 * Ng + 1)
      * Real.exp (-(Real.pi / t)) := by
    rw [hE1def]; exact TE w n hn hw t ht htle
  have e6 : ‖F1‖ ≤ (1728 * Cg * Cg * Cσ * (B4 * B4) * cΔ⁻¹) * (scale w) ^ (4 * Ng + 1)
      * Real.exp (-(Real.pi / t)) := by
    rw [hF1def, hzdef]; exact TF w n hn hw t ht htle
  calc ‖A1 + A2 + C1 + D1 + E1 - F1‖
      ≤ ‖A1‖ + ‖A2‖ + ‖C1‖ + ‖D1‖ + ‖E1‖ + ‖F1‖ := by
        have h1 := norm_sub_le (A1 + A2 + C1 + D1 + E1) F1
        have h2 := norm_add_le (A1 + A2 + C1 + D1) E1
        have h3 := norm_add_le (A1 + A2 + C1) D1
        have h4 := norm_add_le (A1 + A2) C1
        have h5 := norm_add_le A1 A2
        linarith
    _ ≤ (6 * Cg * Cg * Cg * Cσ) * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t))
          + (6 * Cg * Cg * Cjσ) * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t))
          + (1728 * Cg * Cg * Cg * Cg * (5 * Cσ + 2 * C2m1)) * (scale w) ^ (4 * Ng + 1)
              * Real.exp (-(Real.pi / t))
          + (1728 * Cg * Cg * Cg * Cg * C2m1) * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t))
          + (1728 * Cg * Cg * Cg * CE4m1) * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t))
          + (1728 * Cg * Cg * Cσ * (B4 * B4) * cΔ⁻¹) * (scale w) ^ (4 * Ng + 1)
              * Real.exp (-(Real.pi / t)) := by
        linarith [e1, e2, e3, e4, e5, e6]
    _ = (6 * Cg * Cg * Cg * Cσ + 6 * Cg * Cg * Cjσ
          + 1728 * Cg * Cg * Cg * Cg * (5 * Cσ + 2 * C2m1) + 1728 * Cg * Cg * Cg * Cg * C2m1
          + 1728 * Cg * Cg * Cg * CE4m1 + 1728 * Cg * Cg * Cσ * (B4 * B4) * cΔ⁻¹)
          * (scale w) ^ (4 * Ng + 1) * Real.exp (-(Real.pi / t)) := by ring

/-! ## The main tile bound -/

theorem Kplus_tile_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hdiv : ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
      (1 / 4 : ℝ) ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) *
        (Work.Kernels.jInvariantFun w -
          Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)))‖)
    (hjne : ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
      Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) ≠
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ C N K : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ K ∧
      ∀ (w : UpperHalfPlane) (n : ℤ), (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        ∀ (t : ℝ) (ht : 0 < t), t ≤ w.im / 2 →
          ‖Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
            ≤ C * (Work.Kernels.scale w) ^ N * (1 + t⁻¹) ^ K * Real.exp (-(Real.pi / t)) := by
  obtain ⟨C8, N8, hC8, hN8, hb8⟩ := Xi8_tile
  obtain ⟨C24, N24, hC24, hN24, hb24⟩ := Xi24_tile
  have hc8 : ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
  have hc24 : ((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) Complex.I_ne_zero
    · simp [Work.Kernels.c1728]
    · exact zpow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
  rcases hd with rfl | rfl
  · refine ⟨4 * C8 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖ + 1, N8, 0,
      by positivity, hN8, le_refl 0, ?_⟩
    intro w n hn hw t ht htle
    set z : ℍ := Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) with hzdef
    have hznorm : ‖(z : ℂ)‖ = t⁻¹ := by rw [hzdef]; exact z_norm t ht
    have hSW : ModularGroup.S • z = Work.Kernels.imagAxis t ht := by
      have h := Work.Asymptotics.imagAxis_smul_S t ht
      have h2 := congrArg (fun u => ModularGroup.S • u) h
      rw [Work.Asymptotics.S_smul_S_smul] at h2
      exact h2.symm
    have hjz : Work.Kernels.jInvariantFun z = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
      have h := Work.Kernels.KernelFacts.jInvariantFun_S_smul (Work.Kernels.imagAxis t ht)
      have h2 : ModularGroup.S • (Work.Kernels.imagAxis t ht) = z :=
        (Work.Asymptotics.imagAxis_smul_S t ht).trans hzdef.symm
      rw [h2] at h
      exact h
    have hjτ : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) = Work.Kernels.jInvariantFun w :=
      vadd_ne_of_vadd_one Work.Kernels.KernelFacts.jInvariantFun_vadd_one w hn
    have hne : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) ≠ Work.Kernels.jInvariantFun z := by
      rw [hjz]; exact hjne w n hn hw t ht htle
    have hDge : (1 / 4 : ℝ) ≤ ‖Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) - Work.Kernels.jInvariantFun z)‖ := by
      have h := hdiv w n hn hw t ht htle
      rw [← hzdef] at h
      rw [hjτ]
      exact h
    have hkey := Xi8_eq ((n : ℝ) +ᵥ w) z hne
    rw [hSW] at hkey
    have hz0 : (z : ℂ) ≠ 0 := fun hh => z.im_ne_zero (by rw [← UpperHalfPlane.coe_im z, hh]; simp)
    have hDne : Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) - Work.Kernels.jInvariantFun z) ≠ 0 :=
      mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) (sub_ne_zero.mpr hne)
    have hden : ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)
        * (Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
            - Work.Kernels.jInvariantFun z)) * (z : ℂ) ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero hc8 hDne) (pow_ne_zero 2 hz0)
    have hKdiv : Work.Kernels.KPlus 8 ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
        = Xi8 ((n : ℝ) +ᵥ w) z / (((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)
            * (Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
              - Work.Kernels.jInvariantFun z)) * (z : ℂ) ^ 2) := by
      rw [eq_div_iff hden]
      rw [← hkey]
      ring
    have hdennorm : ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)
        * (Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
          - Work.Kernels.jInvariantFun z)) * (z : ℂ) ^ 2‖
        = ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖
          * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
            - Work.Kernels.jInvariantFun z)‖ * (t⁻¹) ^ 2 := by
      rw [norm_mul, norm_mul, norm_pow, hznorm]
    have hKbound : ‖Work.Kernels.KPlus 8 ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
        ≤ ‖Xi8 ((n : ℝ) +ᵥ w) z‖
          * (4 * t ^ 2 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖) := by
      have hc8pos : 0 < ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖ := norm_pos_iff.mpr hc8
      have hDpos : 0 < ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
          - Work.Kernels.jInvariantFun z)‖ := lt_of_lt_of_le (by norm_num) hDge
      have hdenpos : 0 < ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖
          * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
            - Work.Kernels.jInvariantFun z)‖ * (t⁻¹) ^ 2 :=
        mul_pos (mul_pos hc8pos hDpos) (by positivity)
      have hT2 : t ^ 2 * (t⁻¹) ^ 2 = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt ht), one_pow]
      have h4 : 1 ≤ 4 * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
          - Work.Kernels.jInvariantFun z)‖ := by linarith
      have hrec : 1 / (‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖
            * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
              - Work.Kernels.jInvariantFun z)‖ * (t⁻¹) ^ 2)
          ≤ 4 * t ^ 2 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖ := by
        rw [div_le_div_iff₀ hdenpos hc8pos]
        have hE : (4 * t ^ 2) * (‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖
              * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
                - Work.Kernels.jInvariantFun z)‖ * (t⁻¹) ^ 2)
            = 4 * ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖
              * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
                - Work.Kernels.jInvariantFun z)‖ := by
          rw [show (4 * t ^ 2) * (‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖
                * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
                  - Work.Kernels.jInvariantFun z)‖ * (t⁻¹) ^ 2)
              = 4 * ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖
                * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
                  - Work.Kernels.jInvariantFun z)‖ * (t ^ 2 * (t⁻¹) ^ 2) by ring,
            hT2, mul_one]
        rw [hE]
        nlinarith [hc8pos.le, h4, norm_nonneg (Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) - Work.Kernels.jInvariantFun z))]
      rw [hKdiv, norm_div, hdennorm]
      calc ‖Xi8 ((n : ℝ) +ᵥ w) z‖ / (‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖
            * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
              - Work.Kernels.jInvariantFun z)‖ * (t⁻¹) ^ 2)
          = ‖Xi8 ((n : ℝ) +ᵥ w) z‖ * (1 / (‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖
              * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
                - Work.Kernels.jInvariantFun z)‖ * (t⁻¹) ^ 2)) := by ring
        _ ≤ ‖Xi8 ((n : ℝ) +ᵥ w) z‖
              * (4 * t ^ 2 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖) :=
            mul_le_mul_of_nonneg_left hrec (norm_nonneg _)
    have hXi := hb8 w n hn hw t ht htle
    have ht2le : t ^ 2 ≤ 1 := by
      have h1 := Work.Asymptotics.tile_im_le_half hw
      nlinarith [ht, htle, h1]
    have hmono : (C8 * (Work.Kernels.scale w) ^ N8 * Real.exp (-(Real.pi / t)))
          * (4 * t ^ 2 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖)
        ≤ (4 * C8 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖ + 1)
          * (Work.Kernels.scale w) ^ N8 * Real.exp (-(Real.pi / t)) := by
      have h1 : (C8 * (Work.Kernels.scale w) ^ N8 * Real.exp (-(Real.pi / t)))
            * (4 * t ^ 2 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖)
          = (4 * C8 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖)
            * (t ^ 2 * ((Work.Kernels.scale w) ^ N8 * Real.exp (-(Real.pi / t)))) := by ring
      rw [h1]
      have hS : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ N8 :=
        Real.rpow_nonneg (Work.Kernels.scale_pos w).le N8
      have h2 : t ^ 2 * ((Work.Kernels.scale w) ^ N8 * Real.exp (-(Real.pi / t)))
          ≤ 1 * ((Work.Kernels.scale w) ^ N8 * Real.exp (-(Real.pi / t))) :=
        mul_le_mul_of_nonneg_right ht2le (mul_nonneg hS (Real.exp_pos _).le)
      have h3 : (4 * C8 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖)
          ≤ 4 * C8 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖ + 1 := by linarith
      calc (4 * C8 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖)
            * (t ^ 2 * ((Work.Kernels.scale w) ^ N8 * Real.exp (-(Real.pi / t))))
          ≤ (4 * C8 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖)
            * (1 * ((Work.Kernels.scale w) ^ N8 * Real.exp (-(Real.pi / t)))) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ (4 * C8 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖ + 1)
              * (1 * ((Work.Kernels.scale w) ^ N8 * Real.exp (-(Real.pi / t)))) :=
            mul_le_mul_of_nonneg_right h3 (mul_nonneg zero_le_one (mul_nonneg hS (Real.exp_pos _).le))
        _ = (4 * C8 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖ + 1)
              * ((Work.Kernels.scale w) ^ N8 * Real.exp (-(Real.pi / t))) := by ring
        _ = (4 * C8 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖ + 1)
              * (Work.Kernels.scale w) ^ N8 * Real.exp (-(Real.pi / t)) := by ring
    calc ‖Work.Kernels.KPlus 8 ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
        ≤ ‖Xi8 ((n : ℝ) +ᵥ w) z‖
            * (4 * t ^ 2 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖) := hKbound
      _ ≤ (C8 * (Work.Kernels.scale w) ^ N8 * Real.exp (-(Real.pi / t)))
            * (4 * t ^ 2 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖) :=
          mul_le_mul_of_nonneg_right hXi (by positivity)
      _ ≤ (4 * C8 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖ + 1)
            * (Work.Kernels.scale w) ^ N8 * Real.exp (-(Real.pi / t)) := hmono
      _ = (4 * C8 / ‖((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖ + 1)
            * (Work.Kernels.scale w) ^ N8 * (1 + t⁻¹) ^ (0 : ℝ) * Real.exp (-(Real.pi / t)) := by
          simp only [Real.rpow_zero, mul_one]
  · refine ⟨4 * C24 / ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖ + 1,
      N24, 10, by positivity, hN24, by norm_num, ?_⟩
    intro w n hn hw t ht htle
    set z : ℍ := Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) with hzdef
    have hznorm : ‖(z : ℂ)‖ = t⁻¹ := by rw [hzdef]; exact z_norm t ht
    have hSW : ModularGroup.S • z = Work.Kernels.imagAxis t ht := by
      have h := Work.Asymptotics.imagAxis_smul_S t ht
      have h2 := congrArg (fun u => ModularGroup.S • u) h
      rw [Work.Asymptotics.S_smul_S_smul] at h2
      exact h2.symm
    have hjz : Work.Kernels.jInvariantFun z = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
      have h := Work.Kernels.KernelFacts.jInvariantFun_S_smul (Work.Kernels.imagAxis t ht)
      have h2 : ModularGroup.S • (Work.Kernels.imagAxis t ht) = z :=
        (Work.Asymptotics.imagAxis_smul_S t ht).trans hzdef.symm
      rw [h2] at h
      exact h
    have hjτ : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) = Work.Kernels.jInvariantFun w :=
      vadd_ne_of_vadd_one Work.Kernels.KernelFacts.jInvariantFun_vadd_one w hn
    have hne : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) ≠ Work.Kernels.jInvariantFun z := by
      rw [hjz]; exact hjne w n hn hw t ht htle
    have hDge : (1 / 4 : ℝ) ≤ ‖Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) - Work.Kernels.jInvariantFun z)‖ := by
      have h := hdiv w n hn hw t ht htle
      rw [← hzdef] at h
      rw [hjτ]
      exact h
    have hkey := Xi24_eq ((n : ℝ) +ᵥ w) z hne
    rw [hSW] at hkey
    have hz0 : (z : ℂ) ≠ 0 := fun hh => z.im_ne_zero (by rw [← UpperHalfPlane.coe_im z, hh]; simp)
    have hDne : Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) - Work.Kernels.jInvariantFun z) ≠ 0 :=
      mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) (sub_ne_zero.mpr hne)
    have hden : ((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)
        * (Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
            - Work.Kernels.jInvariantFun z)) * (z : ℂ) ^ 10 ≠ 0 :=
      mul_ne_zero (mul_ne_zero hc24 hDne) (pow_ne_zero 10 hz0)
    have hKdiv : Work.Kernels.KPlus 24 ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
        = Xi24 ((n : ℝ) +ᵥ w) z / (((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)
            * (Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
              - Work.Kernels.jInvariantFun z)) * (z : ℂ) ^ 10) := by
      rw [eq_div_iff hden]
      rw [← hkey]
      ring
    have hdennorm : ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)
        * (Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
          - Work.Kernels.jInvariantFun z)) * (z : ℂ) ^ 10‖
        = ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖
          * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
            - Work.Kernels.jInvariantFun z)‖ * (t⁻¹) ^ 10 := by
      rw [norm_mul, norm_mul, norm_pow, hznorm]
    have hKbound : ‖Work.Kernels.KPlus 24 ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
        ≤ ‖Xi24 ((n : ℝ) +ᵥ w) z‖ * (4 * t ^ 10
            / ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖) := by
      have hcpos : 0 < ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖ :=
        norm_pos_iff.mpr hc24
      have hDpos : 0 < ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
          - Work.Kernels.jInvariantFun z)‖ := lt_of_lt_of_le (by norm_num) hDge
      have hdenpos : 0 < ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖
          * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
            - Work.Kernels.jInvariantFun z)‖ * (t⁻¹) ^ 10 :=
        mul_pos (mul_pos hcpos hDpos) (by positivity)
      have hT10 : t ^ 10 * (t⁻¹) ^ 10 = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt ht), one_pow]
      have h4 : 1 ≤ 4 * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
          - Work.Kernels.jInvariantFun z)‖ := by linarith
      have hrec : 1 / (‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖
            * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
              - Work.Kernels.jInvariantFun z)‖ * (t⁻¹) ^ 10)
          ≤ 4 * t ^ 10
            / ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖ := by
        rw [div_le_div_iff₀ hdenpos hcpos]
        have hE : (4 * t ^ 10)
              * (‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖
              * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
                - Work.Kernels.jInvariantFun z)‖ * (t⁻¹) ^ 10)
            = 4 * ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖
              * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
                - Work.Kernels.jInvariantFun z)‖ := by
          rw [show (4 * t ^ 10) * (‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ)
                  * Complex.I)‖ * ‖Work.Kernels.DeltaFun z
                  * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) - Work.Kernels.jInvariantFun z)‖
                  * (t⁻¹) ^ 10)
              = 4 * ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖
                * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
                  - Work.Kernels.jInvariantFun z)‖ * (t ^ 10 * (t⁻¹) ^ 10) by ring,
            hT10, mul_one]
        rw [hE]
        nlinarith [hcpos.le, h4, norm_nonneg (Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) - Work.Kernels.jInvariantFun z))]
      rw [hKdiv, norm_div, hdennorm]
      calc ‖Xi24 ((n : ℝ) +ᵥ w) z‖ / (‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ)
              * Complex.I)‖ * ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) - Work.Kernels.jInvariantFun z)‖
              * (t⁻¹) ^ 10)
          = ‖Xi24 ((n : ℝ) +ᵥ w) z‖
            * (1 / (‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖
              * ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
                - Work.Kernels.jInvariantFun z)‖ * (t⁻¹) ^ 10)) := by ring
        _ ≤ ‖Xi24 ((n : ℝ) +ᵥ w) z‖ * (4 * t ^ 10
              / ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖) :=
            mul_le_mul_of_nonneg_left hrec (norm_nonneg _)
    have hXi := hb24 w n hn hw t ht htle
    have htle1 : t ≤ 1 := by
      have h1 := Work.Asymptotics.tile_im_le_half hw
      linarith
    have hpow : t ^ 10 ≤ (1 + t⁻¹) ^ (10 : ℝ) := by
      have h1 : t ^ 10 ≤ 1 := pow_le_one₀ ht.le htle1
      have h2 : (1 : ℝ) ≤ (1 + t⁻¹) ^ (10 : ℝ) :=
        Real.one_le_rpow (by linarith [inv_nonneg.mpr ht.le]) (by norm_num)
      linarith
    have hmono : (C24 * (Work.Kernels.scale w) ^ N24 * Real.exp (-(Real.pi / t)))
          * (4 * t ^ 10
            / ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖)
        ≤ (4 * C24 / ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖ + 1)
          * (Work.Kernels.scale w) ^ N24 * (1 + t⁻¹) ^ (10 : ℝ)
          * Real.exp (-(Real.pi / t)) := by
      have h1 : (C24 * (Work.Kernels.scale w) ^ N24 * Real.exp (-(Real.pi / t)))
            * (4 * t ^ 10
              / ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖)
          = (4 * C24 / ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖)
            * (t ^ 10 * ((Work.Kernels.scale w) ^ N24 * Real.exp (-(Real.pi / t)))) := by ring
      rw [h1]
      have hS : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ N24 :=
        Real.rpow_nonneg (Work.Kernels.scale_pos w).le N24
      have h2 : t ^ 10 * ((Work.Kernels.scale w) ^ N24 * Real.exp (-(Real.pi / t)))
          ≤ (1 + t⁻¹) ^ (10 : ℝ) * ((Work.Kernels.scale w) ^ N24 * Real.exp (-(Real.pi / t))) :=
        mul_le_mul_of_nonneg_right hpow (mul_nonneg hS (Real.exp_pos _).le)
      have h3 : (4 * C24 / ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ)
            * Complex.I)‖)
          ≤ 4 * C24 / ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖ + 1 := by
        linarith
      calc (4 * C24 / ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖)
            * (t ^ 10 * ((Work.Kernels.scale w) ^ N24 * Real.exp (-(Real.pi / t))))
          ≤ (4 * C24 / ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖)
            * ((1 + t⁻¹) ^ (10 : ℝ) * ((Work.Kernels.scale w) ^ N24
              * Real.exp (-(Real.pi / t)))) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ (4 * C24 / ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖ + 1)
              * ((1 + t⁻¹) ^ (10 : ℝ) * ((Work.Kernels.scale w) ^ N24
                * Real.exp (-(Real.pi / t)))) :=
            mul_le_mul_of_nonneg_right h3
              (mul_nonneg (Real.rpow_nonneg (by positivity) 10) (mul_nonneg hS (Real.exp_pos _).le))
        _ = (4 * C24 / ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖ + 1)
              * (Work.Kernels.scale w) ^ N24 * (1 + t⁻¹) ^ (10 : ℝ)
              * Real.exp (-(Real.pi / t)) := by ring
    calc ‖Work.Kernels.KPlus 24 ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
        ≤ ‖Xi24 ((n : ℝ) +ᵥ w) z‖ * (4 * t ^ 10
            / ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖) := hKbound
      _ ≤ (C24 * (Work.Kernels.scale w) ^ N24 * Real.exp (-(Real.pi / t)))
            * (4 * t ^ 10
              / ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖) :=
          mul_le_mul_of_nonneg_right hXi (by positivity)
      _ ≤ (4 * C24 / ‖((36 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)‖ + 1)
            * (Work.Kernels.scale w) ^ N24 * (1 + t⁻¹) ^ (10 : ℝ)
            * Real.exp (-(Real.pi / t)) := hmono

end

end Work.Asymptotics.Tile
