import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kplus8_tail_core
import Submission.Work.Asymptotics.KPlus_eight_decomposition
import Submission.Work.Asymptotics.DeltaFun_imagAxis_lower_sharp
import Submission.Work.Asymptotics.DeltaFun_funnel_lower_sharp
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.E_jdiff_large
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Asymptotics.tile_Bdd_atoms
import Submission.Work.Asymptotics.Xi8_bound_E
import Submission.Work.Asymptotics.Tile.tileDivisorLowerFar

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane
open Work.Kernels

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Elementary estimates (private helpers for `halfDevFar8High`) -/

private lemma hd8_exp_neg_two_pi_le_half : Real.exp (-(2 * Real.pi)) ≤ 1 / 2 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 : (2 : ℝ) ≤ (Real.exp 1) ^ 6 := by
    have h3 : (2.7 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 :=
      pow_le_pow_left₀ (by norm_num) (le_of_lt h1) 6
    have h4 : (2 : ℝ) ≤ (2.7 : ℝ) ^ 6 := by norm_num
    linarith
  have h5 : (Real.exp 1) ^ 6 = Real.exp 6 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h6 : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h7 : (2 : ℝ) ≤ Real.exp (2 * Real.pi) := by
    have h8 := Real.exp_le_exp.mpr h6
    rw [h5] at h2
    linarith
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) h7

/-! ## Multiplicative bookkeeping -/

private lemma hd8_mono {a b s : ℝ} {n m : ℝ} (hs : 1 ≤ s) (ha : 0 ≤ a) (hab : a ≤ b)
    (hnm : n ≤ m) : a * s ^ n ≤ b * s ^ m := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have h1 : s ^ n ≤ s ^ m := Real.rpow_le_rpow_of_exponent_le hs hnm
  calc a * s ^ n ≤ b * s ^ n := mul_le_mul_of_nonneg_right hab (Real.rpow_nonneg hs0.le n)
    _ ≤ b * s ^ m := mul_le_mul_of_nonneg_left h1 (le_trans ha hab)

private lemma hd8_mul_bd {A B : ℂ} {a b s t n n' m m' : ℝ} (hs : 0 < s) (ht : 0 < t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : ‖A‖ ≤ a * s ^ n * t ^ m)
    (hB : ‖B‖ ≤ b * s ^ n' * t ^ m') :
    ‖A * B‖ ≤ (a * b) * s ^ (n + n') * t ^ (m + m') := by
  rw [norm_mul]
  have h1 : (0:ℝ) ≤ a * s ^ n * t ^ m :=
    mul_nonneg (mul_nonneg ha (Real.rpow_nonneg hs.le n)) (Real.rpow_nonneg ht.le m)
  have h2 : (0:ℝ) ≤ b * s ^ n' * t ^ m' :=
    mul_nonneg (mul_nonneg hb (Real.rpow_nonneg hs.le n')) (Real.rpow_nonneg ht.le m')
  calc ‖A‖ * ‖B‖ ≤ (a * s ^ n * t ^ m) * (b * s ^ n' * t ^ m') :=
        mul_le_mul hA hB (norm_nonneg _) h1
    _ = (a * b) * s ^ (n + n') * t ^ (m + m') := by
        rw [Real.rpow_add hs, Real.rpow_add ht]; ring

private lemma hd8_add_bd {A B : ℂ} {a b s t n m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ‖A‖ ≤ a * s ^ n * t ^ m) (hB : ‖B‖ ≤ b * s ^ n * t ^ m) :
    ‖A + B‖ ≤ (a + b) * s ^ n * t ^ m := by
  refine le_trans (norm_add_le A B) ?_
  have h : a * s ^ n * t ^ m + b * s ^ n * t ^ m = (a + b) * s ^ n * t ^ m := by ring
  linarith [h]

/-- Additivity for the norms (used after `norm_sub_le`). -/
private lemma hd8_add_norm {A B : ℂ} {a b s t n m : ℝ} (hA : ‖A‖ ≤ a * s ^ n * t ^ m)
    (hB : ‖B‖ ≤ b * s ^ n * t ^ m) :
    ‖A‖ + ‖B‖ ≤ (a + b) * s ^ n * t ^ m := by
  have h : a * s ^ n * t ^ m + b * s ^ n * t ^ m = (a + b) * s ^ n * t ^ m := by ring
  linarith [hA, hB, h]

private lemma hd8_div_b0 {A B : ℂ} {a b s t : ℝ} {n m : ℝ} (hs : 0 < s) (ht : 0 < t)
    (ha : 0 ≤ a) (hb : 0 < b) (hB : b ≤ ‖B‖) (hA : ‖A‖ ≤ a * s ^ n * t ^ m) :
    ‖A / B‖ ≤ (a / b) * s ^ n * t ^ m := by
  have hBpos : 0 < ‖B‖ := lt_of_lt_of_le hb hB
  have hinv : ‖B⁻¹‖ ≤ 1 / b := by
    rw [norm_inv]
    simpa [one_div] using (inv_le_inv₀ hBpos hb).mpr hB
  rw [div_eq_mul_inv, norm_mul]
  calc ‖A‖ * ‖B⁻¹‖ ≤ (a * s ^ n * t ^ m) * (1 / b) :=
        mul_le_mul hA hinv (norm_nonneg _)
          (mul_nonneg (mul_nonneg ha (Real.rpow_nonneg hs.le n)) (Real.rpow_nonneg ht.le m))
    _ = (a / b) * s ^ n * t ^ m := by ring

/-- `‖1 - e^{2πi((S • w) - i t)}‖ ≥ 1/2` for `w ∈ E`, `t ≤ Im (S • w) - 1`. -/
private lemma hd8_one_sub_exp_ge_half {w : UpperHalfPlane} {t : ℝ}
    (hw : w ∈ Work.Asymptotics.KEpsilon) (htle : t ≤ (ModularGroup.S • w).im - 1) :
    (1 : ℝ) / 2 ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I *
        ((((ModularGroup.S • w : UpperHalfPlane)) : ℂ) - ((t : ℂ) * Complex.I)))‖ := by
  set Z : ℂ := Complex.exp (2 * Real.pi * Complex.I *
    ((((ModularGroup.S • w : UpperHalfPlane)) : ℂ) - ((t : ℂ) * Complex.I))) with hZdef
  have hnorm : ‖Z‖ = Real.exp (-(2 * Real.pi * ((ModularGroup.S • w).im - t))) := by
    rw [hZdef, Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_im,
      UpperHalfPlane.coe_re]
    norm_num
  have hle : ‖Z‖ ≤ Real.exp (-(2 * Real.pi)) := by
    rw [hnorm]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, htle])
  have hsub := norm_sub_norm_le (1 : ℂ) Z
  rw [norm_one, hnorm] at hsub
  linarith [hd8_exp_neg_two_pi_le_half]

/-- **The polynomial divisor lower bound at `τ = n +ᵥ w`.** -/
private lemma hd8_divisor_lower_tau :
    ∃ c : ℝ, 0 < c ∧ ∀ (w : ℍ) (n : ℤ) (z : ℍ) (t : ℝ),
      (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon → (z : ℂ) = (t : ℂ) * Complex.I →
      1 ≤ t → t ≤ (ModularGroup.S • w).im - 1 →
      c ≤ ‖DeltaFun (((n : ℝ) +ᵥ w : ℍ)) *
            (jInvariantFun (((n : ℝ) +ᵥ w : ℍ)) - jInvariantFun z)‖ := by
  obtain ⟨c₀, hc₀, hJ⟩ := Work.Asymptotics.E_jdiff_large
  refine ⟨c₀ / 4, by positivity, ?_⟩
  intro w n z t hn hw hz ht1 htle
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hzeq : z = imagAxis t ht := UpperHalfPlane.ext (by rw [hz]; rfl)
  have hjτ : jInvariantFun (((n : ℝ) +ᵥ w : ℍ)) = jInvariantFun w :=
    vadd_int_eq_self _ (fun τ => KernelFacts.jInvariantFun_vadd_one τ) n hn w
  have hΔτ : DeltaFun (((n : ℝ) +ᵥ w : ℍ)) = DeltaFun w :=
    vadd_int_eq_self _ (fun τ => KernelFacts.DeltaFun_vadd_one τ) n hn w
  set σ : ℍ := ModularGroup.S • w with hσ
  have hSlaw : DeltaFun w = (σ : ℂ) ^ 12 * DeltaFun σ := by
    rw [hσ]; exact Work.Asymptotics.DeltaFun_S_smul' w
  have hΔσ : (1 / 2) * Real.exp (-(2 * Real.pi * σ.im)) ≤ ‖DeltaFun σ‖ := by
    rw [hσ]; exact Work.Asymptotics.DeltaFun_funnel_lower_sharp hw.2
  have hσ2 : (2 : ℝ) ≤ ‖(σ : ℂ)‖ := by
    rw [hσ]; exact le_trans hw.2 (Work.Kernels.im_le_coe_norm _)
  have hJw : c₀ * Real.exp (2 * Real.pi * σ.im) * (1 / 2) ≤
      ‖jInvariantFun w - jInvariantFun (imagAxis t ht)‖ := by
    have h := hJ w t ht hw ht1
    have hZ := hd8_one_sub_exp_ge_half (w := w) hw htle
    have hc : (0 : ℝ) ≤ c₀ * Real.exp (2 * Real.pi * σ.im) := by positivity
    calc c₀ * Real.exp (2 * Real.pi * σ.im) * (1 / 2)
        ≤ c₀ * Real.exp (2 * Real.pi * σ.im) *
            ‖1 - Complex.exp (2 * Real.pi * Complex.I *
              ((((ModularGroup.S • w : UpperHalfPlane)) : ℂ) - ((t : ℂ) * Complex.I)))‖ :=
          mul_le_mul_of_nonneg_left hZ hc
      _ ≤ ‖jInvariantFun w - jInvariantFun (imagAxis t ht)‖ := h
  have hBC : c₀ / 4 ≤ ‖DeltaFun σ‖ * ‖jInvariantFun w - jInvariantFun (imagAxis t ht)‖ := by
    have h := mul_le_mul hΔσ hJw (by positivity) (norm_nonneg _)
    have heq : (1 / 2 * Real.exp (-(2 * Real.pi * σ.im))) *
        (c₀ * Real.exp (2 * Real.pi * σ.im) * (1 / 2)) = c₀ / 4 := by
      have hE : Real.exp (-(2 * Real.pi * σ.im)) * Real.exp (2 * Real.pi * σ.im) = 1 := by
        rw [← Real.exp_add,
          show -(2 * Real.pi * σ.im) + 2 * Real.pi * σ.im = 0 by ring, Real.exp_zero]
      rw [show (1 / 2 * Real.exp (-(2 * Real.pi * σ.im))) *
            (c₀ * Real.exp (2 * Real.pi * σ.im) * (1 / 2))
          = c₀ / 4 * (Real.exp (-(2 * Real.pi * σ.im))
              * Real.exp (2 * Real.pi * σ.im)) from by ring]
      rw [hE]; ring
    linarith [h, heq]
  have h1 : (1 : ℝ) ≤ ‖(σ : ℂ)‖ ^ 12 := by
    have h : (2 : ℝ) ^ 12 ≤ ‖(σ : ℂ)‖ ^ 12 := pow_le_pow_left₀ (by norm_num) hσ2 12
    norm_num at h; linarith
  rw [hjτ, hΔτ, hSlaw, hzeq]
  simp only [norm_mul, norm_pow]
  calc c₀ / 4 ≤ ‖DeltaFun σ‖ * ‖jInvariantFun w - jInvariantFun (imagAxis t ht)‖ := hBC
    _ ≤ ‖(σ : ℂ)‖ ^ 12
          * (‖DeltaFun σ‖ * ‖jInvariantFun w - jInvariantFun (imagAxis t ht)‖) :=
        le_mul_of_one_le_left (by positivity) h1
    _ = (‖(σ : ℂ)‖ ^ 12 * ‖DeltaFun σ‖)
          * ‖jInvariantFun w - jInvariantFun (imagAxis t ht)‖ := by ring

/-! ## The `τ`-atom bounds at `τ = n +ᵥ w` -/

private lemma hd8_tau_atoms :
    ∃ K N : ℝ, 0 < K ∧ 0 ≤ N ∧ ∀ (w : ℍ) (n : ℤ), (n = 1 ∨ n = -1) →
      w ∈ Work.Asymptotics.KEpsilon →
      ‖(((n : ℝ) +ᵥ w : ℍ) : ℂ) * E6Fun (((n : ℝ) +ᵥ w : ℍ))‖ ≤ K * (scale w) ^ N ∧
      ‖phi0 (((n : ℝ) +ᵥ w : ℍ)) * E4Fun (((n : ℝ) +ᵥ w : ℍ))‖ ≤ K * (scale w) ^ N ∧
      ‖phi2 (((n : ℝ) +ᵥ w : ℍ)) * E14Fun (((n : ℝ) +ᵥ w : ℍ))‖ ≤ K * (scale w) ^ N := by
  have hb1 := EtailE.Bdd.mul_zero (Bdd.vadd 1 (Or.inl rfl)) (Bdd.vadd_E6 1 (Or.inl rfl))
  have hb1' := EtailE.Bdd.mul_zero (Bdd.vadd (-1) (Or.inr rfl)) (Bdd.vadd_E6 (-1) (Or.inr rfl))
  have hb2 := EtailE.Bdd.mul_zero (Bdd.vadd_phi1 1 (Or.inl rfl)) (Bdd.vadd_E4 1 (Or.inl rfl))
  have hb2' := EtailE.Bdd.mul_zero (Bdd.vadd_phi1 (-1) (Or.inr rfl)) (Bdd.vadd_E4 (-1) (Or.inr rfl))
  have hb3 := EtailE.Bdd.mul_zero (Bdd.vadd_phi2 1 (Or.inl rfl)) (Bdd.vadd_E14 1 (Or.inl rfl))
  have hb3' := EtailE.Bdd.mul_zero (Bdd.vadd_phi2 (-1) (Or.inr rfl)) (Bdd.vadd_E14 (-1) (Or.inr rfl))
  obtain ⟨C1, N1, hC1, hN1, b1⟩ := EtailE.Bdd.exists_bound_zero hb1
  obtain ⟨C1', N1', hC1', hN1', b1'⟩ := EtailE.Bdd.exists_bound_zero hb1'
  obtain ⟨C2, N2, hC2, hN2, b2⟩ := EtailE.Bdd.exists_bound_zero hb2
  obtain ⟨C2', N2', hC2', hN2', b2'⟩ := EtailE.Bdd.exists_bound_zero hb2'
  obtain ⟨C3, N3, hC3, hN3, b3⟩ := EtailE.Bdd.exists_bound_zero hb3
  obtain ⟨C3', N3', hC3', hN3', b3'⟩ := EtailE.Bdd.exists_bound_zero hb3'
  refine ⟨C1 + C1' + C2 + C2' + C3 + C3' + 1, N1 + N1' + N2 + N2' + N3 + N3',
    by positivity, by linarith, ?_⟩
  intro w n hn hw
  have hs1 : (1 : ℝ) ≤ scale w := one_le_scale w
  rcases hn with h | h
  · subst h
    exact ⟨le_trans (b1 w hw) (hd8_mono hs1 hC1.le (by linarith) (by linarith)),
      le_trans (by simpa [phiVec] using b2 w hw)
        (hd8_mono hs1 hC2.le (by linarith) (by linarith)),
      le_trans (by simpa [phiVec] using b3 w hw)
        (hd8_mono hs1 hC3.le (by linarith) (by linarith))⟩
  · subst h
    exact ⟨le_trans (b1' w hw) (hd8_mono hs1 hC1'.le (by linarith) (by linarith)),
      le_trans (by simpa [phiVec] using b2' w hw)
        (hd8_mono hs1 hC2'.le (by linarith) (by linarith)),
      le_trans (by simpa [phiVec] using b3' w hw)
        (hd8_mono hs1 hC3'.le (by linarith) (by linarith))⟩

/-- **Far-region deviation of `K_+^{(8)}` on the cusp-`±1` tiles, `3 ≤ t`.**

For `w` in the cusp-`0` neighbourhood `E = KEpsilon`, `n = ±1` and `z = i t` with
`3 ≤ t ≤ Im (S • w) − 1` (strictly below the pole of `z ↦ K(n + w, z)` at height
`Im (S • w)`), the deviation of `K_+^{(8)}` from its cusp-`i∞` model `𝒢_+^{(8)}` is
polynomially bounded in `scale w` and `t`.

Route (all ingredients proved in the workspace):
* `Work.Asymptotics.KPlus_eight_decomposition` (import
  `Submission.Work.Asymptotics.KPlus_eight_decomposition`) expands `KPlus 8 τ z` as
  `tailC⁻¹(z²(τE₆(τ)−2φ₀(τ)E₄(τ)) + (φ₂(τ)E₁₄(τ)Δ(z)z² + Δ(τ)(τE₆(τ)E₈(z)φ̃₂(z) − 2φ₀(τ)E₄(τ)E₁₀(z)φ̃₁(z)))/(Δ(τ)Δ(z)(jτ−jz)))`,
  valid for `j τ ≠ j z`; alternatively `Work.Asymptotics.Compact.KPlus8_sub_Gplus8_decomp`
  with `Φ₁, Φ₂, Φ₃` as in `Submission/Work/Asymptotics/Compact/kplus8_tail_core.lean`;
* the two divisor lower bounds: `c ≤ ‖Δ(τ)(jτ − j z)‖` and
  `c·e^{2π(Im(S•w)−t)} ≤ ‖Δ(z)(jτ − j z)‖` for `τ = n +ᵥ w` (`j`, `Δ` are `T`-invariant, so
  `Δ(i t)(j τ − j z) = Δ(i t)(j w − j(i t))`), from
  `Work.Asymptotics.DeltaFun_imagAxis_lower_sharp` (`‖Δ(i t)‖ ≥ e^{−2πt}/2`),
  `Work.Asymptotics.E_jdiff_large` (`c₀ e^{2π Im(S•w)}‖1 − e^{2πi((S•w)−it)}‖ ≤ ‖j w − j(i t)‖`,
  with `‖1 − e^{2πi((S•w)−it)}‖ ≥ 1/2` because `t ≤ Im(S•w) − 1`),
  `Work.Asymptotics.DeltaFun_funnel_lower_sharp` (`‖Δ(σ)‖ ≥ e^{−2π Im σ}/2` for `Im σ ≥ 2`)
  and the `S`-law `Work.Asymptotics.DeltaFun_S_smul'`;
* the `τ`-atom bounds at `n +ᵥ w` from the `Work.Asymptotics.EtailE.Bdd` calculus
  (`Work.Asymptotics.Bdd.vadd`, `Bdd.vadd_E4`, `Bdd.vadd_E6`, `Bdd.vadd_E10`, `Bdd.vadd_E14`,
  `Bdd.vadd_phi1`, `Bdd.vadd_phi2`, `EtailE.Bdd.mul_zero`, `EtailE.Bdd.exists_bound_zero`;
  cf. `Submission/Work/Asymptotics/tile_Bdd_atoms.lean`; note `phiVec τ 1 = phi0 τ` and
  `phiVec τ 2 = phi2 τ` by `simp [Work.Kernels.phiVec]`);
* the `z`-atom bounds for `t ≥ 1` from `Work.Asymptotics.Compact.imagAxis_cusp_bounds`
  (`‖E₄(i t)‖,‖E₆(i t)‖ ≤ B`, `‖E₂(i t)−1‖,‖E₄(i t)−1‖,‖E₆(i t)−1‖,‖Δ(i t)‖ ≤ B·e^{−2πt}`,
  `‖φ̃₁(i t)‖,‖φ̃₂(i t)‖ ≤ B(1+t)²`), whence `‖E₈(i t)‖ ≤ B²`, `‖E₁₀(i t)‖ ≤ B²`.

Reorganise the `Φ₃`-piece as
`(Δ(z)jτ)/(Δ(z)(jτ−jz))·(τE₆(τ)φ̃₂(z) − 2φ₀(τ)E₄(τ)φ̃₁(z))` plus a term carrying
`(E₈(z)−E₄(z)³)` and `(E₁₀(z)−E₄(z)³)`, so that `Δ(z)jτ` is never bounded separately
(it is exponentially large); the factor `jτ/(jτ−jz)` is bounded by a constant, using
`Work.FunnelNumerics.E4_sub_one_le` (`‖E₄(σ)−1‖ ≤ 1/2` for `Im σ ≥ 2`),
`DeltaFun_funnel_lower_sharp` and `E_jdiff_large`.  The model `𝒢_+^{(8)}` is affine in `z`
(`Work.Asymptotics.Compact.Gplus8_eq_lin`) with `τ`-atom coefficients, hence also
`O((scale w)^N t^M)`. -/
theorem halfDevFar8High :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) (t : ℝ),
        (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
        (z : ℂ) = (t : ℂ) * Complex.I → 3 ≤ t → t ≤ (ModularGroup.S • w).im - 1 →
        ‖Work.Kernels.KPlus 8 ((n : ℝ) +ᵥ w) z
          - Work.Asymptotics.Compact.Gplus 8 ((n : ℝ) +ᵥ w) z‖
        ≤ C * (Work.Kernels.scale w) ^ N * t ^ M := by
  obtain ⟨K, N0, hKpos, hN0, hAtoms⟩ := hd8_tau_atoms
  obtain ⟨B, hB1, hZB⟩ := Compact.imagAxis_cusp_bounds
  obtain ⟨c1, hc1, hDiv1⟩ := hd8_divisor_lower_tau
  obtain ⟨c2, hc2, hDiv2⟩ := tileDivisorLowerFar
  have hB0 : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
  set cL : ℝ := 4 * (1 + B + 12 / Real.pi) with hcL
  have hcL0 : (0 : ℝ) < cL := by rw [hcL]; positivity
  set EE : ℝ := (B * (K * cL + (2 * K) * 4) + (K * 4) / c1)
      + ((K * (4 * B) + (2 * K) * (4 * B))
          + ((K * (4 * B)) * B ^ 2 + ((2 * K) * (4 * B)) * B ^ 2) / c2) with hEE
  have hEE0 : (0 : ℝ) ≤ EE := by rw [hEE]; positivity
  refine ⟨‖Compact.tailC⁻¹‖ * EE + 1, N0, 2, ?_, hN0, by norm_num, ?_⟩
  · have h1 : (0 : ℝ) ≤ ‖Compact.tailC⁻¹‖ * EE := mul_nonneg (norm_nonneg _) hEE0
    linarith
  · intro w n z t hn hw hz ht3 htle
    have ht0 : (0 : ℝ) < t := by linarith
    have ht1 : (1 : ℝ) ≤ t := by linarith
    have hs0 : (0 : ℝ) < scale w := scale_pos w
    have hs1 : (1 : ℝ) ≤ scale w := one_le_scale w
    set τ : ℍ := (n : ℝ) +ᵥ w with hτdef
    have hzeq : z = imagAxis t ht0 := UpperHalfPlane.ext (by rw [hz]; rfl)
    obtain ⟨hAtE6, hAtφ0E4, hAtφ2E14⟩ := hAtoms w n hn hw
    have hτE6 : ‖(τ:ℂ) * E6Fun τ‖ ≤ K * (scale w) ^ N0 * t ^ (0:ℝ) := by
      rw [hτdef]; simpa [Real.rpow_zero, mul_one] using hAtE6
    have hφ0E4 : ‖phi0 τ * E4Fun τ‖ ≤ K * (scale w) ^ N0 * t ^ (0:ℝ) := by
      rw [hτdef]; simpa [Real.rpow_zero, mul_one] using hAtφ0E4
    have hφ2E14 : ‖phi2 τ * E14Fun τ‖ ≤ K * (scale w) ^ N0 * t ^ (0:ℝ) := by
      rw [hτdef]; simpa [Real.rpow_zero, mul_one] using hAtφ2E14
    have hD1 : c1 ≤ ‖DeltaFun τ * (jInvariantFun τ - jInvariantFun z)‖ := by
      have h := hDiv1 w n z t hn hw hz ht1 htle
      rw [← hτdef] at h
      exact h
    have hD2 : c2 ≤ ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ := by
      have h := hDiv2 w n z t hn hw hz ht1 htle
      rw [← hτdef] at h
      exact h
    have hJsub : jInvariantFun τ - jInvariantFun z ≠ 0 := by
      intro h0
      rw [h0, mul_zero, norm_zero] at hD1
      linarith [hc1]
    have hJne : jInvariantFun τ ≠ jInvariantFun z := sub_ne_zero.mp hJsub
    have hdecomp := Compact.KPlus8_sub_Gplus8_decomp τ z hJne
    have hGplus : Compact.Gplus 8 τ z = Compact.Gplus8 τ z := by
      rw [Compact.Gplus]; simp
    have hinv1 : ‖(DeltaFun τ * (jInvariantFun τ - jInvariantFun z))⁻¹‖
        ≤ (1 / c1) * (scale w) ^ (0:ℝ) * t ^ (0:ℝ) := by
      rw [Real.rpow_zero, Real.rpow_zero, mul_one, mul_one]
      have hpos : 0 < ‖DeltaFun τ * (jInvariantFun τ - jInvariantFun z)‖ :=
        lt_of_lt_of_le hc1 hD1
      simpa [one_div] using (inv_le_inv₀ hpos hc1).mpr hD1
    have hinv2 : ‖(DeltaFun z * (jInvariantFun τ - jInvariantFun z))⁻¹‖
        ≤ (1 / c2) * (scale w) ^ (0:ℝ) * t ^ (0:ℝ) := by
      rw [Real.rpow_zero, Real.rpow_zero, mul_one, mul_one]
      have hpos : 0 < ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ :=
        lt_of_lt_of_le hc2 hD2
      simpa [one_div] using (inv_le_inv₀ hpos hc2).mpr hD2
    obtain ⟨hzE2m, hzE4m, hzE6m, hzDm, hzE2b, hzE4b, hzE6b, hzp1, hzp2⟩ := hZB t ht0 ht1
    have hzE2m' : ‖E2Fun z - 1‖ ≤ B * Real.exp (-(2 * Real.pi * t)) := by
      rw [hzeq]; exact hzE2m
    have hzE2b' : ‖E2Fun z‖ ≤ B := by rw [hzeq]; exact hzE2b
    have hzE4b' : ‖E4Fun z‖ ≤ B := by rw [hzeq]; exact hzE4b
    have hzE6b' : ‖E6Fun z‖ ≤ B := by rw [hzeq]; exact hzE6b
    have hzp1' : ‖phitVec z 1‖ ≤ B * (1 + t) ^ 2 := by rw [hzeq]; exact hzp1
    have hzp2' : ‖phitVec z 2‖ ≤ B * (1 + t) ^ 2 := by rw [hzeq]; exact hzp2
    have ht_sq : (1 + t) ^ 2 ≤ 4 * t ^ 2 := by nlinarith [ht1, sq_nonneg t]
    have hF0 : (0 : ℝ) ≤ (scale w) ^ N0 * t ^ (2:ℝ) :=
      mul_nonneg (Real.rpow_nonneg hs0.le N0) (Real.rpow_nonneg ht0.le 2)
    -- `Φ₁`
    have hE2z : ‖E2Fun z - 1‖ ≤ B * (scale w) ^ (0:ℝ) * t ^ (0:ℝ) := by
      rw [Real.rpow_zero, Real.rpow_zero, mul_one, mul_one]
      refine le_trans hzE2m' (mul_le_of_le_one_right hB0.le ?_)
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, ht0.le]
    have hPhiL : ‖Compact.PhiL z‖ ≤ cL * (scale w) ^ (0:ℝ) * t ^ (2:ℝ) := by
      rw [hcL, Real.rpow_zero, mul_one, Real.rpow_ofNat, Compact.PhiL]
      have h1 : ‖(z:ℂ)^2 * (1 + E2Fun z)‖ ≤ (1 + B) * (1 + t)^2 := by
        rw [norm_mul]
        have hA : ‖(z:ℂ)^2‖ ≤ (1 + t)^2 := by
          rw [norm_pow]
          have h2 : ‖(z:ℂ)‖ = t := by
            rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos ht0]
          rw [h2]; nlinarith [ht1, ht0.le]
        have hB : ‖(1:ℂ) + E2Fun z‖ ≤ 1 + B := by
          have h3 := norm_add_le (1:ℂ) (E2Fun z)
          rw [norm_one] at h3
          linarith [hzE2b']
        calc ‖(z:ℂ)^2‖ * ‖(1:ℂ) + E2Fun z‖ ≤ (1 + t)^2 * (1 + B) :=
              mul_le_mul hA hB (norm_nonneg _) (by positivity)
          _ = (1 + B) * (1 + t)^2 := by ring
      have h2 : ‖(12:ℂ) * Complex.I * (z:ℂ) / (Real.pi:ℂ)‖ ≤ (12 / Real.pi) * (1 + t)^2 := by
        rw [norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        have h2' : ‖(z:ℂ)‖ = t := by
          rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos ht0]
        rw [h2']
        have h4 : t ≤ (1 + t)^2 := by nlinarith [ht0.le]
        calc 12 * t / Real.pi = (12 / Real.pi) * t := by ring
          _ ≤ (12 / Real.pi) * (1 + t)^2 := mul_le_mul_of_nonneg_left h4 (by positivity)
      have hmain : ‖-((z:ℂ)^2 * (1 + E2Fun z)) + 12 * Complex.I * (z:ℂ) / (Real.pi:ℂ)‖
          ≤ (1 + B + 12 / Real.pi) * (4 * t^2) := by
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_neg]
        have hsum : (1 + B) * (1 + t)^2 + (12 / Real.pi) * (1 + t)^2
            = (1 + B + 12 / Real.pi) * (1 + t)^2 := by ring
        have hmono : (1 + B + 12 / Real.pi) * (1 + t)^2
            ≤ (1 + B + 12 / Real.pi) * (4 * t^2) :=
          mul_le_mul_of_nonneg_left ht_sq (by positivity)
        linarith [h1, h2, hsum, hmono]
      have heq : (1 + B + 12 / Real.pi) * (4 * t^2) = 4 * (1 + B + 12 / Real.pi) * t^2 := by ring
      linarith [hmain, heq]
    -- `z²`
    have hzsq : ‖(z:ℂ)^2‖ ≤ 4 * (scale w) ^ (0:ℝ) * t ^ (2:ℝ) := by
      rw [Real.rpow_zero, mul_one, norm_pow, Real.rpow_ofNat]
      have h2 : ‖(z:ℂ)‖ = t := by
        rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos ht0]
      rw [h2]; nlinarith [sq_nonneg t]
    have hP1 : ‖(τ:ℂ) * E6Fun τ * Compact.PhiL z‖
        ≤ (K * cL) * (scale w) ^ N0 * t ^ (2:ℝ) := by
      have h := hd8_mul_bd (s := scale w) (t := t) (n := N0) (m := 0) (n' := 0) (m' := 2)
        hs0 ht0 hKpos.le hcL0.le hτE6 hPhiL
      simpa using h
    have hP2a : ‖(2:ℂ) * (phi0 τ * E4Fun τ)‖ ≤ (2 * K) * (scale w) ^ N0 * t ^ (0:ℝ) := by
      have h2c : ‖(2:ℂ)‖ ≤ 2 * (scale w) ^ (0:ℝ) * t ^ (0:ℝ) := by
        rw [Complex.norm_ofNat, Real.rpow_zero, Real.rpow_zero, mul_one, mul_one]
      have h := hd8_mul_bd (s := scale w) (t := t) (n := 0) (m := 0) (n' := N0) (m' := 0)
        hs0 ht0 (by norm_num) hKpos.le h2c hφ0E4
      simpa using h
    have hP2 : ‖(2:ℂ) * (phi0 τ * E4Fun τ) * (z:ℂ)^2‖
        ≤ ((2 * K) * 4) * (scale w) ^ N0 * t ^ (2:ℝ) := by
      have h := hd8_mul_bd (s := scale w) (t := t) (n := N0) (m := 0) (n' := 0) (m' := 2)
        hs0 ht0 (by positivity) (by norm_num) hP2a hzsq
      simpa using h
    have hbr : ‖(τ:ℂ) * E6Fun τ * Compact.PhiL z + 2 * phi0 τ * E4Fun τ * (z:ℂ)^2‖
        ≤ (K * cL + (2 * K) * 4) * (scale w) ^ N0 * t ^ (2:ℝ) := by
      rw [show 2 * phi0 τ * E4Fun τ * (z:ℂ)^2
          = (2:ℂ) * (phi0 τ * E4Fun τ) * (z:ℂ)^2 from by ring]
      exact hd8_add_bd (by positivity) (by positivity) hP1 hP2
    have hPhiMain : ‖Compact.PhiMain τ z‖
        ≤ (B * (K * cL + (2 * K) * 4)) * (scale w) ^ N0 * t ^ (2:ℝ) := by
      rw [Compact.PhiMain_eq τ z]
      have h := hd8_mul_bd (s := scale w) (t := t) (n := 0) (m := 0) (n' := N0) (m' := 2)
        hs0 ht0 hB0.le (by positivity) hE2z hbr
      simpa using h
    -- `Φ₂`
    have hPhiDiv : ‖Compact.PhiDiv τ z‖ ≤ ((K * 4) / c1) * (scale w) ^ N0 * t ^ (2:ℝ) := by
      have hid : Compact.PhiDiv τ z = phi2 τ * E14Fun τ * (z:ℂ)^2
          * (DeltaFun τ * (jInvariantFun τ - jInvariantFun z))⁻¹ := by
        rw [show Compact.PhiDiv τ z = phi2 τ * E14Fun τ * (z:ℂ)^2
              / (DeltaFun τ * (jInvariantFun τ - jInvariantFun z)) from rfl, div_eq_mul_inv]
      rw [hid]
      have hnum : ‖phi2 τ * E14Fun τ * (z:ℂ)^2‖ ≤ (K * 4) * (scale w) ^ N0 * t ^ (2:ℝ) := by
        have h := hd8_mul_bd (s := scale w) (t := t) (n := N0) (m := 0) (n' := 0) (m' := 2)
          hs0 ht0 hKpos.le (by norm_num) hφ2E14 hzsq
        simpa using h
      exact hd8_div_b0 (s := scale w) (t := t) (n := N0) (m := 2)
        hs0 ht0 (by positivity) hc1 hD1 hnum
    -- `Φ₃`
    have hph2 : ‖phitVec z 2‖ ≤ (4 * B) * (scale w) ^ (0:ℝ) * t ^ (2:ℝ) := by
      rw [Real.rpow_zero, mul_one, Real.rpow_ofNat]
      calc ‖phitVec z 2‖ ≤ B * (1 + t)^2 := hzp2'
        _ ≤ B * (4 * t^2) := mul_le_mul_of_nonneg_left ht_sq hB0.le
        _ = 4 * B * t^2 := by ring
    have hph1 : ‖phitVec z 1‖ ≤ (4 * B) * (scale w) ^ (0:ℝ) * t ^ (2:ℝ) := by
      rw [Real.rpow_zero, mul_one, Real.rpow_ofNat]
      calc ‖phitVec z 1‖ ≤ B * (1 + t)^2 := hzp1'
        _ ≤ B * (4 * t^2) := mul_le_mul_of_nonneg_left ht_sq hB0.le
        _ = 4 * B * t^2 := by ring
    have hE8z : ‖E8Fun z‖ ≤ B ^ 2 * (scale w) ^ (0:ℝ) * t ^ (0:ℝ) := by
      rw [Real.rpow_zero, Real.rpow_zero, mul_one, mul_one, EtailE.E8_eq z, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hzE4b' 2
    have hE10z : ‖E10Fun z‖ ≤ B ^ 2 * (scale w) ^ (0:ℝ) * t ^ (0:ℝ) := by
      rw [Real.rpow_zero, Real.rpow_zero, mul_one, mul_one, EtailE.E10_eq z, norm_mul]
      calc ‖E4Fun z‖ * ‖E6Fun z‖ ≤ B * B := mul_le_mul hzE4b' hzE6b' (norm_nonneg _) hB0.le
        _ = B ^ 2 := by ring
    have hkey : Compact.PhiCorr τ z
        = ((τ:ℂ) * E6Fun τ * phitVec z 2 - 2 * phi0 τ * E4Fun τ * phitVec z 1)
          + ((τ:ℂ) * E6Fun τ * phitVec z 2 * E8Fun z
            - 2 * phi0 τ * E4Fun τ * phitVec z 1 * E10Fun z)
            * (DeltaFun z * (jInvariantFun τ - jInvariantFun z))⁻¹ := by
      have hΔzj : DeltaFun z * jInvariantFun τ
          = DeltaFun z * (jInvariantFun τ - jInvariantFun z) + E4Fun z ^ 3 := by
        rw [← Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun z]; ring
      have hz0 : DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
      have hD : DeltaFun z * (jInvariantFun τ - jInvariantFun z) ≠ 0 := mul_ne_zero hz0 hJsub
      have hnum : ((τ:ℂ) * E6Fun τ * phitVec z 2
            * (E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)
          - 2 * phi0 τ * E4Fun τ * phitVec z 1
            * (E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ))
          = (((τ:ℂ) * E6Fun τ * phitVec z 2 - 2 * phi0 τ * E4Fun τ * phitVec z 1)
              * (DeltaFun z * (jInvariantFun τ - jInvariantFun z)))
            + ((τ:ℂ) * E6Fun τ * phitVec z 2 * E8Fun z
              - 2 * phi0 τ * E4Fun τ * phitVec z 1 * E10Fun z) := by
        rw [hΔzj]
        simp only [EtailE.E8_eq, EtailE.E10_eq]
        ring
      rw [Compact.PhiCorr, hnum, div_eq_mul_inv, add_mul, mul_assoc,
        mul_inv_cancel₀ hD, mul_one]
    have hmod1 : ‖(τ:ℂ) * E6Fun τ * phitVec z 2‖
        ≤ (K * (4 * B)) * (scale w) ^ N0 * t ^ (2:ℝ) := by
      have h := hd8_mul_bd (s := scale w) (t := t) (n := N0) (m := 0) (n' := 0) (m' := 2)
        hs0 ht0 hKpos.le (by positivity) hτE6 hph2
      simpa using h
    have hmod2 : ‖(2:ℂ) * (phi0 τ * E4Fun τ) * phitVec z 1‖
        ≤ ((2 * K) * (4 * B)) * (scale w) ^ N0 * t ^ (2:ℝ) := by
      have h := hd8_mul_bd (s := scale w) (t := t) (n := N0) (m := 0) (n' := 0) (m' := 2)
        hs0 ht0 (by positivity) (by positivity) hP2a hph1
      simpa using h
    have hmod2' : ‖2 * phi0 τ * E4Fun τ * phitVec z 1‖
        ≤ ((2 * K) * (4 * B)) * (scale w) ^ N0 * t ^ (2:ℝ) := by
      rw [show 2 * phi0 τ * E4Fun τ * phitVec z 1
          = (2:ℂ) * (phi0 τ * E4Fun τ) * phitVec z 1 from by ring]
      exact hmod2
    have hmodel : ‖(τ:ℂ) * E6Fun τ * phitVec z 2 - 2 * phi0 τ * E4Fun τ * phitVec z 1‖
        ≤ (K * (4 * B) + (2 * K) * (4 * B)) * (scale w) ^ N0 * t ^ (2:ℝ) := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [← norm_neg (2 * phi0 τ * E4Fun τ * phitVec z 1)]
      have hneg : ‖-(2 * phi0 τ * E4Fun τ * phitVec z 1)‖
          ≤ ((2 * K) * (4 * B)) * (scale w) ^ N0 * t ^ (2:ℝ) := by
        rw [norm_neg]; exact hmod2'
      exact hd8_add_norm hmod1 hneg
    have hcor1 : ‖(τ:ℂ) * E6Fun τ * phitVec z 2 * E8Fun z‖
        ≤ ((K * (4 * B)) * B ^ 2) * (scale w) ^ N0 * t ^ (2:ℝ) := by
      have h := hd8_mul_bd (s := scale w) (t := t) (n := N0) (m := 2) (n' := 0) (m' := 0)
        hs0 ht0 (by positivity) (by positivity) hmod1 hE8z
      simpa using h
    have hcor2 : ‖(2:ℂ) * (phi0 τ * E4Fun τ) * phitVec z 1 * E10Fun z‖
        ≤ (((2 * K) * (4 * B)) * B ^ 2) * (scale w) ^ N0 * t ^ (2:ℝ) := by
      have h := hd8_mul_bd (s := scale w) (t := t) (n := N0) (m := 2) (n' := 0) (m' := 0)
        hs0 ht0 (by positivity) (by positivity) hmod2 hE10z
      simpa using h
    have hcor2' : ‖2 * phi0 τ * E4Fun τ * phitVec z 1 * E10Fun z‖
        ≤ (((2 * K) * (4 * B)) * B ^ 2) * (scale w) ^ N0 * t ^ (2:ℝ) := by
      rw [show 2 * phi0 τ * E4Fun τ * phitVec z 1 * E10Fun z
          = (2:ℂ) * (phi0 τ * E4Fun τ) * phitVec z 1 * E10Fun z from by ring]
      exact hcor2
    have hcorrnum : ‖(τ:ℂ) * E6Fun τ * phitVec z 2 * E8Fun z
          - 2 * phi0 τ * E4Fun τ * phitVec z 1 * E10Fun z‖
        ≤ ((K * (4 * B)) * B ^ 2 + ((2 * K) * (4 * B)) * B ^ 2) * (scale w) ^ N0 * t ^ (2:ℝ) := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [← norm_neg (2 * phi0 τ * E4Fun τ * phitVec z 1 * E10Fun z)]
      have hneg : ‖-(2 * phi0 τ * E4Fun τ * phitVec z 1 * E10Fun z)‖
          ≤ (((2 * K) * (4 * B)) * B ^ 2) * (scale w) ^ N0 * t ^ (2:ℝ) := by
        rw [norm_neg]; exact hcor2'
      exact hd8_add_norm hcor1 hneg
    have hcorr : ‖((τ:ℂ) * E6Fun τ * phitVec z 2 * E8Fun z
          - 2 * phi0 τ * E4Fun τ * phitVec z 1 * E10Fun z)
          * (DeltaFun z * (jInvariantFun τ - jInvariantFun z))⁻¹‖
        ≤ (((K * (4 * B)) * B ^ 2 + ((2 * K) * (4 * B)) * B ^ 2) / c2)
            * (scale w) ^ N0 * t ^ (2:ℝ) := by
      have h := hd8_mul_bd (s := scale w) (t := t) (n := N0) (m := 2) (n' := 0) (m' := 0)
        hs0 ht0 (by positivity) (by positivity) hcorrnum hinv2
      calc ‖((τ:ℂ) * E6Fun τ * phitVec z 2 * E8Fun z
            - 2 * phi0 τ * E4Fun τ * phitVec z 1 * E10Fun z)
            * (DeltaFun z * (jInvariantFun τ - jInvariantFun z))⁻¹‖
          ≤ (((K * (4 * B)) * B ^ 2 + ((2 * K) * (4 * B)) * B ^ 2) * (1 / c2))
              * (scale w) ^ N0 * t ^ (2:ℝ) := by simpa using h
        _ = (((K * (4 * B)) * B ^ 2 + ((2 * K) * (4 * B)) * B ^ 2) / c2)
              * (scale w) ^ N0 * t ^ (2:ℝ) := by ring
    have hPhiCorr : ‖Compact.PhiCorr τ z‖
        ≤ ((K * (4 * B) + (2 * K) * (4 * B))
            + ((K * (4 * B)) * B ^ 2 + ((2 * K) * (4 * B)) * B ^ 2) / c2)
            * (scale w) ^ N0 * t ^ (2:ℝ) := by
      rw [hkey]
      refine le_trans (norm_add_le _ _) ?_
      exact hd8_add_norm hmodel hcorr
    -- assembly
    have hsum : ‖Compact.PhiMain τ z + Compact.PhiDiv τ z + Compact.PhiCorr τ z‖
        ≤ EE * (scale w) ^ N0 * t ^ (2:ℝ) := by
      rw [hEE]
      have h12 : ‖Compact.PhiMain τ z + Compact.PhiDiv τ z‖
          ≤ (B * (K * cL + (2 * K) * 4) + (K * 4) / c1) * (scale w) ^ N0 * t ^ (2:ℝ) :=
        hd8_add_bd (by positivity) (by positivity) hPhiMain hPhiDiv
      exact hd8_add_bd (by positivity) (by positivity) h12 hPhiCorr
    have hgoal : ‖KPlus 8 τ z - Compact.Gplus 8 τ z‖
        ≤ (‖Compact.tailC⁻¹‖ * EE + 1) * (scale w) ^ N0 * t ^ (2:ℝ) := by
      rw [hGplus, hdecomp]
      have hconst : ‖Compact.tailC⁻¹‖ ≤ ‖Compact.tailC⁻¹‖ * (scale w) ^ (0:ℝ) * t ^ (0:ℝ) := by
        rw [Real.rpow_zero, Real.rpow_zero, mul_one, mul_one]
      have hmain := hd8_mul_bd (s := scale w) (t := t) (n := 0) (m := 0) (n' := N0) (m' := 2)
        hs0 ht0 (norm_nonneg _) (by positivity) hconst hsum
      have hmain' : ‖Compact.tailC⁻¹ * (Compact.PhiMain τ z + Compact.PhiDiv τ z
            + Compact.PhiCorr τ z)‖
          ≤ (‖Compact.tailC⁻¹‖ * EE) * (scale w) ^ N0 * t ^ (2:ℝ) := by
        simpa using hmain
      refine le_trans hmain' ?_
      have hcoef : (‖Compact.tailC⁻¹‖ * EE) * (scale w) ^ N0
          ≤ (‖Compact.tailC⁻¹‖ * EE + 1) * (scale w) ^ N0 :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hs0.le N0)
      exact mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg ht0.le 2)
    rw [hτdef] at hgoal
    exact hgoal


end

end Work.Asymptotics.Tile
