import Submission.FUP.HkBound

open MeasureTheory Metric Filter Set
open scoped Real BigOperators Topology ContDiff

set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# Section 4 of the paper, V: the derivative bound for `g_k`

This module proves the second half of estimate `eq:omega_reg_pieces`: for the correction term

`g_k(x) = (p_k)⁻¹ ψ_k(‖x‖)(q_k - h_k(x))`

one has `‖D^a g_k(x)‖ ≲ C_reg 2^{(1-a)k}` for `a ≤ 3` and `x` in the support annulus of `ω_k`.

Everything is expressed in natural powers of `P = 2^k`, which makes the arithmetic a matter of
`pow_add`/`inv_pow`: the factors are

* `|(p_k)⁻¹| ≤ (2p_1)⁻¹ P`                (`ModifyWeight.abs_inv_pk_le`),
* `‖D^i ψ_k‖ ≤ C_ψ (P⁻¹)^i`                (`WeightPiece.radialPsi_iteratedFDeriv_le`),
* `‖D^j h_k‖ ≤ C h (P^j)⁻¹`                (`norm_iteratedFDeriv_hk_le`),
* `|q_k| ≤ C h`                            (`abs_qk_le_regular`).
-/

/-- `(x⁻¹)^n = (x^n)⁻¹`. -/
lemma inv_pow_eq (x : ℝ) (n : ℕ) : (x⁻¹) ^ n = (x ^ n)⁻¹ := inv_pow x n

/-- **Derivative bound for `g_k`.** -/
lemma norm_iteratedFDeriv_gk_le (hd : 1 ≤ d) (k a : ℕ) (ha : a ≤ 3) (hk1 : 1 ≤ k)
    {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hcd : ContDiffOn ℝ 3 (gwin k w) (annOpen (d := d) k))
    {Creg Cinv Cp : ℝ} (hCinv : 0 < Cinv) (hCreg : 0 ≤ Creg) (hCp : 0 ≤ Cp)
    (hinv : ∀ n : ℕ, n ≤ 3 → ∀ x : ℝᵈ, x ≠ 0 →
      ‖iteratedFDeriv ℝ n (fun y : ℝᵈ => (‖y‖)⁻¹) x‖ ≤ Cinv * (‖x‖ ^ (n + 1))⁻¹)
    (hpiece : ∀ n : ℕ, n ≤ 3 → ∀ z : ℝᵈ,
      ‖iteratedFDeriv ℝ n (omegaPiece k w) z‖
        ≤ Creg * Cp * (2 : ℝ) ^ ((k : ℝ) * (1 - (n : ℝ))))
    {x : ℝᵈ} (hx : x ∈ annOpen (d := d) k) :
    ‖iteratedFDeriv ℝ a (gk k w) x‖
      ≤ (2 * pkConst)⁻¹ * rpsCps d * 512000 * 2 ^ a * Cinv * Creg * Cp
          * (2 : ℝ) ^ k * (((2 : ℝ) ^ k) ^ a)⁻¹ := by
  set U := annOpen (d := d) k with hUdef
  have hUopen : IsOpen U := isOpen_annOpen (d := d) k
  have hU : UniqueDiffOn ℝ U := hUopen.uniqueDiffOn
  set HkU : ℝᵈ → ℝ := fun y => (‖y‖)⁻¹ * gwin k w y with hHkU
  set QU : ℝᵈ → ℝ := fun y => qk k w - HkU y with hQU
  set AU : ℝᵈ → ℝ := fun y => radialPsi (d := d) k y * QU y with hAU
  set GkU : ℝᵈ → ℝ := fun y => (pk k)⁻¹ * AU y with hGkU
  -- `gk` and `GkU` agree on `U`
  have hEq : Set.EqOn (gk k w) GkU U := by
    intro y hy
    have h3 : hk k w y = hkW k w y := hk_eq_hkW k hk1 w hy
    have h4 : hkW k w y = (‖y‖)⁻¹ * gwin k w y := hkW_def k w y
    simp only [gk, hGkU, hAU, hQU, hHkU]
    rw [h3, h4]
    ring
  -- smoothness
  have hHkUcd : ContDiffOn ℝ 3 HkU U := by
    rw [hHkU]
    exact (contDiffOn_inv_norm_annOpen (d := d) k).mul hcd
  have hQcd : ContDiffOn ℝ 3 QU U := by
    rw [hQU]
    exact contDiffOn_const.sub hHkUcd
  have hAcd : ContDiffOn ℝ 3 AU U := by
    rw [hAU]
    exact (contDiff_radialPsi (d := d) k).contDiffOn.mul hQcd
  -- reduce to `AU`
  have hglob : iteratedFDeriv ℝ a (gk k w) x = iteratedFDerivWithin ℝ a (gk k w) U x :=
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (n := a) (f := gk k w) hUopen hx).symm
  have hstep1 : iteratedFDerivWithin ℝ a (gk k w) U x = iteratedFDerivWithin ℝ a GkU U x :=
    iteratedFDerivWithin_congr (𝕜 := ℝ) (E := ℝᵈ) (s := U) hEq hx a
  have hstep2 : iteratedFDerivWithin ℝ a GkU U x
      = (pk k)⁻¹ • iteratedFDerivWithin ℝ a AU U x := by
    have hsmul : GkU = (pk k)⁻¹ • AU := by
      rw [hGkU]
      funext y
      simp [smul_eq_mul]
    rw [hsmul]
    exact iteratedFDerivWithin_const_smul_apply (𝕜 := ℝ) (i := a) (a := (pk k)⁻¹)
      ((hAcd.contDiffWithinAt hx).of_le (by exact_mod_cast ha)) hU hx
  rw [hglob, hstep1, hstep2, norm_smul, Real.norm_eq_abs]
  -- Leibniz for `AU = ψ_k · QU`
  have hleib := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (E := ℝᵈ) (A := ℝ) (s := U)
    (f := radialPsi (d := d) k) (g := QU) (N := (3 : ℕ∞ω))
    (contDiff_radialPsi (d := d) k).contDiffOn hQcd hU hx (by exact_mod_cast ha)
  -- bound the summands
  have hterm : ∀ i ∈ Finset.range (a + 1),
      (a.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (radialPsi (d := d) k) U x‖ *
        ‖iteratedFDerivWithin ℝ (a - i) QU U x‖
      ≤ (a.choose i : ℝ) * (rpsCps d * (((2 : ℝ) ^ k)⁻¹) ^ i
          * (512000 * (Cinv * Creg * Cp) * (((2 : ℝ) ^ k)⁻¹) ^ (a - i))) := by
    intro i hi
    have hia : i ≤ a := by have := Finset.mem_range.mp hi; omega
    have hi3 : i ≤ 3 := by omega
    have hai3 : a - i ≤ 3 := by omega
    have hψ : ‖iteratedFDerivWithin ℝ i (radialPsi (d := d) k) U x‖
        ≤ rpsCps d * (((2 : ℝ) ^ k)⁻¹) ^ i := by
      rw [(iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (n := i) (f := radialPsi (d := d) k)
        hUopen) hx]
      exact radialPsi_iteratedFDeriv_le (d := d) i hi3 k hk1 x
    have hQ : ‖iteratedFDerivWithin ℝ (a - i) QU U x‖
        ≤ 512000 * (Cinv * Creg * Cp) * (((2 : ℝ) ^ k)⁻¹) ^ (a - i) := by
      rcases Nat.eq_zero_or_pos (a - i) with h0 | hpos
      · -- order `0`: pointwise bound
        rw [h0]
        have hq := abs_qk_le_regular (d := d) hd k hk1 hw hcd hCinv hCreg hCp hinv hpiece
        have hh := norm_iteratedFDeriv_hk_le (d := d) (k := k) (b := 0) (by norm_num) hk1
          hw hcd hCinv hCreg hCp hinv hpiece hx
        have hhk : |HkU x| ≤ 256000 * Cinv * Creg * Cp := by
          have h1 : hk k w x = HkU x := by
            rw [hk_eq_hkW k hk1 w hx, hkW_def, hHkU]
          have h2 : ‖hk k w x‖ ≤ 256000 * Cinv * Creg * Cp := by
            simpa [norm_iteratedFDeriv_zero] using hh
          rw [h1, Real.norm_eq_abs] at h2
          exact h2
        have hnorm : ‖iteratedFDerivWithin ℝ 0 QU U x‖ = |qk k w - HkU x| := by
          rw [norm_iteratedFDerivWithin_zero, Real.norm_eq_abs]
        calc ‖iteratedFDerivWithin ℝ 0 QU U x‖
            = |qk k w - HkU x| := hnorm
          _ ≤ |qk k w| + |HkU x| := abs_sub _ _
          _ ≤ 512000 * (Cinv * Creg * Cp) := by linarith
          _ = 512000 * (Cinv * Creg * Cp) * (((2 : ℝ) ^ k)⁻¹) ^ (0 : ℕ) := by
              rw [pow_zero, mul_one]
      · -- order `≥ 1`: the derivative of the constant drops out
        have hsub : iteratedFDerivWithin ℝ (a - i) QU U x
            = iteratedFDerivWithin ℝ (a - i) (fun _ : ℝᵈ => qk k w) U x
              - iteratedFDerivWithin ℝ (a - i) HkU U x := by
          rw [hQU]
          exact iteratedFDerivWithin_sub_apply (𝕜 := ℝ) (i := a - i)
            contDiffWithinAt_const
            ((hHkUcd.contDiffWithinAt hx).of_le (by exact_mod_cast hai3)) hU hx
        have hconst : iteratedFDerivWithin ℝ (a - i) (fun _ : ℝᵈ => qk k w) U x = 0 :=
          congrFun (iteratedFDerivWithin_const_of_ne hpos.ne' (qk k w) U) x
        have hHkU : iteratedFDerivWithin ℝ (a - i) HkU U x
            = iteratedFDerivWithin ℝ (a - i) (hk k w) U x := by
          refine iteratedFDerivWithin_congr (𝕜 := ℝ) (E := ℝᵈ) (s := U) ?_ hx (a - i)
          intro y hy
          rw [hHkU]
          exact ((hk_eq_hkW k hk1 w hy).trans (hkW_def k w y)).symm
        have hhk := norm_iteratedFDeriv_hk_le (d := d) (k := k) (b := a - i) hai3 hk1
          hw hcd hCinv hCreg hCp hinv hpiece hx
        rw [hsub, hconst, zero_sub, norm_neg, hHkU,
          (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (n := a - i) (f := hk k w) hUopen) hx]
        calc ‖iteratedFDeriv ℝ (a - i) (hk k w) x‖
            ≤ 256000 * Cinv * Creg * Cp * (((2 : ℝ) ^ k) ^ (a - i))⁻¹ := hhk
          _ = 256000 * Cinv * Creg * Cp * (((2 : ℝ) ^ k)⁻¹) ^ (a - i) := by
              rw [inv_pow_eq]
          _ ≤ 512000 * (Cinv * Creg * Cp) * (((2 : ℝ) ^ k)⁻¹) ^ (a - i) := by
              have hnn : (0 : ℝ) ≤ (((2 : ℝ) ^ k)⁻¹) ^ (a - i) := by positivity
              have h2 : (256000 : ℝ) * Cinv * Creg * Cp ≤ 512000 * (Cinv * Creg * Cp) := by
                nlinarith [mul_nonneg hCinv.le (mul_nonneg hCreg hCp)]
              exact mul_le_mul_of_nonneg_right h2 hnn
    have hchoose : (0 : ℝ) ≤ (a.choose i : ℝ) := by positivity
    calc (a.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (radialPsi (d := d) k) U x‖ *
          ‖iteratedFDerivWithin ℝ (a - i) QU U x‖
        = (a.choose i : ℝ) *
            (‖iteratedFDerivWithin ℝ i (radialPsi (d := d) k) U x‖ *
              ‖iteratedFDerivWithin ℝ (a - i) QU U x‖) := by ring
      _ ≤ (a.choose i : ℝ) * (rpsCps d * (((2 : ℝ) ^ k)⁻¹) ^ i
            * (512000 * (Cinv * Creg * Cp) * (((2 : ℝ) ^ k)⁻¹) ^ (a - i))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hψ hQ (by positivity)
              (mul_nonneg (rpsCps_pos d).le (by positivity))) hchoose
  have hsumle : (∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) *
        (rpsCps d * (((2 : ℝ) ^ k)⁻¹) ^ i
          * (512000 * (Cinv * Creg * Cp) * (((2 : ℝ) ^ k)⁻¹) ^ (a - i))))
      ≤ rpsCps d * (512000 * (Cinv * Creg * Cp)) * (((2 : ℝ) ^ k)⁻¹) ^ a * 2 ^ a := by
    refine le_of_eq ?_
    have h1 : (∑ i ∈ Finset.range (a + 1), ((a.choose i : ℝ) * (((2 : ℝ) ^ k)⁻¹) ^ i
          * (((2 : ℝ) ^ k)⁻¹) ^ (a - i))) = (((2 : ℝ) ^ k)⁻¹) ^ a * 2 ^ a := by
      have hfac : ∀ i ∈ Finset.range (a + 1), ((a.choose i : ℝ) * (((2 : ℝ) ^ k)⁻¹) ^ i
          * (((2 : ℝ) ^ k)⁻¹) ^ (a - i)) = (((2 : ℝ) ^ k)⁻¹) ^ a * (a.choose i : ℝ) := by
        intro i hi
        have hia : i ≤ a := by have := Finset.mem_range.mp hi; omega
        rw [mul_assoc, ← pow_add, show i + (a - i) = a by omega]
        ring
      rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
      congr 1
      rw [← Nat.cast_sum, Nat.sum_range_choose]
      norm_num
    calc (∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) *
            (rpsCps d * (((2 : ℝ) ^ k)⁻¹) ^ i
              * (512000 * (Cinv * Creg * Cp) * (((2 : ℝ) ^ k)⁻¹) ^ (a - i))))
        = rpsCps d * (512000 * (Cinv * Creg * Cp)) *
            (∑ i ∈ Finset.range (a + 1), ((a.choose i : ℝ) * (((2 : ℝ) ^ k)⁻¹) ^ i
              * (((2 : ℝ) ^ k)⁻¹) ^ (a - i))) := by
          have hrw : (∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) *
                (rpsCps d * (((2 : ℝ) ^ k)⁻¹) ^ i
                  * (512000 * (Cinv * Creg * Cp) * (((2 : ℝ) ^ k)⁻¹) ^ (a - i))))
              = ∑ i ∈ Finset.range (a + 1), rpsCps d * (512000 * (Cinv * Creg * Cp)) *
                  ((a.choose i : ℝ) * (((2 : ℝ) ^ k)⁻¹) ^ i
                    * (((2 : ℝ) ^ k)⁻¹) ^ (a - i)) :=
            Finset.sum_congr rfl fun i hi => by ring
          rw [hrw, ← Finset.mul_sum]
      _ = rpsCps d * (512000 * (Cinv * Creg * Cp)) * (((2 : ℝ) ^ k)⁻¹) ^ a * 2 ^ a := by
          rw [h1]; ring
  have hAUle : ‖iteratedFDerivWithin ℝ a AU U x‖
      ≤ ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) *
          (rpsCps d * (((2 : ℝ) ^ k)⁻¹) ^ i
            * (512000 * (Cinv * Creg * Cp) * (((2 : ℝ) ^ k)⁻¹) ^ (a - i))) :=
    le_trans hleib (Finset.sum_le_sum hterm)
  have hCnn : (0 : ℝ) ≤ rpsCps d * (512000 * (Cinv * Creg * Cp)) * (((2 : ℝ) ^ k)⁻¹) ^ a
      * 2 ^ a := by
    have hr : (0 : ℝ) < rpsCps d := rpsCps_pos d
    have h2 : (0 : ℝ) ≤ Cinv * Creg * Cp :=
      mul_nonneg (mul_nonneg hCinv.le hCreg) hCp
    have h3 : (0 : ℝ) ≤ (((2 : ℝ) ^ k)⁻¹) ^ a := by positivity
    have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ a := by positivity
    positivity
  calc |(pk k)⁻¹| * ‖iteratedFDerivWithin ℝ a AU U x‖
      ≤ |(pk k)⁻¹| * (rpsCps d * (512000 * (Cinv * Creg * Cp)) * (((2 : ℝ) ^ k)⁻¹) ^ a
          * 2 ^ a) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact le_trans hAUle hsumle
    _ ≤ (2 * pkConst)⁻¹ * (2 : ℝ) ^ k *
          (rpsCps d * (512000 * (Cinv * Creg * Cp)) * (((2 : ℝ) ^ k)⁻¹) ^ a * 2 ^ a) :=
        mul_le_mul_of_nonneg_right (abs_inv_pk_le k hk1) hCnn
    _ = (2 * pkConst)⁻¹ * rpsCps d * 512000 * 2 ^ a * Cinv * Creg * Cp
          * (2 : ℝ) ^ k * (((2 : ℝ) ^ k) ^ a)⁻¹ := by
        rw [inv_pow_eq]
        ring

end Submission.FUP
