import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Bracket24TailCore
import Submission.Work.Asymptotics.KhatE1Core.Bracket24E2PrimeDefs
import Submission.Work.Asymptotics.KhatE1Core.Bracket24BCoeffs
import Submission.Work.Asymptotics.KhatE1Core.Bracket24XtruncDefs
import Submission.Work.Asymptotics.KhatE1Core.XWrTreeDefs
import Submission.Work.Asymptotics.KhatE1Core.XWrTreeBounds
import Submission.Work.Asymptotics.KhatE1Core.DSm1RowBound
import Submission.Work.Asymptotics.KhatE1Core.KPlus24Refs
import Submission.Work.Asymptotics.KhatE1Core.StripAtoms
import Submission.Work.Asymptotics.KhatE1Core.invDeltaSecondOrder
import Submission.Work.Asymptotics.KhatE1Core.InvE4SecondOrder
import Submission.Work.Asymptotics.KhatE1Core.InvE4cubeFourthOrder
import Submission.Work.Asymptotics.KhatE1Core.ZDevRefined
import Submission.Work.Asymptotics.KhatE1.cusp_L_fourth
import Submission.Work.Asymptotics.KhatE1Core.Bracket24B4Bound_proof

namespace Work.Asymptotics.KhatE1Core
open UpperHalfPlane
open Work.Residues (Ept)
noncomputable section

lemma norm_Ept_sq_eq_q (z : ℍ) : ‖Ept z‖ ^ 2 = ‖Work.Kernels.qParamFun z‖ := by
  rw [← norm_pow, show (Ept z) ^ 2 = Work.Kernels.qParamFun z from
    (Work.Asymptotics.K24F.qParamFun_eq_Ept_sq' z).symm]

lemma zpow_mul_zpow_le {Q Qz : ℝ} (hQz0 : 0 < Qz) (hQzQ : Qz ≤ Q)
    (hQ1 : Q ≤ 1) {n k : ℤ} (hk : 2 ≤ k) (hnk : 2 ≤ n + k) :
    Q ^ n * Qz ^ k ≤ Qz ^ (2 : ℤ) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le hQz0 hQzQ
  have hQz1 : Qz ≤ 1 := le_trans hQzQ hQ1
  have hQzne : Qz ≠ 0 := ne_of_gt hQz0
  have hsplit : Qz ^ k = Qz ^ (k - 2) * Qz ^ (2 : ℤ) := by
    rw [← zpow_add₀ hQzne (k-2) 2]; congr 1; ring
  rw [hsplit]
  have hj0 : (0:ℤ) ≤ k - 2 := by omega
  have hQzk : Qz ^ (k - 2) ≤ Q ^ (k - 2) := by
    have h : (((k-2).toNat : ℤ)) = k - 2 := Int.toNat_of_nonneg hj0
    rw [← h, zpow_natCast, zpow_natCast]
    exact pow_le_pow_left₀ (le_of_lt hQz0) hQzQ _
  have h1 : Q ^ n * Qz ^ (k - 2) ≤ Q ^ n * Q ^ (k - 2) :=
    mul_le_mul_of_nonneg_left hQzk (zpow_nonneg (le_of_lt hQ0) n)
  have h2 : Q ^ n * Q ^ (k - 2) = Q ^ (n + k - 2) := by
    rw [← zpow_add₀ (ne_of_gt hQ0) n (k-2)]; congr 1; ring
  have h3 : Q ^ (n + k - 2) ≤ 1 := by
    have hj0' : (0:ℤ) ≤ n + k - 2 := by omega
    have h : (((n+k-2).toNat : ℤ)) = n + k - 2 := Int.toNat_of_nonneg hj0'
    rw [← h, zpow_natCast]
    exact pow_le_one₀ (le_of_lt hQ0) hQ1
  calc Q ^ n * (Qz ^ (k - 2) * Qz ^ (2 : ℤ))
      = (Q ^ n * Qz ^ (k - 2)) * Qz ^ (2 : ℤ) := by ring
    _ ≤ 1 * Qz ^ (2 : ℤ) := mul_le_mul_of_nonneg_right (le_trans h1 (h2 ▸ h3))
        (zpow_nonneg (le_of_lt hQz0) _)
    _ = Qz ^ (2 : ℤ) := by ring

def Bnd (f : ℍ → ℍ → ℂ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
      0 ≤ z.re → z.re ≤ 1 → z.im = t →
      ‖f τ z‖ ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)

lemma Bnd.of_Bound2 {f : ℍ → ℍ → ℂ} {n k : ℤ} (h : Bound2 f n k) (hk : 2 ≤ k)
    (hnk : 2 ≤ n + k) : Bnd f := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hQ0 : (0:ℝ) < ‖Work.Kernels.qParamFun τ‖ := norm_q_pos' τ
  have hQ1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := norm_q_le_one' hF
  have hE0 : (0:ℝ) ≤ ‖Ept z‖ := norm_nonneg _
  have hQz0 : (0:ℝ) < ‖Work.Kernels.qParamFun z‖ := norm_q_pos' z
  have hQzQ : ‖Work.Kernels.qParamFun z‖ ≤ ‖Work.Kernels.qParamFun τ‖ := qz_norm_le_qt hF ht hzim
  have hE2 : ‖Ept z‖ ^ 2 = ‖Work.Kernels.qParamFun z‖ := norm_Ept_sq_eq_q z
  have h4 : ‖Work.Kernels.qParamFun z‖ ^ 2 = ‖Ept z‖ ^ 4 := by
    rw [show (4:ℕ) = 2 * 2 by norm_num, pow_mul, ← hE2]
  have hQinv : (0:ℝ) ≤ (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 :=
    mul_nonneg (inv_nonneg.mpr (le_of_lt hQ0)) (pow_nonneg hE0 6)
  have key : ‖Work.Kernels.qParamFun τ‖ ^ n * ‖Work.Kernels.qParamFun z‖ ^ k
      ≤ (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4 :=
    le_trans (h4 ▸ zpow_mul_zpow_le hQz0 hQzQ hQ1 hk hnk) (le_add_of_nonneg_left hQinv)
  have hs0 : (0:ℝ) ≤ Work.Kernels.scale τ := (Work.Kernels.scale_pos τ).le
  have hu0 : (0:ℝ) ≤ 1 + t := by have := hF.2; linarith
  have hmain := hb τ z t hF ht hz0 hz1 hzim
  have hN0 : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ N := Real.rpow_nonneg hs0 N
  have hM0 : (0:ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg hu0 M
  have h2 : (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * (‖Work.Kernels.qParamFun τ‖ ^ n * ‖Work.Kernels.qParamFun z‖ ^ k)
      ≤ (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) :=
    mul_le_mul_of_nonneg_left key (mul_nonneg hN0 hM0)
  have h3 : C * (‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ‖Work.Kernels.qParamFun z‖ ^ k)
      ≤ C * ((Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)) := by
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    calc ‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * ‖Work.Kernels.qParamFun z‖ ^ k
        = (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * (‖Work.Kernels.qParamFun τ‖ ^ n * ‖Work.Kernels.qParamFun z‖ ^ k) := by ring
      _ ≤ _ := h2
  refine le_trans hmain ?_
  calc C * (‖Work.Kernels.qParamFun τ‖ ^ n * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ‖Work.Kernels.qParamFun z‖ ^ k)
      ≤ C * ((Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)) := h3
    _ = C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) := by ring

lemma Bnd.congr {f g : ℍ → ℍ → ℂ} (h : Bnd f) (hfg : ∀ τ z, f τ z = g τ z) : Bnd g := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  exact ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => by
    rw [← hfg τ z]; exact hb τ z t hF ht hz0 hz1 hzim⟩

lemma Bnd.add {f g : ℍ → ℍ → ℂ} (hf : Bnd f) (hg : Bnd g) :
    Bnd (fun τ z => f τ z + g τ z) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb1⟩ := hf
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := hg
  refine ⟨C1 + C2, max N1 N2, max M1 M2, by linarith,
    le_trans hN1 (le_max_left _ _), le_trans hM1 (le_max_left _ _),
    fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hs1 : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hu1 : (1:ℝ) ≤ 1 + t := by have := hF.2; linarith
  have hN0 : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ (max N1 N2) :=
    Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) _
  have hM0 : (0:ℝ) ≤ (1 + t) ^ (max M1 M2) := Real.rpow_nonneg (by linarith [hF.2]) _
  have hbr0 : (0:ℝ) ≤ (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4 :=
    add_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (pow_nonneg (norm_nonneg _) 6))
      (pow_nonneg (norm_nonneg _) 4)
  have hN1' : (Work.Kernels.scale τ) ^ N1 ≤ (Work.Kernels.scale τ) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
  have hM1' : (1 + t) ^ M1 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le hu1 (le_max_left _ _)
  have hN2' : (Work.Kernels.scale τ) ^ N2 ≤ (Work.Kernels.scale τ) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
  have hM2' : (1 + t) ^ M2 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le hu1 (le_max_right _ _)
  have e1 : C1 * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)
      ≤ C1 * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) := by
    have hstep : (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
        ≤ (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) :=
      mul_le_mul hN1' hM1' (Real.rpow_nonneg (by linarith [hF.2]) _)
        (Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) _)
    calc C1 * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)
        = C1 * ((Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1) * _ := by ring
      _ ≤ C1 * ((Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)) * _ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hC1.le) hbr0
      _ = C1 * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * _ := by ring
  have e2 : C2 * (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)
      ≤ C2 * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) := by
    have hstep : (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2
        ≤ (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) :=
      mul_le_mul hN2' hM2' (Real.rpow_nonneg (by linarith [hF.2]) _)
        (Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) _)
    calc C2 * (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)
        = C2 * ((Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2) * _ := by ring
      _ ≤ C2 * ((Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)) * _ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hC2.le) hbr0
      _ = C2 * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) * _ := by ring
  calc ‖f τ z + g τ z‖ ≤ ‖f τ z‖ + ‖g τ z‖ := norm_add_le _ _
    _ ≤ C1 * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)
        + C2 * (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) :=
        add_le_add (hb1 τ z t hF ht hz0 hz1 hzim) (hb2 τ z t hF ht hz0 hz1 hzim)
    _ ≤ (C1 + C2) * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) := by
        rw [add_mul]; linarith [e1, e2]

lemma Bnd.neg {f : ℍ → ℍ → ℂ} (hf : Bnd f) : Bnd (fun τ z => -f τ z) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := hf
  exact ⟨C, N, M, hC, hN, hM, fun τ z t hF ht hz0 hz1 hzim => by
    rw [norm_neg]; exact hb τ z t hF ht hz0 hz1 hzim⟩

lemma Bnd.sub {f g : ℍ → ℍ → ℂ} (hf : Bnd f) (hg : Bnd g) :
    Bnd (fun τ z => f τ z - g τ z) :=
  (hf.add hg.neg).congr (fun τ z => by ring)

/-! ## Triangle-inequality helpers -/

lemma norm_add3_le' (a b c : ℂ) : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have h1 : ‖a + b + c‖ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
  have h2 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
  linarith [h1, h2, norm_nonneg a, norm_nonneg b, norm_nonneg c]

lemma norm_add4_le' (a b c d : ℂ) : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h1 : ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
  have h2 := norm_add3_le' a b c
  linarith [h1, h2, norm_nonneg a, norm_nonneg b, norm_nonneg c, norm_nonneg d]

lemma norm_add5_le' (a b c d e : ℂ) :
    ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  have h1 : ‖a + b + c + d + e‖ ≤ ‖a + b + c + d‖ + ‖e‖ := norm_add_le _ _
  have h2 := norm_add4_le' a b c d
  linarith [h1, h2, norm_nonneg a, norm_nonneg b, norm_nonneg c, norm_nonneg d, norm_nonneg e]

lemma norm_add6_le' (a b c d e f : ℂ) :
    ‖a + b + c + d + e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  have h1 : ‖a + b + c + d + e + f‖ ≤ ‖a + b + c + d + e‖ + ‖f‖ := norm_add_le _ _
  have h2 := norm_add5_le' a b c d e
  linarith [h1, h2, norm_nonneg a, norm_nonneg b, norm_nonneg c, norm_nonneg d, norm_nonneg e,
    norm_nonneg f]

/-! ## Bound2 bounds for the truncated atoms -/

lemma B2_Ept : Bound2 (fun (_ : ℍ) (z : ℍ) => Ept z) 0 0 := by
  refine Bound2.of_le_qz (K := 0) (C := 1) (N := 0) (M := 0) (by norm_num) le_rfl le_rfl ?_
  intro τ z t hF ht hz0 hz1 hzim
  simpa using le_of_lt (Work.Residues.norm_Ept_lt_one z)

lemma B2_Ept3 : Bound2 (fun (_ : ℍ) (z : ℍ) => Ept z ^ 3) 0 1 := by
  refine Bound2.of_le_qz (K := 1) (C := 1) (N := 0) (M := 0) (by norm_num) le_rfl le_rfl ?_
  intro τ z t hF ht hz0 hz1 hzim
  have hE2 : ‖Ept z‖ ^ 2 = ‖Work.Kernels.qParamFun z‖ := norm_Ept_sq_eq_q z
  have hE1 : ‖Ept z‖ ≤ 1 := le_of_lt (Work.Residues.norm_Ept_lt_one z)
  have hE0 : (0:ℝ) ≤ ‖Ept z‖ := norm_nonneg _
  rw [norm_pow]
  have h3 : ‖Ept z‖ ^ 3 ≤ ‖Work.Kernels.qParamFun z‖ := by
    calc ‖Ept z‖ ^ 3 ≤ ‖Ept z‖ ^ 2 := pow_le_pow_of_le_one hE0 hE1 (by norm_num)
      _ = ‖Work.Kernels.qParamFun z‖ := hE2
  simpa using h3

lemma B2_Ept5 : Bound2 (fun (_ : ℍ) (z : ℍ) => Ept z ^ 5) 0 2 := by
  refine Bound2.of_le_qz (K := 2) (C := 1) (N := 0) (M := 0) (by norm_num) le_rfl le_rfl ?_
  intro τ z t hF ht hz0 hz1 hzim
  have hE2 : ‖Ept z‖ ^ 2 = ‖Work.Kernels.qParamFun z‖ := norm_Ept_sq_eq_q z
  have hE1 : ‖Ept z‖ ≤ 1 := le_of_lt (Work.Residues.norm_Ept_lt_one z)
  have hE0 : (0:ℝ) ≤ ‖Ept z‖ := norm_nonneg _
  rw [norm_pow]
  have h4 : ‖Ept z‖ ^ 4 = ‖Work.Kernels.qParamFun z‖ ^ 2 := by
    rw [show (4:ℕ) = 2*2 by norm_num, pow_mul, hE2]
  have h5 : ‖Ept z‖ ^ 5 ≤ ‖Work.Kernels.qParamFun z‖ ^ 2 :=
    calc ‖Ept z‖ ^ 5 ≤ ‖Ept z‖ ^ 4 := pow_le_pow_of_le_one hE0 hE1 (by norm_num)
      _ = ‖Work.Kernels.qParamFun z‖ ^ 2 := h4
  simpa using h5

lemma B2_E4T : Bound2 (fun (_ : ℍ) (z : ℍ) => E4T z) 0 0 :=
  Bound2_E4Ref.congr (fun τ z => by simp only [E4T, Tq, E4Ref])

lemma B2_E6T : Bound2 (fun (_ : ℍ) (z : ℍ) => E6T z) 0 0 := by
  refine Bound2.of_le_qz (K := 0) (C := 17137) (N := 0) (M := 0) (by norm_num) le_rfl le_rfl ?_
  intro τ z t hF ht hz0 hz1 hzim
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := qz_norm_le_one hF ht hzim
  have hq0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hkey : E6T z = 1 - 504 * Work.Kernels.qParamFun z
      - 16632 * (Work.Kernels.qParamFun z) ^ 2 := by simp only [E6T, Tq]
  rw [hkey]
  have h1 : ‖(1:ℂ) - 504 * Work.Kernels.qParamFun z - 16632 * (Work.Kernels.qParamFun z)^2‖
      ≤ 1 + 504 * ‖Work.Kernels.qParamFun z‖ + 16632 * ‖Work.Kernels.qParamFun z‖^2 := by
    calc ‖(1:ℂ) - 504 * Work.Kernels.qParamFun z - 16632 * (Work.Kernels.qParamFun z)^2‖
        ≤ ‖(1:ℂ) - 504 * Work.Kernels.qParamFun z‖
          + ‖16632 * (Work.Kernels.qParamFun z)^2‖ := norm_sub_le _ _
      _ ≤ (1 + 504 * ‖Work.Kernels.qParamFun z‖) + 16632 * ‖Work.Kernels.qParamFun z‖^2 := by
          refine add_le_add ?_ ?_
          · calc ‖(1:ℂ) - 504 * Work.Kernels.qParamFun z‖
                ≤ ‖(1:ℂ)‖ + ‖504 * Work.Kernels.qParamFun z‖ := norm_sub_le _ _
              _ = 1 + 504 * ‖Work.Kernels.qParamFun z‖ := by
                  rw [norm_one, norm_mul, Complex.norm_ofNat]
          · rw [norm_mul, norm_pow, Complex.norm_ofNat]
  refine le_trans h1 ?_
  have hb : 1 + 504 * ‖Work.Kernels.qParamFun z‖ + 16632 * ‖Work.Kernels.qParamFun z‖^2
      ≤ 17137 := by nlinarith [hq1, hq0]
  simpa using hb

lemma B2_E14T : Bound2 (fun (_ : ℍ) (z : ℍ) => E14T z) 0 0 :=
  Bound2_E14Ref.congr (fun τ z => by simp only [E14T, Tq, E14Ref])

lemma B2_E2ST : Bound2 (fun (_ : ℍ) (z : ℍ) => E2ST z) 0 0 :=
  Bound2_E2SRef.congr (fun τ z => by
    simp only [E2ST, Tq, E2SRef, Work.Asymptotics.K24F.S0, Work.Asymptotics.KhatE1.S0z])

lemma B2_I4T : Bound2 (fun (_ : ℍ) (z : ℍ) => invE4cubeT z) 0 0 :=
  Bound2_I4Ref.congr (fun τ z => by simp only [invE4cubeT, Tq, I4Ref])

lemma B2_DeltaT : Bound2 (fun (_ : ℍ) (z : ℍ) => DeltaT z) 0 1 := by
  refine Bound2.of_le_qz (K := 1) (C := 277) (N := 0) (M := 0) (by norm_num) le_rfl le_rfl ?_
  intro τ z t hF ht hz0 hz1 hzim
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := qz_norm_le_one hF ht hzim
  have hq0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hkey : DeltaT z = Work.Kernels.qParamFun z - 24 * (Work.Kernels.qParamFun z)^2
      + 252 * (Work.Kernels.qParamFun z)^3 := by simp only [DeltaT, Tq]
  rw [hkey]
  have h1 : ‖Work.Kernels.qParamFun z - 24 * (Work.Kernels.qParamFun z)^2
        + 252 * (Work.Kernels.qParamFun z)^3‖
      ≤ ‖Work.Kernels.qParamFun z‖ + 24 * ‖Work.Kernels.qParamFun z‖^2
        + 252 * ‖Work.Kernels.qParamFun z‖^3 := by
    calc _ ≤ ‖Work.Kernels.qParamFun z - 24 * (Work.Kernels.qParamFun z)^2‖
          + ‖252 * (Work.Kernels.qParamFun z)^3‖ := norm_add_le _ _
      _ ≤ (‖Work.Kernels.qParamFun z‖ + 24 * ‖Work.Kernels.qParamFun z‖^2)
          + 252 * ‖Work.Kernels.qParamFun z‖^3 := by
          refine add_le_add ?_ ?_
          · calc _ ≤ ‖Work.Kernels.qParamFun z‖ + ‖24 * (Work.Kernels.qParamFun z)^2‖ := norm_sub_le _ _
              _ = ‖Work.Kernels.qParamFun z‖ + 24 * ‖Work.Kernels.qParamFun z‖^2 := by
                  rw [norm_mul, norm_pow, Complex.norm_ofNat]
          · rw [norm_mul, norm_pow, Complex.norm_ofNat]
  refine le_trans h1 ?_
  have hb : ‖Work.Kernels.qParamFun z‖ + 24 * ‖Work.Kernels.qParamFun z‖^2
      + 252 * ‖Work.Kernels.qParamFun z‖^3 ≤ 277 * ‖Work.Kernels.qParamFun z‖ := by
    nlinarith [hq1, hq0]
  simpa using hb

lemma B2_invDeltaT : Bound2 (fun (_ : ℍ) (z : ℍ) => invDeltaT z) 0 (-1) := by
  refine ⟨349, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have hq0 : (0:ℝ) < ‖Work.Kernels.qParamFun z‖ := norm_q_pos' z
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := qz_norm_le_one hF ht hzim
  have hinv : (1:ℝ) ≤ (‖Work.Kernels.qParamFun z‖)⁻¹ := (one_le_inv₀ hq0).mpr hq1
  have h2 : ‖(Work.Kernels.qParamFun z)⁻¹ + 24 + 324 * Work.Kernels.qParamFun z‖
      ≤ 349 * (‖Work.Kernels.qParamFun z‖)⁻¹ := by
    calc ‖(Work.Kernels.qParamFun z)⁻¹ + 24 + 324 * Work.Kernels.qParamFun z‖
        ≤ ‖(Work.Kernels.qParamFun z)⁻¹‖ + ‖(24:ℂ)‖ + ‖324 * Work.Kernels.qParamFun z‖ :=
          norm_add3_le' _ _ _
      _ = (‖Work.Kernels.qParamFun z‖)⁻¹ + 24 + 324 * ‖Work.Kernels.qParamFun z‖ := by
          rw [norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_ofNat]
      _ ≤ 349 * (‖Work.Kernels.qParamFun z‖)⁻¹ := by nlinarith [hinv, hq1, hq0]
  have h4 : (‖Work.Kernels.qParamFun τ‖) ^ (0:ℤ) * (Work.Kernels.scale τ) ^ (0:ℝ)
      * (1 + t) ^ (0:ℝ) * (‖Work.Kernels.qParamFun z‖) ^ (-1:ℤ)
      = (‖Work.Kernels.qParamFun z‖)⁻¹ := by
    simp only [zpow_zero, zpow_neg_one, Real.rpow_zero, mul_one, one_mul]
  rw [show (fun (_ : ℍ) (z : ℍ) => invDeltaT z) τ z = invDeltaT z from rfl, invDeltaT, Tq]
  rw [h4]
  exact h2

lemma B2_invE4T : Bound2 (fun (_ : ℍ) (z : ℍ) => invE4T z) 0 0 := by
  refine Bound2.of_le_qz (K := 0) (C := 55681) (N := 0) (M := 0) (by norm_num) le_rfl le_rfl ?_
  intro τ z t hF ht hz0 hz1 hzim
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := qz_norm_le_one hF ht hzim
  have hq0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hkey : invE4T z = 1 - 240 * Work.Kernels.qParamFun z
      + 55440 * (Work.Kernels.qParamFun z) ^ 2 := by simp only [invE4T, Tq]
  rw [hkey]
  have h1 : ‖(1:ℂ) - 240 * Work.Kernels.qParamFun z + 55440 * (Work.Kernels.qParamFun z)^2‖
      ≤ 1 + 240 * ‖Work.Kernels.qParamFun z‖ + 55440 * ‖Work.Kernels.qParamFun z‖^2 := by
    calc _ ≤ ‖(1:ℂ) - 240 * Work.Kernels.qParamFun z‖
          + ‖55440 * (Work.Kernels.qParamFun z)^2‖ := norm_add_le _ _
      _ ≤ (1 + 240 * ‖Work.Kernels.qParamFun z‖) + 55440 * ‖Work.Kernels.qParamFun z‖^2 := by
          refine add_le_add ?_ ?_
          · calc _ ≤ ‖(1:ℂ)‖ + ‖240 * Work.Kernels.qParamFun z‖ := norm_sub_le _ _
              _ = 1 + 240 * ‖Work.Kernels.qParamFun z‖ := by rw [norm_one, norm_mul, Complex.norm_ofNat]
          · rw [norm_mul, norm_pow, Complex.norm_ofNat]
  refine le_trans h1 ?_
  have hb : 1 + 240 * ‖Work.Kernels.qParamFun z‖ + 55440 * ‖Work.Kernels.qParamFun z‖^2
      ≤ 55681 := by nlinarith [hq1, hq0]
  simpa using hb

lemma B2_qinv : Bound2 (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.qParamFun z)⁻¹) 0 (-1) := by
  refine ⟨1, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hF ht hz0 hz1 hzim => ?_⟩
  have h : (‖Work.Kernels.qParamFun z‖)⁻¹
      ≤ (1:ℝ) * ((‖Work.Kernels.qParamFun τ‖) ^ (0:ℤ) * (Work.Kernels.scale τ) ^ (0:ℝ)
          * (1 + t) ^ (0:ℝ) * (‖Work.Kernels.qParamFun z‖) ^ (-1:ℤ)) := by
    simp only [zpow_zero, zpow_neg_one, Real.rpow_zero, mul_one, one_mul, le_refl]
  simp only [norm_inv]
  exact h

lemma B2_WT : Bound2 (fun (_ : ℍ) (z : ℍ) => WT z) 0 0 := by
  refine Bound2.of_le_qz (K := 0) (C := 137) (N := 0) (M := 0) (by norm_num) le_rfl le_rfl ?_
  intro τ z t hF ht hz0 hz1 hzim
  have hE1 : ‖Ept z‖ ≤ 1 := le_of_lt (Work.Residues.norm_Ept_lt_one z)
  have hE0 : (0:ℝ) ≤ ‖Ept z‖ := norm_nonneg _
  have hkey : WT z = (1:ℂ) + (-(8:ℂ)) * Ept z + (24:ℂ) * (Ept z)^2
      + (-(32:ℂ)) * (Ept z)^3 + (24:ℂ) * ((Ept z)^2)^2 + (-(48:ℂ)) * (Ept z)^5 := by
    simp only [WT, Tq, Te, Work.Asymptotics.K24F.qParamFun_eq_Ept_sq']
    ring
  rw [hkey]
  have t2 : ‖(-(8:ℂ)) * Ept z‖ = 8 * ‖Ept z‖ := by rw [norm_mul, norm_neg, Complex.norm_ofNat]
  have t3 : ‖(24:ℂ) * (Ept z)^2‖ = 24 * ‖Ept z‖^2 := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
  have t4 : ‖(-(32:ℂ)) * (Ept z)^3‖ = 32 * ‖Ept z‖^3 := by
    rw [norm_mul, norm_neg, norm_pow, Complex.norm_ofNat]
  have t5 : ‖(24:ℂ) * ((Ept z)^2)^2‖ = 24 * (‖Ept z‖^2)^2 := by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_ofNat]
  have t6 : ‖(-(48:ℂ)) * (Ept z)^5‖ = 48 * ‖Ept z‖^5 := by
    rw [norm_mul, norm_neg, norm_pow, Complex.norm_ofNat]
  refine le_trans (norm_add6_le' _ _ _ _ _ _) ?_
  rw [norm_one, t2, t3, t4, t5, t6]
  have : 1 + 8 * ‖Ept z‖ + 24 * ‖Ept z‖^2 + 32 * ‖Ept z‖^3
      + 24 * (‖Ept z‖^2)^2 + 48 * ‖Ept z‖^5 ≤ 137 := by
    have h2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ hE0 hE1
    have h3 : ‖Ept z‖ ^ 3 ≤ 1 := pow_le_one₀ hE0 hE1
    have h4 : (‖Ept z‖ ^ 2)^2 ≤ 1 := pow_le_one₀ (pow_nonneg hE0 2) h2
    have h5 : ‖Ept z‖ ^ 5 ≤ 1 := pow_le_one₀ hE0 hE1
    nlinarith [hE1, h2, h3, h4, h5, hE0]
  simpa using this

lemma B2_D2T : Bound2 (fun (_ : ℍ) (z : ℍ) => D2T z) 0 0 := by
  refine Bound2.of_le_qz (K := 0) (C := 3537) (N := 0) (M := 0) (by norm_num) le_rfl le_rfl ?_
  intro τ z t hF ht hz0 hz1 hzim
  have hE1 : ‖Ept z‖ ≤ 1 := le_of_lt (Work.Residues.norm_Ept_lt_one z)
  have hE0 : (0:ℝ) ≤ ‖Ept z‖ := norm_nonneg _
  have hkey : D2T z = (1:ℂ) + (16:ℂ) * Ept z + (-(144:ℂ)) * (Ept z)^2
      + (448:ℂ) * (Ept z)^3 + (-(912:ℂ)) * ((Ept z)^2)^2 + (2016:ℂ) * (Ept z)^5 := by
    simp only [D2T, Tq, Te, Work.Asymptotics.K24F.qParamFun_eq_Ept_sq']
    ring
  rw [hkey]
  have t2 : ‖(16:ℂ) * Ept z‖ = 16 * ‖Ept z‖ := by rw [norm_mul, Complex.norm_ofNat]
  have t3 : ‖(-(144:ℂ)) * (Ept z)^2‖ = 144 * ‖Ept z‖^2 := by
    rw [norm_mul, norm_neg, norm_pow, Complex.norm_ofNat]
  have t4 : ‖(448:ℂ) * (Ept z)^3‖ = 448 * ‖Ept z‖^3 := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
  have t5 : ‖(-(912:ℂ)) * ((Ept z)^2)^2‖ = 912 * (‖Ept z‖^2)^2 := by
    rw [norm_mul, norm_neg, norm_pow, norm_pow, Complex.norm_ofNat]
  have t6 : ‖(2016:ℂ) * (Ept z)^5‖ = 2016 * ‖Ept z‖^5 := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
  refine le_trans (norm_add6_le' _ _ _ _ _ _) ?_
  rw [norm_one, t2, t3, t4, t5, t6]
  have : 1 + 16 * ‖Ept z‖ + 144 * ‖Ept z‖^2 + 448 * ‖Ept z‖^3
      + 912 * (‖Ept z‖^2)^2 + 2016 * ‖Ept z‖^5 ≤ 3537 := by
    have h2 : ‖Ept z‖ ^ 2 ≤ 1 := pow_le_one₀ hE0 hE1
    have h3 : ‖Ept z‖ ^ 3 ≤ 1 := pow_le_one₀ hE0 hE1
    have h4 : (‖Ept z‖ ^ 2)^2 ≤ 1 := pow_le_one₀ (pow_nonneg hE0 2) h2
    have h5 : ‖Ept z‖ ^ 5 ≤ 1 := pow_le_one₀ hE0 hE1
    nlinarith [hE1, h2, h3, h4, h5, hE0]
  simpa using this

lemma B2_E10T : Bound2 (fun (_ : ℍ) (z : ℍ) => E10T z) 0 0 := by
  refine Bound2.of_le_qz (K := 0) (C := 135697) (N := 0) (M := 0) (by norm_num) le_rfl le_rfl ?_
  intro τ z t hF ht hz0 hz1 hzim
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := qz_norm_le_one hF ht hzim
  have hq0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hkey : E10T z = 1 - 264 * Work.Kernels.qParamFun z
      - 135432 * (Work.Kernels.qParamFun z) ^ 2 := by simp only [E10T, Tq]
  rw [hkey]
  have h1 : ‖(1:ℂ) - 264 * Work.Kernels.qParamFun z - 135432 * (Work.Kernels.qParamFun z)^2‖
      ≤ 1 + 264 * ‖Work.Kernels.qParamFun z‖ + 135432 * ‖Work.Kernels.qParamFun z‖^2 := by
    calc _ ≤ ‖(1:ℂ) - 264 * Work.Kernels.qParamFun z‖
          + ‖135432 * (Work.Kernels.qParamFun z)^2‖ := norm_sub_le _ _
      _ ≤ (1 + 264 * ‖Work.Kernels.qParamFun z‖) + 135432 * ‖Work.Kernels.qParamFun z‖^2 := by
          refine add_le_add ?_ ?_
          · calc _ ≤ ‖(1:ℂ)‖ + ‖264 * Work.Kernels.qParamFun z‖ := norm_sub_le _ _
              _ = 1 + 264 * ‖Work.Kernels.qParamFun z‖ := by rw [norm_one, norm_mul, Complex.norm_ofNat]
          · rw [norm_mul, norm_pow, Complex.norm_ofNat]
  refine le_trans h1 ?_
  have hb : 1 + 264 * ‖Work.Kernels.qParamFun z‖ + 135432 * ‖Work.Kernels.qParamFun z‖^2
      ≤ 135697 := by nlinarith [hq1, hq0]
  simpa using hb

lemma B2_jzT : Bound2 (fun (_ : ℍ) (z : ℍ) => jzT z) 0 (-1) := by
  have h1 : Bound2 (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.qParamFun z)⁻¹
      + (744 : ℂ) + 196884 * Work.Kernels.qParamFun z) 0 (-1) :=
    ((B2_qinv.add (Bound2.const (744:ℂ))).add (Bound2_qparam.cmul 196884))
  exact h1.congr (fun τ z => by simp only [jzT, Tq])

lemma B2_zC : Bound2 (fun (_ : ℍ) (z : ℍ) => (z : ℂ)) 0 0 := by
  refine Bound2.of_le_qz (K := 0) (C := 1) (N := 0) (M := 1) (by norm_num) le_rfl (by norm_num) ?_
  intro τ z t hF ht hz0 hz1 hzim
  have h1 : ‖(z : ℂ)‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im (z : ℂ)
  have h2 : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith, hz1⟩
  have h3 : |z.im| = t := by rw [abs_of_pos z.im_pos, hzim]
  rw [h3] at h1
  have : ‖(z : ℂ)‖ ≤ 1 + t := by linarith [h1, h2]
  simpa using this

lemma B2_Xc (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun (_ : ℍ) (z : ℍ) => Work.Asymptotics.Compact.Xc ℓ z) 0 0 := by
  have h : Bound2 (fun (_ : ℍ) (z : ℍ) => ((Real.pi : ℂ) * Complex.I) * (z : ℂ)
      + Work.Asymptotics.Compact.cuspC ℓ) 0 0 :=
    ((B2_zC.cmul (((Real.pi : ℂ) * Complex.I))).add
      (Bound2.const (Work.Asymptotics.Compact.cuspC ℓ)))
  exact h.congr (fun τ z => by simp only [Work.Asymptotics.Compact.Xc])

lemma B2_LT (ℓ : Work.Kernels.LogLambdaData) :
    Bound2 (fun (_ : ℍ) (z : ℍ) => LT ℓ z) 0 0 := by
  have hq2 : Bound2 (fun (_ : ℍ) (z : ℍ) => (Work.Kernels.qParamFun z)^2) 0 2 := by
    refine (Bound2_qparam.mul Bound2_qparam).congr (fun τ z => by rw [pow_two]) |>.mono ?_ ?_
    · norm_num
    · norm_num
  have h : Bound2 (fun (_ : ℍ) (z : ℍ) =>
      Work.Asymptotics.Compact.Xc ℓ z - 8 * Ept z + 12 * Work.Kernels.qParamFun z
      - (32/3:ℂ) * (Ept z)^3 + 6 * (Work.Kernels.qParamFun z)^2) 0 0 :=
    ((((B2_Xc ℓ).sub (B2_Ept.cmul 8)).add (Bound2_qparam.cmul 12)).sub
      (B2_Ept3.cmul (32/3:ℂ))).add (hq2.cmul 6)
  exact h.congr (fun τ z => by simp only [LT, Tq, Te])


end
end Work.Asymptotics.KhatE1Core
