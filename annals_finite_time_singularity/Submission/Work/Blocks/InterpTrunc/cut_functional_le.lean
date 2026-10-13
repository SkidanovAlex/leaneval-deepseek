/-
Copyright: work module for the Elgindi finite-time singularity project.

# The functional estimates for the logarithmic truncation `ζ_k · G`

This module proves `Work.Blocks.InterpTrunc.cut_functional_le`: the three weighted
functionals `ttInt`, `dInt`, `ddInt` of the truncated function `cut φ k G = ζ_k · G`
differ from those of `G` by at most `O(1/log k)` times their sum, provided the
commutators `D_zζ_k`, `D_z²ζ_k` are `O(1/log k)` (the latter is the hypothesis
`∀ z, |zF φ k z| ≤ Kf / log k`) and the angular coercivity `inn G z ≤ Ks · inn (∂_θθG) z`
holds.

The proof is slicewise.  Writing `Z = zE φ k z = D_zζ_k(z)` and `C = ζ_k(z)`,

* `D_z(ζG) = Z·G + C·D_zG`,
* `D_z²(ζG) = zF·G + 2 Z·D_zG + C·D_z²G`,
* `∂_θθ(ζG) = ζ·∂_θθG`  (exactly),

and the Young splittings `sliceSplit2`/`sliceSplit3` convert each sum into the sum of the
weighted `L²`-norms of the individual terms.  Since `|Z| ≤ K/log k`, `|zF| ≤ Kf/log k`,
`0 ≤ ζ ≤ 1`, and `inn G ≤ Ks · inn (∂_θθG)`, every error term is `O(1/log k)` times one of
`ttInt G`, `dInt G`, `ddInt G`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Blocks.InterpTruncDefs
import Submission.Work.Blocks.InterpTrunc.sliceL2_le
import Submission.Work.Blocks.InterpTrunc.zF_abs_le
import Submission.Work.Blocks.InterpTrunc.sliceSplit2
import Submission.Work.Blocks.InterpTrunc.sliceSplit3
import Submission.Work.FTS.EllipticEst.Alpha4.integrable_slice_pthDz_sigma

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks.InterpTrunc

set_option autoImplicit false

/-! ## Elementary facts about `w` and `sl` -/

theorem w_zero : Work.Spaces.w 0 = 0 := by
  simp [Work.Spaces.w]

theorem sl_zero (F : ℝ → ℝ → ℝ) : sl F 0 = 0 := by
  rw [sl, w_zero]
  ring

/-- Factoring a constant out of the angular slice integral:
`∫_θ (c·u θ)² σ = c² ∫_θ (u θ)² σ`. -/
theorem setIntegral_const_sq (c : ℝ) (u : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, (c * u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = c ^ 2 * (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  rw [show (∫ θ in Work.Spaces.Iθ, (c * u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Work.Spaces.Iθ,
          ((u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) * c ^ 2 from
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_mul_const]
  ring

/-- Factoring a constant out of `inn`. -/
theorem inn_const_mul (c : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    inn (fun z' θ => c * F z' θ) z = c ^ 2 * inn F z := by
  rw [inn]
  rw [show (∫ θ in Work.Spaces.Iθ,
        (fun z' θ => c * F z' θ) z θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Work.Spaces.Iθ, (F z θ ^ 2 * Work.FTS.EllipticEst.thEta θ) * c ^ 2 from
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_mul_const, inn]
  ring

/-! ## The three slicewise estimates for the truncation -/

/-- **`D_z`-estimate.**  With `Z = D_zζ_k(z)` and the coercivity bound for `G`,
`inn (D_z(ζG)) z ≤ (1+L) Z² Ks inn(∂_θθG) z + (1+1/L) inn(D_zG) z`. -/
theorem inn_cutDz_le {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G) {k : ℕ} (hk : 2 ≤ k)
    {Ks L : ℝ} (hKs : 0 ≤ Ks) (hL : 0 < L)
    (hSl : ∀ z : ℝ, 0 < z →
      inn G z ≤ Ks * inn (Work.Spaces.pth (Work.Spaces.pth G)) z) {z : ℝ} (hz : 0 < z) :
    inn (Work.Spaces.Dz (cut φ k G)) z
      ≤ (1 + L) * (zE φ k z) ^ 2 * (Ks * inn (Work.Spaces.pth (Work.Spaces.pth G)) z)
        + (1 + 1 / L) * inn (Work.Spaces.Dz G) z := by
  have hIθ := Work.FTS.EllipticEst.ThetaU.Iθ_subset_Ioo
  have hA : ContinuousOn (fun θ => zE φ k z * G z θ) Work.Spaces.Iθ :=
    continuousOn_const.mul (hG.sliceSmoothO hz).continuousOn_Iθ
  have hB : ContinuousOn (fun θ => zeta φ k z * Work.Spaces.Dz G z θ) Work.Spaces.Iθ :=
    continuousOn_const.mul (hG.continuousOn_slice_DzIter 1 hz)
  have hcast : inn (Work.Spaces.Dz (cut φ k G)) z
      = ∫ θ in Work.Spaces.Iθ, (zE φ k z * G z θ
          + zeta φ k z * Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    rw [inn]
    refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [cut_Dz hφ hk hG hz (hIθ hθ)]
  have hsplit := sliceSplit2 hA hB hL
  have hAeq : (∫ θ in Work.Spaces.Iθ,
        (zE φ k z * G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = (zE φ k z) ^ 2 * inn G z := by
    rw [setIntegral_const_sq, inn]
  have hBeq : (∫ θ in Work.Spaces.Iθ,
        (zeta φ k z * Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = (zeta φ k z) ^ 2 * inn (Work.Spaces.Dz G) z := by
    rw [setIntegral_const_sq, inn]
  have hζ2 : (zeta φ k z) ^ 2 ≤ 1 := by
    have h1 := zeta_nonneg hφ k z
    have h2 := zeta_le_one hφ k z
    nlinarith
  have h1p : 0 ≤ 1 + L := by linarith
  have h2p : 0 ≤ 1 + 1 / L := by
    have := one_div_pos.mpr hL
    linarith
  rw [hcast]
  refine le_trans hsplit ?_
  rw [hAeq, hBeq]
  have h1 : (1 + L) * (zE φ k z) ^ 2 * inn G z
      ≤ (1 + L) * (zE φ k z) ^ 2 * (Ks * inn (Work.Spaces.pth (Work.Spaces.pth G)) z) :=
    mul_le_mul_of_nonneg_left (hSl z hz) (mul_nonneg h1p (sq_nonneg _))
  have h2 : (1 + 1 / L) * ((zeta φ k z) ^ 2 * inn (Work.Spaces.Dz G) z)
      ≤ (1 + 1 / L) * inn (Work.Spaces.Dz G) z :=
    mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (inn_nonneg (Work.Spaces.Dz G) z) hζ2) h2p
  linarith [h1, h2]

/-- **`D_z²`-estimate.**  With the second commutator bound `|zF| ≤ Kf/L`,
`inn (D_z²(ζG)) z ≤ (1+1/L) inn(D_z²G) z
 + 2(1+L) (zF² Ks inn(∂_θθG) z + 4 zE² inn(D_zG) z)`. -/
theorem inn_cutDzDz_le {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G) {k : ℕ} (hk : 2 ≤ k)
    {Ks Kf L : ℝ} (hKs : 0 ≤ Ks) (hKf : 0 ≤ Kf) (hL : 0 < L)
    (hSl : ∀ z : ℝ, 0 < z →
      inn G z ≤ Ks * inn (Work.Spaces.pth (Work.Spaces.pth G)) z)
    (hzF : ∀ z : ℝ, |zF φ k z| ≤ Kf / L) {z : ℝ} (hz : 0 < z) :
    inn (Work.Spaces.Dz (Work.Spaces.Dz (cut φ k G))) z
      ≤ (1 + 1 / L) * inn (Work.Spaces.Dz (Work.Spaces.Dz G)) z
        + 2 * (1 + L) * ((zF φ k z) ^ 2
            * (Ks * inn (Work.Spaces.pth (Work.Spaces.pth G)) z)
          + 4 * (zE φ k z) ^ 2 * inn (Work.Spaces.Dz G) z) := by
  have hIθ := Work.FTS.EllipticEst.ThetaU.Iθ_subset_Ioo
  have hA : ContinuousOn (fun θ => zF φ k z * G z θ) Work.Spaces.Iθ :=
    continuousOn_const.mul (hG.sliceSmoothO hz).continuousOn_Iθ
  have hB : ContinuousOn (fun θ => 2 * (zE φ k z * Work.Spaces.Dz G z θ)) Work.Spaces.Iθ :=
    continuousOn_const.mul (continuousOn_const.mul (hG.continuousOn_slice_DzIter 1 hz))
  have hC : ContinuousOn
      (fun θ => zeta φ k z * Work.Spaces.Dz (Work.Spaces.Dz G) z θ) Work.Spaces.Iθ :=
    continuousOn_const.mul (hG.continuousOn_slice_DzIter 2 hz)
  have hcast : inn (Work.Spaces.Dz (Work.Spaces.Dz (cut φ k G))) z
      = ∫ θ in Work.Spaces.Iθ, (zF φ k z * G z θ
          + 2 * (zE φ k z * Work.Spaces.Dz G z θ)
          + zeta φ k z * Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ := by
    rw [inn]
    refine setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [cut_DzDz hφ hk hG hz (hIθ hθ)]
  have hsplit := sliceSplit3 hA hB hC hL
  have hAeq : (∫ θ in Work.Spaces.Iθ,
        (zF φ k z * G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = (zF φ k z) ^ 2 * inn G z := by
    rw [setIntegral_const_sq, inn]
  have hBeq : (∫ θ in Work.Spaces.Iθ,
        (2 * (zE φ k z * Work.Spaces.Dz G z θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      = 4 * (zE φ k z) ^ 2 * inn (Work.Spaces.Dz G) z := by
    rw [show (∫ θ in Work.Spaces.Iθ,
          (2 * (zE φ k z * Work.Spaces.Dz G z θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        = ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz G z θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
              * (4 * (zE φ k z) ^ 2) from
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
    rw [MeasureTheory.integral_mul_const, inn]
    ring
  have hCeq : (∫ θ in Work.Spaces.Iθ,
        (zeta φ k z * Work.Spaces.Dz (Work.Spaces.Dz G) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
      = (zeta φ k z) ^ 2 * inn (Work.Spaces.Dz (Work.Spaces.Dz G)) z := by
    rw [setIntegral_const_sq, inn]
  have hζ2 : (zeta φ k z) ^ 2 ≤ 1 := by
    have h1 := zeta_nonneg hφ k z
    have h2 := zeta_le_one hφ k z
    nlinarith
  have h1L : 0 ≤ 1 + L := by linarith
  have hCL : 0 ≤ 1 + 1 / L := by
    have := one_div_pos.mpr hL
    linarith
  rw [hcast]
  refine le_trans hsplit ?_
  rw [hAeq, hBeq, hCeq]
  have h1 : (1 + 1 / L) * ((zeta φ k z) ^ 2 * inn (Work.Spaces.Dz (Work.Spaces.Dz G)) z)
      ≤ (1 + 1 / L) * inn (Work.Spaces.Dz (Work.Spaces.Dz G)) z :=
    mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (inn_nonneg (Work.Spaces.Dz (Work.Spaces.Dz G)) z) hζ2) hCL
  have h2 : (zF φ k z) ^ 2 * inn G z
      ≤ (zF φ k z) ^ 2 * (Ks * inn (Work.Spaces.pth (Work.Spaces.pth G)) z) :=
    mul_le_mul_of_nonneg_left (hSl z hz) (sq_nonneg _)
  have h2L : 0 ≤ 2 * (1 + L) := by linarith
  have hsum : (zF φ k z) ^ 2 * inn G z + 4 * (zE φ k z) ^ 2 * inn (Work.Spaces.Dz G) z
      ≤ (zF φ k z) ^ 2 * (Ks * inn (Work.Spaces.pth (Work.Spaces.pth G)) z)
        + 4 * (zE φ k z) ^ 2 * inn (Work.Spaces.Dz G) z := by linarith [h2]
  have h4 := mul_le_mul_of_nonneg_left hsum h2L
  linarith [h1, h4]

/-- **`∂_θθ`-estimate.**  `∂_θθ(ζG) = ζ ∂_θθG` exactly, so `inn` does not increase. -/
theorem inn_cutPthPth_le {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G) {k : ℕ} (hk : 2 ≤ k)
    {z : ℝ} (hz : 0 < z) :
    inn (Work.Spaces.pth (Work.Spaces.pth (cut φ k G))) z
      ≤ inn (Work.Spaces.pth (Work.Spaces.pth G)) z := by
  have hIθ := Work.FTS.EllipticEst.ThetaU.Iθ_subset_Ioo
  rw [inn]
  rw [show (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pth (Work.Spaces.pth (cut φ k G)) z θ ^ 2
          * Work.FTS.EllipticEst.thEta θ)
      = ∫ θ in Work.Spaces.Iθ,
          (zeta φ k z * Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ from
    setIntegral_congr_fun measurableSet_Icc (fun θ hθ => by
      rw [cut_pthPth hφ hk hG hz (hIθ hθ)])]
  rw [setIntegral_const_sq, inn]
  have hζ2 : (zeta φ k z) ^ 2 ≤ 1 := by
    have h1 := zeta_nonneg hφ k z
    have h2 := zeta_le_one hφ k z
    nlinarith
  have h0 : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.pth (Work.Spaces.pth G) z θ ^ 2 * Work.FTS.EllipticEst.thEta θ :=
    setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
  exact mul_le_of_le_one_left h0 hζ2

/-! ## The arithmetic of the coefficients -/

/-- `a (1+L) / L² ≤ a (1 + 1/log 2) / L` for `L ≥ log 2 > 0`. -/
theorem coeff_le {a L : ℝ} (hL : Real.log 2 ≤ L) (ha : 0 ≤ a) :
    a * (1 + L) / L ^ 2 ≤ a * (1 + 1 / Real.log 2) / L := by
  have hlog2 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hLpos : 0 < L := lt_of_lt_of_le hlog2 hL
  have h1 : 0 ≤ a * L * (L - Real.log 2) :=
    mul_nonneg (mul_nonneg ha hLpos.le) (sub_nonneg.mpr hL)
  have hkey : a * (1 + 1 / Real.log 2) * L ^ 2 - a * (1 + L) * L
      = a * L * (L - Real.log 2) / Real.log 2 := by
    field_simp
    ring
  rw [div_le_div_iff₀ (pow_pos hLpos 2) hLpos]
  have hnn : 0 ≤ a * L * (L - Real.log 2) / Real.log 2 := div_nonneg h1 hlog2.le
  linarith [hkey, hnn]

/-! ## The main estimate -/

theorem cut_functional_le {φ : ℝ → ℝ} {K : ℝ} (hφ : Work.FTS.EllipticEst.IsZCut φ K)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G)
    (hF : Work.FTS.EllipticEst.FourInt G) {Ks Kf : ℝ} (hKs : 0 ≤ Ks) (hKf : 0 ≤ Kf)
    (hSl : ∀ z : ℝ, 0 < z →
      inn G z ≤ Ks * inn (Work.Spaces.pth (Work.Spaces.pth G)) z) :
    ∃ Ke : ℝ, 0 ≤ Ke ∧ ∀ (k : ℕ) (hk : 2 ≤ k),
      (∀ z : ℝ, |zF φ k z| ≤ Kf / Real.log k) →
      Work.FTS.EllipticEst.ttInt (cut φ k G) ≤ Work.FTS.EllipticEst.ttInt G ∧
      Work.FTS.EllipticEst.dInt (cut φ k G) ≤ Work.FTS.EllipticEst.dInt G
        + (Ke / Real.log k) * (Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.dInt G
            + Work.FTS.EllipticEst.ttInt G) ∧
      Work.FTS.EllipticEst.ddInt (cut φ k G) ≤ Work.FTS.EllipticEst.ddInt G
        + (Ke / Real.log k) * (Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.dInt G
            + Work.FTS.EllipticEst.ttInt G) := by
  obtain ⟨hmiI, hddI, httI, hdI⟩ := (fourInt_iff G).mp hF
  have hlog2 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2i : 0 ≤ 1 + 1 / Real.log 2 := by
    have := one_div_pos.mpr hlog2
    linarith
  have hKcoef : 0 ≤ K ^ 2 * Ks := mul_nonneg (sq_nonneg K) hKs
  have hFcoef : 0 ≤ 2 * Kf ^ 2 * Ks :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Kf)) hKs
  have hEcoef : 0 ≤ 8 * K ^ 2 := mul_nonneg (by norm_num) (sq_nonneg K)
  have hKc : 0 ≤ K ^ 2 * Ks * (1 + 1 / Real.log 2) := mul_nonneg hKcoef hlog2i
  have hFc : 0 ≤ 2 * Kf ^ 2 * Ks * (1 + 1 / Real.log 2) := mul_nonneg hFcoef hlog2i
  have hEc : 0 ≤ 8 * K ^ 2 * (1 + 1 / Real.log 2) := mul_nonneg hEcoef hlog2i
  refine ⟨1 + K ^ 2 * Ks * (1 + 1 / Real.log 2) + 2 * Kf ^ 2 * Ks * (1 + 1 / Real.log 2)
      + 8 * K ^ 2 * (1 + 1 / Real.log 2), ?_, ?_⟩
  · linarith [hKc, hFc, hEc]
  · intro k hk hzF
    set Ke : ℝ := 1 + K ^ 2 * Ks * (1 + 1 / Real.log 2)
      + 2 * Kf ^ 2 * Ks * (1 + 1 / Real.log 2) + 8 * K ^ 2 * (1 + 1 / Real.log 2) with hKe
    have hLpos : 0 < Real.log k :=
      Real.log_pos (by
        have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        linarith)
    have hL2 : Real.log 2 ≤ Real.log k :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hk)
    -- nonnegativity of the three functionals
    have hT0 : 0 ≤ Work.FTS.EllipticEst.ttInt G := by
      rw [ttInt_eq_int_sl]
      exact setIntegral_nonneg measurableSet_Ici (fun z _ => sl_nonneg _ z)
    have hD0 : 0 ≤ Work.FTS.EllipticEst.dInt G := by
      rw [dInt_eq_int_sl]
      exact setIntegral_nonneg measurableSet_Ici (fun z _ => sl_nonneg _ z)
    have hDD0 : 0 ≤ Work.FTS.EllipticEst.ddInt G := by
      rw [ddInt_eq_int_sl]
      exact setIntegral_nonneg measurableSet_Ici (fun z _ => sl_nonneg _ z)
    -- the key coefficient comparisons
    have hKe0 : 0 ≤ Ke := by rw [hKe]; linarith [hKc, hFc, hEc]
    have hKe1 : K ^ 2 * Ks * (1 + 1 / Real.log 2) ≤ Ke := by
      rw [hKe]; linarith [hFc, hEc]
    have hKe2 : 1 ≤ Ke := by rw [hKe]; linarith [hKc, hFc, hEc]
    have hKe3 : 2 * Kf ^ 2 * Ks * (1 + 1 / Real.log 2) ≤ Ke := by
      rw [hKe]; linarith [hKc, hEc]
    have hKe4 : 8 * K ^ 2 * (1 + 1 / Real.log 2) ≤ Ke := by
      rw [hKe]; linarith [hKc, hFc]
    have hLdiv : 0 ≤ Ke / Real.log k := div_nonneg (le_trans (by norm_num) hKe2) hLpos.le
    -- the bound `|zE| ≤ K / log k`
    have hzE2 : ∀ z : ℝ, (zE φ k z) ^ 2 ≤ K ^ 2 / (Real.log k) ^ 2 := by
      intro z
      have h3 : (zE φ k z) ^ 2 ≤ (K / Real.log k) ^ 2 := by
        rw [sq_le_sq, abs_div, abs_of_nonneg hφ.2.2.2.2.1, abs_of_pos hLpos]
        exact zE_abs_le hφ hk z
      rwa [div_pow] at h3
    -- the bound `|zF| ≤ Kf / log k`
    have hzF2 : ∀ z : ℝ, (zF φ k z) ^ 2 ≤ Kf ^ 2 / (Real.log k) ^ 2 := by
      intro z
      have h3 : (zF φ k z) ^ 2 ≤ (Kf / Real.log k) ^ 2 := by
        rw [sq_le_sq, abs_div, abs_of_nonneg hKf, abs_of_pos hLpos]
        exact hzF z
      rwa [div_pow] at h3
    refine ⟨?_, ?_, ?_⟩
    · -- `ttInt` does not increase
      rw [ttInt_eq_int_sl, ttInt_eq_int_sl]
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun z => sl_nonneg _ z)) httI ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      by_cases hz0 : z = 0
      · rw [hz0]
        simp [sl_zero]
      · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
        have h := inn_cutPthPth_le hφ hG hk hzpos
        simp only [sl]
        exact mul_le_mul_of_nonneg_left h (sq_nonneg _)
    · -- `dInt`
      have hcoef : (1 + Real.log k) * K ^ 2 * Ks / (Real.log k) ^ 2
          ≤ K ^ 2 * Ks * (1 + 1 / Real.log 2) / Real.log k := by
        have h := coeff_le hL2 (show 0 ≤ K ^ 2 * Ks by positivity)
        have e : (1 + Real.log k) * K ^ 2 * Ks / (Real.log k) ^ 2
            = K ^ 2 * Ks * (1 + Real.log k) / (Real.log k) ^ 2 := by ring
        rw [e]
        exact h
      have hbnd : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          sl (Work.Spaces.Dz (cut φ k G)) z
            ≤ ((1 + Real.log k) * K ^ 2 * Ks / (Real.log k) ^ 2)
                * sl (Work.Spaces.pth (Work.Spaces.pth G)) z
              + (1 + 1 / Real.log k) * sl (Work.Spaces.Dz G) z := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
        by_cases hz0 : z = 0
        · rw [hz0]
          simp [sl_zero]
        · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
          have h := inn_cutDz_le hφ hG hk hKs hLpos hSl hzpos
          have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
          have h1p : 0 ≤ 1 + Real.log k := by linarith
          have hcoef2 : (1 + Real.log k) * (zE φ k z) ^ 2 * Ks
              ≤ (1 + Real.log k) * K ^ 2 * Ks / (Real.log k) ^ 2 := by
            have ha : (1 + Real.log k) * (zE φ k z) ^ 2
                ≤ (1 + Real.log k) * (K ^ 2 / (Real.log k) ^ 2) :=
              mul_le_mul_of_nonneg_left (hzE2 z) h1p
            have hb : (1 + Real.log k) * (zE φ k z) ^ 2 * Ks
                ≤ (1 + Real.log k) * (K ^ 2 / (Real.log k) ^ 2) * Ks :=
              mul_le_mul_of_nonneg_right ha hKs
            have hc : (1 + Real.log k) * (K ^ 2 / (Real.log k) ^ 2) * Ks
                = (1 + Real.log k) * K ^ 2 * Ks / (Real.log k) ^ 2 := by ring
            linarith [hb, hc]
          calc sl (Work.Spaces.Dz (cut φ k G)) z
              = (Work.Spaces.w z) ^ 2 * inn (Work.Spaces.Dz (cut φ k G)) z := rfl
            _ ≤ (Work.Spaces.w z) ^ 2 * ((1 + Real.log k) * (zE φ k z) ^ 2
                  * (Ks * inn (Work.Spaces.pth (Work.Spaces.pth G)) z)
                  + (1 + 1 / Real.log k) * inn (Work.Spaces.Dz G) z) :=
                mul_le_mul_of_nonneg_left h hw2
            _ = ((1 + Real.log k) * (zE φ k z) ^ 2 * Ks)
                  * sl (Work.Spaces.pth (Work.Spaces.pth G)) z
                + (1 + 1 / Real.log k) * sl (Work.Spaces.Dz G) z := by
                rw [sl, sl]; ring
            _ ≤ ((1 + Real.log k) * K ^ 2 * Ks / (Real.log k) ^ 2)
                  * sl (Work.Spaces.pth (Work.Spaces.pth G)) z
                + (1 + 1 / Real.log k) * sl (Work.Spaces.Dz G) z := by
                have := mul_le_mul_of_nonneg_right hcoef2
                  (sl_nonneg (Work.Spaces.pth (Work.Spaces.pth G)) z)
                linarith [this]
      have hgint : IntegrableOn
          (fun z => ((1 + Real.log k) * K ^ 2 * Ks / (Real.log k) ^ 2)
                * sl (Work.Spaces.pth (Work.Spaces.pth G)) z
              + (1 + 1 / Real.log k) * sl (Work.Spaces.Dz G) z) Work.Spaces.Iz :=
        (httI.const_mul _).add (hdI.const_mul _)
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun z => sl_nonneg _ z)) hgint hbnd
      have hval : (∫ z in Work.Spaces.Iz,
            ((1 + Real.log k) * K ^ 2 * Ks / (Real.log k) ^ 2)
                * sl (Work.Spaces.pth (Work.Spaces.pth G)) z
              + (1 + 1 / Real.log k) * sl (Work.Spaces.Dz G) z)
          = ((1 + Real.log k) * K ^ 2 * Ks / (Real.log k) ^ 2) * Work.FTS.EllipticEst.ttInt G
            + (1 + 1 / Real.log k) * Work.FTS.EllipticEst.dInt G := by
        rw [MeasureTheory.integral_add (httI.const_mul _) (hdI.const_mul _),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          ← ttInt_eq_int_sl, ← dInt_eq_int_sl]
      calc Work.FTS.EllipticEst.dInt (cut φ k G)
          = ∫ z in Work.Spaces.Iz, sl (Work.Spaces.Dz (cut φ k G)) z := dInt_eq_int_sl _
        _ ≤ ∫ z in Work.Spaces.Iz,
              ((1 + Real.log k) * K ^ 2 * Ks / (Real.log k) ^ 2)
                  * sl (Work.Spaces.pth (Work.Spaces.pth G)) z
                + (1 + 1 / Real.log k) * sl (Work.Spaces.Dz G) z := hmono
        _ = ((1 + Real.log k) * K ^ 2 * Ks / (Real.log k) ^ 2) * Work.FTS.EllipticEst.ttInt G
              + (1 + 1 / Real.log k) * Work.FTS.EllipticEst.dInt G := hval
        _ ≤ Work.FTS.EllipticEst.dInt G
              + (Ke / Real.log k) * (Work.FTS.EllipticEst.ddInt G
                  + Work.FTS.EllipticEst.dInt G + Work.FTS.EllipticEst.ttInt G) := by
            have hstepT : ((1 + Real.log k) * K ^ 2 * Ks / (Real.log k) ^ 2)
                  * Work.FTS.EllipticEst.ttInt G
                ≤ (Ke / Real.log k) * Work.FTS.EllipticEst.ttInt G := by
              calc ((1 + Real.log k) * K ^ 2 * Ks / (Real.log k) ^ 2)
                    * Work.FTS.EllipticEst.ttInt G
                  ≤ (K ^ 2 * Ks * (1 + 1 / Real.log 2) / Real.log k)
                    * Work.FTS.EllipticEst.ttInt G :=
                    mul_le_mul_of_nonneg_right hcoef hT0
                _ ≤ (Ke / Real.log k) * Work.FTS.EllipticEst.ttInt G := by
                    refine mul_le_mul_of_nonneg_right ?_ hT0
                    exact div_le_div_of_nonneg_right hKe1 hLpos.le
            have hstepD : (1 + 1 / Real.log k) * Work.FTS.EllipticEst.dInt G
                ≤ Work.FTS.EllipticEst.dInt G
                  + (Ke / Real.log k) * Work.FTS.EllipticEst.dInt G
                  + (Ke / Real.log k) * Work.FTS.EllipticEst.ddInt G := by
              have hsplitD : (1 + 1 / Real.log k) * Work.FTS.EllipticEst.dInt G
                  = Work.FTS.EllipticEst.dInt G
                    + (1 / Real.log k) * Work.FTS.EllipticEst.dInt G := by ring
              have h1 : (1 / Real.log k) * Work.FTS.EllipticEst.dInt G
                  ≤ (Ke / Real.log k) * Work.FTS.EllipticEst.dInt G := by
                refine mul_le_mul_of_nonneg_right ?_ hD0
                exact div_le_div_of_nonneg_right hKe2 hLpos.le
              have h2 : 0 ≤ (Ke / Real.log k) * Work.FTS.EllipticEst.ddInt G :=
                mul_nonneg hLdiv hDD0
              linarith [hsplitD, h1, h2]
            have hexp : (Ke / Real.log k) * (Work.FTS.EllipticEst.ddInt G
                  + Work.FTS.EllipticEst.dInt G + Work.FTS.EllipticEst.ttInt G)
                = (Ke / Real.log k) * Work.FTS.EllipticEst.ddInt G
                  + (Ke / Real.log k) * Work.FTS.EllipticEst.dInt G
                  + (Ke / Real.log k) * Work.FTS.EllipticEst.ttInt G := by ring
            linarith [hstepT, hstepD, hexp]
    · -- `ddInt`
      have hcoefF : 2 * (1 + Real.log k) * Kf ^ 2 * Ks / (Real.log k) ^ 2
          ≤ 2 * Kf ^ 2 * Ks * (1 + 1 / Real.log 2) / Real.log k := by
        have h := coeff_le hL2 (show 0 ≤ 2 * Kf ^ 2 * Ks by positivity)
        have e : 2 * (1 + Real.log k) * Kf ^ 2 * Ks / (Real.log k) ^ 2
            = 2 * Kf ^ 2 * Ks * (1 + Real.log k) / (Real.log k) ^ 2 := by ring
        rw [e]
        exact h
      have hcoefE : 8 * (1 + Real.log k) * K ^ 2 / (Real.log k) ^ 2
          ≤ 8 * K ^ 2 * (1 + 1 / Real.log 2) / Real.log k := by
        have h := coeff_le hL2 (show 0 ≤ 8 * K ^ 2 by positivity)
        have e : 8 * (1 + Real.log k) * K ^ 2 / (Real.log k) ^ 2
            = 8 * K ^ 2 * (1 + Real.log k) / (Real.log k) ^ 2 := by ring
        rw [e]
        exact h
      have hbnd : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          sl (Work.Spaces.Dz (Work.Spaces.Dz (cut φ k G))) z
            ≤ (1 + 1 / Real.log k) * sl (Work.Spaces.Dz (Work.Spaces.Dz G)) z
              + (2 * (1 + Real.log k) * Kf ^ 2 * Ks / (Real.log k) ^ 2)
                  * sl (Work.Spaces.pth (Work.Spaces.pth G)) z
              + (8 * (1 + Real.log k) * K ^ 2 / (Real.log k) ^ 2)
                  * sl (Work.Spaces.Dz G) z := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
        by_cases hz0 : z = 0
        · rw [hz0]
          simp [sl_zero]
        · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
          have h := inn_cutDzDz_le hφ hG hk hKs hKf hLpos hSl hzF hzpos
          have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
          have h2p : 0 ≤ 2 * (1 + Real.log k) := by linarith
          have hcoefF2 : 2 * (1 + Real.log k) * (zF φ k z) ^ 2 * Ks
              ≤ 2 * (1 + Real.log k) * Kf ^ 2 * Ks / (Real.log k) ^ 2 := by
            have ha : 2 * (1 + Real.log k) * (zF φ k z) ^ 2
                ≤ 2 * (1 + Real.log k) * (Kf ^ 2 / (Real.log k) ^ 2) :=
              mul_le_mul_of_nonneg_left (hzF2 z) h2p
            have hb : 2 * (1 + Real.log k) * (zF φ k z) ^ 2 * Ks
                ≤ 2 * (1 + Real.log k) * (Kf ^ 2 / (Real.log k) ^ 2) * Ks :=
              mul_le_mul_of_nonneg_right ha hKs
            have hc : 2 * (1 + Real.log k) * (Kf ^ 2 / (Real.log k) ^ 2) * Ks
                = 2 * (1 + Real.log k) * Kf ^ 2 * Ks / (Real.log k) ^ 2 := by ring
            linarith [hb, hc]
          have hcoefE2 : 8 * (1 + Real.log k) * (zE φ k z) ^ 2
              ≤ 8 * (1 + Real.log k) * K ^ 2 / (Real.log k) ^ 2 := by
            have ha : 8 * (1 + Real.log k) * (zE φ k z) ^ 2
                ≤ 8 * (1 + Real.log k) * (K ^ 2 / (Real.log k) ^ 2) :=
              mul_le_mul_of_nonneg_left (hzE2 z) (by linarith)
            have hc : 8 * (1 + Real.log k) * (K ^ 2 / (Real.log k) ^ 2)
                = 8 * (1 + Real.log k) * K ^ 2 / (Real.log k) ^ 2 := by ring
            linarith [ha, hc]
          calc sl (Work.Spaces.Dz (Work.Spaces.Dz (cut φ k G))) z
              = (Work.Spaces.w z) ^ 2
                  * inn (Work.Spaces.Dz (Work.Spaces.Dz (cut φ k G))) z := rfl
            _ ≤ (Work.Spaces.w z) ^ 2 * ((1 + 1 / Real.log k)
                  * inn (Work.Spaces.Dz (Work.Spaces.Dz G)) z
                  + 2 * (1 + Real.log k) * ((zF φ k z) ^ 2
                      * (Ks * inn (Work.Spaces.pth (Work.Spaces.pth G)) z)
                    + 4 * (zE φ k z) ^ 2 * inn (Work.Spaces.Dz G) z)) :=
                mul_le_mul_of_nonneg_left h hw2
            _ = (1 + 1 / Real.log k) * sl (Work.Spaces.Dz (Work.Spaces.Dz G)) z
                + (2 * (1 + Real.log k) * (zF φ k z) ^ 2 * Ks)
                    * sl (Work.Spaces.pth (Work.Spaces.pth G)) z
                + (8 * (1 + Real.log k) * (zE φ k z) ^ 2) * sl (Work.Spaces.Dz G) z := by
                rw [sl, sl, sl]; ring
            _ ≤ (1 + 1 / Real.log k) * sl (Work.Spaces.Dz (Work.Spaces.Dz G)) z
                + (2 * (1 + Real.log k) * Kf ^ 2 * Ks / (Real.log k) ^ 2)
                    * sl (Work.Spaces.pth (Work.Spaces.pth G)) z
                + (8 * (1 + Real.log k) * K ^ 2 / (Real.log k) ^ 2)
                    * sl (Work.Spaces.Dz G) z := by
                have hF' : (2 * (1 + Real.log k) * (zF φ k z) ^ 2 * Ks)
                      * sl (Work.Spaces.pth (Work.Spaces.pth G)) z
                    ≤ (2 * (1 + Real.log k) * Kf ^ 2 * Ks / (Real.log k) ^ 2)
                      * sl (Work.Spaces.pth (Work.Spaces.pth G)) z :=
                  mul_le_mul_of_nonneg_right hcoefF2
                    (sl_nonneg (Work.Spaces.pth (Work.Spaces.pth G)) z)
                have hE' : (8 * (1 + Real.log k) * (zE φ k z) ^ 2)
                      * sl (Work.Spaces.Dz G) z
                    ≤ (8 * (1 + Real.log k) * K ^ 2 / (Real.log k) ^ 2)
                      * sl (Work.Spaces.Dz G) z :=
                  mul_le_mul_of_nonneg_right hcoefE2 (sl_nonneg (Work.Spaces.Dz G) z)
                linarith [hF', hE']
      have hgint : IntegrableOn
          (fun z => (1 + 1 / Real.log k) * sl (Work.Spaces.Dz (Work.Spaces.Dz G)) z
              + (2 * (1 + Real.log k) * Kf ^ 2 * Ks / (Real.log k) ^ 2)
                  * sl (Work.Spaces.pth (Work.Spaces.pth G)) z
              + (8 * (1 + Real.log k) * K ^ 2 / (Real.log k) ^ 2)
                  * sl (Work.Spaces.Dz G) z) Work.Spaces.Iz :=
        ((hddI.const_mul _).add (httI.const_mul _)).add (hdI.const_mul _)
      have hmono := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun z => sl_nonneg _ z)) hgint hbnd
      have hval : (∫ z in Work.Spaces.Iz,
            (1 + 1 / Real.log k) * sl (Work.Spaces.Dz (Work.Spaces.Dz G)) z
              + (2 * (1 + Real.log k) * Kf ^ 2 * Ks / (Real.log k) ^ 2)
                  * sl (Work.Spaces.pth (Work.Spaces.pth G)) z
              + (8 * (1 + Real.log k) * K ^ 2 / (Real.log k) ^ 2)
                  * sl (Work.Spaces.Dz G) z)
          = (1 + 1 / Real.log k) * Work.FTS.EllipticEst.ddInt G
            + (2 * (1 + Real.log k) * Kf ^ 2 * Ks / (Real.log k) ^ 2)
                * Work.FTS.EllipticEst.ttInt G
            + (8 * (1 + Real.log k) * K ^ 2 / (Real.log k) ^ 2)
                * Work.FTS.EllipticEst.dInt G := by
        rw [MeasureTheory.integral_add
              (f := fun z => (1 + 1 / Real.log k)
                  * sl (Work.Spaces.Dz (Work.Spaces.Dz G)) z
                + (2 * (1 + Real.log k) * Kf ^ 2 * Ks / (Real.log k) ^ 2)
                  * sl (Work.Spaces.pth (Work.Spaces.pth G)) z)
              (g := fun z => (8 * (1 + Real.log k) * K ^ 2 / (Real.log k) ^ 2)
                  * sl (Work.Spaces.Dz G) z)
              ((hddI.const_mul _).add (httI.const_mul _)) (hdI.const_mul _),
          MeasureTheory.integral_add (hddI.const_mul _) (httI.const_mul _),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul,
          ← ddInt_eq_int_sl, ← ttInt_eq_int_sl, ← dInt_eq_int_sl]
      calc Work.FTS.EllipticEst.ddInt (cut φ k G)
          = ∫ z in Work.Spaces.Iz,
              sl (Work.Spaces.Dz (Work.Spaces.Dz (cut φ k G))) z := ddInt_eq_int_sl _
        _ ≤ ∫ z in Work.Spaces.Iz,
              (1 + 1 / Real.log k) * sl (Work.Spaces.Dz (Work.Spaces.Dz G)) z
                + (2 * (1 + Real.log k) * Kf ^ 2 * Ks / (Real.log k) ^ 2)
                    * sl (Work.Spaces.pth (Work.Spaces.pth G)) z
                + (8 * (1 + Real.log k) * K ^ 2 / (Real.log k) ^ 2)
                    * sl (Work.Spaces.Dz G) z := hmono
        _ = (1 + 1 / Real.log k) * Work.FTS.EllipticEst.ddInt G
              + (2 * (1 + Real.log k) * Kf ^ 2 * Ks / (Real.log k) ^ 2)
                  * Work.FTS.EllipticEst.ttInt G
              + (8 * (1 + Real.log k) * K ^ 2 / (Real.log k) ^ 2)
                  * Work.FTS.EllipticEst.dInt G := hval
        _ ≤ Work.FTS.EllipticEst.ddInt G
              + (Ke / Real.log k) * (Work.FTS.EllipticEst.ddInt G
                  + Work.FTS.EllipticEst.dInt G + Work.FTS.EllipticEst.ttInt G) := by
            have hsplitDD : (1 + 1 / Real.log k) * Work.FTS.EllipticEst.ddInt G
                = Work.FTS.EllipticEst.ddInt G
                  + (1 / Real.log k) * Work.FTS.EllipticEst.ddInt G := by ring
            have h1 : (1 / Real.log k) * Work.FTS.EllipticEst.ddInt G
                ≤ (Ke / Real.log k) * Work.FTS.EllipticEst.ddInt G := by
              refine mul_le_mul_of_nonneg_right ?_ hDD0
              exact div_le_div_of_nonneg_right hKe2 hLpos.le
            have hstepT : (2 * (1 + Real.log k) * Kf ^ 2 * Ks / (Real.log k) ^ 2)
                  * Work.FTS.EllipticEst.ttInt G
                ≤ (Ke / Real.log k) * Work.FTS.EllipticEst.ttInt G := by
              calc (2 * (1 + Real.log k) * Kf ^ 2 * Ks / (Real.log k) ^ 2)
                    * Work.FTS.EllipticEst.ttInt G
                  ≤ (2 * Kf ^ 2 * Ks * (1 + 1 / Real.log 2) / Real.log k)
                    * Work.FTS.EllipticEst.ttInt G :=
                    mul_le_mul_of_nonneg_right hcoefF hT0
                _ ≤ (Ke / Real.log k) * Work.FTS.EllipticEst.ttInt G := by
                    refine mul_le_mul_of_nonneg_right ?_ hT0
                    exact div_le_div_of_nonneg_right hKe3 hLpos.le
            have hstepD : (8 * (1 + Real.log k) * K ^ 2 / (Real.log k) ^ 2)
                  * Work.FTS.EllipticEst.dInt G
                ≤ (Ke / Real.log k) * Work.FTS.EllipticEst.dInt G := by
              calc (8 * (1 + Real.log k) * K ^ 2 / (Real.log k) ^ 2)
                    * Work.FTS.EllipticEst.dInt G
                  ≤ (8 * K ^ 2 * (1 + 1 / Real.log 2) / Real.log k)
                    * Work.FTS.EllipticEst.dInt G :=
                    mul_le_mul_of_nonneg_right hcoefE hD0
                _ ≤ (Ke / Real.log k) * Work.FTS.EllipticEst.dInt G := by
                    refine mul_le_mul_of_nonneg_right ?_ hD0
                    exact div_le_div_of_nonneg_right hKe4 hLpos.le
            have hexp : (Ke / Real.log k) * (Work.FTS.EllipticEst.ddInt G
                  + Work.FTS.EllipticEst.dInt G + Work.FTS.EllipticEst.ttInt G)
                = (Ke / Real.log k) * Work.FTS.EllipticEst.ddInt G
                  + (Ke / Real.log k) * Work.FTS.EllipticEst.dInt G
                  + (Ke / Real.log k) * Work.FTS.EllipticEst.ttInt G := by ring
            linarith [hsplitDD, h1, hstepT, hstepD, hexp]

end Work.Blocks.InterpTrunc
