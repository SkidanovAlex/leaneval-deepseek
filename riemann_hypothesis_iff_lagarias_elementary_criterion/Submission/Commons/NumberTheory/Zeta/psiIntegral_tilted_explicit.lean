import Mathlib
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_mfold_explicit
import Submission.Commons.Analysis.Real.exists_gap_height
import Submission.Commons.NumberTheory.Zeta.riemannZeta_ordinate_window
import Submission.Commons.NumberTheory.Zeta.psiIntegral_perron_bound
import Submission.Commons.NumberTheory.Zeta.zeta1_zeroBall_multiplicity_sum_le
import Submission.Commons.Analysis.SpecialFunctions.Gamma.psi_kernel_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le
import Submission.Commons.Analysis.Real.head_harmonic_le
import Submission.Commons.NumberTheory.Harmonic.abs_harmonic_sub_log_sub_euler_le_inv
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.tan_norm_le_of_abs_im_ge
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_at_height_farLeft_neg_consts_bounded
import Submission.Commons.NumberTheory.Zeta.logDeriv_zeta1_strip_goodHeight_le
import Submission.Commons.NumberTheory.Zeta.trivial_zero_of_riemannZeta_eq_zero_of_re_nonpos
import Submission.Commons.NumberTheory.Zeta.mem_strip_of_riemannZeta_eq_zero_of_not_trivial
import Submission.Commons.NumberTheory.Zeta.logDeriv_riemannZeta_neg_one
import Submission.Commons.NumberTheory.Zeta.zeta1_zero_tilted_term_le
import Submission.Commons.NumberTheory.Zeta.zeta1_zeroBall_multiplicity_sum_le
import Submission.Commons.Analysis.Fourier.perronStep_deviation
import Submission.Commons.NumberTheory.Zeta.mangoldt_perron_sum_eq

open Complex MeasureTheory intervalIntegral Filter
open scoped Real Topology BigOperators ComplexConjugate

set_option maxHeartbeats 1600000

noncomputable section

open Classical

namespace Commons.NumberTheory.Zeta

/-! ## The tilted Perron kernel -/

/-- The tilted Perron kernel `x·ψIntF1 x s/(s+1) = -(ζ'/ζ)(s)·x^{s+1}/(s(s+1))`. -/
def tiltIntF (x : ℝ) (s : ℂ) : ℂ := (x : ℂ) * psiIntF1 x s / (s + 1)

lemma tiltIntF_apply (x : ℝ) (s : ℂ) : tiltIntF x s = (x : ℂ) * psiIntF1 x s / (s + 1) := rfl

/-- `x·ψIntF1 x (-1) = ζ'(−1)/ζ(−1) = logDeriv ζ (−1)`. -/
lemma mul_psiIntF1_neg_one {x : ℝ} (hx : 0 < x) :
    (x : ℂ) * psiIntF1 x (-1) = logDeriv riemannZeta (-1) := by
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hx1 : (x : ℂ) ^ (-1 : ℂ) = (x : ℂ)⁻¹ := by
    rw [show (-1 : ℂ) = -(1 : ℂ) by ring, Complex.cpow_neg, Complex.cpow_one]
  have hz1 : riemannZeta₁ (-1) ≠ 0 :=
    zeta1_ne_zero_of_re_le_zero (by norm_num) (by norm_num)
  have hlog := logDeriv_zeta1_eq (s := (-1 : ℂ)) (by norm_num) hz1
  have hlog' : logDeriv riemannZeta₁ (-1) = logDeriv riemannZeta (-1) + ((-1 : ℂ) - 1)⁻¹ := by
    rw [hlog]; rfl
  unfold psiIntF1
  rw [hlog', hx1]
  have : ((-1 : ℂ) - 1) = -2 := by ring
  rw [this]
  field_simp
  ring

/-- the coefficient of the pole of `psiIntF1 x` at the zero `ρ`. -/
def tiltC (x : ℝ) (ρ : ℂ) : ℂ := - (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ

/-- the coefficient of the model at the pole `i` (`0`, `1`, `-1`, or a zero). -/
def tiltCoeff (x : ℝ) (i : ℂ) : ℂ :=
  if i = 0 then (x : ℂ) * caZeroCoeff
  else if i = 1 then (x : ℂ) * (x : ℂ) / 2
  else if i = -1 then (x : ℂ) * psiIntF1 x (-1)
  else - (zeta1Order i : ℂ) * (x : ℂ) ^ (i + 1) / (i * (i + 1))

/-- the set of poles of the model: `0`, `1`, `-1` and the zeros in `Z`. -/
def tiltPoles (Z : Finset ℂ) : Finset ℂ := insert 0 (insert 1 (insert (-1) Z))

lemma cpow_add_one {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ (s + 1) = (x : ℂ) * (x : ℂ) ^ s := by
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [show s + 1 = 1 + s by ring, Complex.cpow_add (1 : ℂ) s hxne, Complex.cpow_one]

lemma tiltCoeff_zero (x : ℝ) : tiltCoeff x 0 = (x : ℂ) * caZeroCoeff := by
  unfold tiltCoeff
  rw [if_pos rfl]

lemma tiltCoeff_one (x : ℝ) : tiltCoeff x 1 = (x : ℂ) * (x : ℂ) / 2 := by
  unfold tiltCoeff
  rw [if_neg (by norm_num : (1 : ℂ) ≠ 0), if_pos rfl]

lemma tiltCoeff_neg_one (x : ℝ) : tiltCoeff x (-1) = (x : ℂ) * psiIntF1 x (-1) := by
  unfold tiltCoeff
  rw [if_neg (by norm_num : (-1 : ℂ) ≠ 0), if_neg (by norm_num : (-1 : ℂ) ≠ 1), if_pos rfl]

lemma tiltCoeff_of_mem {x : ℝ} (hx : 0 < x) {Z : Finset ℂ} {ρ : ℂ} (hρ : ρ ∈ Z)
    (h0 : (0 : ℂ) ∉ Z) (h1 : (1 : ℂ) ∉ Z) (hm1 : (-1 : ℂ) ∉ Z) :
    tiltCoeff x ρ = (x : ℂ) * tiltC x ρ / (ρ + 1) := by
  have hρ0 : ρ ≠ 0 := fun h => h0 (h ▸ hρ)
  have hρ1 : ρ ≠ 1 := fun h => h1 (h ▸ hρ)
  have hρm1 : ρ ≠ -1 := fun h => hm1 (h ▸ hρ)
  have hp : ρ + 1 ≠ 0 := by
    intro h; exact hρm1 (by linear_combination h)
  have hr : ρ * (ρ + 1) ≠ 0 := mul_ne_zero hρ0 hp
  unfold tiltCoeff tiltC
  rw [if_neg hρ0, if_neg hρ1, if_neg hρm1]
  rw [cpow_add_one hx ρ]
  field_simp

lemma tiltPoles_sum {Z : Finset ℂ} (h0 : (0 : ℂ) ∉ Z) (h1 : (1 : ℂ) ∉ Z)
    (hm1 : (-1 : ℂ) ∉ Z) (f : ℂ → ℂ) :
    ∑ i ∈ tiltPoles Z, f i = f 0 + f 1 + f (-1) + ∑ ρ ∈ Z, f ρ := by
  have h0' : (0 : ℂ) ∉ insert 1 (insert (-1) Z) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨by norm_num, by norm_num, h0⟩
  have h1' : (1 : ℂ) ∉ insert (-1) Z := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨by norm_num, h1⟩
  unfold tiltPoles
  rw [Finset.sum_insert h0', Finset.sum_insert h1', Finset.sum_insert hm1]
  ring




/-! ## The pole-removed remainder and its analyticity -/

lemma analyticAt_div_sub_one (x : ℝ) {z : ℂ} (hz : z ≠ 1) :
    AnalyticAt ℂ (fun w : ℂ => (x : ℂ) / (w - 1)) z :=
  AnalyticAt.div analyticAt_const (AnalyticAt.sub analyticAt_id analyticAt_const) (sub_ne_zero.mpr hz)

lemma analyticAt_caZeroCoeff_mul_inv {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ (fun w : ℂ => caZeroCoeff * w⁻¹) z :=
  analyticAt_const.mul (AnalyticAt.inv analyticAt_id hz)

lemma analyticAt_tiltC_div {x : ℝ} {Z : Finset ℂ} {z : ℂ} (hz : z ∉ Z) :
    AnalyticAt ℂ (fun w : ℂ => ∑ ρ ∈ Z, tiltC x ρ / (w - ρ)) z := by
  refine analyticAt_sum Z (fun ρ hρ => ?_)
  exact AnalyticAt.div analyticAt_const (AnalyticAt.sub analyticAt_id analyticAt_const)
    (sub_ne_zero.mpr (fun h => hz (h ▸ hρ)))

/-- local removal function at a zero `ρ` of `ζ₁` (junk value if `ρ` is not such a zero). -/
noncomputable def tiltZeroRemovalFun (x : ℝ) (hx : 0 < x) (ρ : ℂ) : ℂ → ℂ :=
  if h : riemannZeta₁ ρ = 0 ∧ ρ ≠ 0 ∧ ρ ≠ 1 then psiZeroRemoval x hx ρ h.1 h.2.1 h.2.2
  else fun _ => 0

lemma tiltZeroRemovalFun_analyticAt {x : ℝ} (hx : 0 < x) {ρ : ℂ}
    (hρ : riemannZeta₁ ρ = 0) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    AnalyticAt ℂ (tiltZeroRemovalFun x hx ρ) ρ := by
  unfold tiltZeroRemovalFun
  rw [dif_pos ⟨hρ, hρ0, hρ1⟩]
  exact psiZeroRemoval_analyticAt hx ρ hρ hρ0 hρ1

lemma tiltZeroRemovalFun_eventually {x : ℝ} (hx : 0 < x) {ρ : ℂ}
    (hρ : riemannZeta₁ ρ = 0) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    ∀ᶠ s in 𝓝[≠] ρ, tiltZeroRemovalFun x hx ρ s =
      psiIntF1 x s + (zeta1Order ρ : ℂ) * (x : ℂ) ^ ρ / ρ * (s - ρ)⁻¹ := by
  unfold tiltZeroRemovalFun
  rw [dif_pos ⟨hρ, hρ0, hρ1⟩]
  exact psiZeroRemoval_eventually hx ρ hρ hρ0 hρ1

/-- the global patched remainder `ψIntF1 x − (poles at 0, 1 and the zeros of `Z`)`. -/
noncomputable def tiltRemainder (x : ℝ) (hx : 0 < x) (Z : Finset ℂ) : ℂ → ℂ :=
  fun s =>
    if s = 0 then psiZeroPoleRemoval x hx s - (x : ℂ) / (s - 1) - ∑ ρ ∈ Z, tiltC x ρ / (s - ρ)
    else if s = 1 then psiOneRemoval x hx s - caZeroCoeff * s⁻¹ - ∑ ρ ∈ Z, tiltC x ρ / (s - ρ)
    else if hs : s ∈ Z then
      tiltZeroRemovalFun x hx s s - caZeroCoeff * s⁻¹ - (x : ℂ) / (s - 1)
        - ∑ ρ ∈ Z.erase s, tiltC x ρ / (s - ρ)
    else psiIntF1 x s - caZeroCoeff * s⁻¹ - (x : ℂ) / (s - 1) - ∑ ρ ∈ Z, tiltC x ρ / (s - ρ)

/-- off the pole set the patched remainder is the literal difference. -/
lemma tiltRemainder_eq_diff {x : ℝ} (hx : 0 < x) {Z : Finset ℂ} {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsZ : s ∉ Z) :
    tiltRemainder x hx Z s = psiIntF1 x s - caZeroCoeff * s⁻¹ - (x : ℂ) / (s - 1)
      - ∑ ρ ∈ Z, tiltC x ρ / (s - ρ) := by
  unfold tiltRemainder
  rw [if_neg hs0, if_neg hs1, dif_neg hsZ]

lemma analyticAt_tiltRemainder_zero {x : ℝ} (hx : 0 < x) {Z : Finset ℂ}
    (hZ0 : (0 : ℂ) ∉ Z) :
    AnalyticAt ℂ (tiltRemainder x hx Z) 0 := by
  have hH : AnalyticAt ℂ (fun z => psiZeroPoleRemoval x hx z - (x : ℂ) / (z - 1)
      - ∑ ρ ∈ Z, tiltC x ρ / (z - ρ)) 0 :=
    ((psiZeroPoleRemoval_analyticAt hx).sub (analyticAt_div_sub_one x (by norm_num))).sub
      (analyticAt_tiltC_div hZ0)
  refine hH.congr ?_
  have hev := psiZeroPoleRemoval_eventually hx
  rw [eventually_nhdsWithin_iff] at hev
  filter_upwards [hev, eventually_not_mem_finset hZ0,
    eventually_ne_nhds (show (0 : ℂ) ≠ 1 by norm_num)] with z hzRem hzZ hz1
  by_cases hz0 : z = 0
  · subst hz0
    rw [tiltRemainder, if_pos rfl]
  · rw [tiltRemainder, if_neg hz0, if_neg hz1, dif_neg hzZ,
      hzRem hz0]

lemma analyticAt_tiltRemainder_one {x : ℝ} (hx : 0 < x) {Z : Finset ℂ}
    (hZ1 : (1 : ℂ) ∉ Z) :
    AnalyticAt ℂ (tiltRemainder x hx Z) 1 := by
  have hH : AnalyticAt ℂ (fun z => psiOneRemoval x hx z - caZeroCoeff * z⁻¹
      - ∑ ρ ∈ Z, tiltC x ρ / (z - ρ)) 1 :=
    ((psiOneRemoval_analyticAt hx).sub (analyticAt_caZeroCoeff_mul_inv (by norm_num))).sub
      (analyticAt_tiltC_div hZ1)
  refine hH.congr ?_
  have hev := psiOneRemoval_eventually hx
  rw [eventually_nhdsWithin_iff] at hev
  filter_upwards [hev, eventually_not_mem_finset hZ1,
    eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num)] with z hzRem hzZ hz0
  by_cases hz1 : z = 1
  · subst hz1
    rw [tiltRemainder, if_neg (by norm_num : (1 : ℂ) ≠ 0), if_pos rfl]
  · rw [tiltRemainder, if_neg hz0, if_neg hz1, dif_neg hzZ,
      hzRem hz1]
    ring

lemma analyticAt_tiltRemainder_zeroPole {x : ℝ} (hx : 0 < x) {Z : Finset ℂ} {s : ℂ}
    (hZ : ∀ ρ ∈ Z, riemannZeta₁ ρ = 0) (hZ0 : (0 : ℂ) ∉ Z) (hZ1 : (1 : ℂ) ∉ Z)
    (hsZ : s ∈ Z) :
    AnalyticAt ℂ (tiltRemainder x hx Z) s := by
  have hs0 : s ≠ 0 := fun h => hZ0 (h ▸ hsZ)
  have hs1 : s ≠ 1 := fun h => hZ1 (h ▸ hsZ)
  have hρ := hZ s hsZ
  have hH : AnalyticAt ℂ (fun z => tiltZeroRemovalFun x hx s z - caZeroCoeff * z⁻¹
      - (x : ℂ) / (z - 1) - ∑ ρ ∈ Z.erase s, tiltC x ρ / (z - ρ)) s :=
    (((tiltZeroRemovalFun_analyticAt hx hρ hs0 hs1).sub
      (analyticAt_caZeroCoeff_mul_inv hs0)).sub (analyticAt_div_sub_one x hs1)).sub
      (analyticAt_tiltC_div (Finset.notMem_erase s Z))
  refine hH.congr ?_
  have hev := tiltZeroRemovalFun_eventually hx hρ hs0 hs1
  rw [eventually_nhdsWithin_iff] at hev
  filter_upwards [hev, eventually_not_mem_finset (Finset.notMem_erase s Z),
    eventually_ne_nhds hs0, eventually_ne_nhds hs1] with z hzRem hzZ hz0 hz1
  have hsum : (∑ ρ ∈ Z, tiltC x ρ / (z - ρ))
      = tiltC x s / (z - s) + ∑ ρ ∈ Z.erase s, tiltC x ρ / (z - ρ) :=
    (Finset.add_sum_erase Z (fun ρ => tiltC x ρ / (z - ρ)) hsZ).symm
  by_cases hzs : z = s
  · subst hzs
    rw [tiltRemainder, if_neg hs0, if_neg hs1, dif_pos hsZ]
  · have hzZ' : z ∉ Z := by
      intro hzmem
      exact hzZ (Finset.mem_erase.mpr ⟨hzs, hzmem⟩)
    rw [tiltRemainder, if_neg hz0, if_neg hz1, dif_neg hzZ', hsum, hzRem hzs]
    have htC : tiltC x s = - ((zeta1Order s : ℂ) * (x : ℂ) ^ s / s) := by
      unfold tiltC; ring
    rw [htC]
    ring

lemma analyticAt_tiltRemainder_of_ne {x : ℝ} (hx : 0 < x) {Z : Finset ℂ} {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsZ : s ∉ Z) (hζ : riemannZeta₁ s ≠ 0) :
    AnalyticAt ℂ (tiltRemainder x hx Z) s := by
  have hH : AnalyticAt ℂ (fun z => psiIntF1 x z - caZeroCoeff * z⁻¹ - (x : ℂ) / (z - 1)
      - ∑ ρ ∈ Z, tiltC x ρ / (z - ρ)) s :=
    ((psiIntF1_analyticAt hx hs0 hs1 hζ).sub (analyticAt_caZeroCoeff_mul_inv hs0)).sub
      (analyticAt_div_sub_one x hs1) |>.sub (analyticAt_tiltC_div hsZ)
  refine hH.congr ?_
  filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1,
    eventually_not_mem_finset hsZ] with z hz0 hz1 hzZ
  exact (tiltRemainder_eq_diff hx hz0 hz1 hzZ).symm


/-! ## The pointwise model identity -/

/-- abstract algebraic core of the model decomposition. -/
lemma tilt_alg {t x S S1 S2 psi psi1 coeff : ℂ} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (htm1 : t + 1 ≠ 0) (h1 : (t + 1) * S1 = x * (S - S2)) :
    (t + 1) * (x * psi / (t + 1) - (x * coeff / t + (x * x / 2) / (t - 1) + x * psi1 / (t + 1) + S1))
      = x * ((psi - coeff * t⁻¹ - x / (t - 1) - S)
          - (psi1 - coeff * (-1)⁻¹ - x / ((-1) - 1) - S2)) := by
  have hS1 : S1 = x * (S - S2) / (t + 1) := by
    rw [eq_div_iff htm1, mul_comm]
    exact h1
  rw [hS1]
  field_simp
  ring

lemma tiltIntF_eq_model {x : ℝ} (hx : 0 < x) {Z : Finset ℂ}
    (hZ0 : (0 : ℂ) ∉ Z) (hZ1 : (1 : ℂ) ∉ Z) (hm1 : (-1 : ℂ) ∉ Z) {t : ℂ}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htZ : t ∉ Z) (htm1 : t ≠ -1) :
    tiltIntF x t = (∑ i ∈ tiltPoles Z, tiltCoeff x i / (t - i))
      + (x : ℂ) * dslope (tiltRemainder x hx Z) (-1) t := by
  have htm1' : t + 1 ≠ 0 := by
    intro h; exact htm1 (by linear_combination h)
  have hS12 : (t + 1) * (∑ ρ ∈ Z, (x : ℂ) * tiltC x ρ / ((ρ + 1) * (t - ρ)))
      = (x : ℂ) * ((∑ ρ ∈ Z, tiltC x ρ / (t - ρ))
          - ∑ ρ ∈ Z, tiltC x ρ / ((-1) - ρ)) := by
    rw [Finset.mul_sum, mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun ρ hρ => ?_)
    have hρm1 : ρ ≠ -1 := fun h => hm1 (h ▸ hρ)
    have htρ : t - ρ ≠ 0 := sub_ne_zero.mpr (fun h => htZ (h ▸ hρ))
    have hρ1 : ρ + 1 ≠ 0 := by intro h; exact hρm1 (by linear_combination h)
    field_simp
    ring
  have hsumZ : (∑ ρ ∈ Z, tiltCoeff x ρ / (t - ρ))
      = ∑ ρ ∈ Z, (x : ℂ) * tiltC x ρ / ((ρ + 1) * (t - ρ)) :=
    Finset.sum_congr rfl (fun ρ hρ => by
      rw [tiltCoeff_of_mem hx hρ hZ0 hZ1 hm1, div_div])
  have hmul : (t + 1) * (tiltIntF x t - (∑ i ∈ tiltPoles Z, tiltCoeff x i / (t - i)))
      = (x : ℂ) * (tiltRemainder x hx Z t - tiltRemainder x hx Z (-1)) := by
    rw [tiltIntF_apply, tiltPoles_sum hZ0 hZ1 hm1 (fun i => tiltCoeff x i / (t - i)),
      tiltCoeff_zero, tiltCoeff_one, tiltCoeff_neg_one, hsumZ,
      tiltRemainder_eq_diff hx ht0 ht1 htZ,
      tiltRemainder_eq_diff hx (by norm_num : (-1 : ℂ) ≠ 0) (by norm_num : (-1 : ℂ) ≠ 1) hm1]
    simp only [sub_zero, sub_neg_eq_add]
    exact tilt_alg ht0 ht1 htm1' hS12
  have hAB : tiltIntF x t - (∑ i ∈ tiltPoles Z, tiltCoeff x i / (t - i))
      = (x : ℂ) * (tiltRemainder x hx Z t - tiltRemainder x hx Z (-1)) / (t + 1) := by
    rw [eq_div_iff htm1']
    simpa only [mul_comm] using hmul
  have hC : dslope (tiltRemainder x hx Z) (-1) t
      = (tiltRemainder x hx Z t - tiltRemainder x hx Z (-1)) / (t + 1) := by
    rw [dslope_of_ne _ htm1, slope, smul_eq_mul]
    simp only [sub_neg_eq_add, vsub_eq_sub]
    ring
  have hA : tiltIntF x t = (x : ℂ) * (tiltRemainder x hx Z t - tiltRemainder x hx Z (-1)) / (t + 1)
      + (∑ i ∈ tiltPoles Z, tiltCoeff x i / (t - i)) :=
    (sub_eq_iff_eq_add (a := tiltIntF x t)
      (b := ∑ i ∈ tiltPoles Z, tiltCoeff x i / (t - i))
      (c := (x : ℂ) * (tiltRemainder x hx Z t - tiltRemainder x hx Z (-1)) / (t + 1))).mp hAB
  rw [hA, hC]
  ring

/-! ## Differentiability of the remainder on the far-left rectangle -/

lemma tiltRemainder_differentiableOn {x : ℝ} (hx : 0 < x) {R a b Tp : ℝ}
    (hR : 0 ≤ R) (ha : a < -1) (h1b : 1 < b) (hTp : 0 < Tp)
    (hrect : closedContourRect a b Tp ⊆ Metric.closedBall (0 : ℂ) R)
    (hgood : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ Tp ∧ ρ.im ≠ -Tp)
    (hleft : ∀ s : ℂ, s.re = a → riemannZeta₁ s ≠ 0) :
    DifferentiableOn ℂ (tiltRemainder x hx (zRectZeros hR a b Tp)) (closedContourRect a b Tp) := by
  have hZ0 : (0 : ℂ) ∉ zRectZeros hR a b Tp := fun h => by
    have hz := zRectZeros_zero hR a b Tp h
    rw [riemannZeta₁_zero] at hz
    norm_num at hz
  have hZ1 : (1 : ℂ) ∉ zRectZeros hR a b Tp := one_not_mem_zRectZeros hR a b Tp
  have hZ : ∀ ρ ∈ zRectZeros hR a b Tp, riemannZeta₁ ρ = 0 := fun ρ hρ => zRectZeros_zero hR a b Tp hρ
  intro s hs
  by_cases hs0 : s = 0
  · subst hs0
    exact (analyticAt_tiltRemainder_zero hx hZ0).differentiableAt.differentiableWithinAt
  · by_cases hs1 : s = 1
    · subst hs1
      exact (analyticAt_tiltRemainder_one hx hZ1).differentiableAt.differentiableWithinAt
    · by_cases hsZ : s ∈ zRectZeros hR a b Tp
      · exact (analyticAt_tiltRemainder_zeroPole hx hZ hZ0 hZ1 hsZ).differentiableAt.differentiableWithinAt
      · have hζ : riemannZeta₁ s ≠ 0 := by
          intro hz
          have hab : a ≤ b := by linarith
          have hT : -Tp ≤ Tp := by linarith
          have hmem := (mem_closedContourRect hab hT s).mp hs
          obtain ⟨hre1, hre2, him1, him2⟩ := hmem
          have hζz : riemannZeta s = 0 := by
            rw [riemannZeta_eq_inv_sub_mul hs1, hz, mul_zero]
          rcases lt_trichotomy s.re a with h | h | h
          · linarith
          · exact hleft s h hz
          · rcases lt_trichotomy s.re b with h2 | h2 | h2
            · refine hsZ ?_
              rw [zRectZeros, memS_zetaZeroRectFin]
              refine ⟨(zetaZeroBallFin_spec R hR s).mpr ⟨hrect hs, hz⟩, ?_⟩
              simp only [RectInside, zRect_re, wRect_re, zRect_im, wRect_im]
              refine ⟨h, h2, ?_, ?_⟩
              · rcases lt_trichotomy (-Tp) s.im with h3 | h3 | h3
                · exact h3
                · exact absurd h3.symm (hgood s hz).2
                · linarith
              · rcases lt_trichotomy s.im Tp with h3 | h3 | h3
                · exact h3
                · exact absurd h3 (hgood s hz).1
                · linarith
            · exact riemannZeta_ne_zero_of_one_le_re (by rw [h2]; linarith) hζz
            · linarith
        exact (analyticAt_tiltRemainder_of_ne hx hs0 hs1 hsZ hζ).differentiableAt.differentiableWithinAt

/-! ## The residue identity on the far-left rectangle -/

/-- `-1` lies in the interior of `closedContourRect a b Tp` when `a < -1 < b`, `Tp > 0`. -/
lemma closedContourRect_mem_nhds {a b Tp : ℝ} (ha : a < -1) (h1b : 1 < b) (hTp : 0 < Tp) :
    closedContourRect a b Tp ∈ 𝓝 (-1 : ℂ) := by
  have hbox : {s : ℂ | a < s.re ∧ s.re < b ∧ -Tp < s.im ∧ s.im < Tp} ∈ 𝓝 (-1 : ℂ) := by
    have h1 : IsOpen {s : ℂ | a < s.re} := isOpen_lt continuous_const continuous_re
    have h2 : IsOpen {s : ℂ | s.re < b} := isOpen_lt continuous_re continuous_const
    have h3 : IsOpen {s : ℂ | -Tp < s.im} := isOpen_lt continuous_const continuous_im
    have h4 : IsOpen {s : ℂ | s.im < Tp} := isOpen_lt continuous_im continuous_const
    have hopen : IsOpen {s : ℂ | a < s.re ∧ s.re < b ∧ -Tp < s.im ∧ s.im < Tp} := by
      simpa only [Set.setOf_and] using (h1.inter (h2.inter (h3.inter h4)))
    refine hopen.mem_nhds ?_
    simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
      neg_neg, neg_zero]
    exact ⟨ha, by linarith, by linarith, hTp⟩
  refine Filter.mem_of_superset hbox ?_
  intro s hs
  obtain ⟨h1, h2, h3, h4⟩ := hs
  exact (mem_closedContourRect (by linarith) (by linarith) s).mpr ⟨h1.le, h2.le, h3.le, h4.le⟩

theorem rectInt_tiltIntF_engineSum {R a b Tp x : ℝ} (hR : 0 ≤ R) (hx : 0 < x)
    (ha : a < -1) (h1b : 1 < b) (hTp : 0 < Tp)
    (hrect : closedContourRect a b Tp ⊆ Metric.closedBall (0 : ℂ) R)
    (hgood : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ Tp ∧ ρ.im ≠ -Tp)
    (hleft : ∀ s : ℂ, s.re = a → riemannZeta₁ s ≠ 0) :
    rectInt (zRect a Tp) (wRect b Tp) (tiltIntF x) =
      ((x : ℂ) ^ 2 / 2 - (x : ℂ) * Complex.log (2 * (Real.pi : ℂ)) +
        logDeriv riemannZeta (-1) -
        ∑ ρ ∈ zRectZeros hR a b Tp, (zeta1Order ρ : ℂ) * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))) *
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
  set Z := zRectZeros hR a b Tp with hZdef
  have hZ0 : (0 : ℂ) ∉ Z := by
    rw [hZdef]
    intro h
    have hz := zRectZeros_zero hR a b Tp h
    rw [riemannZeta₁_zero] at hz
    norm_num at hz
  have hZ1 : (1 : ℂ) ∉ Z := by rw [hZdef]; exact one_not_mem_zRectZeros hR a b Tp
  have hm1 : (-1 : ℂ) ∉ Z := by
    rw [hZdef]
    intro h
    have hz := zRectZeros_zero hR a b Tp h
    have hz1' : riemannZeta₁ (-1) ≠ 0 :=
      zeta1_ne_zero_of_re_le_zero (by norm_num) (by norm_num)
    exact hz1' hz
  -- membership facts
  have hZstrict : ∀ t : ℂ, t ∈ Z → a < t.re ∧ t.re < b ∧ -Tp < t.im ∧ t.im < Tp := by
    intro t ht
    have h1 : t ∈ zetaZeroRectFin (R := R) hR (zRect a Tp) (wRect b Tp) := by
      rw [← zRectZeros]
      rw [hZdef] at ht
      exact ht
    have h3 := ((memS_zetaZeroRectFin hR).mp h1).2
    simp only [RectInside, zRect_re, wRect_re, zRect_im, wRect_im] at h3
    exact h3
  have hu : ∀ i ∈ tiltPoles Z, (zRect a Tp).re < i.re ∧ i.re < (wRect b Tp).re ∧
      (zRect a Tp).im < i.im ∧ i.im < (wRect b Tp).im := by
    intro i hi
    rw [tiltPoles] at hi
    rcases Finset.mem_insert.mp hi with h | h
    · subst h
      simp only [zRect_re, wRect_re, zRect_im, wRect_im, Complex.zero_re, Complex.zero_im]
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    rcases Finset.mem_insert.mp h with h | h
    · subst h
      simp only [zRect_re, wRect_re, zRect_im, wRect_im, Complex.one_re, Complex.one_im]
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    rcases Finset.mem_insert.mp h with h | h
    · subst h
      simp only [zRect_re, wRect_re, zRect_im, wRect_im, Complex.neg_re, Complex.neg_im,
        Complex.one_re, Complex.one_im]
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · simp only [zRect_re, wRect_re, zRect_im, wRect_im]
      exact hZstrict i h
  have hG : DifferentiableOn ℂ (fun s => (x : ℂ) * dslope (tiltRemainder x hx Z) (-1) s)
      (Set.uIcc (zRect a Tp).re (wRect b Tp).re ×ℂ Set.uIcc (zRect a Tp).im (wRect b Tp).im) := by
    rw [zRect_re, wRect_re, zRect_im, wRect_im]
    have hnb : closedContourRect a b Tp ∈ 𝓝 (-1 : ℂ) := closedContourRect_mem_nhds ha h1b hTp
    have hd : DifferentiableOn ℂ (tiltRemainder x hx Z) (closedContourRect a b Tp) := by
      rw [hZdef]
      exact tiltRemainder_differentiableOn hx hR ha h1b hTp hrect hgood hleft
    have hD := (Complex.differentiableOn_dslope (f := tiltRemainder x hx Z) (c := (-1 : ℂ)) hnb).mpr hd
    exact hD.const_mul (x : ℂ)
  have hmodel : rectInt (zRect a Tp) (wRect b Tp)
      (fun t => (∑ i ∈ tiltPoles Z, tiltCoeff x i / (t - i))
        + (x : ℂ) * dslope (tiltRemainder x hx Z) (-1) t)
      = (∑ i ∈ tiltPoles Z, tiltCoeff x i) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
    have h := rectInt_model_multi_pole (s := tiltPoles Z) (u := fun i : ℂ => i)
      (z := zRect a Tp) (w := wRect b Tp) (c := fun i => tiltCoeff x i)
      (G := fun s => (x : ℂ) * dslope (tiltRemainder x hx Z) (-1) s)
      (by simp only [zRect_re, wRect_re]; linarith)
      (by simp only [zRect_im, wRect_im]; linarith) hu hG
    simpa only using h
  have hnotZ_of_im {t : ℂ} (h1 : t.im = Tp ∨ t.im = -Tp) : t ∉ Z := by
    intro hmem
    have h := (hZstrict t hmem).2.2
    rcases h1 with h1 | h1 <;> · rw [h1] at h; linarith
  have hnotZ_of_re {t : ℂ} (h1 : t.re = a ∨ t.re = b) : t ∉ Z := by
    intro hmem
    have h := hZstrict t hmem
    rcases h1 with h1 | h1
    · rw [h1] at h; linarith [h.1]
    · rw [h1] at h; linarith [h.2.1]
  have hne_of_im {t : ℂ} (h1 : t.im = Tp ∨ t.im = -Tp) : t ≠ 0 ∧ t ≠ 1 ∧ t ≠ -1 := by
    rcases h1 with h1 | h1
    · refine ⟨?_, ?_, ?_⟩ <;> · intro h; rw [h] at h1; simp at h1; linarith
    · refine ⟨?_, ?_, ?_⟩ <;> · intro h; rw [h] at h1; simp at h1; linarith
  have hne_of_re {t : ℂ} (h1 : t.re = a ∨ t.re = b) : t ≠ 0 ∧ t ≠ 1 ∧ t ≠ -1 := by
    rcases h1 with h1 | h1 <;> refine ⟨?_, ?_, ?_⟩ <;> · intro h; rw [h] at h1; simp at h1 <;> linarith
  have hcong : rectInt (zRect a Tp) (wRect b Tp) (tiltIntF x)
      = rectInt (zRect a Tp) (wRect b Tp)
          (fun t => (∑ i ∈ tiltPoles Z, tiltCoeff x i / (t - i))
            + (x : ℂ) * dslope (tiltRemainder x hx Z) (-1) t) := by
    refine rectInt_congr_boundary ?_ ?_ ?_ ?_
    · intro x0 _
      have hy : ((x0 : ℂ) + ↑(zRect a Tp).im * Complex.I).im = -Tp := by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, zRect_im]
        ring
      obtain ⟨h0, h1, hm₁⟩ := hne_of_im (Or.inr hy)
      exact tiltIntF_eq_model hx hZ0 hZ1 hm1 h0 h1 (hnotZ_of_im (Or.inr hy)) hm₁
    · intro x0 _
      have hy : ((x0 : ℂ) + ↑(wRect b Tp).im * Complex.I).im = Tp := by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, wRect_im]
        ring
      obtain ⟨h0, h1, hm₁⟩ := hne_of_im (Or.inl hy)
      exact tiltIntF_eq_model hx hZ0 hZ1 hm1 h0 h1 (hnotZ_of_im (Or.inl hy)) hm₁
    · intro y _
      have hx' : ((wRect b Tp).re + ↑y * Complex.I).re = b := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, wRect_re]
        ring
      obtain ⟨h0, h1, hm₁⟩ := hne_of_re (Or.inr hx')
      exact tiltIntF_eq_model hx hZ0 hZ1 hm1 h0 h1 (hnotZ_of_re (Or.inr hx')) hm₁
    · intro y _
      have hx' : ((zRect a Tp).re + ↑y * Complex.I).re = a := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, zRect_re]
        ring
      obtain ⟨h0, h1, hm₁⟩ := hne_of_re (Or.inl hx')
      exact tiltIntF_eq_model hx hZ0 hZ1 hm1 h0 h1 (hnotZ_of_re (Or.inl hx')) hm₁
  rw [hcong, hmodel]
  congr 1
  rw [tiltPoles_sum hZ0 hZ1 hm1, tiltCoeff_zero, tiltCoeff_one, tiltCoeff_neg_one, caZeroCoeff,
    mul_psiIntF1_neg_one hx]
  have hsum : (∑ ρ ∈ Z, tiltCoeff x ρ)
      = - ∑ ρ ∈ Z, (zeta1Order ρ : ℂ) * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun ρ hρ => ?_)
    rw [tiltCoeff_of_mem hx hρ hZ0 hZ1 hm1]
    unfold tiltC
    rw [cpow_add_one hx ρ]
    field_simp
  rw [hsum]
  ring

/-! ## Bounds on the boundary edges -/

/-- on the line `Re s = 2` the tilted kernel is the classical Perron kernel. -/
lemma tiltIntF_two_add {x : ℝ} (hx : 0 < x) (y : ℝ) :
    tiltIntF x ((2 : ℂ) + Complex.I * (y : ℂ))
      = (-(deriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))) /
            riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ)))
          * (x : ℂ) ^ ((2 : ℂ) + Complex.I * (y : ℂ) + 1)
          / (((2 : ℂ) + Complex.I * (y : ℂ)) *
              ((2 : ℂ) + Complex.I * (y : ℂ) + 1)) := by
  set s : ℂ := (2 : ℂ) + Complex.I * (y : ℂ) with hs
  have hsre : s.re = 2 := by simp [s]
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hsre] at this; norm_num at this
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hsre] at this; norm_num at this
  have hsp1 : s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re] at this; rw [hsre] at this; norm_num at this
  have hpsi : psiIntF1 x s = -(deriv riemannZeta s) / riemannZeta s * (x : ℂ) ^ s / s := by
    rw [psiIntF1_eq_psiIntF_on_re_ge_one (by rw [hsre]; norm_num) hs1]
    rfl
  rw [tiltIntF_apply, hpsi]
  rw [cpow_add_one hx s]
  rw [hs]
  field_simp

/-- the left edge integral as a function of the vertical cut `a`. -/
noncomputable def tiltLeftLimit (x a : ℝ) : ℂ :=
  ∫ y : ℝ, tiltIntF x ((a : ℂ) + Complex.I * (y : ℂ))


lemma tiltIntF_norm_le {x : ℝ} (hx : 0 ≤ x) {s : ℂ} :
    ‖tiltIntF x s‖ ≤ x * ‖psiIntF1 x s‖ / ‖s + 1‖ := by
  rw [tiltIntF_apply, norm_div, norm_mul,
    show ‖(x : ℂ)‖ = x by simp [Real.norm_eq_abs, abs_of_nonneg hx]]

/-- the tilted kernel on the horizontal line `Im s = T` is small when `logDeriv ζ₁` is. -/
lemma tiltIntF_horiz_le {x a T C : ℝ} (hx : 1 ≤ x) (ha : a ≤ 2) (hT : 5 ≤ T) (hC : 0 ≤ C)
    (hb : ∀ σ ∈ Set.uIcc a 2, ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤ C)
    {σ : ℝ} (hσ : σ ∈ Set.uIcc a 2) :
    ‖tiltIntF x ((σ : ℂ) + Complex.I * (T : ℂ))‖ ≤ 4 * x ^ (4 : ℝ) * (C + 1) / T ^ 2 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hT0 : (0 : ℝ) < T := by linarith
  set s : ℂ := (σ : ℂ) + Complex.I * (T : ℂ) with hs
  have hsim : s.im = T := by simp [s]
  have hsre : s.re = σ := by simp [s]
  have hsT : T ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    rw [hsim, abs_of_nonneg (by linarith)] at h
    exact h
  have hsp1 : T / 2 ≤ ‖s + 1‖ := by
    have h := Complex.abs_im_le_norm (s + 1)
    have h2 : (s + 1).im = T := by simp [s]
    rw [h2, abs_of_nonneg (by linarith)] at h
    linarith
  have hsm1 : T / 2 ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    have h2 : (s - 1).im = T := by simp [s]
    rw [h2, abs_of_nonneg (by linarith)] at h
    linarith
  have hσ2 : σ ≤ 2 := by
    have := hσ; rw [Set.uIcc_of_le ha] at this; exact this.2
  have hxσ : x ^ s.re ≤ x ^ (3 : ℝ) := by
    rw [hsre]
    calc x ^ σ ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hσ2
      _ ≤ x ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hlog := hb σ hσ
  have hpsi' : ‖psiIntF1 x s‖ ≤ (C + 1) * (x ^ (3 : ℝ) / T) := by
    have h1 : ‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖ ≤ C + 1 := by
      have h2 : 1 / ‖s - 1‖ ≤ 1 := by
        rw [div_le_one (by linarith [hsm1])]
        linarith [hsm1]
      linarith [hlog]
    have h3 : x ^ s.re / ‖s‖ ≤ x ^ (3 : ℝ) / T := by
      calc x ^ s.re / ‖s‖ ≤ x ^ (3 : ℝ) / ‖s‖ :=
            div_le_div_of_nonneg_right hxσ (norm_nonneg s)
        _ ≤ x ^ (3 : ℝ) / T :=
            div_le_div_of_nonneg_left (by positivity) hT0 hsT
    calc ‖psiIntF1 x s‖
        ≤ (‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖) * (x ^ s.re / ‖s‖) :=
          psiIntF1_norm_le_logDeriv hx0 s
      _ ≤ (C + 1) * (x ^ (3 : ℝ) / T) := by
          refine mul_le_mul h1 h3 (by positivity) (by linarith)
  calc ‖tiltIntF x s‖ ≤ x * ‖psiIntF1 x s‖ / ‖s + 1‖ := tiltIntF_norm_le hx0.le
    _ ≤ x * ((C + 1) * (x ^ (3 : ℝ) / T)) / ‖s + 1‖ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpsi' hx0.le) (norm_nonneg _)
    _ ≤ x * ((C + 1) * (x ^ (3 : ℝ) / T)) / (T / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) hsp1
    _ ≤ 4 * x ^ (4 : ℝ) * (C + 1) / T ^ 2 := by
        have hx4 : x * x ^ (3 : ℝ) = x ^ (4 : ℝ) := by
          nth_rewrite 1 [show x = x ^ (1 : ℝ) by rw [Real.rpow_one]]
          rw [← Real.rpow_add hx0, show (1 : ℝ) + 3 = 4 by norm_num]
        have heq : x * ((C + 1) * (x ^ (3 : ℝ) / T)) / (T / 2)
            = 2 * x ^ (4 : ℝ) * (C + 1) / T ^ 2 := by
          rw [← hx4]
          field_simp
        rw [heq]
        rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < T ^ 2)]
        nlinarith [hC, Real.rpow_nonneg hx0.le (4 : ℝ)]

/-! ## The digamma bound in the right half-plane -/

lemma digamma_add_nat_rec (m : ℕ) (w : ℂ)
    (hw : ∀ j : ℕ, j < m → ∀ n : ℕ, w + (j : ℂ) ≠ -(n : ℂ)) :
    Complex.digamma (w + (m : ℂ)) = Complex.digamma w + ∑ j ∈ Finset.range m, (w + (j : ℂ))⁻¹ := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, show w + ((k + 1 : ℕ) : ℂ) = (w + (k : ℂ)) + 1 by push_cast; ring,
      Complex.digamma_apply_add_one (w + (k : ℂ)) (fun n => hw k (Nat.lt_succ_self k) n),
      ih (fun j hj => hw j (Nat.lt_succ_of_lt hj))]
    ring

theorem digamma_right_half_le :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 2 ≤ w.re → ‖Complex.digamma w‖ ≤ C * (Real.log (‖w‖ + 2) + 1) := by
  refine ⟨8, by norm_num, fun w hw => ?_⟩
  set m : ℕ := ⌊w.re⌋₊ - 1 with hm
  have hfloor : (2 : ℕ) ≤ ⌊w.re⌋₊ := Nat.le_floor (by exact_mod_cast hw)
  have hmcast : ((m : ℕ) : ℝ) = (⌊w.re⌋₊ : ℝ) - 1 := by
    rw [hm, Nat.cast_sub (by omega)]; push_cast; ring
  have hm_le : (m : ℝ) ≤ w.re - 1 := by
    have h1 : (⌊w.re⌋₊ : ℝ) ≤ w.re := Nat.floor_le (by linarith)
    rw [hmcast]; linarith
  have hm_ge : w.re - 2 < (m : ℝ) := by
    have h1 : w.re < (⌊w.re⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one w.re
    rw [hmcast]; linarith
  have hmn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hre1 : (w - (m : ℂ)).re ≥ (1 / 2 : ℝ) := by
    simp only [Complex.sub_re, Complex.natCast_re]; linarith
  have hre2 : (w - (m : ℂ)).re ≤ 8 := by
    simp only [Complex.sub_re, Complex.natCast_re]; linarith
  have hmid : ‖Complex.digamma (w - (m : ℂ))‖ ≤ Real.log (2 + |(w - (m : ℂ)).im|) + 2 := by
    have h := Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le
      (w - (m : ℂ)).re (w - (m : ℂ)).im hre1 hre2
    convert h using 2
    rw [Complex.re_add_im]
  have hrec := digamma_add_nat_rec m (w - (m : ℂ)) (by
    intro j hj n hcon
    have hre : ((w - (m : ℂ)) + (j : ℂ)).re = w.re - (m : ℝ) + (j : ℝ) := by
      simp [Complex.add_re, Complex.sub_re]
    have hpos : 0 < ((w - (m : ℂ)) + (j : ℂ)).re := by
      rw [hre]
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hneg : ((-(n : ℂ))).re = -(n : ℝ) := by simp
    have := congrArg Complex.re hcon
    rw [hre, hneg] at this
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith)
  have hcast : (w - (m : ℂ)) + (m : ℂ) = w := by ring
  rw [hcast] at hrec
  have hsum : ‖∑ j ∈ Finset.range m, ((w - (m : ℂ)) + (j : ℂ))⁻¹‖
      ≤ 2 + Real.log (m : ℝ) := by
    have h1 : ∀ j ∈ Finset.range m, ‖((w - (m : ℂ)) + (j : ℂ))⁻¹‖ ≤ (1 / ((j : ℝ) + 1)) := by
      intro j hj
      have hre : ((w - (m : ℂ)) + (j : ℂ)).re = w.re - (m : ℝ) + (j : ℝ) := by
        simp [Complex.add_re, Complex.sub_re]
      have hz : ((w - (m : ℂ)) + (j : ℂ)) ≠ 0 := by
        intro h0
        have hre0 : ((w - (m : ℂ)) + (j : ℂ)).re = 0 := by rw [h0]; simp
        rw [hre] at hre0
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      have hge : (j : ℝ) + 1 ≤ ‖((w - (m : ℂ)) + (j : ℂ))‖ := by
        have := Complex.re_le_norm ((w - (m : ℂ)) + (j : ℂ))
        rw [hre] at this
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      rw [norm_inv]
      calc ‖((w - (m : ℂ)) + (j : ℂ))‖⁻¹ ≤ ((j : ℝ) + 1)⁻¹ :=
            (inv_le_inv₀ (norm_pos_iff.mpr hz) (by positivity)).mpr hge
        _ = 1 / ((j : ℝ) + 1) := by rw [one_div]
    calc ‖∑ j ∈ Finset.range m, ((w - (m : ℂ)) + (j : ℂ))⁻¹‖
        ≤ ∑ j ∈ Finset.range m, ‖((w - (m : ℂ)) + (j : ℂ))⁻¹‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range m, (1 / ((j : ℝ) + 1)) := Finset.sum_le_sum h1
      _ = (harmonic m : ℝ) := by
          rw [harmonic]
          push_cast
          refine Finset.sum_congr rfl (fun j hj => ?_)
          push_cast
          rw [one_div]
      _ ≤ 2 + Real.log (m : ℝ) := by
          rcases Nat.eq_zero_or_pos m with h | h
          · rw [h]; simp only [Nat.cast_zero, Real.log_zero, harmonic]
            norm_num
          · have hb := Commons.NumberTheory.Harmonic.abs_harmonic_sub_log_sub_euler_le_inv m h
            have h1 : (harmonic m : ℝ) - Real.log (m : ℝ) - Real.eulerMascheroniConstant
                ≤ 1 / (m : ℝ) := (abs_le.mp hb).2
            have h2 : 1 / (m : ℝ) ≤ 1 := by
              rw [div_le_one (by exact_mod_cast h)]
              exact_mod_cast h
            have h3 : Real.eulerMascheroniConstant ≤ 1 :=
              Commons.Analysis.SpecialFunctions.Gamma.eulerMascheroniConstant_le_one
            linarith
  have hlog1 : Real.log (2 + |(w - (m : ℂ)).im|) ≤ 1 + Real.log (‖w‖ + 2) := by
    have h1 : |(w - (m : ℂ)).im| ≤ ‖w‖ + (m : ℝ) := by
      have h2 := Complex.abs_im_le_norm (w - (m : ℂ))
      have h3 : ‖w - (m : ℂ)‖ ≤ ‖w‖ + (m : ℝ) := by
        calc ‖w - (m : ℂ)‖ ≤ ‖w‖ + ‖(m : ℂ)‖ := norm_sub_le _ _
          _ = ‖w‖ + (m : ℝ) := by simp
      linarith
    have hmnorm : (m : ℝ) ≤ ‖w‖ := by
      have h2 : (m : ℝ) ≤ w.re := by linarith [hm_le]
      linarith [Complex.re_le_norm w]
    have h4 : 2 + |(w - (m : ℂ)).im| ≤ 2 * (‖w‖ + 2) := by linarith [h1, hmnorm]
    calc Real.log (2 + |(w - (m : ℂ)).im|) ≤ Real.log (2 * (‖w‖ + 2)) :=
          Real.log_le_log (by positivity) h4
      _ = Real.log 2 + Real.log (‖w‖ + 2) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ 1 + Real.log (‖w‖ + 2) := by
          have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
          linarith
  have hlog2 : Real.log (m : ℝ) ≤ Real.log (‖w‖ + 2) := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h]; simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by linarith [norm_nonneg w])
    · refine Real.log_le_log (by positivity) ?_
      have h2 : (m : ℝ) ≤ w.re := by linarith [hm_le]
      have h3 : w.re ≤ ‖w‖ := Complex.re_le_norm w
      linarith
  have hL : 0 ≤ Real.log (‖w‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg w])
  calc ‖Complex.digamma w‖
      = ‖Complex.digamma (w - (m : ℂ)) + ∑ j ∈ Finset.range m, ((w - (m : ℂ)) + (j : ℂ))⁻¹‖ := by
        rw [← hrec]
    _ ≤ ‖Complex.digamma (w - (m : ℂ))‖ + ‖∑ j ∈ Finset.range m, ((w - (m : ℂ)) + (j : ℂ))⁻¹‖ :=
        norm_add_le _ _
    _ ≤ (Real.log (2 + |(w - (m : ℂ)).im|) + 2) + (2 + Real.log (m : ℝ)) :=
        add_le_add hmid hsum
    _ ≤ 8 * (Real.log (‖w‖ + 2) + 1) := by linarith [hlog1, hlog2, hL]

/-! ## The logarithmic derivative far left -/

/-- A uniform bound for `‖digamma w‖` on the half-plane `Re w ≥ 3/2`. -/
lemma digamma_re_ge_le : ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, (3 / 2 : ℝ) ≤ w.re →
    ‖Complex.digamma w‖ ≤ C * (Real.log (‖w‖ + 2) + 1) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := digamma_right_half_le
  refine ⟨max C₁ 3, lt_of_lt_of_le (by norm_num : (0:ℝ) < 3) (le_max_right C₁ 3), fun w hw => ?_⟩
  by_cases h2 : (2 : ℝ) ≤ w.re
  · have h3 : (0:ℝ) < 3 := by norm_num
    exact le_trans (hC₁ w h2) (mul_le_mul_of_nonneg_right (le_max_left C₁ 3)
      (by have h4 := Real.log_nonneg (by linarith [norm_nonneg w] : (1:ℝ) ≤ ‖w‖ + 2)
          linarith))
  · push_neg at h2
    have hmid := Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le w.re w.im
      (by linarith) (by linarith)
    have hEq : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
    rw [hEq]
    set u : ℂ := (w.re : ℂ) + (w.im : ℂ) * Complex.I with hu
    have hu_im : u.im = w.im := by simp [u]
    have h1 : Real.log (2 + |w.im|) ≤ Real.log (‖u‖ + 2) := by
      refine Real.log_le_log (by positivity) ?_
      have h3 := Complex.abs_im_le_norm u
      rw [hu_im] at h3
      linarith
    have h2' : 0 ≤ Real.log (‖u‖ + 2) := by
      refine Real.log_nonneg ?_
      have h3 := norm_nonneg u
      linarith
    calc ‖Complex.digamma u‖ ≤ Real.log (2 + |w.im|) + 2 := hmid
      _ ≤ (max C₁ 3) * (Real.log (‖u‖ + 2) + 1) := by
          have h3 : (3 : ℝ) ≤ max C₁ 3 := le_max_right C₁ 3
          nlinarith

/-- The tangent of `π(N+1) - i t` is that of a pure imaginary argument: `‖tan‖ ≤ 1`. -/
lemma tan_piN_sub_le (N : ℕ) (t : ℝ) :
    ‖Complex.tan (((N : ℂ) + 1) * (↑Real.pi) - ((t : ℂ) * Complex.I))‖ ≤ 1 := by
  set u : ℂ := (((N + 1 : ℕ)) : ℂ) * (↑Real.pi) with hu
  set v : ℂ := -((t : ℂ) * Complex.I) with hv
  have hz : ((N : ℂ) + 1) * (↑Real.pi) - ((t : ℂ) * Complex.I) = u + v := by
    rw [hu, hv]; push_cast; ring
  have hsinu : Complex.sin u = 0 := by rw [hu]; exact Complex.sin_nat_mul_pi (N + 1)
  have hcosu : Complex.cos u ≠ 0 := by
    intro h0
    have hsc := Complex.sin_sq_add_cos_sq u
    rw [hsinu, h0] at hsc
    norm_num at hsc
  rw [hz, Complex.tan_eq_sin_div_cos, Complex.sin_add, Complex.cos_add, hsinu, zero_mul, zero_add,
    zero_mul, sub_zero]
  rw [mul_div_mul_left _ _ hcosu]
  rw [← Complex.tan_eq_sin_div_cos]
  rw [hv, Complex.tan_neg, Complex.tan_mul_I, ← Complex.ofReal_tanh, norm_neg, norm_mul,
    Complex.norm_I, mul_one]
  have hnorm : ‖((Real.tanh t : ℝ) : ℂ)‖ = |Real.tanh t| := by
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs]
  rw [hnorm]
  exact le_of_lt (Real.abs_tanh_lt_one t)

lemma cos_nat_mul_pi_ne_zero (n : ℕ) : Complex.cos ((n : ℂ) * (↑Real.pi)) ≠ 0 := by
  intro h0
  have hsc := Complex.sin_sq_add_cos_sq ((n : ℂ) * (↑Real.pi))
  rw [Complex.sin_nat_mul_pi, h0] at hsc
  norm_num at hsc

/-- the functional-equation decomposition of `logDeriv ζ₁`. -/
lemma logDeriv_zeta1_FE_eq {s w : ℂ} (hw : w = 1 - s) (hζs : riemannZeta s ≠ 0)
    (hζw : riemannZeta w ≠ 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hGamma : ∀ n : ℕ, w ≠ -(n : ℂ)) (hcos : Complex.cos ((↑Real.pi) * w / 2) ≠ 0) :
    logDeriv riemannZeta₁ s = Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma w
      + ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * w / 2)
      - deriv riemannZeta w / riemannZeta w + (s - 1)⁻¹ := by
  have hζw' : riemannZeta (1 - s) ≠ 0 := by rw [← hw]; exact hζw
  have hGamma' : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by intro n; rw [← hw]; exact hGamma n
  have hcos' : Complex.cos ((↑Real.pi) * (1 - s) / 2) ≠ 0 := by rw [← hw]; exact hcos
  have hFE := zeta_logDeriv_fe_expanded hζs hζw' hs0 hs1 hGamma' hcos'
  have hlog1 := logDeriv_zeta1_eq (s := s) hs1 (zeta1_ne_zero_iff_zeta_ne_zero hs1 |>.mpr hζs)
  rw [hlog1, hFE, hw]
  push_cast
  ring

/-- The FE-based bound for `logDeriv ζ₁` far to the left of the critical strip. -/
theorem logDeriv_riemannZeta1_halfplane_far_t_le :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, σ ≤ -(1 / 2 : ℝ) → 2 ≤ |t| →
      ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (t : ℂ))‖
        ≤ C * (Real.log (|σ| + |t| + 3)) ^ 4 := by
  obtain ⟨M, hMpos, hMle, hMb⟩ := logDeriv_zeta_const_bound_b
  obtain ⟨Cdg, hCdgpos, hCdg⟩ := digamma_re_ge_le
  refine ⟨100 * (M + Cdg + 10), by linarith, fun σ t hσ ht => ?_⟩
  set s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ) with hs
  set w : ℂ := 1 - s with hw
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hwre : w.re = 1 - σ := by simp [w, s]
  have hwim : w.im = -t := by simp [w, s]
  have hwre2 : (3 / 2 : ℝ) ≤ w.re := by rw [hwre]; linarith
  have ht2 : (2 : ℝ) ≤ |t| := ht
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; rw [hsre] at this; simp at this; linarith
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hsre] at this; simp at this; linarith
  have hζs : riemannZeta s ≠ 0 := by
    intro hz
    obtain ⟨n, hn⟩ := trivial_zero_of_riemannZeta_eq_zero_of_re_nonpos hz (by rw [hsre]; linarith)
    have h1 : t = 0 := by
      have h2 := congrArg Complex.im hn
      rw [hsim] at h2
      have h3 : ((-2 : ℂ) * ((n : ℂ) + 1)).im = 0 := by simp
      rw [h3] at h2
      exact h2
    rw [h1, abs_zero] at ht2
    linarith
  have hζw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hwre]; linarith)
  have hGamma : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n h
    have h1 := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at h1
    rw [hwre] at h1
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hpiw : ((↑Real.pi) * w / 2) = (((Real.pi / 2 : ℝ)) : ℂ) * w := by push_cast; ring_nf
  have hcos : Complex.cos ((↑Real.pi) * w / 2) ≠ 0 := by
    intro h0
    rw [hpiw] at h0
    rw [Complex.cos_eq_zero_iff] at h0
    obtain ⟨k, hk⟩ := h0
    have h1 := congrArg Complex.im hk
    have him : (((2 * (k : ℂ) + 1) * (↑Real.pi) / 2)).im = 0 := by simp
    rw [him, Complex.mul_im] at h1
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hwim] at h1
    have h2 : Real.pi / 2 * t = 0 := by linarith
    have ht0 : t = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · nlinarith [Real.pi_pos]
      · exact h
    rw [ht0, abs_zero] at ht2
    linarith
  have hkey := logDeriv_zeta1_FE_eq hw hζs hζw hs0 hs1 hGamma hcos
  rw [hkey]
  have htan : ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * w / 2)‖ ≤ 8 := by
    have h2 : ‖Complex.tan ((↑Real.pi) * w / 2)‖ ≤ 4 := by
      refine Commons.Analysis.SpecialFunctions.Trigonometric.tan_norm_le_of_abs_im_ge _ ?_
      have h3 : ((↑Real.pi) * w / 2).im = -(π * t) / 2 := by
        rw [hpiw, Complex.mul_im]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hwim]
        ring
      rw [h3, abs_div, abs_neg, abs_mul, abs_of_nonneg Real.pi_pos.le]
      norm_num
      have h4 : (1 : ℝ) ≤ Real.pi * |t| / 2 := by
        have := Real.pi_gt_three
        nlinarith
      linarith
    rw [norm_mul]
    have h1 : ‖((Real.pi / 2 : ℝ) : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_of_nonneg (by positivity)]
      have := Real.pi_lt_four
      linarith
    calc ‖((Real.pi / 2 : ℝ) : ℂ)‖ * ‖Complex.tan ((↑Real.pi) * w / 2)‖ ≤ 2 * 4 :=
          mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      _ ≤ 8 := by norm_num
  have hdig : ‖Complex.digamma w‖ ≤ Cdg * (Real.log (|σ| + |t| + 3) + 1) := by
    have h1 := hCdg w hwre2
    have h2 : ‖w‖ + 2 ≤ |σ| + |t| + 3 := by
      have h3 : ‖w‖ = ‖s - 1‖ := by
        rw [hw, show (1 : ℂ) - s = -(s - 1) by ring, norm_neg]
      rw [h3]
      have h4 : ‖s‖ ≤ |σ| + |t| := by
        rw [hs]
        calc ‖(σ : ℂ) + Complex.I * (t : ℂ)‖
            ≤ ‖(σ : ℂ)‖ + ‖Complex.I * (t : ℂ)‖ := norm_add_le _ _
          _ = |σ| + |t| := by simp
      have h5 : ‖s - 1‖ ≤ ‖s‖ + 1 := by simpa using norm_sub_le s 1
      linarith
    calc ‖Complex.digamma w‖ ≤ Cdg * (Real.log (‖w‖ + 2) + 1) := h1
      _ ≤ Cdg * (Real.log (|σ| + |t| + 3) + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hCdgpos.le
          have h3 := Real.log_le_log (by positivity) h2
          nlinarith [h3]
  have hl2pi : ‖Complex.log (2 * (Real.pi : ℂ))‖ ≤ 2 := by
    have h1 : Complex.log (2 * (Real.pi : ℂ)) = ((Real.log (2 * Real.pi) : ℝ) : ℂ) := by
      rw [show (2 * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ)) : ℂ) by push_cast; ring,
        ← Complex.ofReal_log (by positivity)]
    rw [h1, Complex.norm_of_nonneg (Real.log_nonneg (by nlinarith [Real.pi_gt_three]))]
    exact log_two_pi_le_two
  have hinv : ‖(s - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    refine inv_le_one_of_one_le₀ ?_
    have h2 := Complex.abs_re_le_norm (s - 1)
    simp only [Complex.sub_re, Complex.one_re] at h2
    rw [hsre] at h2
    have h3 : (1 : ℝ) ≤ |σ - 1| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    linarith
  have hMw := hMb w hwre2
  set L : ℝ := Real.log (|σ| + |t| + 3) with hL
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    have h1 := abs_nonneg σ
    have h2 := abs_nonneg t
    nlinarith [Real.exp_one_lt_three]
  have hL4 : (1 : ℝ) ≤ L ^ 4 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hL1 4
  have h10 : (0 : ℝ) ≤ M + Cdg + 10 := by linarith
  have htot : ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma w
      + ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * w / 2)
      - deriv riemannZeta w / riemannZeta w + (s - 1)⁻¹‖ ≤ 10 * ((M + Cdg + 10) * L ^ 4) := by
    have ha := norm_add_le (Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma w
      + ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * w / 2)
      - deriv riemannZeta w / riemannZeta w) ((s - 1)⁻¹)
    have hb := norm_sub_le (Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma w
      + ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * w / 2))
      (deriv riemannZeta w / riemannZeta w)
    have hc := norm_add_le (Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma w)
      (((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * w / 2))
    have hd := norm_sub_le (Complex.log (2 * (Real.pi : ℂ))) (Complex.digamma w)
    have hsum : ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma w
        + ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * w / 2)
        - deriv riemannZeta w / riemannZeta w + (s - 1)⁻¹‖
        ≤ ‖Complex.log (2 * (Real.pi : ℂ))‖ + ‖Complex.digamma w‖
          + ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * w / 2)‖
          + ‖deriv riemannZeta w / riemannZeta w‖ + ‖(s - 1)⁻¹‖ := by
      have h5 : (0:ℝ) ≤ ‖Complex.digamma w‖ := norm_nonneg _
      have h6 : (0:ℝ) ≤ ‖(s - 1)⁻¹‖ := norm_nonneg _
      have h7 : (0:ℝ) ≤ ‖deriv riemannZeta w / riemannZeta w‖ := norm_nonneg _
      have h8 : (0:ℝ) ≤ ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * w / 2)‖ :=
        norm_nonneg _
      have h9 : (0:ℝ) ≤ ‖Complex.log (2 * (Real.pi : ℂ))‖ := norm_nonneg _
      have ha' : ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma w
          + ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * w / 2)
          - deriv riemannZeta w / riemannZeta w + (s - 1)⁻¹‖
          ≤ ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma w
            + ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * w / 2)
            - deriv riemannZeta w / riemannZeta w‖ + ‖(s - 1)⁻¹‖ :=
        norm_add_le _ _
      have hb' : ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma w
            + ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * w / 2)
            - deriv riemannZeta w / riemannZeta w‖
          ≤ ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma w
            + ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * w / 2)‖
            + ‖deriv riemannZeta w / riemannZeta w‖ :=
        norm_sub_le _ _
      have hc' : ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma w
            + ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * w / 2)‖
          ≤ ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma w‖
            + ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * w / 2)‖ :=
        norm_add_le _ _
      have hd' : ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma w‖
          ≤ ‖Complex.log (2 * (Real.pi : ℂ))‖ + ‖Complex.digamma w‖ :=
        norm_sub_le _ _
      linarith [ha', hb', hc', hd', h5, h6, h7, h8, h9]
    have hfin : ‖Complex.log (2 * (Real.pi : ℂ))‖ + ‖Complex.digamma w‖
          + ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * w / 2)‖
          + ‖deriv riemannZeta w / riemannZeta w‖ + ‖(s - 1)⁻¹‖
        ≤ 10 * ((M + Cdg + 10) * L ^ 4) := by
      rw [hL] at hdig hL1 hL4 ⊢
      have hKnn : (0: ℝ) ≤ M + Cdg + 10 := by linarith
      have hCdgnn : (0: ℝ) ≤ Cdg := hCdgpos.le
      have hK1 : (1 : ℝ) ≤ (M + Cdg + 10) * L ^ 4 := by
        have h := mul_le_mul (by linarith : (1:ℝ) ≤ M + Cdg + 10) hL4
          (by norm_num : (0:ℝ) ≤ 1) hKnn
        simpa using h
      have hK2 : (5 : ℝ) ≤ (M + Cdg + 10) * L ^ 4 := by
        have h := mul_le_mul (by linarith : (5:ℝ) ≤ M + Cdg + 10) hL4 (by norm_num : (0:ℝ) ≤ 1)
          hKnn
        simpa using h
      have hMd : M ≤ (M + Cdg + 10) * L ^ 4 := by
        have h := mul_le_mul (by linarith : M ≤ M + Cdg + 10) hL4 (by norm_num : (0:ℝ) ≤ 1) hKnn
        simpa using h
      have hCd : Cdg * (L + 1) ≤ 2 * ((M + Cdg + 10) * L ^ 4) := by
        have h1 : Cdg * (L + 1) ≤ Cdg * (2 * L) :=
          mul_le_mul_of_nonneg_left (by linarith) hCdgnn
        have h2 : Cdg * (2 * L) ≤ (M + Cdg + 10) * (2 * L) :=
          mul_le_mul_of_nonneg_right (by linarith) (by linarith)
        have hLL3 : (1:ℝ) ≤ L ^ 3 := by
          simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hL1 3
        have hL3 : L ≤ L ^ 4 := by
          calc L = L * 1 := by ring
            _ ≤ L * L ^ 3 := mul_le_mul_of_nonneg_left hLL3 (by linarith)
            _ = L ^ 4 := by ring
        have h3 : (M + Cdg + 10) * (2 * L) ≤ 2 * ((M + Cdg + 10) * L ^ 4) := by
          calc (M + Cdg + 10) * (2 * L) ≤ (M + Cdg + 10) * (2 * L ^ 4) :=
                mul_le_mul_of_nonneg_left (by linarith) hKnn
            _ = 2 * ((M + Cdg + 10) * L ^ 4) := by ring
        exact le_trans h1 (le_trans h2 h3)
      have ht1 : ‖Complex.log (2 * (Real.pi : ℂ))‖ ≤ 2 * ((M + Cdg + 10) * L ^ 4) := by
        linarith [hl2pi, hK1]
      have ht2 : ‖Complex.digamma w‖ ≤ 2 * ((M + Cdg + 10) * L ^ 4) :=
        le_trans hdig hCd
      have ht3 : ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * w / 2)‖
          ≤ 2 * ((M + Cdg + 10) * L ^ 4) := by
        linarith [htan, hK2]
      have ht4 : ‖deriv riemannZeta w / riemannZeta w‖ ≤ 2 * ((M + Cdg + 10) * L ^ 4) := by
        linarith [hMw, hMd]
      have ht5 : ‖(s - 1)⁻¹‖ ≤ 2 * ((M + Cdg + 10) * L ^ 4) := by
        linarith [hinv, hK1]
      have h12 := add_le_add ht1 ht2
      have h123 := add_le_add h12 ht3
      have h1234 := add_le_add h123 ht4
      have h12345 := add_le_add h1234 ht5
      calc ‖Complex.log (2 * (Real.pi : ℂ))‖ + ‖Complex.digamma w‖
            + ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * w / 2)‖
            + ‖deriv riemannZeta w / riemannZeta w‖ + ‖(s - 1)⁻¹‖
          ≤ 2 * ((M + Cdg + 10) * L ^ 4) + 2 * ((M + Cdg + 10) * L ^ 4)
            + 2 * ((M + Cdg + 10) * L ^ 4) + 2 * ((M + Cdg + 10) * L ^ 4)
            + 2 * ((M + Cdg + 10) * L ^ 4) := h12345
        _ = 10 * ((M + Cdg + 10) * L ^ 4) := by ring
    exact le_trans hsum hfin
  rw [hL] at htot
  refine le_trans htot ?_
  have h0 : (0:ℝ) ≤ (M + Cdg + 10) * L ^ 4 := by positivity
  have heq : (100 : ℝ) * (M + Cdg + 10) * L ^ 4 = 100 * ((M + Cdg + 10) * L ^ 4) := by ring
  rw [heq]
  linarith [h0]

/-- `ζ'/ζ` on the odd vertical lines `Re s = -(2N+1)` is `O(log(2N+|y|+3))`. -/
theorem zeta_logDeriv_odd_vertical_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (y : ℝ),
      ‖deriv riemannZeta ((((-(((2 * (N : ℝ)) + 1)) : ℝ)) : ℂ) + Complex.I * ((y : ℂ))) /
        riemannZeta ((((-(((2 * (N : ℝ)) + 1)) : ℝ)) : ℂ) + Complex.I * ((y : ℂ)))‖
        ≤ C * (Real.log (2 * (N : ℝ) + |y| + 3) + 1) := by
  obtain ⟨M, hMpos, hMle, hM⟩ := logDeriv_zeta_const_bound_b
  obtain ⟨Cdg, hCdgpos, hCdg⟩ := digamma_re_ge_le
  refine ⟨2 + 2 * Cdg + M + 4, by linarith, ?_⟩
  intro N y
  set X : ℝ := Real.log (2 * (N : ℝ) + |y| + 3) with hX
  have hXnn : 0 ≤ X := by
    rw [hX]
    apply Real.log_nonneg
    have hy0 : (0 : ℝ) ≤ |y| := abs_nonneg y
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  set A : ℝ := -(((2 * (N : ℝ)) + 1)) with hA
  set s : ℂ := (A : ℂ) + Complex.I * ((y : ℂ)) with hs
  have hsre : s.re = A := by simp [s]
  have hsim : s.im = y := by simp [s]
  have hAval : A = -(((2 * (N : ℝ)) + 1)) := hA
  set w : ℂ := 1 - s with hw
  have hwre : w.re = 2 * (N : ℝ) + 2 := by
    rw [hw, Complex.sub_re, Complex.one_re, hsre, hAval]; ring
  have hwim : w.im = -y := by
    rw [hw, Complex.sub_im, Complex.one_im, hsim]; simp
  have hs0 : s ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    rw [hsre, hAval] at h1
    simp at h1
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have h1 := congrArg Complex.re h
    rw [hsre, hAval] at h1
    simp at h1
    linarith
  have hzs : riemannZeta s ≠ 0 := by
    intro hz
    obtain ⟨n, hn⟩ := (riemannZeta_eq_zero_iff_trivial_of_re_nonpos (s := s)
      (by rw [hsre, hAval]; linarith)).mp hz
    have h2 : s.re = -2 * ((n : ℝ) + 1) := by
      rw [hn]
      simp
    rw [hsre, hAval] at h2
    have h3 : 2 * (N : ℝ) + 1 = 2 * ((n : ℝ) + 1) := by linarith
    have h4 : 2 * N + 1 = 2 * n + 2 := by exact_mod_cast h3
    omega
  have hzw : riemannZeta w ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    rw [hwre]; linarith
  have hΓ : ∀ n : ℕ, (1 : ℂ) - s ≠ -(n : ℂ) := by
    intro n hn
    have h2 := congrArg Complex.re hn
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at h2
    rw [hsre, hAval] at h2
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hui : ((1 : ℂ) - s).im = -y := by
    rw [Complex.sub_im, Complex.one_im, hsim]; simp
  have hur : ((1 : ℂ) - s).re = 2 * (N : ℝ) + 2 := by
    rw [Complex.sub_re, Complex.one_re, hsre, hAval]; ring
  have hcos : Complex.cos ((↑Real.pi) * (1 - s) / 2) ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h0
    have h1 : (2 : ℂ) * ((↑Real.pi) * (1 - s) / 2)
        = (2 : ℂ) * ((2 * (↑k) + 1) * (↑Real.pi) / 2) :=
      congrArg (fun z => (2 : ℂ) * z) hk
    have h1' : (↑Real.pi) * (1 - s) = (2 * (↑k) + 1) * (↑Real.pi) := by
      have h2 : (2 : ℂ) * ((↑Real.pi) * (1 - s) / 2) = (↑Real.pi) * (1 - s) := by ring
      have h3 : (2 : ℂ) * ((2 * (↑k) + 1) * (↑Real.pi) / 2)
          = (2 * (↑k) + 1) * (↑Real.pi) := by ring
      rw [← h2, h1, h3]
    have h1'' : (↑Real.pi) * (1 - s) = (↑Real.pi) * (2 * (↑k) + 1) := by
      rw [h1', mul_comm]
    have h3 : (1 : ℂ) - s = 2 * (↑k) + 1 :=
      mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) h1''
    have h4 := congrArg Complex.im h3
    rw [hui] at h4
    simp at h4
    have h5 := congrArg Complex.re h3
    rw [hur] at h5
    simp at h5
    have h6 : (2 * (↑k) + 1 : ℤ) = 2 * ((N : ℤ) + 1) := by
      have h7 : (2 * (k : ℝ) + 1 : ℝ) = 2 * ((N : ℝ) + 1) := by linarith
      exact_mod_cast h7
    omega
  have hFE := zeta_logDeriv_fe_expanded hzs hzw hs0 hs1 hΓ hcos
  have htanarg : (↑Real.pi) * (1 - s) / 2
      = (((N : ℂ) + 1)) * (↑Real.pi) - (((Real.pi / 2) * y : ℝ) : ℂ) * Complex.I := by
    have hmul : (↑Real.pi) * (1 - s) / 2 = (((Real.pi / 2 : ℝ)) : ℂ) * ((1 : ℂ) - s) := by
      push_cast; ring
    rw [hmul]
    apply Complex.ext
    · rw [Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hur,
        Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.one_re, Complex.natCast_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
      ring
    · rw [Complex.mul_im]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hui,
        Complex.sub_im, Complex.mul_im, Complex.add_im, Complex.one_im, Complex.natCast_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
      ring
  have htan : ‖((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * (1 - s) / 2)‖ ≤ 2 := by
    have h1 : ‖Complex.tan ((↑Real.pi) * (1 - s) / 2)‖ ≤ 1 := by
      rw [htanarg]
      simpa using tan_piN_sub_le N (Real.pi / 2 * y)
    rw [norm_mul]
    have h2 : ‖((Real.pi / 2 : ℝ) : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_of_nonneg (by positivity)]
      linarith [Real.pi_lt_four]
    calc ‖((Real.pi / 2 : ℝ) : ℂ)‖ * ‖Complex.tan ((↑Real.pi) * (1 - s) / 2)‖ ≤ 2 * 1 :=
          mul_le_mul h2 h1 (norm_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  have hlog : ‖Complex.log (2 * (Real.pi : ℂ))‖ ≤ 2 := by
    have h1 : Complex.log (2 * (Real.pi : ℂ)) = ((Real.log (2 * Real.pi) : ℝ) : ℂ) := by
      rw [show (2 * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ)) : ℂ) by push_cast; ring,
        ← Complex.ofReal_log (by positivity)]
    rw [h1, Complex.norm_of_nonneg (Real.log_nonneg (by nlinarith [Real.pi_gt_three]))]
    exact log_two_pi_le_two
  have hdig : ‖Complex.digamma (1 - s)‖ ≤ 2 * Cdg * (X + 1) := by
    have h1 := hCdg (1 - s) (by rw [hur]; linarith)
    have hnn : ‖(1 : ℂ) - s‖ + 2 ≤ 2 * (2 * (N : ℝ) + |y| + 3) := by
      have h3 : ‖(1 : ℂ) - s‖ ≤ 2 * (N : ℝ) + 2 + |y| := by
        have h4 := Complex.norm_le_abs_re_add_abs_im ((1 : ℂ) - s)
        rw [hur, hui, abs_neg] at h4
        have h5 : |2 * (N : ℝ) + 2| = 2 * (N : ℝ) + 2 := abs_of_nonneg (by linarith)
        rw [h5] at h4
        linarith
      linarith [abs_nonneg y]
    have h6 : Real.log (‖(1 : ℂ) - s‖ + 2) ≤ X + 1 := by
      have h7 := Real.log_le_log (by positivity : (0:ℝ) < ‖(1 : ℂ) - s‖ + 2) hnn
      have h8 : Real.log (2 * (2 * (N : ℝ) + |y| + 3)) = Real.log 2 + X := by
        rw [Real.log_mul (by norm_num) (by positivity), hX]
      rw [h8] at h7
      have h9 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
      linarith
    have h10 : Real.log (‖(1 : ℂ) - s‖ + 2) + 1 ≤ 2 * (X + 1) := by linarith
    calc ‖Complex.digamma (1 - s)‖ ≤ Cdg * (Real.log (‖(1 : ℂ) - s‖ + 2) + 1) := h1
      _ ≤ Cdg * (2 * (X + 1)) := mul_le_mul_of_nonneg_left h10 hCdgpos.le
      _ = 2 * Cdg * (X + 1) := by ring
  have hMw : ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ ≤ M * (X + 1) := by
    have h1 := hM (1 - s) (by rw [hur]; linarith)
    have h2 : M ≤ M * (X + 1) := by
      have h3 : (1:ℝ) ≤ X + 1 := by linarith
      calc M = M * 1 := by ring
        _ ≤ M * (X + 1) := mul_le_mul_of_nonneg_left h3 hMpos.le
    linarith
  rw [hFE]
  rw [show Complex.log ((2 * Real.pi : ℝ) : ℂ) = Complex.log (2 * (Real.pi : ℂ)) by
    congr 1; push_cast; ring]
  have hsum : ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma (1 - s)
      + ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * (1 - s) / 2)
      - deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖
      ≤ 2 + 2 * Cdg * (X + 1) + 2 + M * (X + 1) := by
    have hab : ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma (1 - s)
        + ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * (1 - s) / 2)‖
        ≤ 2 + 2 * Cdg * (X + 1) + 2 := by
      have hb := norm_add_le (Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma (1 - s))
        (((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * (1 - s) / 2))
      have hc : ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma (1 - s)‖
          ≤ 2 + 2 * Cdg * (X + 1) := by
        have h := norm_sub_le (Complex.log (2 * (Real.pi : ℂ))) (Complex.digamma (1 - s))
        linarith [h, hlog, hdig]
      linarith [hb, hc, htan]
    calc ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma (1 - s)
          + ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * (1 - s) / 2)
          - deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖
        ≤ ‖Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma (1 - s)
            + ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * (1 - s) / 2)‖
          + ‖deriv riemannZeta (1 - s) / riemannZeta (1 - s)‖ := by
            have h := norm_add_le (Complex.log (2 * (Real.pi : ℂ)) - Complex.digamma (1 - s)
              + ((Real.pi / 2 : ℝ) : ℂ) * Complex.tan ((↑Real.pi) * (1 - s) / 2))
              (-(deriv riemannZeta (1 - s) / riemannZeta (1 - s)))
            rw [sub_eq_add_neg]
            simpa using h
      _ ≤ (2 + 2 * Cdg * (X + 1) + 2) + M * (X + 1) := add_le_add hab hMw
  have hfin : 2 + 2 * Cdg * (X + 1) + 2 + M * (X + 1)
      ≤ (2 + 2 * Cdg + M + 4) * (X + 1) := by nlinarith [hXnn]
  exact le_trans hsum hfin

/-! ## A good height for the zeros of `ζ₁` -/

/-- There is a "good height" `Tp ∈ [T, T+1]` : no zero of `ζ₁` has imaginary part within
`c/(log T + 1)` of `Tp`. -/
theorem zeta1_exists_good_height (h : RiemannHypothesis) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 5 ≤ T → ∃ Tp : ℝ,
      T ≤ Tp ∧ Tp ≤ T + 1 ∧
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → c / (Real.log T + 1) ≤ |ρ.im - Tp|) := by
  obtain ⟨c0, hc0pos, hc0⟩ := riemannZeta_ordinate_window h
  refine ⟨1 / (8 * c0 + 6), by positivity, fun T hT => ?_⟩
  set L : ℝ := Real.log T + 1 with hL
  have hL2 : 2 ≤ L := by
    have h1 : (1 : ℝ) ≤ Real.log 5 := by
      have h3 : Real.exp 1 ≤ (5 : ℝ) :=
        le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num))
      have h4 := Real.log_le_log (Real.exp_pos 1) h3
      rwa [Real.log_exp] at h4
    have h5 : Real.log 5 ≤ Real.log T := Real.log_le_log (by norm_num) hT
    rw [hL]; linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  obtain ⟨S, hSrange, hScard, hSzeros⟩ := hc0 T hT
  set n : ℕ := ⌈c0 * L⌉₊ + 1 with hn
  have hn1 : 1 ≤ n := by simp [hn]
  have hnle : (n : ℝ) ≤ c0 * L + 2 := by
    have h1 : ((⌈c0 * L⌉₊ : ℕ) : ℝ) < c0 * L + 1 :=
      Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ c0 * L)
    rw [hn]; push_cast; linarith
  have hcard : S.card ≤ n := by
    have h1 : (S.card : ℝ) ≤ c0 * L := by rw [hL]; exact hScard
    have h2 : (S.card : ℝ) ≤ (⌈c0 * L⌉₊ : ℝ) := le_trans h1 (Nat.le_ceil _)
    have h3 : (S.card : ℝ) ≤ (n : ℝ) := by rw [hn]; push_cast; linarith
    exact_mod_cast h3
  have hSrange' : ∀ s ∈ S, T - 1 ≤ s ∧ s ≤ T + 2 := hSrange
  obtain ⟨Tp, hTp1, hTp2, hgap⟩ :=
    Commons.Analysis.Real.exists_gap_height T hn1 S hcard hSrange'
  refine ⟨Tp, hTp1, hTp2, fun ρ hρ => ?_⟩
  have hcpos : 0 < 1 / (8 * c0 + 6) := by positivity
  have hkey : 1 / (8 * c0 + 6) / L ≤ 1 / (2 * (n : ℝ) + 2) := by
    have hnum : (2 * (n : ℝ) + 2) ≤ (8 * c0 + 6) * L := by
      have h1 : 2 * (n : ℝ) + 2 ≤ 2 * (c0 * L + 2) + 2 := by linarith
      have h2 : 2 * (c0 * L + 2) + 2 = 2 * c0 * L + 6 := by ring
      have h3 : 2 * c0 * L + 6 ≤ 2 * c0 * L + 3 * L := by linarith
      have h4 : 2 * c0 * L + 3 * L = (2 * c0 + 3) * L := by ring
      have h5 : (2 * c0 + 3) * L ≤ (8 * c0 + 6) * L := by
        have h6 : (0:ℝ) ≤ L := by linarith
        have h7 : 2 * c0 + 3 ≤ 8 * c0 + 6 := by linarith
        exact mul_le_mul_of_nonneg_right h7 h6
      linarith
    rw [div_div]
    exact one_div_le_one_div_of_le (by positivity) hnum
  by_cases hcase : T - 1 ≤ ρ.im ∧ ρ.im ≤ T + 2
  · have hρ1 : ρ ≠ 1 := by
      intro hh
      rw [hh, riemannZeta₁_one] at hρ
      norm_num at hρ
    have hζ : riemannZeta ρ = 0 := by
      by_contra hz
      exact (zeta1_ne_zero_iff_zeta_ne_zero hρ1).mpr hz hρ
    have hntriv : ¬ ∃ m : ℕ, ρ = -2 * ((m : ℂ) + 1) := by
      rintro ⟨m, hm⟩
      have him : ρ.im = 0 := by rw [hm]; simp
      linarith [hcase.1, hT]
    have hre : ρ.re = 1 / 2 := h ρ hζ hntriv hρ1
    have hmem : ρ.im ∈ S := hSzeros ρ hζ hre hcase.1 hcase.2
    have h1 := hgap ρ.im hmem
    rw [abs_sub_comm] at h1
    exact le_trans hkey h1
  · have hge : 1 ≤ |ρ.im - Tp| := by
      by_cases hlt : ρ.im < T - 1
      · have h1 : Tp - ρ.im ≥ 1 := by linarith
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        exact h1
      · rw [not_lt] at hlt
        have hgt : T + 2 < ρ.im := by
          by_contra hc
          rw [not_lt] at hc
          exact hcase ⟨hlt, hc⟩
        have h1 : ρ.im - Tp ≥ 1 := by linarith
        rw [abs_of_nonneg (by linarith)]
        exact h1
    have hc1 : 1 / (8 * c0 + 6) / L ≤ 1 := by
      rw [div_div, div_le_one (by positivity)]
      nlinarith [hc0pos, hL1]
    linarith

/-! ## Shell bounds for the zero sums -/


private lemma exists_two_pow_gt (r : ℝ) : ∃ j : ℕ, r < (2:ℝ)^j := by
  refine ⟨Nat.ceil r + 1, ?_⟩
  have h1 : r ≤ ((Nat.ceil r : ℕ) : ℝ) := Nat.le_ceil r
  have h2 : ((Nat.ceil r : ℕ) : ℝ) < (2:ℝ)^(Nat.ceil r) := by
    have h := Nat.lt_two_pow_self (n := Nat.ceil r)
    exact_mod_cast h
  have h3 : (2:ℝ)^(Nat.ceil r) ≤ (2:ℝ)^(Nat.ceil r + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
  linarith

private lemma exists_two_pow_ge (r : ℝ) : ∃ j : ℕ, r ≤ (2:ℝ)^j :=
  ⟨Nat.ceil r + 1, by
    have h1 : r ≤ ((Nat.ceil r : ℕ) : ℝ) := Nat.le_ceil r
    have h2 : ((Nat.ceil r : ℕ) : ℝ) ≤ (2:ℝ)^(Nat.ceil r) := by
      have h := Nat.lt_two_pow_self (n := Nat.ceil r)
      have h' : (Nat.ceil r : ℝ) < (2:ℝ)^(Nat.ceil r) := by exact_mod_cast h
      linarith
    have h3 : (2:ℝ)^(Nat.ceil r) ≤ (2:ℝ)^(Nat.ceil r + 1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
    linarith⟩

private noncomputable def shell (ρ : ℂ) : ℕ := Nat.find (exists_two_pow_gt ‖ρ‖)

private lemma shell_spec (ρ : ℂ) : ‖ρ‖ < (2:ℝ)^(shell ρ) :=
  Nat.find_spec (exists_two_pow_gt ‖ρ‖)

private lemma shell_min (ρ : ℂ) {j : ℕ} (hj : ‖ρ‖ < (2:ℝ)^j) : shell ρ ≤ j :=
  Nat.find_min' _ hj

private lemma shell_lower (ρ : ℂ) (h : 1 ≤ shell ρ) : (2:ℝ)^(shell ρ - 1) ≤ ‖ρ‖ := by
  by_contra hc
  rw [not_le] at hc
  have h1 := shell_min ρ hc
  omega

private lemma shell_pointwise (ρ : ℂ) :
    (1 : ℝ) / (1 + ‖ρ‖^2) ≤ 4 / (4:ℝ)^(shell ρ) := by
  rcases Nat.eq_zero_or_pos (shell ρ) with h0 | hpos
  · rw [h0, pow_zero]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (‖ρ‖)]
  · have hlow := shell_lower ρ hpos
    have h4 : (4:ℝ)^(shell ρ - 1) ≤ ‖ρ‖^2 := by
      have h : ((2:ℝ)^(shell ρ - 1))^2 ≤ ‖ρ‖^2 :=
        pow_le_pow_left₀ (by positivity) hlow 2
      have hh : ((2:ℝ)^(shell ρ - 1))^2 = (4:ℝ)^(shell ρ - 1) := by
        rw [show (4:ℝ) = 2^2 by norm_num, ← pow_mul, ← pow_mul]
        ring_nf
      rwa [hh] at h
    have h5 : (4:ℝ)^(shell ρ) ≤ 4 * (1 + ‖ρ‖^2) := by
      have hpow : (4:ℝ)^(shell ρ) = 4 * (4:ℝ)^(shell ρ - 1) := by
        conv_lhs => rw [show shell ρ = (shell ρ - 1) + 1 by omega]
        rw [pow_succ]
        ring
      rw [hpow]
      nlinarith [sq_nonneg (‖ρ‖), h4]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith

/-- `∑_{j<J} (j+4)/2^j ≤ 10`. -/
private lemma sum_range_lin_le (J : ℕ) :
    ∑ j ∈ Finset.range J, ((j:ℝ)+4)/(2:ℝ)^j ≤ 10 := by
  have h : ∑ j ∈ Finset.range J, ((j:ℝ)+4)/(2:ℝ)^j = 10 - (2*(J:ℝ)+10)/(2:ℝ)^J := by
    induction J with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have h2 : (0:ℝ) < (2:ℝ)^k := by positivity
      have h3 : (2:ℝ)^(k+1) = 2 * (2:ℝ)^k := by rw [pow_succ]; ring
      rw [h3]
      field_simp
      push_cast
      ring
  rw [h]
  have : (0:ℝ) ≤ (2*(J:ℝ)+10)/(2:ℝ)^J := by positivity
  linarith

private lemma log_two_pow_add_le (j : ℕ) :
    Real.log ((2:ℝ)^j + 2) + 2 ≤ (j:ℝ) + 4 := by
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
    have h1 : (2:ℝ)^0 + 2 = 3 := by norm_num
    rw [h1]
    norm_num
    linarith
  · have hj : 1 ≤ j := Nat.succ_le_of_lt hpos
    have h2 : (2:ℝ)^j + 2 ≤ 2 * (2:ℝ)^j := by
      have hlt : (2:ℝ) ≤ (2:ℝ)^j := by
        calc (2:ℝ) = (2:ℝ)^1 := by ring
          _ ≤ (2:ℝ)^j := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by exact_mod_cast hj)
      linarith
    have h3 : Real.log ((2:ℝ)^j + 2) ≤ Real.log (2 * (2:ℝ)^j) :=
      Real.log_le_log (by positivity) h2
    have h4 : Real.log (2 * (2:ℝ)^j) = Real.log 2 + (j:ℝ) * Real.log 2 := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h5 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    have h6 : (0:ℝ) ≤ (j:ℝ) * Real.log 2 := by
      have : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      positivity
    have h7 : Real.log 2 + (j:ℝ) * Real.log 2 ≤ 1 + (j:ℝ) := by
      have h8 : Real.log 2 + (j:ℝ) * Real.log 2 = Real.log 2 * (1 + (j:ℝ)) := by ring
      rw [h8]
      exact mul_le_of_le_one_left (by positivity) h5
    rw [h4] at h3
    linarith


/-- `4/4^n = 4·(1/4)^n`. -/
private lemma four_div_pow (n : ℕ) : (4:ℝ)/(4:ℝ)^n = 4 * ((1:ℝ)/4)^n := by
  rw [div_eq_mul_inv, show ((1:ℝ)/4)^n = ((4:ℝ)^n)⁻¹ by rw [one_div, inv_pow]]

/-- A uniform bound for `∑ m_ρ/(1+‖ρ‖²)` over finite sets of zeros. -/
theorem zeroSum_inv_sq_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℂ), (∀ ρ ∈ S, riemannZeta₁ ρ = 0) →
      S.sum (fun ρ => (zeta1Order ρ : ℝ) / (1 + ‖ρ‖^2)) ≤ C := by
  obtain ⟨c, hc⟩ := zeta1_zeroBall_multiplicity_sum_le
  refine ⟨40 * max c 0 + 40, by positivity, fun S hS => ?_⟩
  classical
  set J : ℕ := S.sup shell + 1 with hJ
  have hJle : ∀ ρ ∈ S, shell ρ < J := by
    intro ρ hρ
    have h := Finset.le_sup (f := shell) hρ
    omega
  have hpt : ∀ ρ ∈ S, (zeta1Order ρ : ℝ) / (1 + ‖ρ‖^2)
      ≤ ∑ j ∈ Finset.range J, (if shell ρ = j then (4 * ((1:ℝ)/4)^j) * (zeta1Order ρ : ℝ) else 0) := by
    intro ρ hρ
    have hp := shell_pointwise ρ
    have hm : (0:ℝ) ≤ (zeta1Order ρ : ℝ) := Nat.cast_nonneg _
    have h1 : (zeta1Order ρ : ℝ) / (1 + ‖ρ‖^2) ≤ (zeta1Order ρ : ℝ) * (4 / (4:ℝ)^(shell ρ)) := by
      have hp' : (1 + ‖ρ‖^2)⁻¹ ≤ 4 / (4:ℝ)^(shell ρ) := by simpa [one_div] using hp
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hp' hm
    have h2 : (zeta1Order ρ : ℝ) * (4 / (4:ℝ)^(shell ρ))
        = (4 * ((1:ℝ)/4)^(shell ρ)) * (zeta1Order ρ : ℝ) := by
      rw [four_div_pow]; ring
    have h3 : ∑ j ∈ Finset.range J, (if shell ρ = j then (4 * ((1:ℝ)/4)^j) * (zeta1Order ρ : ℝ) else 0)
        = (4 * ((1:ℝ)/4)^(shell ρ)) * (zeta1Order ρ : ℝ) := by
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (hJle ρ hρ))]
    linarith [h1, le_of_eq h2, le_of_eq h3.symm]
  have hfinal : ∑ j ∈ Finset.range J, (4 * ((1:ℝ)/4)^j) *
      (max c 0 * (2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2))
      ≤ 40 * max c 0 + 40 := by
    have h1 : ∑ j ∈ Finset.range J, (4 * ((1:ℝ)/4)^j) *
        (max c 0 * (2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2))
        = 4 * max c 0 * ∑ j ∈ Finset.range J, (Real.log ((2:ℝ)^j + 2) + 2)/(2:ℝ)^j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have h4 : (0:ℝ) < (2:ℝ)^j := by positivity
      have h5 : ((1:ℝ)/4)^j * (2:ℝ)^j = 1/(2:ℝ)^j := by
        rw [← mul_pow]; norm_num
        rw [one_div, inv_pow]
      rw [show 4 * ((1:ℝ)/4)^j * (max c 0 * (2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2))
          = (4 * max c 0 * (Real.log ((2:ℝ)^j + 2) + 2)) * (((1:ℝ)/4)^j * (2:ℝ)^j) by ring]
      rw [h5]
      field_simp
    have h2 : ∑ j ∈ Finset.range J, (Real.log ((2:ℝ)^j + 2) + 2)/(2:ℝ)^j ≤ 10 := by
      have ha : ∑ j ∈ Finset.range J, (Real.log ((2:ℝ)^j + 2) + 2)/(2:ℝ)^j
          ≤ ∑ j ∈ Finset.range J, ((j:ℝ)+4)/(2:ℝ)^j := by
        apply Finset.sum_le_sum
        intro j hj
        rw [div_le_div_iff_of_pos_right (by positivity)]
        exact log_two_pow_add_le j
      exact le_trans ha (sum_range_lin_le J)
    have h3 : (0:ℝ) ≤ max c 0 := le_max_right _ _
    rw [h1]
    nlinarith [h2, h3]
  calc S.sum (fun ρ => (zeta1Order ρ : ℝ)/(1+‖ρ‖^2))
      ≤ S.sum (fun ρ => ∑ j ∈ Finset.range J,
          (if shell ρ = j then (4*((1:ℝ)/4)^j)*(zeta1Order ρ : ℝ) else 0)) :=
        Finset.sum_le_sum hpt
    _ = ∑ j ∈ Finset.range J, S.sum (fun ρ =>
          (if shell ρ = j then (4*((1:ℝ)/4)^j)*(zeta1Order ρ : ℝ) else 0)) :=
        Finset.sum_comm
    _ = ∑ j ∈ Finset.range J, (4*((1:ℝ)/4)^j) *
          (S.filter (fun ρ => shell ρ = j)).sum (fun ρ => (zeta1Order ρ : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum, Finset.sum_filter]
    _ ≤ ∑ j ∈ Finset.range J, (4*((1:ℝ)/4)^j) *
          (max c 0 * (2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2)) := by
        apply Finset.sum_le_sum
        intro j hj
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hsub : S.filter (fun ρ => shell ρ = j) ⊆ zetaZeroBallFin ((2:ℝ)^j) (by positivity) := by
          intro ρ hρ
          obtain ⟨hρS, hsh⟩ := Finset.mem_filter.mp hρ
          rw [zetaZeroBallFin_spec]
          refine ⟨?_, hS ρ hρS⟩
          rw [Metric.mem_closedBall, dist_zero_right]
          have := shell_spec ρ
          rw [hsh] at this
          exact le_of_lt this
        calc (S.filter (fun ρ => shell ρ = j)).sum (fun ρ => (zeta1Order ρ : ℝ))
            ≤ (zetaZeroBallFin ((2:ℝ)^j) (by positivity)).sum (fun ρ => (zeta1Order ρ : ℝ)) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.cast_nonneg _)
          _ ≤ c * (2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2) := hc _ _
          _ ≤ max c 0 * (2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2) := by
              have hZ : (0:ℝ) ≤ (2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2) := by
                have h1 : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
                have h2 : (0:ℝ) ≤ Real.log ((2:ℝ)^j + 2) := Real.log_nonneg (by linarith)
                positivity
              calc c * (2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2)
                  = c * ((2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2)) := by ring
                _ ≤ max c 0 * ((2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2)) :=
                    mul_le_mul_of_nonneg_right (le_max_left _ _) hZ
                _ = max c 0 * (2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2) := by ring
    _ ≤ 40 * max c 0 + 40 := hfinal


/-- Every zero of `ζ₁` has real part `≤ 1`. -/
private lemma zeta1_zero_re_le_one {ρ : ℂ} (hρ : riemannZeta₁ ρ = 0) : ρ.re ≤ 1 := by
  have hρ1 : ρ ≠ 1 := by
    intro hh; rw [hh, riemannZeta₁_one] at hρ; norm_num at hρ
  have hζ : riemannZeta ρ = 0 := by
    by_contra hz
    exact (zeta1_ne_zero_iff_zeta_ne_zero hρ1).mpr hz hρ
  by_cases htriv : ∃ n : ℕ, ρ = -2 * ((n:ℂ) + 1)
  · obtain ⟨n, hn⟩ := htriv
    rw [hn]
    have h1 : ((-2 : ℂ) * ((n:ℂ) + 1)).re = -2 * ((n:ℝ) + 1) := by
      rw [Complex.mul_re]; simp
    rw [h1]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · have hstrip := mem_strip_of_riemannZeta_eq_zero_of_not_trivial hζ htriv
    linarith [hstrip.2]

/-- The absolute tilted zero sum over any finite set of zeros is `O(x²)`. -/
theorem tiltedZeroSum_abs_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ), 1 ≤ x → ∀ (S : Finset ℂ), (∀ ρ ∈ S, riemannZeta₁ ρ = 0) →
      S.sum (fun ρ => ‖(zeta1Order ρ : ℂ) * (x:ℂ)^(ρ+1)/(ρ*(ρ+1))‖) ≤ C * x^2 := by
  obtain ⟨c1, hc1pos, hc1⟩ := zeroSum_inv_sq_bounded
  set B : ℝ := (zetaZeroBallFin (2:ℝ) (by norm_num)).sum
    (fun ρ => (zeta1Order ρ : ℝ)/(‖ρ‖ * ‖ρ+1‖)) with hB
  have hBnn : 0 ≤ B := by
    rw [hB]; exact Finset.sum_nonneg (fun ρ _ => by positivity)
  refine ⟨4*c1 + B + 1, by positivity, fun x hx S hS => ?_⟩
  have hxpos : (0:ℝ) < x := by linarith
  have hnorm : ∀ ρ : ℂ, ‖(zeta1Order ρ : ℂ) * (x:ℂ)^(ρ+1)/(ρ*(ρ+1))‖
      = (zeta1Order ρ : ℝ) * x^(ρ.re+1)/(‖ρ‖ * ‖ρ+1‖) := by
    intro ρ
    rw [norm_div, norm_mul, norm_mul, Complex.norm_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.add_re, Complex.one_re]
  have hlarge : (S.filter (fun ρ => (2:ℝ) ≤ ‖ρ‖)).sum
      (fun ρ => ‖(zeta1Order ρ : ℂ) * (x:ℂ)^(ρ+1)/(ρ*(ρ+1))‖) ≤ 4 * x^2 * c1 := by
    have hterm : ∀ ρ ∈ S.filter (fun ρ => (2:ℝ) ≤ ‖ρ‖),
        ‖(zeta1Order ρ : ℂ) * (x:ℂ)^(ρ+1)/(ρ*(ρ+1))‖
          ≤ 4*x^2*((zeta1Order ρ : ℝ)/(1+‖ρ‖^2)) := by
      intro ρ hρ
      obtain ⟨hρS, hρ2⟩ := Finset.mem_filter.mp hρ
      have hz1 := hS ρ hρS
      rw [hnorm ρ]
      have hre := zeta1_zero_re_le_one hz1
      have hxp : x^(ρ.re+1) ≤ x^2 := by
        have h := Real.rpow_le_rpow_of_exponent_le (y := ρ.re+1) (z := (2:ℝ)) hx (by linarith)
        have h2 : x ^ (2:ℝ) = x^2 := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        rwa [h2] at h
      have hm : (0:ℝ) ≤ (zeta1Order ρ : ℝ) := Nat.cast_nonneg _
      have hn1 : (2:ℝ) ≤ ‖ρ‖ := hρ2
      have hshift : ‖ρ‖/2 ≤ ‖ρ+1‖ := by
        have h := norm_sub_le (ρ+1) 1
        simp only [add_sub_cancel_right, norm_one] at h
        linarith
      have hden : ‖ρ‖^2/2 ≤ ‖ρ‖ * ‖ρ+1‖ := by
        have := mul_le_mul_of_nonneg_left hshift (norm_nonneg ρ)
        nlinarith
      have hdenpos : (0:ℝ) < ‖ρ‖ * ‖ρ+1‖ := by nlinarith [hden]
      have hfac : (1:ℝ)/(‖ρ‖*‖ρ+1‖) ≤ 4/(1+‖ρ‖^2) := by
        have h2 : (1:ℝ)/(‖ρ‖*‖ρ+1‖) ≤ 2/‖ρ‖^2 := by
          rw [div_le_div_iff₀ hdenpos (by positivity)]
          linarith
        have h3 : (2:ℝ)/‖ρ‖^2 ≤ 4/(1+‖ρ‖^2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
      have hnum : (zeta1Order ρ : ℝ) * x^(ρ.re+1) ≤ 4*x^2*((zeta1Order ρ : ℝ)) := by
        nlinarith [hxp, hm, sq_nonneg x]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hstep1 : (zeta1Order ρ : ℝ) * x^(ρ.re+1) * (‖ρ‖*‖ρ+1‖)⁻¹
          ≤ (zeta1Order ρ : ℝ) * x^2 * (‖ρ‖*‖ρ+1‖)⁻¹ :=
        mul_le_mul_of_nonneg_right (by nlinarith [hxp, hm]) (by positivity)
      calc (zeta1Order ρ : ℝ) * x^(ρ.re+1) * (‖ρ‖*‖ρ+1‖)⁻¹
          ≤ (zeta1Order ρ : ℝ) * x^2 * (‖ρ‖*‖ρ+1‖)⁻¹ := hstep1
        _ = (zeta1Order ρ : ℝ) * x^2 * ((1:ℝ)/(‖ρ‖*‖ρ+1‖)) := by rw [one_div]
        _ ≤ (zeta1Order ρ : ℝ) * x^2 * (4/(1+‖ρ‖^2)) :=
            mul_le_mul_of_nonneg_left hfac (by positivity)
        _ = 4*x^2*((zeta1Order ρ : ℝ)/(1+‖ρ‖^2)) := by ring
    calc (S.filter (fun ρ => (2:ℝ) ≤ ‖ρ‖)).sum (fun ρ => ‖(zeta1Order ρ : ℂ) * (x:ℂ)^(ρ+1)/(ρ*(ρ+1))‖)
        ≤ (S.filter (fun ρ => (2:ℝ) ≤ ‖ρ‖)).sum (fun ρ => 4*x^2*((zeta1Order ρ : ℝ)/(1+‖ρ‖^2))) :=
          Finset.sum_le_sum hterm
      _ = 4*x^2 * (S.filter (fun ρ => (2:ℝ) ≤ ‖ρ‖)).sum (fun ρ => (zeta1Order ρ : ℝ)/(1+‖ρ‖^2)) := by
          rw [Finset.mul_sum]
      _ ≤ 4*x^2 * c1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hsub : S.filter (fun ρ => (2:ℝ) ≤ ‖ρ‖) ⊆ S := Finset.filter_subset _ _
          calc (S.filter (fun ρ => (2:ℝ) ≤ ‖ρ‖)).sum (fun ρ => (zeta1Order ρ : ℝ)/(1+‖ρ‖^2))
              ≤ S.sum (fun ρ => (zeta1Order ρ : ℝ)/(1+‖ρ‖^2)) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg hsub
                intro i _ _; positivity
            _ ≤ c1 := hc1 S hS
  have hsmall : (S.filter (fun ρ => ¬ ((2:ℝ) ≤ ‖ρ‖))).sum
      (fun ρ => ‖(zeta1Order ρ : ℂ) * (x:ℂ)^(ρ+1)/(ρ*(ρ+1))‖) ≤ x^2 * B := by
    have hterm : ∀ ρ ∈ S.filter (fun ρ => ¬ ((2:ℝ) ≤ ‖ρ‖)),
        ‖(zeta1Order ρ : ℂ) * (x:ℂ)^(ρ+1)/(ρ*(ρ+1))‖
          ≤ x^2 * ((zeta1Order ρ : ℝ)/(‖ρ‖*‖ρ+1‖)) := by
      intro ρ hρ
      obtain ⟨hρS, hρ2⟩ := Finset.mem_filter.mp hρ
      have hz1 := hS ρ hρS
      rw [hnorm ρ]
      have hre := zeta1_zero_re_le_one hz1
      have hxp : x^(ρ.re+1) ≤ x^2 := by
        have h := Real.rpow_le_rpow_of_exponent_le (y := ρ.re+1) (z := (2:ℝ)) hx (by linarith)
        have h2 : x ^ (2:ℝ) = x^2 := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        rwa [h2] at h
      have hm : (0:ℝ) ≤ (zeta1Order ρ : ℝ) := Nat.cast_nonneg _
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have h1 : (zeta1Order ρ : ℝ) * x^(ρ.re+1) ≤ x^2 * (zeta1Order ρ : ℝ) := by nlinarith
      calc (zeta1Order ρ : ℝ) * x^(ρ.re+1) * (‖ρ‖*‖ρ+1‖)⁻¹
          ≤ x^2 * (zeta1Order ρ : ℝ) * (‖ρ‖*‖ρ+1‖)⁻¹ :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = x^2 * ((zeta1Order ρ : ℝ) * (‖ρ‖*‖ρ+1‖)⁻¹) := by ring
        _ = x^2 * ((zeta1Order ρ : ℝ)/(‖ρ‖*‖ρ+1‖)) := by rw [div_eq_mul_inv]
    calc (S.filter (fun ρ => ¬ ((2:ℝ) ≤ ‖ρ‖))).sum
          (fun ρ => ‖(zeta1Order ρ : ℂ) * (x:ℂ)^(ρ+1)/(ρ*(ρ+1))‖)
        ≤ (S.filter (fun ρ => ¬ ((2:ℝ) ≤ ‖ρ‖))).sum
          (fun ρ => x^2 * ((zeta1Order ρ : ℝ)/(‖ρ‖*‖ρ+1‖))) := Finset.sum_le_sum hterm
      _ = x^2 * (S.filter (fun ρ => ¬ ((2:ℝ) ≤ ‖ρ‖))).sum
          (fun ρ => (zeta1Order ρ : ℝ)/(‖ρ‖*‖ρ+1‖)) := by rw [Finset.mul_sum]
      _ ≤ x^2 * B := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [hB]
          apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun i _ _ => by positivity)
          intro ρ hρ
          obtain ⟨hρS, hρ2⟩ := Finset.mem_filter.mp hρ
          rw [zetaZeroBallFin_spec]
          refine ⟨?_, hS ρ hρS⟩
          rw [Metric.mem_closedBall, dist_zero_right]
          exact le_of_lt (lt_of_not_ge hρ2)
  have hsum := Finset.sum_filter_add_sum_filter_not S (fun ρ => (2:ℝ) ≤ ‖ρ‖)
    (fun ρ => ‖(zeta1Order ρ : ℂ) * (x:ℂ)^(ρ+1)/(ρ*(ρ+1))‖)
  rw [← hsum]
  have h1 : (0:ℝ) ≤ x^2 := by positivity
  nlinarith [hlarge, hsmall, h1, hBnn, hc1pos]


/-- The closed form `∑_{j<J} (j+4)/2^j = 10 - (2J+10)/2^J`. -/
private lemma sum_range_lin_eq (J : ℕ) :
    ∑ j ∈ Finset.range J, ((j:ℝ)+4)/(2:ℝ)^j = 10 - (2*(J:ℝ)+10)/(2:ℝ)^J := by
  induction J with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h2 : (0:ℝ) < (2:ℝ)^k := by positivity
    have h3 : (2:ℝ)^(k+1) = 2 * (2:ℝ)^k := by rw [pow_succ]; ring
    rw [h3]
    field_simp
    push_cast
    ring

/-- Tail bound: the `1/(1+‖ρ‖²)`-weighted sum over zeros of `ζ₁` with `‖ρ‖ ≥ T` is `O(log T / T)`. -/
theorem zeroSum_inv_sq_tail_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℂ), (∀ ρ ∈ S, riemannZeta₁ ρ = 0) →
      ∀ T : ℝ, 2 ≤ T →
        (S.filter (fun ρ => T ≤ ‖ρ‖)).sum (fun ρ => (zeta1Order ρ : ℝ)/(1+‖ρ‖^2))
          ≤ C * (Real.log (T + 2) + 1) / T := by
  obtain ⟨c, hc⟩ := zeta1_zeroBall_multiplicity_sum_le
  refine ⟨500 * max c 0 + 100, by positivity, fun S hS T hT => ?_⟩
  classical
  set J : ℕ := S.sup shell + 1 with hJ
  have hJle : ∀ ρ ∈ S, shell ρ < J := by
    intro ρ hρ
    have h := Finset.le_sup (f := shell) hρ
    omega
  set Kk : ℕ := ⌈Real.log T / Real.log 2⌉₊ with hKk
  have hshellK : ∀ ρ ∈ S.filter (fun ρ => T ≤ ‖ρ‖), Kk ≤ shell ρ := by
    intro ρ hρ
    obtain ⟨hρS, hρT⟩ := Finset.mem_filter.mp hρ
    have h1 : Real.log T / Real.log 2 < (shell ρ : ℝ) := by
      have h2 : T < (2:ℝ)^(shell ρ) := lt_of_le_of_lt hρT (shell_spec ρ)
      have h3 := Real.log_lt_log (by linarith) h2
      rw [Real.log_pow] at h3
      have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      rw [div_lt_iff₀ hlog2pos]
      linarith
    have h4 : ⌈Real.log T / Real.log 2⌉₊ ≤ shell ρ := Nat.ceil_le.mpr (le_of_lt h1)
    rwa [hKk]
  by_cases hne : (S.filter (fun ρ => T ≤ ‖ρ‖)).Nonempty
  · obtain ⟨ρ0, hρ0⟩ := hne
    have hKle : Kk ≤ J := le_trans (hshellK ρ0 hρ0) (le_of_lt (hJle ρ0 (Finset.mem_of_mem_filter ρ0 hρ0)))
    set S' : Finset ℂ := S.filter (fun ρ => T ≤ ‖ρ‖) with hS'
    have hpt : ∀ ρ ∈ S', (zeta1Order ρ : ℝ)/(1+‖ρ‖^2)
        ≤ ∑ j ∈ Finset.Ico Kk J, (if shell ρ = j then (4*((1:ℝ)/4)^j)*(zeta1Order ρ : ℝ) else 0) := by
      intro ρ hρ
      have hp := shell_pointwise ρ
      have hm : (0:ℝ) ≤ (zeta1Order ρ : ℝ) := Nat.cast_nonneg _
      have h1 : (zeta1Order ρ : ℝ) / (1 + ‖ρ‖^2) ≤ (zeta1Order ρ : ℝ) * (4 / (4:ℝ)^(shell ρ)) := by
        have hp' : (1 + ‖ρ‖^2)⁻¹ ≤ 4 / (4:ℝ)^(shell ρ) := by simpa [one_div] using hp
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hp' hm
      have h2 : (zeta1Order ρ : ℝ) * (4 / (4:ℝ)^(shell ρ))
          = (4 * ((1:ℝ)/4)^(shell ρ)) * (zeta1Order ρ : ℝ) := by
        rw [four_div_pow]; ring
      have hmem : shell ρ ∈ Finset.Ico Kk J := by
        rw [Finset.mem_Ico]
        exact ⟨hshellK ρ hρ, hJle ρ (Finset.mem_of_mem_filter ρ hρ)⟩
      have h3 : ∑ j ∈ Finset.Ico Kk J, (if shell ρ = j then (4*((1:ℝ)/4)^j)*(zeta1Order ρ : ℝ) else 0)
          = (4*((1:ℝ)/4)^(shell ρ)) * (zeta1Order ρ : ℝ) := by
        rw [Finset.sum_ite_eq, if_pos hmem]
      linarith [h1, le_of_eq h2, le_of_eq h3.symm]
    have hKbound : (2*(Kk:ℝ)+10) ≤ 100 * (Real.log (T + 2) + 1) := by
      have h1 : (Kk : ℝ) ≤ Real.log T / Real.log 2 + 1 := by
        have h := Nat.ceil_lt_add_one (a := Real.log T / Real.log 2)
          (show (0:ℝ) ≤ Real.log T / Real.log 2 by
            exact div_nonneg (Real.log_nonneg (by linarith))
              (Real.log_pos (by norm_num)).le)
        rw [hKk]; linarith
      have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by
        have h := Real.log_le_log (Real.exp_pos 1)
          (show Real.exp 1 ≤ 4 by linarith [Real.exp_one_lt_three])
        rw [Real.log_exp, show (4:ℝ) = 2^2 by norm_num, Real.log_pow] at h
        norm_num at h
        linarith
      have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have h2 : Real.log T / Real.log 2 ≤ 2 * Real.log T := by
        rw [div_le_iff₀ hlog2pos]
        nlinarith [Real.log_nonneg (by linarith : (1:ℝ) ≤ T)]
      have h3 : Real.log T ≤ Real.log (T + 2) := Real.log_le_log (by linarith) (by linarith)
      have h4 : (0:ℝ) ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
      linarith
    have hfinal : ∑ j ∈ Finset.Ico Kk J, (4*((1:ℝ)/4)^j) *
        (max c 0 * (2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2))
        ≤ 500 * max c 0 * (Real.log (T + 2) + 1) / T := by
      have h1 : ∑ j ∈ Finset.Ico Kk J, (4*((1:ℝ)/4)^j) *
          (max c 0 * (2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2))
          = 4 * max c 0 * ∑ j ∈ Finset.Ico Kk J, (Real.log ((2:ℝ)^j + 2) + 2)/(2:ℝ)^j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have h4 : (0:ℝ) < (2:ℝ)^j := by positivity
        have h5 : ((1:ℝ)/4)^j * (2:ℝ)^j = 1/(2:ℝ)^j := by
          rw [← mul_pow]; norm_num
          rw [one_div, inv_pow]
        rw [show 4 * ((1:ℝ)/4)^j * (max c 0 * (2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2))
            = (4 * max c 0 * (Real.log ((2:ℝ)^j + 2) + 2)) * (((1:ℝ)/4)^j * (2:ℝ)^j) by ring]
        rw [h5]
        field_simp
      have h2 : ∑ j ∈ Finset.Ico Kk J, (Real.log ((2:ℝ)^j + 2) + 2)/(2:ℝ)^j
          ≤ (2*(Kk:ℝ)+10)/(2:ℝ)^Kk := by
        have ha : ∑ j ∈ Finset.Ico Kk J, (Real.log ((2:ℝ)^j + 2) + 2)/(2:ℝ)^j
            ≤ ∑ j ∈ Finset.Ico Kk J, ((j:ℝ)+4)/(2:ℝ)^j := by
          apply Finset.sum_le_sum
          intro j hj
          rw [div_le_div_iff_of_pos_right (by positivity)]
          exact log_two_pow_add_le j
        have hb : ∑ j ∈ Finset.Ico Kk J, ((j:ℝ)+4)/(2:ℝ)^j
            = (2*(Kk:ℝ)+10)/(2:ℝ)^Kk - (2*(J:ℝ)+10)/(2:ℝ)^J := by
          rw [Finset.sum_Ico_eq_sub _ hKle, sum_range_lin_eq, sum_range_lin_eq]
          ring
        have hc2 : (0:ℝ) ≤ (2*(J:ℝ)+10)/(2:ℝ)^J := by positivity
        linarith [ha, le_of_eq hb]
      have h3 : (0:ℝ) ≤ max c 0 := le_max_right _ _
      have h4 : (0:ℝ) < (2:ℝ)^Kk := by positivity
      have h5 : T ≤ (2:ℝ)^Kk := by
        have hceil : Real.log T / Real.log 2 ≤ (Kk:ℝ) := by
          rw [hKk]; exact Nat.le_ceil _
        have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        have hTcanon : T = (2:ℝ) ^ (Real.log T / Real.log 2) := by
          rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2),
            mul_div_cancel₀ _ (ne_of_gt hlog2pos), Real.exp_log (by linarith)]
        have hstep : (2:ℝ) ^ (Real.log T / Real.log 2) ≤ (2:ℝ) ^ (Kk:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hceil
        rw [Real.rpow_natCast] at hstep
        rw [← hTcanon] at hstep
        exact hstep
      have h6 : (2*(Kk:ℝ)+10)/(2:ℝ)^Kk ≤ (2*(Kk:ℝ)+10)/T := by
        rw [div_le_div_iff₀ h4 (by linarith)]
        nlinarith
      have h7 : (0:ℝ) ≤ (Real.log (T + 2) + 1) / T := by
        apply div_nonneg _ (by linarith)
        have := Real.log_nonneg (by linarith : (1:ℝ) ≤ T + 2); linarith
      have hsum2 : ∑ j ∈ Finset.Ico Kk J, (Real.log ((2:ℝ)^j + 2) + 2)/(2:ℝ)^j
          ≤ 100 * (Real.log (T + 2) + 1) / T := by
        calc _ ≤ (2*(Kk:ℝ)+10)/(2:ℝ)^Kk := h2
          _ ≤ (2*(Kk:ℝ)+10)/T := h6
          _ ≤ 100 * (Real.log (T + 2) + 1) / T := by
              rw [div_le_div_iff_of_pos_right (by linarith : (0:ℝ) < T)]
              linarith [hKbound]
      rw [h1]
      have hc0 : (0:ℝ) ≤ max c 0 := le_max_right _ _
      have hstep1 : 4 * max c 0 * (∑ j ∈ Finset.Ico Kk J, (Real.log ((2:ℝ)^j + 2) + 2)/(2:ℝ)^j)
          ≤ 4 * max c 0 * (100 * (Real.log (T+2)+1)/T) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
      have hstep2 : 4 * max c 0 * (100 * (Real.log (T+2)+1)/T)
          = 400 * max c 0 * (Real.log (T+2)+1)/T := by ring
      have hstep3 : (400:ℝ) * max c 0 * (Real.log (T+2)+1)/T
          ≤ 500 * max c 0 * (Real.log (T+2)+1)/T := by
        rw [div_le_div_iff_of_pos_right (by linarith : (0:ℝ) < T)]
        have hL : (0:ℝ) ≤ Real.log (T + 2) + 1 := by
          have := Real.log_nonneg (by linarith : (1:ℝ) ≤ T + 2); linarith
        nlinarith [hc0, hL]
      linarith [hstep1, le_of_eq hstep2, hstep3]
    calc S'.sum (fun ρ => (zeta1Order ρ : ℝ)/(1+‖ρ‖^2))
        ≤ S'.sum (fun ρ => ∑ j ∈ Finset.Ico Kk J,
            (if shell ρ = j then (4*((1:ℝ)/4)^j)*(zeta1Order ρ : ℝ) else 0)) :=
          Finset.sum_le_sum hpt
      _ = ∑ j ∈ Finset.Ico Kk J, S'.sum (fun ρ =>
            (if shell ρ = j then (4*((1:ℝ)/4)^j)*(zeta1Order ρ : ℝ) else 0)) := Finset.sum_comm
      _ = ∑ j ∈ Finset.Ico Kk J, (4*((1:ℝ)/4)^j) *
            (S'.filter (fun ρ => shell ρ = j)).sum (fun ρ => (zeta1Order ρ : ℝ)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← Finset.sum_filter, Finset.mul_sum]
      _ ≤ ∑ j ∈ Finset.Ico Kk J, (4*((1:ℝ)/4)^j) *
            (max c 0 * (2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2)) := by
          apply Finset.sum_le_sum
          intro j hj
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hsub : S'.filter (fun ρ => shell ρ = j) ⊆ zetaZeroBallFin ((2:ℝ)^j) (by positivity) := by
            intro ρ hρ
            obtain ⟨hρS, hsh⟩ := Finset.mem_filter.mp hρ
            have hz : riemannZeta₁ ρ = 0 := hS ρ (Finset.mem_filter.mp hρS).1
            rw [zetaZeroBallFin_spec]
            refine ⟨?_, hz⟩
            rw [Metric.mem_closedBall, dist_zero_right]
            have := shell_spec ρ
            rw [hsh] at this
            exact le_of_lt this
          calc (S'.filter (fun ρ => shell ρ = j)).sum (fun ρ => (zeta1Order ρ : ℝ))
              ≤ (zetaZeroBallFin ((2:ℝ)^j) (by positivity)).sum (fun ρ => (zeta1Order ρ : ℝ)) :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.cast_nonneg _)
            _ ≤ c * (2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2) := hc _ _
            _ ≤ max c 0 * (2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2) := by
                have hZ : (0:ℝ) ≤ (2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2) := by
                  have h1 : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
                  have h2 : (0:ℝ) ≤ Real.log ((2:ℝ)^j + 2) := Real.log_nonneg (by linarith)
                  positivity
                calc c * (2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2)
                    = c * ((2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2)) := by ring
                  _ ≤ max c 0 * ((2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2)) :=
                      mul_le_mul_of_nonneg_right (le_max_left _ _) hZ
                  _ = max c 0 * (2:ℝ)^j * (Real.log ((2:ℝ)^j + 2) + 2) := by ring
      _ ≤ 500 * max c 0 * (Real.log (T + 2) + 1) / T := hfinal
      _ ≤ (500 * max c 0 + 100) * (Real.log (T + 2) + 1) / T := by
          have hL : (0:ℝ) ≤ Real.log (T + 2) + 1 := by
            have := Real.log_nonneg (by linarith : (1:ℝ) ≤ T + 2); linarith
          have hc0 : (0:ℝ) ≤ max c 0 := le_max_right _ _
          rw [div_le_div_iff_of_pos_right (by linarith : (0:ℝ) < T)]
          nlinarith [hL, hc0]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp only [Finset.sum_empty]
    have hL : (0:ℝ) ≤ Real.log (T + 2) + 1 := by
      have := Real.log_nonneg (by linarith : (1:ℝ) ≤ T + 2); linarith
    have hC : (0:ℝ) ≤ 500 * max c 0 + 100 := by
      have := le_max_right c 0; linarith
    exact div_nonneg (mul_nonneg hC hL) (by linarith)

/-! ## The horizontal edge integral bound for the tilted kernel -/

private lemma log_le_eight_mul_rpow {y : ℝ} (hy : 1 ≤ y) :
    Real.log y ≤ 8 * y ^ ((1 : ℝ) / 8) := by
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hp : 0 ≤ y ^ ((1 : ℝ) / 8) := Real.rpow_nonneg hy0.le _
  have hlog : Real.log y = 8 * Real.log (y ^ ((1 : ℝ) / 8)) := by
    rw [Real.log_rpow hy0]; ring
  have hle : Real.log (y ^ ((1 : ℝ) / 8)) ≤ y ^ ((1 : ℝ) / 8) := Real.log_le_self hp
  linarith

private lemma log_pow_four_le_sqrt {u : ℝ} (hu : 1 ≤ u) :
    (Real.log u) ^ (4 : ℕ) ≤ 4096 * Real.sqrt u := by
  have h0 : 0 ≤ Real.log u := Real.log_nonneg hu
  have h := log_le_eight_mul_rpow hu
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hp2 : (0 : ℝ) ≤ u ^ ((1 : ℝ) / 8) := Real.rpow_nonneg hu0 _
  have hpow : (8 * u ^ ((1 : ℝ) / 8)) ^ (4 : ℕ) = 4096 * u ^ ((1 : ℝ) / 2) := by
    have h1 : (8 * u ^ ((1 : ℝ) / 8)) ^ (4 : ℕ)
        = (8 * u ^ ((1 : ℝ) / 8)) ^ (((4 : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
    rw [h1, Real.mul_rpow (by norm_num) hp2, ← Real.rpow_mul hu0]
    have h8 : (8 : ℝ) ^ (((4 : ℕ) : ℝ)) = 4096 := by
      rw [Real.rpow_natCast]; norm_num
    have hexp : ((1 : ℝ) / 8) * (((4 : ℕ) : ℝ)) = (1 : ℝ) / 2 := by norm_num
    rw [h8, hexp]
  calc (Real.log u) ^ (4 : ℕ) ≤ (8 * u ^ ((1 : ℝ) / 8)) ^ (4 : ℕ) := pow_le_pow_left₀ h0 h 4
    _ = 4096 * u ^ ((1 : ℝ) / 2) := hpow
    _ = 4096 * Real.sqrt u := by rw [Real.sqrt_eq_rpow]

private lemma integral_rpow_neg_three_halves_le {T M : ℝ} (hT : 2 ≤ T) (hTM : T ≤ M) :
    (∫ u in T..M, u ^ (-(3 / 2) : ℝ)) ≤ 2 * (T ^ ((1 : ℝ) / 2))⁻¹ := by
  have hT0 : 0 < T := by linarith
  have hM0 : 0 < M := by linarith
  have hnin : (0 : ℝ) ∉ Set.uIcc T M := by
    rw [Set.uIcc_of_le hTM]; intro h; simp at h; linarith
  rw [integral_rpow (Or.inr ⟨by norm_num, hnin⟩)]
  have hr : -(3 / 2 : ℝ) + 1 = -(1 / 2) := by norm_num
  rw [hr, Real.rpow_neg hM0.le, Real.rpow_neg hT0.le]
  have heq : ((M ^ ((1 : ℝ) / 2))⁻¹ - (T ^ ((1 : ℝ) / 2))⁻¹) / (-(1 / 2))
      = 2 * ((T ^ ((1 : ℝ) / 2))⁻¹ - (M ^ ((1 : ℝ) / 2))⁻¹) := by
    field_simp
    ring
  rw [heq]
  have h1 : (0 : ℝ) ≤ (M ^ ((1 : ℝ) / 2))⁻¹ :=
    inv_nonneg.mpr (Real.rpow_nonneg hM0.le _)
  linarith

private lemma continuousAt_tiltIntF {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hz : riemannZeta₁ s ≠ 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsp1 : s + 1 ≠ 0) :
    ContinuousAt (fun w : ℂ => tiltIntF x w) s := by
  have hpsi : ContinuousAt (fun w : ℂ => psiIntF1 x w) s :=
    (psiIntF1_analyticAt hx hs0 hs1 hz).continuousAt
  change ContinuousAt (fun w : ℂ => (x : ℂ) * psiIntF1 x w / (w + 1)) s
  exact (continuousAt_const.mul hpsi).div
    (continuous_id.continuousAt.add continuousAt_const) hsp1

private lemma continuousOn_tiltIntF_line {x T : ℝ} (hx : 0 < x) (hT : T ≠ 0) {a b : ℝ}
    (hne : ∀ σ ∈ Set.uIcc a b, riemannZeta₁ ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0) :
    ContinuousOn (fun σ : ℝ => tiltIntF x ((σ : ℂ) + Complex.I * (T : ℂ))) (Set.uIcc a b) := by
  intro σ hσ
  have hz := hne σ hσ
  have hca : ContinuousAt (fun s : ℂ => tiltIntF x s)
      ((σ : ℂ) + Complex.I * (T : ℂ)) := by
    refine continuousAt_tiltIntF hx hz ?_ ?_ ?_ <;>
      · intro h
        have h' := congrArg Complex.im h
        simp at h'
        exact hT h'
  have hg : ContinuousAt (fun σ' : ℝ => ((σ' : ℂ) + Complex.I * (T : ℂ))) σ :=
    (continuous_ofReal.add continuous_const).continuousAt
  exact ContinuousAt.comp_continuousWithinAt
    (f := fun σ' : ℝ => ((σ' : ℂ) + Complex.I * (T : ℂ))) hca hg.continuousWithinAt

private lemma continuousOn_tiltIntF_line_neg {x T : ℝ} (hx : 0 < x) (hT : T ≠ 0) {a b : ℝ}
    (hne : ∀ σ ∈ Set.uIcc a b, riemannZeta₁ (((-σ : ℝ) : ℂ) + Complex.I * (T : ℂ)) ≠ 0) :
    ContinuousOn (fun σ : ℝ => tiltIntF x (((-σ : ℝ) : ℂ) + Complex.I * (T : ℂ)))
      (Set.uIcc a b) := by
  intro σ hσ
  have hz := hne σ hσ
  have hca : ContinuousAt (fun s : ℂ => tiltIntF x s)
      (((-σ : ℝ) : ℂ) + Complex.I * (T : ℂ)) := by
    refine continuousAt_tiltIntF hx hz ?_ ?_ ?_ <;>
      · intro h
        have h' := congrArg Complex.im h
        simp at h'
        exact hT h'
  have hg : ContinuousAt (fun σ' : ℝ => (((-σ' : ℝ)) : ℂ) + Complex.I * (T : ℂ)) σ :=
    ((continuous_ofReal.comp continuous_neg).add continuous_const).continuousAt
  exact ContinuousAt.comp_continuousWithinAt
    (f := fun σ' : ℝ => (((-σ' : ℝ)) : ℂ) + Complex.I * (T : ℂ)) hca hg.continuousWithinAt

/-- pointwise bound on the far-left region `Re s ≤ -1/2`. -/
private lemma tiltIntF_pointwise_farLeft {x σ Tp Cf : ℝ} (hx : 1 ≤ x) (hTp : 1 ≤ Tp)
    (hCf : 0 ≤ Cf) (hσ : σ ≤ -(1 / 2 : ℝ))
    (hlog : ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (Tp : ℂ))‖
      ≤ Cf * (Real.log (|σ| + Tp + 3)) ^ 4) :
    ‖tiltIntF x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖
      ≤ x * (Cf * (Real.log (|σ| + Tp + 3)) ^ 4 + 1) / (|σ| * max Tp (|σ| - 1)) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  set s : ℂ := (σ : ℂ) + Complex.I * (Tp : ℂ) with hs
  have hsim : s.im = Tp := by simp [s]
  have hsre : s.re = σ := by simp [s]
  have hTp0 : (0 : ℝ) < Tp := by linarith
  have hTp3 : (1 : ℝ) ≤ |σ| + Tp + 3 := by
    have h1 : (0:ℝ) ≤ |σ| := abs_nonneg σ
    linarith
  have hLnn : (0:ℝ) ≤ Real.log (|σ| + Tp + 3) := Real.log_nonneg hTp3
  have hsT : Tp ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    rw [hsim, abs_of_nonneg hTp0.le] at h; exact h
  have hssig : |σ| ≤ ‖s‖ := by
    have h := Complex.abs_re_le_norm s; rwa [hsre] at h
  have hsp1T : Tp ≤ ‖s + 1‖ := by
    have h := Complex.abs_im_le_norm (s + 1)
    have h2 : (s + 1).im = Tp := by simp [s]
    rw [h2, abs_of_nonneg hTp0.le] at h; exact h
  have hsm1T : Tp ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    have h2 : (s - 1).im = Tp := by simp [s]
    rw [h2, abs_of_nonneg hTp0.le] at h; exact h
  have hsp1sig : max Tp (|σ| - 1) ≤ ‖s + 1‖ := by
    refine max_le hsp1T ?_
    have h := Complex.abs_re_le_norm (s + 1)
    have h2 : (s + 1).re = σ + 1 := by simp [s]
    rw [h2] at h
    have h3 : |σ| - 1 ≤ |σ + 1| := by
      have h4 := abs_add_le (σ + 1) (-1)
      simp only [add_neg_cancel_right, abs_neg, abs_one] at h4
      linarith
    linarith
  have hmaxnn : (0:ℝ) ≤ max Tp (|σ| - 1) := le_trans (by linarith : (0:ℝ) ≤ Tp) (le_max_left _ _)
  have hden_le : |σ| * max Tp (|σ| - 1) ≤ ‖s‖ * ‖s + 1‖ :=
    mul_le_mul hssig hsp1sig hmaxnn (norm_nonneg s)
  have hden_pos : 0 < |σ| * max Tp (|σ| - 1) := by
    have h1 : 0 < |σ| := by
      apply abs_pos.mpr
      intro h; rw [h] at hσ; norm_num at hσ
    exact mul_pos h1 (lt_of_lt_of_le hTp0 (le_max_left _ _))
  have hxσ : x ^ s.re ≤ 1 := by
    rw [hsre]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  have hs1 : 1 / ‖s - 1‖ ≤ 1 := by
    rw [div_le_one (by linarith [hsm1T])]
    linarith [hsm1T]
  have hlog' : ‖logDeriv riemannZeta₁ s‖ ≤ Cf * (Real.log (|σ| + Tp + 3)) ^ 4 := by
    have := hlog; rwa [hs] at this
  have hBnonneg : (0 : ℝ) ≤ Cf * (Real.log (|σ| + Tp + 3)) ^ 4 + 1 := by
    have := pow_nonneg hLnn 4
    nlinarith [hCf, this]
  have hA : x * ((‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖) * (x ^ s.re / ‖s‖)) / ‖s + 1‖
      ≤ x * ((Cf * (Real.log (|σ| + Tp + 3)) ^ 4 + 1) * (1 / ‖s‖)) / ‖s + 1‖ := by
    refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ hx0.le
    exact mul_le_mul (by linarith [hlog', hs1])
      (div_le_div_of_nonneg_right hxσ (norm_nonneg s))
      (div_nonneg (Real.rpow_nonneg hx0.le _) (norm_nonneg s)) hBnonneg
  have hd1 : ‖s‖ ≠ 0 := ne_of_gt (by linarith [hsT, hTp0])
  have hd2 : ‖s + 1‖ ≠ 0 := ne_of_gt (by linarith [hsp1T, hTp0])
  have hAeq : x * ((Cf * (Real.log (|σ| + Tp + 3)) ^ 4 + 1) * (1 / ‖s‖)) / ‖s + 1‖
      = x * (Cf * (Real.log (|σ| + Tp + 3)) ^ 4 + 1) / (‖s‖ * ‖s + 1‖) := by
    rw [mul_one_div]
    field_simp
  calc ‖tiltIntF x s‖ ≤ x * ‖psiIntF1 x s‖ / ‖s + 1‖ := tiltIntF_norm_le hx0.le
    _ ≤ x * ((‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖) * (x ^ s.re / ‖s‖)) / ‖s + 1‖ := by
        refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (psiIntF1_norm_le_logDeriv hx0 s) hx0.le
    _ ≤ x * ((Cf * (Real.log (|σ| + Tp + 3)) ^ 4 + 1) * (1 / ‖s‖)) / ‖s + 1‖ := hA
    _ = x * (Cf * (Real.log (|σ| + Tp + 3)) ^ 4 + 1) / (‖s‖ * ‖s + 1‖) := hAeq
    _ ≤ x * (Cf * (Real.log (|σ| + Tp + 3)) ^ 4 + 1) / (|σ| * max Tp (|σ| - 1)) :=
        div_le_div_of_nonneg_left (mul_nonneg hx0.le hBnonneg) hden_pos hden_le

/-- pointwise bound on the strip `-1/2 ≤ Re s ≤ 2` at a good height. -/
private lemma tiltIntF_pointwise_strip {x σ Tp δ Cs : ℝ} (hx : 1 ≤ x) (hTp : 5 ≤ Tp)
    (hxTp : x ≤ Tp) (hCs : 0 ≤ Cs) (hδ : 0 < δ)
    (hσhi : σ ≤ 2)
    (hlog : ‖logDeriv riemannZeta₁ ((σ : ℂ) + Complex.I * (Tp : ℂ))‖
      ≤ Cs * ((Real.log (Tp + 3) + 1) ^ 3 + (Real.log (Tp + 3) + 1) ^ 2 / δ)) :
    ‖tiltIntF x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖
      ≤ x ^ 2 * (Cs * ((Real.log (Tp + 3) + 1) ^ 3 + (Real.log (Tp + 3) + 1) ^ 2 / δ) + 1)
          / Tp := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hTp0 : (0 : ℝ) < Tp := by linarith
  set s : ℂ := (σ : ℂ) + Complex.I * (Tp : ℂ) with hs
  have hsim : s.im = Tp := by simp [s]
  have hsre : s.re = σ := by simp [s]
  have hsT : Tp ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    rw [hsim, abs_of_nonneg hTp0.le] at h; exact h
  have hsp1T : Tp ≤ ‖s + 1‖ := by
    have h := Complex.abs_im_le_norm (s + 1)
    have h2 : (s + 1).im = Tp := by simp [s]
    rw [h2, abs_of_nonneg hTp0.le] at h; exact h
  have hsm1T : Tp ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    have h2 : (s - 1).im = Tp := by simp [s]
    rw [h2, abs_of_nonneg hTp0.le] at h; exact h
  have hxσ : x ^ s.re ≤ x ^ (2 : ℝ) := by
    rw [hsre]; exact Real.rpow_le_rpow_of_exponent_le hx hσhi
  have hs1 : 1 / ‖s - 1‖ ≤ 1 := by
    rw [div_le_one (by linarith [hsm1T])]
    linarith [hsm1T]
  have hlog' : ‖logDeriv riemannZeta₁ s‖
      ≤ Cs * ((Real.log (Tp + 3) + 1) ^ 3 + (Real.log (Tp + 3) + 1) ^ 2 / δ) := by
    have := hlog; rwa [hs] at this
  set Cq : ℝ := Cs * ((Real.log (Tp + 3) + 1) ^ 3 + (Real.log (Tp + 3) + 1) ^ 2 / δ) with hCq
  have hCqnn : 0 ≤ Cq := by
    rw [hCq]
    have hL : (0:ℝ) ≤ Real.log (Tp + 3) + 1 := by
      have h := Real.log_nonneg (by linarith : (1:ℝ) ≤ Tp + 3)
      linarith
    have h1 : (0:ℝ) ≤ (Real.log (Tp + 3) + 1) ^ 3 := pow_nonneg hL 3
    have h2 : (0:ℝ) ≤ (Real.log (Tp + 3) + 1) ^ 2 / δ := div_nonneg (pow_nonneg hL 2) hδ.le
    nlinarith [hCs, h1, h2]
  have hBnonneg : (0 : ℝ) ≤ Cq + 1 := by linarith
  have hA1 : x * ((‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖) * (x ^ s.re / ‖s‖)) / ‖s + 1‖
      ≤ x * ((Cq + 1) * (x ^ (2 : ℝ) / Tp)) / ‖s + 1‖ := by
    refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ hx0.le
    refine mul_le_mul (by linarith [hlog', hs1]) ?_
      (div_nonneg (Real.rpow_nonneg hx0.le _) (le_of_lt (lt_of_lt_of_le hTp0 hsT))) hBnonneg
    calc x ^ s.re / ‖s‖ ≤ x ^ (2 : ℝ) / ‖s‖ :=
          div_le_div_of_nonneg_right hxσ (norm_nonneg s)
      _ ≤ x ^ (2 : ℝ) / Tp :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le 2) hTp0 hsT
  have hA2 : x * ((Cq + 1) * (x ^ (2 : ℝ) / Tp)) / ‖s + 1‖
      ≤ x * ((Cq + 1) * (x ^ (2 : ℝ) / Tp)) / Tp :=
    div_le_div_of_nonneg_left (mul_nonneg hx0.le (mul_nonneg hBnonneg
      (div_nonneg (Real.rpow_nonneg hx0.le 2) hTp0.le))) hTp0 hsp1T
  have hx4 : x * x ^ (2 : ℝ) = x ^ (3 : ℝ) := by
    have h := Real.rpow_add hx0 (1 : ℝ) (2 : ℝ)
    rw [Real.rpow_one] at h
    rw [show (3 : ℝ) = (1 : ℝ) + 2 by norm_num]
    exact h.symm
  have hkey : x * ((Cq + 1) * (x ^ (2 : ℝ) / Tp)) / Tp
      = (Cq + 1) * x ^ (3 : ℝ) / Tp ^ 2 := by
    rw [← hx4, show Tp ^ 2 = Tp * Tp by ring]
    ring
  have hinner : x ^ (3 : ℝ) ≤ x ^ (2 : ℝ) * Tp := by
    have hx3r : x ^ (3 : ℝ) = x ^ (2 : ℝ) * x := by
      have h := Real.rpow_add hx0 (2 : ℝ) (1 : ℝ)
      rw [Real.rpow_one] at h
      rw [show (3 : ℝ) = (2 : ℝ) + 1 by norm_num]
      exact h
    rw [hx3r]
    exact mul_le_mul_of_nonneg_left hxTp (Real.rpow_nonneg hx0.le 2)
  have hfin : (Cq + 1) * x ^ (3 : ℝ) / Tp ^ 2 ≤ (Cq + 1) * x ^ (2 : ℝ) / Tp := by
    have h2 : (0 : ℝ) < Tp ^ 2 := by positivity
    rw [div_le_iff₀ h2]
    have he : (Cq + 1) * x ^ (2 : ℝ) / Tp * Tp ^ 2 = (Cq + 1) * x ^ (2 : ℝ) * Tp := by
      field_simp
    rw [he]
    calc (Cq + 1) * x ^ (3 : ℝ) ≤ (Cq + 1) * (x ^ (2 : ℝ) * Tp) :=
          mul_le_mul_of_nonneg_left hinner hBnonneg
      _ = (Cq + 1) * x ^ (2 : ℝ) * Tp := by ring
  calc ‖tiltIntF x s‖ ≤ x * ‖psiIntF1 x s‖ / ‖s + 1‖ := tiltIntF_norm_le hx0.le
    _ ≤ x * ((‖logDeriv riemannZeta₁ s‖ + 1 / ‖s - 1‖) * (x ^ s.re / ‖s‖)) / ‖s + 1‖ := by
        refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (psiIntF1_norm_le_logDeriv hx0 s) hx0.le
    _ ≤ x * ((Cq + 1) * (x ^ (2 : ℝ) / Tp)) / ‖s + 1‖ := hA1
    _ ≤ x * ((Cq + 1) * (x ^ (2 : ℝ) / Tp)) / Tp := hA2
    _ = (Cq + 1) * x ^ (3 : ℝ) / Tp ^ 2 := hkey
    _ ≤ (Cq + 1) * x ^ (2 : ℝ) / Tp := hfin
    _ = x ^ 2 * (Cq + 1) / Tp := by
        rw [show x ^ (2 : ℝ) = x ^ 2 by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
        ring

private lemma continuousOn_id_add_const (a b : ℝ) (s : Set ℝ) :
    ContinuousOn (fun u : ℝ => u + a + b) s := by
  have h1 : ContinuousOn (fun u : ℝ => u) s := continuousOn_id
  have h2 : ContinuousOn (fun _ : ℝ => a) s := continuousOn_const
  have h3 : ContinuousOn (fun _ : ℝ => b) s := continuousOn_const
  have h4 : ContinuousOn (fun u : ℝ => (u + a) + b) s := (h1.add h2).add h3
  simpa using h4

/-- Piece `∫_2^N` (with `N ≤ Tp`) of the far-left bound. -/
private lemma farLeft_piece1_le {x Cf Tp N : ℝ} (hx : 1 ≤ x) (hCf : 0 ≤ Cf) (hTp : 5 ≤ Tp)
    (hN2 : 2 ≤ N) (hNT : N ≤ Tp) :
    (∫ u in (2 : ℝ)..N, x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * Tp))
      ≤ x * (16 * Cf + 1) * (Real.log (Tp + 2)) ^ 5 / Tp := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hTp0 : (0 : ℝ) < Tp := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log (Tp + 2) := by
    have h1 : Real.exp 1 ≤ (7 : ℝ) := le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num))
    have h2 := Real.log_le_log (Real.exp_pos 1) h1
    rw [Real.log_exp] at h2
    have h3 : Real.log (7 : ℝ) ≤ Real.log (Tp + 2) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  set L0 : ℝ := Real.log (2 * Tp + 3) with hL0def
  set L : ℝ := Real.log (Tp + 2) with hLdef
  have hL0nn : 0 ≤ L0 := by rw [hL0def]; exact Real.log_nonneg (by linarith)
  have hL0bound : L0 ≤ 2 * L := by
    rw [hL0def, hLdef]
    have h2 : 2 * Tp + 3 ≤ (Tp + 2) ^ 2 := by nlinarith
    calc Real.log (2 * Tp + 3) ≤ Real.log ((Tp + 2) ^ 2) := Real.log_le_log (by linarith) h2
      _ = 2 * Real.log (Tp + 2) := by rw [Real.log_pow]; push_cast; ring
  have hL0pow : L0 ^ 4 ≤ 16 * L ^ 4 := by
    have h := pow_le_pow_left₀ hL0nn hL0bound 4
    rwa [mul_pow, show ((2 : ℝ)) ^ (4 : ℕ) = 16 by norm_num] at h
  have hL4ge1 : (1 : ℝ) ≤ L ^ 4 := by
    have h11 : (1 : ℝ) ^ (4 : ℕ) ≤ L ^ 4 := pow_le_pow_left₀ zero_le_one hL1 4
    simpa using h11
  set C1 : ℝ := x * (Cf * L0 ^ 4 + 1) / Tp with hC1def
  have hC1nn : 0 ≤ C1 := by
    rw [hC1def]
    exact div_nonneg (mul_nonneg hx0.le (by positivity)) hTp0.le
  have hpt : ∀ u ∈ Set.Icc (2 : ℝ) N,
      x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * Tp) ≤ C1 * u⁻¹ := by
    intro u hu
    have hu2 : (2 : ℝ) ≤ u := hu.1
    have hlogu : Real.log (u + Tp + 3) ≤ L0 := by
      rw [hL0def]; exact Real.log_le_log (by linarith) (by linarith [hu.2, hNT])
    have hlogunn : 0 ≤ Real.log (u + Tp + 3) := Real.log_nonneg (by linarith)
    have hlog4u : (Real.log (u + Tp + 3)) ^ 4 ≤ L0 ^ 4 := pow_le_pow_left₀ hlogunn hlogu 4
    have hnum : x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) ≤ x * (Cf * L0 ^ 4 + 1) := by
      apply mul_le_mul_of_nonneg_left _ hx0.le
      nlinarith [hCf, hlog4u]
    calc x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * Tp)
        ≤ x * (Cf * L0 ^ 4 + 1) / (u * Tp) := div_le_div_of_nonneg_right hnum (by positivity)
      _ = C1 * u⁻¹ := by
          rw [hC1def, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]; ring
  have hintg : IntervalIntegrable
      (fun u : ℝ => x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * Tp)) volume 2 N := by
    apply ContinuousOn.intervalIntegrable
    have hlin : ContinuousOn (fun u : ℝ => u + Tp + 3) (Set.uIcc (2 : ℝ) N) :=
      (continuousOn_id_add_const Tp 3 (Set.uIcc (2 : ℝ) N))
    have hlog : ContinuousOn (fun u : ℝ => Real.log (u + Tp + 3)) (Set.uIcc (2 : ℝ) N) :=
      hlin.log (fun u hu => by
        rw [Set.uIcc_of_le hN2, Set.mem_Icc] at hu
        have h1 : (0 : ℝ) < u := by linarith [hu.1]
        positivity)
    have hnum : ContinuousOn
        (fun u : ℝ => x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1)) (Set.uIcc (2 : ℝ) N) :=
      (((hlog.pow 4).const_mul Cf).add continuousOn_const).const_mul x
    refine ContinuousOn.div hnum ?_ ?_
    · exact continuousOn_id.mul continuousOn_const
    · intro u hu
      rw [Set.uIcc_of_le hN2, Set.mem_Icc] at hu
      exact mul_ne_zero (ne_of_gt (by linarith [hu.1] : (0 : ℝ) < u)) (ne_of_gt hTp0)
  have hintc : IntervalIntegrable (fun u : ℝ => C1 * u⁻¹) volume 2 N := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.const_mul (continuousOn_id.inv₀ (fun u hu => ?_)) C1
    rw [Set.uIcc_of_le hN2, Set.mem_Icc] at hu
    exact ne_of_gt (by linarith [hu.1] : (0 : ℝ) < u)
  have hmono := intervalIntegral.integral_mono_on hN2 hintg hintc hpt
  have hintinv : (∫ u in (2 : ℝ)..N, u⁻¹) = Real.log (N / 2) :=
    integral_inv (by rw [Set.uIcc_of_le hN2]; intro h; simp at h; linarith)
  have hcalc : (∫ u in (2 : ℝ)..N, C1 * u⁻¹) = C1 * Real.log (N / 2) := by
    rw [intervalIntegral.integral_const_mul, hintinv]
  have hN2pos : (0 : ℝ) < N / 2 := by linarith
  have hlogN : Real.log (N / 2) ≤ Real.log (Tp / 2) := Real.log_le_log hN2pos (by linarith)
  have hstep1 : C1 * Real.log (N / 2) ≤ C1 * Real.log (Tp / 2) :=
    mul_le_mul_of_nonneg_left hlogN hC1nn
  have hmono' : (∫ u in (2 : ℝ)..N, x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * Tp))
      ≤ C1 * Real.log (N / 2) := hmono.trans (le_of_eq hcalc)
  have hlogTp : Real.log (Tp / 2) ≤ L := by
    rw [hLdef]; exact Real.log_le_log (by linarith) (by linarith)
  have hstep2 : C1 * Real.log (Tp / 2) ≤ x * (16 * Cf + 1) * L ^ 5 / Tp := by
    have hLnn : (0 : ℝ) ≤ L := by rw [hLdef]; linarith
    have hlogTpnn : (0 : ℝ) ≤ Real.log (Tp / 2) := Real.log_nonneg (by linarith)
    have hnum : Cf * L0 ^ 4 + 1 ≤ (16 * Cf + 1) * L ^ 4 := by
      nlinarith [hCf, hL0pow, hL4ge1]
    rw [hC1def, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hTp0.le
    have h4 : x * (Cf * L0 ^ 4 + 1) ≤ x * ((16 * Cf + 1) * L ^ 4) :=
      mul_le_mul_of_nonneg_left hnum hx0.le
    calc x * (Cf * L0 ^ 4 + 1) * Real.log (Tp / 2)
        ≤ x * ((16 * Cf + 1) * L ^ 4) * L := mul_le_mul h4 hlogTp hlogTpnn (by positivity)
      _ = x * (16 * Cf + 1) * L ^ 5 := by ring
  exact le_trans (le_trans hmono' hstep1) hstep2

/-- Piece `∫_{Tp}^M` of the far-left bound. -/
private lemma farLeft_piece2_le {x Cf Tp M : ℝ} (hx : 1 ≤ x) (hCf : 0 ≤ Cf) (hTp : 5 ≤ Tp)
    (hTM : Tp ≤ M) :
    (∫ u in Tp..M, x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * max Tp (u - 1)))
      ≤ 4 * x * (16 * Cf * 4096 + 1) * (Tp ^ ((1 : ℝ) / 2))⁻¹ := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hTp0 : (0 : ℝ) < Tp := by linarith
  set D : ℝ := 2 * x * (16 * Cf * 4096 + 1) with hD
  have hDnn : 0 ≤ D := by rw [hD]; nlinarith [hx0, hCf]
  have hpt : ∀ u ∈ Set.Icc Tp M,
      x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * max Tp (u - 1))
        ≤ D * (u * Real.sqrt u)⁻¹ := by
    intro u hu
    have huT : Tp ≤ u := hu.1
    have hu2 : (2 : ℝ) ≤ u := le_trans (by linarith) huT
    have hu0 : (0 : ℝ) < u := by linarith
    have hlogu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
    have hlog4 : (Real.log (u + Tp + 3)) ^ 4 ≤ 16 * (Real.log u) ^ 4 := by
      have hle : u + Tp + 3 ≤ u ^ 2 := by nlinarith
      have h1 : Real.log (u + Tp + 3) ≤ 2 * Real.log u := by
        calc Real.log (u + Tp + 3) ≤ Real.log (u ^ 2) := Real.log_le_log (by linarith) hle
          _ = 2 * Real.log u := by rw [Real.log_pow]; push_cast; ring
      have h2 := pow_le_pow_left₀ (Real.log_nonneg (by linarith)) h1 4
      rwa [mul_pow, show ((2 : ℝ)) ^ (4 : ℕ) = 16 by norm_num] at h2
    have hnum : x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1)
        ≤ x * (16 * Cf * (Real.log u) ^ 4 + 1) := by
      apply mul_le_mul_of_nonneg_left _ hx0.le
      nlinarith [hCf, hlog4]
    have hstep1 : x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * max Tp (u - 1))
        ≤ 2 * x * (16 * Cf * (Real.log u) ^ 4 + 1) / u ^ 2 := by
      have hden1 : 0 < u * (u - 1) := by nlinarith [hu2]
      have hmax : u * (u - 1) ≤ u * max Tp (u - 1) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hu0.le
      have hdenmax : 0 < u * max Tp (u - 1) :=
        mul_pos hu0 (lt_of_lt_of_le hTp0 (le_max_left _ _))
      have hnum_nn : (0 : ℝ) ≤ x * (16 * Cf * (Real.log u) ^ 4 + 1) := by positivity
      have hA : x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * max Tp (u - 1))
          ≤ x * (16 * Cf * (Real.log u) ^ 4 + 1) / (u * (u - 1)) :=
        div_le_div₀ hnum_nn hnum hden1 hmax
      refine le_trans hA ?_
      have hden2 : 0 < u * (u / 2) := by positivity
      have h2 : u * (u / 2) ≤ u * (u - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hu0.le
      have hB : x * (16 * Cf * (Real.log u) ^ 4 + 1) / (u * (u - 1))
          ≤ x * (16 * Cf * (Real.log u) ^ 4 + 1) / (u * (u / 2)) :=
        div_le_div_of_nonneg_left (by positivity) hden2 h2
      have hC : x * (16 * Cf * (Real.log u) ^ 4 + 1) / (u * (u / 2))
          = 2 * x * (16 * Cf * (Real.log u) ^ 4 + 1) / u ^ 2 := by
        rw [div_eq_div_iff (by positivity) (by positivity)]
        ring
      exact le_trans hB (le_of_eq hC)
    have hstep2 : 2 * x * (16 * Cf * (Real.log u) ^ 4 + 1) / u ^ 2
        ≤ D * (u * Real.sqrt u)⁻¹ := by
      have hlog4' : (Real.log u) ^ 4 ≤ 4096 * Real.sqrt u := log_pow_four_le_sqrt (by linarith)
      have hs1 : (1 : ℝ) ≤ Real.sqrt u := Real.one_le_sqrt.mpr (by linarith)
      have hsn : 0 ≤ Real.sqrt u := Real.sqrt_nonneg u
      have hprod : 16 * Cf * (Real.log u) ^ 4 ≤ 16 * Cf * 4096 * Real.sqrt u := by
        nlinarith [hCf, hlog4']
      have hnum2 : 2 * x * (16 * Cf * (Real.log u) ^ 4 + 1)
          ≤ 2 * x * (16 * Cf * 4096 + 1) * Real.sqrt u := by
        nlinarith [hprod, hx0, hs1, hsn]
      have h1 : 2 * x * (16 * Cf * (Real.log u) ^ 4 + 1) / u ^ 2
          ≤ 2 * x * (16 * Cf * 4096 + 1) * Real.sqrt u / u ^ 2 :=
        div_le_div_of_nonneg_right hnum2 (by positivity)
      have h2 : 2 * x * (16 * Cf * 4096 + 1) * Real.sqrt u / u ^ 2
          = D * (u * Real.sqrt u)⁻¹ := by
        rw [hD]
        field_simp
        rw [Real.sq_sqrt hu0.le]
      exact le_trans h1 (le_of_eq h2)
    exact le_trans hstep1 hstep2
  have hintg : IntervalIntegrable
      (fun u : ℝ => x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * max Tp (u - 1)))
      volume Tp M := by
    apply ContinuousOn.intervalIntegrable
    have hlin : ContinuousOn (fun u : ℝ => u + Tp + 3) (Set.uIcc Tp M) :=
      (continuousOn_id_add_const Tp 3 (Set.uIcc Tp M))
    have hlog : ContinuousOn (fun u : ℝ => Real.log (u + Tp + 3)) (Set.uIcc Tp M) :=
      hlin.log (fun u hu => by
        rw [Set.uIcc_of_le hTM, Set.mem_Icc] at hu
        have h1 : (0 : ℝ) < u := by linarith [hu.1]
        positivity)
    have hnum : ContinuousOn
        (fun u : ℝ => x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1)) (Set.uIcc Tp M) :=
      (((hlog.pow 4).const_mul Cf).add continuousOn_const).const_mul x
    refine ContinuousOn.div hnum ?_ ?_
    · exact continuousOn_id.mul
        ((continuous_const.max (continuous_id.sub continuous_const)).continuousOn)
    · intro u hu
      rw [Set.uIcc_of_le hTM, Set.mem_Icc] at hu
      exact mul_ne_zero (ne_of_gt (by linarith [hu.1] : (0 : ℝ) < u))
        (ne_of_gt (lt_of_lt_of_le hTp0 (le_max_left _ _)))
  have hintc : IntervalIntegrable (fun u : ℝ => D * (u * Real.sqrt u)⁻¹) volume Tp M := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.const_mul (ContinuousOn.inv₀ ?_ ?_) D
    · exact continuousOn_id.mul Real.continuous_sqrt.continuousOn
    · intro u hu
      rw [Set.uIcc_of_le hTM, Set.mem_Icc] at hu
      have hu0 : (0 : ℝ) < u := by linarith [hu.1]
      exact ne_of_gt (mul_pos hu0 (Real.sqrt_pos.mpr hu0))
  have hmono := intervalIntegral.integral_mono_on hTM hintg hintc hpt
  have hcongr : Set.EqOn (fun u : ℝ => (u * Real.sqrt u)⁻¹) (fun u : ℝ => u ^ (-(3 / 2) : ℝ))
      (Set.uIcc Tp M) := by
    intro u hu
    rw [Set.uIcc_of_le hTM, Set.mem_Icc] at hu
    have hu0 : (0 : ℝ) < u := by linarith [hu.1]
    have h3 : u ^ ((3 : ℝ) / 2) = u * Real.sqrt u := by
      rw [show ((3 : ℝ) / 2) = (1 : ℝ) + 1 / 2 by norm_num, Real.rpow_add hu0, Real.rpow_one,
        Real.sqrt_eq_rpow]
    change (u * Real.sqrt u)⁻¹ = u ^ (-(3 / 2) : ℝ)
    rw [← h3, Real.rpow_neg hu0.le]
  have hcongr2 : Set.EqOn (fun u : ℝ => D * (u * Real.sqrt u)⁻¹)
      (fun u : ℝ => D * u ^ (-(3 / 2) : ℝ)) (Set.uIcc Tp M) :=
    fun u hu => by simpa using congrArg (fun z : ℝ => D * z) (hcongr hu)
  have heq2 : (∫ u in Tp..M, D * (u * Real.sqrt u)⁻¹)
      = (∫ u in Tp..M, D * u ^ (-(3 / 2) : ℝ)) :=
    intervalIntegral.integral_congr hcongr2
  rw [heq2, intervalIntegral.integral_const_mul] at hmono
  have h3 := integral_rpow_neg_three_halves_le (T := Tp) (M := M) (by linarith) hTM
  have h4 : D * (∫ u in Tp..M, u ^ (-(3 / 2) : ℝ)) ≤ D * (2 * (Tp ^ ((1 : ℝ) / 2))⁻¹) :=
    mul_le_mul_of_nonneg_left h3 hDnn
  refine le_trans hmono (le_trans h4 (le_of_eq ?_))
  rw [hD]; ring

/-- The far-left tail `∫_2^M` of the pointwise far-left bound. -/
private lemma farLeft_tail_integral_le {x Cf Tp M : ℝ} (hx : 1 ≤ x) (hCf : 0 ≤ Cf)
    (hTp : 5 ≤ Tp) (hM : 2 ≤ M) :
    (∫ u in (2 : ℝ)..M, x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * max Tp (u - 1)))
      ≤ x * (16 * Cf + 1) * (Real.log (Tp + 2)) ^ 5 / Tp
        + 4 * x * (16 * Cf * 4096 + 1) * (Tp ^ ((1 : ℝ) / 2))⁻¹ := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hTp0 : (0 : ℝ) < Tp := by linarith
  have hcontOn : ∀ c d : ℝ, (2 : ℝ) ≤ c → c ≤ d → ContinuousOn
      (fun u : ℝ => x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * max Tp (u - 1)))
      (Set.uIcc c d) := by
    intro c d hc hcd
    have hlin : ContinuousOn (fun u : ℝ => u + Tp + 3) (Set.uIcc c d) :=
      (continuousOn_id_add_const Tp 3 (Set.uIcc c d))
    have hlog : ContinuousOn (fun u : ℝ => Real.log (u + Tp + 3)) (Set.uIcc c d) :=
      hlin.log (fun u hu => by
        rw [Set.uIcc_of_le hcd, Set.mem_Icc] at hu
        have h1 : (0 : ℝ) < u := by linarith [hu.1, hc]
        positivity)
    have hnum : ContinuousOn
        (fun u : ℝ => x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1)) (Set.uIcc c d) :=
      (((hlog.pow 4).const_mul Cf).add continuousOn_const).const_mul x
    refine ContinuousOn.div hnum ?_ ?_
    · exact continuousOn_id.mul
        ((continuous_const.max (continuous_id.sub continuous_const)).continuousOn)
    · intro u hu
      rw [Set.uIcc_of_le hcd, Set.mem_Icc] at hu
      exact mul_ne_zero (ne_of_gt (by linarith [hu.1, hc] : (0 : ℝ) < u))
        (ne_of_gt (lt_of_lt_of_le hTp0 (le_max_left _ _)))
  rcases le_total M Tp with hMT | hTM
  · have hmax : ∀ u ∈ Set.uIcc (2 : ℝ) M, max Tp (u - 1) = Tp := by
      intro u hu
      rw [Set.uIcc_of_le hM] at hu
      exact max_eq_left (by linarith [hu.2, hMT])
    have hEq : Set.EqOn
        (fun u : ℝ => x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * max Tp (u - 1)))
        (fun u : ℝ => x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * Tp)) (Set.uIcc (2 : ℝ) M) :=
      fun u hu => by simp only [hmax u hu]
    rw [intervalIntegral.integral_congr hEq]
    have hp1 := farLeft_piece1_le hx hCf hTp hM hMT
    exact le_trans hp1 (le_add_of_nonneg_right (by positivity))
  · have hsplit : (∫ u in (2 : ℝ)..Tp,
          x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * max Tp (u - 1)))
        + (∫ u in Tp..M,
          x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * max Tp (u - 1)))
        = ∫ u in (2 : ℝ)..M,
          x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * max Tp (u - 1)) :=
      integral_add_adjacent_intervals
        ((hcontOn 2 Tp (by linarith) (by linarith)).intervalIntegrable)
        ((hcontOn Tp M (by linarith) hTM).intervalIntegrable)
    rw [← hsplit]
    have hmax : ∀ u ∈ Set.uIcc (2 : ℝ) Tp, max Tp (u - 1) = Tp := by
      intro u hu
      rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ Tp)] at hu
      exact max_eq_left (by linarith [hu.2])
    have hcongr : Set.EqOn
        (fun u : ℝ => x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * Tp))
        (fun u : ℝ => x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * max Tp (u - 1)))
        (Set.uIcc (2 : ℝ) Tp) := fun u hu => by simp only [hmax u hu]
    have hp1' : (∫ u in (2 : ℝ)..Tp,
          x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * max Tp (u - 1)))
        ≤ x * (16 * Cf + 1) * (Real.log (Tp + 2)) ^ 5 / Tp := by
      rw [← intervalIntegral.integral_congr hcongr]
      exact farLeft_piece1_le hx hCf hTp (by linarith : (2 : ℝ) ≤ Tp) (le_refl Tp)
    have hp2 := farLeft_piece2_le hx hCf hTp hTM
    linarith

/-- Continuity of the far-left majorant on intervals in `[2,∞)`. -/
private lemma continuousOn_farLeft_gfun {x Cf Tp : ℝ} (hTp : 0 < Tp) {c d : ℝ}
    (hc : (2 : ℝ) ≤ c) (hcd : c ≤ d) :
    ContinuousOn (fun u : ℝ => x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * max Tp (u - 1)))
      (Set.uIcc c d) := by
  have hlin : ContinuousOn (fun u : ℝ => u + Tp + 3) (Set.uIcc c d) :=
    continuousOn_id_add_const Tp 3 (Set.uIcc c d)
  have hlog : ContinuousOn (fun u : ℝ => Real.log (u + Tp + 3)) (Set.uIcc c d) :=
    hlin.log (fun u hu => by
      rw [Set.uIcc_of_le hcd, Set.mem_Icc] at hu
      have h1 : (0 : ℝ) < u := by linarith [hu.1, hc]
      positivity)
  have hnum : ContinuousOn (fun u : ℝ => x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1))
      (Set.uIcc c d) :=
    (((hlog.pow 4).const_mul Cf).add continuousOn_const).const_mul x
  refine ContinuousOn.div hnum ?_ ?_
  · exact continuousOn_id.mul
      ((continuous_const.max (continuous_id.sub continuous_const)).continuousOn)
  · intro u hu
    rw [Set.uIcc_of_le hcd, Set.mem_Icc] at hu
    exact mul_ne_zero (ne_of_gt (by linarith [hu.1, hc] : (0 : ℝ) < u))
      (ne_of_gt (lt_of_lt_of_le hTp (le_max_left _ _)))

/-- the "middle" region `[-2,-1/2]` (or a subinterval) of the horizontal edge. -/
private lemma midRegion_integral_le {x Cf Tp c d : ℝ} (hx : 1 ≤ x) (hCf : 0 ≤ Cf)
    (hTp : 5 ≤ Tp) (hcd : c ≤ d) (hc : -2 ≤ c) (hd : d ≤ -(1 / 2 : ℝ))
    (hlen : d - c ≤ 3 / 2)
    (hint : IntervalIntegrable
      (fun σ : ℝ => ‖tiltIntF x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖) volume c d)
    (hpt : ∀ σ ∈ Set.Icc c d, ‖tiltIntF x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖
      ≤ x * (Cf * (Real.log (|σ| + Tp + 3)) ^ 4 + 1) / (|σ| * max Tp (|σ| - 1))) :
    (∫ σ in c..d, ‖tiltIntF x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖)
      ≤ 3 * (16 * Cf + 1) * x ^ 2 * (Real.log (Tp + 2)) ^ 5 / Tp := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hTp0 : (0 : ℝ) < Tp := by linarith
  set L : ℝ := Real.log (Tp + 2) with hL
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hL]
    have h1 : Real.exp 1 ≤ (7 : ℝ) := le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num))
    have h2 := Real.log_le_log (Real.exp_pos 1) h1
    rw [Real.log_exp] at h2
    have h3 : Real.log (7 : ℝ) ≤ Real.log (Tp + 2) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  set B : ℝ := 2 * (16 * Cf + 1) * x ^ 2 * L ^ 5 / Tp with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hpt2 : ∀ σ ∈ Set.Icc c d,
      x * (Cf * (Real.log (|σ| + Tp + 3)) ^ 4 + 1) / (|σ| * max Tp (|σ| - 1)) ≤ B := by
    intro σ hσ
    have hneg : σ < 0 := by linarith [hσ.2, hd]
    have hs1 : (1 / 2 : ℝ) ≤ |σ| := by
      rw [abs_of_neg hneg]; linarith [hσ.2, hd]
    have hs2 : |σ| ≤ 2 := by
      rw [abs_le]; exact ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hlogσ : Real.log (|σ| + Tp + 3) ≤ 2 * L := by
      rw [hL]
      have hle : |σ| + Tp + 3 ≤ (Tp + 2) ^ 2 := by nlinarith [hs2, hTp]
      calc Real.log (|σ| + Tp + 3) ≤ Real.log ((Tp + 2) ^ 2) :=
            Real.log_le_log (by linarith) hle
        _ = 2 * Real.log (Tp + 2) := by rw [Real.log_pow]; push_cast; ring
    have hlogσnn : 0 ≤ Real.log (|σ| + Tp + 3) := Real.log_nonneg (by linarith)
    have hlog4 : (Real.log (|σ| + Tp + 3)) ^ 4 ≤ 16 * L ^ 4 := by
      have h := pow_le_pow_left₀ hlogσnn hlogσ 4
      rwa [mul_pow, show ((2 : ℝ)) ^ (4 : ℕ) = 16 by norm_num] at h
    have hden : (1 / 2 : ℝ) * Tp ≤ |σ| * max Tp (|σ| - 1) := by
      have h2 : Tp ≤ max Tp (|σ| - 1) := le_max_left _ _
      nlinarith
    have hdenpos : 0 < (1 / 2 : ℝ) * Tp := by linarith
    have hnum : x * (Cf * (Real.log (|σ| + Tp + 3)) ^ 4 + 1)
        ≤ x * (16 * Cf * L ^ 4 + 1) := by
      apply mul_le_mul_of_nonneg_left _ hx0.le
      nlinarith [hCf, hlog4]
    have hstep : x * (Cf * (Real.log (|σ| + Tp + 3)) ^ 4 + 1) / (|σ| * max Tp (|σ| - 1))
        ≤ 2 * x * (16 * Cf * L ^ 4 + 1) / Tp := by
      calc x * (Cf * (Real.log (|σ| + Tp + 3)) ^ 4 + 1) / (|σ| * max Tp (|σ| - 1))
          ≤ x * (16 * Cf * L ^ 4 + 1) / ((1 / 2) * Tp) :=
            div_le_div₀ (by positivity) hnum hdenpos hden
        _ = 2 * x * (16 * Cf * L ^ 4 + 1) / Tp := by
            rw [div_eq_div_iff (ne_of_gt hdenpos) (ne_of_gt hTp0)]
            ring
    refine le_trans hstep ?_
    rw [hB, div_le_div_iff_of_pos_right hTp0]
    have hx2 : x ≤ x ^ 2 := by nlinarith [hx0, hx]
    have hx2nn : (0 : ℝ) ≤ x ^ 2 := by positivity
    have hL45 : L ^ 4 ≤ L ^ 5 := by
      have h := pow_le_pow_right₀ hL1 (by norm_num : 4 ≤ 5); simpa using h
    have hL4nn : (0 : ℝ) ≤ L ^ 4 := by positivity
    have hL5ge1 : (1 : ℝ) ≤ L ^ 5 := one_le_pow₀ hL1
    have hA : 16 * Cf * (x * L ^ 4) ≤ 16 * Cf * (x ^ 2 * L ^ 5) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hx2 hL45 hL4nn hx2nn) (by positivity)
    have hB' : x ≤ x ^ 2 * L ^ 5 := by nlinarith [hx2, hL5ge1, hx0]
    calc 2 * x * (16 * Cf * L ^ 4 + 1) = 2 * (16 * Cf * (x * L ^ 4) + x) := by ring
      _ ≤ 2 * (16 * Cf * (x ^ 2 * L ^ 5) + x ^ 2 * L ^ 5) := by linarith [hA, hB']
      _ = 2 * (16 * Cf + 1) * x ^ 2 * L ^ 5 := by ring
  have hconst : IntervalIntegrable (fun _ : ℝ => B) volume c d :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ => B) (Set.uIcc c d)).intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hcd hint hconst
    (fun σ hσ => le_trans (hpt σ hσ) (hpt2 σ hσ))
  have hval : (∫ σ in c..d, B) = (d - c) * B := by
    rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
  rw [hval] at hmono
  refine le_trans hmono ?_
  calc (d - c) * B ≤ (3 / 2) * B := mul_le_mul_of_nonneg_right hlen hBnn
    _ = 3 * (16 * Cf + 1) * x ^ 2 * (Real.log (Tp + 2)) ^ 5 / Tp := by rw [hB, hL]; ring

/-- the strip region `[-1/2,2]` (or a subinterval) of the horizontal edge. -/
private lemma stripRegion_integral_le {x Cs Tp δ c d : ℝ} (hx : 1 ≤ x) (hTp : 5 ≤ Tp)
    (hCs : 0 ≤ Cs) (hδ : 0 < δ)
    (hcd : c ≤ d) (hlen : d - c ≤ 5 / 2)
    (hint : IntervalIntegrable
      (fun σ : ℝ => ‖tiltIntF x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖) volume c d)
    (hpt : ∀ σ ∈ Set.Icc c d, ‖tiltIntF x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖
      ≤ x ^ 2 * (Cs * ((Real.log (Tp + 3) + 1) ^ 3 + (Real.log (Tp + 3) + 1) ^ 2 / δ) + 1)
          / Tp) :
    (∫ σ in c..d, ‖tiltIntF x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖)
      ≤ (5 / 2) * x ^ 2 * ((27 * Cs + 1) * (Real.log (Tp + 2)) ^ 3 / Tp
          + 9 * Cs * (Real.log (Tp + 2)) ^ 3 / (δ * Tp)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hTp0 : (0 : ℝ) < Tp := by linarith
  set L : ℝ := Real.log (Tp + 2) with hL
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hL]
    have h1 : Real.exp 1 ≤ (7 : ℝ) := le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num))
    have h2 := Real.log_le_log (Real.exp_pos 1) h1
    rw [Real.log_exp] at h2
    have h3 : Real.log (7 : ℝ) ≤ Real.log (Tp + 2) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hM3L : Real.log (Tp + 3) + 1 ≤ 3 * L := by
    rw [hL]
    have hle : Tp + 3 ≤ (Tp + 2) * (Tp + 2) := by nlinarith [hTp]
    have h1 : Real.log (Tp + 3) ≤ 2 * Real.log (Tp + 2) := by
      calc Real.log (Tp + 3) ≤ Real.log ((Tp + 2) * (Tp + 2)) :=
            Real.log_le_log (by linarith) hle
        _ = 2 * Real.log (Tp + 2) := by rw [Real.log_mul (by linarith) (by linarith)]; ring
    have h3 : (1 : ℝ) ≤ Real.log (Tp + 3) := by
      have h4 : Real.log (7 : ℝ) ≤ Real.log (Tp + 3) :=
        Real.log_le_log (by norm_num) (by linarith)
      have h5 : Real.exp 1 ≤ (7 : ℝ) := le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num))
      have h6 := Real.log_le_log (Real.exp_pos 1) h5
      rw [Real.log_exp] at h6
      linarith
    linarith
  have hMnn : (0 : ℝ) ≤ Real.log (Tp + 3) + 1 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ Tp + 3 by linarith); linarith
  have hM3 : (Real.log (Tp + 3) + 1) ^ 3 ≤ 27 * L ^ 3 := by
    have h := pow_le_pow_left₀ hMnn hM3L 3
    rwa [mul_pow, show ((3 : ℝ)) ^ (3 : ℕ) = 27 by norm_num] at h
  have hM2 : (Real.log (Tp + 3) + 1) ^ 2 ≤ 9 * L ^ 3 := by
    have h := pow_le_pow_left₀ hMnn hM3L 2
    rw [mul_pow, show ((3 : ℝ)) ^ (2 : ℕ) = 9 by norm_num] at h
    have hL2 : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL1
    nlinarith [h, hL1, hL2]
  have hL3ge1 : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL1
  have hCqbound : Cs * (Real.log (Tp + 3) + 1) ^ 3
        + Cs * ((Real.log (Tp + 3) + 1) ^ 2 / δ) + 1
      ≤ (27 * Cs + 1) * L ^ 3 + 9 * Cs * L ^ 3 / δ := by
    have hA : Cs * (Real.log (Tp + 3) + 1) ^ 3 ≤ 27 * Cs * L ^ 3 := by
      calc Cs * (Real.log (Tp + 3) + 1) ^ 3 ≤ Cs * (27 * L ^ 3) :=
            mul_le_mul_of_nonneg_left hM3 hCs
        _ = 27 * Cs * L ^ 3 := by ring
    have hB : Cs * ((Real.log (Tp + 3) + 1) ^ 2 / δ) ≤ 9 * Cs * L ^ 3 / δ := by
      calc Cs * ((Real.log (Tp + 3) + 1) ^ 2 / δ) ≤ Cs * (9 * L ^ 3 / δ) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hM2 hδ.le) hCs
        _ = 9 * Cs * L ^ 3 / δ := by ring
    linarith [hA, hB, hL3ge1]
  set B : ℝ := x ^ 2 * ((27 * Cs + 1) * L ^ 3 / Tp + 9 * Cs * L ^ 3 / (δ * Tp)) with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    have h1 : (0 : ℝ) ≤ (27 * Cs + 1) * L ^ 3 / Tp := by positivity
    have h2 : (0 : ℝ) ≤ 9 * Cs * L ^ 3 / (δ * Tp) := by positivity
    positivity
  have hpt2 : ∀ σ ∈ Set.Icc c d,
      x ^ 2 * (Cs * ((Real.log (Tp + 3) + 1) ^ 3 + (Real.log (Tp + 3) + 1) ^ 2 / δ) + 1) / Tp ≤ B := by
    intro σ hσ
    have hx2nn : (0 : ℝ) ≤ x ^ 2 := by positivity
    rw [hBdef, div_le_iff₀ hTp0]
    have heq2 : Cs * ((Real.log (Tp + 3) + 1) ^ 3 + (Real.log (Tp + 3) + 1) ^ 2 / δ) + 1
        = Cs * (Real.log (Tp + 3) + 1) ^ 3 + Cs * ((Real.log (Tp + 3) + 1) ^ 2 / δ) + 1 := by
      ring
    have hsum : x ^ 2 * (Cs * ((Real.log (Tp + 3) + 1) ^ 3 + (Real.log (Tp + 3) + 1) ^ 2 / δ) + 1)
        ≤ x ^ 2 * ((27 * Cs + 1) * L ^ 3 + 9 * Cs * L ^ 3 / δ) := by
      rw [heq2]
      exact mul_le_mul_of_nonneg_left hCqbound hx2nn
    have heq : x ^ 2 * ((27 * Cs + 1) * L ^ 3 / Tp + 9 * Cs * L ^ 3 / (δ * Tp)) * Tp
        = x ^ 2 * ((27 * Cs + 1) * L ^ 3 + 9 * Cs * L ^ 3 / δ) := by
      field_simp
    rw [heq]
    exact hsum
  have hconst : IntervalIntegrable (fun _ : ℝ => B) volume c d :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ => B) (Set.uIcc c d)).intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hcd hint hconst
    (fun σ hσ => le_trans (hpt σ hσ) (hpt2 σ hσ))
  have hval : (∫ σ in c..d, B) = (d - c) * B := by
    rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
  rw [hval] at hmono
  refine le_trans hmono ?_
  calc (d - c) * B ≤ (5 / 2) * B := mul_le_mul_of_nonneg_right hlen hBnn
    _ = (5 / 2) * x ^ 2 * ((27 * Cs + 1) * (Real.log (Tp + 2)) ^ 3 / Tp
          + 9 * Cs * (Real.log (Tp + 2)) ^ 3 / (δ * Tp)) := by rw [hBdef, hL]; ring

/-- `a * b * c ≤ a^2 * b * c` for `1 ≤ a`, `0 ≤ b`, `0 ≤ c`. -/
private lemma mul_sq_le {a b c : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤ a ^ 2 * b * c := by
  have h : a ≤ a ^ 2 := by nlinarith
  calc a * b * c = (a * b) * c := by ring
    _ ≤ (a ^ 2 * b) * c := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hb) hc
    _ = a ^ 2 * b * c := by ring

/-- **Horizontal edge bound**: the integral of the tilted kernel along the line `Im s = Tp`
over `a ≤ Re s ≤ 2` is small. -/
theorem tiltIntF_horiz_integral_bound (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x Tp δ a : ℝ, 1 ≤ x → 5 ≤ Tp → x ≤ Tp → 0 < δ →
      (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - Tp|) → a ≤ -1 →
      (∫ σ in a..2, ‖tiltIntF x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖)
        ≤ C * x ^ 2 * ((Real.log (Tp + 2)) ^ 5 / Tp +
            (Real.log (Tp + 2)) ^ 3 / (δ * Tp) + 1 / Real.sqrt Tp) := by
  obtain ⟨Cf, hCfpos, hCf⟩ := logDeriv_riemannZeta1_halfplane_far_t_le
  obtain ⟨Cs, hCspos, hCs⟩ := logDeriv_zeta1_strip_goodHeight_le h
  set K : ℝ := (16 * Cf + 1) + 3 * (16 * Cf + 1) + (5 / 2) * (27 * Cs + 1)
      + (5 / 2) * (9 * Cs) + 4 * (16 * Cf * 4096 + 1) + 1 with hK
  refine ⟨K, ?_, fun x Tp δ a hx hTp hxTp hδ hgap ha => ?_⟩
  · rw [hK]; nlinarith [hCfpos, hCspos]
  have hx0 : (0 : ℝ) < x := by linarith
  have hTp0 : (0 : ℝ) < Tp := by linarith
  set G : ℝ → ℝ := fun σ => ‖tiltIntF x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖ with hGdef
  have hneAll : ∀ σ : ℝ, riemannZeta₁ ((σ : ℂ) + Complex.I * (Tp : ℂ)) ≠ 0 := by
    intro σ hz
    have h1 := hgap ((σ : ℂ) + Complex.I * (Tp : ℂ)) hz
    have h2 : (((σ : ℂ) + Complex.I * (Tp : ℂ)).im : ℝ) = Tp := by simp
    rw [h2, sub_self, abs_zero] at h1
    linarith [hδ]
  have hGi : ∀ c d : ℝ, IntervalIntegrable G volume c d := by
    intro c d
    exact (continuousOn_tiltIntF_line (x := x) (T := Tp) hx0 (by linarith)
      (fun σ _ => hneAll σ)).norm.intervalIntegrable
  have hGi' : ∀ c d : ℝ, IntervalIntegrable (fun u : ℝ => G (-u)) volume c d := by
    intro c d
    exact (continuousOn_tiltIntF_line_neg (x := x) (T := Tp) hx0 (by linarith)
      (fun σ _ => hneAll (-σ))).norm.intervalIntegrable
  have hptFar : ∀ σ : ℝ, σ ≤ -(1 / 2 : ℝ) → G σ
      ≤ x * (Cf * (Real.log (|σ| + Tp + 3)) ^ 4 + 1) / (|σ| * max Tp (|σ| - 1)) := by
    intro σ hσ
    refine tiltIntF_pointwise_farLeft hx (by linarith) hCfpos.le hσ ?_
    have h1 := hCf σ Tp (by linarith) (by rw [abs_of_nonneg hTp0.le]; linarith)
    rwa [abs_of_nonneg hTp0.le] at h1
  have hptStrip : ∀ σ : ℝ, -(1 / 2 : ℝ) ≤ σ → σ ≤ 2 → G σ
      ≤ x ^ 2 * (Cs * ((Real.log (Tp + 3) + 1) ^ 3 + (Real.log (Tp + 3) + 1) ^ 2 / δ) + 1)
          / Tp := by
    intro σ h1 h2
    exact tiltIntF_pointwise_strip hx hTp hxTp hCspos.le hδ h2
      (hCs Tp δ hTp hδ hgap σ h1 h2)
  set L5 : ℝ := (Real.log (Tp + 2)) ^ 5 with hL5
  set L3 : ℝ := (Real.log (Tp + 2)) ^ 3 with hL3
  set R : ℝ := (Tp ^ ((1 : ℝ) / 2))⁻¹ with hR
  have hLp : (0 : ℝ) < Real.log (Tp + 2) := Real.log_pos (by linarith)
  have hL5nn : 0 ≤ L5 := by rw [hL5]; positivity
  have hL3nn : 0 ≤ L3 := by rw [hL3]; positivity
  have hRnn : 0 ≤ R := by rw [hR]; positivity
  have hL35 : L3 ≤ L5 := by
    rw [hL3, hL5]
    have h1 : (1 : ℝ) ≤ Real.log (Tp + 2) := by
      have h2 : Real.exp 1 ≤ (7 : ℝ) := le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num))
      have h3 := Real.log_le_log (Real.exp_pos 1) h2
      rw [Real.log_exp] at h3
      have h4 : Real.log (7 : ℝ) ≤ Real.log (Tp + 2) :=
        Real.log_le_log (by norm_num) (by linarith)
      linarith
    exact pow_le_pow_right₀ h1 (by norm_num : 3 ≤ 5)
  have hK5 : (16 * Cf + 1) + 3 * (16 * Cf + 1) + (5 / 2) * (27 * Cs + 1) ≤ K := by
    rw [hK]; linarith
  have hKd : (5 / 2) * (9 * Cs) ≤ K := by rw [hK]; linarith
  have hKr : 4 * (16 * Cf * 4096 + 1) ≤ K := by rw [hK]; linarith
  rcases lt_or_ge a (-2) with ha2 | ha2
  · -- a < -2
    have hM2 : (2 : ℝ) ≤ -a := by linarith
    have hsplit1 : (∫ σ in a..(-2), G σ) + (∫ σ in (-2)..(-1 / 2), G σ)
        = ∫ σ in a..(-1 / 2), G σ :=
      integral_add_adjacent_intervals (hGi a (-2)) (hGi (-2) (-1 / 2))
    have hsplit2 : (∫ σ in a..(-1 / 2), G σ) + (∫ σ in (-1 / 2)..2, G σ)
        = ∫ σ in a..2, G σ :=
      integral_add_adjacent_intervals (hGi a (-1 / 2)) (hGi (-1 / 2) 2)
    have hlow : (∫ σ in a..(-2), G σ) ≤ x * (16 * Cf + 1) * L5 / Tp + 4 * x * (16 * Cf * 4096 + 1) * R := by
      have h1 : (∫ σ in (-2 : ℝ)..a, G σ) = (∫ u in (-a)..2, G (-u)) := by
        have h2 := integral_comp_neg (fun z : ℝ => G (-z)) (a := (-2 : ℝ)) (b := a)
        simpa using h2
      have h4 : (∫ σ in a..(-2), G σ) = -(∫ σ in (-2 : ℝ)..a, G σ) := integral_symm (-2) a
      have h5 : -(∫ u in (-a)..2, G (-u)) = (∫ u in (2 : ℝ)..(-a), G (-u)) := by
        rw [integral_symm (2 : ℝ) (-a)]; ring
      rw [h4, h1, h5]
      have hpt : ∀ u ∈ Set.Icc (2 : ℝ) (-a), G (-u)
          ≤ x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * max Tp (u - 1)) := by
        intro u hu
        have hu2 : (2 : ℝ) ≤ u := hu.1
        have hh := hptFar (-u) (by linarith)
        simp only [abs_of_neg (by linarith : (-u : ℝ) < 0), neg_neg] at hh
        exact hh
      have hmono := intervalIntegral.integral_mono_on hM2 (hGi' 2 (-a))
        ((continuousOn_farLeft_gfun (x := x) (Cf := Cf) (Tp := Tp) hTp0 (by norm_num) hM2).intervalIntegrable)
        hpt
      have htail : (∫ u in (2 : ℝ)..(-a),
            x * (Cf * (Real.log (u + Tp + 3)) ^ 4 + 1) / (u * max Tp (u - 1)))
          ≤ x * (16 * Cf + 1) * L5 / Tp + 4 * x * (16 * Cf * 4096 + 1) * R := by
        have hh := farLeft_tail_integral_le hx hCfpos.le hTp hM2
        rw [← hL5, ← hR] at hh
        exact hh
      exact le_trans hmono htail
    have hmid : (∫ σ in (-2)..(-1 / 2), G σ) ≤ 3 * (16 * Cf + 1) * x ^ 2 * L5 / Tp := by
      have hh := midRegion_integral_le (x := x) (Cf := Cf) (Tp := Tp) (c := (-2 : ℝ)) (d := (-1/2 : ℝ))
        hx hCfpos.le hTp (by norm_num) (by norm_num) (by norm_num)
        (by norm_num : (-1/2 : ℝ) - (-2) ≤ 3/2) (hGi (-2) (-1/2))
        (fun σ hσ => hptFar σ (by linarith [hσ.2]))
      rwa [← hL5] at hh
    have hstrip : (∫ σ in (-1 / 2)..2, G σ)
        ≤ (5 / 2) * x ^ 2 * ((27 * Cs + 1) * L3 / Tp + 9 * Cs * L3 / (δ * Tp)) := by
      have hh := stripRegion_integral_le (x := x) (Cs := Cs) (Tp := Tp) (δ := δ)
        (c := (-1/2 : ℝ)) (d := 2) hx hTp hCspos.le hδ (by norm_num)
        (by norm_num : (2:ℝ) - (-1/2) ≤ 5/2) (hGi (-1/2) 2)
        (fun σ hσ => hptStrip σ (by linarith [hσ.1]) (by linarith [hσ.2]))
      rwa [← hL3] at hh
    rw [← hsplit2, ← hsplit1]
    have hfin : x * (16 * Cf + 1) * L5 / Tp + 4 * x * (16 * Cf * 4096 + 1) * R
          + 3 * (16 * Cf + 1) * x ^ 2 * L5 / Tp
          + (5 / 2) * x ^ 2 * ((27 * Cs + 1) * L3 / Tp + 9 * Cs * L3 / (δ * Tp))
        ≤ K * x ^ 2 * (L5 / Tp + L3 / (δ * Tp) + R) := by
      have hxx : x ≤ x ^ 2 := by nlinarith [hx0, hx]
      have hc1 : (0 : ℝ) ≤ 16 * Cf + 1 := by linarith
      have hc2 : (0 : ℝ) ≤ 4 * (16 * Cf * 4096 + 1) := by linarith
      have hc3 : (0 : ℝ) ≤ (5 / 2) * (27 * Cs + 1) := by linarith
      have hc4 : (0 : ℝ) ≤ (5 / 2) * (9 * Cs) := by linarith
      have hAn : (0 : ℝ) ≤ L5 / Tp := by
        rw [hL5, div_eq_mul_inv]
        exact mul_nonneg (pow_nonneg (Real.log_pos (by linarith)).le 5) (inv_nonneg.mpr hTp0.le)
      have hBn : (0 : ℝ) ≤ L3 / (δ * Tp) := by
        rw [hL3, div_eq_mul_inv]
        exact mul_nonneg (pow_nonneg (Real.log_pos (by linarith)).le 3)
          (inv_nonneg.mpr (by positivity))
      have hA1 : x * (16 * Cf + 1) * (L5 / Tp) ≤ (16 * Cf + 1) * x ^ 2 * (L5 / Tp) := by
        have h := mul_sq_le hx hc1 hAn
        linarith [h]
      have hA2 : x * (4 * (16 * Cf * 4096 + 1)) * R ≤ (4 * (16 * Cf * 4096 + 1)) * x ^ 2 * R := by
        have h := mul_sq_le hx hc2 hRnn
        linarith [h]
      have hA4 : (5 / 2) * x ^ 2 * ((27 * Cs + 1) * (L3 / Tp))
          ≤ (5 / 2) * x ^ 2 * ((27 * Cs + 1) * (L5 / Tp)) := by
        have h1 : (27 * Cs + 1) * (L3 / Tp) ≤ (27 * Cs + 1) * (L5 / Tp) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hL35 hTp0.le) (by linarith)
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have hE : x * (16 * Cf + 1) * L5 / Tp + 4 * x * (16 * Cf * 4096 + 1) * R
            + 3 * (16 * Cf + 1) * x ^ 2 * L5 / Tp
            + (5 / 2) * x ^ 2 * ((27 * Cs + 1) * L3 / Tp + 9 * Cs * L3 / (δ * Tp))
          = x * (16 * Cf + 1) * (L5 / Tp) + x * (4 * (16 * Cf * 4096 + 1)) * R
            + 3 * (16 * Cf + 1) * x ^ 2 * (L5 / Tp)
            + (5 / 2) * x ^ 2 * ((27 * Cs + 1) * (L3 / Tp))
            + (5 / 2) * x ^ 2 * (9 * Cs * (L3 / (δ * Tp))) := by ring
      rw [hE]
      have hx2nn : (0 : ℝ) ≤ x ^ 2 := by positivity
      calc x * (16 * Cf + 1) * (L5 / Tp) + x * (4 * (16 * Cf * 4096 + 1)) * R
            + 3 * (16 * Cf + 1) * x ^ 2 * (L5 / Tp)
            + (5 / 2) * x ^ 2 * ((27 * Cs + 1) * (L3 / Tp))
            + (5 / 2) * x ^ 2 * (9 * Cs * (L3 / (δ * Tp)))
          ≤ (16 * Cf + 1) * x ^ 2 * (L5 / Tp) + (4 * (16 * Cf * 4096 + 1)) * x ^ 2 * R
            + 3 * (16 * Cf + 1) * x ^ 2 * (L5 / Tp)
            + (5 / 2) * x ^ 2 * ((27 * Cs + 1) * (L5 / Tp))
            + (5 / 2) * x ^ 2 * (9 * Cs * (L3 / (δ * Tp))) := by linarith [hA1, hA2, hA4]
        _ = x ^ 2 * (((16 * Cf + 1) + 3 * (16 * Cf + 1) + (5 / 2) * (27 * Cs + 1)) * (L5 / Tp)
              + (4 * (16 * Cf * 4096 + 1)) * R + ((5 / 2) * (9 * Cs)) * (L3 / (δ * Tp))) := by ring
        _ ≤ x ^ 2 * (K * (L5 / Tp) + K * R + K * (L3 / (δ * Tp))) := by
            refine mul_le_mul_of_nonneg_left ?_ hx2nn
            have f1 : ((16 * Cf + 1) + 3 * (16 * Cf + 1) + (5 / 2) * (27 * Cs + 1)) * (L5 / Tp)
                ≤ K * (L5 / Tp) := mul_le_mul_of_nonneg_right hK5 hAn
            have f2 : (4 * (16 * Cf * 4096 + 1)) * R ≤ K * R := mul_le_mul_of_nonneg_right hKr hRnn
            have f3 : ((5 / 2) * (9 * Cs)) * (L3 / (δ * Tp)) ≤ K * (L3 / (δ * Tp)) :=
              mul_le_mul_of_nonneg_right hKd hBn
            linarith [f1, f2, f3]
        _ = K * x ^ 2 * (L5 / Tp + L3 / (δ * Tp) + R) := by ring
    have hRT : 1 / Real.sqrt Tp = R := by rw [one_div, hR, Real.sqrt_eq_rpow]
    have hgoal : K * x ^ 2 * (L5 / Tp + L3 / (δ * Tp) + R)
        = K * x ^ 2 * ((Real.log (Tp + 2)) ^ 5 / Tp
            + (Real.log (Tp + 2)) ^ 3 / (δ * Tp) + 1 / Real.sqrt Tp) := by
      rw [hRT, hL5, hL3]
    have hb : ((∫ σ in a..(-2), G σ) + (∫ σ in (-2)..(-1 / 2), G σ))
          + (∫ σ in (-1 / 2)..2, G σ)
        ≤ x * (16 * Cf + 1) * L5 / Tp + 4 * x * (16 * Cf * 4096 + 1) * R
          + 3 * (16 * Cf + 1) * x ^ 2 * L5 / Tp
          + (5 / 2) * x ^ 2 * ((27 * Cs + 1) * L3 / Tp + 9 * Cs * L3 / (δ * Tp)) := by
      linarith [hlow, hmid, hstrip]
    exact le_trans hb (le_trans hfin (le_of_eq hgoal))
  · -- -2 ≤ a
    have hsplit2 : (∫ σ in a..(-1 / 2), G σ) + (∫ σ in (-1 / 2)..2, G σ)
        = ∫ σ in a..2, G σ :=
      integral_add_adjacent_intervals (hGi a (-1 / 2)) (hGi (-1 / 2) 2)
    have hmid : (∫ σ in a..(-1 / 2), G σ) ≤ 3 * (16 * Cf + 1) * x ^ 2 * L5 / Tp := by
      have hh := midRegion_integral_le (x := x) (Cf := Cf) (Tp := Tp) (c := a) (d := (-1/2 : ℝ))
        hx hCfpos.le hTp (by linarith) ha2 (by norm_num) (by linarith) (hGi a (-1/2))
        (fun σ hσ => hptFar σ (by linarith [hσ.2]))
      rwa [← hL5] at hh
    have hstrip : (∫ σ in (-1 / 2)..2, G σ)
        ≤ (5 / 2) * x ^ 2 * ((27 * Cs + 1) * L3 / Tp + 9 * Cs * L3 / (δ * Tp)) := by
      have hh := stripRegion_integral_le (x := x) (Cs := Cs) (Tp := Tp) (δ := δ)
        (c := (-1/2 : ℝ)) (d := 2) hx hTp hCspos.le hδ (by norm_num)
        (by norm_num : (2:ℝ) - (-1/2) ≤ 5/2) (hGi (-1/2) 2)
        (fun σ hσ => hptStrip σ (by linarith [hσ.1]) (by linarith [hσ.2]))
      rwa [← hL3] at hh
    rw [← hsplit2]
    have hfin : 3 * (16 * Cf + 1) * x ^ 2 * L5 / Tp
          + (5 / 2) * x ^ 2 * ((27 * Cs + 1) * L3 / Tp + 9 * Cs * L3 / (δ * Tp))
        ≤ K * x ^ 2 * (L5 / Tp + L3 / (δ * Tp) + R) := by
      have hc1 : (0 : ℝ) ≤ 16 * Cf + 1 := by linarith
      have hc3 : (0 : ℝ) ≤ (5 / 2) * (27 * Cs + 1) := by linarith
      have hc4 : (0 : ℝ) ≤ (5 / 2) * (9 * Cs) := by linarith
      have hAn : (0 : ℝ) ≤ L5 / Tp := by
        rw [hL5, div_eq_mul_inv]
        exact mul_nonneg (pow_nonneg (Real.log_pos (by linarith)).le 5) (inv_nonneg.mpr hTp0.le)
      have hBn : (0 : ℝ) ≤ L3 / (δ * Tp) := by
        rw [hL3, div_eq_mul_inv]
        exact mul_nonneg (pow_nonneg (Real.log_pos (by linarith)).le 3)
          (inv_nonneg.mpr (by positivity))
      have hx2nn : (0 : ℝ) ≤ x ^ 2 := by positivity
      have hA4 : (5 / 2) * x ^ 2 * ((27 * Cs + 1) * (L3 / Tp))
          ≤ (5 / 2) * x ^ 2 * ((27 * Cs + 1) * (L5 / Tp)) := by
        have h1 : (27 * Cs + 1) * (L3 / Tp) ≤ (27 * Cs + 1) * (L5 / Tp) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hL35 hTp0.le) (by linarith)
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have hE : 3 * (16 * Cf + 1) * x ^ 2 * L5 / Tp
            + (5 / 2) * x ^ 2 * ((27 * Cs + 1) * L3 / Tp + 9 * Cs * L3 / (δ * Tp))
          = 3 * (16 * Cf + 1) * x ^ 2 * (L5 / Tp)
            + (5 / 2) * x ^ 2 * ((27 * Cs + 1) * (L3 / Tp))
            + (5 / 2) * x ^ 2 * (9 * Cs * (L3 / (δ * Tp))) := by ring
      rw [hE]
      calc 3 * (16 * Cf + 1) * x ^ 2 * (L5 / Tp)
            + (5 / 2) * x ^ 2 * ((27 * Cs + 1) * (L3 / Tp))
            + (5 / 2) * x ^ 2 * (9 * Cs * (L3 / (δ * Tp)))
          ≤ 3 * (16 * Cf + 1) * x ^ 2 * (L5 / Tp)
            + (5 / 2) * x ^ 2 * ((27 * Cs + 1) * (L5 / Tp))
            + (5 / 2) * x ^ 2 * (9 * Cs * (L3 / (δ * Tp))) := by linarith [hA4]
        _ = x ^ 2 * ((3 * (16 * Cf + 1) + (5 / 2) * (27 * Cs + 1)) * (L5 / Tp)
              + ((5 / 2) * (9 * Cs)) * (L3 / (δ * Tp))) := by ring
        _ ≤ x ^ 2 * (K * (L5 / Tp) + K * R + K * (L3 / (δ * Tp))) := by
            refine mul_le_mul_of_nonneg_left ?_ hx2nn
            have f1 : (3 * (16 * Cf + 1) + (5 / 2) * (27 * Cs + 1)) * (L5 / Tp) ≤ K * (L5 / Tp) :=
              mul_le_mul_of_nonneg_right (by linarith [hK5]) hAn
            have f2 : (0 : ℝ) ≤ K * R := mul_nonneg (by linarith) hRnn
            have f3 : ((5 / 2) * (9 * Cs)) * (L3 / (δ * Tp)) ≤ K * (L3 / (δ * Tp)) :=
              mul_le_mul_of_nonneg_right hKd hBn
            linarith [f1, f2, f3]
        _ = K * x ^ 2 * (L5 / Tp + L3 / (δ * Tp) + R) := by ring
    have hRT : 1 / Real.sqrt Tp = R := by rw [one_div, hR, Real.sqrt_eq_rpow]
    have hgoal : K * x ^ 2 * (L5 / Tp + L3 / (δ * Tp) + R)
        = K * x ^ 2 * ((Real.log (Tp + 2)) ^ 5 / Tp
            + (Real.log (Tp + 2)) ^ 3 / (δ * Tp) + 1 / Real.sqrt Tp) := by
      rw [hRT, hL5, hL3]
    have hb : (∫ σ in a..(-1 / 2), G σ) + (∫ σ in (-1 / 2)..2, G σ)
        ≤ 3 * (16 * Cf + 1) * x ^ 2 * L5 / Tp
          + (5 / 2) * x ^ 2 * ((27 * Cs + 1) * L3 / Tp + 9 * Cs * L3 / (δ * Tp)) := by
      linarith [hmid, hstrip]
    exact le_trans hb (le_trans hfin (le_of_eq hgoal))

/-- `psiIntF1 x s` equals the classical Perron kernel `-(ζ'/ζ)(s)·x^s/s` away from `ζ₁ = 0`. -/
private lemma psiIntF1_eq_logDeriv_of_zeta1_ne {x : ℝ} {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hz1 : riemannZeta₁ s ≠ 0) :
    psiIntF1 x s = -(logDeriv riemannZeta s) * ((x : ℂ) ^ s / s) := by
  have h := deriv_zeta_div_zeta_eq s hs1 hz1
  have h2 : logDeriv riemannZeta₁ s = logDeriv riemannZeta s + (s - 1)⁻¹ := by
    dsimp [logDeriv] at h ⊢
    rw [h]
    ring
  unfold psiIntF1
  rw [h2]
  field_simp [hs0, sub_ne_zero.mpr hs1]
  ring

/-- **Left vertical edge bound**: on the line `Re s = -(2N+1)` the tilted kernel is small. -/
theorem tiltIntF_left_edge_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ) (N : ℕ) (Tp : ℝ), 1 ≤ x → 1 ≤ N → 0 < Tp →
      (∫ y in -Tp..Tp,
          ‖tiltIntF x (((-((2 * (N : ℝ)) + 1)) : ℝ) + Complex.I * (y : ℂ))‖)
        ≤ C * x ^ (-(2 * (N : ℝ)) : ℝ) * Tp
            * (Real.log (2 * (N : ℝ) + Tp + 3) + 1) / (N : ℝ) ^ 2 := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := zeta_logDeriv_odd_vertical_le
  refine ⟨(C₁ + 1) / 2, by linarith, fun x N Tp hx hN hTp => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNr : (0 : ℝ) < (N : ℝ) := by linarith
  set a : ℝ := -((2 * (N : ℝ)) + 1) with ha
  have ha3 : a ≤ -3 := by rw [ha]; push_cast; linarith
  have ha0 : a ≤ 0 := by linarith
  set B : ℝ := (C₁ + 1) * x ^ (-(2 * (N : ℝ)) : ℝ)
      * (Real.log (2 * (N : ℝ) + Tp + 3) + 1) / (4 * (N : ℝ) ^ 2) with hB
  have hpt : ∀ y ∈ Set.Icc (-Tp) Tp,
      ‖tiltIntF x ((a : ℂ) + Complex.I * (y : ℂ))‖ ≤ B := by
    intro y hy
    have hyT : |y| ≤ Tp := by
      rw [abs_le]; exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    set s : ℂ := (a : ℂ) + Complex.I * (y : ℂ) with hs
    have hsre : s.re = a := by simp [s]
    have hsim : s.im = y := by simp [s]
    have hs0 : s ≠ 0 := by
      intro hh; have := congrArg Complex.re hh; rw [hsre] at this; simp at this; linarith
    have hs1 : s ≠ 1 := by
      intro hh; have := congrArg Complex.re hh; rw [hsre] at this; simp at this; linarith
    have hz1 : riemannZeta₁ s ≠ 0 := by
      refine (zeta1_ne_zero_iff_zeta_ne_zero hs1).mpr ?_
      intro hζ
      obtain ⟨n, hn⟩ := trivial_zero_of_riemannZeta_eq_zero_of_re_nonpos hζ (by rw [hsre]; linarith)
      have hre' : s.re = -2 * ((n : ℝ) + 1) := by rw [hn]; simp
      rw [hsre, ha] at hre'
      have h2 : 2 * (N : ℝ) = 2 * (n : ℝ) + 1 := by linarith [hre']
      have h3 : 2 * N = 2 * n + 1 := by exact_mod_cast h2
      omega
    have hsp1 : s + 1 ≠ 0 := by
      intro hh
      have hh2 : (s + 1).re = a + 1 := by simp [s]
      have := congrArg Complex.re hh
      simp only [Complex.zero_re] at this
      rw [hh2] at this; linarith
    have hzeta : ‖logDeriv riemannZeta s‖
        ≤ C₁ * (Real.log (2 * (N : ℝ) + |y| + 3) + 1) := by
      have h := hC₁ N y
      have harg : (((-((2 * (N : ℝ)) + 1)) : ℝ) : ℂ) + Complex.I * (y : ℂ) = s := by
        rw [hs, ha]
      rw [harg] at h
      exact h
    have hsT : 2 * (N : ℝ) ≤ ‖s + 1‖ := by
      have h := Complex.abs_re_le_norm (s + 1)
      have h2 : (s + 1).re = a + 1 := by simp [s]
      rw [h2] at h
      have h3 : |a + 1| = 2 * (N : ℝ) := by
        rw [ha]
        have h4 : -((2 * (N : ℝ)) + 1) + 1 = -(2 * (N : ℝ)) := by ring
        rw [h4, abs_neg, abs_of_nonneg (by linarith)]
      linarith [h3.symm.le, h]
    have hsN : 2 * (N : ℝ) + 1 ≤ ‖s‖ := by
      have h := Complex.abs_re_le_norm s
      rw [hsre] at h
      have h3 : |a| = 2 * (N : ℝ) + 1 := by rw [ha, abs_neg, abs_of_nonneg (by linarith)]
      linarith [h3.symm.le, h]
    have hxx : x * x ^ s.re ≤ x ^ (-(2 * (N : ℝ)) : ℝ) := by
      have h1 : x * x ^ s.re = x ^ ((1 : ℝ) + s.re) := by
        rw [Real.rpow_add hx0, Real.rpow_one]
      rw [h1, hsre, ha]
      rw [show (1 : ℝ) + -((2 * (N : ℝ)) + 1) = -(2 * (N : ℝ)) by ring]
    have hnorm_eq : ‖tiltIntF x s‖
        = ‖logDeriv riemannZeta s‖ * (x * x ^ s.re / (‖s‖ * ‖s + 1‖)) := by
      rw [tiltIntF_apply, psiIntF1_eq_logDeriv_of_zeta1_ne hs0 hs1 hz1]
      simp only [norm_div, norm_mul, norm_neg]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      rw [show ‖(x : ℂ)‖ = x by simp [Real.norm_eq_abs, abs_of_nonneg hx0.le]]
      ring
    have hdenpos : 0 < ‖s‖ * ‖s + 1‖ := by
      refine mul_pos ?_ ?_
      · linarith
      · linarith
    have hden2 : (4 : ℝ) * (N : ℝ) ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
      have h1 : (2 * (N : ℝ) + 1) * (2 * (N : ℝ)) ≤ ‖s‖ * ‖s + 1‖ :=
        mul_le_mul hsN hsT (by linarith) (by linarith)
      nlinarith [h1, hNr]
    have hquot : x * x ^ s.re / (‖s‖ * ‖s + 1‖)
        ≤ x ^ (-(2 * (N : ℝ)) : ℝ) / (4 * (N : ℝ) ^ 2) := by
      have hq : (0 : ℝ) < 4 * (N : ℝ) ^ 2 := by positivity
      rw [div_le_div_iff₀ hdenpos hq]
      calc x * x ^ s.re * (4 * (N : ℝ) ^ 2)
          ≤ x ^ (-(2 * (N : ℝ)) : ℝ) * (4 * (N : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hxx (by positivity)
        _ ≤ x ^ (-(2 * (N : ℝ)) : ℝ) * (‖s‖ * ‖s + 1‖) :=
            mul_le_mul_of_nonneg_left hden2 (Real.rpow_nonneg hx0.le _)
    have hzetal : ‖logDeriv riemannZeta s‖
        ≤ (C₁ + 1) * (Real.log (2 * (N : ℝ) + Tp + 3) + 1) := by
      refine le_trans hzeta ?_
      have h2 : Real.log (2 * (N : ℝ) + |y| + 3) + 1
          ≤ Real.log (2 * (N : ℝ) + Tp + 3) + 1 := by
        have h3 : 2 * (N : ℝ) + |y| + 3 ≤ 2 * (N : ℝ) + Tp + 3 := by linarith [hyT]
        have h4 := Real.log_le_log
          (show (0:ℝ) < 2 * (N:ℝ) + |y| + 3 by have := abs_nonneg y; linarith) h3
        linarith
      have h2nn : (0 : ℝ) ≤ Real.log (2 * (N : ℝ) + Tp + 3) + 1 := by
        have := Real.log_nonneg (show (1:ℝ) ≤ 2 * (N:ℝ) + Tp + 3 by linarith); linarith
      calc C₁ * (Real.log (2 * (N : ℝ) + |y| + 3) + 1)
          ≤ C₁ * (Real.log (2 * (N : ℝ) + Tp + 3) + 1) := mul_le_mul_of_nonneg_left h2 hC₁pos.le
        _ ≤ (C₁ + 1) * (Real.log (2 * (N : ℝ) + Tp + 3) + 1) := by nlinarith [h2nn, hC₁pos]
    rw [hnorm_eq, hB]
    have hzetalnn : (0:ℝ) ≤ ‖logDeriv riemannZeta s‖ := norm_nonneg _
    have hnn : (0:ℝ) ≤ (C₁ + 1) * (Real.log (2 * (N : ℝ) + Tp + 3) + 1) := by
      have h2nn : (0 : ℝ) ≤ Real.log (2 * (N : ℝ) + Tp + 3) + 1 := by
        have := Real.log_nonneg (show (1:ℝ) ≤ 2 * (N:ℝ) + Tp + 3 by linarith); linarith
      positivity
    have hcnn : (0:ℝ) ≤ x * x ^ s.re / (‖s‖ * ‖s + 1‖) :=
      div_nonneg (mul_nonneg hx0.le (Real.rpow_nonneg hx0.le _)) hdenpos.le
    have hfinal := mul_le_mul hzetal hquot hcnn hnn
    calc ‖logDeriv riemannZeta s‖ * (x * x ^ s.re / (‖s‖ * ‖s + 1‖))
        ≤ ((C₁ + 1) * (Real.log (2 * (N : ℝ) + Tp + 3) + 1))
            * (x ^ (-(2 * (N : ℝ)) : ℝ) / (4 * (N : ℝ) ^ 2)) := hfinal
      _ = (C₁ + 1) * x ^ (-(2 * (N : ℝ)) : ℝ)
            * (Real.log (2 * (N : ℝ) + Tp + 3) + 1) / (4 * (N : ℝ) ^ 2) := by ring
  have hconst : IntervalIntegrable (fun _ : ℝ => B) volume (-Tp) Tp :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ => B) (Set.uIcc (-Tp) Tp)).intervalIntegrable
  have hcont : ContinuousOn
      (fun y : ℝ => ‖tiltIntF x ((a : ℂ) + Complex.I * (y : ℂ))‖) (Set.uIcc (-Tp) Tp) := by
    intro y hy
    set s : ℂ := (a : ℂ) + Complex.I * (y : ℂ) with hss
    have hsre : s.re = a := by simp [s]
    have hs0 : s ≠ 0 := by
      intro hh; have := congrArg Complex.re hh; rw [hsre] at this; simp at this; linarith
    have hs1 : s ≠ 1 := by
      intro hh; have := congrArg Complex.re hh; rw [hsre] at this; simp at this; linarith
    have hz : riemannZeta₁ s ≠ 0 := by
      refine (zeta1_ne_zero_iff_zeta_ne_zero hs1).mpr ?_
      intro hζ
      obtain ⟨n, hn⟩ := trivial_zero_of_riemannZeta_eq_zero_of_re_nonpos hζ (by rw [hsre]; linarith)
      have hre' : s.re = -2 * ((n : ℝ) + 1) := by rw [hn]; simp
      rw [hsre, ha] at hre'
      have h2 : 2 * (N : ℝ) = 2 * (n : ℝ) + 1 := by linarith [hre']
      have h3 : 2 * N = 2 * n + 1 := by exact_mod_cast h2
      omega
    have hsp1 : s + 1 ≠ 0 := by
      intro hh
      have hh2 : (s + 1).re = a + 1 := by simp [s]
      have := congrArg Complex.re hh
      simp only [Complex.zero_re] at this
      rw [hh2] at this; linarith
    have hca : ContinuousAt (fun s : ℂ => tiltIntF x s) s :=
      continuousAt_tiltIntF hx0 hz hs0 hs1 hsp1
    have hg : ContinuousAt (fun y' : ℝ => ((a : ℂ) + Complex.I * (y' : ℂ))) y :=
      (continuous_const.add (continuous_const.mul continuous_ofReal)).continuousAt
    exact (ContinuousAt.comp_continuousWithinAt
      (f := fun y' : ℝ => ((a : ℂ) + Complex.I * (y' : ℂ))) hca hg.continuousWithinAt).norm
  have hle : -Tp ≤ Tp := by linarith
  have hmono := intervalIntegral.integral_mono_on hle hcont.intervalIntegrable hconst hpt
  have hval : (∫ y in -Tp..Tp, B) = (Tp - (-Tp)) * B := by
    rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
  rw [hval] at hmono
  refine le_trans hmono (le_of_eq ?_)
  rw [hB]
  field_simp
  ring

private lemma log_le_coeff_mul_rpow {y s : ℝ} (hy : 1 ≤ y) (hs : 0 < s) :
    Real.log y ≤ (8 / s) * y ^ (s / 8) := by
  have hy0 : 0 < y := by linarith
  have h := log_le_eight_mul_rpow (Real.one_le_rpow hy hs.le)
  have hlog : Real.log y = (1 / s) * Real.log (y ^ s) := by
    rw [Real.log_rpow hy0]; field_simp
  have hA : (y ^ s) ^ ((1 : ℝ) / 8) = y ^ (s / 8) := by
    rw [← Real.rpow_mul hy0.le]
    congr 1
    ring
  rw [hlog]
  calc (1 / s) * Real.log (y ^ s) ≤ (1 / s) * (8 * (y ^ s) ^ ((1 : ℝ) / 8)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (8 / s) * y ^ (s / 8) := by rw [hA]; ring

/-- `(log y)^k * y^{-a} → 0` made explicit: a threshold beyond which it is `≤ ε`. -/
private lemma exists_T_log_pow_div (C : ℝ) (k : ℕ) (a : ℝ) (ha : 0 < a) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → C * (Real.log (T + 3)) ^ k / T ^ a ≤ ε := by
  have hmain : ∀ y : ℝ, 1 ≤ y → (Real.log y) ^ k ≤ (2 * (k : ℝ) / a) ^ k * y ^ (a / 2) := by
    intro y hy
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [pow_zero, Nat.cast_zero, mul_zero, zero_div, one_mul]
      exact Real.one_le_rpow hy (by positivity)
    · have hk1 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hy0 : 0 < y := by linarith
      have hs : (0 : ℝ) < 4 * a / (k : ℝ) := by positivity
      have hb := log_le_coeff_mul_rpow hy hs
      have hcoef : (8 : ℝ) / (4 * a / (k : ℝ)) = 2 * (k : ℝ) / a := by field_simp; ring
      have hexp : (4 * a / (k : ℝ)) / 8 = a / (2 * (k : ℝ)) := by field_simp; ring
      rw [hcoef, hexp] at hb
      have h2 : (Real.log y) ^ k ≤ ((2 * (k : ℝ) / a) * y ^ (a / (2 * (k : ℝ)))) ^ k :=
        pow_le_pow_left₀ (Real.log_nonneg hy) hb k
      have h3 : ((2 * (k : ℝ) / a) * y ^ (a / (2 * (k : ℝ)))) ^ k
          = (2 * (k : ℝ) / a) ^ k * y ^ (a / 2) := by
        rw [mul_pow]
        congr 1
        have h4 : ((y ^ (a / (2 * (k : ℝ))))) ^ k = (y ^ (a / (2 * (k : ℝ)))) ^ (k : ℝ) := by
          rw [Real.rpow_natCast]
        rw [h4, ← Real.rpow_mul hy0.le]
        rw [show (a / (2 * (k : ℝ))) * (k : ℝ) = a / 2 by field_simp]
      rwa [h3] at h2
  set B : ℝ := C * (2 * (k : ℝ) / a) ^ k * 2 ^ (a / 2) with hBdef
  rcases le_or_gt C 0 with hC | hC
  · refine ⟨1, fun T hT => ?_⟩
    have h1 : C * (Real.log (T + 3)) ^ k ≤ 0 := by
      have h2 : (0 : ℝ) ≤ (Real.log (T + 3)) ^ k :=
        pow_nonneg (Real.log_nonneg (by linarith)) k
      nlinarith
    have h3 : (0 : ℝ) < T ^ a := Real.rpow_pos_of_pos (by linarith) a
    exact le_trans (div_nonpos_of_nonpos_of_nonneg h1 h3.le) hε.le
  · have hBpos : 0 < B := by
      rw [hBdef]
      have h1 : 0 < (2 * (k : ℝ) / a) ^ k := by
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; norm_num
        · have : 0 < 2 * (k : ℝ) / a := by positivity
          exact pow_pos this k
      positivity
    refine ⟨max 3 (max 1 ((B / ε) ^ (2 / a))), fun T hT => ?_⟩
    have hT3 : (3 : ℝ) ≤ T := le_trans (le_max_left _ _) hT
    have hT1 : (1 : ℝ) ≤ T := by linarith
    have hT0 : (0 : ℝ) < T := by linarith
    have hTB : (B / ε) ^ (2 / a) ≤ T :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
    have hpos : (0 : ℝ) < B / ε := div_pos hBpos hε
    have h5 : C * (Real.log (T + 3)) ^ k ≤ B * T ^ (a / 2) := by
      have h2 := hmain (T + 3) (by linarith)
      have h3 : (T + 3) ^ (a / 2) ≤ 2 ^ (a / 2) * T ^ (a / 2) := by
        have h4 : T + 3 ≤ 2 * T := by linarith
        calc (T + 3) ^ (a / 2) ≤ (2 * T) ^ (a / 2) :=
              Real.rpow_le_rpow (by linarith) h4 (by positivity)
          _ = 2 ^ (a / 2) * T ^ (a / 2) := by rw [Real.mul_rpow (by norm_num) (by linarith)]
      rw [hBdef]
      calc C * (Real.log (T + 3)) ^ k ≤ C * ((2 * (k : ℝ) / a) ^ k * (T + 3) ^ (a / 2)) :=
            mul_le_mul_of_nonneg_left h2 hC.le
        _ ≤ C * ((2 * (k : ℝ) / a) ^ k * (2 ^ (a / 2) * T ^ (a / 2))) := by
            refine mul_le_mul_of_nonneg_left ?_ hC.le
            exact mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = C * (2 * (k : ℝ) / a) ^ k * 2 ^ (a / 2) * T ^ (a / 2) := by ring
    have h1 : C * (Real.log (T + 3)) ^ k / T ^ a ≤ B / T ^ (a / 2) := by
      rw [div_le_iff₀ (Real.rpow_pos_of_pos hT0 a)]
      have h9 : B / T ^ (a / 2) * T ^ a = B * T ^ (a / 2) := by
        rw [div_mul_eq_mul_div, mul_div_assoc, ← Real.rpow_sub hT0]
        congr 1
        rw [show a - a / 2 = a / 2 by ring]
      rw [h9]
      exact h5
    refine le_trans h1 ?_
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hT0 (a / 2))]
    have h7 : ((B / ε) ^ (2 / a)) ^ (a / 2) ≤ T ^ (a / 2) :=
      Real.rpow_le_rpow (by positivity) hTB (by positivity)
    have h8 : ((B / ε) ^ (2 / a)) ^ (a / 2) = B / ε := by
      rw [← Real.rpow_mul (le_of_lt hpos), show (2 / a) * (a / 2) = 1 by field_simp, Real.rpow_one]
    rw [h8, div_le_iff₀ hε] at h7
    linarith [h7]

/-- Conjugation symmetry of the tilted kernel. -/
private lemma tiltIntF_conj {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    tiltIntF x (conj s) = conj (tiltIntF x s) := by
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx]
    exact Real.pi_ne_zero.symm
  have hpow : (x : ℂ) ^ (conj s) = conj ((x : ℂ) ^ s) := by
    have h1 := Complex.cpow_conj (x : ℂ) s harg
    rwa [Complex.conj_ofReal] at h1
  have hlog : logDeriv riemannZeta₁ (conj s) = conj (logDeriv riemannZeta₁ s) := by
    rw [logDeriv_apply, logDeriv_apply, deriv_riemannZeta₁_conj, riemannZeta₁_conj]
    rw [map_div₀]
  have hpsi : psiIntF1 x (conj s) = conj (psiIntF1 x s) := by
    unfold psiIntF1
    rw [hlog, hpow]
    simp only [map_div₀, map_mul, map_neg, map_add, map_sub, map_one]
  have hcs : conj s + 1 = conj (s + 1) := by simp
  unfold tiltIntF
  rw [hpsi, hcs]
  simp only [map_div₀, map_mul, Complex.conj_ofReal]

/-- The tilted zero sum converges. -/
private lemma tiltedZeroSum_summable {x : ℝ} (hx : 1 ≤ x) :
    Summable (fun ρ : ℂ => (zeta1Order ρ : ℂ) * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))) := by
  obtain ⟨C, hCpos, hC⟩ := tiltedZeroSum_abs_le
  have hbound : ∀ u : Finset ℂ,
      ∑ ρ ∈ u, ‖(zeta1Order ρ : ℂ) * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖ ≤ C * x ^ 2 := by
    intro u
    have hcongr : ∀ ρ ∈ u, ‖(zeta1Order ρ : ℂ) * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖
        = (if riemannZeta₁ ρ = 0 then
            ‖(zeta1Order ρ : ℂ) * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖ else 0) := by
      intro ρ _
      by_cases hc : riemannZeta₁ ρ = 0
      · rw [if_pos hc]
      · rw [if_neg hc]
        have h2 : zeta1Order ρ = 0 := by unfold zeta1Order; rw [dif_neg hc]
        rw [h2]; simp
    rw [Finset.sum_congr rfl hcongr,
      (Finset.sum_filter (fun ρ => riemannZeta₁ ρ = 0)
        (fun ρ => ‖(zeta1Order ρ : ℂ) * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))‖)).symm]
    exact hC x hx _ (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
  exact Summable.of_norm (summable_of_sum_le (fun ρ => norm_nonneg _) hbound)

/-- Zeros of `ζ₁` outside the rectangle `[a,2] × [-Tp,Tp]` have large modulus. -/
private lemma zero_notin_rect_norm_ge {R a Tp : ℝ} (hR : 0 ≤ R) (ha : a ≤ -1)
    (hTp : 0 < Tp) (hRbig : Tp ≤ R) :
    ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ ∉ zRectZeros hR a 2 Tp → min Tp (-a) ≤ ‖ρ‖ := by
  intro ρ hz hnot
  by_cases h : Tp ≤ ‖ρ‖
  · exact le_trans (min_le_left _ _) h
  · rw [not_le] at h
    have hmem : ρ ∈ zetaZeroBallFin R hR := by
      rw [zetaZeroBallFin_spec]
      refine ⟨?_, hz⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    have him : |ρ.im| < Tp := lt_of_le_of_lt (Complex.abs_im_le_norm ρ) h
    rw [abs_lt] at him
    have hnotin : ¬ RectInside (zRect a Tp) (wRect 2 Tp) ρ := by
      intro hri
      exact hnot (by rw [zRectZeros, memS_zetaZeroRectFin]; exact ⟨hmem, hri⟩)
    have hre : ρ.re ≤ a ∨ 2 ≤ ρ.re := by
      by_contra hc
      push_neg at hc
      exact hnotin (by
        simp only [RectInside, zRect_re, wRect_re, zRect_im, wRect_im]
        exact ⟨hc.1, hc.2, him.1, him.2⟩)
    rcases hre with hre | hre
    · have h1 : -a ≤ ‖ρ‖ := by
        have h2 := Complex.abs_re_le_norm ρ
        rw [abs_le] at h2
        linarith [h2.1]
      exact le_trans (min_le_right _ _) h1
    · have hle1 : ρ.re ≤ 1 := zeta1_zero_re_le_one hz
      linarith

/-- The `1/(1+‖ρ‖²)`-weighted sum over the zeros of `ζ₁` outside a finite set `Z`. -/
private lemma zeroSum_compl_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : Finset ℂ), (∀ ρ ∈ Z, riemannZeta₁ ρ = 0) →
      ∀ T : ℝ, 2 ≤ T → (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ ∉ Z → T ≤ ‖ρ‖) →
      (∑' ρ : {ρ : ℂ // ρ ∉ Z}, (zeta1Order (ρ : ℂ) : ℝ) / (1 + ‖(ρ : ℂ)‖ ^ 2))
        ≤ C * (Real.log (T + 2) + 1) / T := by
  obtain ⟨C, hCpos, hC⟩ := zeroSum_inv_sq_tail_le
  refine ⟨C, hCpos, fun Z _ T hT hge => ?_⟩
  have hb : ∀ s : Finset {ρ : ℂ // ρ ∉ Z},
      ∑ i ∈ s, (zeta1Order (i : ℂ) : ℝ) / (1 + ‖(i : ℂ)‖ ^ 2) ≤ C * (Real.log (T + 2) + 1) / T := by
    intro s
    have hcongr : ∀ i ∈ s, (zeta1Order (i : ℂ) : ℝ) / (1 + ‖(i : ℂ)‖ ^ 2)
        = (if riemannZeta₁ (i : ℂ) = 0 then (zeta1Order (i : ℂ) : ℝ) / (1 + ‖(i : ℂ)‖ ^ 2) else 0) := by
      intro i _
      by_cases hc : riemannZeta₁ (i : ℂ) = 0
      · rw [if_pos hc]
      · rw [if_neg hc]
        have h2 : zeta1Order (i : ℂ) = 0 := by unfold zeta1Order; rw [dif_neg hc]
        rw [h2]; simp
    rw [Finset.sum_congr rfl hcongr,
      (Finset.sum_filter (s := s) (fun i : {ρ : ℂ // ρ ∉ Z} => riemannZeta₁ (i : ℂ) = 0)
        (fun i => (zeta1Order (i : ℂ) : ℝ) / (1 + ‖(i : ℂ)‖ ^ 2))).symm]
    set S : Finset ℂ := (s.filter (fun i : {ρ : ℂ // ρ ∉ Z} => riemannZeta₁ (i : ℂ) = 0)).image
      Subtype.val with hSdef
    have hinj : Set.InjOn (Subtype.val : {ρ : ℂ // ρ ∉ Z} → ℂ)
        ↑(s.filter (fun i : {ρ : ℂ // ρ ∉ Z} => riemannZeta₁ (i : ℂ) = 0)) := by
      intro a _ b _ hab
      exact Subtype.ext hab
    have hsum : ∑ i ∈ s.filter (fun i : {ρ : ℂ // ρ ∉ Z} => riemannZeta₁ (i : ℂ) = 0),
        (zeta1Order (i : ℂ) : ℝ) / (1 + ‖(i : ℂ)‖ ^ 2)
        = ∑ ρ ∈ S, (zeta1Order ρ : ℝ) / (1 + ‖ρ‖ ^ 2) := by
      rw [hSdef]
      exact (Finset.sum_image (f := fun ρ : ℂ => (zeta1Order ρ : ℝ) / (1 + ‖ρ‖ ^ 2))
        (g := Subtype.val) hinj).symm
    rw [hsum]
    have hzS : ∀ ρ ∈ S, riemannZeta₁ ρ = 0 := by
      intro ρ hρ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hρ
      exact (Finset.mem_filter.mp hi).2
    have hgeS : ∀ ρ ∈ S, T ≤ ‖ρ‖ := by
      intro ρ hρ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hρ
      exact hge i (Finset.mem_filter.mp hi).2 i.2
    have h1 := hC S hzS T hT
    rwa [Finset.filter_true_of_mem hgeS] at h1
  have hs := summable_of_sum_le (fun i : {ρ : ℂ // ρ ∉ Z} => by positivity) hb
  exact Summable.tsum_le_of_sum_le hs hb

/-- The two horizontal edge integrals have the same norm. -/
private lemma horizEdge_norm_eq {x a Tp : ℝ} (hx : 0 ≤ x) :
    (∫ σ in a..2, ‖tiltIntF x ((σ : ℂ) + ((-Tp : ℝ) : ℂ) * Complex.I)‖)
      = (∫ σ in a..2, ‖tiltIntF x ((σ : ℂ) + (Tp : ℂ) * Complex.I)‖) := by
  apply intervalIntegral.integral_congr
  intro σ _
  show ‖tiltIntF x ((σ : ℂ) + ((-Tp : ℝ) : ℂ) * Complex.I)‖ = ‖tiltIntF x ((σ : ℂ) + (Tp : ℂ) * Complex.I)‖
  have h1 : (σ : ℂ) + ((-Tp : ℝ) : ℂ) * Complex.I = conj ((σ : ℂ) + (Tp : ℂ) * Complex.I) := by
    simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [h1, tiltIntF_conj hx]
  simp

private lemma zero_notin_rect_norm_ge' {R a Tp : ℝ} (hR : 0 ≤ R) (ha : a ≤ -1)
    (hTp : 0 < Tp) (hRbig : Tp ≤ R) (haTp : Tp ≤ -a) {ρ : ℂ} (hz : riemannZeta₁ ρ = 0)
    (hnot : ρ ∉ zRectZeros hR a 2 Tp) : Tp ≤ ‖ρ‖ := by
  have h := zero_notin_rect_norm_ge hR ha hTp hRbig ρ hz hnot
  have h2 : min Tp (-a) = Tp := min_eq_left haTp
  rwa [h2] at h

private lemma blk_le_of_mem_closedContourRect {a Tp : ℝ} (ha : a ≤ -2) (hTp : 0 < Tp) {s : ℂ}
    (hs : s ∈ closedContourRect a 2 Tp) : ‖s‖ ≤ |a| + Tp := by
  rw [closedContourRect] at hs
  rw [Complex.mem_reProdIm] at hs
  obtain ⟨h1, h2⟩ := hs
  rw [Set.uIcc_of_le (by linarith : a ≤ 2)] at h1
  rw [Set.uIcc_of_le (by linarith : -Tp ≤ Tp)] at h2
  have habs : |a| = -a := abs_of_neg (by linarith)
  have hre : |s.re| ≤ -a := by
    rw [abs_le]; exact ⟨by linarith [h1.1], by linarith [h1.2, ha]⟩
  have him : |s.im| ≤ Tp := by rw [abs_le]; exact ⟨h2.1, h2.2⟩
  calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    _ ≤ -a + Tp := by linarith
    _ = |a| + Tp := by rw [habs]



/-! ## Glue lemmas for the final assembly -/

/-- On the vertical line `Re s = -(2N+1)` (`N ≥ 1`) the function `ζ₁` does not vanish. -/
private lemma zeta1_ne_zero_of_re_neg_odd {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs : s.re = -((2 * (N : ℝ)) + 1)) : riemannZeta₁ s ≠ 0 := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hs1 : s ≠ 1 := by
    intro hh
    have h := congrArg Complex.re hh
    rw [hs] at h
    simp only [Complex.one_re] at h
    linarith
  refine (zeta1_ne_zero_iff_zeta_ne_zero hs1).mpr ?_
  intro hζ
  have hre0 : s.re ≤ 0 := by rw [hs]; linarith
  obtain ⟨n, hn⟩ := trivial_zero_of_riemannZeta_eq_zero_of_re_nonpos hζ hre0
  have hre' : s.re = -2 * ((n : ℝ) + 1) := by rw [hn]; simp
  rw [hs] at hre'
  have h2 : 2 * (N : ℝ) = 2 * (n : ℝ) + 1 := by linarith
  have h3 : 2 * N = 2 * n + 1 := by exact_mod_cast h2
  omega

/-- Finite-sum form of the complement tail bound (`zeroSum_compl_le` with `Finset` instead of
`tsum`): the `1/(1+‖ρ‖²)`-weighted sum over zeros of `ζ₁` outside `Z` and of modulus `≥ T`. -/
private lemma subtype_zeroSum_finset_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : Finset ℂ), (∀ ρ ∈ Z, riemannZeta₁ ρ = 0) →
      ∀ T : ℝ, 2 ≤ T → (∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ ∉ Z → T ≤ ‖ρ‖) →
      ∀ s : Finset {ρ : ℂ // ρ ∉ Z},
        ∑ i ∈ s, (zeta1Order (i : ℂ) : ℝ) / (1 + ‖(i : ℂ)‖ ^ 2)
          ≤ C * (Real.log (T + 2) + 1) / T := by
  obtain ⟨C, hCpos, hC⟩ := zeroSum_inv_sq_tail_le
  refine ⟨C, hCpos, fun Z _ T hT hge s => ?_⟩
  classical
  have hcongr : ∀ i ∈ s, (zeta1Order (i : ℂ) : ℝ) / (1 + ‖(i : ℂ)‖ ^ 2)
      = (if riemannZeta₁ (i : ℂ) = 0 then
          (zeta1Order (i : ℂ) : ℝ) / (1 + ‖(i : ℂ)‖ ^ 2) else 0) := by
    intro i _
    by_cases hc : riemannZeta₁ (i : ℂ) = 0
    · rw [if_pos hc]
    · rw [if_neg hc]
      have h2 : zeta1Order (i : ℂ) = 0 := by unfold zeta1Order; rw [dif_neg hc]
      rw [h2]; simp
  rw [Finset.sum_congr rfl hcongr,
    (Finset.sum_filter (s := s) (fun i : {ρ : ℂ // ρ ∉ Z} => riemannZeta₁ (i : ℂ) = 0)
      (fun i => (zeta1Order (i : ℂ) : ℝ) / (1 + ‖(i : ℂ)‖ ^ 2))).symm]
  set S : Finset ℂ := (s.filter (fun i : {ρ : ℂ // ρ ∉ Z} => riemannZeta₁ (i : ℂ) = 0)).image
    Subtype.val with hSdef
  have hinj : Set.InjOn (Subtype.val : {ρ : ℂ // ρ ∉ Z} → ℂ)
      ↑(s.filter (fun i : {ρ : ℂ // ρ ∉ Z} => riemannZeta₁ (i : ℂ) = 0)) := by
    intro a _ b _ hab
    exact Subtype.ext hab
  have hsum : ∑ i ∈ s.filter (fun i : {ρ : ℂ // ρ ∉ Z} => riemannZeta₁ (i : ℂ) = 0),
      (zeta1Order (i : ℂ) : ℝ) / (1 + ‖(i : ℂ)‖ ^ 2)
      = ∑ ρ ∈ S, (zeta1Order ρ : ℝ) / (1 + ‖ρ‖ ^ 2) := by
    rw [hSdef]
    exact (Finset.sum_image (f := fun ρ : ℂ => (zeta1Order ρ : ℝ) / (1 + ‖ρ‖ ^ 2))
      (g := Subtype.val) hinj).symm
  rw [hsum]
  have hzS : ∀ ρ ∈ S, riemannZeta₁ ρ = 0 := by
    intro ρ hρ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hρ
    exact (Finset.mem_filter.mp hi).2
  have hgeS : ∀ ρ ∈ S, T ≤ ‖ρ‖ := by
    intro ρ hρ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hρ
    exact hge i (Finset.mem_filter.mp hi).2 i.2
  have h1 := hC S hzS T hT
  rwa [Finset.filter_true_of_mem hgeS] at h1


lemma log_shift_le_two {x T Tp : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ T) (hTp : Tp ≤ T + 1)
    (hTp0 : 0 ≤ Tp) (hT : 5 ≤ T) : Real.log (x + Tp + 2) ≤ 2 * Real.log (T + 3) := by
  have hlog5 : Real.log 5 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hle : x + Tp + 2 ≤ 5 * T := by linarith
  have hpos : (0:ℝ) < x + Tp + 2 := by linarith
  calc Real.log (x + Tp + 2) ≤ Real.log (5 * T) := Real.log_le_log hpos hle
    _ = Real.log 5 + Real.log T := Real.log_mul (by norm_num) (by linarith)
    _ ≤ Real.log T + Real.log T := by linarith
    _ = 2 * Real.log T := by ring
    _ ≤ 2 * Real.log (T + 3) := by
        have h := Real.log_le_log (by linarith : (0:ℝ) < T) (by linarith : T ≤ T + 3)
        linarith

lemma log_odd_le_three {T Tp N : ℝ} (hN0 : 0 ≤ N) (hTp0 : 0 < Tp) (hNlt : N < Tp / 2 + 1)
    (hTpLe : Tp ≤ T + 1) (hT : 5 ≤ T) :
    Real.log (2 * N + Tp + 3) + 1 ≤ 3 * Real.log (T + 3) := by
  have hle : 2 * N + Tp + 3 ≤ 3 * (T + 3) := by linarith
  have hpos : (0:ℝ) < 2 * N + Tp + 3 := by linarith
  have h1 : Real.log (2 * N + Tp + 3) ≤ Real.log (3 * (T + 3)) := Real.log_le_log hpos hle
  rw [Real.log_mul (by norm_num) (by linarith : (T + 3) ≠ 0)] at h1
  have h2 : Real.log 3 ≤ Real.log (T + 3) := Real.log_le_log (by norm_num) (by linarith)
  have h3 : (1:ℝ) ≤ Real.log (T + 3) := by
    have hexp : Real.exp 1 ≤ T + 3 := by linarith [Real.exp_one_lt_three, Real.exp_pos 1]
    have h4 := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at h4
  linarith

lemma right_edge_arith {Cper x T Tp ε : ℝ} (hCper : 0 ≤ Cper) (hx : 0 ≤ x)
    (hT : 5 ≤ T) (hTp0 : 0 < Tp) (hxT : x ≤ T) (hTleTp : T ≤ Tp) (hTpLe : Tp ≤ T + 1)
    (hTa : 8 * Cper * x * (Real.log (T + 3)) ^ 3 / T ≤ ε) :
    Cper * x * (Real.log (x + Tp + 2)) ^ 3 / Tp ≤ ε := by
  have hT0 : (0:ℝ) < T := by linarith
  have hlogx : Real.log (x + Tp + 2) ≤ 2 * Real.log (T + 3) :=
    log_shift_le_two hx hxT hTpLe hTp0.le hT
  have hlog0 : (0:ℝ) ≤ Real.log (x + Tp + 2) := Real.log_nonneg (by linarith)
  have hcube : (Real.log (x + Tp + 2)) ^ 3 ≤ 8 * (Real.log (T + 3)) ^ 3 := by
    have h := pow_le_pow_left₀ hlog0 hlogx 3
    calc (Real.log (x + Tp + 2)) ^ 3 ≤ (2 * Real.log (T + 3)) ^ 3 := h
      _ = 8 * (Real.log (T + 3)) ^ 3 := by ring
  have hlog3nn : (0:ℝ) ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have h8cx : (0:ℝ) ≤ 8 * Cper * x * (Real.log (T + 3)) ^ 3 := by positivity
  have hstep : Cper * x * (Real.log (x + Tp + 2)) ^ 3 / Tp
      ≤ 8 * Cper * x * (Real.log (T + 3)) ^ 3 / T := by
    rw [div_le_div_iff₀ hTp0 hT0]
    have hA : Cper * x * (Real.log (x + Tp + 2)) ^ 3 ≤ Cper * x * (8 * (Real.log (T + 3)) ^ 3) :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    have hB : Cper * x * (Real.log (x + Tp + 2)) ^ 3 * T
        ≤ Cper * x * (8 * (Real.log (T + 3)) ^ 3) * T :=
      mul_le_mul_of_nonneg_right hA hT0.le
    have hC : Cper * x * (8 * (Real.log (T + 3)) ^ 3) * T
        ≤ 8 * Cper * x * (Real.log (T + 3)) ^ 3 * Tp := by
      have h2 : Cper * x * (8 * (Real.log (T + 3)) ^ 3) * T
          = 8 * Cper * x * (Real.log (T + 3)) ^ 3 * T := by ring
      rw [h2]
      exact mul_le_mul_of_nonneg_left hTleTp h8cx
    linarith
  linarith

lemma horiz_edge_arith {K1 x T Tp δ cgh ε : ℝ} (hK1 : 0 ≤ K1) (hx : 0 ≤ x)
    (hT : 5 ≤ T) (hTp0 : 0 < Tp) (hTleTp : T ≤ Tp) (hTpLe : Tp ≤ T + 1)
    (hcgh : 0 < cgh) (hδ : δ = cgh / (Real.log T + 1))
    (h1 : K1 * x ^ 2 * (Real.log (T + 3)) ^ 5 / T ≤ ε / 3)
    (h2 : (2 * K1 * x ^ 2 / cgh) * (Real.log (T + 3)) ^ 5 / T ≤ ε / 3)
    (h3 : K1 * x ^ 2 / T ^ (1 / 2 : ℝ) ≤ ε / 3) :
    K1 * x ^ 2 * ((Real.log (Tp + 2)) ^ 5 / Tp + (Real.log (Tp + 2)) ^ 3 / (δ * Tp)
        + 1 / Real.sqrt Tp) ≤ ε := by
  have hT0 : (0:ℝ) < T := by linarith
  have hlog3_1 : (1:ℝ) ≤ Real.log (T + 3) := by
    have hexp : Real.exp 1 ≤ T + 3 := by linarith [Real.exp_one_lt_three, Real.exp_pos 1]
    have h4 := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at h4
  have hlog3_0 : (0:ℝ) ≤ Real.log (T + 3) := by linarith
  have hlogTp_le : Real.log (Tp + 2) ≤ Real.log (T + 3) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlogTp0 : (0:ℝ) ≤ Real.log (Tp + 2) := Real.log_nonneg (by linarith)
  have hlogT1 : (0:ℝ) < Real.log T + 1 := by
    have := Real.log_nonneg (by linarith : (1:ℝ) ≤ T); linarith
  have hp1 : (Real.log (Tp + 2)) ^ 5 / Tp ≤ (Real.log (T + 3)) ^ 5 / T := by
    rw [div_le_div_iff₀ hTp0 hT0]
    exact mul_le_mul (pow_le_pow_left₀ hlogTp0 hlogTp_le 5) hTleTp hT0.le (by positivity)
  have hlogTp3 : (Real.log (Tp + 2)) ^ 3 ≤ (Real.log (T + 3)) ^ 3 :=
    pow_le_pow_left₀ hlogTp0 hlogTp_le 3
  have hlogT1le : Real.log T + 1 ≤ 2 * Real.log (T + 3) := by
    have h := Real.log_le_log (by linarith : (0:ℝ) < T) (by linarith : T ≤ T + 3)
    linarith
  have hnum : (Real.log (Tp + 2)) ^ 3 * (Real.log T + 1)
      ≤ (Real.log (T + 3)) ^ 3 * (2 * Real.log (T + 3)) :=
    mul_le_mul hlogTp3 hlogT1le (by linarith) (by positivity)
  have hp2a : (Real.log (Tp + 2)) ^ 3 / (δ * Tp)
      ≤ (2 / cgh) * (Real.log (T + 3)) ^ 4 / T := by
    rw [hδ]
    have hEq : (Real.log (Tp + 2)) ^ 3 / (cgh / (Real.log T + 1) * Tp)
        = (Real.log (Tp + 2)) ^ 3 * (Real.log T + 1) / (cgh * Tp) := by
      field_simp
    rw [hEq]
    have hstep1 : (Real.log (Tp + 2)) ^ 3 * (Real.log T + 1) / (cgh * Tp)
        ≤ (Real.log (T + 3)) ^ 3 * (2 * Real.log (T + 3)) / (cgh * Tp) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    have hstep2 : (Real.log (T + 3)) ^ 3 * (2 * Real.log (T + 3)) / (cgh * Tp)
        ≤ (Real.log (T + 3)) ^ 3 * (2 * Real.log (T + 3)) / (cgh * T) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hTleTp hcgh.le)
    have hstep3 : (Real.log (T + 3)) ^ 3 * (2 * Real.log (T + 3)) / (cgh * T)
        = (2 / cgh) * (Real.log (T + 3)) ^ 4 / T := by
      field_simp
    linarith
  have h45 : (Real.log (T + 3)) ^ 4 ≤ (Real.log (T + 3)) ^ 5 := by
    have hpow : (Real.log (T + 3)) ^ 5 = (Real.log (T + 3)) ^ 4 * Real.log (T + 3) := by ring
    rw [hpow]
    have h4nn : (0:ℝ) ≤ (Real.log (T + 3)) ^ 4 := by positivity
    nlinarith [hlog3_1, h4nn]
  have hp2 : (Real.log (Tp + 2)) ^ 3 / (δ * Tp) ≤ (2 / cgh) * (Real.log (T + 3)) ^ 5 / T := by
    refine le_trans hp2a ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h45 (by positivity)) hT0.le
  have hp3 : 1 / Real.sqrt Tp ≤ 1 / T ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hT0 _)
      (Real.rpow_le_rpow hT0.le hTleTp (by norm_num))
  have hsum : (Real.log (Tp + 2)) ^ 5 / Tp + (Real.log (Tp + 2)) ^ 3 / (δ * Tp)
      + 1 / Real.sqrt Tp
      ≤ (Real.log (T + 3)) ^ 5 / T + (2 / cgh) * (Real.log (T + 3)) ^ 5 / T
        + 1 / T ^ (1 / 2 : ℝ) := by
    linarith
  have hfin : K1 * x ^ 2 * ((Real.log (Tp + 2)) ^ 5 / Tp + (Real.log (Tp + 2)) ^ 3 / (δ * Tp)
        + 1 / Real.sqrt Tp)
      ≤ K1 * x ^ 2 * ((Real.log (T + 3)) ^ 5 / T + (2 / cgh) * (Real.log (T + 3)) ^ 5 / T
        + 1 / T ^ (1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have hexp : K1 * x ^ 2 * ((Real.log (T + 3)) ^ 5 / T + (2 / cgh) * (Real.log (T + 3)) ^ 5 / T
        + 1 / T ^ (1 / 2 : ℝ))
      = K1 * x ^ 2 * (Real.log (T + 3)) ^ 5 / T
        + (2 * K1 * x ^ 2 / cgh) * (Real.log (T + 3)) ^ 5 / T
        + K1 * x ^ 2 / T ^ (1 / 2 : ℝ) := by
    field_simp
  rw [hexp] at hfin
  linarith

lemma left_edge_arith {Cn x T Tp ε : ℝ} {N : ℕ} (hCn : 0 ≤ Cn) (hx : 1 ≤ x)
    (hN : 1 ≤ N) (hT : 5 ≤ T) (hTp0 : 0 < Tp) (hTleTp : T ≤ Tp)
    (hTpLe : Tp ≤ T + 1) (hNr : Tp / 2 ≤ (N : ℝ)) (hNlt : (N : ℝ) < Tp / 2 + 1)
    (hTe : 12 * Cn * Real.log (T + 3) / T ≤ ε) :
    Cn * x ^ (-(2 * (N : ℝ)) : ℝ) * Tp * (Real.log (2 * (N : ℝ) + Tp + 3) + 1) / (N : ℝ) ^ 2
      ≤ ε := by
  have hT0 : (0:ℝ) < T := by linarith
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (0:ℝ) < (N : ℝ) ^ 2 := by positivity
  have hlog3nn : (0:ℝ) ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have hxk : x ^ (-(2 * (N : ℝ)) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  have hL : Real.log (2 * (N : ℝ) + Tp + 3) + 1 ≤ 3 * Real.log (T + 3) :=
    log_odd_le_three (by positivity) hTp0 hNlt hTpLe hT
  have hLnn : (0:ℝ) ≤ Real.log (2 * (N : ℝ) + Tp + 3) + 1 := by
    have h := Real.log_nonneg (show (1:ℝ) ≤ 2 * (N : ℝ) + Tp + 3 by
      have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
      linarith)
    linarith
  have hq : Tp / (N : ℝ) ^ 2 ≤ 4 / Tp := by
    rw [div_le_div_iff₀ hN2 hTp0]
    nlinarith [hNr, hTp0, hNpos]
  have hq2 : 4 / Tp ≤ 4 / T :=
    div_le_div₀ (by norm_num) (by norm_num) hT0 hTleTp
  have hEq : Cn * x ^ (-(2 * (N : ℝ)) : ℝ) * Tp
        * (Real.log (2 * (N : ℝ) + Tp + 3) + 1) / (N : ℝ) ^ 2
      = Cn * x ^ (-(2 * (N : ℝ)) : ℝ) * (Real.log (2 * (N : ℝ) + Tp + 3) + 1)
        * (Tp / (N : ℝ) ^ 2) := by
    field_simp
  rw [hEq]
  have hA : Cn * x ^ (-(2 * (N : ℝ)) : ℝ) ≤ Cn * 1 :=
    mul_le_mul_of_nonneg_left hxk hCn
  have hB : Cn * x ^ (-(2 * (N : ℝ)) : ℝ) * (Real.log (2 * (N : ℝ) + Tp + 3) + 1)
      ≤ Cn * 1 * (3 * Real.log (T + 3)) :=
    mul_le_mul hA hL hLnn (by positivity)
  have hq3 : Tp / (N : ℝ) ^ 2 ≤ 4 / T := le_trans hq hq2
  have hC : Cn * x ^ (-(2 * (N : ℝ)) : ℝ) * (Real.log (2 * (N : ℝ) + Tp + 3) + 1)
        * (Tp / (N : ℝ) ^ 2)
      ≤ Cn * 1 * (3 * Real.log (T + 3)) * (4 / T) :=
    mul_le_mul hB hq3 (by positivity) (by positivity)
  have hD : Cn * 1 * (3 * Real.log (T + 3)) * (4 / T) = 12 * Cn * Real.log (T + 3) / T := by
    field_simp
    ring
  linarith

lemma tail_arith {C x T Tp ε : ℝ} (hC : 0 ≤ C) (hx : 0 ≤ x) (hT : 5 ≤ T)
    (hTp0 : 0 < Tp) (hTleTp : T ≤ Tp) (hTpLe : Tp ≤ T + 1)
    (hTf : 8 * x ^ 2 * C * Real.log (T + 3) / T ≤ ε) :
    4 * x ^ 2 * (C * (Real.log (Tp + 2) + 1) / Tp) ≤ ε := by
  have hT0 : (0:ℝ) < T := by linarith
  have hlog1 : (1:ℝ) ≤ Real.log (T + 3) := by
    have hexp : Real.exp 1 ≤ T + 3 := by linarith [Real.exp_one_lt_three, Real.exp_pos 1]
    have h4 := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at h4
  have hlogTp : Real.log (Tp + 2) ≤ Real.log (T + 3) :=
    Real.log_le_log (by linarith) (by linarith)
  have hstep : C * (Real.log (Tp + 2) + 1) / Tp ≤ 2 * C * Real.log (T + 3) / T := by
    rw [div_le_div_iff₀ hTp0 hT0]
    have hnum : C * (Real.log (Tp + 2) + 1) ≤ C * (2 * Real.log (T + 3)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC
    calc C * (Real.log (Tp + 2) + 1) * T ≤ C * (2 * Real.log (T + 3)) * T :=
          mul_le_mul_of_nonneg_right hnum hT0.le
      _ ≤ 2 * C * Real.log (T + 3) * Tp := by
          have h2 : C * (2 * Real.log (T + 3)) * T = 2 * C * Real.log (T + 3) * T := by ring
          rw [h2]
          exact mul_le_mul_of_nonneg_left hTleTp (by positivity)
  have hfin : 4 * x ^ 2 * (C * (Real.log (Tp + 2) + 1) / Tp)
      ≤ 4 * x ^ 2 * (2 * C * Real.log (T + 3) / T) :=
    mul_le_mul_of_nonneg_left hstep (by positivity)
  have hexp : 4 * x ^ 2 * (2 * C * Real.log (T + 3) / T)
      = 8 * x ^ 2 * C * Real.log (T + 3) / T := by
    field_simp
    ring
  linarith
/-- The right-edge integral of the tilted kernel is the classical Riesz–Perron integrand. -/
private lemma edgeR_tiltIntF_perron {x Tp : ℝ} (hx : 0 < x) :
    edgeR 2 Tp (tiltIntF x) =
      ∫ y in -Tp..Tp, (-(deriv riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ))) /
            riemannZeta ((2 : ℂ) + Complex.I * (y : ℂ)))
          * (x : ℂ) ^ ((2 : ℂ) + Complex.I * (y : ℂ) + 1)
          / (((2 : ℂ) + Complex.I * (y : ℂ)) *
              ((2 : ℂ) + Complex.I * (y : ℂ) + 1)) := by
  unfold edgeR
  rw [wRect_re]
  apply intervalIntegral.integral_congr
  intro y _
  have harg : (((2 : ℝ)) : ℂ) + (y : ℂ) * Complex.I
      = ((2 : ℂ) + Complex.I * (y : ℂ)) := by push_cast; ring
  simp only [harg, tiltIntF_two_add hx y]

/-- Norm bound for the bottom edge in terms of the top line `Im s = Tp`. -/
private lemma norm_edgeB_tiltIntF_le {x a Tp : ℝ} (hx : 1 ≤ x) (ha : a ≤ 2) :
    ‖edgeB a 2 Tp (tiltIntF x)‖
      ≤ ∫ σ in a..2, ‖tiltIntF x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖ := by
  have h1 : ‖edgeB a 2 Tp (tiltIntF x)‖
      ≤ ∫ σ in a..2, ‖tiltIntF x ((σ : ℂ) + ((-Tp : ℝ) : ℂ) * Complex.I)‖ := by
    unfold edgeB
    rw [zRect_im]
    exact intervalIntegral.norm_integral_le_integral_norm ha
  rw [horizEdge_norm_eq (x := x) (a := a) (Tp := Tp) (by linarith)] at h1
  refine le_trans h1 (le_of_eq ?_)
  apply intervalIntegral.integral_congr
  intro σ _
  have harg : ((σ : ℂ) + (Tp : ℂ) * Complex.I) = ((σ : ℂ) + Complex.I * (Tp : ℂ)) := by ring
  simp only [harg]

/-- Norm bound for the top edge. -/
private lemma norm_edgeT_tiltIntF_le {x a Tp : ℝ} (ha : a ≤ 2) :
    ‖edgeT a 2 Tp (tiltIntF x)‖
      ≤ ∫ σ in a..2, ‖tiltIntF x ((σ : ℂ) + Complex.I * (Tp : ℂ))‖ := by
  unfold edgeT
  rw [wRect_im]
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm ha) (le_of_eq ?_)
  apply intervalIntegral.integral_congr
  intro σ _
  have harg : ((σ : ℂ) + (Tp : ℂ) * Complex.I) = ((σ : ℂ) + Complex.I * (Tp : ℂ)) := by ring
  simp only [harg]

/-- Norm bound for the left edge. -/
private lemma norm_edgeL_tiltIntF_le {x a Tp : ℝ} (hTp : 0 ≤ Tp) :
    ‖edgeL a Tp (tiltIntF x)‖
      ≤ ∫ y in -Tp..Tp, ‖tiltIntF x ((a : ℂ) + Complex.I * (y : ℂ))‖ := by
  unfold edgeL
  rw [zRect_re]
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by linarith)) (le_of_eq ?_)
  apply intervalIntegral.integral_congr
  intro y _
  have harg : ((a : ℂ) + (y : ℂ) * Complex.I) = ((a : ℂ) + Complex.I * (y : ℂ)) := by ring
  simp only [harg]

/-!
# The tilted explicit formula

This file proves `psiIntegral_tilted_explicit`: under `RiemannHypothesis`, for `x ≥ 1`,

    ∫_0^x ψ = x²/2 - x·log(2π) + (log(2π) - 1 + γ) + Σ_n Λ(n)/n²
              - Σ_ρ m_ρ·x^(ρ+1)/(ρ(ρ+1)).

Here `ψ` is the Chebyshev function, `Λ` the von Mangoldt function and the last sum runs over
the nontrivial zeros `ρ` of `ζ`, weighted by their multiplicities `m_ρ = zeta1Order ρ`.

The proof is a contour-integral argument:

* `tiltIntF x s = x·ψIntF1 x s/(s+1) = -(ζ'/ζ)(s)·x^(s+1)/(s(s+1))` is the tilted
  (Riesz–Perron) kernel; on `Re s = 2` it is the classical Riesz–Perron integrand
  (`tiltIntF_two_add`), whose truncated integral differs from `∫_0^x ψ` by
  `O(x log³(x+T)/T)` (`psiIntegral_perron_bound`).
* `rectInt_tiltIntF_engineSum` is the residue theorem on the rectangle
  `[a,2] × [-Tp,Tp]`: the boundary integral equals `2πi` times the model sum, whose terms
  are the constants of the explicit formula, the `Λ`-series at `2` (through
  `logDeriv_riemannZeta_neg_one`) and the interior zeros.
* `rectInt_decompose` splits that into the four oriented edges `edgeB, edgeT, edgeR, edgeL`;
  solving for `edgeR` expresses the Perron integral in terms of the model sum plus the other
  three edges.
* The horizontal edges are controlled by `tiltIntF_horiz_integral_bound` (Good-height bounds
  for `ζ'/ζ` inside the critical strip), the left edge by `tiltIntF_left_edge_bound`
  (trivial zeros / functional equation on the odd negative integers), and the missing tail
  `Σ_ρ ∉ Z` by `zeta1_zero_tilted_term_le` plus the zero-density tail bounds.

Everything is assembled with an `ε`-argument; the six thresholds are produced by
`exists_T_log_pow_div`.
-/


theorem psiIntegral_tilted_explicit (h : RiemannHypothesis) :
    ∀ x : ℝ, 1 ≤ x →
      (∫ t in (0 : ℝ)..x, (Chebyshev.psi t : ℂ))
        = (x : ℂ) ^ 2 / 2 - (x : ℂ) * ((Real.log (2 * Real.pi) : ℝ) : ℂ)
          + ((Real.log (2 * Real.pi) - 1 + Real.eulerMascheroniConstant : ℝ) : ℂ)
          + ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) ^ 2
          - ∑' ρ : ℂ, (Commons.NumberTheory.Zeta.zeta1Order ρ : ℂ) * (x : ℂ) ^ (ρ + 1)
              / (ρ * (ρ + 1)) := by
  intro x hx
  obtain ⟨K1, hK1pos, hK1⟩ := tiltIntF_horiz_integral_bound h
  obtain ⟨Cn, hCnpos, hCn⟩ := tiltIntF_left_edge_bound
  obtain ⟨Cper, hCperpos, hCper⟩ := psiIntegral_perron_bound x hx
  obtain ⟨Cfins, hCfinspos, hCfins⟩ := subtype_zeroSum_finset_le
  obtain ⟨cgh, hcghpos, hcgh⟩ := zeta1_exists_good_height h
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  set S : ℂ := ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (n : ℂ) ^ 2 with hS
  set Z : ℂ := ∑' ρ : ℂ, (zeta1Order ρ : ℂ) * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) with hZ
  set Ahat : ℂ := (x : ℂ) ^ 2 / 2 - (x : ℂ) * ((Real.log (2 * Real.pi) : ℝ) : ℂ)
      + ((Real.log (2 * Real.pi) - 1 + Real.eulerMascheroniConstant : ℝ) : ℂ) + S with hAhat
  have key : ∀ ε : ℝ, 0 < ε →
      ‖(∫ t in (0 : ℝ)..x, (Chebyshev.psi t : ℂ)) - (Ahat - Z)‖ ≤ ε := by
    intro ε hε
    have hε4 : (0 : ℝ) < ε / 4 := by linarith
    have hε12 : (0 : ℝ) < ε / 12 := by linarith
    have hε2 : (0 : ℝ) < ε / 2 := by linarith
    obtain ⟨Ta, hTa⟩ := exists_T_log_pow_div (8 * Cper * x) 3 1 (by norm_num) (ε / 4) hε4
    obtain ⟨Tb, hTb⟩ := exists_T_log_pow_div (K1 * x ^ 2) 5 1 (by norm_num) (ε / 12) hε12
    obtain ⟨Tc, hTc⟩ := exists_T_log_pow_div (2 * K1 * x ^ 2 / cgh) 5 1 (by norm_num) (ε / 12) hε12
    obtain ⟨Td, hTd⟩ := exists_T_log_pow_div (K1 * x ^ 2) 0 (1 / 2) (by norm_num) (ε / 12) hε12
    obtain ⟨Te, hTe⟩ := exists_T_log_pow_div (12 * Cn) 1 1 (by norm_num) (ε / 2) hε2
    obtain ⟨Tf, hTf⟩ := exists_T_log_pow_div (8 * x ^ 2 * Cfins) 1 1 (by norm_num) (ε / 4) hε4
    set Ts : Finset ℝ := {Ta, Tb, Tc, Td, Te, Tf, x, 5} with hTs
    have hTsne : Ts.Nonempty := ⟨x, by simp [hTs]⟩
    set T : ℝ := Ts.max' hTsne with hTmax
    have hTaT : Ta ≤ T := Finset.le_max' Ts Ta (by simp [hTs])
    have hTbT : Tb ≤ T := Finset.le_max' Ts Tb (by simp [hTs])
    have hTcT : Tc ≤ T := Finset.le_max' Ts Tc (by simp [hTs])
    have hTdT : Td ≤ T := Finset.le_max' Ts Td (by simp [hTs])
    have hTeT : Te ≤ T := Finset.le_max' Ts Te (by simp [hTs])
    have hTfT : Tf ≤ T := Finset.le_max' Ts Tf (by simp [hTs])
    have hT5 : 5 ≤ T := Finset.le_max' Ts 5 (by simp [hTs])
    have hxT : x ≤ T := Finset.le_max' Ts x (by simp [hTs])
    have hTpos : (0 : ℝ) < T := by linarith
    obtain ⟨Tp, hTleTp, hTpLe, hgap⟩ := hcgh T hT5
    have hTp5 : 5 ≤ Tp := le_trans hT5 hTleTp
    have hTp0 : (0 : ℝ) < Tp := by linarith
    have hTp2 : 2 ≤ Tp := by linarith
    have hxTp : x ≤ Tp := le_trans hxT hTleTp
    set δ : ℝ := cgh / (Real.log T + 1) with hδ
    have hlogT1pos : (0 : ℝ) < Real.log T + 1 := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T); linarith
    have hδpos : 0 < δ := by rw [hδ]; exact div_pos hcghpos hlogT1pos
    have hgapδ : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → δ ≤ |ρ.im - Tp| := by
      intro ρ hρ; rw [hδ]; exact hgap ρ hρ
    set N : ℕ := ⌈Tp / 2⌉₊ with hN
    have hNr : Tp / 2 ≤ (N : ℝ) := by rw [hN]; exact Nat.le_ceil _
    have hNlt : (N : ℝ) < Tp / 2 + 1 := by
      rw [hN]; exact Nat.ceil_lt_add_one (by linarith)
    have hN1 : 1 ≤ N := by
      have h2 : (2 : ℝ) < (N : ℝ) := by linarith
      have h3 : 2 < N := by exact_mod_cast h2
      omega
    set a : ℝ := -((2 * (N : ℝ)) + 1) with ha
    have ha2 : a ≤ -2 := by rw [ha]; push_cast; linarith
    have ha1 : a < -1 := by linarith
    have haTp : Tp ≤ -a := by rw [ha]; push_cast; linarith
    have ha2' : a ≤ 2 := by linarith
    set R : ℝ := |a| + Tp + 4 with hR
    have hR0 : 0 ≤ R := by rw [hR]; positivity
    have hTpR : Tp ≤ R := by rw [hR]; have := abs_nonneg a; linarith
    set Zc : Finset ℂ := zRectZeros hR0 a 2 Tp with hZc
    have hZczeros : ∀ ρ ∈ Zc, riemannZeta₁ ρ = 0 := fun ρ hρ =>
      zRectZeros_zero hR0 a 2 Tp hρ
    set SZc : ℂ := ∑ ρ ∈ zRectZeros hR0 a 2 Tp,
      (zeta1Order ρ : ℂ) * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) with hSZc
    set F : ℂ → ℂ := fun ρ => (zeta1Order ρ : ℂ) * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) with hF
    have hsumF : Summable F := by rw [hF]; exact tiltedZeroSum_summable hx
    have hZF : Z = ∑' ρ : ℂ, F ρ := by rw [hZ]
    set u : ℂ := 1 / (2 * Real.pi) with hu
    -- engine
    have hrect : closedContourRect a 2 Tp ⊆ Metric.closedBall (0 : ℂ) R := by
      intro s hs
      rw [Metric.mem_closedBall, dist_zero_right]
      refine le_trans (blk_le_of_mem_closedContourRect ha2 hTp0 hs) ?_
      rw [hR]; have := abs_nonneg a; linarith
    have hgood : ∀ ρ : ℂ, riemannZeta₁ ρ = 0 → ρ.im ≠ Tp ∧ ρ.im ≠ -Tp := by
      intro ρ hρ
      refine ⟨?_, ?_⟩
      · intro him
        have h1 := hgapδ ρ hρ
        rw [him, sub_self, abs_zero] at h1
        linarith
      · intro him
        have hconj : riemannZeta₁ (conj ρ) = 0 := by
          rw [riemannZeta₁_conj, hρ, map_zero]
        have h1 := hgapδ (conj ρ) hconj
        simp only [Complex.conj_im, him, neg_neg, sub_self, abs_zero] at h1
        linarith
    have hleft : ∀ s : ℂ, s.re = a → riemannZeta₁ s ≠ 0 := by
      intro s hs
      refine zeta1_ne_zero_of_re_neg_odd hN1 ?_
      rw [hs, ha]
    have hengine := rectInt_tiltIntF_engineSum (R := R) (a := a) (b := 2) (Tp := Tp) (x := x)
      hR0 hx0 ha1 (by norm_num) hTp0 hrect hgood hleft
    have hlog : Complex.log (2 * (Real.pi : ℂ)) = ((Real.log (2 * Real.pi) : ℝ) : ℂ) := by
      rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]
      exact (Complex.ofReal_log (x := 2 * Real.pi) (by positivity)).symm
    have hAeng : Ahat = (x : ℂ) ^ 2 / 2 - (x : ℂ) * Complex.log (2 * (Real.pi : ℂ))
        + logDeriv riemannZeta (-1) := by
      rw [hAhat, hS, hlog, logDeriv_riemannZeta_neg_one]
      ring
    have hengine' : rectInt (zRect a Tp) (wRect 2 Tp) (tiltIntF x)
        = (Ahat - SZc) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
      rw [hengine, hSZc, hAeng]
    have hcomb : edgeB a 2 Tp (tiltIntF x) - edgeT a 2 Tp (tiltIntF x)
        + Complex.I * edgeR 2 Tp (tiltIntF x) - Complex.I * edgeL a Tp (tiltIntF x)
        = (Ahat - SZc) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) := by
      have h1 : edgeB a 2 Tp (tiltIntF x) - edgeT a 2 Tp (tiltIntF x)
          + Complex.I • edgeR 2 Tp (tiltIntF x) - Complex.I • edgeL a Tp (tiltIntF x)
          = rectInt (zRect a Tp) (wRect 2 Tp) (tiltIntF x) :=
        (rectInt_decompose a 2 Tp (tiltIntF x)).symm
      rw [hengine'] at h1
      simpa only [smul_eq_mul] using h1
    have hkeyI : Complex.I * (edgeR 2 Tp (tiltIntF x) - (Ahat - SZc) * ((2 : ℂ) * (Real.pi : ℂ)))
        = -edgeB a 2 Tp (tiltIntF x) + edgeT a 2 Tp (tiltIntF x)
          + Complex.I * edgeL a Tp (tiltIntF x) := by
      linear_combination hcomb
    -- the horizontal-edge bound
    have hhoriz : K1 * x ^ 2 * ((Real.log (Tp + 2)) ^ 5 / Tp + (Real.log (Tp + 2)) ^ 3 / (δ * Tp)
        + 1 / Real.sqrt Tp) ≤ ε / 4 := by
      refine horiz_edge_arith hK1pos.le hx0.le hT5 hTp0 hTleTp hTpLe hcghpos hδ ?_ ?_ ?_
      · have h := hTb T hTbT; rw [Real.rpow_one] at h; linarith
      · have h := hTc T hTcT; rw [Real.rpow_one] at h; linarith
      · have h := hTd T hTdT
        rw [pow_zero, mul_one] at h
        linarith
    have hEBle : ‖edgeB a 2 Tp (tiltIntF x)‖ ≤ ε / 4 :=
      le_trans (norm_edgeB_tiltIntF_le hx ha2')
        (le_trans (hK1 x Tp δ a hx hTp5 hxTp hδpos hgapδ ha1.le) hhoriz)
    have hETle : ‖edgeT a 2 Tp (tiltIntF x)‖ ≤ ε / 4 :=
      le_trans (norm_edgeT_tiltIntF_le (x := x) (a := a) (Tp := Tp) ha2')
        (le_trans (hK1 x Tp δ a hx hTp5 hxTp hδpos hgapδ ha1.le) hhoriz)
    have hELle : ‖edgeL a Tp (tiltIntF x)‖ ≤ ε / 2 := by
      refine le_trans (norm_edgeL_tiltIntF_le (x := x) (a := a) (Tp := Tp) hTp0.le) ?_
      refine le_trans (hCn x N Tp hx hN1 hTp0) ?_
      have h := hTe T hTeT
      rw [pow_one, Real.rpow_one] at h
      exact left_edge_arith hCnpos.le hx hN1 hT5 hTp0 hTleTp hTpLe hNr hNlt h
    have htri : ‖-edgeB a 2 Tp (tiltIntF x) + edgeT a 2 Tp (tiltIntF x)
        + Complex.I * edgeL a Tp (tiltIntF x)‖ ≤ ε := by
      have h1 : ‖-edgeB a 2 Tp (tiltIntF x) + edgeT a 2 Tp (tiltIntF x)‖ ≤ ε / 2 := by
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_neg]
        linarith
      have h2 : ‖Complex.I * edgeL a Tp (tiltIntF x)‖ = ‖edgeL a Tp (tiltIntF x)‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
      calc ‖-edgeB a 2 Tp (tiltIntF x) + edgeT a 2 Tp (tiltIntF x)
            + Complex.I * edgeL a Tp (tiltIntF x)‖
          ≤ ‖-edgeB a 2 Tp (tiltIntF x) + edgeT a 2 Tp (tiltIntF x)‖
            + ‖Complex.I * edgeL a Tp (tiltIntF x)‖ := norm_add_le _ _
        _ ≤ ε / 2 + ε / 2 := by rw [h2]; linarith
        _ = ε := by ring
    -- the right-edge error
    have hRight : ‖(∫ t in (0 : ℝ)..x, (Chebyshev.psi t : ℂ)) - u * edgeR 2 Tp (tiltIntF x)‖
        ≤ ε / 4 := by
      rw [edgeR_tiltIntF_perron hx0]
      refine le_trans (hCper Tp hTp2) ?_
      have h := hTa T hTaT
      rw [Real.rpow_one] at h
      exact right_edge_arith hCperpos.le hx0.le hT5 hTp0 hxT hTleTp hTpLe h
    -- rewriting the solved edge integral
    have huw : u * ((2 : ℂ) * (Real.pi : ℂ)) = 1 := by
      rw [hu, one_div, inv_mul_cancel₀]
      simp [Real.pi_ne_zero]
    have herr : ‖edgeR 2 Tp (tiltIntF x) - (Ahat - SZc) * ((2 : ℂ) * (Real.pi : ℂ))‖
        = ‖-edgeB a 2 Tp (tiltIntF x) + edgeT a 2 Tp (tiltIntF x)
            + Complex.I * edgeL a Tp (tiltIntF x)‖ := by
      rw [← hkeyI, norm_mul, Complex.norm_I, one_mul]
    have hRight' : ‖u * edgeR 2 Tp (tiltIntF x) - (Ahat - SZc)‖ ≤ ε / 4 := by
      have hrw : u * edgeR 2 Tp (tiltIntF x) - (Ahat - SZc)
          = u * (edgeR 2 Tp (tiltIntF x) - (Ahat - SZc) * ((2 : ℂ) * (Real.pi : ℂ))) := by
        have hkey2 : u * ((Ahat - SZc) * ((2 : ℂ) * (Real.pi : ℂ))) = (Ahat - SZc) := by
          rw [← mul_assoc, mul_comm u (Ahat - SZc), mul_assoc, huw, mul_one]
        rw [mul_sub, hkey2]
      rw [hrw, norm_mul, herr]
      have hunorm : ‖u‖ ≤ 1 / 4 := by
        rw [hu, norm_div, norm_one, norm_mul]
        have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
        have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
          simp [Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]
        rw [h2, hpi, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
        linarith [Real.two_le_pi]
      nlinarith [norm_nonneg (-edgeB a 2 Tp (tiltIntF x) + edgeT a 2 Tp (tiltIntF x)
        + Complex.I * edgeL a Tp (tiltIntF x)), hunorm, htri, hε]
    -- the complement tail
    have htail : ‖Z - ∑ ρ ∈ Zc, F ρ‖ ≤ ε / 4 := by
      have hsplit := hsumF.sum_add_tsum_subtype_compl Zc
      have heq : Z - (∑ ρ ∈ Zc, F ρ) = ∑' x : {ρ : ℂ // ρ ∉ Zc}, F x := by
        rw [hZF, ← hsplit]
        ring
      rw [heq]
      have hnormsum : Summable (fun i : {ρ : ℂ // ρ ∉ Zc} => ‖F (i : ℂ)‖) :=
        (hsumF.subtype (fun ρ => ρ ∉ Zc)).norm
      refine le_trans (norm_tsum_le_tsum_norm hnormsum) ?_
      have hfinite : ∀ s : Finset {ρ : ℂ // ρ ∉ Zc},
          ∑ i ∈ s, ‖F (i : ℂ)‖ ≤ 4 * x ^ 2 * (Cfins * (Real.log (Tp + 2) + 1) / Tp) := by
        intro s
        have hpt : ∀ i ∈ s, ‖F (i : ℂ)‖
            ≤ 4 * x ^ 2 * ((zeta1Order (i : ℂ) : ℝ) / (1 + ‖(i : ℂ)‖ ^ 2)) := by
          intro i _
          by_cases hz : riemannZeta₁ (i : ℂ) = 0
          · have hnorm : Tp ≤ ‖(i : ℂ)‖ :=
              zero_notin_rect_norm_ge' hR0 ha1.le hTp0 hTpR haTp hz i.2
            have h2 : (2 : ℝ) ≤ ‖(i : ℂ)‖ := by linarith
            have h' := zeta1_zero_tilted_term_le x hx (i : ℂ) hz h2
            simpa only [hF] using h'
          · have hzo : zeta1Order (i : ℂ) = 0 := by unfold zeta1Order; rw [dif_neg hz]
            have hFz : F (i : ℂ) = 0 := by rw [hF]; simp [hzo]
            rw [hFz, norm_zero]
            rw [hzo]
            simp
        calc ∑ i ∈ s, ‖F (i : ℂ)‖
            ≤ ∑ i ∈ s, 4 * x ^ 2 * ((zeta1Order (i : ℂ) : ℝ) / (1 + ‖(i : ℂ)‖ ^ 2)) :=
              Finset.sum_le_sum hpt
          _ = 4 * x ^ 2 * ∑ i ∈ s, ((zeta1Order (i : ℂ) : ℝ) / (1 + ‖(i : ℂ)‖ ^ 2)) := by
              rw [Finset.mul_sum]
          _ ≤ 4 * x ^ 2 * (Cfins * (Real.log (Tp + 2) + 1) / Tp) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact hCfins Zc hZczeros Tp hTp2 (fun ρ hz hnot =>
                zero_notin_rect_norm_ge' hR0 ha1.le hTp0 hTpR haTp hz hnot) s
      have htsum := Summable.tsum_le_of_sum_le hnormsum hfinite
      have h := hTf T hTfT
      rw [pow_one, Real.rpow_one] at h
      exact le_trans htsum (tail_arith hCfinspos.le hx0.le hT5 hTp0 hTleTp hTpLe h)
    have hdecomp : (∫ t in (0 : ℝ)..x, (Chebyshev.psi t : ℂ)) - (Ahat - Z)
        = ((∫ t in (0 : ℝ)..x, (Chebyshev.psi t : ℂ)) - u * edgeR 2 Tp (tiltIntF x))
          + (u * edgeR 2 Tp (tiltIntF x) - (Ahat - SZc))
          + (Z - ∑ ρ ∈ Zc, F ρ) := by ring
    rw [hdecomp]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
    linarith [hRight, hRight', htail]
  have hle : ‖(∫ t in (0 : ℝ)..x, (Chebyshev.psi t : ℂ)) - (Ahat - Z)‖ ≤ 0 :=
    le_of_forall_pos_le_add (fun ε hε => by simpa using key ε hε)
  have hzero : (∫ t in (0 : ℝ)..x, (Chebyshev.psi t : ℂ)) - (Ahat - Z) = 0 :=
    norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  exact sub_eq_zero.mp hzero

end Commons.NumberTheory.Zeta
