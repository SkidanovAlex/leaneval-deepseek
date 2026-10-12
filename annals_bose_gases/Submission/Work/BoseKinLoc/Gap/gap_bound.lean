import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Decomp.bsShift_L2_tendsto
import Submission.Work.BSKinetic.bsMean_hasCompactSupport
import Submission.Work.BoseKinLoc.Gap.gapBare_eq_expand
import Submission.Work.BoseKinLoc.Gap.integral_lamBox_eq_acube
import Submission.Work.BoseKinLoc.Gap.integral_lamBox_sq
import Submission.Work.BoseKinLoc.Residuals
import Submission.Work.OneBodyKin.BoxHat.boxHat_scale
import Submission.Work.OneBodyKin.Cross.symbol_pq_swap
import Submission.Work.OneBodyKin.integral_bsMean_sq_eq_symbol
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Gap

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

open Submission.BoseGases
open Work.BSKinetic

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. The elementary symbol bound `1 − boxHat 1 q ^ 2 ≤ β⁻¹ ‖q‖²/(‖q‖²+β)`, `β = 1/2` -/

/-- On the unit cube, `‖z‖² ≤ 3/4`. -/
private lemma norm_sq_le_three_quarters_of_mem_acube_one {z : ℝ³} (hz : z ∈ acube 1) :
    ‖z‖ ^ 2 ≤ 3 / 4 := by
  rw [EuclideanSpace.norm_sq_eq]
  have h : ∀ m : Fin 3, ‖z.ofLp m‖ ^ 2 ≤ (1 / 4 : ℝ) := by
    intro m
    have hm := (mem_acube_iff 1 z).mp hz m
    rw [Set.mem_Icc] at hm
    have h1 : ‖z.ofLp m‖ ≤ 1 / 2 := by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
    nlinarith [h1, norm_nonneg (z.ofLp m)]
  calc ∑ m : Fin 3, ‖z.ofLp m‖ ^ 2 ≤ ∑ _m : Fin 3, (1 / 4 : ℝ) :=
        Finset.sum_le_sum (fun m _ => h m)
    _ = 3 / 4 := by norm_num

/-- Pointwise cosine bound on the unit cube: `1 − cos⟪Q,z⟫ ≤ 3‖Q‖²/8` for `z ∈ acube 1`. -/
private lemma one_sub_cos_inner_le_of_mem {Q z : ℝ³} (hz : z ∈ acube 1) :
    1 - Real.cos (inner ℝ Q z) ≤ 3 * ‖Q‖ ^ 2 / 8 := by
  have hz' : ‖z‖ ^ 2 ≤ 3 / 4 := norm_sq_le_three_quarters_of_mem_acube_one hz
  have hcos : 1 - Real.cos (inner ℝ Q z) ≤ (inner ℝ Q z) ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := inner ℝ Q z)]
  have hinner : |inner ℝ Q z| ≤ ‖Q‖ * ‖z‖ := by
    refine abs_le.mpr ⟨?_, real_inner_le_norm Q z⟩
    have h := real_inner_le_norm (-Q) z
    rw [inner_neg_left, norm_neg] at h
    linarith
  have h2 : (inner ℝ Q z) ^ 2 ≤ 3 * ‖Q‖ ^ 2 / 4 := by
    have hb := abs_le.mp hinner
    nlinarith [hb.1, hb.2, hz', sq_nonneg ‖Q‖, norm_nonneg Q, norm_nonneg z]
  linarith

/-- **The box profile bound**: `1 − boxHat 1 Q ≤ 3‖Q‖²/8`. -/
private lemma one_sub_boxHat_le (Q : ℝ³) :
    1 - Work.OneBodyKin.boxHat 1 Q ≤ 3 * ‖Q‖ ^ 2 / 8 := by
  have hfin : (volume : Measure ℝ³) (acube 1) ≠ ⊤ := ne_of_lt (acube_lt_top 1 (by norm_num))
  have hreal : (volume : Measure ℝ³).real (acube 1) = 1 := by
    rw [Measure.real_def, acube_volume 1 (by norm_num), ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  have hconst : IntegrableOn (fun _ : ℝ³ => (1 : ℝ)) (acube 1) volume := integrableOn_const (μ := volume) hfin
  have hcos : IntegrableOn (fun z : ℝ³ => Real.cos (inner ℝ Q z)) (acube 1) volume :=
    (Real.continuous_cos.comp (continuous_const.inner continuous_id)).continuousOn.integrableOn_compact
      (acube_compact (by norm_num : (0:ℝ) < 1))
  have h1 : (∫ z in acube 1, (1 - Real.cos (inner ℝ Q z)))
      = 1 - Work.OneBodyKin.boxHat 1 Q := by
    rw [integral_sub hconst hcos, setIntegral_const, hreal, one_smul]
    rfl
  have hmono : (∫ z in acube 1, (1 - Real.cos (inner ℝ Q z)))
      ≤ ∫ z in acube 1, (3 * ‖Q‖ ^ 2 / 8 : ℝ) :=
    setIntegral_mono_on (f := fun z : ℝ³ => 1 - Real.cos (inner ℝ Q z))
      (g := fun _ : ℝ³ => 3 * ‖Q‖ ^ 2 / 8) (hconst.sub hcos) (integrableOn_const (μ := volume) hfin)
      (acube_measurable 1) (fun z hz => one_sub_cos_inner_le_of_mem hz)
  calc 1 - Work.OneBodyKin.boxHat 1 Q
      = ∫ z in acube 1, (1 - Real.cos (inner ℝ Q z)) := h1.symm
    _ ≤ ∫ z in acube 1, (3 * ‖Q‖ ^ 2 / 8 : ℝ) := hmono
    _ = 3 * ‖Q‖ ^ 2 / 8 := by rw [setIntegral_const, hreal, one_smul]

/-- The elementary arithmetic of `β = 1/2`: `min 1 (3x/4) ≤ (1/2)⁻¹ x/(x+1/2)` for `x ≥ 0`. -/
private lemma arith_min (x : ℝ) (hx : 0 ≤ x) :
    min 1 (3 * x / 4) ≤ (1 / 2 : ℝ)⁻¹ * (x / (x + 1 / 2)) := by
  have hden : (0 : ℝ) < 2 * x + 1 := by linarith
  have heq : (1 / 2 : ℝ)⁻¹ * (x / (x + 1 / 2)) = 4 * x / (2 * x + 1) := by
    field_simp
    ring
  rw [heq]
  rcases lt_or_ge x (4 / 3 : ℝ) with h | h
  · rw [min_eq_right (by linarith : 3 * x / 4 ≤ 1)]
    rw [le_div_iff₀ hden]
    nlinarith
  · rw [min_eq_left (by linarith : 1 ≤ 3 * x / 4)]
    rw [le_div_iff₀ hden]
    nlinarith

/-- **The symbol bound at `β = 1/2`**: `1 − boxHat 1 (ℓ•q)² ≤ gapSym ℓ (1/2) q`. -/
private lemma one_sub_boxHat_sq_le_gapSym (ℓ : ℝ) (hℓ : 0 < ℓ) (q : ℝ³) :
    1 - (Work.OneBodyKin.boxHat 1 (ℓ • q)) ^ 2 ≤ gapSym ℓ (1 / 2) q := by
  set Q : ℝ³ := ℓ • q with hQ
  have hb : |Work.OneBodyKin.boxHat 1 Q| ≤ 1 := by
    have h := Work.OneBodyKin.abs_boxHat_le (ℓ := 1) (by norm_num : (0 : ℝ) ≤ 1) Q
    simpa using h
  have hb1 : -1 ≤ Work.OneBodyKin.boxHat 1 Q := (abs_le.mp hb).1
  have htail := one_sub_boxHat_le Q
  have h2 : 1 - (Work.OneBodyKin.boxHat 1 Q) ^ 2 ≤ 3 * ‖Q‖ ^ 2 / 4 := by
    nlinarith [hb1, htail, sq_nonneg (Work.OneBodyKin.boxHat 1 Q)]
  have hnorm : ‖Q‖ ^ 2 = ℓ ^ 2 * ‖q‖ ^ 2 := by
    rw [hQ, norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
    ring
  have hx : (0 : ℝ) ≤ ℓ ^ 2 * ‖q‖ ^ 2 := by positivity
  have hmin : 1 - (Work.OneBodyKin.boxHat 1 Q) ^ 2 ≤ min 1 (3 * (ℓ ^ 2 * ‖q‖ ^ 2) / 4) :=
    le_min (by linarith [sq_nonneg (Work.OneBodyKin.boxHat 1 Q)])
      (by rw [← hnorm]; linarith [h2])
  have har := arith_min (ℓ ^ 2 * ‖q‖ ^ 2) hx
  rw [hQ] at hmin
  exact le_trans hmin (by simpa only [gapSym] using har)

/-! ## 2. The box-integral inputs

The three inputs `integral_lamBox_eq_acube` (change of variables on the moving box),
`gapBare_eq_expand` (expansion of the mean-free box mass) and `integral_lamBox_sq`
(the `u`-integral of the box mass equals the full mass) are proved in the sibling
modules of this directory. -/


/-! ## 3. The assembly -/

theorem gap_bound : ∃ β : ℝ, 0 < β ∧ β < 1 ∧ GapBound β := by
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  intro ψ hψ hcs ℓ hℓ hint
  -- the moving-box mean is continuous of compact support in `u`
  have hcontB : Continuous (fun u : ℝ³ => bsMean ℓ u ψ) :=
    Work.BSKinetic.Decomp.continuous_bsMean hψ.continuous hcs
  have hcsB : HasCompactSupport (fun u : ℝ³ => bsMean ℓ u ψ) :=
    bsMean_hasCompactSupport hℓ hψ hcs
  have hIntB : Integrable (fun u : ℝ³ => (bsMean ℓ u ψ) ^ 2) :=
    (hcontB.pow 2).integrable_of_hasCompactSupport
      (hcsB.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num : (0 : ℝ) ^ 2 = 0))
  -- the box mass `u ↦ ∫_{Λ(u)} ψ²` is `ℓ³ • bsMean ℓ · (ψ²)`, hence integrable
  have hψ2_cd : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => (ψ z) ^ 2) := by
    simpa [pow_two] using hψ.mul hψ
  have hψ2_cs : HasCompactSupport (fun z : ℝ³ => (ψ z) ^ 2) :=
    hcs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num : (0 : ℝ) ^ 2 = 0)
  have hcontBS2 : Continuous (fun u : ℝ³ => bsMean ℓ u (fun z : ℝ³ => (ψ z) ^ 2)) :=
    Work.BSKinetic.Decomp.continuous_bsMean hψ2_cd.continuous hψ2_cs
  have hcsBS2 : HasCompactSupport (fun u : ℝ³ => bsMean ℓ u (fun z : ℝ³ => (ψ z) ^ 2)) :=
    bsMean_hasCompactSupport hℓ hψ2_cd hψ2_cs
  have hboxmass : ∀ u : ℝ³, (∫ z in lamBox ℓ u, (ψ z) ^ 2)
      = ℓ ^ 3 * bsMean ℓ u (fun z : ℝ³ => (ψ z) ^ 2) := by
    intro u
    rw [integral_lamBox_eq_acube ℓ hℓ (fun z : ℝ³ => (ψ z) ^ 2) u, bsMean]
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 hℓ.ne'), one_mul]
  have hIntA : Integrable (fun u : ℝ³ => ∫ z in lamBox ℓ u, (ψ z) ^ 2) := by
    rw [show (fun u : ℝ³ => ∫ z in lamBox ℓ u, (ψ z) ^ 2)
        = (fun u : ℝ³ => ℓ ^ 3 * bsMean ℓ u (fun z : ℝ³ => (ψ z) ^ 2))
        from funext hboxmass]
    exact (hcontBS2.integrable_of_hasCompactSupport hcsBS2).const_mul (ℓ ^ 3)
  -- the pointwise expansion
  have hpoint : ∀ u : ℝ³, gapBare ℓ u ψ
      = (∫ z in lamBox ℓ u, (ψ z) ^ 2) - ℓ ^ 3 * (bsMean ℓ u ψ) ^ 2 :=
    fun u => gapBare_eq_expand ℓ hℓ ψ hψ u
  have hsplit : (∫ u, gapBare ℓ u ψ)
      = (∫ u, ∫ z in lamBox ℓ u, (ψ z) ^ 2) - ℓ ^ 3 * ∫ u, (bsMean ℓ u ψ) ^ 2 := by
    rw [show (fun u : ℝ³ => gapBare ℓ u ψ)
        = (fun u : ℝ³ => (∫ z in lamBox ℓ u, (ψ z) ^ 2)
            - ℓ ^ 3 * (bsMean ℓ u ψ) ^ 2) from funext hpoint]
    rw [integral_sub hIntA (hIntB.const_mul (ℓ ^ 3)), integral_const_mul]
  -- the three pieces
  have hAsq : (∫ u, ∫ z in lamBox ℓ u, (ψ z) ^ 2) = ∫ z : ℝ³, (ψ z) ^ 2 :=
    integral_lamBox_sq ℓ hℓ ψ hψ hcs
  have hBsq : (∫ u, (bsMean ℓ u ψ) ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ * (ℓ ^ 9)⁻¹
        * ∫ q : ℝ³, Work.OneBodyKin.boxHat ℓ q ^ 2 * ‖fhat ψ q‖ ^ 2 := by
    simpa only [fhat] using Work.OneBodyKin.integral_bsMean_sq_eq_symbol hℓ ψ hψ hcs
  have hPlanch : (∫ z : ℝ³, (ψ z) ^ 2) = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³, ‖fhat ψ q‖ ^ 2 := by
    simpa only [fhat] using (plancherel_pconv ψ hψ hcs).symm
  have hscale : (∫ q : ℝ³, Work.OneBodyKin.boxHat ℓ q ^ 2 * ‖fhat ψ q‖ ^ 2)
      = ℓ ^ 6 * ∫ q : ℝ³, (Work.OneBodyKin.boxHat 1 (ℓ • q)) ^ 2 * ‖fhat ψ q‖ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun q => ?_))
    show Work.OneBodyKin.boxHat ℓ q ^ 2 * ‖fhat ψ q‖ ^ 2
      = ℓ ^ 6 * (Work.OneBodyKin.boxHat 1 (ℓ • q) ^ 2 * ‖fhat ψ q‖ ^ 2)
    rw [Work.OneBodyKin.BoxHat.boxHat_scale hℓ q]
    ring
  have hBscaled : ℓ ^ 3 * (∫ u, (bsMean ℓ u ψ) ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹
        * ∫ q : ℝ³, (Work.OneBodyKin.boxHat 1 (ℓ • q)) ^ 2 * ‖fhat ψ q‖ ^ 2 := by
    rw [hBsq, hscale]
    have hℓne : ℓ ≠ 0 := hℓ.ne'
    have h2pi : ((2 * Real.pi) ^ 3 : ℝ) ≠ 0 := by positivity
    field_simp
  -- integrability on the momentum side
  have hIsq : Integrable (fun q : ℝ³ => ‖fhat ψ q‖ ^ 2) := by
    simpa only [fhat] using integrable_kinFT_sq ψ hψ hcs
  have hboxcont : Continuous (fun q : ℝ³ => Work.OneBodyKin.boxHat 1 (ℓ • q)) :=
    Work.OneBodyKin.Cross.continuous_boxHat_one_smul ℓ
  have hboxbound : ∀ q : ℝ³, ‖(Work.OneBodyKin.boxHat 1 (ℓ • q)) ^ 2‖ ≤ 1 := by
    intro q
    have hb : |Work.OneBodyKin.boxHat 1 (ℓ • q)| ≤ 1 := by
      have h := Work.OneBodyKin.abs_boxHat_le (ℓ := 1) (by norm_num : (0 : ℝ) ≤ 1) (ℓ • q)
      simpa using h
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb' := abs_le.mp hb
    nlinarith [hb'.1, hb'.2]
  have hIbox : Integrable
      (fun q : ℝ³ => (Work.OneBodyKin.boxHat 1 (ℓ • q)) ^ 2 * ‖fhat ψ q‖ ^ 2) :=
    hIsq.bdd_mul ((hboxcont.pow 2).aestronglyMeasurable)
      (Filter.Eventually.of_forall hboxbound)
  have hcomb : (∫ u, gapBare ℓ u ψ)
      = ((2 * Real.pi) ^ 3)⁻¹
        * ∫ q : ℝ³, (1 - (Work.OneBodyKin.boxHat 1 (ℓ • q)) ^ 2) * ‖fhat ψ q‖ ^ 2 := by
    rw [hsplit, hAsq, hPlanch, hBscaled]
    have hsub : (∫ q : ℝ³, (1 - (Work.OneBodyKin.boxHat 1 (ℓ • q)) ^ 2) * ‖fhat ψ q‖ ^ 2)
        = (∫ q : ℝ³, ‖fhat ψ q‖ ^ 2)
          - ∫ q : ℝ³, (Work.OneBodyKin.boxHat 1 (ℓ • q)) ^ 2 * ‖fhat ψ q‖ ^ 2 := by
      rw [← integral_sub hIsq hIbox]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun q => by ring))
    rw [hsub]
    ring
  -- the monotone comparison with the symbol
  have hgp : Continuous (fun q : ℝ³ => gapSym ℓ (1 / 2) q) := by
    have hnum : Continuous (fun q : ℝ³ => ℓ ^ 2 * ‖q‖ ^ 2) := by fun_prop
    have hden : Continuous (fun q : ℝ³ => ℓ ^ 2 * ‖q‖ ^ 2 + 1 / 2) := hnum.add continuous_const
    have hne : ∀ q : ℝ³, ℓ ^ 2 * ‖q‖ ^ 2 + 1 / 2 ≠ 0 := by
      intro q; positivity
    have hquot : Continuous
        (fun q : ℝ³ => (ℓ ^ 2 * ‖q‖ ^ 2) / (ℓ ^ 2 * ‖q‖ ^ 2 + 1 / 2)) :=
      hnum.div hden hne
    have hfun : (fun q : ℝ³ => gapSym ℓ (1 / 2) q)
        = (fun _ : ℝ³ => (1 / 2 : ℝ)⁻¹)
          * (fun q : ℝ³ => (ℓ ^ 2 * ‖q‖ ^ 2) / (ℓ ^ 2 * ‖q‖ ^ 2 + 1 / 2)) := by
      funext q; rfl
    rw [hfun]
    exact continuous_const.mul hquot
  have hgpbound : ∀ q : ℝ³, ‖gapSym ℓ (1 / 2) q‖ ≤ 2 := by
    intro q
    have hden : (0 : ℝ) < ℓ ^ 2 * ‖q‖ ^ 2 + 1 / 2 := by positivity
    have hquot : (ℓ ^ 2 * ‖q‖ ^ 2) / (ℓ ^ 2 * ‖q‖ ^ 2 + 1 / 2) ≤ 1 := by
      rw [div_le_iff₀ hden]; linarith
    have h1 : gapSym ℓ (1 / 2) q
        = (1 / 2 : ℝ)⁻¹ * ((ℓ ^ 2 * ‖q‖ ^ 2) / (ℓ ^ 2 * ‖q‖ ^ 2 + 1 / 2)) := rfl
    rw [h1, Real.norm_eq_abs, abs_of_nonneg (by positivity), show ((1 / 2 : ℝ)⁻¹) = 2 by norm_num]
    nlinarith
  have hIgap : Integrable (fun q : ℝ³ => gapSym ℓ (1 / 2) q * ‖fhat ψ q‖ ^ 2) :=
    hIsq.bdd_mul hgp.aestronglyMeasurable (Filter.Eventually.of_forall hgpbound)
  have hmono : (∫ q : ℝ³, (1 - (Work.OneBodyKin.boxHat 1 (ℓ • q)) ^ 2) * ‖fhat ψ q‖ ^ 2)
      ≤ ∫ q : ℝ³, gapSym ℓ (1 / 2) q * ‖fhat ψ q‖ ^ 2 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun q => ?_)) hIgap
      (Filter.Eventually.of_forall (fun q => ?_))
    · have hb : (Work.OneBodyKin.boxHat 1 (ℓ • q)) ^ 2 ≤ 1 := by
        have h := Work.OneBodyKin.abs_boxHat_le (ℓ := 1) (by norm_num : (0 : ℝ) ≤ 1) (ℓ • q)
        have h' : |Work.OneBodyKin.boxHat 1 (ℓ • q)| ≤ 1 := by simpa using h
        have h'' := abs_le.mp h'
        nlinarith [h''.1, h''.2]
      exact mul_nonneg (by linarith) (sq_nonneg _)
    · exact mul_le_mul_of_nonneg_right (one_sub_boxHat_sq_le_gapSym ℓ hℓ q) (sq_nonneg _)
  calc (∫ u, gapBare ℓ u ψ)
      = ((2 * Real.pi) ^ 3)⁻¹
        * ∫ q : ℝ³, (1 - (Work.OneBodyKin.boxHat 1 (ℓ • q)) ^ 2) * ‖fhat ψ q‖ ^ 2 := hcomb
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : ℝ³, gapSym ℓ (1 / 2) q * ‖fhat ψ q‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = gapFrac ℓ (1 / 2) ψ := rfl

end Work.BoseKinLoc.Gap
