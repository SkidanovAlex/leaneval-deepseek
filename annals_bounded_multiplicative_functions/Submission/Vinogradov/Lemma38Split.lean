/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.Lemma38Step5
import Submission.Commons.Measure.Integral.lintegral_ell2_minkowski_rpow_finset
import Submission.Commons.Measure.Integral.setIntegral_le_mul_lintegral_mul_of_one_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# GLYZ Lemma 3.8, step 4: the level-gap split

`Lemma38Step5.exists_asymAV_le_proj_K` hands the caller two obligations: the largeness of the level
gap `K ≤ M − m`, and the degree-`l` model hypothesis at the (fixed) enlargement `2 Λ₀`.  The
arithmetic obligation `2 Λ₀ ≤ 2^(M−m)` is discharged by `exists_two_mul_le_two_pow`; the remaining
work is the case split on the gap:

* **large gap** (`K ≤ M − m`): the window `[Λ₀, 2^(M−m)/2]` for the plate enlargement is
  non-empty and the lane-4 bound applies at `lam := Λ₀`;
* **small gap** (`M − m < K`): the number of level-`M` sub-blocks is bounded by the *fixed*
  constant `2^(K−1)`, so the trivial triangle-inequality bound applies with a fixed constant.  This
  is the absorption of the small-gap case.

This file contains (a) the combinatorial ingredient of the small-gap branch, `card_subBlkLvl_le`,
and (b) **step 1** of that branch, `asymAV_le_trivial_pt`: the pointwise Cauchy–Schwarz inequality
over the sub-blocks of the block, integrated, with the constant `card^{p_l/2}` pulled out.  Steps 2
(Minkowski on the restricted measure, `lintegral_ell2_minkowski_rpow_finset`) and 3 (the tent
comparison, `setIntegral_le_mul_lintegral_mul_of_one_le` plus `BallTent.le_ballTent_of_mem`) are
now also done, giving the full trivial bound `asymAV_le_trivial`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-- **The number of level-`M` sub-blocks of a level-`m` block is at most `2^(M−m)`.**  This is what
makes the small-gap branch of the level-gap split absorbable: when `M − m < K` the number of
sub-blocks is bounded by the *fixed* constant `2^(K−1)`, so the trivial bound carries a fixed
constant.

Proof: `image_subIdx_univ` identifies the sub-blocks with the image of `Fin (2^(M−m))` under
`subIdx`, and `Finset.card_image_le` bounds the cardinality by the source. -/
lemma card_subBlkLvl_le (m M : ℕ) (hmM : m ≤ M) (q : Fin (2 ^ m)) :
    (subBlkLvl m M q).card ≤ 2 ^ (M - m) := by
  calc (subBlkLvl m M q).card
      = (Finset.image (subIdx m M hmM q) (Finset.univ : Finset (Fin (2 ^ (M - m))))).card := by
        rw [image_subIdx_univ]
    _ ≤ (Finset.univ : Finset (Fin (2 ^ (M - m)))).card := Finset.card_image_le
    _ = 2 ^ (M - m) := by simp

/-- **Step 1 of the small-gap bound**: the pointwise Cauchy–Schwarz inequality over the sub-blocks
of the block, integrated. -/
lemma asymAV_le_trivial_pt {k l N m M : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k)
    (hmM : m ≤ M) (hMN : M ≤ N) {ξ' : ℝ} (q : Fin (2 ^ m)) (u : E k) {r : ℝ}
    {f : Fin (2 ^ N) → E k → ℂ} (hf : ∀ i, Measurable (f i)) :
    (∫⁻ w in Metric.ball (0 : E l) r,
        (‖∑ i ∈ blkFin N m q,
          f i (u + projEmbedLin k l (torsionVec k l hlk ξ') w)‖₊ : ℝ≥0∞) ^ (plExp l))
      ≤ ((subBlkLvl m M q).card : ℝ≥0∞) ^ (plExp l / 2)
        * ∫⁻ w in Metric.ball (0 : E l) r,
            (∑ J ∈ subBlkLvl m M q,
              ((‖∑ i ∈ blkFin N M J,
                f i (u + projEmbedLin k l (torsionVec k l hlk ξ') w)‖₊ : ℝ≥0∞)) ^ (2 : ℝ))
              ^ (plExp l / 2) := by
  have hpl1 : 1 ≤ plExp l := by rw [plExp]; exact_mod_cast (by nlinarith : 1 ≤ l * (l + 1))
  have hpl0 : 0 < plExp l := lt_of_lt_of_le zero_lt_one hpl1
  set ψ : E l →ₗ[ℝ] E k := projEmbedLin k l (torsionVec k l hlk ξ') with hψ
  set G : Fin (2 ^ M) → E l → ℂ := fun J y => ∑ i ∈ blkFin N M J, f i (u + ψ y) with hG
  have hpt : ∀ y : E l,
      (‖∑ i ∈ blkFin N m q, f i (u + ψ y)‖₊ : ℝ≥0∞) ^ (plExp l)
        ≤ (((subBlkLvl m M q).card : ℝ≥0∞) ^ ((1 : ℝ) / 2)
            * (∑ J ∈ subBlkLvl m M q, ((‖G J y‖₊ : ℝ≥0∞)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
          ^ (plExp l) := by
    intro y
    have hid : (∑ i ∈ blkFin N m q, f i (u + ψ y)) = ∑ J ∈ subBlkLvl m M q, G J y := by
      simp only [hG]
      exact sum_subBlkLvl hmM hMN q (fun i : Fin (2 ^ N) => f i (u + ψ y))
    rw [hid]
    have h1 : (‖∑ J ∈ subBlkLvl m M q, G J y‖₊ : ℝ≥0∞)
        ≤ ∑ J ∈ subBlkLvl m M q, (‖G J y‖₊ : ℝ≥0∞) := by
      have h := nnnorm_sum_le (subBlkLvl m M q) (fun J => G J y)
      exact_mod_cast h
    have h2 := Commons.Analysis.Inequalities.sum_rpow_le_card_rpow_mul_sum_rpow
      (subBlkLvl m M q) (fun J => (‖G J y‖₊ : ℝ≥0∞)) (by norm_num : (1 : ℝ) ≤ 2)
    have h3 : (∑ J ∈ subBlkLvl m M q, (‖G J y‖₊ : ℝ≥0∞))
        ≤ ((subBlkLvl m M q).card : ℝ≥0∞) ^ ((1 : ℝ) / 2)
          * (∑ J ∈ subBlkLvl m M q, ((‖G J y‖₊ : ℝ≥0∞)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
      have h := ENNReal.rpow_le_rpow h2 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
      have e1 : (((∑ J ∈ subBlkLvl m M q, (‖G J y‖₊ : ℝ≥0∞)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2))
          = ∑ J ∈ subBlkLvl m M q, (‖G J y‖₊ : ℝ≥0∞) := by
        rw [← ENNReal.rpow_mul, show (2 : ℝ) * ((1 : ℝ) / 2) = 1 by norm_num,
          ENNReal.rpow_one]
      have e2 : ((((subBlkLvl m M q).card : ℝ≥0∞) ^ ((2 : ℝ) - 1)
              * (∑ J ∈ subBlkLvl m M q, ((‖G J y‖₊ : ℝ≥0∞)) ^ (2 : ℝ))) ^ ((1 : ℝ) / 2))
          = ((subBlkLvl m M q).card : ℝ≥0∞) ^ ((1 : ℝ) / 2)
            * (∑ J ∈ subBlkLvl m M q, ((‖G J y‖₊ : ℝ≥0∞)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
        rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]
      rw [e1, e2] at h
      exact h
    exact ENNReal.rpow_le_rpow (h1.trans h3) hpl0.le
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  have hcongr : (∫⁻ y in Metric.ball (0 : E l) r,
        (((subBlkLvl m M q).card : ℝ≥0∞) ^ ((1 : ℝ) / 2)
          * (∑ J ∈ subBlkLvl m M q, ((‖G J y‖₊ : ℝ≥0∞)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ (plExp l))
      = ∫⁻ y in Metric.ball (0 : E l) r,
          ((subBlkLvl m M q).card : ℝ≥0∞) ^ (plExp l / 2)
            * (∑ J ∈ subBlkLvl m M q, ((‖G J y‖₊ : ℝ≥0∞)) ^ (2 : ℝ)) ^ (plExp l / 2) := by
    refine lintegral_congr fun y => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hpl0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    congr 2 <;> ring
  rw [hcongr, lintegral_const_mul'
    (((subBlkLvl m M q).card : ℝ≥0∞) ^ (plExp l / 2)) _ ?_]
  refine ENNReal.rpow_ne_top_of_ne_zero ?_ (by simp)
  intro h
  have h0 : (subIdx m M hmM q 0) ∈ subBlkLvl m M q :=
    mem_subBlkLvl.mpr (subIdx_div m M hmM q 0)
  exact Finset.card_ne_zero_of_mem h0 (Nat.cast_eq_zero.mp h)

theorem asymAV_le_trivial {k l N m M m' : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k)
    (hmM : m ≤ M) (hMN : M ≤ N) {ξ' : ℝ} (q : Fin (2 ^ m))
    {A : ℝ} (hA : 0 ≤ A) {u : E k} {r : ℝ} (hr : 0 < r)
    {f : Fin (2 ^ N) → E k → ℂ} (hf : ∀ i, Measurable (f i)) :
    (∫⁻ w in Metric.ball (0 : E l) r,
        (‖∑ i ∈ blkFin N m q,
          f i (u + projEmbedLin k l (torsionVec k l hlk ξ') w)‖₊ : ℝ≥0∞) ^ (plExp l))
      ≤ ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal)
        * ((subBlkLvl m M q).card : ℝ≥0∞) ^ (plExp l / 2)
        * (∑ J ∈ subBlkLvl m M q,
            (tentNorm l A 0 r (fun y : E l => ∑ i ∈ blkFin N M J,
              f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
          ^ (plExp l / 2) := by
  have hpl1 : 1 ≤ plExp l := by rw [plExp]; exact_mod_cast (by nlinarith : 1 ≤ l * (l + 1))
  have hpl2 : 2 ≤ plExp l := by rw [plExp]; exact_mod_cast (by nlinarith : 2 ≤ l * (l + 1))
  have hpl0 : 0 < plExp l := lt_of_lt_of_le zero_lt_one hpl1
  have hplne : plExp l ≠ 0 := ne_of_gt hpl0
  set ψ : E l →ₗ[ℝ] E k := projEmbedLin k l (torsionVec k l hlk ξ') with hψ
  set G : Fin (2 ^ M) → E l → ℂ := fun J y => ∑ i ∈ blkFin N M J, f i (u + ψ y) with hG
  set TN : Fin (2 ^ M) → ℝ≥0∞ := fun J =>
    tentNorm l A 0 r (fun y : E l => ∑ i ∈ blkFin N M J, f i (u + ψ y)) with hTN
  have hBpos : ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact ENNReal.toReal_pos (Metric.measure_ball_pos (μ := volume) 0 hr).ne'
      (measure_ball_lt_top (μ := volume)).ne
  have hBtop : ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hbmeas : ∀ J : Fin (2 ^ M),
      AEMeasurable (fun y : E l => (‖G J y‖₊ : ℝ≥0∞))
        (volume.restrict (Metric.ball (0 : E l) r)) := by
    intro J
    have h1 : Measurable (fun y : E l => G J y) := by
      simp only [hG]
      exact Finset.measurable_sum _ fun i _ => (hf i).comp
        (measurable_const.add (LinearMap.continuous_of_finiteDimensional ψ).measurable)
    exact (h1.nnnorm.coe_nnreal_ennreal).aemeasurable
  -- step 2: Minkowski
  have hmink := Commons.Measure.Integral.lintegral_ell2_minkowski_rpow_finset
    (volume.restrict (Metric.ball (0 : E l) r)) (subBlkLvl m M q) hpl2
    (fun J y => (‖G J y‖₊ : ℝ≥0∞)) hbmeas
  -- step 3: the tent comparison
  have htent : ∀ J ∈ subBlkLvl m M q,
      (∫⁻ y, (‖G J y‖₊ : ℝ≥0∞) ^ (plExp l)
        ∂(volume.restrict (Metric.ball (0 : E l) r)))
        ≤ ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal) * TN J := by
    intro J _
    have hΦ : ∀ x ∈ Metric.ball (0 : E l) r,
        (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal)
          * ballTent l A 0 r x := by
      intro x hx
      have h1 := le_ballTent_of_mem l A 0 hx
      have h2 := mul_le_mul_of_nonneg_left h1
        (by positivity : (0 : ℝ≥0∞) ≤ ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal))
      rwa [ENNReal.mul_inv_cancel hBpos hBtop] at h2
    have h1 : Measurable (fun y : E l => G J y) := by
      simp only [hG]
      exact Finset.measurable_sum _ fun i _ => (hf i).comp
        (measurable_const.add (LinearMap.continuous_of_finiteDimensional ψ).measurable)
    have hF : AEMeasurable (fun y : E l => (‖G J y‖₊ : ℝ≥0∞) ^ (plExp l)) volume :=
      ((h1.nnnorm.coe_nnreal_ennreal).pow_const _).aemeasurable
    have hΦm : AEMeasurable (ballTent l A 0 r) volume :=
      (measurable_ballTent l A 0 r).aemeasurable
    have h := Commons.Measure.Integral.setIntegral_le_mul_lintegral_mul_of_one_le
      (μ := volume) (measurableSet_ball) hF hΦm hΦ
    simpa only [hG, hTN, tentNorm] using h
  -- combine steps 2 and 3
  have hS : (∑ J ∈ subBlkLvl m M q,
        ((∫⁻ y, (‖G J y‖₊ : ℝ≥0∞) ^ (plExp l)
          ∂(volume.restrict (Metric.ball (0 : E l) r))) ^ (2 / plExp l)))
      ≤ (ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal)) ^ (2 / plExp l)
        * ∑ J ∈ subBlkLvl m M q, (TN J) ^ (2 / plExp l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun J hJ => ?_
    refine (ENNReal.rpow_le_rpow (htent J hJ) (by positivity : (0 : ℝ) ≤ 2 / plExp l)).trans
      (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 2 / plExp l)]
  have hI : (∫⁻ y, (∑ J ∈ subBlkLvl m M q, ((‖G J y‖₊ : ℝ≥0∞)) ^ (2 : ℝ)) ^ (plExp l / 2)
        ∂(volume.restrict (Metric.ball (0 : E l) r)))
      ≤ ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal)
        * (∑ J ∈ subBlkLvl m M q, (TN J) ^ (2 / plExp l)) ^ (plExp l / 2) := by
    set Bv : ℝ≥0∞ := ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal) with hBv
    set T : ℝ≥0∞ := ∑ J ∈ subBlkLvl m M q, (TN J) ^ (2 / plExp l) with hT
    have hroot : (∫⁻ y, (∑ J ∈ subBlkLvl m M q, ((‖G J y‖₊ : ℝ≥0∞)) ^ (2 : ℝ)) ^ (plExp l / 2)
          ∂(volume.restrict (Metric.ball (0 : E l) r))) ^ (1 / plExp l) ≤ Bv ^ (1 / plExp l) * T ^ ((1 : ℝ) / 2) := by
      refine hmink.trans ?_
      refine (ENNReal.rpow_le_rpow hS (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)).trans ?_
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity : (0 : ℝ≥0∞) ≤ T ^ ((1 : ℝ) / 2))
      refine le_of_eq ?_
      rw [← ENNReal.rpow_mul]
      congr 1
      field_simp
    have hfinal : (∫⁻ y, (∑ J ∈ subBlkLvl m M q, ((‖G J y‖₊ : ℝ≥0∞)) ^ (2 : ℝ)) ^ (plExp l / 2)
          ∂(volume.restrict (Metric.ball (0 : E l) r))) ≤ Bv * T ^ (plExp l / 2) := by
      calc (∫⁻ y, (∑ J ∈ subBlkLvl m M q, ((‖G J y‖₊ : ℝ≥0∞)) ^ (2 : ℝ)) ^ (plExp l / 2)
            ∂(volume.restrict (Metric.ball (0 : E l) r)))
          = ((∫⁻ y, (∑ J ∈ subBlkLvl m M q, ((‖G J y‖₊ : ℝ≥0∞)) ^ (2 : ℝ)) ^ (plExp l / 2)
              ∂(volume.restrict (Metric.ball (0 : E l) r))) ^ (1 / plExp l)) ^ (plExp l) := by
            rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hplne, ENNReal.rpow_one]
        _ ≤ (Bv ^ (1 / plExp l) * T ^ ((1 : ℝ) / 2)) ^ (plExp l) :=
            ENNReal.rpow_le_rpow hroot hpl0.le
        _ = Bv * T ^ (plExp l / 2) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hpl0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
              one_div, inv_mul_cancel₀ hplne, ENNReal.rpow_one]
            congr 1
            ring
    rwa [hBv, hT] at hfinal
  refine (asymAV_le_trivial_pt hl hlk hmM hMN q u hf).trans ?_
  refine (mul_le_mul_of_nonneg_left hI (by positivity : (0 : ℝ≥0∞) ≤ ((subBlkLvl m M q).card : ℝ≥0∞) ^ (plExp l / 2))).trans (le_of_eq ?_)
  rw [show (∑ J ∈ subBlkLvl m M q,
        (tentNorm l A 0 r (fun y : E l => ∑ i ∈ blkFin N M J,
          f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
      = ∑ J ∈ subBlkLvl m M q, (TN J) ^ (2 / plExp l) from
    Finset.sum_congr rfl fun J _ => by rw [hTN]]
  ring

/-- **The level-gap split.**  The two obligations of `exists_asymAV_le_proj_K` are discharged: the
threshold `Λ₀`, its integer witness `K` (`2 Λ₀ ≤ 2^n` for `n ≥ K`), and — for every `M`, `m` — the
lane-4 conclusion, given the model hypothesis at the *fixed* enlargement `2 Λ₀`.  When the gap
`K ≤ M − m` is large the window `[Λ₀, 2^(M−m)/2]` is non-empty and the lane applies at `lam := Λ₀`;
when it is small the trivial bound applies with the fixed constant `C = (2^(M−m))^{1/2}`. -/
theorem exists_asymAV_le_proj_all {k l N m M m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    (h2m : 2 ≤ m) (hmM : m ≤ M) (hMN : M ≤ N)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) (q : Fin (2 ^ m))
    (hsepI : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      1 / 4 ≤ |((q : ℕ) : ℝ) / (2 : ℝ) ^ m + (1 / (2 : ℝ) ^ m) * t - ξ'|)
    (hsep : ∀ j : Fin (2 ^ (M - m)),
      1 / 4 ≤ |pieceCenter (2 ^ M) (subIdx m M hmM q j) - ξ'|)
    {cL R : ℝ} (hcL : 0 < cL) (hR : 0 < R)
    (hplate : ∀ t ∈ Set.Icc (0 : ℝ) 1, 1 / 4 ≤ |t - ξ'| →
      PlateLowerAt l (projCurveDeriv k l (torsionVec k l hlk ξ')) cL t)
    (htay : CurveTaylorTop l (projCurveDeriv k l (torsionVec k l hlk ξ')) R)
    {a₀ εm A : ℝ} (ha1 : 1 ≤ a₀) (hεm : 0 < εm) (hA : 0 ≤ A)
    (hm : 1 ≤ m) (hM : M = refLvl l k m') (h4 : 4 ≤ 2 ^ (M - m))
    {f : Fin (2 ^ N) → E k → ℂ}
    (hf : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i))
    (u : E k) {r : ℝ} (hrR : hBallR k l m' ≤ r) :
    ∃ Λ₀ : ℝ, 1 ≤ Λ₀ ∧ ∃ K : ℕ, (∀ {n : ℕ}, K ≤ n → 2 * Λ₀ ≤ (2 : ℝ) ^ n) ∧
      ((∀ M' : ℕ, 1 ≤ M' → DecLinScale l M' (towerEnlP l cL R (2 * Λ₀))
          (ENNReal.ofReal (a₀ * (M' : ℝ) ^ εm))) →
        ∃ C : ℝ≥0∞,
          (∫⁻ w in Metric.ball (0 : E l) r,
              (‖∑ i ∈ blkFin N m q,
                f i (u + projEmbedLin k l (torsionVec k l hlk ξ') w)‖₊ : ℝ≥0∞) ^ (plExp l))
            ≤ ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal) * C ^ (plExp l)
              * (∑ J ∈ subBlkLvl m M q,
                  (tentNorm l A 0 r (fun y : E l => ∑ i ∈ blkFin N M J,
                    f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
                ^ (plExp l / 2)) := by
  have hfm : ∀ i, Measurable (f i) := fun i => (hf i).continuous.measurable
  obtain ⟨Λ₀, hΛ₀1, K, hK, hmain⟩ := exists_asymAV_le_proj_K (ξ' := ξ') hk hl hlk
    h2m hmM hMN hξ' q hsepI hsep hcL hR hplate htay ha1 hεm hA hm hM h4 hf (u := u) hrR
  refine ⟨Λ₀, hΛ₀1, K, hK, fun hmMod => ?_⟩
  by_cases hgap : K ≤ M - m
  · exact hmain hgap (le_refl Λ₀) (hK hgap) hmMod
  · have hr : 0 < r := lt_of_lt_of_le (hBallR_pos k l m') hrR
    have hC := asymAV_le_trivial (m' := m') (ξ' := ξ') (A := A) (u := u)
      hl hlk hmM hMN q hA hr hfm
    refine ⟨(((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ ((1 : ℝ) / 2), ?_⟩
    -- `card^{p/2} ≤ ((2^(M-m))^{1/2})^{p}`
    have hcard : ((subBlkLvl m M q).card : ℝ≥0∞) ≤ ((((2 ^ (M - m) : ℕ)) : ℝ≥0∞)) := by
      exact_mod_cast card_subBlkLvl_le m M hmM q
    have hpl0 : (0 : ℝ) ≤ plExp l / 2 := by rw [plExp]; positivity
    have hcardp : ((subBlkLvl m M q).card : ℝ≥0∞) ^ (plExp l / 2)
        ≤ ((((2 ^ (M - m) : ℕ)) : ℝ≥0∞)) ^ (plExp l / 2) :=
      ENNReal.rpow_le_rpow hcard hpl0
    have hpow : ((((2 ^ (M - m) : ℕ)) : ℝ≥0∞)) ^ (plExp l / 2)
        = ((((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ ((1 : ℝ) / 2)) ^ (plExp l) := by
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    have hmid : ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal)
          * ((subBlkLvl m M q).card : ℝ≥0∞) ^ (plExp l / 2)
          * (∑ J ∈ subBlkLvl m M q,
              (tentNorm l A 0 r (fun y : E l => ∑ i ∈ blkFin N M J,
                f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
            ^ (plExp l / 2)
        ≤ ENNReal.ofReal ((volume (Metric.ball (0 : E l) r)).toReal)
          * ((((2 ^ (M - m) : ℕ)) : ℝ≥0∞) ^ ((1 : ℝ) / 2)) ^ (plExp l)
          * (∑ J ∈ subBlkLvl m M q,
              (tentNorm l A 0 r (fun y : E l => ∑ i ∈ blkFin N M J,
                f i (u + projEmbedLin k l (torsionVec k l hlk ξ') y))) ^ (2 / plExp l))
            ^ (plExp l / 2) := by
      rw [← hpow]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcardp (by positivity)) (by positivity)
    exact hC.trans hmid

end Submission.Vinogradov

