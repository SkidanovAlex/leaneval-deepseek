import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.Analysis.BoseBand.box_meanFree_mul_const_eq_zero
import Submission.Work.Analysis.BoseBand.polar_mainWord_fibre
import Submission.Work.Analysis.BoseBand.tBamp_pair_fixed_p_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.Analysis.BoseBand.mainWord_fibre_offdiag`

The off-diagonal fibre integral of the kinetic word `mainWord` (the fourth term of FS `eq:DefT`,
FS `eq:T'u`):

    `∫_{abox n ℓ} indU(x_j)·( mainWord(fibre_j(E_SΨ + E_TΨ)x) − mainWord(fibre_j(E_SΨ − E_TΨ)x) ) = 0`

for two joint sector projections `E_S`, `E_T` (`Work.BoseFixB2.jointProj`) that both contain the
slot `j` and differ, `S ≠ T`.

## Why it vanishes

`mainWord` is a quadratic form in the one-body state, so the difference above is four times the
polarised word evaluated at the two slot-`j` fibres `f = fibre_j(E_SΨ)x`, `g = fibre_j(E_TΨ)x`.
The polarisation identity (`Analysis/BoseBand/polar_mainWord_fibre`) exhibits that bilinear form as
the momentum integral

    `4·(2π)⁻³·∫_p W(‖p‖)·Re(star(A_p)·B_p) dp`,
    `W(r) = (1−ε_T)·fsKinCoeff((2sℓ)⁻¹)(r) + ε_T·fsKinCoeff((2dsℓ)⁻¹)(r)`,
    `A_p = tBamp χ₀ p E_S j x`, `B_p = tBamp χ₀ p E_T j x`, `χ₀ = bsWin ℓ 0`.

Since `S ≠ T` while both sectors contain `j`, some slot `k < n` differs from the other, and
`k ≠ j`.  At that slot one of `E_SΨ`, `E_TΨ` is *mean-free* — its box mean in the slot variable
vanishes (`P_k` annihilates the sector, `Sector.aP_blockOp_eq_zero`) — while the other is
*independent* of the slot variable (`ConstIn` for a sector not containing the slot,
`Sector.constIn_jointProj`).  Consequently:

* for every momentum `p` the box integral of `indU(x_j)·Re(star(A_p)·B_p)` vanishes
  (`tBamp_pair_fixed_p_zero`, whose hypothesis is discharged by the peel
  `box_meanFree_mul_const_eq_zero`);
* the momentum integral and the configuration integral commute
  (`swap_p_abox_pair_fubini`, proved here from the uniform `(1+‖p‖)⁻³` decay of `tBamp` on the box,
  `Work.SmallBoxTBWord.tBamp_decay`, together with the quadratic growth bound on `W`).

## Contents of this file

* `swap_p_abox_pair_fubini` — the `p ↔ abox` Fubini exchange for the polarised amplitude pairing;
* `mainWord_fibre_swap_at` — the polarised word is symmetric in its two arguments (because
  `Re(star z · w)` is), so the argument may be run in whichever orientation puts the mean-free
  sector first;
* `mainWord_slot_step` — the vanishing at a slot where the first state is mean-free and the second
  is constant in the slot;
* `mainWord_fibre_offdiag` — the target, dispatching on the differing slot.
-/


noncomputable section
open MeasureTheory

namespace Work.Analysis.BoseBand

/-! ## Elementary helpers -/

/-- The real part of `star z * w` is symmetric: `Re(conj z · w) = Re(conj w · z)`. -/
lemma re_star_mul_comm (z w : ℂ) : (star z * w).re = (star w * z).re := by
  have h : star (star z * w) = star w * z := by rw [star_mul, star_star]
  rw [← h]
  simp

/-- The symbol `fsKinCoeff c` grows at most quadratically on `[0,∞)`. -/
lemma fsKinCoeff_le_bound {c t : ℝ} (ht : 0 ≤ t) :
    Submission.BoseGases.fsKinCoeff c t ≤ (1 + |c|) ^ 2 * (1 + t) ^ 2 := by
  rw [Submission.BoseGases.fsKinCoeff]
  have h1 : max (t - c) 0 ≤ (1 + |c|) * (1 + t) := by
    apply max_le
    · have hlt : t - c ≤ t + |c| := by linarith [neg_le_abs c]
      have h2 : t + |c| ≤ (1 + |c|) * (1 + t) := by nlinarith [abs_nonneg c, ht]
      linarith
    · positivity
  simpa [mul_pow] using pow_le_pow_left₀ (le_max_right (t - c) 0) h1 2

/-- A constant multiple of `1/(1+‖p‖)⁴` is integrable on `ℝ³`. -/
private lemma integrable_const_div_pow4 (C : ℝ) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => C / (1 + ‖p‖) ^ 4) := by
  refine (Work.BSKinetic.SwapTBAmp.integrable_one_div_pow4.const_mul C).congr
    (Filter.Eventually.of_forall fun p => ?_)
  change C * (1 / (1 + ‖p‖) ^ 4) = C / (1 + ‖p‖) ^ 4
  rw [mul_one_div]

/-- **The `p ↔ abox` exchange** for the polarised amplitude pairing, proved from the uniform
`(1+‖p‖)⁻³` Fourier decay of `tBamp` on the box (`Work.SmallBoxTBWord.tBamp_decay`) and
Fubini for the jointly integrable `(p,x)`-integrand. -/
theorem swap_p_abox_pair_fubini {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n)
    {F : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hFm : Measurable F)
    (hFbd : ∀ r : ℝ, 0 ≤ r → |F r| ≤ K * (1 + r) ^ 2)
    {W V : Submission.BoseGases.X n → ℝ} (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
        (∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ *
          (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p W j x) *
            Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p V j x).re))
      = ∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ *
          (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
            (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p W j x) *
              Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p V j x).re) := by
  classical
  set χ : EuclideanSpace ℝ (Fin 3) → ℝ := Work.BSKinetic.bsWin ℓ 0 with hχ
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hχcd : ContDiff ℝ (⊤ : ℕ∞) χ := by
    rw [hχ]
    have h : Work.BSKinetic.bsWin ℓ 0 = fun x : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.chiScale ℓ (x - ℓ • (0 : EuclideanSpace ℝ (Fin 3))) := rfl
    rw [h]
    exact (Submission.BoseGases.chiScale_contDiff hℓne).comp (contDiff_id.sub contDiff_const)
  have hχcs : HasCompactSupport χ := by
    rw [hχ]
    have h : Work.BSKinetic.bsWin ℓ 0 = Submission.BoseGases.chiScale ℓ ∘
        ⇑(Homeomorph.subRight (ℓ • (0 : EuclideanSpace ℝ (Fin 3)))) := rfl
    rw [h]
    exact (Submission.BoseGases.chiScale_hasCompactSupport hℓne).comp_homeomorph _
  set ν : MeasureTheory.Measure (Submission.BoseGases.X n) :=
    (volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
      (Submission.BoseGases.abox n ℓ) with hν
  set f : EuclideanSpace ℝ (Fin 3) → Submission.BoseGases.X n → ℝ := fun p x =>
    Work.BoseKinLoc.indU ℓ 0 (x j) * (F ‖p‖ *
      (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
        Work.SmallBoxTBWord.tBamp χ p V j x).re) with hf
  obtain ⟨CW, hCW0, hCW⟩ := Work.SmallBoxTBWord.tBamp_decay (N := n) hℓ hχcd hχcs hW
  obtain ⟨CV, hCV0, hCV⟩ := Work.SmallBoxTBWord.tBamp_decay (N := n) hℓ hχcd hχcs hV
  -- pointwise domination of the `(p,x)`-integrand on the box
  have hpt : ∀ p : EuclideanSpace ℝ (Fin 3), ∀ x ∈ Submission.BoseGases.abox n ℓ,
      ‖f p x‖ ≤ K * CW * CV / (1 + ‖p‖) ^ 4 := by
    intro p x hx
    have hWb : ‖Work.SmallBoxTBWord.tBamp χ p W j x‖ ≤ CW / (1 + ‖p‖) ^ 3 := hCW x hx j p
    have hVb : ‖Work.SmallBoxTBWord.tBamp χ p V j x‖ ≤ CV / (1 + ‖p‖) ^ 3 := hCV x hx j p
    have hind : |Work.BoseKinLoc.indU ℓ 0 (x j)| ≤ 1 := by
      rw [Work.BoseKinLoc.indU]
      by_cases hmem : x j ∈ Work.BoseKinLoc.lamBox ℓ 0
      · rw [Set.indicator_of_mem hmem, abs_one]
      · rw [Set.indicator_of_notMem hmem, abs_zero]
        norm_num
    have hFle : |F ‖p‖| ≤ K * (1 + ‖p‖) ^ 2 := hFbd ‖p‖ (norm_nonneg p)
    have hre : |(star (Work.SmallBoxTBWord.tBamp χ p W j x) *
        Work.SmallBoxTBWord.tBamp χ p V j x).re| ≤ CW * CV / (1 + ‖p‖) ^ 6 := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_star]
      calc ‖Work.SmallBoxTBWord.tBamp χ p W j x‖ * ‖Work.SmallBoxTBWord.tBamp χ p V j x‖
          ≤ (CW / (1 + ‖p‖) ^ 3) * (CV / (1 + ‖p‖) ^ 3) :=
            mul_le_mul hWb hVb (norm_nonneg _) (by positivity)
        _ = CW * CV / ((1 + ‖p‖) ^ 3 * (1 + ‖p‖) ^ 3) := by rw [div_mul_div_comm]
        _ = CW * CV / (1 + ‖p‖) ^ 6 := by
            rw [← pow_add, show ((3 : ℕ) + 3) = 6 from rfl]
    have hnorm : ‖Work.BoseKinLoc.indU ℓ 0 (x j) * (F ‖p‖ *
          (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
            Work.SmallBoxTBWord.tBamp χ p V j x).re)‖
        = |Work.BoseKinLoc.indU ℓ 0 (x j)| * (|F ‖p‖| *
            |(star (Work.SmallBoxTBWord.tBamp χ p W j x) *
              Work.SmallBoxTBWord.tBamp χ p V j x).re|) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
    rw [hnorm]
    calc |Work.BoseKinLoc.indU ℓ 0 (x j)| * (|F ‖p‖| *
          |(star (Work.SmallBoxTBWord.tBamp χ p W j x) *
            Work.SmallBoxTBWord.tBamp χ p V j x).re|)
        ≤ 1 * ((K * (1 + ‖p‖) ^ 2) * (CW * CV / (1 + ‖p‖) ^ 6)) :=
          mul_le_mul hind (mul_le_mul hFle hre (abs_nonneg _) (by positivity)) (by positivity)
            (by norm_num)
      _ = K * CW * CV / (1 + ‖p‖) ^ 4 := by
          field_simp
  have hDnn : ∀ p : EuclideanSpace ℝ (Fin 3), 0 ≤ K * CW * CV / (1 + ‖p‖) ^ 4 := by
    intro p; positivity
  have hD : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) => K * CW * CV / (1 + ‖p‖) ^ 4) :=
    integrable_const_div_pow4 (K * CW * CV)
  -- joint measurability
  have hmeas : AEStronglyMeasurable (Function.uncurry f) (volume.prod ν) := by
    change AEStronglyMeasurable (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
      Work.BoseKinLoc.indU ℓ 0 (q.2 j) * (F ‖q.1‖ *
        (star (Work.SmallBoxTBWord.tBamp χ q.1 W j q.2) *
          Work.SmallBoxTBWord.tBamp χ q.1 V j q.2).re)) (volume.prod ν)
    have hindm : Measurable (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (q.2 j)) := by
      have hset : MeasurableSet (Work.BSKinetic.bsBox ℓ 0) := by
        have h : Work.BSKinetic.bsBox ℓ 0
            = {y : EuclideanSpace ℝ (Fin 3) | y - ℓ • (0 : EuclideanSpace ℝ (Fin 3))
                ∈ Submission.BoseGases.acube ℓ} := rfl
        rw [h]
        exact (Submission.BoseGases.acube_measurable ℓ).preimage
          (continuous_id.sub continuous_const).measurable
      have hfun : Work.BoseKinLoc.indU ℓ 0
          = (Work.BSKinetic.bsBox ℓ 0).indicator (fun _ => (1 : ℝ)) := rfl
      rw [hfun]
      exact (measurable_const.indicator hset).comp
        ((continuous_apply j).comp continuous_snd).measurable
    have hcont : Continuous (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        (star (Work.SmallBoxTBWord.tBamp χ q.1 W j q.2) *
          Work.SmallBoxTBWord.tBamp χ q.1 V j q.2).re) :=
      Complex.continuous_re.comp
        ((continuous_star.comp
            (Work.SmallBoxTBWord.continuous_tBamp_pair hχcd.continuous hχcs hW.continuous j)).mul
          (Work.SmallBoxTBWord.continuous_tBamp_pair hχcd.continuous hχcs hV.continuous j))
    exact (hindm.mul ((hFm.comp (continuous_norm.measurable.comp continuous_fst.measurable)).mul
      hcont.measurable)).aestronglyMeasurable
  -- the iterated-lintegral bound along the box fibres
  have hbm : ∀ᵐ x ∂ν, (∫⁻ p : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal ‖f p x‖) ≤
      ENNReal.ofReal (∫ p : EuclideanSpace ℝ (Fin 3), K * CW * CV / (1 + ‖p‖) ^ 4) := by
    rw [hν, ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
    filter_upwards with x hx
    calc (∫⁻ p : EuclideanSpace ℝ (Fin 3), ENNReal.ofReal ‖f p x‖)
        ≤ ∫⁻ p : EuclideanSpace ℝ (Fin 3),
            ENNReal.ofReal (K * CW * CV / (1 + ‖p‖) ^ 4) := by
          apply lintegral_mono; intro p
          exact ENNReal.ofReal_le_ofReal (hpt p x hx)
      _ = ENNReal.ofReal (∫ p : EuclideanSpace ℝ (Fin 3), K * CW * CV / (1 + ‖p‖) ^ 4) :=
          (ofReal_integral_eq_lintegral_ofReal hD (Filter.Eventually.of_forall hDnn)).symm
  have hg : (∫⁻ x : Submission.BoseGases.X n,
      ENNReal.ofReal (∫ p : EuclideanSpace ℝ (Fin 3), K * CW * CV / (1 + ‖p‖) ^ 4) ∂ν) ≠ ⊤ := by
    rw [hν, lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (Submission.BoseGases.abox_lt_top n ℓ hℓ.le).ne
  have hInt : MeasureTheory.Integrable (Function.uncurry f) (volume.prod ν) :=
    Commons.Measure.Integral.integrable_uncurry_of_lintegral_le_sfinite hmeas hg hbm
  have hswap := MeasureTheory.integral_integral_swap (μ := volume) (ν := ν) hInt
  have hL : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
        (∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ *
          (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
            Work.SmallBoxTBWord.tBamp χ p V j x).re))
      = ∫ x : Submission.BoseGases.X n,
          ∫ p : EuclideanSpace ℝ (Fin 3), f p x ∂volume ∂ν := by
    rw [hν]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [hf]
    change Work.BoseKinLoc.indU ℓ 0 (x j) *
        (∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ *
          (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
            Work.SmallBoxTBWord.tBamp χ p V j x).re)
      = ∫ p : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.indU ℓ 0 (x j) *
          (F ‖p‖ * (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
            Work.SmallBoxTBWord.tBamp χ p V j x).re)
    rw [MeasureTheory.integral_const_mul]
  have hR : (∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ *
        (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
          (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
            Work.SmallBoxTBWord.tBamp χ p V j x).re))
      = ∫ p : EuclideanSpace ℝ (Fin 3),
          ∫ x : Submission.BoseGases.X n, f p x ∂ν ∂volume := by
    rw [hν]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    rw [hf]
    change F ‖p‖ * (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
          (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
            Work.SmallBoxTBWord.tBamp χ p V j x).re)
      = ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
          (F ‖p‖ * (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
            Work.SmallBoxTBWord.tBamp χ p V j x).re)
    rw [show (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
          (F ‖p‖ * (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
            Work.SmallBoxTBWord.tBamp χ p V j x).re))
        = ∫ x in Submission.BoseGases.abox n ℓ, F ‖p‖ *
            (Work.BoseKinLoc.indU ℓ 0 (x j) *
              (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
                Work.SmallBoxTBWord.tBamp χ p V j x).re) from by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          ring]
    rw [MeasureTheory.integral_const_mul]
  calc (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
        (∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ *
          (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
            Work.SmallBoxTBWord.tBamp χ p V j x).re))
      = ∫ x : Submission.BoseGases.X n,
          ∫ p : EuclideanSpace ℝ (Fin 3), f p x ∂volume ∂ν := hL
    _ = ∫ p : EuclideanSpace ℝ (Fin 3),
          ∫ x : Submission.BoseGases.X n, f p x ∂ν ∂volume := hswap.symm
    _ = ∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ *
          (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
            (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
              Work.SmallBoxTBWord.tBamp χ p V j x).re) := hR.symm

/-! ## The pointwise polarisation of `mainWord` is symmetric in its two arguments -/

/-- The pointwise polarisation of `mainWord` at the two slot-`j` fibres is symmetric under the
exchange of the two states, because `Re(star z · w)` is symmetric.  Both `aQ ℓ j`-invariance
hypotheses are needed only to keep the two states of the `tBamp` pairing fixed along the use of
`polar_mainWord_fibre`. -/
lemma mainWord_fibre_swap_at {ℓ d s εT : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    (x : Submission.BoseGases.X n) {W V : Submission.BoseGases.X n → ℝ}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hWj : Submission.BoseGases.aQ ℓ j W = W) (hVj : Submission.BoseGases.aQ ℓ j V = V) :
    Work.BoseKinLoc.mainWord ℓ d s εT 0
        (fun z => Work.BoseKinLoc.fibre n j W x z + Work.BoseKinLoc.fibre n j V x z)
      - Work.BoseKinLoc.mainWord ℓ d s εT 0
        (fun z => Work.BoseKinLoc.fibre n j W x z - Work.BoseKinLoc.fibre n j V x z)
    = Work.BoseKinLoc.mainWord ℓ d s εT 0
        (fun z => Work.BoseKinLoc.fibre n j V x z + Work.BoseKinLoc.fibre n j W x z)
      - Work.BoseKinLoc.mainWord ℓ d s εT 0
        (fun z => Work.BoseKinLoc.fibre n j V x z - Work.BoseKinLoc.fibre n j W x z) := by
  rw [polar_mainWord_fibre (Ψ := W) (Ψ' := V) hℓ j hW hV x,
    polar_mainWord_fibre (Ψ := V) (Ψ' := W) hℓ j hV hW x, hWj, hVj]
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  rw [re_star_mul_comm]

/-! ## The slot step -/

/-- **The slot step.**  If `W` is mean-free in the slot `k` and `V` is independent of the slot
`k` (with `k ≠ j`, and both fixed by `aQ ℓ j`), then the box integral of the polarised word
vanishes. -/
theorem mainWord_slot_step {ℓ d s εT : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {j k : Fin n} (hjk : j ≠ k)
    {W V : Submission.BoseGases.X n → ℝ} (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hWj : Submission.BoseGases.aQ ℓ j W = W)
    (hVj : Submission.BoseGases.aQ ℓ j V = V)
    (hfree : ∀ y : Submission.BoseGases.X n,
      (1 / ℓ ^ 3) * ∫ w in Submission.BoseGases.acube ℓ, W (Function.update y k w) = 0)
    (hconst : ∀ (y : Submission.BoseGases.X n) (w : EuclideanSpace ℝ (Fin 3)),
      V (Function.update y k w) = V y) :
    (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
      (Work.BoseKinLoc.mainWord ℓ d s εT 0
          (fun z => Work.BoseKinLoc.fibre n j W x z + Work.BoseKinLoc.fibre n j V x z)
        - Work.BoseKinLoc.mainWord ℓ d s εT 0
          (fun z => Work.BoseKinLoc.fibre n j W x z - Work.BoseKinLoc.fibre n j V x z))) = 0 := by
  -- the weight of the polarised momentum integral
  set F : ℝ → ℝ := fun r => (1 - εT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) r
      + εT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) r with hF
  set K : ℝ := |1 - εT| * (1 + |(2 * (s * ℓ))⁻¹|) ^ 2
      + |εT| * (1 + |(2 * (d * s * ℓ))⁻¹|) ^ 2 with hK
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  have hFbd : ∀ r : ℝ, 0 ≤ r → |F r| ≤ K * (1 + r) ^ 2 := by
    intro r hr
    have h1 := fsKinCoeff_le_bound (c := (2 * (s * ℓ))⁻¹) hr
    have h2 := fsKinCoeff_le_bound (c := (2 * (d * s * ℓ))⁻¹) hr
    have h3 : (0 : ℝ) ≤ Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) r :=
      Submission.BoseGases.fsKinCoeff_nonneg _ _
    have h4 : (0 : ℝ) ≤ Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) r :=
      Submission.BoseGases.fsKinCoeff_nonneg _ _
    rw [hF, hK]
    calc |(1 - εT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) r
            + εT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) r|
        ≤ |(1 - εT) * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) r|
            + |εT * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) r| := abs_add_le _ _
      _ = |1 - εT| * Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) r
            + |εT| * Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) r := by
          rw [abs_mul, abs_mul, abs_of_nonneg h3, abs_of_nonneg h4]
      _ ≤ |1 - εT| * ((1 + |(2 * (s * ℓ))⁻¹|) ^ 2 * (1 + r) ^ 2)
            + |εT| * ((1 + |(2 * (d * s * ℓ))⁻¹|) ^ 2 * (1 + r) ^ 2) := by
          exact add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
      _ = (|1 - εT| * (1 + |(2 * (s * ℓ))⁻¹|) ^ 2
            + |εT| * (1 + |(2 * (d * s * ℓ))⁻¹|) ^ 2) * (1 + r) ^ 2 := by ring
  have hFm : Measurable F := by
    rw [hF]
    have hc : ∀ c : ℝ, Measurable fun r : ℝ => Submission.BoseGases.fsKinCoeff c r := by
      intro c
      rw [show Submission.BoseGases.fsKinCoeff c
          = fun r : ℝ => (max (r - c) 0) ^ 2 from rfl]
      fun_prop
    exact ((measurable_const.mul (hc _)).add (measurable_const.mul (hc _)))
  -- pointwise polarisation, and the `aQ`-invariance of the two states
  have hpt : ∀ x : Submission.BoseGases.X n,
      Work.BoseKinLoc.mainWord ℓ d s εT 0
          (fun z => Work.BoseKinLoc.fibre n j W x z + Work.BoseKinLoc.fibre n j V x z)
        - Work.BoseKinLoc.mainWord ℓ d s εT 0
          (fun z => Work.BoseKinLoc.fibre n j W x z - Work.BoseKinLoc.fibre n j V x z)
      = 4 * ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ *
            (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p W j x) *
              Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p V j x).re := by
    intro x
    rw [polar_mainWord_fibre (Ψ := W) (Ψ' := V) hℓ j hW hV x, hWj, hVj, hF]
  rw [show (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
        (Work.BoseKinLoc.mainWord ℓ d s εT 0
            (fun z => Work.BoseKinLoc.fibre n j W x z + Work.BoseKinLoc.fibre n j V x z)
          - Work.BoseKinLoc.mainWord ℓ d s εT 0
            (fun z => Work.BoseKinLoc.fibre n j W x z - Work.BoseKinLoc.fibre n j V x z)))
      = ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
          (4 * ((2 * Real.pi) ^ 3)⁻¹ *
            ∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ *
              (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p W j x) *
                Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p V j x).re)
      from by
        apply integral_congr_ae
        filter_upwards with x
        rw [hpt x]]
  -- pull the constant `4(2π)^{-3}` out of the configuration integral
  rw [show (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
        (4 * ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ *
            (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p W j x) *
              Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p V j x).re))
      = 4 * ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
            (∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ *
              (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p W j x) *
                Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p V j x).re)
      from by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        ring]
  -- exchange the momentum integral with the configuration integral
  rw [swap_p_abox_pair_fubini (ℓ := ℓ) (j := j) hℓ hKnn hFm hFbd hW hV]
  -- for each momentum the inner box integral vanishes
  rw [show (∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ *
        (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
          (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p W j x) *
            Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p V j x).re))
      = ∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ * 0
      from by
        apply integral_congr_ae
        filter_upwards with p
        rw [tBamp_pair_fixed_p_zero (ℓ := ℓ) (j := j) (k := k) hℓ hjk hW.continuous hV.continuous
          (box_meanFree_mul_const_eq_zero (j := j) (k := k) hℓ hjk hW.continuous hV.continuous
            hfree hconst) p]]
  simp

/-! ## The target -/

theorem mainWord_fibre_offdiag {ℓ d s εT : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {S T : Finset ℕ} (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n) (hjS : (j : ℕ) ∈ S) (hjT : (j : ℕ) ∈ T) (hST : S ≠ T) : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) * (Work.BoseKinLoc.mainWord ℓ d s εT 0 (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ + Work.BoseFixB2.jointProj ℓ T Φ) x) - Work.BoseKinLoc.mainWord ℓ d s εT 0 (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ - Work.BoseFixB2.jointProj ℓ T Φ) x))) = 0 := by
  -- a slot `< n` in which the two sectors differ
  obtain ⟨k, hkST⟩ : ∃ k : ℕ, (k ∈ S ∧ k ∉ T) ∨ (k ∈ T ∧ k ∉ S) := by
    by_contra h
    push Not at h
    exact hST (Finset.ext fun k => ⟨fun hkS => (h k).1 hkS, fun hkT => (h k).2 hkT⟩)
  have hkn : k < n := by
    rcases hkST with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Finset.mem_range.mp (hS h1)
    · exact Finset.mem_range.mp (hT h1)
  have hkj : k ≠ (j : ℕ) := by
    rcases hkST with ⟨-, h2⟩ | ⟨-, h2⟩
    · intro hc; exact h2 (hc ▸ hjT)
    · intro hc; exact h2 (hc ▸ hjS)
  have hjk : j ≠ (⟨k, hkn⟩ : Fin n) := fun hc => hkj (congrArg Fin.val hc).symm
  -- the two sectors are smooth
  have hWcd : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB2.jointProj ℓ S Φ) :=
    Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ
  have hVcd : ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB2.jointProj ℓ T Φ) :=
    Work.BoseFixB2.Sector.jointProj_contDiff hℓ T hΦ
  -- and fixed by the slot-`j` complement projection (`j` lies in both sectors)
  have hWj : Submission.BoseGases.aQ ℓ j (Work.BoseFixB2.jointProj ℓ S Φ)
      = Work.BoseFixB2.jointProj ℓ S Φ := by
    have h := Work.BoseFixB2.Sector.aP_blockOp_eq_zero hℓ j.isLt hjS hΦ.continuous
    funext x
    simp only [Submission.BoseGases.aQ]
    rw [congrFun h x]
    simp
  have hVj : Submission.BoseGases.aQ ℓ j (Work.BoseFixB2.jointProj ℓ T Φ)
      = Work.BoseFixB2.jointProj ℓ T Φ := by
    have h := Work.BoseFixB2.Sector.aP_blockOp_eq_zero hℓ j.isLt hjT hΦ.continuous
    funext x
    simp only [Submission.BoseGases.aQ]
    rw [congrFun h x]
    simp
  rcases hkST with ⟨hkS, hkT⟩ | ⟨hkT, hkS⟩
  · -- `k ∈ S \ T`: `E_SΦ` is mean-free in the slot `k`, `E_TΦ` is independent of it
    have hfree : ∀ y : Submission.BoseGases.X n,
        (1 / ℓ ^ 3) * ∫ w in Submission.BoseGases.acube ℓ,
          (Work.BoseFixB2.jointProj ℓ S Φ) (Function.update y ⟨k, hkn⟩ w) = 0 := by
      have h := Work.BoseFixB2.Sector.aP_blockOp_eq_zero hℓ hkn hkS hΦ.continuous
      intro y
      simpa [Submission.BoseGases.aP] using congrFun h y
    have hconst : ∀ (y : Submission.BoseGases.X n) (w : EuclideanSpace ℝ (Fin 3)),
        (Work.BoseFixB2.jointProj ℓ T Φ) (Function.update y ⟨k, hkn⟩ w)
          = (Work.BoseFixB2.jointProj ℓ T Φ) y :=
      fun y w => Work.BoseFixB2.Sector.constIn_jointProj hℓ hkn hkT hΦ.continuous y w
    exact mainWord_slot_step (W := Work.BoseFixB2.jointProj ℓ S Φ)
      (V := Work.BoseFixB2.jointProj ℓ T Φ) hℓ hjk hWcd hVcd hWj hVj hfree hconst
  · -- `k ∈ T \ S`: the roles of the two sectors are exchanged
    have hfree : ∀ y : Submission.BoseGases.X n,
        (1 / ℓ ^ 3) * ∫ w in Submission.BoseGases.acube ℓ,
          (Work.BoseFixB2.jointProj ℓ T Φ) (Function.update y ⟨k, hkn⟩ w) = 0 := by
      have h := Work.BoseFixB2.Sector.aP_blockOp_eq_zero hℓ hkn hkT hΦ.continuous
      intro y
      simpa [Submission.BoseGases.aP] using congrFun h y
    have hconst : ∀ (y : Submission.BoseGases.X n) (w : EuclideanSpace ℝ (Fin 3)),
        (Work.BoseFixB2.jointProj ℓ S Φ) (Function.update y ⟨k, hkn⟩ w)
          = (Work.BoseFixB2.jointProj ℓ S Φ) y :=
      fun y w => Work.BoseFixB2.Sector.constIn_jointProj hℓ hkn hkS hΦ.continuous y w
    -- rewrite the goal into the exchanged orientation, then apply the slot step
    rw [show (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
          (Work.BoseKinLoc.mainWord ℓ d s εT 0
              (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ
                + Work.BoseFixB2.jointProj ℓ T Φ) x)
            - Work.BoseKinLoc.mainWord ℓ d s εT 0
              (Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ
                - Work.BoseFixB2.jointProj ℓ T Φ) x)))
        = ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
            (Work.BoseKinLoc.mainWord ℓ d s εT 0
                (fun z => Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x z
                  + Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x z)
              - Work.BoseKinLoc.mainWord ℓ d s εT 0
                (fun z => Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x z
                  - Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x z))
        from by
          apply integral_congr_ae
          filter_upwards with x
          rw [show Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ
                + Work.BoseFixB2.jointProj ℓ T Φ) x
              = fun z => Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x z
                + Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x z from rfl,
            show Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ
                - Work.BoseFixB2.jointProj ℓ T Φ) x
              = fun z => Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ S Φ) x z
                - Work.BoseKinLoc.fibre n j (Work.BoseFixB2.jointProj ℓ T Φ) x z from rfl,
            mainWord_fibre_swap_at (ℓ := ℓ) (d := d) (s := s) (εT := εT) hℓ j x hWcd hVcd hWj hVj]]
    exact mainWord_slot_step (W := Work.BoseFixB2.jointProj ℓ T Φ)
      (V := Work.BoseFixB2.jointProj ℓ S Φ) hℓ hjk hVcd hWcd hVj hWj hfree hconst

end Work.Analysis.BoseBand
