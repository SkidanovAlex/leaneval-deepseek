import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1B.tendsto_cutProd_mass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.tendsto_qLHSwordB_cutProd`

The **potential-word convergence** along the smooth product approximants of the sharp box state:

    qLHSwordB h M L d μ u (∏ᵢγ_δ(xᵢ)·ψ)  ⟶  qLHSwordB h M L d μ u (1_{B(u)^k}·ψ)   (δ → 0⁺).

This is the potential-half of `Work.BoseFixB1B.fibreWord_tendsto_cutProd` (the sliding word
`fibreWord` is `tBwordBInd + qLHSwordB`), and the exact input that
`Work.BoseFixB1B.sharpCountCoreAt_of_tendsto` consumes in its `hconv` slot.

The proof is the same *pointwise* mechanism as `Work.BoseFixB1B.tendsto_cutProd_mass`: off the
finite union of coordinate hyperplanes (a Lebesgue-null set, `volume_goodCollar_compl`) the product
approximant is *eventually equal* to the sharp state, so the squared modulus converges pointwise
(`tendsto_cutProd_sq_pointwise`); the density `qLHSden` is `L¹` on the box by hypothesis, so
dominated convergence applies with the dominating function `Cb²·|qLHSden|`
(`0 ≤ (∏γ)² ≤ 1_{B^k}` and `|ψ| ≤ Cb` on the box give `|cutProd| ≤ Cb`).

The first ingredient is that `qLHSwordB` *is* the box integral of `Φ²·qLHSden` (definitional,
`qLHSwordB_eq_qLHSden_integral`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`qLHSwordB` as the box integral of the diagonal density.**  The corpus localised potential
word is the `abox`-integral of `Φ²` times the diagonal density `qLHSden` (this is definitional:
`qLHSword`'s body is the same parenthesised expression that `qLHSden` names). -/
theorem qLHSwordB_eq_qLHSden_integral {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (M k : ℕ) (L d μ : ℝ) (u : E3) (Φ : Submission.BoseGases.X k → ℝ) :
    Work.SmallBoxSliding.qLHSwordB h M L d μ u Φ
      = ∫ x in Submission.BoseGases.abox k L, (Φ x) ^ 2 *
          Submission.BoseGases.qLHSden k L μ (Submission.BoseGases.wSmallPair M L d u v)
            (Submission.BoseGases.wSmall1Pair h M L d u) x := by
  rw [Work.SmallBoxSliding.qLHSwordB, Submission.BoseGases.qLHSword]
  simp only [Submission.BoseGases.qLHSden]

theorem tendsto_qLHSwordB_cutProd {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (M k : ℕ) (L d μ : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    {ψ : Submission.BoseGases.X k → ℝ} {K Cb : ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hL : 0 < L) (hd : 0 < d) (hcut : Work.BoseFixB1B.IsCutFamily L d u K γ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hCb : 0 ≤ Cb)
    (hψb : ∀ x ∈ Submission.BoseGases.abox k L, |ψ x| ≤ Cb)
    (hpot : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X k =>
        Submission.BoseGases.qLHSden k L μ (Submission.BoseGases.wSmallPair M L d u v)
          (Submission.BoseGases.wSmall1Pair h M L d u) x) (Submission.BoseGases.abox k L)) :
    Filter.Tendsto (fun δ : ℝ => Work.SmallBoxSliding.qLHSwordB h M L d μ u
        (Work.BoseFixB1B.cutProd (γ δ) ψ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (Work.SmallBoxSliding.qLHSwordB h M L d μ u
        (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ))) := by
  classical
  obtain ⟨hK, hcutδ⟩ := hcut
  -- the box is measurable, hence a.e. membership is available
  have haboxm : MeasurableSet (Submission.BoseGases.abox k L) :=
    (Submission.BoseGases.abox_isClosed k L).measurableSet
  -- the cut family: support, values in `[0,1]`, and `= 1` off the `δ`-collar
  have hγsupp : ∀ δ : ℝ, 0 < δ → ∀ y, γ δ y ≠ 0 → y ∈ Submission.BoseGases.dlBox L d u :=
    fun δ hδ y hy => (hcutδ δ hδ).2.1 (subset_tsupport _ (Function.mem_support.mpr hy))
  have hγone : ∀ δ : ℝ, 0 < δ → ∀ y, Work.BoseFixB1B.boxMargin L d u y ≥ δ → γ δ y = 1 :=
    fun δ hδ => (hcutδ δ hδ).2.2.2.1
  have hγ01 : ∀ δ : ℝ, 0 < δ → ∀ y, 0 ≤ γ δ y ∧ γ δ y ≤ 1 :=
    fun δ hδ => (hcutδ δ hδ).2.2.1
  -- the density is `L¹` on the box (hypothesis), hence its modulus is integrable
  have hfabs : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X k => |Submission.BoseGases.qLHSden k L μ
        (Submission.BoseGases.wSmallPair M L d u v)
        (Submission.BoseGases.wSmall1Pair h M L d u) x|)
      ((volume : Measure (Submission.BoseGases.X k)).restrict (Submission.BoseGases.abox k L)) :=
    hpot.abs
  -- the uniform bound `|cutProd γ ψ| ≤ Cb` on the box
  have hcutCb : ∀ δ : ℝ, 0 < δ → ∀ x ∈ Submission.BoseGases.abox k L,
      (Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2 ≤ Cb ^ 2 := by
    intro δ hδ x hx
    refine le_trans (Work.BoseFixB1B.cutProd_sq_le_sharp (hγ01 δ hδ)
      (hcutδ δ hδ).2.1 x) ?_
    by_cases hall : ∀ i : Fin k, x i ∈ Submission.BoseGases.dlBox L d u
    · rw [Work.BoseFixB1B.sharpState_eq_self_of_mem hall]
      calc (ψ x) ^ 2 = |ψ x| ^ 2 := by rw [sq_abs]
        _ ≤ Cb ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hψb x hx) 2
    · rw [Work.BoseFixB1B.sharpState_eq_zero_of_notMem hall]
      simpa using sq_nonneg Cb
  -- the pointwise domination by `Cb²|qLHSden|`
  have hbound : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X k)).restrict
        (Submission.BoseGases.abox k L)),
      ‖(Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2 *
        Submission.BoseGases.qLHSden k L μ (Submission.BoseGases.wSmallPair M L d u v)
          (Submission.BoseGases.wSmall1Pair h M L d u) x‖
      ≤ Cb ^ 2 * |Submission.BoseGases.qLHSden k L μ (Submission.BoseGases.wSmallPair M L d u v)
          (Submission.BoseGases.wSmall1Pair h M L d u) x| := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_restrict_mem haboxm] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right (hcutCb δ hδ x hx) (abs_nonneg _)
  -- the integrands are a.e. strongly measurable
  have hmeas : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      AEStronglyMeasurable (fun x : Submission.BoseGases.X k =>
        (Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2 *
        Submission.BoseGases.qLHSden k L μ (Submission.BoseGases.wSmallPair M L d u v)
          (Submission.BoseGases.wSmall1Pair h M L d u) x)
      ((volume : Measure (Submission.BoseGases.X k)).restrict (Submission.BoseGases.abox k L)) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hprod : Continuous (fun x : Submission.BoseGases.X k => ∏ i : Fin k, γ δ (x i)) :=
      continuous_finsetProd (Finset.univ : Finset (Fin k))
        (fun i _ => (hcutδ δ hδ).1.continuous.comp (continuous_apply i))
    exact ((hprod.mul hψ.continuous).pow 2).aestronglyMeasurable.mul hpot.aestronglyMeasurable
  -- the bad configurations (a coordinate on a face) are null
  have hnull : (volume : Measure (Submission.BoseGases.X k))
      {x : Submission.BoseGases.X k | ¬ Work.BoseFixB1B.GoodCollar L d u x} = 0 :=
    Work.BoseFixB1B.volume_goodCollar_compl (k := k) (L := L) (d := d) u
  have hae : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X k)).restrict
      (Submission.BoseGases.abox k L)), Work.BoseFixB1B.GoodCollar L d u x := by
    rw [MeasureTheory.ae_iff]
    exact le_antisymm (le_trans (Measure.restrict_apply_le _ _) hnull.le) bot_le
  -- pointwise convergence of the integrands at a.e. `x`
  have hlim : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X k)).restrict
      (Submission.BoseGases.abox k L)),
      Filter.Tendsto (fun δ : ℝ => (Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2 *
          Submission.BoseGases.qLHSden k L μ (Submission.BoseGases.wSmallPair M L d u v)
            (Submission.BoseGases.wSmall1Pair h M L d u) x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ x) ^ 2 *
          Submission.BoseGases.qLHSden k L μ (Submission.BoseGases.wSmallPair M L d u v)
            (Submission.BoseGases.wSmall1Pair h M L d u) x)) := by
    filter_upwards [hae] with x hx
    exact (Work.BoseFixB1B.tendsto_cutProd_sq_pointwise hγsupp hγone hx).mul_const _
  -- dominated convergence
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (Submission.BoseGases.X k)).restrict (Submission.BoseGases.abox k L))
    (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (F := fun δ x => (Work.BoseFixB1B.cutProd (γ δ) ψ x) ^ 2 *
        Submission.BoseGases.qLHSden k L μ (Submission.BoseGases.wSmallPair M L d u v)
          (Submission.BoseGases.wSmall1Pair h M L d u) x)
    (f := fun x => (Work.BoseFixB1B.sharpBoxState (Submission.BoseGases.dlBox L d u) ψ x) ^ 2 *
        Submission.BoseGases.qLHSden k L μ (Submission.BoseGases.wSmallPair M L d u v)
          (Submission.BoseGases.wSmall1Pair h M L d u) x)
    (fun x => Cb ^ 2 * |Submission.BoseGases.qLHSden k L μ
          (Submission.BoseGases.wSmallPair M L d u v)
          (Submission.BoseGases.wSmall1Pair h M L d u) x|)
    hmeas hbound (hfabs.const_mul _) hlim
  simpa only [qLHSwordB_eq_qLHSden_integral] using hDCT

end Work.BoseFixB1B

end
