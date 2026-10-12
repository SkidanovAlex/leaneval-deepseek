import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseFixR.KinSplit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.KinFibreMarginal`

**The *marginal* integrability of the two blocks of the box-restricted kinetic word.**

`Work.BoseFixR.KinSplit` proves the splitting identity

`kinFormB (k+j) ℓ d s ε_T b Φ = ∫_{abox j ℓ} kinFormB k … (bfL Φ y)
                              + ∫_{abox k ℓ} kinFormB j … (bfR Φ z)`

which is an identity of *numbers*; the two integrals on the right are therefore only well
behaved if the two marginal functions `y ↦ kinFormB k … (bfL Φ y)` and
`z ↦ kinFormB j … (bfR Φ z)` are integrable over their respective boxes.  That is what is
proved here, **without any hypothesis on the kinetic parameters** other than `0 < ℓ` (and
without any support or boundedness hypothesis on `Φ` beyond smoothness).

The mechanism is Fubini, **not** continuity (the kinetic word `fsT` is a quadratic form whose
symbol grows at infinity, so it is not continuous in the state for any topology that a merely
smooth state would supply):

* the first-block slot aggregate `kinIntL` — the sum of the slot integrands of the
  `(k+j)`-particle word over the first block of slots — is integrable on `abox (k+j) ℓ` for a
  *merely smooth* state, by `Work.BoseFixR.integrableOn_fsT_fibre`;
* along the block equivalence `blockME k j : X k × X j ≃ᵐ X (k+j)` (measure preserving, with
  `blockME k j '' (abox k ℓ ×ˢ abox j ℓ) = abox (k+j) ℓ`) this integrability transfers to the
  product of the two restricted boxes, and Mathlib's Fubini marginal theorem
  (`MeasureTheory.Integrable.integral_prod_right` / `_left`) makes the marginal integrable;
* the marginal is `ℓ⁻³` times `kinFormB k … (bfL Φ ·)`: this is `kinFormB_blockL` (from
  `KinSplit`), together with the fibre identities `fibre_blockME_castAdd` /
  `fibre_blockME_natAdd` and the fact that the anchored window `indU ℓ 0` is `1` on the box.

## Contents

* `kinIntL`, `kinIntR` — the two slot aggregates of the `(k+j)`-word;
* `integrableOn_kinIntL`, `integrableOn_kinIntR` — their integrability on the full box;
* `integrable_marginal_blockME` — the Fubini marginal lemma;
* `integral_kinIntL_blockME`, `integral_kinIntR_blockME` — the marginal is `ℓ³` times the
  block word;
* `kinFibreMarginal_general`, and the target `KinFibreMarginal`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixR

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The two slot aggregates of the `(k+j)`-word -/

/-- **The first-block slot aggregate** of the `(k+j)`-particle kinetic word: the sum of the
slot integrands of `Work.BoseKinLoc.kinFormB (k+j)`, over the slots `i < k`, written in terms
of the concatenated configuration (the `i`-th slot update being expressed through the block
equivalence). -/
def kinIntL (k j : ℕ) (ℓ d s eT b : ℝ) (Φ : Submission.BoseGases.X (k + j) → ℝ) :
    Submission.BoseGases.X (k + j) → ℝ :=
  fun x => ∑ i : Fin k, Work.BoseKinLoc.indU ℓ 0 (x (Fin.castAdd j i))
    * Work.BoseKinLoc.fsT ℓ d s eT b 0
        (Work.BoseKinLoc.fibre (k + j) (Fin.castAdd j i) Φ x)

/-- **The second-block slot aggregate** of the `(k+j)`-particle kinetic word: the sum of the
slot integrands of `Work.BoseKinLoc.kinFormB (k+j)` over the slots `k ≤ i < k+j`. -/
def kinIntR (k j : ℕ) (ℓ d s eT b : ℝ) (Φ : Submission.BoseGases.X (k + j) → ℝ) :
    Submission.BoseGases.X (k + j) → ℝ :=
  fun x => ∑ i : Fin j, Work.BoseKinLoc.indU ℓ 0 (x (Fin.natAdd k i))
    * Work.BoseKinLoc.fsT ℓ d s eT b 0
        (Work.BoseKinLoc.fibre (k + j) (Fin.natAdd k i) Φ x)

/-! ## 2. Integrability of the slot aggregates on the box -/

/-- **The first-block slot aggregate is integrable on the full box**, for a merely smooth
state: on the box the anchored window is `1`, so this is the finite sum of the slot
integrabilities `Work.BoseFixR.integrableOn_fsT_fibre`. -/
lemma integrableOn_kinIntL {k j : ℕ} {ℓ d s eT b : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    MeasureTheory.IntegrableOn (kinIntL k j ℓ d s eT b Φ)
      (Submission.BoseGases.abox (k + j) ℓ) := by
  have hSum : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (k + j) =>
      ∑ i : Fin k, Work.BoseKinLoc.fsT ℓ d s eT b 0
        (Work.BoseKinLoc.fibre (k + j) (Fin.castAdd j i) Φ x))
      (Submission.BoseGases.abox (k + j) ℓ) :=
    integrable_finsetSum Finset.univ
      (fun i _ => integrableOn_fsT_fibre hℓ hΦ (Fin.castAdd j i))
  refine hSum.congr_fun (fun x hx => ?_) (Submission.BoseGases.abox_measurable (k + j) ℓ)
  simp only [kinIntL]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [indU_zero_eq_one_of_mem_abox hx (Fin.castAdd j i), one_mul]

/-- **The second-block slot aggregate is integrable on the full box.** -/
lemma integrableOn_kinIntR {k j : ℕ} {ℓ d s eT b : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    MeasureTheory.IntegrableOn (kinIntR k j ℓ d s eT b Φ)
      (Submission.BoseGases.abox (k + j) ℓ) := by
  have hSum : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (k + j) =>
      ∑ i : Fin j, Work.BoseKinLoc.fsT ℓ d s eT b 0
        (Work.BoseKinLoc.fibre (k + j) (Fin.natAdd k i) Φ x))
      (Submission.BoseGases.abox (k + j) ℓ) :=
    integrable_finsetSum Finset.univ
      (fun i _ => integrableOn_fsT_fibre hℓ hΦ (Fin.natAdd k i))
  refine hSum.congr_fun (fun x hx => ?_) (Submission.BoseGases.abox_measurable (k + j) ℓ)
  simp only [kinIntR]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [indU_zero_eq_one_of_mem_abox hx (Fin.natAdd k i), one_mul]

/-! ## 3. The Fubini marginal lemma -/

/-- **Fubini marginal of an integrable function of the concatenated configuration.**  If `G`
is integrable on the full configuration box, then both of its marginals along the block
equivalence `blockME k j` are integrable over the corresponding box: the `y`-marginal is the
integral over `z ∈ abox k ℓ` and lives on `abox j ℓ`, and dually. -/
lemma integrable_marginal_blockME {k j : ℕ} {ℓ : ℝ} {G : Submission.BoseGases.X (k + j) → ℝ}
    (hG : MeasureTheory.IntegrableOn G (Submission.BoseGases.abox (k + j) ℓ)) :
    MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
        ∫ z in Submission.BoseGases.abox k ℓ, G (blockME k j (z, y)))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox j ℓ))
    ∧ MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
        ∫ y in Submission.BoseGases.abox j ℓ, G (blockME k j (z, y)))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ)) := by
  -- the product-space integrability of `G ∘ blockME`
  have hGp : MeasureTheory.IntegrableOn (fun p : Submission.BoseGases.X k ×
      Submission.BoseGases.X j => G (blockME k j p))
      (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ) := by
    have h := (measurePreserving_blockME k j).integrableOn_image
      (MeasurableEquiv.measurableEmbedding (blockME k j)) (f := G)
      (s := Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ)
    rw [blockME_image_abox] at h
    exact h.mp hG
  -- the restricted product measure is the product of the restricted measures
  have hm : (volume : Measure (Submission.BoseGases.X k × Submission.BoseGases.X j)).restrict
        (Submission.BoseGases.abox k ℓ ×ˢ Submission.BoseGases.abox j ℓ)
      = ((volume : Measure (Submission.BoseGases.X k)).restrict
            (Submission.BoseGases.abox k ℓ)).prod
        ((volume : Measure (Submission.BoseGases.X j)).restrict
          (Submission.BoseGases.abox j ℓ)) := by
    rw [show (volume : Measure (Submission.BoseGases.X k × Submission.BoseGases.X j))
        = (volume : Measure (Submission.BoseGases.X k)).prod
          (volume : Measure (Submission.BoseGases.X j)) from rfl]
    exact (Measure.prod_restrict _ _).symm
  have hGprod : MeasureTheory.Integrable (fun p : Submission.BoseGases.X k ×
      Submission.BoseGases.X j => G (blockME k j p))
      (((volume : Measure (Submission.BoseGases.X k)).restrict
          (Submission.BoseGases.abox k ℓ)).prod
        ((volume : Measure (Submission.BoseGases.X j)).restrict
          (Submission.BoseGases.abox j ℓ))) := by
    rw [← hm]
    exact hGp
  exact ⟨hGprod.integral_prod_right, hGprod.integral_prod_left⟩

/-! ## 4. The marginal is `ℓ³` times the block word -/

/-- **The `y`-marginal of the first-block slot aggregate is `ℓ³` times the first block word.**
This is `Work.BoseFixR.kinFormB_blockL` (the inner-integral identity of `KinSplit`) combined
with the slot identities `blockME_castAdd`, `fibre_blockME_castAdd` and `indU ℓ 0 = 1` on the
box. -/
lemma integral_kinIntL_blockME {k j : ℕ} {ℓ d s eT b : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (y : Submission.BoseGases.X j) :
    (∫ z in Submission.BoseGases.abox k ℓ, kinIntL k j ℓ d s eT b Φ (blockME k j (z, y)))
      = ℓ ^ (3 : ℤ) * Work.BoseKinLoc.kinFormB k ℓ d s eT b (bfL Φ y) := by
  rw [← kinFormB_blockL (k := k) (j := j) hℓ hΦ y]
  refine setIntegral_congr_fun (Submission.BoseGases.abox_measurable k ℓ) (fun z hz => ?_)
  simp only [kinIntL]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [blockME_castAdd, fibre_blockME_castAdd,
    indU_zero_eq_one_of_mem_abox hz i, one_mul]

/-- **The `z`-marginal of the second-block slot aggregate is `ℓ³` times the second block
word** (`Work.BoseFixR.kinFormB_blockR`, dually). -/
lemma integral_kinIntR_blockME {k j : ℕ} {ℓ d s eT b : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (z : Submission.BoseGases.X k) :
    (∫ y in Submission.BoseGases.abox j ℓ, kinIntR k j ℓ d s eT b Φ (blockME k j (z, y)))
      = ℓ ^ (3 : ℤ) * Work.BoseKinLoc.kinFormB j ℓ d s eT b (bfR Φ z) := by
  rw [← kinFormB_blockR (k := k) (j := j) hℓ hΦ z]
  refine setIntegral_congr_fun (Submission.BoseGases.abox_measurable j ℓ) (fun y hy => ?_)
  simp only [kinIntR]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [blockME_natAdd, fibre_blockME_natAdd,
    indU_zero_eq_one_of_mem_abox hy i, one_mul]

/-! ## 5. The theorem -/

/-- **The marginal integrability of the two blocks of the box-restricted kinetic word**, in
free-parameter form (`ℓ, d, s, ε_T, b` arbitrary real parameters, `0 < ℓ` the only
hypothesis). -/
theorem kinFibreMarginal_general {k j : ℕ} {ℓ d s eT b : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
        Work.BoseKinLoc.kinFormB k ℓ d s eT b (bfL Φ y))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox j ℓ))
    ∧ MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
        Work.BoseKinLoc.kinFormB j ℓ d s eT b (bfR Φ z))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox k ℓ)) := by
  constructor
  · have hmarg := (integrable_marginal_blockME (k := k) (j := j) (ℓ := ℓ)
      (G := kinIntL k j ℓ d s eT b Φ) (integrableOn_kinIntL hℓ hΦ)).1
    refine (hmarg.const_mul (ℓ ^ (-3 : ℤ))).congr ?_
    filter_upwards with y
    rw [integral_kinIntL_blockME hℓ hΦ y]
    exact zpow_neg_three_mul_left hℓ _
  · have hmarg := (integrable_marginal_blockME (k := k) (j := j) (ℓ := ℓ)
      (G := kinIntR k j ℓ d s eT b Φ) (integrableOn_kinIntR hℓ hΦ)).2
    refine (hmarg.const_mul (ℓ ^ (-3 : ℤ))).congr ?_
    filter_upwards with z
    rw [integral_kinIntR_blockME hℓ hΦ z]
    exact zpow_neg_three_mul_left hℓ _

theorem KinFibreMarginal {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    {k j : ℕ} {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    MeasureTheory.Integrable (fun y : Submission.BoseGases.X j =>
        Work.BoseKinLoc.kinFormB k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Work.BoseFixR.bfL Φ y))
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.abox j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))
    ∧ MeasureTheory.Integrable (fun z : Submission.BoseGases.X k =>
        Work.BoseKinLoc.kinFormB j (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b (Work.BoseFixR.bfR Φ z))
      (MeasureTheory.volume.restrict
        (Submission.BoseGases.abox k (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))) :=
  kinFibreMarginal_general (k := k) (j := j)
    (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (s := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
    (eT := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (b := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b) hℓ hΦ

end Work.BoseFixR
