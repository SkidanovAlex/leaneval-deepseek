import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.aemeasurable_boxQInd_sliding
import Submission.Work.BoseFixB1.sbWord_marginal_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.integrableHalvesB1`

The `u`-marginal integrability of the **two halves** of FS `eq:appTB`'s sliding small-box
kinetic word `𝒯_{B(u)}` (`Work.UBBInputs8.tBwordBInd`), at FS's parameters
`ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`, `ε = ε_T`, `c = (dsℓ)⁻¹`
(`Work.BoseFixB1.sbCut`), on the one-particle sector `N = 1`.

The two halves are

* the **gap half** `½ε_T(1+π⁻²)⁻¹(dℓ)⁻²·n₊(B(u))` — the coefficient
  `Work.SmallBoxTBWord.tbGapCoeff (ℓ d) ε_T` times the FS-faithful excited count
  `Work.UBBInputs8.cnPlusBoxInd` over the sliding boxes `B(u) = dlBox ℓ d u`;
* the **spectral half** `Q_{B(u)}χ_{B(u)}[√−Δ−c]₊²χ_{B(u)}Q_{B(u)}` — the FS-faithful `p`-diagonal
  form `Work.UBBInputs8.tBdiagFormInd` with the symbol
  `Submission.BoseGases.fsKinCoeff c = [·−c]₊²`.

Integrability of the *sum* of the two halves is already known:
`Work.BoseFixB1.integrable_tBwordBInd` (for **every** smooth state, at any `ℓ > 0`, `d > 0`).
The point of the present file is that — at `N = 1`, and only there — the two halves can be
separated *out of* that sum, because each of them is nonnegative and the excited-count half is
a.e. strongly measurable in `u`.  The separation is what a consumer needs who has to bound the
gap term and the spectral term by different constants.

## The argument (three steps)

1. **Nonnegativity.**  `tBwordBInd 1 ℓ d ε c u φ` is, *definitionally*, the sum of the two halves
   (`tBwordBInd_one_eq_halves`); both halves are `≥ 0` for `0 ≤ ε` and `ℓ > 0`
   (`tbGapHalf_nonneg`, `tBdiagHalf_nonneg`): the gap coefficient is `≥ 0`
   (`SmallBoxTBWord.tbGapCoeff_nonneg`), the excited count is a sum of integrals of squares, and
   the spectral symbol `fsKinCoeff c` is `≥ 0` with a nonnegative slot normalisation `(ℓ³)⁻¹`.
   Hence for every `u`
   `‖gap half u‖ = gap half u ≤ gap half u + diag half u = ‖tBwordBInd … u φ‖`.

2. **Measurability of the gap half.**  `cnPlusBoxInd ℓ A volA φ` at `N = 1` is the `x`-integral
   over `abox 1 ℓ` of `(boxQInd volA A 0 φ ·)²` (`Fin.sum_univ_one`).  The `(u,x)`-integrand is
   `AEMeasurable` for `volume.prod volume` — this is `Work.BoseFixB1.aemeasurable_boxQInd_sliding`
   (joint measurability of FS's box projection along the sliding family `B(u)`, which needs no
   integrability hypothesis at all) — so the parametric-integral lemma
   `MeasureTheory.AEStronglyMeasurable.integral_prod_right'` makes the `u`-marginal
   a.e. strongly measurable (`aestronglyMeasurable_cnPlusBoxInd_sliding`).

3. **Separation.**  `MeasureTheory.Integrable.mono` with the sum as dominating function gives the
   integrability of the gap half, and then the spectral half is the difference
   `tBwordBInd − gap half` (`MeasureTheory.Integrable.sub`).

The diluteness threshold `ε₀` in the requested statement is therefore *free*: no diluteness is
used anywhere (only `0 < sideAt μ (a v)`, `0 < d`, `0 ≤ ε_T`, all of which follow from
`Adm v ε₀ μ` for **any** `ε₀`), so `ε₀ = 1` works.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## 1.  The definitional split of the sliding word at `N = 1` -/

/-- **`𝒯_{B(u)}` at `N = 1` is the sum of its two halves**, definitionally: the gap half
`tbGapCoeff (ℓ d) ε · cnPlusBoxInd` and the spectral half `tBdiagFormInd … (fsKinCoeff c)`. -/
lemma tBwordBInd_one_eq_halves {ℓ d ε c : ℝ} (u : EuclideanSpace ℝ (Fin 3))
    (φ : Submission.BoseGases.X 1 → ℝ) :
    Work.UBBInputs8.tBwordBInd 1 ℓ d ε c u φ
      = Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε *
            Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Work.SmallBoxSliding.boxMass ℓ d u) φ
        + Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u)
            (Submission.BoseGases.fsKinCoeff c) φ := rfl

/-! ## 2.  Nonnegativity of the two halves -/

/-- **The gap half is nonnegative** for `0 ≤ ε`: a nonnegative coefficient times a sum of
integrals of squares. -/
lemma tbGapHalf_nonneg {ℓ d ε : ℝ} (hε : 0 ≤ ε) (u : EuclideanSpace ℝ (Fin 3))
    (φ : Submission.BoseGases.X 1 → ℝ) :
    0 ≤ Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε *
      Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) φ := by
  refine mul_nonneg (Work.SmallBoxTBWord.tbGapCoeff_nonneg hε) ?_
  simp only [Work.UBBInputs8.cnPlusBoxInd]
  exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _

/-- **The spectral half is nonnegative** for `ℓ > 0`: the symbol `fsKinCoeff c = [·−c]₊²` is
nonnegative and the slot normalisation `(ℓ³)⁻¹` is nonnegative. -/
lemma tBdiagHalf_nonneg {ℓ d c : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    (φ : Submission.BoseGases.X 1 → ℝ) :
    0 ≤ Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u)
      (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u)
      (Submission.BoseGases.fsKinCoeff c) φ := by
  simp only [Work.UBBInputs8.tBdiagFormInd]
  refine Finset.sum_nonneg fun i _ => ?_
  refine mul_nonneg (le_of_lt Work.SmallBoxTBWord.twoPiInv3_pos) ?_
  refine integral_nonneg fun p => mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖) ?_
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hℓ.le 3)) (integral_nonneg fun x => sq_nonneg _)

/-! ## 3.  Measurability of the excited-count half in `u` -/

/-- **The sliding excited count is a.e. strongly measurable in the sliding parameter.**  At
`N = 1` the count is the `x`-integral of the square of FS's box projection, whose
`(u,x)`-joint measurability is `Work.BoseFixB1.aemeasurable_boxQInd_sliding`; the parametric
integral lemma turns that into measurability of the `u`-marginal. -/
lemma aestronglyMeasurable_cnPlusBoxInd_sliding {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {φ : Submission.BoseGases.X 1 → ℝ} (hφ : Continuous φ) :
    MeasureTheory.AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) φ) MeasureTheory.volume := by
  classical
  have h0 : AEMeasurable (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X 1 =>
      Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d q.1)
        (Submission.BoseGases.dlBox ℓ d q.1) 0 φ q.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    Work.BoseFixB1.aemeasurable_boxQInd_sliding hℓ hd hφ 0
  have hset : MeasurableSet {q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X 1 |
      q.2 ∈ Submission.BoseGases.abox 1 ℓ} :=
    (Submission.BoseGases.abox_measurable 1 ℓ).preimage measurable_snd
  -- the box indicator of `abox 1 ℓ`, in the `(u,x)`-product, makes the joint integrand measurable
  have hEq : (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X 1 =>
        (Submission.BoseGases.abox 1 ℓ).indicator
          (fun y : Submission.BoseGases.X 1 =>
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d q.1)
              (Submission.BoseGases.dlBox ℓ d q.1) 0 φ y) ^ 2) q.2)
      = {q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X 1 |
          q.2 ∈ Submission.BoseGases.abox 1 ℓ}.indicator
          (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X 1 =>
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d q.1)
              (Submission.BoseGases.dlBox ℓ d q.1) 0 φ q.2) ^ 2) := by
    funext q
    by_cases h : q.2 ∈ Submission.BoseGases.abox 1 ℓ
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show q ∈
        {q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X 1 |
          q.2 ∈ Submission.BoseGases.abox 1 ℓ} from h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show q ∉
        {q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X 1 |
          q.2 ∈ Submission.BoseGases.abox 1 ℓ} from h)]
  have hjoint : AEMeasurable (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X 1 =>
        (Submission.BoseGases.abox 1 ℓ).indicator
          (fun y : Submission.BoseGases.X 1 =>
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d q.1)
              (Submission.BoseGases.dlBox ℓ d q.1) 0 φ y) ^ 2) q.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    rw [hEq]
    exact (h0.pow_const 2).indicator hset
  have hint : MeasureTheory.AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      ∫ x : Submission.BoseGases.X 1,
        (Submission.BoseGases.abox 1 ℓ).indicator
          (fun y : Submission.BoseGases.X 1 =>
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) 0 φ y) ^ 2) x) MeasureTheory.volume :=
    hjoint.aestronglyMeasurable.integral_prod_right'
  refine hint.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only []
  rw [MeasureTheory.integral_indicator (Submission.BoseGases.abox_measurable 1 ℓ)]
  simp [Work.UBBInputs8.cnPlusBoxInd]

/-! ## 4.  The general integrability lemma -/

/-- **The two halves of FS `eq:appTB`'s sliding word are `u`-integrable**, for every `ℓ > 0`,
`d > 0`, `0 ≤ ε`, every real `c`, and every smooth one-particle state `φ`.

The sum of the halves is `Work.BoseFixB1.integrable_tBwordBInd`; the gap half is dominated by the
sum (both halves are nonnegative) and is a.e. strongly measurable
(`aestronglyMeasurable_cnPlusBoxInd_sliding`), so it is integrable
(`MeasureTheory.Integrable.mono`); the spectral half is then the difference
(`MeasureTheory.Integrable.sub`). -/
theorem integrable_halves_general {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hε : 0 ≤ ε)
    {φ : Submission.BoseGases.X 1 → ℝ} (hφ : ContDiff ℝ (⊤ : ENat) φ) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε *
          Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Work.SmallBoxSliding.boxMass ℓ d u) φ) ∧
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u)
          (Submission.BoseGases.fsKinCoeff c) φ) := by
  classical
  -- the two halves sum to the sliding word, which is integrable
  have hsum : MeasureTheory.Integrable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.UBBInputs8.tBwordBInd 1 ℓ d ε c u φ) :=
    Work.BoseFixB1.integrable_tBwordBInd (ℓ := ℓ) (d := d) (ε := ε) (c := c) (N := 1) hℓ hd hφ
  -- nonnegativity of both halves
  have hgap_nn : ∀ u : EuclideanSpace ℝ (Fin 3),
      0 ≤ Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε *
        Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) φ :=
    fun u => tbGapHalf_nonneg hε u φ
  have hdiag_nn : ∀ u : EuclideanSpace ℝ (Fin 3),
      0 ≤ Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u)
        (Submission.BoseGases.fsKinCoeff c) φ :=
    fun u => tBdiagHalf_nonneg hℓ u φ
  -- the gap half is dominated by the sum
  have hgap : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.SmallBoxTBWord.tbGapCoeff (ℓ * d) ε *
        Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) φ) :=
    hsum.mono
      ((aestronglyMeasurable_cnPlusBoxInd_sliding hℓ hd hφ.continuous).const_mul _)
      (Filter.Eventually.of_forall fun u => by
        rw [tBwordBInd_one_eq_halves u φ, Real.norm_of_nonneg (hgap_nn u),
          Real.norm_of_nonneg (add_nonneg (hgap_nn u) (hdiag_nn u))]
        linarith [hdiag_nn u])
  -- the spectral half is the difference
  have hdiag : MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u)
        (Submission.BoseGases.fsKinCoeff c) φ) :=
    (hsum.sub hgap).congr (Filter.Eventually.of_forall fun u => by
      rw [Pi.sub_apply, tBwordBInd_one_eq_halves u φ]
      ring)
  exact ⟨hgap, hdiag⟩

/-! ## 5.  The requested theorem -/

theorem integrableHalvesB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ φ : Submission.BoseGases.X 1 → ℝ, ContDiff ℝ (⊤ : ENat) φ →
      MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
          Work.SmallBoxTBWord.tbGapCoeff
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT *
          Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) φ) ∧
      MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
          Work.UBBInputs8.tBdiagFormInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))) φ) := by
  refine ⟨1, one_pos, fun μ hAdm φ hφ => ?_⟩
  exact integrable_halves_general (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (ε := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (c := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
    (Work.BoseFixB1.adm_ell_pos hAdm) (Work.BoseFixB1.adm_d_pos hAdm)
    (Work.BoseFixB1.adm_eT_bounds hAdm).1 hφ

end Work.BoseFixB1S
