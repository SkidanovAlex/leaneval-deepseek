import ChallengeDeps
import Submission.Work.BoseFixB1.boxPIndFibreMassB1
import Submission.Work.BoseFixB1S.boxPInd_fib_collapse
import Submission.Work.BoseFixB1S.mfRows
import Submission.Work.BoseFixB1S.mf_boxQ0_integrable_inputs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.mfMuManifestPart` — the `μ`-part of the manifest sum

The `μ`-line of the sliding-box potential word, in the `mf`-vocabulary of
`Submission.Work.BoseFixB1S.mfRows`: the integral of `Φ²` against the slot sum of the fibre
weights `w1Fibre` is

  `- μ·(M₁/|B(u)|)·S - 2μ·(fibre `QP`-line) - μ·(fibre `Q`-line)`,

with `S = mfS = Σᵢ∫(PᵢΦ)²` the localised flat count and `M₁/|B(u)| = mfM1/mfV` the fibre
box average.  This is the `μ`-part of `Work.BoseFixB1S.mfQSumManifestEq`.

The proof composes two independent facts.

* `Work.BoseFixB1M.muPart_dlBox` (the localised one-body word at the box projections): the
  integral is `-μ·(Σᵢ∫(PᵢΦ)²fib + 2Σᵢ∫(QᵢΦ)(PᵢΦ)fib + Σᵢ∫(QᵢΦ)²fib)`, from the *pointwise*
  resolution `Φ² = (PᵢΦ + QᵢΦ)²` in each slot (no state-support hypothesis is needed: both
  sides vanish off the box, where the fibre is zero).
* the fibre collapse `Work.BoseFixB1S.boxPInd_fib_collapse` (conjunct 1) — the box projection
  is `1_A(xᵢ)` times a slot-`i`-independent mean, so the slot fibre is peeled off and replaced
  by its box average `(1/|A|)∫_A fib = M₁/mfV`:
  `Σᵢ∫(PᵢΦ)²fib = (mfM1/mfV)·mfS`.  The fibre's integrability on the sliding box is
  `Work.BoseFixB1S.mf_boxQ0_integrable_inputs`.

The two `Q`-lines are definitional, so the remaining difference is the arithmetic identity
`-μ((M₁/V)S + 2X + Y) = -μ(M₁/V)S - 2μX - μY`.
-/

namespace Work.BoseFixB1S

set_option linter.unusedVariables false

open MeasureTheory

theorem mfMuManifestPart {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v)
    {μ : ℝ} (hμ : 0 ≤ μ)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (hR : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < mfV v μ u)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Φ x) ^ 2 * (- μ * ∑ i : Fin n,
          Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (boxW1 h μ u) (x i)))
      = - μ * (mfM1 h μ u / mfV v μ u) * mfS v μ n Φ u
        - 2 * μ * mfFibQP h μ n Φ u - μ * mfFibQ h μ n Φ u := by
  classical
  -- the regularity index of the sliding box is the fixed `mValue ≥ 1`
  have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  -- the fibre of the localised one-body kernel is integrable on the sliding box
  have hfib : MeasureTheory.IntegrableOn
      (fun z => Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (boxW1 h μ u) z) (boxA v μ u) :=
    (Work.BoseFixB1S.mf_boxQ0_integrable_inputs h hv hv1 hvrad hR0 hv_supp hℓ hd hR hRχ).2
  -- `mfV` is the measure of the sliding box
  have hvolA : mfV v μ u =
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real
        (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) := by
    rw [mfV, Work.SmallBoxSliding.boxMass_eq_measureReal]
  -- ### 1. the `P`-side fibre collapse: `Σᵢ∫(PᵢΦ)²fib = (M₁/V)·S`
  have hP : (∑ i : Fin n, boxMuP (mfV v μ u) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (boxA v μ u) (boxW1 h μ u) Φ i)
      = (mfM1 h μ u / mfV v μ u) * mfS v μ n Φ u := by
    have h0 := (Work.BoseFixB1S.boxPInd_fib_collapse (N := n)
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (volA := mfV v μ u)
      hℓ hvol
      (Work.SmallBoxSliding.measurableSet_dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (Work.SmallBoxSliding.dlBox_subset_acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      hvolA hΦc
      (fib := fun z => Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (boxW1 h μ u) z) hfib).1
    simp only [boxMuP, boxA]
    rw [h0]
    simp only [mfS, mfM1, boxM1, boxFlatCount, mfV, boxA]
    ring
  -- ### 2. the two `Q`-lines are definitional
  have hQ : (∑ i : Fin n, boxMuQ (mfV v μ u) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (boxA v μ u) (boxW1 h μ u) Φ i) = mfFibQ h μ n Φ u := rfl
  have hQP : (∑ i : Fin n, boxMuQP (mfV v μ u) (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (boxA v μ u) (boxW1 h μ u) Φ i) = mfFibQP h μ n Φ u := rfl
  -- ### 3. the localised one-body word at the box projections
  have hmu : (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Φ x) ^ 2 * (- μ * ∑ i : Fin n,
          Submission.BoseGases.w1Fibre (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (boxW1 h μ u) (x i)))
      = - μ * ((∑ i : Fin n, boxMuP (mfV v μ u)
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (boxA v μ u) (boxW1 h μ u) Φ i)
        + 2 * (∑ i : Fin n, boxMuQP (mfV v μ u)
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (boxA v μ u) (boxW1 h μ u) Φ i)
        + (∑ i : Fin n, boxMuQ (mfV v μ u)
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (boxA v μ u) (boxW1 h μ u) Φ i)) :=
    Work.BoseFixB1M.muPart_dlBox (v := v) (R0 := R) (μ := μ) hv_supp hR0 hv hvrad hv1 h hM1
      hℓ hd hR hRχ u hvol hΦc
  -- ### 4. assembly
  rw [hmu, hQP, hP, hQ]
  ring

end Work.BoseFixB1S
