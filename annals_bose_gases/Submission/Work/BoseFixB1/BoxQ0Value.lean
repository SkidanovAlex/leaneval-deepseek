import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxQIndCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The box-projected `Q₀`-value (rung 2 of the box-projected chapter)

`Work.BoseFixB1S.boxQ0` (the condensate word at FS's own box projections `P_{B(u),i}`) is
*exactly* the flat-condensate form: the two-slot and one-slot peels
`Work.BoseFixB1S.Q0C.pair_value` / `Work.BoseFixB1S.Q0C.one_value` (proved in
`Submission/Work/BoseFixB1S/BoxQIndCore.lean`) give, term by term,

    ∫(P_iP_jΦ)² · w₂(xᵢ,xⱼ) = (∬_{A×A}w₂/volA²)·∫(P_iP_jΦ)² ,
    ∫(P_iΦ)² · w₁-fibre(xᵢ)  = (∫_A w₁-fibre/volA)·∫(P_iΦ)² ,

so summing over the pairs and the slots yields the value identity below.  This is the
box-projection analogue of the proved `Work.BoseFixB1.q0word_localised_value`
(which is the same computation at the centred-cube projections), and it is the input of the
box-projected `A₀` step (`a0MainLoc`-form).  Nothing here is delegated: it is the finite-sum
bookkeeping on top of the two proved peels. -/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The box-projected `A₀`-main term** — `Work.BoseFixB1.a0MainLoc` with the box volume
`volA` in place of `ℓ³` in every normalisation (FS's `A₀` uses the *box* density `n₀/|B|`, and
the box projections `boxPInd` average over `A` of volume `volA`):

    a0MainLocBox volA μ M₁ S
      = ¼(S/volA − μ)²·M₁ − ½μ²·M₁ − (M₁/(2volA))·(2S/volA + μ) − M₁/(4volA²) ,

i.e. the mean-field square at the box density `S/volA` minus the `½μ²` background, with the
`n₀ ↔ n₀+1`/`1/V` defects that `Q₀`'s exact value (rung 2, `boxQ0_value`) actually produces. -/
noncomputable def a0MainLocBox (volA μ M₁ S : ℝ) : ℝ :=
  (1 / 4) * (S / volA - μ) ^ 2 * M₁
    - (1 / 2) * μ ^ 2 * M₁
    - (M₁ / (2 * volA)) * (2 * (S / volA) + μ)
    - M₁ / (4 * volA ^ 2)

/-- **The box-projected `Q₀`-value.**  For any kernel pair `w₁,w₂` integrable on the box product
(with `w₁`'s fibre integrable on `A`),

    boxQ0 volA ℓ μ A w₁ w₂ Φ
      = ½(∬_{A×A}w₂/volA²)·boxPairCount − μ(∫_A w₁fibre/volA)·boxFlatCount . -/
theorem boxQ0_value {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w1 w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw2i : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => w2 p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure
        (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))).restrict (A ×ˢ A)))
    (hfib : MeasureTheory.IntegrableOn
      (fun z : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.w1Fibre ℓ w1 z) A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    Work.BoseFixB1S.boxQ0 volA ℓ μ A w1 w2 Φ
      = (1 / 2) * (Work.BoseFixB1S.boxM2 volA A w2 / volA ^ 2)
          * Work.BoseFixB1S.boxPairCount volA ℓ A Φ
        - μ * (Work.BoseFixB1S.boxM1 ℓ A w1 / volA)
          * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ := by
  have hpair : (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2
            * w2 (x p.1) (x p.2))
      = (Work.BoseFixB1S.boxM2 volA A w2 / volA ^ 2)
        * (∑ p ∈ Submission.BoseGases.pairSet N,
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A p.1
                (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hne : p.1 ≠ p.2 := by
      have hp' := hp
      simp only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ,
        true_and] at hp'
      exact hp'
    exact Work.BoseFixB1S.Q0C.pair_value hℓ hvol hA hvolA hAc hne hw2i hΦc
  have hone : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
          * Submission.BoseGases.w1Fibre ℓ w1 (x i))
      = (Work.BoseFixB1S.boxM1 ℓ A w1 / volA)
        * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Work.BoseFixB1S.Q0C.one_value hℓ hvol hA hvolA hAc i hfib hΦc
  rw [Work.BoseFixB1S.boxQ0, Work.BoseFixB1S.boxPairCount, Work.BoseFixB1S.boxFlatCount,
    hpair, hone]
  ring

end Work.BoseFixB1
