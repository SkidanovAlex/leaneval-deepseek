import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.frameSmear
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

/-- **The slot means of distinct slots commute, under the bare `L¹` hypothesis.**

The corpus statements (`Submission.BoseGases.aP_comm` for *continuous* states,
`Work.BoseBoxFock.Weak.aP_comm` for *measurable, bounded* states) both supply the
integrability needed for the Fubini step from extra hypotheses on `Φ`.  Here the
integrability is assumed *directly*, in exactly the form in which the Fubini step
consumes it: the joint function

    `p ↦ Φ (x[i ↦ p.1][j ↦ p.2])`

is integrable for the product of the two centred-cube measures.  That is the only
hypothesis the proof needs; the whole content is the definitional unfolding of the
two iterated slot means followed by Fubini (`integral_integral_swap`), the two
orders being identified by `Function.update_comm` (`i ≠ j`). -/
theorem aP_comm_of_integrable {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X n → ℝ} (x : Submission.BoseGases.X n)
    (h : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Φ (Function.update (Function.update x i p.1) j p.2))
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)))) :
    Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x
      = Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x := by
  let μ' : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)) :=
    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
      (Submission.BoseGases.acube ℓ)
  let G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun y z => Φ (Function.update (Function.update x i y) j z)
  -- the integrability hypothesis, in the form the Fubini lemma wants
  have hGint : Integrable (Function.uncurry G) (μ'.prod μ') := h
  -- the two updated configurations agree (`i ≠ j`)
  have hGsymm : ∀ y z : EuclideanSpace ℝ (Fin 3),
      G y z = Φ (Function.update (Function.update x j z) i y) := by
    intro y z
    dsimp only [G]
    congr 1
    rw [Function.update_comm hij]
  -- Fubini: swapping the order of the two slot integrals
  have hswap : (∫ y : EuclideanSpace ℝ (Fin 3), ∫ z : EuclideanSpace ℝ (Fin 3), G y z ∂μ' ∂μ')
      = ∫ z : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3), G y z ∂μ' ∂μ' :=
    integral_integral_swap hGint
  -- unfold the left-hand iterated slot mean
  have hL : Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x
      = (1 / ℓ ^ 3) * ((1 / ℓ ^ 3) *
          ∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ, G y z) := by
    simp only [Submission.BoseGases.aP]
    rw [MeasureTheory.integral_const_mul]
  -- the second slot integral of the *right* order, rewritten into `G`
  have hfun_eq : (fun z : EuclideanSpace ℝ (Fin 3) => ∫ y in Submission.BoseGases.acube ℓ,
        Φ (Function.update (Function.update x j z) i y))
      = fun z : EuclideanSpace ℝ (Fin 3) =>
          ∫ y in Submission.BoseGases.acube ℓ, G y z := by
    funext z
    refine integral_congr_ae ?_
    filter_upwards with y
    exact (hGsymm y z).symm
  -- unfold the right-hand iterated slot mean
  have hR : Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x
      = (1 / ℓ ^ 3) * ((1 / ℓ ^ 3) *
          ∫ z in Submission.BoseGases.acube ℓ, ∫ y in Submission.BoseGases.acube ℓ, G y z) := by
    simp only [Submission.BoseGases.aP]
    rw [MeasureTheory.integral_const_mul, hfun_eq]
  rw [hL, hR, hswap]

end Work.BoseBoxFock.PCFU
