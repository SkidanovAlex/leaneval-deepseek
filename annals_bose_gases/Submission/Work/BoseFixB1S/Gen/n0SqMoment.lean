import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.Gen.n0FunOpSqrtPairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S.Gen

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The bridge: the quadratic form of the `n₀` functional calculus over the subset
idempotents -/

/-- **The quadratic form of the functional calculus.**  For a continuous state `Φ` and an arbitrary
scalar weight `g`,

  `∫_{abox N ℓ} (g(n₀)Φ)·Φ  =  Σ_{S} g (|S|) · ∫_{abox N ℓ} (P_S Φ)²`.

`g(n₀)Φ = Σ_S g(|S|)·P_SΦ` pointwise (`n0FunOp_eq_sum_card`); integrating against `Φ` and
expanding the finite sum (`abox_integral_mul_finset_sum`) reduces the left-hand side to
`Σ_S g(|S|)·∫Φ·P_SΦ`, and `∫Φ·P_SΦ = ∫(P_SΦ)²` is the diagonal pairing of the orthogonal
projection `P_S` (`n0ProjOp_pairing_diag_mixed`, self-adjointness + idempotence). -/
theorem n0FunOp_quadform {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (g : ℝ → ℝ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.n0FunOp volA A g Φ x * Φ x)
      = ∑ S : Finset (Fin N), g (S.card : ℝ)
          * ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.n0ProjOp volA A S Φ x) ^ 2 := by
  have hΦG : Work.BoseFixB1S.GoodState ℓ Φ := Work.BoseFixB1S.BoxNice.of_continuous hℓ hΦc
  have hSG : ∀ S : Finset (Fin N),
      Work.BoseFixB1S.GoodState ℓ (Work.BoseFixB1S.n0ProjOp volA A S Φ) :=
    fun S => Work.BoseFixB1S.n0ProjOp_goodStateB1 hℓ hvol hA hvolA hAc hΦG S
  -- integrability of `Φ · P_S Φ` on the box
  have hInt : ∀ S : Finset (Fin N), IntegrableOn
      (fun x : Submission.BoseGases.X N => Φ x * Work.BoseFixB1S.n0ProjOp volA A S Φ x)
      (Submission.BoseGases.abox N ℓ) volume := fun S =>
    integrableOn_mul_of_bound hℓ hΦG.1 (hSG S).1 hΦG.2.choose_spec (hSG S).2.choose_spec
  -- the pointwise expansion of the functional calculus
  have hfac : ∀ x : Submission.BoseGases.X N,
      Work.BoseFixB1S.n0FunOp volA A g Φ x
        = ∑ S : Finset (Fin N), g (S.card : ℝ) * Work.BoseFixB1S.n0ProjOp volA A S Φ x :=
    fun x => congrFun (Work.BoseFixB1S.n0FunOp_eq_sum_card volA A g Φ) x
  have hpt : (fun x : Submission.BoseGases.X N =>
        Work.BoseFixB1S.n0FunOp volA A g Φ x * Φ x)
      = fun x : Submission.BoseGases.X N => Φ x
          * ∑ S : Finset (Fin N),
              g (S.card : ℝ) * Work.BoseFixB1S.n0ProjOp volA A S Φ x := by
    funext x
    rw [hfac x, mul_comm]
  rw [hpt, Work.BoseFixB1S.abox_integral_mul_finset_sum Finset.univ Φ
      (fun S : Finset (Fin N) => g (S.card : ℝ))
      (fun S : Finset (Fin N) => Work.BoseFixB1S.n0ProjOp volA A S Φ)
      (fun S _ => hInt S)]
  -- term by term: `∫ Φ·P_SΦ = ∫ (P_SΦ)²`
  refine Finset.sum_congr rfl (fun S _ => ?_)
  congr 1
  rw [show (∫ x in Submission.BoseGases.abox N ℓ,
          Φ x * Work.BoseFixB1S.n0ProjOp volA A S Φ x)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            Work.BoseFixB1S.n0ProjOp volA A S Φ x * Φ x from by
      apply integral_congr_ae
      filter_upwards with x
      ring]
  rw [n0ProjOp_pairing_diag_mixed hℓ hvol hA hvolA hAc hΦG hΦG S]
  apply integral_congr_ae
  filter_upwards with x
  rw [sq]

/-! ## 2. The elementary splitting of the quadratic weight -/

/-- `(|S| + 1 − m)² = |S|² + 2(1 − m)|S| + (1 − m)²` summed against the spectral weights. -/
private theorem sum_quad_split_measure {N : ℕ} {ℓ volA : ℝ} (A : Set E3)
    (Φ : Submission.BoseGases.X N → ℝ) (m : ℝ) :
    (∑ S : Finset (Fin N), (fun r : ℝ => (r + 1 - m) ^ 2) (S.card : ℝ)
        * ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.n0ProjOp volA A S Φ x) ^ 2)
      = (∑ S : Finset (Fin N), ((S.card : ℝ) ^ 2)
            * ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.n0ProjOp volA A S Φ x) ^ 2)
        + 2 * (1 - m) * (∑ S : Finset (Fin N), (S.card : ℝ)
            * ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.n0ProjOp volA A S Φ x) ^ 2)
        + (1 - m) ^ 2 * (∑ S : Finset (Fin N),
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.n0ProjOp volA A S Φ x) ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  ring

/-! ## 3. The target -/

theorem n0SqMoment {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {m : ℝ} (hm : 0 ≤ m)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Φ x * Work.BoseFixB1S.n0FunOp volA A (fun r => (r + 1 - m) ^ 2) Φ x)
      = (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
            + Work.BoseFixB1S.boxPairCount volA ℓ A Φ)
          + 2 * (1 - m) * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
          + (1 - m) ^ 2 * (∫ x in Submission.BoseGases.abox N ℓ, Φ x ^ 2) := by
  have hq := n0FunOp_quadform hℓ hvol hA hvolA hAc (fun r : ℝ => (r + 1 - m) ^ 2) hΦc
  rw [show (∫ x in Submission.BoseGases.abox N ℓ,
          Φ x * Work.BoseFixB1S.n0FunOp volA A (fun r => (r + 1 - m) ^ 2) Φ x)
        = ∫ x in Submission.BoseGases.abox N ℓ,
            Work.BoseFixB1S.n0FunOp volA A (fun r => (r + 1 - m) ^ 2) Φ x * Φ x from by
      apply integral_congr_ae
      filter_upwards with x
      ring]
  rw [hq, sum_quad_split_measure A Φ m,
    Work.BoseFixB1S.n0Moments_threeB1 hℓ hvol hA hvolA hAc hΦc,
    Work.BoseFixB1S.n0Moments_twoB1 hℓ hvol hA hvolA hAc hΦc,
    Work.BoseFixB1S.n0Moments_oneB1 hℓ hvol hA hvolA hAc hΦc]

end Work.BoseFixB1S.Gen
