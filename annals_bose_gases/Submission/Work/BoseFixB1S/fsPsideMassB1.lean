import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.Gen.n0SqMoment
import Submission.Work.BoseFixB1S.n0Op_quadform_sum_pInd_sq
import Submission.Work.BoseFixB1S.n0PairingSumNice
import Submission.Work.BoseFixB1S.n0PairingZeroNice
import Submission.Work.BoseFixB1S.n0ProjOpBoxPIndB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators ENNReal

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# `Submission.Work.BoseFixB1S.fsPsideMassB1`

**The `P`-side mass identity for the `n₀` functional calculus.**  For the FS box projections
`P_{B,i} = UBBInputs8.boxPInd volA A i` (`eq:HBU`) and the functional calculus `n0FunOp volA A g`
of the condensate-count operator `n₀ = Σᵢ P_{B,i}`,

  `Σᵢ ∫_{abox N ℓ} (g(n₀)(P_{B,i}Φ))²  =  ∫_{abox N ℓ} (r g(r)²)(n₀)Φ · Φ`.

## Math

Writing `P_S := n0ProjOp volA A S` for the subset idempotents of the commuting projections `P_{B,i}`
and `u_S := P_S Φ`, the functional calculus is the finite spectral combination
`g(n₀) = Σ_S g(|S|) P_S` (`n0FunOp_eq_sum_card`).  Since the `P_S` are orthogonal projections
(idempotence, orthogonality and self-adjointness on the box: `n0ProjOpOrthB1`), the square of the
calculus expands into its diagonal:

  `∫ (g(n₀)Ψ)² = Σ_S g(|S|)² · ∫ (P_SΨ)²`     (`n0FunOp_sqB1`).

Applying this to `Ψ = P_{B,i}Φ` and using the slot collapse
`P_S (P_{B,i}Φ) = 1_S(i)·P_SΦ` on the box (`n0ProjOpBoxPIndB1`) gives

  `Σᵢ ∫ (g(n₀)(P_{B,i}Φ))² = Σᵢ Σ_S g(|S|)² · 1_S(i) · ∫(P_SΦ)²
                            = Σ_S |S| g(|S|)² · ∫(P_SΦ)²`,

the inner sum over `i` contributing exactly the multiplicity `|S|`.  The right-hand side is the same
spectral sum, because the *quadratic form* of the calculus is diagonal in the same way
(`Gen.n0FunOp_quadform`):  `∫ ((r g(r)²)(n₀)Φ)·Φ = Σ_S |S| g(|S|)² ∫(P_SΦ)²`.
-/

/-- **The square form of the `n₀` functional calculus.**  For a state `Ψ` measurable and bounded on
the analysis box (`GoodState`) and an arbitrary scalar weight `g`, the box integral of the square of
`g(n₀)Ψ` is the diagonal of the spectral decomposition:

  `∫_{abox N ℓ} (g(n₀)Ψ)² = Σ_S g(|S|)² · ∫_{abox N ℓ} (P_S Ψ)²`.

This is the general-weight companion of `n0Sqrt_quadform_good` (whose weight is `√(·+1)`): expand
`g(n₀)Ψ = Σ_S g(|S|)·P_SΨ` (`n0FunOp_eq_sum_card`), square the finite sum
(`abox_integral_sq_finset_sum`), and kill the off-diagonal pairings by the orthogonality of the
subset idempotents (`Gen.n0ProjOp_pairing_zero_mixed`). -/
theorem n0FunOp_sqB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (g : ℝ → ℝ) {Ψ : X N → ℝ} (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ) :
    (∫ x in abox N ℓ, (Work.BoseFixB1S.n0FunOp volA A g Ψ x) ^ 2)
      = ∑ S : Finset (Fin N), (g (S.card : ℝ)) ^ 2
          * ∫ x in abox N ℓ, (Work.BoseFixB1S.n0ProjOp volA A S Ψ x) ^ 2 := by
  classical
  have hvolA' : volA = (MeasureTheory.volume : MeasureTheory.Measure E3).real A := by
    rw [MeasureTheory.Measure.real_def]
    exact hvolA
  have hexp : ∀ x : X N, Work.BoseFixB1S.n0FunOp volA A g Ψ x
      = ∑ S : Finset (Fin N), g (S.card : ℝ) * Work.BoseFixB1S.n0ProjOp volA A S Ψ x :=
    fun x => congrFun (Work.BoseFixB1S.n0FunOp_eq_sum_card volA A g Ψ) x
  have hint : ∀ S T : Finset (Fin N), IntegrableOn
      (fun x : X N => Work.BoseFixB1S.n0ProjOp volA A S Ψ x
        * Work.BoseFixB1S.n0ProjOp volA A T Ψ x) (abox N ℓ) volume :=
    fun S T => Work.BoseFixB1S.n0ProjOp_pairing_integrableB1 hℓ hvol hA hvolA hAc hΨ S T
  have hpt : (fun x : X N => (Work.BoseFixB1S.n0FunOp volA A g Ψ x) ^ 2)
      = fun x : X N => (∑ S : Finset (Fin N),
          g (S.card : ℝ) * Work.BoseFixB1S.n0ProjOp volA A S Ψ x) ^ 2 := by
    funext x
    rw [hexp x]
  rw [hpt, Work.BoseFixB1S.abox_integral_sq_finset_sum Finset.univ
      (fun S : Finset (Fin N) => g (S.card : ℝ))
      (fun S : Finset (Fin N) => Work.BoseFixB1S.n0ProjOp volA A S Ψ)
      (fun i _ j _ => hint i j)]
  rw [Work.BoseFixB1S.sum_sum_eq_diag Finset.univ
      (fun i j : Finset (Fin N) => g (i.card : ℝ) * g (j.card : ℝ)
        * ∫ x in abox N ℓ,
            Work.BoseFixB1S.n0ProjOp volA A i Ψ x * Work.BoseFixB1S.n0ProjOp volA A j Ψ x)
      (fun i _ j _ hij => by
        rw [Work.BoseFixB1S.Gen.n0ProjOp_pairing_zero_mixed hℓ hvol hA hvolA' hAc hΨ hΨ hij,
          mul_zero])]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [show (∫ x in abox N ℓ,
        Work.BoseFixB1S.n0ProjOp volA A S Ψ x * Work.BoseFixB1S.n0ProjOp volA A S Ψ x)
      = ∫ x in abox N ℓ, (Work.BoseFixB1S.n0ProjOp volA A S Ψ x) ^ 2 from by
    apply integral_congr_ae
    filter_upwards with x
    rw [sq]]
  ring

/-- The multiplicity reindexing: summing the weight `c` over the slots of `S` gives `|S|·c`. -/
private theorem sum_ite_mem_mul {N : ℕ} (S : Finset (Fin N)) (c v : ℝ) :
    (∑ i : Fin N, c * (if i ∈ S then v else 0)) = c * ((S.card : ℝ) * v) := by
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

theorem fsPsideMassB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (g : ℝ → ℝ) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp volA A g (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.n0FunOp volA A (fun r : ℝ => r * (g r) ^ 2) Φ x) * Φ x := by
  classical
  obtain ⟨C, _hC0, hCb⟩ := Work.BoseFixB1S.exists_abox_bound hℓ hΦc
  have hΦG : Work.BoseFixB1S.GoodState ℓ Φ := ⟨hΦc.measurable, C, hCb⟩
  -- ## Step 1: expand each summand of the left-hand side over the spectral decomposition
  have hstep : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.n0FunOp volA A g
            (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2)
        = ∑ S : Finset (Fin N), (g (S.card : ℝ)) ^ 2
            * (if i ∈ S then
                ∫ x in Submission.BoseGases.abox N ℓ,
                  (Work.BoseFixB1S.n0ProjOp volA A S Φ x) ^ 2
              else 0) := by
    intro i
    rw [Work.BoseFixB1S.n0FunOp_sqB1 hℓ hvol hA hvolA hAc g
      (Work.BoseFixB1S.goodState_boxPInd hℓ hvol hA hvolA hAc i hΦG)]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    have hI : (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.n0ProjOp volA A S
            (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2)
        = if i ∈ S then
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.n0ProjOp volA A S Φ x) ^ 2
          else 0 := by
      have hae := Work.BoseFixB1S.n0ProjOpBoxPIndB1 hℓ hvol hA hvolA hAc S i hΦG
      rw [show (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.n0ProjOp volA A S
              (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2)
          = ∫ x in Submission.BoseGases.abox N ℓ,
              (if i ∈ S then Work.BoseFixB1S.n0ProjOp volA A S Φ x else 0) ^ 2 from by
        apply integral_congr_ae
        filter_upwards [hae] with x hx
        rw [hx]]
      by_cases hi : i ∈ S
      · simp [if_pos hi]
      · simp [if_neg hi]
    rw [hI]
  -- ## Step 2: sum over the slots and use the multiplicity `|S|`
  have hLHS : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp volA A g
          (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2)
      = ∑ S : Finset (Fin N), (g (S.card : ℝ)) ^ 2
          * ((S.card : ℝ)
              * ∫ x in Submission.BoseGases.abox N ℓ,
                  (Work.BoseFixB1S.n0ProjOp volA A S Φ x) ^ 2) := by
    rw [Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    exact sum_ite_mem_mul S ((g (S.card : ℝ)) ^ 2)
      (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0ProjOp volA A S Φ x) ^ 2)
  -- ## Step 3: identify the right-hand side as the same spectral sum
  rw [hLHS, Work.BoseFixB1S.Gen.n0FunOp_quadform hℓ hvol hA hvolA hAc
    (fun r : ℝ => r * (g r) ^ 2) hΦc]
  exact Finset.sum_congr rfl (fun S _ => by ring)

end Work.BoseFixB1S
