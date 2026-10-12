import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.fsQsharp.n0FunOpSqSpectral
import Submission.Work.BoseFixB1S.n0ProjOpBoxPIndB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.n0FunOpSumSpectralB1`

**The spectral sum rule for the `n₀` functional calculus, summed over the slots.**

For a `GoodState` `Φ` and any `g : ℝ → ℝ` of the occupation number,

    Σ_i ∫_{abox N ℓ} (g(n₀) P_{B,i} Φ)²  =  Σ_S |S| · g(|S|)² · ∫_{abox N ℓ} (P_S Φ)² ,

where `P_{B,i} = UBBInputs8.boxPInd V A i`, `P_S = n0ProjOp V A S` are the subset idempotents of
the FS box projections, `g(n₀) = n0FunOp V A g = Σ_S g(|S|)·P_S` is the functional calculus, and
`V = |A|`, `A ⊆ acube ℓ`.

## Proof

Insert the slot projection into the spectral (Parseval) identity and sum.

* `fsQsharp.n0FunOpSqSpectral` for the state `P_{B,i}Φ` (a `GoodState` by `goodState_boxPInd`)
  evaluates each slot term as `Σ_S g(|S|)² ∫ (P_S (P_{B,i}Φ))²`.
* `n0ProjOpBoxPIndB1` says `P_S (P_{B,i}Φ) =ᵐ 1_{i∈S}·P_SΦ` on the box, so
  `∫ (P_S (P_{B,i}Φ))² = [i ∈ S]·∫ (P_SΦ)²` — the squared indicator collapses by `integral_const_mul`
  (which needs no integrability hypothesis).
* Swapping the two finite sums (`Finset.sum_comm`) leaves `Σ_S g(|S|)²·(Σ_i [i ∈ S])·∫ (P_SΦ)²`,
  and `Σ_i [i ∈ S] = |S|` is `card_cast_eq_sum_ite_mem`.

No continuity of `Φ` is used: `GoodState` is exactly the class on which the two ingredients are
stated.
-/

namespace Work.BoseFixB1S

theorem n0FunOpSumSpectralB1 {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (g : ℝ → ℝ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Work.BoseFixB1S.GoodState ℓ Φ) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp V A g (Work.UBBInputs8.boxPInd V A i Φ)) x ^ 2)
      = ∑ S : Finset (Fin N), (S.card : ℝ) * (g (S.card : ℝ)) ^ 2
          * ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.n0ProjOp V A S Φ) x ^ 2 := by
  classical
  -- Step 1: the spectral identity, slot by slot.
  have hterm : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp V A g (Work.UBBInputs8.boxPInd V A i Φ)) x ^ 2)
        = ∑ S : Finset (Fin N), (g (S.card : ℝ)) ^ 2 *
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.n0ProjOp V A S (Work.UBBInputs8.boxPInd V A i Φ)) x ^ 2 :=
    fun i => Work.BoseFixB1S.fsQsharp.n0FunOpSqSpectral hℓ hV hA hVeq hAc g
      (Work.BoseFixB1S.goodState_boxPInd hℓ hV hA hVeq hAc i hΦ)
  -- Step 2: the slot projection inside `P_S` collapses to the indicator `[i ∈ S]`.
  have hpair : ∀ (i : Fin N) (S : Finset (Fin N)),
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.n0ProjOp V A S (Work.UBBInputs8.boxPInd V A i Φ)) x ^ 2)
        = (if i ∈ S then (1:ℝ) else 0) *
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.n0ProjOp V A S Φ) x ^ 2 := by
    intro i S
    have hae := Work.BoseFixB1S.n0ProjOpBoxPIndB1 hℓ hV hA hVeq hAc S i hΦ
    have h2 : (fun x : Submission.BoseGases.X N =>
          (Work.BoseFixB1S.n0ProjOp V A S (Work.UBBInputs8.boxPInd V A i Φ)) x ^ 2)
        =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
          fun x => (if i ∈ S then Work.BoseFixB1S.n0ProjOp V A S Φ x else 0) ^ 2 := by
      filter_upwards [hae] with x hx
      rw [hx]
    rw [MeasureTheory.integral_congr_ae h2]
    have hstep : ∀ x : Submission.BoseGases.X N,
        (if i ∈ S then Work.BoseFixB1S.n0ProjOp V A S Φ x else 0) ^ 2
          = (if i ∈ S then (1:ℝ) else 0) * (Work.BoseFixB1S.n0ProjOp V A S Φ x) ^ 2 := by
      intro x
      by_cases h : i ∈ S <;> simp [h]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hstep),
      MeasureTheory.integral_const_mul]
  -- Step 3: reorganise the double sum.
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  simp only [hpair]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  have hstep : ∀ i : Fin N,
      (g (S.card : ℝ)) ^ 2 * ((if i ∈ S then (1:ℝ) else 0)
          * (∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.n0ProjOp V A S Φ) x ^ 2))
        = (g (S.card : ℝ)) ^ 2 * (if i ∈ S then (1:ℝ) else 0)
          * (∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.n0ProjOp V A S Φ) x ^ 2) := by
    intro i; ring
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  rw [← Finset.sum_mul, ← Finset.mul_sum, Work.BoseFixB1S.card_cast_eq_sum_ite_mem S]
  ring

end Work.BoseFixB1S
