import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.commutatorPairingB1
import Submission.Work.BoseFixB1S.flatSlotFib_integrable
import Submission.Work.BoseFixB1S.fsShiftQuadB1
import Submission.Work.BoseFixB1S.n0LossPPairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.pMassFibSharpB1` — the fibre-weighted, sharp `P`-side mass bound

The `P`-side loss of FS's completion of squares (`lm:appinteractionestimate`, `final_v2.tex`
l. 3726–3743), *fibre-weighted*: the sum over the slots of the `f(xᵢ)`-weighted squares of the
spectral state `g(n₀)(P_{B,i}Φ)`, `g(r) = √(r+1) − √c`, is bounded by the fibre average
`κ := (∫_A f)/volA` times the sharp spectral moment `Σ_S (|S|+1−c)²·∫(Π_SΦ)²`:

    Σᵢ ∫_{abox N ℓ} f(xᵢ)·(g(n₀)(P_{B,i}Φ))²  ≤  κ · Σ_S (|S|+1−c)²·∫_{abox N ℓ}(Π_SΦ)² .

## The proof, in two independent halves

* **The per-slot fibre identity** (`perSlotFibIdentity`).  For each slot `i`,

      ∫_{abox N ℓ} f(xᵢ)·(g(n₀)(P_{B,i}Φ))² = κ · ∫_{abox N ℓ} (g(n₀)(P_{B,i}Φ))² .

  This is *not* a special case of `flatSlotFib_integrable` (which needs the state to be `Pᵢ`-fixed
  *globally*), but the `GoodState`-commutation `boxPInd_comm_n0FunOp` supplies exactly the missing
  information in its cleanest form: with `v := g(n₀)Φ` and `W := Pᵢv`,

      `U := g(n₀)(P_{B,i}Φ) =ᵃᵉ W`   (on `abox N ℓ`, by `boxPInd_comm_n0FunOp`),

  so the two integrals may be interchanged with `U` (`integral_congr_ae`), and `W` — being the
  image of `Pᵢ` — *is* globally `Pᵢ`-fixed (`boxPInd_idempotent`), measurable
  (`measurable_boxPInd`) and bounded on the box (`abs_boxPInd_le`).  Hence
  `flatSlotFib_integrable` at `Ψ = Θ = W` applies and the fibre weight collapses to `κ`.

  This is why no fixedness of `U` itself (nor boundedness/measurability of `U`) is needed.

* **The sharp spectral moment** (`fsPsideSharpBoundB1`, `fsShiftQuadB1`): already proved in the
  corpus as `Σᵢ∫(g(n₀)(P_{B,i}Φ))² ≤ Σ_S (|S|+1−c)²∫(Π_SΦ)²`, from the `n₀`-calculus and the
  scalar atom `t(√(t+1)−√c)² ≤ (t+1−c)²`.

Assembly: the per-slot identities sum to `κ` times `Σᵢ∫(g(n₀)(P_{B,i}Φ))²`, the constant `κ` is
non-negative (`f ≥ 0`), and the sharp bound is multiplied by it.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The per-slot fibre identity.**  The `f(xᵢ)`-weighted square of the spectral state
`g(n₀)(P_{B,i}Φ)` is exactly its fibre average `(∫_A f)/volA` times its unweighted square.

(`κ = (∫_A f)/volA`; the statement is `Fin (n+1)`-indexed because it peels the slot `i`.) -/
theorem perSlotFibIdentity {n : ℕ} {ℓ volA c : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {f : E3 → ℝ} (hf : MeasureTheory.IntegrableOn f A)
    (i : Fin (n + 1)) {Φ : X (n + 1) → ℝ} (hΦc : Continuous Φ) :
    (∫ x in abox (n + 1) ℓ,
        f (x i) * (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
          (UBBInputs8.boxPInd volA A i Φ) x) ^ 2)
      = ((∫ z in A, f z) / volA) *
          ∫ x in abox (n + 1) ℓ,
            (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
              (UBBInputs8.boxPInd volA A i Φ) x) ^ 2 := by
  classical
  have hvolA' : volA = (MeasureTheory.volume : MeasureTheory.Measure E3).real A := by
    rw [MeasureTheory.Measure.real_def, hvolA]
  -- the target state `U := g(n₀)(PᵢΦ)` and its `Pᵢ`-image `W := Pᵢ(g(n₀)Φ)`
  set U : X (n + 1) → ℝ :=
    n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
      (UBBInputs8.boxPInd volA A i Φ) with hU
  set W : X (n + 1) → ℝ :=
    fun x => UBBInputs8.boxPInd volA A i
      (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c) Φ) x with hW
  -- `U =ᵃᵉ W` on the analysis box (`boxPInd_comm_n0FunOp`, with the *continuous* `Φ`)
  have hcomm : U =ᵐ[MeasureTheory.volume.restrict (abox (n + 1) ℓ)] W := by
    have h := (boxPInd_comm_n0FunOp hℓ hvol hA hvolA hAc
      (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c) i hΦc).symm
    rw [hU, hW]
    exact h
  -- `W` is globally `Pᵢ`-fixed, measurable, bounded on the box
  have hmeasW : Measurable W := by
    rw [hW]
    refine measurable_boxPInd volA A hA i ?_
    rw [n0FunOp_eq_sum_card]
    refine Finset.measurable_sum _ (fun S _ => ?_)
    exact (goodState_n0Iter hℓ hvol hA hvolA' hAc (fun j : Fin (n + 1) => decide (j ∈ S))
      (List.ofFn (fun j : Fin (n + 1) => j)) (continuous_goodState hℓ hΦc)).1.const_mul _
  have hfixW : UBBInputs8.boxPInd volA A i W = W := by
    funext x
    rw [hW]
    exact boxPInd_idempotent hℓ hvol hA hvolA hAc i
      (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c) Φ) x
  -- coefficient bound for `g` on the spectrum `{0,…,n+1}`
  have hgC : ∀ S : Finset (Fin (n + 1)),
      |(fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c) (S.card : ℝ)|
        ≤ Real.sqrt ((n : ℝ) + 2) + Real.sqrt c := by
    intro S
    have hcard : (S.card : ℝ) ≤ (n : ℝ) + 1 := by
      have h := Finset.card_le_univ S
      rw [Fintype.card_fin] at h
      exact_mod_cast h
    have h1 : (S.card : ℝ) + 1 ≤ (n : ℝ) + 2 := by linarith
    have h2 : |Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt c|
        ≤ Real.sqrt ((S.card : ℝ) + 1) + Real.sqrt c := by
      calc |Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt c|
          ≤ |Real.sqrt ((S.card : ℝ) + 1)| + |Real.sqrt c| := abs_sub _ _
        _ = Real.sqrt ((S.card : ℝ) + 1) + Real.sqrt c := by
            rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    have h3 : Real.sqrt ((S.card : ℝ) + 1) ≤ Real.sqrt ((n : ℝ) + 2) :=
      Real.sqrt_le_sqrt h1
    linarith
  have hGood : GoodState ℓ
      (n0FunOp volA A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c) Φ) :=
    goodState_n0FunOp hℓ hvol hA hvolA hAc _ hgC (continuous_goodState hℓ hΦc)
  have hbound : ∀ x ∈ abox (n + 1) ℓ, |W x| ≤ hGood.2.choose := by
    intro x hx
    simpa [hW] using abs_boxPInd_le hℓ hvol hA hvolA hAc i hGood.2.choose_spec x hx
  -- the three rewrites
  have hstep1 : (∫ x in abox (n + 1) ℓ, f (x i) * (U x) ^ 2)
      = ∫ x in abox (n + 1) ℓ, f (x i) * (W x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hcomm] with x hx
    rw [hx]
  have hstep2 : (∫ x in abox (n + 1) ℓ, f (x i) * (W x) ^ 2)
      = ((∫ z in A, f z) / volA) * (∫ x in abox (n + 1) ℓ, (W x) ^ 2) := by
    have hflat := flatSlotFib_integrable (n := n) (ℓ := ℓ) (volA := volA)
      hℓ hvol hA hvolA' hAc i hmeasW hmeasW hfixW hfixW hbound hbound (fib := f) hf
    have e1 : (∫ x in abox (n + 1) ℓ, f (x i) * (W x) ^ 2)
        = ∫ x in abox (n + 1) ℓ, W x * W x * f (x i) := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    have e2 : (1 / volA * ∫ z in A, f z) * (∫ x in abox (n + 1) ℓ, W x * W x)
        = ((∫ z in A, f z) / volA) * (∫ x in abox (n + 1) ℓ, (W x) ^ 2) := by
      have h1 : (∫ x in abox (n + 1) ℓ, W x * W x)
          = ∫ x in abox (n + 1) ℓ, (W x) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      rw [h1]
      ring
    rw [e1, hflat, e2]
  have hstep3 : (∫ x in abox (n + 1) ℓ, (W x) ^ 2)
      = ∫ x in abox (n + 1) ℓ, (U x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hcomm] with x hx
    rw [← hx]
  rw [hstep1, hstep2, hstep3]

theorem pMassFibSharpB1 {N : ℕ} {ℓ volA c : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (hc : 0 ≤ c)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : MeasureTheory.IntegrableOn f A)
    (hfnn : ∀ z : EuclideanSpace ℝ (Fin 3), 0 ≤ f z)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        f (x i) * (Work.BoseFixB1S.n0FunOp volA A
            (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
            (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2)
      ≤ ((∫ z in A, f z) / volA) *
          ∑ S : Finset (Fin N), ((S.card : ℝ) + 1 - c) ^ 2
            * ∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.n0ProjOp volA A S Φ x) ^ 2 := by
  classical
  -- the fibre average is non-negative
  have hκ : 0 ≤ (∫ z in A, f z) / volA :=
    div_nonneg (MeasureTheory.setIntegral_nonneg hA (fun z _ => hfnn z)) (le_of_lt hvol)
  rcases N with _ | n
  · -- no slots: the left side is `0`, the right side is non-negative
    have hL : (∑ i : Fin 0, ∫ x in Submission.BoseGases.abox 0 ℓ,
        f (x i) * (Work.BoseFixB1S.n0FunOp volA A
            (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
            (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2) = 0 := by
      simp
    rw [hL]
    refine mul_nonneg hκ (Finset.sum_nonneg (fun S _ => ?_))
    exact mul_nonneg (sq_nonneg _) (integral_nonneg (fun x => sq_nonneg _))
  · -- the general case: sum the per-slot fibre identities, then the sharp bound
    have hper : ∀ i : Fin (n + 1),
        (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            f (x i) * (Work.BoseFixB1S.n0FunOp volA A
              (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
              (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2)
          = ((∫ z in A, f z) / volA) *
              ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                (Work.BoseFixB1S.n0FunOp volA A
                  (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
                  (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2 :=
      fun i => perSlotFibIdentity hℓ hvol hA hvolA hAc hf i hΦc
    calc (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            f (x i) * (Work.BoseFixB1S.n0FunOp volA A
              (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
              (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2)
        = ∑ i : Fin (n + 1), ((∫ z in A, f z) / volA) *
              ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                (Work.BoseFixB1S.n0FunOp volA A
                  (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
                  (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2 :=
            Finset.sum_congr rfl (fun i _ => hper i)
      _ = ((∫ z in A, f z) / volA) *
            ∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
              (Work.BoseFixB1S.n0FunOp volA A
                (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
                (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2 :=
            (Finset.mul_sum _ _ _).symm
      _ ≤ ((∫ z in A, f z) / volA) *
            ∑ S : Finset (Fin (n + 1)), ((S.card : ℝ) + 1 - c) ^ 2
              * ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                  (Work.BoseFixB1S.n0ProjOp volA A S Φ x) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (fsPsideSharpBoundB1 hℓ hvol hA hvolA hAc hc hΦc) hκ

end Work.BoseFixB1S
