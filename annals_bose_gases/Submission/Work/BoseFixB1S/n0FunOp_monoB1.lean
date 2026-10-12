import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.n0FunOp_eq_sum_card
import Submission.Work.BoseFixB1S.n0PairingSumNice
import Submission.Work.BoseFixB1S.n0PairingZeroNice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.n0FunOp_monoB1` — monotonicity of the `n₀` functional calculus

**Monotonicity of the `n₀` functional calculus in quadratic-form (expectation) sense.**  If the
scalar weight `g` is dominated on `{0, …, N}` by `h`, then the box expectation of the operator
`g(n₀) = n0FunOp volA A g` against a state `Ψ` is dominated by that of `h(n₀)`:

  `∫_{abox N ℓ} (g(n₀)Ψ)·Ψ  ≤  ∫_{abox N ℓ} (h(n₀)Ψ)·Ψ`,

for `Ψ` merely measurable and bounded on the box (`BoxNice`/`GoodState`).

This is the missing ingredient recorded in
`Submission/Work/BoseFixB1S/FINDING_interEstB1_ledger_s3.md` §7: the on-disk orthogonality lemmas
(`n0ProjOp_pairing_zero`, `n0ProjOp_pairing_sum`) were stated for *continuous* states, while the
`P`-side input `δ(xᵢ)·PᵢΦ` of FS `lm:appinteractionestimate` is only bounded measurable.
The two `…Nice` companion modules reprove those pairings at the right generality.

## Proof

Write `P_S := n0ProjOp volA A S Ψ` for the subset idempotents of the FS box projections.  The
functional calculus is a *finite* combination of them,
`n0FunOp volA A f Ψ = ∑_S f (|S|) · P_S Ψ` (`n0FunOp_eq_sum_card`), so by finite linearity of the
box integral (every term being bounded and measurable on the finite-measure box)

  `∫ (n0FunOp g Ψ)·Ψ = ∑_S g (|S|) · ∫ P_S Ψ · Ψ`.

The integrated partition of unity (`n0PairingSumNice`) together with the orthogonality of distinct
subset idempotents (`n0PairingZeroNice`) collapses the inner pairing to its diagonal,

  `∫ P_S Ψ · Ψ = ∫ P_S Ψ · P_S Ψ = ∫ (P_S Ψ)² ≥ 0`,

i.e. the diagonal of the spectral decomposition is a *square*, hence non-negative.  Therefore

  `∫ (g(n₀)Ψ)·Ψ = ∑_S g (|S|) · ∫ (P_S Ψ)²  ≤  ∑_S h (|S|) · ∫ (P_S Ψ)² = ∫ (h(n₀)Ψ)·Ψ`,

each term being compared by `g (|S|) ≤ h (|S|)` (available since `|S| ≤ N`, a subset of `Fin N`)
times the non-negative diagonal.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

theorem n0FunOp_monoB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {g h : ℝ → ℝ} (hgh : ∀ k : ℕ, k ≤ N → g (k : ℝ) ≤ h (k : ℝ))
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ) {CΨ : ℝ}
    (hΨb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ CΨ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp volA A g Ψ x) * Ψ x)
      ≤ ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.n0FunOp volA A h Ψ x) * Ψ x := by
  classical
  -- `Ψ` is measurable and bounded on the box, i.e. a `BoxNice`/`GoodState` state.
  have hΨn : BoxNice ℓ Ψ := ⟨hΨm, CΨ, hΨb⟩
  -- hence so is every subset idempotent applied to it (`n0Iter` closure).
  have hΦn : ∀ S : Finset (Fin N), BoxNice ℓ (n0ProjOp volA A S Ψ) := fun S => by
    have h := BoxNice.iter hℓ hvol hA hvolA hAc (fun i => decide (i ∈ S)) hΨn
      (List.ofFn (fun i : Fin N => i))
    simpa only [n0ProjOp] using h
  -- bound/measurability side conditions: every product occurring below is integrable on the box.
  have hInt_SP : ∀ S : Finset (Fin N), IntegrableOn
      (fun x : X N => n0ProjOp volA A S Ψ x * Ψ x) (abox N ℓ) volume := fun S =>
    integrableOn_mul_of_bound hℓ (hΦn S).1 hΨm (hΦn S).2.choose_spec hΨb
  -- ## The diagonal of the spectral decomposition
  -- integrated partition of unity + orthogonality of distinct idempotents
  have hdiag : ∀ S : Finset (Fin N),
      (∫ x in abox N ℓ, Ψ x * n0ProjOp volA A S Ψ x)
        = ∫ x in abox N ℓ, n0ProjOp volA A S Ψ x * n0ProjOp volA A S Ψ x := by
    intro S
    have hsum := n0PairingSumNice hℓ hvol hA hvolA hAc hΨm hΨb S
    have hsingle : (∑ T : Finset (Fin N), ∫ x in abox N ℓ,
          n0ProjOp volA A T Ψ x * n0ProjOp volA A S Ψ x)
        = ∫ x in abox N ℓ, n0ProjOp volA A S Ψ x * n0ProjOp volA A S Ψ x :=
      Finset.sum_eq_single S
        (fun T _ hTS => n0PairingZeroNice hℓ hvol hA hvolA hAc hΨm hΨb hTS)
        (fun hS => absurd (Finset.mem_univ S) hS)
    rw [hsum, hsingle]
  -- ## The quadratic form of the functional calculus, as a sum of non-negative diagonal terms
  have hquad : ∀ f : ℝ → ℝ,
      (∫ x in abox N ℓ, n0FunOp volA A f Ψ x * Ψ x)
        = ∑ S : Finset (Fin N), f (S.card) *
            ∫ x in abox N ℓ, n0ProjOp volA A S Ψ x * n0ProjOp volA A S Ψ x := by
    intro f
    -- the functional calculus is a finite combination of the subset idempotents
    have hpt : (fun x : X N => n0FunOp volA A f Ψ x * Ψ x)
        = fun x => ∑ S : Finset (Fin N), f (S.card) * (n0ProjOp volA A S Ψ x * Ψ x) := by
      funext x
      have hx := congrFun (n0FunOp_eq_sum_card volA A f Ψ) x
      rw [hx, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun S _ => by ring)
    rw [hpt, integral_finsetSum _ (fun S _ => (hInt_SP S).const_mul _)]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [integral_const_mul]
    congr 1
    -- the pairing is symmetric and equals the (non-negative) diagonal
    have hflip : (∫ x in abox N ℓ, n0ProjOp volA A S Ψ x * Ψ x)
        = ∫ x in abox N ℓ, Ψ x * n0ProjOp volA A S Ψ x :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
    rw [hflip, hdiag S]
  -- ## Monotonicity, term by term
  rw [hquad g, hquad h]
  refine Finset.sum_le_sum (fun S _ => ?_)
  refine mul_le_mul_of_nonneg_right (hgh S.card ?_) ?_
  · simpa using Finset.card_le_card (Finset.subset_univ S)
  · exact integral_nonneg (fun x => mul_self_nonneg _)

end Work.BoseFixB1S
