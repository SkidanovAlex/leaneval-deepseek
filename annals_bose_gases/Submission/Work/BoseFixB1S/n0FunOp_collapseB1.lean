import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.exclFunOpAux
import Submission.Work.BoseFixB1S.n0FunOp_eq_sum_card
import Submission.Work.BoseFixB1S.n0ProjOpOrthB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.n0FunOp_collapseB1`

**The collapsing identity for the completed square.**  With

  `Θ± = √(n₀ + 1) ± √c`   (`c = μ|B| ≥ 0`),

the composition of the two shifted `n₀`-functional calculi collapses to the affine weight:

  `Θ₊ (Θ₋ p) = n0FunOp (r ↦ r + 1 − c) p`   a.e. on the analysis box,

for every `p ∈ GoodState ℓ` (measurable, bounded on `abox N ℓ`) — the class on which the whole
`n₀` layer states its hypotheses.

## Contents

* `n0FunOp_compB1_goodState` — multiplicativity of the `n₀` functional calculus,
  `n0FunOp a (n0FunOp b Ψ) = n0FunOp (a·b) Ψ` a.e. on the box, for `Ψ ∈ GoodState`.
  This is `n0FunOp_compB1` with its `Continuous Ψ` hypothesis weakened to `GoodState ℓ Ψ`;
  that is the only thing the proof of `n0FunOp_compB1` uses `Continuous Ψ` for (to produce a
  bound on the analysis box), so the proof is the same line for line.  The weakening matters
  here because the inner state `n0FunOp (√(r+1) − √c) p` of the target is *not* known to be
  continuous, only to be a `GoodState`.
* `n0FunOp_congr_card` — the functional calculus only reads its weight off the cardinalities of
  the subsets, so two weights agreeing on `S.card`, `S ⊆ Fin N`, define the same operator.  This
  is what lets us replace the pointwise product
  `(√(r+1) + √c)(√(r+1) − √c)` by `r + 1 − c` without having to know the two functions agree at
  *negative* arguments (they do not; but `n0FunOp` only ever evaluates the weight at
  `k = S.card ≥ 0`, where `Real.sq_sqrt` applies).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-- **Multiplicativity of the `n₀` functional calculus on `GoodState`s.**
`n0FunOp a (n0FunOp b Ψ) = n0FunOp (a · b) Ψ` a.e. on the analysis box, for every state `Ψ`
that is measurable and bounded there.  (`n0FunOp_compB1` under its weakest hypothesis; the
proof is the direct double-sum computation over the mutually orthogonal subset idempotents
`n0ProjOp volA A S`.) -/
theorem n0FunOp_compB1_goodState {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ)
    (a b : ℝ → ℝ) {Ψ : X N → ℝ} (hΨ : GoodState ℓ Ψ) :
    (fun x => n0FunOp volA A a (fun y => n0FunOp volA A b Ψ y) x)
      =ᵐ[MeasureTheory.volume.restrict (abox N ℓ)]
      fun x => n0FunOp volA A (fun r => a r * b r) Ψ x := by
  filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
  have hS : ∀ S : Finset (Fin N), GoodState ℓ (n0ProjOp volA A S Ψ) :=
    fun S => goodState_n0Iter hℓ hvol hA hvolA hAc (fun j => decide (j ∈ S))
      (List.ofFn (fun j : Fin N => j)) hΨ
  -- the eigen-step: `n0ProjOp T` reads off the `T`-component of `b(n₀)Ψ`
  have hstep : ∀ T : Finset (Fin N),
      n0ProjOp volA A T (n0FunOp volA A b Ψ) x
        = b (T.card : ℝ) * n0ProjOp volA A T Ψ x := by
    intro T
    have hlin := n0IterFinsetSum hℓ hvol hA hvolA hAc
      (Finset.univ : Finset (Finset (Fin N))) (fun S => b (S.card : ℝ))
      (fun j => decide (j ∈ T)) (List.ofFn (fun j : Fin N => j))
      (fun S => n0ProjOp volA A S Ψ) (fun S _ => hS S) x hx
    calc n0ProjOp volA A T (n0FunOp volA A b Ψ) x
        = n0Iter volA A (fun j => decide (j ∈ T)) (List.ofFn (fun j : Fin N => j))
            (fun y => ∑ S : Finset (Fin N), b (S.card : ℝ) * n0ProjOp volA A S Ψ y) x := by
          rw [n0ProjOp, n0FunOp_eq_sum_card volA A b Ψ]
      _ = ∑ S : Finset (Fin N), b (S.card : ℝ)
            * n0Iter volA A (fun j => decide (j ∈ T)) (List.ofFn (fun j : Fin N => j))
                (n0ProjOp volA A S Ψ) x := hlin
      _ = ∑ S : Finset (Fin N), b (S.card : ℝ)
            * (if T = S then n0ProjOp volA A S Ψ x else 0) := by
          apply Finset.sum_congr rfl
          intro S _
          rw [show n0Iter volA A (fun j => decide (j ∈ T)) (List.ofFn (fun j : Fin N => j))
                (n0ProjOp volA A S Ψ) x
              = n0ProjOp volA A T (n0ProjOp volA A S Ψ) x from rfl,
            n0ProjOpEigenOrth hℓ hvol hA hvolA hAc hΨ S T x hx]
      _ = b (T.card : ℝ) * n0ProjOp volA A T Ψ x := by
          rw [Finset.sum_eq_single T]
          · rw [if_pos rfl]
          · intro S _ hST
            rw [if_neg (Ne.symm hST), mul_zero]
          · intro hT
            exact absurd (Finset.mem_univ T) hT
  calc n0FunOp volA A a (fun y => n0FunOp volA A b Ψ y) x
      = ∑ T : Finset (Fin N), a (T.card : ℝ)
          * n0ProjOp volA A T (n0FunOp volA A b Ψ) x := by
        rw [n0FunOp_eq_sum_card volA A a (fun y => n0FunOp volA A b Ψ y)]
    _ = ∑ T : Finset (Fin N), a (T.card : ℝ)
          * (b (T.card : ℝ) * n0ProjOp volA A T Ψ x) := by
        apply Finset.sum_congr rfl
        intro T _
        rw [hstep T]
    _ = ∑ T : Finset (Fin N),
          (a (T.card : ℝ) * b (T.card : ℝ)) * n0ProjOp volA A T Ψ x := by
        apply Finset.sum_congr rfl
        intro T _
        ring
    _ = n0FunOp volA A (fun r => a r * b r) Ψ x := by
        rw [n0FunOp_eq_sum_card volA A (fun r => a r * b r) Ψ]

/-- **The functional calculus sees its weight only through the cardinalities.**  If two weights
agree on `S.card` for every `S : Finset (Fin N)` — e.g. because they agree on all of
`{0, …, N}` — then they define the same operator. -/
theorem n0FunOp_congr_card {N : ℕ} (volA : ℝ) (A : Set E3) {g₁ g₂ : ℝ → ℝ}
    (h : ∀ S : Finset (Fin N), g₁ (S.card : ℝ) = g₂ (S.card : ℝ)) (Ψ : X N → ℝ) :
    n0FunOp volA A g₁ Ψ = n0FunOp volA A g₂ Ψ := by
  rw [n0FunOp_eq_sum_card volA A g₁ Ψ, n0FunOp_eq_sum_card volA A g₂ Ψ]
  funext x
  exact Finset.sum_congr rfl (fun S _ => by rw [h S])

/-- **The collapsing identity of the completed square.**  For `c ≥ 0` and `p` measurable and
bounded on the analysis box, the composition `√(n₀+1) + √c` after `√(n₀+1) − √c` is the affine
weight `r ↦ r + 1 − c` applied to `n₀`:
`(Θ₊ Θ₋ p) = n0FunOp (r ↦ r + 1 − c) p` a.e. on `abox N ℓ`. -/
theorem n0FunOp_collapseB1 {N : ℕ} {ℓ volA c : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA) (hc : 0 ≤ c)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {p : Submission.BoseGases.X N → ℝ} (hp : Work.BoseFixB1S.GoodState ℓ p) :
    (fun x => Work.BoseFixB1S.n0FunOp volA A
        (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
        (fun y => Work.BoseFixB1S.n0FunOp volA A
          (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c) p y) x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
      fun x => Work.BoseFixB1S.n0FunOp volA A (fun r : ℝ => r + 1 - c) p x := by
  have hcomp := n0FunOp_compB1_goodState hℓ hvol hA hvolA hAc
    (fun r : ℝ => Real.sqrt (r + 1) + Real.sqrt c)
    (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c) hp
  have hcongr := n0FunOp_congr_card volA A
    (g₁ := fun r : ℝ => (Real.sqrt (r + 1) + Real.sqrt c) * (Real.sqrt (r + 1) - Real.sqrt c))
    (g₂ := fun r : ℝ => r + 1 - c) (fun S => by
      have h1 : Real.sqrt ((S.card : ℝ) + 1) ^ 2 = (S.card : ℝ) + 1 :=
        Real.sq_sqrt (by positivity)
      have h2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc
      show (Real.sqrt ((S.card : ℝ) + 1) + Real.sqrt c)
          * (Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt c) = (S.card : ℝ) + 1 - c
      calc (Real.sqrt ((S.card : ℝ) + 1) + Real.sqrt c)
            * (Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt c)
          = Real.sqrt ((S.card : ℝ) + 1) ^ 2 - Real.sqrt c ^ 2 := by ring
        _ = ((S.card : ℝ) + 1) - c := by rw [h1, h2]) p
  filter_upwards [hcomp] with x hx
  rw [hx, congrFun hcongr x]

end Work.BoseFixB1S
