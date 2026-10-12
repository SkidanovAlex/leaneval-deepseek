import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.exclFunOpPropsB1
import Submission.Work.BoseFixB1S.n0FunOp_eq_sum_card
import Submission.Work.BoseFixB1S.n0ProjOpOrthB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.n0FunOp_eq_excl_shift`

**The slot-`i` splitting of the `n₀` functional calculus.**

With `P_i := UBBInputs8.boxPInd volA A i` (FS `eq:HBU`), `n₀ = Σ_i P_i` (`n0Op`) and the subset
idempotents `Proj_S = n0ProjOp volA A S` (with `Proj_S Ψ = ∏_{i∈S} P_i ∏_{i∉S} (1 − P_i) Ψ`,
composition), the functional calculus of `n₀` (`n0FunOp`) splits according to the occupation of
the *single* slot `i`:

    g(n₀) Ψ  =  g(n₀ − P_i + 1)(P_i Ψ)  +  g(n₀ − P_i)(Ψ − P_i Ψ)          on `abox N ℓ`,

where the two excluded operators are the explicit spectral sums `exclFunOp` of `n0ExclFunOp`.  In
terms of the `Proj_S`, this is the pointwise bookkeeping that the `√`-completion of squares of FS
`lm:appinteractionestimate` uses: `Proj_S` is an eigen-idempotent of `P_i` for the eigenvalue
`1_{i∈S}` (`n0IterEigen`, applied to the *inner* slot via the commutation `n0Iter_comm_boxPInd`),
so

* `i ∈ S`: `g(|S|)·Proj_S Ψ = g(|S| − 1 + 1)·Proj_S (P_i Ψ) + g(|S| − 1)·Proj_S (Ψ − P_i Ψ)`,
  the second term being `0` because `Proj_S(P_i Ψ) = Proj_S Ψ` there;
* `i ∉ S`: the first term vanishes (`Proj_S(P_i Ψ) = 0`) and the second is `g(|S|)·Proj_S Ψ`.

The only hypothesis beyond the standing box data is `GoodState ℓ Ψ` (measurable and bounded on
the analysis box), which is what both `n0Iter_comm_boxPInd` and the linearity `n0Iter_sub` — and
through them the two identities above — need; compare `FINDING_n0FunOp_affineB1_false.md` for
what happens without it.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators

/-- **The single-slot eigen-property, slot applied *before* the iteration**: the subset
idempotent `Proj_S` of a box-projected state is the projection of the eigen-component,
`Proj_S (P_i Ψ) = 1_{i∈S} · Proj_S Ψ` pointwise on `abox N ℓ`.  Indeed `Proj_S` commutes with
`P_i` (`n0Iter_comm_boxPInd`), and `P_i` acts on `Proj_S Ψ` by the eigenvalue `1_{i∈S}`
(`n0IterEigen`). -/
theorem n0ProjOp_boxPInd_eigen {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (S : Finset (Fin N)) (i : Fin N) {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.BoseFixB1S.n0ProjOp volA A S (Work.UBBInputs8.boxPInd volA A i Ψ) x
        = (if i ∈ S then Work.BoseFixB1S.n0ProjOp volA A S Ψ x else 0) := by
  intro x hx
  have h1 := Work.BoseFixB1S.n0Iter_comm_boxPInd hℓ hvol hA hvolA hAc
    (fun j : Fin N => decide (j ∈ S)) i (List.ofFn (fun j : Fin N => j)) hΨ x hx
  have h2 := Work.BoseFixB1S.n0IterEigen hℓ hvol hA hvolA hAc S hΨ i x hx
  rw [Work.BoseFixB1S.n0ProjOp] at h2 ⊢
  rw [h1, h2]

theorem n0FunOp_eq_excl_shift {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (g : ℝ → ℝ) (i : Fin N) {Ψ : Submission.BoseGases.X N → ℝ}
    (hΨ : Work.BoseFixB1S.GoodState ℓ Ψ) (x : Submission.BoseGases.X N)
    (hx : x ∈ Submission.BoseGases.abox N ℓ) :
    Work.BoseFixB1S.n0FunOp volA A g Ψ x
      = Work.BoseFixB1S.exclFunOp volA A i (fun r => g (r + 1))
          (Work.UBBInputs8.boxPInd volA A i Ψ) x
        + Work.BoseFixB1S.exclFunOp volA A i g
            (fun y => Ψ y - Work.UBBInputs8.boxPInd volA A i Ψ y) x := by
  have hPi : Work.BoseFixB1S.GoodState ℓ (Work.UBBInputs8.boxPInd volA A i Ψ) :=
    Work.BoseFixB1S.goodState_boxPInd hℓ hvol hA hvolA hAc i hΨ
  -- linearity of the subset idempotent on the single-slot complement
  have hsplit : ∀ S : Finset (Fin N),
      Work.BoseFixB1S.n0ProjOp volA A S (fun y => Ψ y - Work.UBBInputs8.boxPInd volA A i Ψ y) x
        = Work.BoseFixB1S.n0ProjOp volA A S Ψ x
          - Work.BoseFixB1S.n0ProjOp volA A S (Work.UBBInputs8.boxPInd volA A i Ψ) x := by
    intro S
    rw [Work.BoseFixB1S.n0ProjOp]
    exact Work.n0ProjOpOrthAux.n0Iter_sub hℓ hvol hA hvolA hAc
      (fun j : Fin N => decide (j ∈ S)) (List.ofFn (fun j : Fin N => j)) hΨ hPi x hx
  -- both sides as sums over the subset idempotents
  rw [Work.BoseFixB1S.n0FunOp_eq_sum_card volA A g Ψ]
  simp only [Work.BoseFixB1S.exclFunOp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hi : i ∈ S
  · -- `i ∈ S`: the `Proj_S`-component of `P_iΨ` is all of `Proj_S Ψ`, that of `Ψ − P_iΨ` is `0`
    have h1 : Work.BoseFixB1S.n0ProjOp volA A S (Work.UBBInputs8.boxPInd volA A i Ψ) x
        = Work.BoseFixB1S.n0ProjOp volA A S Ψ x := by
      have h := n0ProjOp_boxPInd_eigen hℓ hvol hA hvolA hAc S i hΨ x hx
      rw [if_pos hi] at h
      exact h
    have h2 : Work.BoseFixB1S.n0ProjOp volA A S
        (fun y => Ψ y - Work.UBBInputs8.boxPInd volA A i Ψ y) x = 0 := by
      rw [hsplit S, h1, sub_self]
    simp only [if_pos hi]
    rw [h1, h2]
    rw [show (S.card : ℝ) - 1 + 1 = (S.card : ℝ) from by ring, mul_zero, add_zero]
  · -- `i ∉ S`: the `Proj_S`-component of `P_iΨ` vanishes, that of `Ψ − P_iΨ` is `Proj_S Ψ`
    have h1 : Work.BoseFixB1S.n0ProjOp volA A S (Work.UBBInputs8.boxPInd volA A i Ψ) x = 0 := by
      have h := n0ProjOp_boxPInd_eigen hℓ hvol hA hvolA hAc S i hΨ x hx
      rw [if_neg hi] at h
      exact h
    have h2 : Work.BoseFixB1S.n0ProjOp volA A S
        (fun y => Ψ y - Work.UBBInputs8.boxPInd volA A i Ψ y) x
        = Work.BoseFixB1S.n0ProjOp volA A S Ψ x := by
      rw [hsplit S, h1, sub_zero]
    simp only [if_neg hi]
    rw [h1, h2]
    rw [show (S.card : ℝ) - 0 + 1 = (S.card : ℝ) + 1 from by ring, mul_zero, zero_add]
    rw [show (S.card : ℝ) - 0 = (S.card : ℝ) from by ring]

end Work.BoseFixB1S
