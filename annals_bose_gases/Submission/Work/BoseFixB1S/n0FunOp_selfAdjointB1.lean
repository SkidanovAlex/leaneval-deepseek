import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.n0FunOp_eq_sum_card
import Submission.Work.BoseFixB1S.n0ProjOpOrthB1
import Submission.Work.BoseFixB1S.n0SpectralMomentsB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.n0FunOp_selfAdjointB1` — self-adjointness of the `n₀` functional calculus

The functional calculus

`n0FunOp volA A g Ψ = Σ_{k ≤ N} g k · (Σ_{|S| = k} n0ProjOp volA A S Ψ)`

of the condensate-count operator `n₀ = Σᵢ P_{B,i}` (`n0SpectralDefs`) is **symmetric on
`L²(abox N ℓ)`**: for states `u`, `v` measurable and bounded on the analysis box (`GoodState`),

`∫_{abox} (g(n₀)u)·v = ∫_{abox} u·(g(n₀)v)`.

## Math

`n0FunOp_eq_sum_card` regroups the defining double sum by cardinality:
`g(n₀) = Σ_S g(|S|) · n0ProjOp S` pointwise.  Each `n0ProjOp S` is self-adjoint on the box
(`n0ProjOpOrthB1`, itself the iteration `n0Iter_selfAdjoint` / `exclFunOpAux.n0IterSelfAdj`), and
the constants `g (|S|)` pull out of the integrals.  Swapping the finite sum with the integral
(`MeasureTheory.integral_finsetSum`) — legitimate because every integrand is a bounded measurable
function on the box, i.e. a product of `GoodState`s (`integrableOn_mul_goodState`) times a
constant — gives the claim.  This is the same computation as item (3) of `exclFunOpPropsB1`, with
the weight `g (|S|)` in place of `g (|S| − 1_{i∈S})`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem n0FunOp_selfAdjointB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (g : ℝ → ℝ) {u v : Submission.BoseGases.X N → ℝ}
    (hu : Work.BoseFixB1S.GoodState ℓ u) (hv : Work.BoseFixB1S.GoodState ℓ v) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp volA A g u) x * v x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          u x * (Work.BoseFixB1S.n0FunOp volA A g v) x := by
  -- the spectral resolution of `g(n₀)`, pointwise
  have hEqU : ∀ x : X N, n0FunOp volA A g u x
      = ∑ S : Finset (Fin N), g (S.card : ℝ) * n0ProjOp volA A S u x :=
    fun x => congrFun (n0FunOp_eq_sum_card volA A g u) x
  have hEqV : ∀ x : X N, n0FunOp volA A g v x
      = ∑ S : Finset (Fin N), g (S.card : ℝ) * n0ProjOp volA A S v x :=
    fun x => congrFun (n0FunOp_eq_sum_card volA A g v) x
  -- the sector functions of `u` and `v` are again states measurable and bounded on the box
  have hGu : ∀ S : Finset (Fin N), GoodState ℓ (n0ProjOp volA A S u) :=
    fun S => n0ProjOp_goodStateB1 hℓ hvol hA hvolA hAc hu S
  have hGv : ∀ S : Finset (Fin N), GoodState ℓ (n0ProjOp volA A S v) :=
    fun S => n0ProjOp_goodStateB1 hℓ hvol hA hvolA hAc hv S
  -- integrability of the summands (bounded measurable products on the box)
  have hI : ∀ S : Finset (Fin N), IntegrableOn (fun x : X N =>
      g (S.card : ℝ) * (n0ProjOp volA A S u x * v x)) (abox N ℓ) volume :=
    fun S => (integrableOn_mul_goodState hℓ (hGu S) hv).const_mul _
  have hJ : ∀ S : Finset (Fin N), IntegrableOn (fun x : X N =>
      g (S.card : ℝ) * (u x * n0ProjOp volA A S v x)) (abox N ℓ) volume :=
    fun S => (integrableOn_mul_goodState hℓ hu (hGv S)).const_mul _
  -- self-adjointness of each sector idempotent
  have hAdj : ∀ S : Finset (Fin N),
      (∫ x in abox N ℓ, n0ProjOp volA A S u x * v x)
        = ∫ x in abox N ℓ, u x * n0ProjOp volA A S v x :=
    fun S => (n0ProjOpOrthB1 hℓ hvol hA hvolA hAc hu).2.2 S hu hv
  calc (∫ x in abox N ℓ, n0FunOp volA A g u x * v x)
      = ∫ x in abox N ℓ, ∑ S : Finset (Fin N),
          g (S.card : ℝ) * (n0ProjOp volA A S u x * v x) := by
        apply setIntegral_congr_fun (abox_measurable N ℓ)
        intro x _
        simp only []
        rw [hEqU x, Finset.sum_mul]
        exact Finset.sum_congr rfl fun S _ => by ring
    _ = ∑ S : Finset (Fin N),
          ∫ x in abox N ℓ, g (S.card : ℝ) * (n0ProjOp volA A S u x * v x) := by
        rw [MeasureTheory.integral_finsetSum]
        exact fun S _ => hI S
    _ = ∑ S : Finset (Fin N),
          g (S.card : ℝ) * ∫ x in abox N ℓ, n0ProjOp volA A S u x * v x := by
        exact Finset.sum_congr rfl fun S _ => MeasureTheory.integral_const_mul _ _
    _ = ∑ S : Finset (Fin N),
          g (S.card : ℝ) * ∫ x in abox N ℓ, u x * n0ProjOp volA A S v x := by
        exact Finset.sum_congr rfl fun S _ => by rw [hAdj S]
    _ = ∑ S : Finset (Fin N),
          ∫ x in abox N ℓ, g (S.card : ℝ) * (u x * n0ProjOp volA A S v x) := by
        exact Finset.sum_congr rfl fun S _ => (MeasureTheory.integral_const_mul _ _).symm
    _ = ∫ x in abox N ℓ, ∑ S : Finset (Fin N),
          g (S.card : ℝ) * (u x * n0ProjOp volA A S v x) := by
        rw [MeasureTheory.integral_finsetSum]
        exact fun S _ => hJ S
    _ = ∫ x in abox N ℓ, u x * n0FunOp volA A g v x := by
        apply setIntegral_congr_fun (abox_measurable N ℓ)
        intro x _
        simp only []
        rw [hEqV x, Finset.mul_sum]
        exact Finset.sum_congr rfl fun S _ => by ring

end Work.BoseFixB1S
