import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.Lambda
import Submission.Work.BG.s02_orbitSumVanish
import Submission.Work.BG.s02_quotCyclic

/-!
# Area BG: BG Remark 3.1, the Gallagher form

For the §2 context `C` (`H₀/U` cyclic, hence abelian, `U ⊴ H₀`), the induced trivial
character of `U = Uin C` is the sum of the linear characters of `H₀/U`, inflated to `H₀`:

`Ind_U^{H₀} 1_U = r(Λ) = lambdaSum C.P`.

This is the `θ = 1` case of Gallagher's decomposition and the identity used in the proof of
BG Remark 3.1.  It is an instance of the OddOrder library's
`induce_trivial_eq_sum_linearClassFunction`; the only input that has to be supplied here is
the commutativity of the quotient `H₀/U`, which `Sec2Ctx.quot_cyclic` provides
(`Work.BG.mul_comm_quotGroup`).
-/

namespace Work.BG

open OddOrder.RepresentationTheory
open scoped commutatorElement

theorem rem31Gallagher {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G)
    [Fintype ↥C.P.H0] [Fintype ↥(Work.GW2.C16.Uin C)]
    [Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ)]
    [Fintype (Work.BG.quotGroup C.P →* ℂˣ)]
    (hcard : Nat.card (Work.BG.quotGroup C.P →* ℂˣ) = (Work.GW2.C16.Uin C).index) :
    OddOrder.RepresentationTheory.ClassFunction.induce (Work.GW2.C16.Uin C)
        (OddOrder.RepresentationTheory.trivialClassFunction ↥(Work.GW2.C16.Uin C))
      = Work.BG.lambdaSum C.P := by
  -- `hcard` (the count of `|Λ| = [H₀:U]`) is not needed for the identity itself:
  -- the equality is Gallagher's decomposition in the abelian-quotient case.
  have _hcard := hcard
  -- `H₀/U` is abelian: the commutator of any two elements of `H₀` lies in `U`.
  have hab : ∀ x y : ↥C.P.H0, ⁅x, y⁆ ∈ Work.GW2.C16.Uin C := by
    intro x y
    have h : ⁅x, y⁆ ∈ (Work.BG.quotMk C.P).ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact Work.BG.mul_comm_quotGroup C _ _
    simpa [Work.GW2.C16.Uin, QuotientGroup.ker_mk'] using h
  rw [induce_trivial_eq_sum_linearClassFunction (H := Work.GW2.C16.Uin C) hab]
  rw [Work.BG.lambdaSum]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  ext x
  rfl

end Work.BG
