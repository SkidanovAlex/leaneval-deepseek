import Mathlib
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Pi6.SQM.SIG.dualEvalPair
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The explicit field universal coefficient theorem

For a field `F` and a chain complex `E` of `F`-vector spaces, the universal coefficient theorem
`Work.StemsB.fieldDualUCT` produces *some* linear equivalence
`Hⁿ(Hom_F(E,F)) ≃ Hom_F(Hₙ(E),F)`.  Here we record one which is *explicit*: the class of a
cocycle `α` of the dual complex corresponds to the functional `[z] ↦ α(z)` on the class of a
cycle `z` of `E`.

The pairing in question is `Work.Pi6.SQM.SIG.sigKron`, whose computation rule on the classes of
cycles is `Work.Pi6.SQM.SIG.sigKron_spec` and whose bijectivity over a field is
`Work.Pi6.SQM.SIG.sigKron_bijective`.
-/

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits HomologicalComplex

/-- **The explicit field universal coefficient isomorphism.**  There is a linear equivalence
`Hⁿ(Hom_F(E,F)) ≃ₗ[F] Hom_F(Hₙ(E), F)` which, on the class of a cocycle `α` of the dual complex
and the class of a cycle `z` of `E`, is the evaluation of `α` on `z`. -/
theorem fieldDualUCT_explicit (F : Type) [Field F] (E : ChainComplex (ModuleCat F) ℕ) (n : ℕ) :
    ∃ e : (Work.Cohomology.dualComplex F E).homology n ≃ₗ[F] (↥(E.homology n) →ₗ[F] F),
      ∀ (α : (Work.Cohomology.dualComplex F E).cycles n) (z : E.cycles n),
        e (((Work.Cohomology.dualComplex F E).homologyπ n) α) ((E.homologyπ n) z)
          = Work.StemsB.fdVal F E n (((Work.Cohomology.dualComplex F E).iCycles n) α)
              ((E.iCycles n) z) := by
  refine ⟨LinearEquiv.ofBijective (Work.Pi6.SQM.SIG.sigKron F E n)
    (Work.Pi6.SQM.SIG.sigKron_bijective F E n), ?_⟩
  intro α z
  simp only [LinearEquiv.ofBijective_apply]
  exact Work.Pi6.SQM.SIG.sigKron_spec F E n α z

end Work.Pi6.MSS
