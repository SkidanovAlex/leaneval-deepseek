import Mathlib
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.DualComplexMap
import Submission.Work.Cohomology.kronH_natural
import Submission.Work.StemsB.FieldDualUCT
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The evaluation pairing of a chain complex with its dual over a field: definitions

This file records the two properties of the evaluation pairing
`H^n(Hom_F(E,F)) ⟶ Hom_F(H_n(E), F)`, `⟨[w],[z]⟩ = w(z)`, that the main theorem
`Work.Pi6.SQM.SIG.dualEvalPair` asserts:

* `IsEvalPair F kron` — the computation rule `⟨[w],[z]⟩ = w(z)` on classes of cycles;
* `IsNaturalKron F kron` — naturality in the chain complex.

They are separated out so that the construction of `kron` and the proofs of its bijectivity and
naturality can be stated as independent lemmas about these predicates.
-/

namespace Work.Pi6.SQM.SIG

/-- **The computation rule for the evaluation pairing of a chain complex with its dual**: on the
class of a cocycle `w` of the dual complex and the class of a cycle `z`, the pairing is the
evaluation of the underlying functional. -/
def IsEvalPair (F : Type) [Field F]
    (kron : ∀ (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ),
      (Work.Cohomology.dualComplex F E).homology n →ₗ[F] ((E.homology n) →ₗ[F] F)) : Prop :=
  ∀ (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ)
    (w : (Work.Cohomology.dualComplex F E).cycles n) (z : E.cycles n),
    kron E n ((Work.Cohomology.dualComplex F E).homologyπ n w) (E.homologyπ n z)
      = Work.StemsB.fdVal F E n ((Work.Cohomology.dualComplex F E).iCycles n w)
          ((E.iCycles n).hom z)

/-- **Naturality of the evaluation pairing**: for a chain map `g : C ⟶ D`,
`⟨a, g_* b⟩ = ⟨g^* a, b⟩`. -/
def IsNaturalKron (F : Type) [Field F]
    (kron : ∀ (E : ChainComplex (ModuleCat.{0} F) ℕ) (n : ℕ),
      (Work.Cohomology.dualComplex F E).homology n →ₗ[F] ((E.homology n) →ₗ[F] F)) : Prop :=
  ∀ {C D : ChainComplex (ModuleCat.{0} F) ℕ} (g : C ⟶ D) (n : ℕ)
    (a : (Work.Cohomology.dualComplex F D).homology n) (b : C.homology n),
    kron D n a ((HomologicalComplex.homologyMap g n) b)
      = kron C n ((HomologicalComplex.homologyMap
          (Work.Cohomology.dualComplexMap F C D g) n) a) b

end Work.Pi6.SQM.SIG
