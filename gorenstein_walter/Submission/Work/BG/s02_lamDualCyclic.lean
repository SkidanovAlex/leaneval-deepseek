import Mathlib
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.s02_quotCyclic

/-!
# Area BG: the dual group of `H₀/U` is finite cyclic

`Work.BG.lamDual C = (H₀/U →* ℂˣ)` is the dual (character) group of `H₀/U`: a homomorphism
`H₀/U →* ℂˣ` is precisely a linear character of `H₀/U`, and `lamCF` inflates it to a class
function on `H₀`.

Since `H₀/U` is a finite **cyclic** group (`Work.BG.quotGroup_isCyclic`), its dual is again
finite and cyclic.  Both halves are instances of Mathlib's theory of the dual of a finite
cyclic group:

* `Finite (L →* Rˣ)` for `L` a finite left cancellative monoid and `R` an integral domain
  (`RootsOfUnity.Basic`);
* `IsCyclic.monoidHom_equiv_self`: for a finite cyclic **commutative** group `A` the dual
  `A →* ℂˣ` is (non-canonically) isomorphic to `A`, hence cyclic.

The only work is bookkeeping: `Sec2Ctx` supplies commutativity of `H₀/U` as a *lemma*
(`Work.BG.mul_comm_quotGroup`), not as an instance.  Installing it with `letI` (a local,
definitionally transparent definition whose underlying group is the existing one) keeps all
instance arguments definitionally equal to the ones in the statement, so the Mathlib lemmas
apply verbatim.
-/

-- The local instances below are needed in the proof context and are defined with
-- `letI`/`haveI` precisely so that typeclass search can use them; the style linter's
-- advice (`let`/`have`) would break instance resolution.
set_option linter.style.haveILetI false

namespace Work.BG

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem s02_lamDualCyclic {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G) :
    Finite (Work.BG.lamDual C) ∧ IsCyclic (Work.BG.lamDual C) := by
  refine ⟨inferInstance, ?_⟩
  -- `H₀/U` is cyclic, hence commutative; install the commutative group structure locally.
  -- This is a *transparent* local definition (`letI`), so that the `Pow ℤ` instance it
  -- induces is definitionally equal to the canonical one, and the dual-group theory applies.
  letI : CommGroup (quotGroup C.P) :=
    { (inferInstance : Group (quotGroup C.P)) with mul_comm := mul_comm_quotGroup C }
  haveI hcyc : IsCyclic (quotGroup C.P) := quotGroup_isCyclic C
  obtain ⟨e⟩ := IsCyclic.monoidHom_equiv_self (quotGroup C.P) ℂ
  exact (MulEquiv.isCyclic e).mpr hcyc

end Work.BG
