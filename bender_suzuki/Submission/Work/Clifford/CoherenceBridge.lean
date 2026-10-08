import Submission.Work.Clifford.CFun
import Submission.Work.Coherence.Defs
import Submission.Work.Coherence.Inner
import Submission.Work.Clifford.cfInner_eq_ite_of_mem_Irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.CoherenceBridge`: agreement with the `Work.Coherence` vocabulary

The area `Work.Coherence` (Feit–Thompson §10 / Peterfalvi §5) fixes the vocabulary of
irreducible characters, the inner product and class functions that the whole project uses:

* `Work.Coherence.Irr G = {f | ∃ V : FDRep ℂ G, Simple V ∧ V.character = f}`,
* `Work.Coherence.cfInner f g = |G|⁻¹ ∑ x, f x * conj (g x)`,
* `Work.Coherence.IsClassFun f = ∀ g h, f (h * g * h⁻¹) = f g`.

`Work.Clifford` was written before those landed and copies the same three notions (with the
same formulas) at an arbitrary universe, because `Work.CharLib`'s originals are confined to
`Type 0`; see `Submission/Work/Clifford/Basic.lean`.  This file records that the copies are
*definitionally equal* to the `Work.Coherence` ones, so results stated in either vocabulary
transfer by `rfl` (in practice `simpa` with the lemmas below).

Remark.  `Work.Clifford.cfInner` and `IsClassFun` are also definitionally equal to
`Work.CharLib.cfInner`/`IsClassFun` on groups in `Type 0`; see
`Work.Clifford.cfInner_eq_charLib`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Classical

namespace Work.Clifford

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- `Work.Clifford.Irr` is `Work.Coherence.Irr` (definitionally). -/
theorem irr_eq_coherence : Irr G = Coherence.Irr G := rfl

@[simp] theorem mem_Irr_iff_coherence {χ : G → ℂ} :
    χ ∈ Irr G ↔ χ ∈ Coherence.Irr G := Iff.rfl

/-- `Work.Clifford.cfInner` is `Work.Coherence.cfInner` (definitionally). -/
theorem cfInner_eq_coherence (f g : G → ℂ) : cfInner f g = Coherence.cfInner f g := rfl

/-- `Work.Clifford.IsClassFun` is `Work.Coherence.IsClassFun` (definitionally). -/
theorem isClassFun_iff_coherence (f : G → ℂ) : IsClassFun f ↔ Coherence.IsClassFun f :=
  Iff.rfl

/-- The `Work.Clifford` normalisation of an irreducible character. -/
theorem cfInner_eq_ite_of_mem_Irr_coherence {χ ψ : G → ℂ}
    (hχ : χ ∈ Coherence.Irr G) (hψ : ψ ∈ Coherence.Irr G) :
    Coherence.cfInner χ ψ = if χ = ψ then 1 else 0 :=
  cfInner_eq_ite_of_mem_Irr (G := G) hχ hψ

end Work.Clifford
