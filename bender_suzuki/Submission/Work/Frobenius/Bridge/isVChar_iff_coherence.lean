import Mathlib
import Submission.Work.Frobenius.Char
import Submission.Work.Coherence.Defs
import Submission.Work.CharCore.Coherence
import Submission.Work.Frobenius.CharZero.mem_span_Irr_of_isClassFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Bridge: `Work.Frobenius.IsVChar` = `Work.Coherence.IsVChar`

The Frobenius area (`Work.Frobenius`) and the coherence area (`Work.Coherence`) each define the
set `Irr G` of irreducible complex characters of a finite group, hence the predicates
`IsChar`/`IsVChar` (non-negative / integral combinations of irreducibles), and these two predicate
families agree.

The two definitions of `Irr` are:

* `Work.Frobenius.Irr G = Set.range (fun d : Work.Frobenius.IrrRep G => d.ρ.character)`, i.e. the
  characters of the irreducible finite dimensional complex representations on a vector space in
  `Type 0`;
* `Work.Coherence.Irr G = {f | ∃ V : FDRep ℂ G, CategoryTheory.Simple V ∧ V.character = f}`.

Both are the same set of functions: every irreducible character occurs among the characters of the
chosen simple submodules of the regular module (`Work.CharCore.irreducible_character_mem_Irr`,
giving `Frobenius.Irr ⊆ Coherence.Irr` after identifying `Work.CharCore.Irr` with
`Work.Coherence.Irr`), and conversely the character of any irreducible representation is an
irreducible character in the `Type 0` sense (`Work.Frobenius.CharZero.char_mem_Irr_of_isIrreducible`,
giving `Coherence.Irr ⊆ Frobenius.Irr`).  Consequently the additive subgroups they generate agree,
which is the statement of the lemma below.
-/

namespace Work.Frobenius.Bridge

/-- The two definitions of the set of irreducible complex characters of `G` agree:
`Work.Frobenius.Irr G = Work.Coherence.Irr G`. -/
theorem mem_Irr_bridge {G : Type*} [Group G] [Fintype G] {f : G → ℂ} :
    f ∈ Irr G ↔ f ∈ Work.Coherence.Irr G := by
  constructor
  · -- `Work.Frobenius.Irr ⊆ Work.Coherence.Irr`
    rintro ⟨d, rfl⟩
    exact (Work.CharCore.mem_Irr_iff_coherence).mp
      (Work.CharCore.irreducible_character_mem_Irr d.ρ d.irred)
  · -- `Work.Coherence.Irr ⊆ Work.Frobenius.Irr`
    rintro ⟨V, hV, rfl⟩
    haveI : CategoryTheory.Simple V := hV
    exact Work.Frobenius.CharZero.char_mem_Irr_of_isIrreducible V.ρ
      (Work.CharCore.isIrreducible_of_simple_fdRep V)

theorem isVChar_iff_coherence {G : Type*} [Group G] [Fintype G] {f : G → ℂ} :
    IsVChar f ↔ Work.Coherence.IsVChar f := by
  have hIrr : Irr G = Work.Coherence.Irr G := Set.ext fun f => mem_Irr_bridge
  simp only [IsVChar, Work.Coherence.IsVChar, hIrr]

end Work.Frobenius.Bridge
