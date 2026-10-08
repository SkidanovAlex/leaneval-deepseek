import Mathlib
import Submission.Work.Frobenius.Char
import Submission.Work.Coherence.Defs
import Submission.Work.CharCore.mem_Irr_iff_fdrep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Bridge: `Work.Frobenius.Irr` and `Work.Coherence.Irr` agree

`Work.Frobenius.Irr G` is the set of characters of irreducible finite dimensional complex
representations of `G`, bundled as `IrrRep` (whose `irred` field is
`Representation.IsIrreducible`).  `Work.Coherence.Irr G` is the set of characters of the simple
objects of the category `FDRep ℂ G`.

`Work.CharCore.fdRep_simple_iff` identifies categorical simplicity of `V : FDRep ℂ G` with
irreducibility of the underlying representation `V.ρ`, so `FDRep.of` and `FDRep.ρ` translate
between the two presentations; hence the two sets of characters coincide.
-/

namespace Work.Frobenius.Bridge

open CategoryTheory

theorem mem_Irr_iff_coherence {G : Type*} [Group G] [Fintype G] {f : G → ℂ} :
    f ∈ Irr G ↔ f ∈ Work.Coherence.Irr G := by
  constructor
  · rintro ⟨d, rfl⟩
    refine ⟨FDRep.of d.ρ, ?_, ?_⟩
    · rw [Work.CharCore.fdRep_simple_iff]
      rw [FDRep.of_ρ']
      exact d.irred
    · exact Work.CharCore.fdRep_character_of_eq d.ρ
  · rintro ⟨V, hV, rfl⟩
    let d : IrrRep G :=
      { V := ↥V, ρ := V.ρ, irred := (Work.CharCore.fdRep_simple_iff V).mp hV }
    exact ⟨d, rfl⟩

end Work.Frobenius.Bridge
