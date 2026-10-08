import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irreducible_character_mem_Irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.CharCore

/-- The trivial complex representation of `G` on `ℂ` has the constant function `1` as its
character: it is the identity endomorphism at every group element, whose trace is
`finrank ℂ ℂ = 1`. -/
theorem trivialRep_character {G : Type*} [Group G] :
    (Representation.trivial ℂ G ℂ).character = (fun _ : G => (1 : ℂ)) := by
  funext g
  rw [Representation.character]
  show (LinearMap.trace ℂ ℂ) ((Representation.trivial ℂ G ℂ) g) = 1
  have h1 : (Representation.trivial ℂ G ℂ) g = (1 : ℂ →ₗ[ℂ] ℂ) := rfl
  rw [h1, LinearMap.trace_one, Module.finrank_self]
  norm_num

/-- The trivial complex representation of `G` on the one-dimensional space `ℂ` is irreducible:
its underlying `ℂ[G]`-module is one-dimensional over `ℂ`, hence simple. -/
theorem trivialRep_isIrreducible {G : Type*} [Group G] :
    (Representation.trivial ℂ G ℂ).IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  have hfr : Module.finrank ℂ (Representation.trivial ℂ G ℂ).asModule = 1 := by
    rw [(Representation.asModuleEquiv (Representation.trivial ℂ G ℂ)).finrank_eq,
      Module.finrank_self]
  rw [isSimpleModule_iff]
  exact is_simple_module_of_finrank_eq_one hfr

/-- The principal (trivial) character of a finite group is irreducible. -/
theorem principalChar_mem_Irr {G : Type*} [Group G] [Fintype G] :
    (fun _ : G => (1 : ℂ)) ∈ Irr G := by
  have hmem := irreducible_character_mem_Irr (Representation.trivial ℂ G ℂ)
    (trivialRep_isIrreducible (G := G))
  rwa [trivialRep_character] at hmem

end Work.CharCore
