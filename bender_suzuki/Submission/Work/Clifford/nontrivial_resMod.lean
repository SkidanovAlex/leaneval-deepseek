import Mathlib
import Submission.Work.Clifford.ResSetup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.nontrivial_resMod`

For a finite group `G`, a subgroup `N ≤ G` and a simple complex representation
`V : FDRep ℂ G`, the restriction `Work.Clifford.ResMod N V` of `V` to `N` has a
nontrivial underlying type.

Concretely, `ResMod N V` is `V` endowed with the `ℂ[N]`-module structure obtained
by restricting along `N ↪ G`, so it suffices to observe that a simple object of
`FDRep ℂ G` is nonzero: if its underlying type were a subsingleton, then the
identity `𝟙 V` would equal the zero morphism `0`, contradicting
`CategoryTheory.id_nonzero`.
-/

namespace Work.Clifford

open CategoryTheory

theorem nontrivial_resMod {G : Type*} [Group G] [Fintype G] {N : Subgroup G}
    (V : FDRep ℂ G) [CategoryTheory.Simple V] : Nontrivial (ResMod N V) := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  -- A subsingleton underlying type forces `𝟙 V = 0`.
  refine CategoryTheory.id_nonzero V ?_
  apply Action.hom_ext
  rw [Action.id_hom, Action.zero_hom]
  ext x
  exact hsub.elim x 0

end Work.Clifford
