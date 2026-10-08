import Mathlib
import Submission.Work.Clifford.ResSetup
import Submission.Work.Clifford.char_mem_Irr_of_isSimpleModule

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.exists_simple_fdrep_of_submodule`

Let `N ⊴ G` be a normal subgroup of a finite group, `V : FDRep ℂ G`, and let
`S ≤ ResMod N V` be a simple `ℂ[N]`-submodule of the restriction of `V` to `N`.
Then `S` is an irreducible `ℂ`-representation of `N` (an object of `FDRep ℂ N`),
and its character is the trace of the action of `N` on `S`, i.e. the sub-character
`Work.Clifford.subChar V S` defined in `ResSetup`.

The categorical simplicity is Schur's lemma, already established for a general simple
finite dimensional `ℂ[N]`-module in `Work.Clifford.simple_fdRep_ofModule'`; here we only
have to supply the finite-dimensionality of `↥S` over `ℂ` (a Noetherian argument, since
`ℂ[N]` is finite over `ℂ` and `ResMod N V` is finite over `ℂ[N]`) and identify the
character of the resulting representation with `subChar`.
-/

noncomputable section

open Classical
open scoped MonoidAlgebra
open CategoryTheory

namespace Work.Clifford

theorem exists_simple_fdrep_of_submodule {G : Type*} [Group G] [Fintype G] {N : Subgroup G}
    [N.Normal] (V : FDRep ℂ G) {S : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)}
    (hS : IsSimpleModule (MonoidAlgebra ℂ ↥N) ↥S) :
    ∃ W : FDRep ℂ N, CategoryTheory.Simple W ∧ ∀ n : N, W.character n = subChar V S n := by
  -- `↥S` is finite dimensional over `ℂ`.
  haveI : Module.Finite ℂ ↥S := by
    haveI : Module.Finite ℂ (MonoidAlgebra ℂ ↥N) := inferInstance
    haveI : IsNoetherianRing (MonoidAlgebra ℂ ↥N) :=
      IsNoetherianRing.of_finite ℂ (MonoidAlgebra ℂ ↥N)
    haveI : Module.Finite (MonoidAlgebra ℂ ↥N) (ResMod N V) :=
      Module.Finite.of_restrictScalars_finite ℂ (MonoidAlgebra ℂ ↥N) (ResMod N V)
    haveI : IsNoetherian (MonoidAlgebra ℂ ↥N) (ResMod N V) := inferInstance
    haveI : IsNoetherian (MonoidAlgebra ℂ ↥N) ↥S := inferInstance
    haveI : Module.Finite (MonoidAlgebra ℂ ↥N) ↥S := inferInstance
    exact Module.Finite.trans (MonoidAlgebra ℂ ↥N) ↥S
  refine ⟨FDRep.of (Representation.ofModule' (k := ℂ) (G := ↥N) ↥S),
    simple_fdRep_ofModule' ↥S hS, fun n => ?_⟩
  rw [character_fdRep_of, Representation.character, subChar_apply]
  congr 1
  ext s
  rw [ofModule'_apply_of]
  rw [Submodule.coe_smul, of_smul, subAct_apply]

end Work.Clifford
