import Mathlib
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.mvCochainDefs
import Submission.Work.Cohomology.mv_shortExact
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.SmallChains
import Submission.Work.Cohomology.SmallChainsIsoAux
import Submission.Work.Cohomology.smallLift_cov

/-!
# Auxiliaries for `coker_smallOfU_iso_relChains`

For `A V : Set X` we consider `V ∩ A` as a subset of `V`, together with the inclusion
`(V, V ∩ A) → (A, A ∩ V)` (the map `(x : V) ↦ (x : X)`, landing in `A`).  These are the
topological maps along which the comparison between the cokernel of `smallOfU A V` and the
relative chains of `(V, V ∩ A)` is made.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- `V ∩ A` viewed as a subset of `V`. -/
abbrev relSubset (A V : Set X) : Set V := setOf (fun x : V => (x : X) ∈ A)

/-- The canonical map `V ∩ A → A`: the inclusion of `V ∩ A` into `V` followed by the inclusion
into `A`. -/
def overlapIncl (A V : Set X) : TopCat.of (relSubset A V) ⟶ TopCat.of A :=
  TopCat.ofHom (ContinuousMap.mk (fun x => (⟨((x : V) : X), x.2⟩ : ↥A)) (by fun_prop))

@[simp]
lemma overlapIncl_apply (A V : Set X) (x : ↥(relSubset A V)) :
    (overlapIncl A V) x = ⟨((x : V) : X), x.2⟩ := rfl

/-- The two inclusions `V ∩ A → A → X` and `V ∩ A → V → X` agree. -/
lemma overlapIncl_comp_subtypeIncl (A V : Set X) :
    overlapIncl A V ≫ subtypeIncl X A
      = subtypeIncl (TopCat.of V) (relSubset A V) ≫ subtypeIncl X V := by
  ext x
  rfl

/-- The map `C_*(V ∩ A) ⟶ C_*(A)` induced by `V ∩ A ⊆ A`. -/
abbrev overlapChainsMap (A V : Set X) :
    singularChains ℤ (TopCat.of (relSubset A V)) ⟶ singularChains ℤ (TopCat.of A) :=
  chainMap ℤ (TopCat.of (relSubset A V)) (TopCat.of A) (overlapIncl A V)

end

end Work.Cohomology
