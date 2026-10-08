import Submission.Work.Hering.Wagner.Defs
import Submission.Work.Hering.Wagner.Core
import Submission.Work.Hering.Wagner.step6_pieces
import Submission.Work.Hering.Wagner.inducedSub_transvection_pieces
import Submission.Work.Hering.Wagner.wagnerProp_of_linear

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Wagner's proposition (Peterfalvi I §1, p. 188)

This is the target file of the `Hering.Wagner` area: it assembles the linear form of Wagner's
proposition from the orbit-counting chain of `Core.lean` (`Peterfalvi I §1`, steps 1--5), the
transvection argument of step 6, and the dictionary between an elementary abelian `2`-group and
a `ZMod 2`-vector space (`wagnerProp_of_linear`).
-/

set_option autoImplicit false

namespace Work.Hering.Wagner

/-- **Wagner's proposition, linear form.**  If `Gm ≤ GL(V)` is doubly transitive on the nonzero
vectors of a finite-dimensional `𝔽₂`-space `V`, then for every 3-dimensional subspace `U` every
linear automorphism of `U` is induced by an element of `Gm`. -/
theorem wagner_core {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Gm : Subgroup (V ≃ₗ[ZMod 2] V)) (h2 : IsTwoTrans Gm)
    (U : Submodule (ZMod 2) V) (hU : Module.finrank (ZMod 2) U = 3) (φ : U ≃ₗ[ZMod 2] U) :
    ∃ g ∈ Gm, ∀ u : U, g u = φ u := by
  have htop : inducedSub Gm U = ⊤ :=
    step6_subgroup_eq_top hU (inducedSub Gm U)
      (fun X hX a haX ha0 => inducedSub_transvection_pieces h2 U hU X hX a haX ha0)
  have hmem : φ ∈ inducedSub Gm U := by rw [htop]; exact Subgroup.mem_top φ
  obtain ⟨g, hg, hgφ⟩ := mem_inducedSub.mp hmem
  exact ⟨g, hg, hgφ⟩

/-- **Wagner's proposition** (Peterfalvi I §1, p. 188), multiplicative form. -/
theorem wagner_prop : WagnerProp :=
  wagnerProp_of_linear (fun {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Gm : Subgroup (V ≃ₗ[ZMod 2] V)) (h2 : IsTwoTrans Gm)
    (U : Submodule (ZMod 2) V) (hU : Module.finrank (ZMod 2) U = 3) (φ : U ≃ₗ[ZMod 2] U) =>
      wagner_core Gm h2 U hU φ)

end Work.Hering.Wagner
