import Submission.Work.SSGRoute.ZConstruction.ZDataReduction
import Submission.Work.SSGRoute.z_data_mup_core
import Submission.Work.SSGRoute.shafarevich_z_data_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The one-dimensional gate `Work.SSGRoute.MupGate` is already available

`Work.SSGRoute.z_data_general_of_gates` (`ZConstruction/ZDataReduction.lean`) reduces the general
`z`-data of Schmidt--Wingberg's Theorem 13 to the conjunction of two gates:

* `Work.SSGRoute.MupGate` — the case `finrank (ZMod p) E ≤ 1` (the `A = μ_p` case), and
* `Work.SSGRoute.SpanningGate` — the case in which the local data of `y` spans `E`, in dimension
  `≥ 2`.

This file proves the **first** gate from the two arithmetic cores of Schmidt--Wingberg §4 that
already sit *below* this node in the import order:

* `Work.SSGRoute.z_data_mup_core` (`z_data_mup_core.lean`, odd `p`) and
* `Work.SSGRoute.shafarevich_z_data_two` (`shafarevich_z_data_two.lean`, `p = 2`).

Consequently the obligation `Work.SSGRoute.z_data_general_of_ramified` of the node
`Work.SSGRoute.shafarevich_z_construction` is **exactly** the spanning gate
`Work.SSGRoute.SpanningGate`: everything else (the one-dimensional case, and every coefficient module
whose `cs(S)`-local data is a proper subspace) is either already on disk or pure linear algebra.

Two remarks on the passage.

* The gates are stated for coefficient modules carrying only `AddCommGroup`, `Module (ZMod p)` and
  `Finite`, whereas the arithmetic cores carry in addition the two unused action instances
  `DistribMulAction (K ≃ₐ[k] K) E` and `SMulCommClass (K ≃ₐ[k] K) (ZMod p) E` of the target theorem.
  The two are supplied here by the **trivial** action, which makes every clause of the cores'
  conclusion the corresponding clause of `HasZData` by definitional unfolding (the `1`-cocycle
  clause is additivity because `res k K g • -` is the identity on `G_K`).
* The assumption is on the *existence* of the gates, so no `sorry` of this node is discharged here:
  the axiom footprint of `mupGate_of_cores` is that of the two cores, i.e. it carries `sorryAx` from
  `Work.SSGRoute.sw_z_exists_odd_sketch` and from
  `Work.SSGRoute.shafarevich_z_data_two_kummerCore` — the *shared* arithmetic obligations of the
  fleet, not an obligation of this node.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- **The one-dimensional gate, from the two arithmetic cores.**  For an odd prime `p` this is
`Work.SSGRoute.z_data_mup_core`; for `p = 2` it is `Work.SSGRoute.shafarevich_z_data_two`. -/
theorem mupGate_of_cores {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [Fintype (K ≃ₐ[k] K)] : MupGate (p := p) K := by
  intro Λ _instΛf _instΛg S hAmb E _instE _instM _instF h1 y hy
  obtain ⟨hKΛ, ζ, hζ, hζK, hSfin, hSdisj, hSram⟩ := hAmb
  -- the trivial action of `Gal(K|k)` makes the arithmetic cores applicable
  letI : DistribMulAction (K ≃ₐ[k] K) E :=
    { smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl }
  haveI : SMulCommClass (K ≃ₐ[k] K) (ZMod p) E := ⟨fun _ _ _ => rfl⟩
  rcases eq_or_ne p 2 with hp2 | hp2
  · haveI : IsAlgClosed Ω := (inferInstance : IsAlgClosure k Ω).isAlgClosed
    obtain ⟨z, hz⟩ := shafarevich_z_data_two p hp2 k Ω K Λ hKΛ ζ hζ hζK E h1 S hSfin hSdisj hSram y
      hy.add hy.locconst hy.hyS hy.hyT hy.hy0 hy.hyinf
    exact ⟨z, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2⟩
  · obtain ⟨z, hz⟩ := z_data_mup_core p hp2 k Ω K Λ hKΛ ζ hζ hζK E h1 S hSfin hSdisj hSram y
      hy.add hy.locconst hy.hyS hy.hyT hy.hy0 hy.hyinf
    exact ⟨z, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2⟩

end Work.SSGRoute
