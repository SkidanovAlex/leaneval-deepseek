import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.Symplectic.Basic
import Submission.Work.PGroup.Symplectic.of_characteristic
import Submission.Work.PGroup.Symplectic.conclusion_map_subtype

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `AllAbelianCharCyclic` transports to the top subgroup

If every abelian characteristic subgroup of `X` is cyclic, then the same holds in `↥(⊤ : Subgroup X)`,
where `⊤` is the top subgroup regarded as a group in its own right.  This is used when the
structure theorem for class-two groups (`Work.PGroup.Symplectic.omega_one_structure_of_class_two`)
is applied with `C = ⊤`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical Pointwise
open Subgroup

namespace Work.PGroup.Symplectic

/-- `AllAbelianCharCyclic` transports to the top subgroup. -/
theorem allAbelianCharCyclic_top {X : Type*} [Group X] (h : Work.PGroup.AllAbelianCharCyclic X) :
    Work.PGroup.AllAbelianCharCyclic ↥(⊤ : Subgroup X) := by
  intro A hA hAc
  have hchar : (A.map (⊤ : Subgroup X).subtype).Characteristic :=
    map_subtype_characteristic Subgroup.topCharacteristic hA
  have hcomm : IsMulCommutative ↥(A.map (⊤ : Subgroup X).subtype) :=
    (ConclusionMapSubtype.isMulCommutative_map_subtype_iff A).mpr hAc
  obtain ⟨a, ha⟩ := h (A.map (⊤ : Subgroup X).subtype) hchar hcomm
  refine ⟨⟨a, trivial⟩, ?_⟩
  apply Subgroup.map_injective (f := (⊤ : Subgroup X).subtype) (Subgroup.subtype_injective ⊤)
  rw [MonoidHom.map_zpowers, ha]
  rfl

end Work.PGroup.Symplectic
