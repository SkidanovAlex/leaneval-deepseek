/-
# `F_{2'}(C_X(t))` centralizes a normal quasisimple `E ≤ C_X(t)`

This file proves

* `Work.DSTR.centralizes_of_mem_fittingPiIn` : if `E ◁ X` is quasisimple and `t` centralizes `E`,
  then every element of `F_{2'}(C_X(t))` centralizes `E`.

## Mathematics

Put `C = C_X(t)`.  Since `E ≤ C` and `E ◁ X`, the subgroup `E` is normal in `C` and remains
quasisimple there (`E.subgroupOf C ≃ E`), so `E` is contained in the layer `E(C)`.  By
`Work.BMAX.LayerCentralizesFitting` (`[E(C), F(C)] = 1`, proved from scratch in area `BMAX`
via the standard `E/Z(E)`-simple dichotomy) we get `E ≤ E(C) ≤ C_X(F(C))`, and
`F_{2'}(C) ≤ F(C)`.  Hence `F_{2'}(C_X(t)) ≤ C_X(E)`.

## Formalisation

The only non-elementary step is `Work.BMAX.LayerCentralizesFitting`; the assembly below is the
observation `E ≤ E(C)` together with the monotonicity `fittingPiIn_le_fittingIn`
(`Work.BMAX.Basic`).
-/
import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.BMAX.Basic
import Submission.Work.BMAX.LayerCentralizesFitting
import Submission.Work.BMAX.commutator_eq_bot_of_isQuasisimple_of_isQuasisimple

namespace Work.DSTR

-- The hypothesis `hxK` (`x ∈ C_X(t)`) is implied by the conclusion together with `hEt`
-- (`[E,t] = 1`), so it is not needed in the proof; silence the unused-variable linter.
set_option linter.unusedVariables false in
/-- If `t` centralizes a normal quasisimple subgroup `E ◁ X` and `x ∈ F_{2'}(C_X(t))` commutes
with `t`, then `x` centralizes `E`. -/
theorem centralizes_of_mem_fittingPiIn {X : Type*} [Group X] [Finite X]
    (E : Subgroup X) [E.Normal] (hEq : Work.GW2.IsQuasisimple E) (t x : X)
    (hEt : E ≤ Subgroup.centralizer ({t} : Set X))
    (hxK : x ∈ Subgroup.centralizer ({t} : Set X))
    (hx : x ∈ Work.GW2.fittingPiIn {n : ℕ | n ≠ 2} (Subgroup.centralizer ({t} : Set X))) :
    x ∈ Subgroup.centralizer (E : Set X) := by
  -- `C = C_X(t)`, the ambient centralizer of `t`
  set C : Subgroup X := Subgroup.centralizer ({t} : Set X) with hCdef
  have hEC : E ≤ C := hEt
  -- `E`, viewed inside `C`, is still normal and quasisimple
  have hEsubNormal : (E.subgroupOf C).Normal := inferInstance
  have hEsubQuasi : Work.GW2.IsQuasisimple (E.subgroupOf C) :=
    Work.BMAX.QuasiComm.isQuasisimple_subgroupOf hEC hEq
  -- hence `E ≤ E(C)`
  have hEleLayer : E.subgroupOf C ≤ Work.GW2.layer C :=
    le_sSup ⟨hEsubNormal, hEsubQuasi⟩
  have hEleLayerIn : E ≤ Work.GW2.layerIn C := by
    rw [Work.GW2.layerIn, ← Subgroup.map_subgroupOf_eq_of_le hEC]
    exact Subgroup.map_mono hEleLayer
  -- and `F_{2'}(C) ≤ F(C)`
  have hxFit : x ∈ Work.GW2.fittingIn C := Work.GW2.fittingPiIn_le_fittingIn _ C hx
  -- `[E(C), F(C)] = 1` (`Work.BMAX.LayerCentralizesFitting`, universe-polymorphic form)
  have hcent : Work.GW2.layerIn C ≤ Subgroup.centralizer (Work.GW2.fittingIn C : Set X) :=
    Work.BMAX.map_le_centralizer_map C.subtype (Work.BMAX.layer_le_centralizer_fitting C)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact ((Subgroup.mem_centralizer_iff.mp (hcent (hEleLayerIn hy))) x hxFit).symm

end Work.DSTR
