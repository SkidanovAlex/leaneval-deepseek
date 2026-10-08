/-
# `Work.ThreePoints.BenderPrelim` — discharging area `NormalComplement`'s Ch. I/II inputs

`Submission.Work.NormalComplement.Prelim` records two statements of Peterfalvi I Ch. I §2
Prop. 2(b) that no area `Prop` exposes and that Chapter III of the paper (Theorem D) uses:

* `BenderPrelimProp` — `D = H ⊓ H^t` acts transitively on `Inv(H)`;
* `BenderPrelimCountProp` — `|K| = |Inv H|` for `K = J(D,t) = invertedBy (twoPoint H t) t`.

Both are proved here from Peterfalvi I Ch. I §2 (via
`Work.ThreePoints.twoPoint_transitive_on_involutions`, `Work.ThmF.Bender.cardKsetEqInv`), so
area `NormalComplement` can drop them as hypotheses:

```lean
Work.ThreePoints.benderPrelimProp : Work.NormalComplement.BenderPrelimProp
Work.ThreePoints.benderPrelimCountProp : Work.NormalComplement.BenderPrelimCountProp
```
-/
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.NormalComplement.Prelim
import Submission.Work.ThmG.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

/-- Peterfalvi I Ch. I §2 Prop. 2(b): `D = H ⊓ H^t` acts transitively on the involutions of `H`
(area `NormalComplement`'s `BenderPrelimProp`). -/
theorem benderPrelimProp : Work.NormalComplement.BenderPrelimProp := by
  intro G _ _ hS H hH t ht htH u hu v hv
  exact twoPoint_transitive_on_involutions hH ht htH hu hv

/-- Peterfalvi I Ch. I §2 Prop. 2(b): `|K| = |Inv H|`
(area `NormalComplement`'s `BenderPrelimCountProp`). -/
theorem benderPrelimCountProp : Work.NormalComplement.BenderPrelimCountProp := by
  intro G _ _ hS H hH t ht htH
  exact Work.ThmF.Bender.cardKsetEqInv hH ht htH

/-- Peterfalvi I Ch. I §2 (with `|K| = |Inv H| = n ≥ 3`): `K = J(D,t) ≠ 1`.
This is field 1 (`KNeOneProp`) of area `ThmG`'s split rank-one structure. -/
theorem kNeOneProp : Work.ThmG.KNeOneProp := by
  intro G _ _ H Q t h
  haveI : Finite G := inferInstance
  obtain ⟨hSit, -, hsplit, -, -⟩ := h
  have hH : IsStronglyEmbedded H := hsplit.stronglyEmbedded
  have ht : orderOf t = 2 := hsplit.invol
  have htH : t ∉ H := hsplit.not_mem
  have hK : (invertedBy (twoPoint H t) t).ncard = (involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardKsetEqInv hH ht htH
  -- `H` contains two distinct involutions, so `|Inv H| ≥ 2`
  obtain ⟨a, b, ha2, hb2, hab, hcomm⟩ := hSit.1.1
  obtain ⟨g, hg⟩ := Work.ThmF.Bender.exists_conj_of_involution hH ha2
  have hgH : IsStronglyEmbedded (conj g H) := conj_stronglyEmbedded hH g
  have hbK : b ∈ conj g H :=
    (Work.ThmF.centralizer_involution_le hgH hg ha2) (by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hcomm)
  have h2 := Work.ThmF.Bender.two_le_ncard_involutions_of_commuting_involutions
    hgH hg ha2 hb2 hab hcomm
  have hcard_conj : (involutions (H : Set G)).ncard = (involutions (conj g H : Set G)).ncard := by
    rw [Work.Models.involutions_conj]
    exact (Set.ncard_image_of_injective _
      (fun x y hxy => by simpa using congrArg (fun z => g⁻¹ * z * g) hxy)).symm
  have hK2 : 2 ≤ (invertedBy (twoPoint H t) t).ncard := by
    rw [hK, hcard_conj]; exact h2
  by_contra hcon
  have hsub : invertedBy (twoPoint H t) t ⊆ ({1} : Set G) := by
    intro x hx
    rw [Set.mem_singleton_iff]
    by_contra hx1
    exact hcon ⟨x, hx, hx1⟩
  have hle := Set.ncard_le_ncard hsub
  rw [Set.ncard_singleton] at hle
  omega

end Work.ThreePoints
