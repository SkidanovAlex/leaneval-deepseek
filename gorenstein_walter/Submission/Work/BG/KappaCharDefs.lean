import Mathlib

/-!
# Area BG: auxiliary definitions for `Work.BG.kappaCharExists`

The lemma `Work.BG.kappaCharExists` produces a non-trivial linear character `χ` of a subgroup
`U ≤ G` (of odd order) which is fixed by conjugation with a 2-subgroup `S ≤ N_G(U)`.

The engine of the proof is the *abelianisation* `U/U'` of `U`: a homomorphism `U →* ℂˣ` that is
trivial on `⁅U,S⁆` is the same thing as a homomorphism `U/U' →* ℂˣ` that is trivial on the image of
`⁅U,S⁆`, and the fixed points of the conjugation action of `S` on `U/U'` can be analysed with the
elementary "averaging" argument for coprime actions on abelian groups.

This module collects the definitions used by both the main proof and the auxiliary lemmas:

* `Work.BG.derivedU U` — the derived subgroup `U' = ⁅U,U⁆` of `U`, as a subgroup of `↥U`;
* `Work.BG.Uab U` — the abelianisation `↥U ⧸ U'`, with a `CommGroup` instance;
* `Work.BG.UabMk U` — the quotient projection `↥U →* Uab U`.
-/

namespace Work.BG

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

/-- The derived subgroup `U' = ⁅U,U⁆` of a subgroup `U ≤ G`, viewed as a subgroup of `↥U`. -/
abbrev derivedU (U : Subgroup G) : Subgroup ↥U := (⁅U, U⁆).subgroupOf U

instance instNormalDerivedU (U : Subgroup G) : (derivedU U).Normal := by
  have h := Subgroup.normal_subgroupOf_commutator_sup U U
  rwa [sup_idem] at h

/-- The abelianisation `U/U'` of a subgroup `U ≤ G`. -/
abbrev Uab (U : Subgroup G) : Type := ↥U ⧸ derivedU U

instance instIsMulCommutativeUab (U : Subgroup G) : IsMulCommutative (Uab U) := by
  refine Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr ?_
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro x _ y _
  rw [Subgroup.mem_subgroupOf,
    show ((⁅x, y⁆ : ↥U) : G) = ⁅(x : G), (y : G)⁆ from
      map_commutatorElement (Subgroup.subtype U) x y]
  exact (Subgroup.commutator_le.mp le_rfl) (x : G) x.2 (y : G) y.2

noncomputable instance instCommGroupUab (U : Subgroup G) : CommGroup (Uab U) :=
  { (inferInstance : Group (Uab U)) with
    mul_comm := fun a b => (IsMulCommutative.is_comm (M := Uab U)).comm a b }

/-- The quotient projection `↥U →* U/U'`. -/
noncomputable def UabMk (U : Subgroup G) : ↥U →* Uab U := QuotientGroup.mk' (derivedU U)

@[simp] lemma UabMk_apply (U : Subgroup G) (x : ↥U) :
    UabMk U x = (QuotientGroup.mk' (derivedU U)) x := rfl

/-- The kernel of the projection `↥U →* U/U'` is the derived subgroup. -/
lemma UabMk_eq_one_iff (U : Subgroup G) (x : ↥U) : UabMk U x = 1 ↔ (x : G) ∈ ⁅U, U⁆ := by
  rw [UabMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

lemma UabMk_surjective (U : Subgroup G) : Function.Surjective (UabMk U) :=
  QuotientGroup.mk'_surjective _

end Work.BG
