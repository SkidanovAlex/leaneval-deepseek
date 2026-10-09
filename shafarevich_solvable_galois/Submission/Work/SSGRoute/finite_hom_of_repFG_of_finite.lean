import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ext_level_lift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- Morphisms of `Coeff`-representations of a finite group form a finite set as soon as the source
is a finitely generated `ℤ`-module and the target is finite as a type.

Indeed, an intertwining map is in particular additive, so it is determined by its values on a
finite generating set `S` of `↥M`; the resulting injection `(M ⟶ A) → (↥S → ↥A)` targets a
finite type. -/
theorem finite_hom_of_repFG_of_finite {G : Type} [Group G] [Fintype G]
    (M A : Rep.{0} SSGRoute.PTExt.Coeff G) [Finite A] (hM : Module.Finite ℤ ↥M) :
    Finite (M ⟶ A) := by
  obtain ⟨S, hS⟩ := hM.fg_top
  refine Finite.of_injective (fun (f : M ⟶ A) (x : ↥S) => f.hom (x : ↥M)) ?_
  intro f g hfg
  have key : ∀ x : ↥M, f.hom x = g.hom x := by
    have hcl : AddSubgroup.closure (↑S : Set ↥M) = ⊤ := by
      rw [← Submodule.span_int_eq_addSubgroupClosure, hS, Submodule.top_toAddSubgroup]
    let H : AddSubgroup ↥M :=
      { carrier := {x | f.hom x = g.hom x},
        zero_mem' := by simp,
        add_mem' := fun ha hb => by
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          rw [map_add, map_add, ha, hb],
        neg_mem' := fun ha => by
          simp only [Set.mem_ofPred_eq] at ha ⊢
          rw [map_neg, map_neg, ha] }
    have hSH : (↑S : Set ↥M) ⊆ (H : Set ↥M) := fun y hy => congrFun hfg ⟨y, hy⟩
    have hle : AddSubgroup.closure (↑S : Set ↥M) ≤ H := (AddSubgroup.closure_le H).mpr hSH
    rw [hcl] at hle
    intro x
    exact hle (AddSubgroup.mem_top x)
  let _ : Module SSGRoute.PTExt.Coeff ↥M := M.hV2
  let _ : Module SSGRoute.PTExt.Coeff ↥A := A.hV2
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  exact key x

end Work.SSGRoute
