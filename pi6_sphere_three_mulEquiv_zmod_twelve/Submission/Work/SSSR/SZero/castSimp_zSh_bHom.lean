import Mathlib
import Submission.Work.SSSR.SZero.Defs
import Submission.Work.SSSR.KunnethEZ.ez23_eq_ezGen
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR.SZero

open CategoryTheory Opposite
open scoped Simplicial
noncomputable section

/-- The second coordinate map `bHom` of the unique `(0,q)`-shuffle is the canonical
identification `⦋0+q⦌ ⟶ ⦋q⦌` of the two degrees. -/
lemma bHom_zSh_eqToHom (q : ℕ) :
    (Work.SSSR.Cohomology.Crux33.bHom (Work.SSSR.KunnethEZ.zSh q).1 (Work.SSSR.KunnethEZ.zSh q).2 :
      ⦋0+q⦌ ⟶ ⦋q⦌) = eqToHom (congrArg SimplexCategory.mk (Nat.zero_add q)) := by
  apply SimplexCategory.Hom.ext
  rw [SimplexCategory.eqToHom_toOrderHom]
  apply OrderHom.ext
  funext i
  apply Fin.ext
  show ((Work.SSSR.Cohomology.Crux33.bHom (Work.SSSR.KunnethEZ.zSh q).1 (Work.SSSR.KunnethEZ.zSh q).2 :
      ⦋0+q⦌ ⟶ ⦋q⦌) i).val = _
  rw [show (((Work.SSSR.Cohomology.Crux33.bHom (Work.SSSR.KunnethEZ.zSh q).1
        (Work.SSSR.KunnethEZ.zSh q).2) : ⦋0+q⦌ ⟶ ⦋q⦌) i).val = i.val
      from Work.SSSR.KunnethEZ.bHom_val_eq q i]
  simp

/-- `castSimp` is `Eq.mp` along the corresponding equality of objects of the simplex category. -/
lemma castSimp_eq_mp_congrArg {Y : SSet.{0}} {m n : ℕ} (h : m = n) :
    castSimp h = Eq.mp (congrArg (fun X => Y.obj (Opposite.op X))
      (congrArg SimplexCategory.mk h)) := by
  unfold castSimp
  exact congrArg Eq.mp (Subsingleton.elim _ _)

/-- Transporting along a degree equality undoes `Y.map` of the corresponding `eqToHom`. -/
lemma eq_mp_congrArg_map_op_eqToHom {C : Type*} [Category C] (Y : Cᵒᵖ ⥤ Type)
    {A B : C} (h : A = B) (x : Y.obj (op B)) :
    Eq.mp (congrArg (fun X => Y.obj (op X)) h) (Y.map (eqToHom h).op x) = x := by
  cases h
  simp

/-- The `(0,q)`-shuffle reindexing of a `q`-simplex, transported back along `Nat.zero_add q`, is the simplex itself.  (`Work.SSSR.SZero.castSimp h` is the transport `Eq.mp (congrArg (fun k => Y _⦋k⦌) h)` of simplices along a degree equality; `Work.SSSR.KunnethEZ.zSh q` is the unique `(0,q)`-shuffle and `bHom` its second coordinate map `⦋0+q⦌ ⟶ ⦋q⦌`.) -/
theorem castSimp_zSh_bHom {Y : SSet.{0}} (q : ℕ)
    (τ : Y.obj (Opposite.op (SimplexCategory.mk q))) :
    Work.SSSR.SZero.castSimp (Nat.zero_add q)
      (Y.map (Quiver.Hom.op (Work.SSSR.Cohomology.Crux33.bHom (Work.SSSR.KunnethEZ.zSh q).1
        (Work.SSSR.KunnethEZ.zSh q).2)) τ) = τ := by
  rw [bHom_zSh_eqToHom q]
  rw [castSimp_eq_mp_congrArg (Y := Y) (Nat.zero_add q)]
  exact eq_mp_congrArg_map_op_eqToHom Y (congrArg SimplexCategory.mk (Nat.zero_add q)) τ

end

end Work.SSSR.SZero
