import Mathlib
import Submission.Work.DSF1.Sheaf.CechAugNat

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

universe u

/-- The degree-zero component of the Čech nerve at the constant simplex `fun _ => i` is the open
`U i`.  (`(cechN U 0).obj y = ∏ᶜ (U ∘ y)` and a product of one open is that open.) -/
lemma cechN_obj_const {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (i : ι) :
    (cechN U 0).obj (fun _ : Fin 1 => i) = U i := by
  rw [cechN_obj]
  exact piFin1

/-- **Injectivity of the augmentation.**  For a sheaf of abelian groups `P`, a family of opens `U`
and an open `W`, the augmentation `P ((⨆ U) ⊓ W) ⟶ ∏_y P ((cechN U 0).obj y ⊓ W)` is injective.
A section whose image is zero restricts to zero on each `(cechN U 0).obj (fun _ => i) ⊓ W = U i ⊓ W`,
and these opens cover `(⨆ U) ⊓ W`, so it is zero by separatedness of the sheaf `P`. -/
theorem cechAugNat_injective {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens)
    (P : CategoryTheory.Functor (Opposite (X.Opens)) (AddCommGrpCat.{u}))
    (hP : TopCat.Presheaf.IsSheaf P) (W : Opposite (X.Opens)) (hW : W.unop ≤ iSup U) :
    Function.Injective
      (fun x : (restrL P (iSup U)).obj W => (cechAugNat U P).app W x) := by
  intro s t hs
  have hs' : augApp U P W s = augApp U P W t := hs
  -- The component of the augmentation at the constant simplex `fun _ => i` is the restriction of
  -- the section to `(cechN U 0).obj (fun _ => i) ⊓ W = U i ⊓ W`.
  have hcomp : ∀ i : ι,
      P.map (homOfLE
          (inf_le_inf (cechN_obj_le_iSup U 0 (fun _ : Fin 1 => i)) le_rfl)).op s
        = P.map (homOfLE
          (inf_le_inf (cechN_obj_le_iSup U 0 (fun _ : Fin 1 => i)) le_rfl)).op t := by
    intro i
    have h1 := congrArg
      (Pi.π (fun y' : (cechN U 0).I => (restrP P W.unop).obj (op ((cechN U 0).obj y')))
        (fun _ : Fin 1 => i)) hs'
    simpa only [augApp_apply_π, augComp_apply] using h1
  -- The opens `(cechN U 0).obj (fun _ => i) ⊓ W` cover `(⨆ U) ⊓ W`.
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨P, hP⟩
    (fun i : ι => (cechN U 0).obj (fun _ : Fin 1 => i) ⊓ W.unop)
    (iSup U ⊓ W.unop)
    (fun i => homOfLE
      (inf_le_inf (cechN_obj_le_iSup U 0 (fun _ : Fin 1 => i)) le_rfl))
    ?_ s t hcomp
  rw [iSup_inf_eq]
  refine iSup_le (fun i => ?_)
  exact le_trans
    (le_of_eq (congrArg (fun Z : X.Opens => Z ⊓ W.unop) (cechN_obj_const U i)).symm)
    (le_iSup (fun i : ι => (cechN U 0).obj (fun _ : Fin 1 => i) ⊓ W.unop) i)

end Work.DSF1.Sheaf
