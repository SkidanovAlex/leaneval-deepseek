import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs
import Submission.Work.DSF1.Sheaf.sections_surjective_of_cechTriv_at
import Submission.Work.DSF1.Sheaf.SSECore
import Submission.Work.DSF1.Sheaf.exists_lift_of_sectionsMap_eq_zero
import Submission.Work.DSF1.Sheaf.exists_glue_compatible_at
import Submission.Work.DSF1.Sheaf.eq_of_resAt_eq_at

/-!
# Lifting one section over `U` from local lifts and Čech-triviality of `X₁`

If `0 → X₁ →f X₂ →g X₃ → 0` is a short exact sequence of sheaves of `𝒪_X`-modules,
`V : ι → X.Opens` is a finite family of opens with `iSup V = U`, a fixed section `y` of `X₃`
over `U` admits lifts over every `V i`, and every `1`-cocycle of the Čech complex of `X₁` with
respect to `V` is a coboundary, then `y` lifts to a section of `X₂` over `U`.

This is the "one section at a time" form of `sections_surjective_of_cechTriv_at`: there the
hypothesis is the surjectivity of `g` on sections over each `V i`, here only the (weaker)
existence of lifts of the restrictions of the single section `y`.  The descent argument is
literally the same; only the construction of the local lifts `ξ i` differs.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Sheaf

theorem sections_lift_of_cechTriv {X : AlgebraicGeometry.Scheme.{u}}
    (S : CategoryTheory.ShortComplex (SheafOfModules X.ringCatSheaf)) (hS : S.ShortExact)
    (U : X.Opens) {ι : Type u} [Finite ι] (V : ι → X.Opens) (hVU : ∀ i, V i ≤ U)
    (hcov : iSup V = U)
    (htriv : Work.DSF1.Sheaf.CechTrivAt (Work.DSF1.Sheaf.cechComplex V S.X₁) 0)
    (y : Work.DSF1.Sheaf.sectionsAt S.X₃ U)
    (hlift : ∀ i, ∃ x : Work.DSF1.Sheaf.sectionsAt S.X₂ (V i),
      Work.DSF1.Sheaf.sectionsMap S.g (V i) x =
        (((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₃).obj.map
          (CategoryTheory.homOfLE (hVU i)).op) y) :
    ∃ x : Work.DSF1.Sheaf.sectionsAt S.X₂ U, Work.DSF1.Sheaf.sectionsMap S.g U x = y := by
  classical
  -- the underlying presheaf morphism of `f`
  let fP := ((SheafOfModules.toSheaf X.ringCatSheaf).map S.f).hom
  -- the nerves of the family `V` cover `U`
  have hW0 : iSup (fun a : (cechN V 0).I => (cechN V 0).obj a) = U :=
    (iSup_cechN V 0).trans hcov
  have hW1 : iSup (fun a : (cechN V 1).I => (cechN V 1).obj a) = U :=
    (iSup_cechN V 1).trans hcov
  -- local lifts of the restrictions of `y`; the restriction of `y` to `V i` is the same
  -- whatever proof of `V i ≤ U` is used
  have hξ : ∀ i : ι, ∃ ξ : sectionsAt S.X₂ (V i),
      sectionsMap S.g (V i) ξ = resAt S.X₃ ((le_iSup V i).trans (le_of_eq hcov)) y := by
    intro i
    obtain ⟨ξ, hξi⟩ := hlift i
    refine ⟨ξ, ?_⟩
    rw [hξi]
    -- the two restriction maps differ only in the proof of `V i ≤ U`
    dsimp only [resAt]
  choose ξ hξ using hξ
  -- the identification of the opens of the nerve with the cover
  have hIdx : ∀ i : (cechN V 0).I, (cechN V 0).obj i = V (i 0) := by
    intro i
    rw [cechN_obj, piFin1']
    rfl
  -- the `0`-cochain of `S.X₂` whose components are the lifts
  let xt : ↥((cechComplex V S.X₂).X 0) :=
    (piLiftHom (fun i : (cechN V 0).I => sectionsAt S.X₂ ((cechN V 0).obj i)))
      (fun i => (trIso S.X₂ (hIdx i).symm).hom (ξ (i 0)))
  have hxt : ∀ i : (cechN V 0).I,
      (Pi.π (fun a : (cechN V 0).I => sectionsAt S.X₂ ((cechN V 0).obj a)) i) xt =
        (trIso S.X₂ (hIdx i).symm).hom (ξ (i 0)) :=
    fun i => piElems_π _ _ i
  -- `g` of the components of `xt`
  have hgxt : ∀ i : (cechN V 0).I,
      sectionsMap S.g ((cechN V 0).obj i)
        ((Pi.π (fun a : (cechN V 0).I => sectionsAt S.X₂ ((cechN V 0).obj a)) i) xt) =
        resAt S.X₃ ((le_iSup (fun a : (cechN V 0).I => (cechN V 0).obj a) i).trans
          (le_of_eq hW0)) y := by
    intro i
    rw [hxt i, sectionsMap_trIso_hom (S.g) (hIdx i).symm, hξ (i 0), trIso_hom_eq_resAt]
    exact resAt_trans' S.X₃ (le_of_eq (hIdx i))
      ((le_iSup V (i 0)).trans (le_of_eq hcov))
      ((le_iSup (fun a : (cechN V 0).I => (cechN V 0).obj a) i).trans (le_of_eq hW0)) y
  -- Stage 2: `d 0 1 xt` is componentwise killed by `g`
  have hker : ∀ x : (cechN V 1).I,
      (sectionsMap S.g ((cechN V 1).obj x))
        ((Pi.π (fun a : (cechN V 1).I => sectionsAt S.X₂ ((cechN V 1).obj a)) x)
          (((cechComplex V S.X₂).d 0 1) xt)) = 0 := by
    intro x
    have hA : (sectionsMap S.g ((cechN V 1).obj x))
        ((((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₂).obj.map
          (((FormalCoproduct.mk ι V).mapPower (Fin.succAbove 0)).φ x).op)
          ((Pi.π (fun a : (cechN V 0).I => sectionsAt S.X₂ ((cechN V 0).obj a))
            (x ∘ Fin.succAbove 0)) xt))
        = resAt S.X₃ ((le_iSup (fun a : (cechN V 1).I => (cechN V 1).obj a) x).trans
            (le_of_eq hW1)) y := by
      rw [show (sectionsMap S.g ((cechN V 1).obj x))
          ((((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₂).obj.map
            (((FormalCoproduct.mk ι V).mapPower (Fin.succAbove 0)).φ x).op)
            ((Pi.π (fun a : (cechN V 0).I => sectionsAt S.X₂ ((cechN V 0).obj a))
              (x ∘ Fin.succAbove 0)) xt))
          = (((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₃).obj.map
              (((FormalCoproduct.mk ι V).mapPower (Fin.succAbove 0)).φ x).op)
            ((sectionsMap S.g ((cechN V 0).obj (x ∘ Fin.succAbove 0)))
              ((Pi.π (fun a : (cechN V 0).I => sectionsAt S.X₂ ((cechN V 0).obj a))
                (x ∘ Fin.succAbove 0)) xt)) from
          sectionsMap_map S.g (((FormalCoproduct.mk ι V).mapPower (Fin.succAbove 0)).φ x) _]
      rw [hgxt (x ∘ Fin.succAbove 0), map_op_eq_resAt]
      exact resAt_trans' S.X₃ (leOfHom (((FormalCoproduct.mk ι V).mapPower (Fin.succAbove 0)).φ x))
        ((le_iSup (fun a : (cechN V 0).I => (cechN V 0).obj a) (x ∘ Fin.succAbove 0)).trans
          (le_of_eq hW0))
        ((le_iSup (fun a : (cechN V 1).I => (cechN V 1).obj a) x).trans
          (le_of_eq hW1)) y
    have hB : (sectionsMap S.g ((cechN V 1).obj x))
        ((((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₂).obj.map
          (((FormalCoproduct.mk ι V).mapPower (Fin.succAbove 1)).φ x).op)
          ((Pi.π (fun a : (cechN V 0).I => sectionsAt S.X₂ ((cechN V 0).obj a))
            (x ∘ Fin.succAbove 1)) xt))
        = resAt S.X₃ ((le_iSup (fun a : (cechN V 1).I => (cechN V 1).obj a) x).trans
            (le_of_eq hW1)) y := by
      rw [show (sectionsMap S.g ((cechN V 1).obj x))
          ((((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₂).obj.map
            (((FormalCoproduct.mk ι V).mapPower (Fin.succAbove 1)).φ x).op)
            ((Pi.π (fun a : (cechN V 0).I => sectionsAt S.X₂ ((cechN V 0).obj a))
              (x ∘ Fin.succAbove 1)) xt))
          = (((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₃).obj.map
              (((FormalCoproduct.mk ι V).mapPower (Fin.succAbove 1)).φ x).op)
            ((sectionsMap S.g ((cechN V 0).obj (x ∘ Fin.succAbove 1)))
              ((Pi.π (fun a : (cechN V 0).I => sectionsAt S.X₂ ((cechN V 0).obj a))
                (x ∘ Fin.succAbove 1)) xt)) from
          sectionsMap_map S.g (((FormalCoproduct.mk ι V).mapPower (Fin.succAbove 1)).φ x) _]
      rw [hgxt (x ∘ Fin.succAbove 1), map_op_eq_resAt]
      exact resAt_trans' S.X₃ (leOfHom (((FormalCoproduct.mk ι V).mapPower (Fin.succAbove 1)).φ x))
        ((le_iSup (fun a : (cechN V 0).I => (cechN V 0).obj a) (x ∘ Fin.succAbove 1)).trans
          (le_of_eq hW0))
        ((le_iSup (fun a : (cechN V 1).I => (cechN V 1).obj a) x).trans
          (le_of_eq hW1)) y
    rw [d01_apply (U := V) (P := ((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₂).obj) xt x]
    rw [map_sub, hA, hB, sub_self]
  -- Stage 3: a `1`-cocycle of the Čech complex of `S.X₁` mapping to `d 0 1 xt`
  have hc : ∀ x : (cechN V 1).I, ∃ a : sectionsAt S.X₁ ((cechN V 1).obj x),
      (sectionsMap S.f ((cechN V 1).obj x)) a =
        (Pi.π (fun a : (cechN V 1).I => sectionsAt S.X₂ ((cechN V 1).obj a)) x)
          (((cechComplex V S.X₂).d 0 1) xt) :=
    fun x => exists_lift_of_sectionsMap_eq_zero S hS ((cechN V 1).obj x) _ (hker x)
  choose cs hcs using hc
  let cc : ↥((cechComplex V S.X₁).X 1) :=
    (piLiftHom (fun a : (cechN V 1).I => sectionsAt S.X₁ ((cechN V 1).obj a))) cs
  have hcc : ∀ x : (cechN V 1).I,
      (Pi.π (fun a : (cechN V 1).I => sectionsAt S.X₁ ((cechN V 1).obj a)) x) cc = cs x :=
    fun x => piElems_π _ _ x
  have hccmap : (((cechComplexFunctor V).map fP).f 1) cc =
      ((cechComplex V S.X₂).d 0 1) xt := by
    refine eq_of_π_eq _ _ _ (fun x => ?_)
    rw [map_f_apply_π, hcc x, hcs x]
  have hdcc : ((cechComplex V S.X₁).d 1 2) cc = 0 := by
    refine (map_f_injective V fP
      (fun W => injective_sectionsMap_of_shortExact S hS W.unop) 2) ?_
    rw [map_zero, ← ConcreteCategory.comp_apply, ← HomologicalComplex.Hom.comm,
      ConcreteCategory.comp_apply, hccmap, ← ConcreteCategory.comp_apply]
    rw [HomologicalComplex.d_comp_d]
    rfl
  -- Stage 4: applying the Čech triviality of `S.X₁`
  obtain ⟨b, hb⟩ := htriv cc hdcc
  let u : ↥((cechComplex V S.X₂).X 0) :=
    xt - (ConcreteCategory.hom (((cechComplexFunctor V).map fP).f 0)) b
  have hdu : ((cechComplex V S.X₂).d 0 1) u = 0 := by
    have hchain := HomologicalComplex.Hom.comm'
      (((cechComplexFunctor V).map fP)) (0 : ℕ) (1 : ℕ) (by simp [ComplexShape.up_Rel])
    have happ := congrArg (fun ψ => (ConcreteCategory.hom ψ) b) hchain
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at happ
    change ((cechComplex V S.X₂).d 0 1)
      (xt - (ConcreteCategory.hom (((cechComplexFunctor V).map fP).f 0)) b) = 0
    rw [map_sub, happ, hb, hccmap, sub_self]
  -- Stage 5: descent and comparison
  obtain ⟨x, hx⟩ := descent_at V S.X₂ U hW0 u hdu
  refine ⟨x, ?_⟩
  refine eq_of_resAt_eq_at S.X₃ (fun i : (cechN V 0).I => (cechN V 0).obj i) U hW0 _ _
    (fun i => ?_)
  rw [← sectionsMap_resAt (S.g) ((le_iSup (fun a : (cechN V 0).I => (cechN V 0).obj a) i).trans
      (le_of_eq hW0)) x, hx i]
  have hu : (Pi.π (fun a : (cechN V 0).I => sectionsAt S.X₂ ((cechN V 0).obj a)) i) u =
      (Pi.π (fun a : (cechN V 0).I => sectionsAt S.X₂ ((cechN V 0).obj a)) i) xt -
        (Pi.π (fun a : (cechN V 0).I => sectionsAt S.X₂ ((cechN V 0).obj a)) i)
          ((ConcreteCategory.hom (((cechComplexFunctor V).map fP).f 0)) b) := by
    change (Pi.π (fun a : (cechN V 0).I => sectionsAt S.X₂ ((cechN V 0).obj a)) i)
      (xt - (ConcreteCategory.hom (((cechComplexFunctor V).map fP).f 0)) b) = _
    rw [map_sub]
  rw [hu, map_sub, hgxt i]
  have hz : (sectionsMap S.g ((cechN V 0).obj i))
      ((Pi.π (fun a : (cechN V 0).I => sectionsAt S.X₂ ((cechN V 0).obj a)) i)
        ((ConcreteCategory.hom (((cechComplexFunctor V).map fP).f 0)) b)) = 0 := by
    rw [map_f_apply_π]
    exact sectionsMap_gf_zero S.f S.g S.zero ((cechN V 0).obj i)
      ((Pi.π (fun a : (cechN V 0).I => sectionsAt S.X₁ ((cechN V 0).obj a)) i) b)
  rw [hz, sub_zero]

end Work.DSF1.Sheaf
