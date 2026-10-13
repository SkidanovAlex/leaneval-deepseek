import Mathlib
import Submission.Work.DSG2.Setup
import Submission.Work.DSG2.Glue
import Submission.Work.DSG2.surjective_pi

/-!
# DSG2: surjectivity of the pieces and of the glued morphism `π`

`Work.DSG2.surjective_pi` (proved in `Submission/Work/DSG2/surjective_pi.lean`) says that the
projection `pi D i : Z ⟶ Zi` is surjective.  Since `Vi D i = pi ⁻¹ᵁ Wi D i` and
`phii D i : Vi D i ⟶ U i` is the restriction of `pi D i` to the preimage of `Wi D i`, it follows
that `phii D i`, and hence `pii D i`, maps onto `U i`; consequently the glued morphism
`P.hom : X' ⟶ X` is surjective.
-/

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace Work.DSG2

namespace ChowSetup

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)}

theorem surjective_pi_restrict (D : ChowSetup A X f) (i : Fin D.m) :
    Function.Surjective (pi D i ∣_ Wi D i) := by
  intro w
  obtain ⟨z, hz⟩ := surjective_pi D i ((Wi D i).ι.base w)
  obtain ⟨p, -, hp2⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pi D i) (g := (Wi D i).ι) z w hz
  refine ⟨(pullbackRestrictIsoRestrict (pi D i) (Wi D i)).hom.base p, ?_⟩
  have hcomp : (pi D i ∣_ Wi D i).base =
      (pullback.snd (pi D i) (Wi D i).ι).base ∘
        (pullbackRestrictIsoRestrict (pi D i) (Wi D i)).inv.base := rfl
  have hcan : (pullbackRestrictIsoRestrict (pi D i) (Wi D i)).inv.base
      ((pullbackRestrictIsoRestrict (pi D i) (Wi D i)).hom.base p) = p := by
    have h := congrFun (congrArg (fun g => g.base)
      (Iso.hom_inv_id (pullbackRestrictIsoRestrict (pi D i) (Wi D i)))) p
    simpa using h
  rw [hcomp, Function.comp_apply, hcan]
  exact hp2

theorem surjective_phii (D : ChowSetup A X f) (i : Fin D.m) :
    Function.Surjective (phii D i) := by
  have h2 : ∀ u : ((D.U i : X.Opens) : Scheme.{u}),
      (eUi D i).inv ((eUi D i).hom u) = u := by
    intro u
    have h := congrFun (congrArg (fun g => g.base) (Iso.hom_inv_id (eUi D i))) u
    simpa using h
  intro u
  obtain ⟨y, hy⟩ := surjective_pi_restrict D i ((eUi D i).hom u)
  refine ⟨y, ?_⟩
  rw [show phii D i = (pi D i ∣_ Wi D i) ≫ (eUi D i).inv from rfl, Scheme.Hom.comp_apply, hy,
    h2 u]

theorem range_pii (D : ChowSetup A X f) (i : Fin D.m) :
    Set.range (pii D i) = ((D.U i : X.Opens) : Set X) := by
  have h1 : (pii D i).base = ((D.U i : X.Opens)).ι.base ∘ (phii D i).base := rfl
  rw [show Set.range (pii D i) = Set.range (pii D i).base from rfl, h1, Set.range_comp,
    Set.range_eq_univ.mpr (surjective_phii D i), Set.image_univ]
  exact Scheme.Opens.range_ι _

theorem exists_pii_eq (D : ChowSetup A X f) (i : Fin D.m) (x : X)
    (hx : x ∈ (D.U i : Set X)) : ∃ v : ↑(Vi D i), pii D i v = x := by
  have hx' : x ∈ Set.range (pii D i) := by
    rw [range_pii]
    exact hx
  exact hx'

theorem surjective_hom (D : ChowSetup A X f) (P : GluedPi D) :
    Function.Surjective P.hom := by
  intro x
  have hx : x ∈ (⨆ i, ((D.U i : X.Opens))) := D.hUcover ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨v, hv⟩ := exists_pii_eq D i x hi
  refine ⟨(cover D).f i v, ?_⟩
  have h1 : P.hom ((cover D).f i v) = pii D i v := by
    rw [← Scheme.Hom.comp_apply, P.comp i]
  rw [h1, hv]

end ChowSetup

end Work.DSG2
