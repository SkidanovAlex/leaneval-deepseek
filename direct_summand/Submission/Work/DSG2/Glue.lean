import Mathlib
import Submission.Work.DSG2.Setup
import Submission.Work.DSG2.phiiCompJ
import Submission.Work.DSG2.piiCompF

/-!
# DSG2: the morphism `π : X' ⟶ X` of Chow's lemma

This file collects everything about the morphism `π : X' ⟶ X` of the Chow construction, packaged
as a structure `Work.DSG2.ChowSetup.GluedPi D`:

* `GluedPi.hom : X' D ⟶ X` is the glued morphism `π`,
* `GluedPi.comp : ∀ i, (cover D).f i ≫ π = pii D i`.

Everything else is stated for an arbitrary `P : GluedPi D`, so that no `Classical.choose` enters
any statement:

* `piCompF` : `π` is a morphism over `Spec A` (`π ≫ f = X'Spec`);
* the open subschemes `Xi P i = π⁻¹(U i)` of `X'`, the maps `piU P i : Xi P i ⟶ U i` and
  `ri P i : V i ⟶ Xi P i` (`ri` is the inclusion `V i ⊆ π⁻¹(U i)`, an open immersion), with
  `ri ≫ piU = phii` proper;
* `isSchemeTheoreticallyDominant_ri`: the inclusion `V i ⊆ π⁻¹(U i)` is scheme-theoretically
  dominant, since it contains `U0` and `U0 ⟶ X'` is scheme-theoretically dominant.

The existence of a `GluedPi D` (for `f` separated, which is what the gluing uses) is
`Work.DSG2.nonempty_gluedPi`, proved in `Submission/Work/DSG2/GlueExists.lean` from
`Work.DSG2.gluePiExists`.
-/

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace Work.DSG2

namespace ChowSetup

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)}

/-! ## The glued morphism `π` -/

/-- A morphism `X' ⟶ X` whose restriction to the piece `V i` is the map `pii D i`. -/
structure GluedPi (D : ChowSetup A X f) where
  /-- the glued morphism -/
  hom : X' D ⟶ X
  /-- its restrictions to the pieces -/
  comp : ∀ i : Fin D.m, (cover D).f i ≫ hom = pii D i

variable {D : ChowSetup A X f}

theorem cover_f_comp_X'Spec (D : ChowSetup A X f) (i : Fin D.m) :
    (cover D).f i ≫ X'Spec D = (Vi D i).ι ≫ Ziota D ≫ D.πP := by
  change (Z D).homOfLE (le_iSup (fun j => Vi D j) i) ≫ ((S D).ι ≫ Ziota D ≫ D.πP) =
    (Vi D i).ι ≫ Ziota D ≫ D.πP
  rw [← Category.assoc, Scheme.homOfLE_ι]

theorem piCompF (P : GluedPi D) : P.hom ≫ f = X'Spec D := by
  refine (cover D).hom_ext _ _ fun (i : Fin D.m) => ?_
  rw [← Category.assoc, P.comp i, piiCompF D i, cover_f_comp_X'Spec]
  exact Category.assoc _ _ _

/-! ## The pieces over `U i` -/

/-- The preimage `π⁻¹(U i) ⊆ X'`. -/
noncomputable abbrev Xi (P : GluedPi D) (i : Fin D.m) : (X' D).Opens :=
  P.hom ⁻¹ᵁ ((D.U i : X.Opens))

/-- The restriction of `π` over `U i`. -/
noncomputable abbrev piU (P : GluedPi D) (i : Fin D.m) :
    ((Xi P i) : Scheme.{u}) ⟶ ((D.U i : X.Opens) : Scheme.{u}) :=
  P.hom ∣_ ((D.U i : X.Opens))

theorem piU_spec (P : GluedPi D) (i : Fin D.m) :
    (Xi P i).ι ≫ P.hom = piU P i ≫ ((D.U i : X.Opens)).ι :=
  (morphismRestrict_ι (P.hom) ((D.U i : X.Opens))).symm

theorem range_cover_f (D : ChowSetup A X f) (i : Fin D.m) :
    Set.range ((cover D).f i) = (V'i D i : Set (X' D)) := by
  have h : ((cover D).f i).opensRange = V'i D i := opensRange_cover_f D i
  rw [← h]
  exact Set.ext fun y => Scheme.Hom.mem_opensRange

/-- The inclusion `V i ⊆ π⁻¹(U i)`. -/
theorem range_cover_f_le_Xi (P : GluedPi D) (i : Fin D.m) :
    Set.range ((cover D).f i) ⊆ Set.range (Xi P i).ι := by
  rintro z ⟨v, rfl⟩
  refine ⟨⟨(cover D).f i v, ?_⟩, rfl⟩
  show P.hom ((cover D).f i v) ∈ (D.U i : Set X)
  rw [← Scheme.Hom.comp_apply, P.comp i]
  exact (phii D i v).property

/-- The map `V i ⟶ π⁻¹(U i)`, an open immersion. -/
noncomputable def ri (P : GluedPi D) (i : Fin D.m) :
    ((Vi D i) : Scheme.{u}) ⟶ ((Xi P i) : Scheme.{u}) :=
  IsOpenImmersion.lift (Xi P i).ι ((cover D).f i) (range_cover_f_le_Xi P i)

theorem ri_fac (P : GluedPi D) (i : Fin D.m) : ri P i ≫ (Xi P i).ι = (cover D).f i :=
  IsOpenImmersion.lift_fac _ _ _

theorem isOpenImmersion_ri (P : GluedPi D) (i : Fin D.m) : IsOpenImmersion (ri P i) := by
  haveI : IsOpenImmersion (ri P i ≫ (Xi P i).ι) :=
    (ri_fac P i) ▸ (inferInstance : IsOpenImmersion ((cover D).f i))
  haveI : IsOpenImmersion ((Xi P i).ι) := inferInstance
  exact IsOpenImmersion.of_comp (ri P i) ((Xi P i).ι)

/-- `ri` composed with the restriction of `π` is the map `phii`. -/
theorem ri_comp_piU (P : GluedPi D) (i : Fin D.m) : ri P i ≫ piU P i = phii D i := by
  rw [← cancel_mono ((D.U i : X.Opens)).ι, Category.assoc, ← piU_spec, ← Category.assoc,
    ri_fac, P.comp i]
  rfl

theorem isProper_ri_comp_piU (P : GluedPi D) (i : Fin D.m) :
    IsProper (ri P i ≫ piU P i) := by
  rw [ri_comp_piU]
  exact D.isProper_phii i

/-! ## Separation of the pieces -/

theorem isSeparated_terminal_from_X' (D : ChowSetup A X f) [IsSeparated f] :
    IsSeparated (terminal.from (X' D)) := by
  rw [show terminal.from (X' D) = X'Spec D ≫ terminal.from (Spec (.of A)) from
    terminal.hom_ext _ _]
  haveI : IsSeparated (X'Spec D) := by
    rw [X'Spec]
    haveI : IsProper (D.πP) := D.πP_proper
    infer_instance
  infer_instance

theorem isSeparated_terminal_from_Xi (P : GluedPi D) [IsSeparated f] (i : Fin D.m) :
    IsSeparated (terminal.from ((Xi P i) : Scheme.{u})) := by
  rw [show terminal.from ((Xi P i) : Scheme.{u}) =
    (Xi P i).ι ≫ terminal.from (X' D) from terminal.hom_ext _ _]
  haveI : IsSeparated (terminal.from (X' D)) :=
    isSeparated_terminal_from_X' (A := A) (X := X) (f := f) D
  infer_instance

theorem isSeparated_piU (P : GluedPi D) [IsSeparated f] (i : Fin D.m) :
    IsSeparated (piU P i) := by
  haveI : (↑(Xi P i) : Scheme.{u}).IsSeparated :=
    ⟨isSeparated_terminal_from_Xi P i⟩
  infer_instance

/-! ## The inclusion of `U0` into the pieces -/

theorem range_u0ToX'_le_cover (D : ChowSetup A X f) (i : Fin D.m) :
    Set.range (u0ToX' D) ⊆ Set.range ((cover D).f i) := by
  intro z hz
  rw [range_cover_f D i]
  obtain ⟨y, rfl⟩ := hz
  change (S D).ι (u0ToX' D y) ∈ (Vi D i : Set (Z D))
  rw [← Scheme.Hom.comp_apply, u0ToX'_fac D]
  exact jU_toImage_mem_Vi D i y

/-- The map `U0 ⟶ V i`. -/
noncomputable def u0ToVi (D : ChowSetup A X f) (i : Fin D.m) :
    (D.U0 : Scheme.{u}) ⟶ ((Vi D i) : Scheme.{u}) :=
  IsOpenImmersion.lift ((cover D).f i) (u0ToX' D) (range_u0ToX'_le_cover D i)

theorem u0ToVi_fac (D : ChowSetup A X f) (i : Fin D.m) :
    u0ToVi D i ≫ (cover D).f i = u0ToX' D :=
  IsOpenImmersion.lift_fac _ _ _

theorem range_u0ToX'_le_Xi (P : GluedPi D) (i : Fin D.m) :
    Set.range (u0ToX' D) ⊆ Set.range (Xi P i).ι :=
  (range_u0ToX'_le_cover D i).trans (range_cover_f_le_Xi P i)

theorem quasiCompact_u0ToX' (D : ChowSetup A X f) : QuasiCompact (u0ToX' D) := by
  haveI : IsNoetherian X := D.hNoeth
  haveI : TopologicalSpace.NoetherianSpace (↑(D.U0) : Scheme.{u}) :=
    noetherianSpace_opensScheme D.U0
  infer_instance

theorem isSchemeTheoreticallyDominant_u0ToVi_comp_ri (P : GluedPi D) (i : Fin D.m) :
    IsSchemeTheoreticallyDominant (u0ToVi D i ≫ ri P i) := by
  haveI : QuasiCompact (u0ToX' D) := quasiCompact_u0ToX' D
  haveI : IsSchemeTheoreticallyDominant (u0ToX' D) := D.isSchemeTheoreticallyDominant_u0ToX'
  have h := isSchemeTheoreticallyDominant_lift_qc (u0ToX' D) (Xi P i) (range_u0ToX'_le_Xi P i)
  have hfac : u0ToVi D i ≫ ri P i =
      IsOpenImmersion.lift (Xi P i).ι (u0ToX' D) (range_u0ToX'_le_Xi P i) :=
    IsOpenImmersion.lift_uniq (f := (Xi P i).ι) (g := u0ToX' D) (range_u0ToX'_le_Xi P i)
      (u0ToVi D i ≫ ri P i) (by rw [Category.assoc, ri_fac, u0ToVi_fac])
  rw [hfac]
  exact h

theorem isSchemeTheoreticallyDominant_ri (P : GluedPi D) (i : Fin D.m) :
    IsSchemeTheoreticallyDominant (ri P i) := by
  have h := isSchemeTheoreticallyDominant_u0ToVi_comp_ri P i
  refine ⟨le_bot_iff.mp ?_⟩
  exact (Scheme.Hom.le_ker_comp (u0ToVi D i) (ri P i)).trans_eq h.ker_eq_bot

end ChowSetup

end Work.DSG2
