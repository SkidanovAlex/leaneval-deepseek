import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSG2.Defs
import Submission.Work.DSG2.Basic
import Submission.Work.DSG2.isSchemeTheoreticallyDominant_lift_qc
import Submission.Work.DSG2.isSchemeTheoreticallyDominant_toImage

/-!
# DSG2: the Chow construction — data and its basic API

This file packages the "Chow data" used by the proof of Chow's lemma over a Noetherian base
(`Work.DSG2.area_G2_chow_proved`, see `Submission/Work/DSG2/Main.lean`), together with the
schemes and morphisms derived from it.

Given `A` Noetherian, `X : Scheme.{u}` proper over `Spec A` and `X` nonempty, the data consists of

* `m ≥ 1` and a finite affine open cover `U : Fin m → X.affineOpens` whose intersection `U0` is
  dense in `X` (`Work.DSG2.denseAffineCover`);
* immersions `j i : U i ⟶ ℙ^N_A` over `Spec A` (`Work.DSG2.exists_immersion_pspace_u`, with a
  common `N`; see `Work.DSG2.nonempty_chowSetup`);
* the `m`-fold product `P ⟶ Spec A` of `ℙ^N_A` with projections `p i` and a closed immersion
  `iP` into a projective space (`Work.DSG2.nonempty_segreProductData`);
* the product map `jU : U0 ⟶ P` of the restrictions of the `j i`.

Everything downstream — the scheme-theoretic image `Z` of `jU`, the projections `qi`, the
closed subschemes `Zi`, the open pieces `Vi ⊆ Z`, the maps `phii : Vi ⟶ U i`, the `pii`, the open
`S = ⋃ Vi` and `X' = S`, the structure maps `X'Spec`, `X'Proj` — is a *definition* on `ChowSetup`,
so that lemmas about them can be stated and proved independently of the construction.

## Conventions

* `Vi D i` is an open of `Z D`; `↑(Vi D i)` denotes the corresponding open subscheme.
* `pi D i : Z D ⟶ Zi D i` is the projection, proper, with `pi ≫ ZiIota = qi`.
* `Wi D i ⊆ Zi D i` is the open image of the immersion `j i`, and `eUi D i : U i ≅ Wi D i`.
* `phii D i : ↑(Vi D i) ⟶ ↑(U i)` is proper and surjective.
* `pii D i = phii D i ≫ (U i).ι : ↑(Vi D i) ⟶ X`, and `π` is their gluing along the open cover
  `{Vi}` of `X'` (see `Submission/Work/DSG2/Glue.lean`).
-/

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace Work.DSG2

/-- The data produced by the classical construction of Chow's lemma (EGA II 5.6.1, Stacks 0200)
over a nonempty proper `X` over a Noetherian affine base. -/
structure ChowSetup (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) where
  /-- `X` is Noetherian -/
  hNoeth : IsNoetherian X
  /-- the number of members of the affine cover -/
  m : ℕ
  /-- the cover is nonempty -/
  hm : 0 < m
  /-- a finite affine open cover of `X` -/
  U : Fin m → X.affineOpens
  /-- the cover covers `X` -/
  hUcover : ⨆ i, ((U i : X.Opens)) = ⊤
  /-- the common refinement of the cover -/
  U0 : X.Opens
  /-- `U0` is contained in every `U i` -/
  hU0le : ∀ i, U0 ≤ ((U i : X.Opens))
  /-- `U0` is dense in `X` -/
  hU0dense : Dense (U0 : Set X)
  /-- the dimension of the common projective space -/
  N : ℕ
  /-- the local immersions `U i ⟶ ℙ^N_A` -/
  j : (i : Fin m) → (((U i : X.Opens)) : Scheme.{u}) ⟶ DSMap.PSpace A N
  /-- the local immersions are immersions -/
  hjImm : ∀ i, IsImmersion (j i)
  /-- the local immersions are morphisms over `Spec A` -/
  hjComp : ∀ i, (j i) ≫ DSMap.PSpace.toSpec A N = ((U i : X.Opens)).ι ≫ f
  /-- the ambient product `∏ᵢ ℙ^N_A` -/
  P : Scheme.{u}
  /-- its structure morphism -/
  πP : P ⟶ Spec (.of A)
  /-- the projections -/
  p : Fin m → (P ⟶ DSMap.PSpace A N)
  /-- the projections are morphisms over `Spec A` -/
  pComp : ∀ i, (p i) ≫ DSMap.PSpace.toSpec A N = πP
  /-- the projections are proper -/
  pProper : ∀ i, IsProper (p i)
  /-- the structure morphism of the product is proper -/
  πP_proper : IsProper πP
  /-- the universal property of the product -/
  lift : ∀ (Q : Scheme.{u}) (q : Fin m → (Q ⟶ DSMap.PSpace A N))
      (πQ : Q ⟶ Spec (.of A)),
      (∀ i, (q i) ≫ DSMap.PSpace.toSpec A N = πQ) →
      ∃ u : Q ⟶ P, u ≫ πP = πQ ∧ ∀ i, u ≫ p i = q i
  /-- the product embeds into a projective space -/
  M : ℕ
  /-- the closed immersion of the product into `ℙ^M_A` -/
  iP : P ⟶ DSMap.PSpace A M
  /-- it is a closed immersion -/
  iP_closed : IsClosedImmersion iP
  /-- it is a morphism over `Spec A` -/
  iP_comp : iP ≫ DSMap.PSpace.toSpec A M = πP
  /-- the product map `U0 ⟶ P` -/
  jU : (U0 : Scheme.{u}) ⟶ P
  /-- its components are the restrictions of the `j i` -/
  jU_proj : ∀ i, jU ≫ p i = X.homOfLE (hU0le i) ≫ j i
  /-- `jU` is a morphism over `Spec A` -/
  jU_π : jU ≫ πP = U0.ι ≫ f

namespace ChowSetup

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)}

/-- The scheme-theoretic image of `jU : U0 ⟶ P` in the product. -/
noncomputable abbrev Z (D : ChowSetup A X f) : Scheme.{u} := D.jU.image

/-- The closed immersion `Z ⟶ P`. -/
noncomputable abbrev Ziota (D : ChowSetup A X f) : Z D ⟶ D.P := D.jU.imageι

theorem isClosedImmersion_Ziota (D : ChowSetup A X f) : IsClosedImmersion (Ziota D) :=
  inferInstanceAs (IsClosedImmersion D.jU.imageι)

theorem isProper_Ziota (D : ChowSetup A X f) : IsProper (Ziota D) :=
  inferInstanceAs (IsProper D.jU.imageι)

/-- The `i`-th projection restricted to `Z`. -/
noncomputable abbrev qi (D : ChowSetup A X f) (i : Fin D.m) : Z D ⟶ DSMap.PSpace A D.N :=
  D.jU.imageι ≫ D.p i

/-- The scheme-theoretic image of `j i : U i ⟶ ℙ^N_A`. -/
noncomputable abbrev Zi (D : ChowSetup A X f) (i : Fin D.m) : Scheme.{u} := (D.j i).image

/-- The closed immersion `Zi ⟶ ℙ^N_A`. -/
noncomputable abbrev ZiIota (D : ChowSetup A X f) (i : Fin D.m) : Zi D i ⟶ DSMap.PSpace A D.N :=
  (D.j i).imageι

theorem isClosedImmersion_ZiIota (D : ChowSetup A X f) (i : Fin D.m) :
    IsClosedImmersion (ZiIota D i) :=
  inferInstanceAs (IsClosedImmersion (D.j i).imageι)

theorem isProper_ZiIota (D : ChowSetup A X f) (i : Fin D.m) : IsProper (ZiIota D i) :=
  inferInstanceAs (IsProper (D.j i).imageι)

/-- `j i` is quasi-compact: its source is affine. -/
theorem quasiCompact_j (D : ChowSetup A X f) (i : Fin D.m) : QuasiCompact (D.j i) := by
  haveI : IsNoetherian X := D.hNoeth
  infer_instance

/-- The open subscheme `↥U` of a Noetherian scheme is Noetherian. -/
theorem noetherianSpace_opensScheme {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace X]
    (U : X.Opens) : TopologicalSpace.NoetherianSpace (↑U : Scheme.{u}) := by
  change TopologicalSpace.NoetherianSpace ((U : Set X))
  infer_instance

theorem quasiCompact_jU (D : ChowSetup A X f) : QuasiCompact D.jU := by
  haveI : IsNoetherian X := D.hNoeth
  haveI : TopologicalSpace.NoetherianSpace (↑(D.U0) : Scheme.{u}) :=
    noetherianSpace_opensScheme D.U0
  infer_instance

theorem isSchemeTheoreticallyDominant_jU_toImage (D : ChowSetup A X f) :
    IsSchemeTheoreticallyDominant D.jU.toImage := by
  haveI : QuasiCompact D.jU := D.quasiCompact_jU
  exact isSchemeTheoreticallyDominant_toImage D.jU

theorem quasiCompact_jU_toImage (D : ChowSetup A X f) : QuasiCompact D.jU.toImage := by
  haveI : QuasiCompact D.jU := D.quasiCompact_jU
  exact .of_comp _ D.jU.imageι

theorem isImmersion_toImage_j (D : ChowSetup A X f) (i : Fin D.m) :
    IsImmersion ((D.j i).toImage) := by
  haveI : IsImmersion (D.j i) := D.hjImm i
  infer_instance

/-- The canonical map `U i ⟶ Zi` is an open immersion onto its image: it is an immersion whose
range is open in the closure `Zi`. -/
theorem isOpenImmersion_toImage_j (D : ChowSetup A X f) (i : Fin D.m) :
    IsOpenImmersion ((D.j i).toImage) := by
  haveI : IsImmersion (D.j i) := D.hjImm i
  haveI : QuasiCompact (D.j i) := D.quasiCompact_j i
  infer_instance

instance instIsOpenImmersion_toImage_j (D : ChowSetup A X f) (i : Fin D.m) :
    IsOpenImmersion ((D.j i).toImage) := D.isOpenImmersion_toImage_j i

/-- The open piece `W i ⊆ Zi` which is the image of the immersion `j i`. -/
noncomputable abbrev Wi (D : ChowSetup A X f) (i : Fin D.m) : (Zi D i).Opens :=
  @Scheme.Hom.opensRange _ _ ((D.j i).toImage) (D.isOpenImmersion_toImage_j i)

/-- `U i ≅ W i`. -/
noncomputable abbrev eUi (D : ChowSetup A X f) (i : Fin D.m) :
    ((D.U i : X.Opens) : Scheme.{u}) ≅ ((Wi D i) : Scheme.{u}) :=
  @Scheme.Hom.isoOpensRange _ _ ((D.j i).toImage) (D.isOpenImmersion_toImage_j i)

theorem eUi_hom_ι (D : ChowSetup A X f) (i : Fin D.m) :
    (eUi D i).hom ≫ (Wi D i).ι = (D.j i).toImage :=
  @Scheme.Hom.isoOpensRange_hom_ι _ _ ((D.j i).toImage) (D.isOpenImmersion_toImage_j i)

theorem eUi_inv_comp (D : ChowSetup A X f) (i : Fin D.m) :
    (eUi D i).inv ≫ (D.j i).toImage = (Wi D i).ι :=
  @Scheme.Hom.isoOpensRange_inv_comp _ _ ((D.j i).toImage) (D.isOpenImmersion_toImage_j i)

/-- The kernel inclusion which makes `qi` factor through the closed subscheme `Zi`. -/
theorem ker_ZiIota_le_ker_qi (D : ChowSetup A X f) (i : Fin D.m) :
    (ZiIota D i).ker ≤ (qi D i).ker := by
  have h1 : (ZiIota D i).ker = (D.j i).ker :=
    Scheme.IdealSheafData.ker_subschemeι (D.j i).ker
  have h2 : (qi D i).ker = (D.jU.ker).map (D.p i) := by
    rw [Scheme.Hom.ker_comp]
    exact congrArg (fun I => I.map (D.p i))
      (Scheme.IdealSheafData.ker_subschemeι D.jU.ker)
  have h3 : (D.jU.ker).map (D.p i) = (D.jU ≫ D.p i).ker :=
    (Scheme.Hom.ker_comp D.jU (D.p i)).symm
  rw [h1, h2, h3, D.jU_proj i]
  exact Scheme.Hom.le_ker_comp (X.homOfLE (D.hU0le i)) (D.j i)

/-- The projection `Z ⟶ Zi`. -/
noncomputable def pi (D : ChowSetup A X f) (i : Fin D.m) : Z D ⟶ Zi D i :=
  IsClosedImmersion.lift (ZiIota D i) (qi D i) (D.ker_ZiIota_le_ker_qi i)

theorem pi_spec (D : ChowSetup A X f) (i : Fin D.m) : pi D i ≫ ZiIota D i = qi D i :=
  IsClosedImmersion.lift_fac _ _ _

theorem isProper_qi (D : ChowSetup A X f) (i : Fin D.m) : IsProper (qi D i) := by
  haveI : IsProper (Ziota D) := D.isProper_Ziota
  haveI : IsProper (D.p i) := D.pProper i
  exact inferInstance

theorem isProper_pi (D : ChowSetup A X f) (i : Fin D.m) : IsProper (pi D i) := by
  haveI : IsProper (pi D i ≫ ZiIota D i) := by
    rw [pi_spec D i]
    exact D.isProper_qi i
  haveI : IsSeparated (ZiIota D i) := inferInstance
  exact IsProper.of_comp (pi D i) (ZiIota D i)

/-- The open piece `V i = πᵢ⁻¹(U i) ⊆ Z`. -/
noncomputable abbrev Vi (D : ChowSetup A X f) (i : Fin D.m) : (Z D).Opens :=
  (pi D i) ⁻¹ᵁ (Wi D i)

theorem isProper_pi_restrict (D : ChowSetup A X f) (i : Fin D.m) :
    IsProper (pi D i ∣_ Wi D i) := by
  haveI : IsProper (pi D i) := D.isProper_pi i
  infer_instance

/-- The map `V i ⟶ U i`. -/
noncomputable def phii (D : ChowSetup A X f) (i : Fin D.m) :
    ((Vi D i) : Scheme.{u}) ⟶ ((D.U i : X.Opens) : Scheme.{u}) :=
  (pi D i ∣_ Wi D i) ≫ (eUi D i).inv

theorem isProper_phii (D : ChowSetup A X f) (i : Fin D.m) : IsProper (phii D i) := by
  haveI : IsProper (phii D i ≫ (eUi D i).hom) := by
    rw [phii, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact D.isProper_pi_restrict i
  haveI : IsSeparated (eUi D i).hom := inferInstance
  exact IsProper.of_comp (phii D i) (eUi D i).hom

/-- The composite `V i ⟶ X`. -/
noncomputable def pii (D : ChowSetup A X f) (i : Fin D.m) : ((Vi D i) : Scheme.{u}) ⟶ X :=
  phii D i ≫ ((D.U i : X.Opens)).ι

/-- The union of the pieces `V i` inside `Z`. -/
noncomputable abbrev S (D : ChowSetup A X f) : (Z D).Opens := ⨆ i, Vi D i

/-- The scheme `X'` of Chow's lemma: the union of the pieces `V i` inside `Z`. -/
noncomputable abbrev X' (D : ChowSetup A X f) : Scheme.{u} := (S D : Scheme.{u})

/-- The open cover of `X'` by the pieces `V i`.  It is given explicitly (rather than as
`Scheme.Opens.iSupOpenCover (Vi D)`) so that the index type of the cover reduces to `Fin D.m`
already at `implicit` transparency, which the tactics below rely on. -/
noncomputable abbrev cover (D : ChowSetup A X f) : (X' D).OpenCover where
  I₀ := Fin D.m
  X := fun i => ((Vi D i) : Scheme.{u})
  f := fun i => (Z D).homOfLE (le_iSup (fun j => Vi D j) i)
  mem₀ := (Scheme.Opens.iSupOpenCover (Vi D)).mem₀

/-- The structure morphism `X' ⟶ Spec A`. -/
noncomputable def X'Spec (D : ChowSetup A X f) : X' D ⟶ Spec (.of A) := (S D).ι ≫ Ziota D ≫ D.πP

/-- The immersion `X' ⟶ ℙ^M_A`. -/
noncomputable def X'Proj (D : ChowSetup A X f) : X' D ⟶ DSMap.PSpace A D.M :=
  (S D).ι ≫ Ziota D ≫ D.iP

theorem isImmersion_X'Proj (D : ChowSetup A X f) : IsImmersion (X'Proj D) := by
  haveI : IsOpenImmersion (S D).ι := inferInstance
  haveI : IsClosedImmersion (Ziota D) := D.isClosedImmersion_Ziota
  haveI : IsClosedImmersion (D.iP) := D.iP_closed
  exact IsImmersion.comp _ _

theorem X'Proj_comp (D : ChowSetup A X f) :
    X'Proj D ≫ DSMap.PSpace.toSpec A D.M = X'Spec D := by
  rw [X'Proj, X'Spec, Category.assoc, Category.assoc, D.iP_comp]

/-! ## The inclusion of `U0` into `X'`, and the identification of the pieces

`U0` maps into every `V i` (the calculation `pi_apply_jU_toImage`), hence into `X'`; the induced
map `u0ToX'` is scheme-theoretically dominant, so its range is dense in `X'`. This density is
what makes the open covering `{V i}` of `X'` "scheme-theoretically dense" in the sense needed to
identify `π⁻¹(U i)` with `V i`. -/

/-- The `i`-th piece `V i` viewed inside `X'`. -/
noncomputable abbrev V'i (D : ChowSetup A X f) (i : Fin D.m) : (X' D).Opens :=
  (S D).ι ⁻¹ᵁ (Vi D i)

instance instIsOpenImmersion_cover_f (D : ChowSetup A X f) (i : Fin D.m) :
    IsOpenImmersion ((cover D).f i) := by
  change IsOpenImmersion ((Z D).homOfLE (le_iSup (fun i => Vi D i) i))
  infer_instance

theorem opensRange_cover_f (D : ChowSetup A X f) (i : Fin D.m) :
    ((cover D).f i).opensRange = V'i D i :=
  Scheme.opensRange_homOfLE (le_iSup (fun i => Vi D i) i)

/-- The component calculation: the projection `pi i` sends the diagonal point `jU.toImage y`
to the point `(j i).toImage (homOfLE y)`. -/
theorem pi_apply_jU_toImage (D : ChowSetup A X f) (i : Fin D.m)
    (y : (D.U0 : Scheme.{u})) :
    (pi D i) (D.jU.toImage y) = (D.j i).toImage ((X.homOfLE (D.hU0le i)) y) := by
  apply (ZiIota D i).isEmbedding.injective
  have h1 : D.jU.toImage ≫ qi D i = X.homOfLE (D.hU0le i) ≫ D.j i := by
    rw [show qi D i = Ziota D ≫ D.p i from rfl, ← Category.assoc,
      Scheme.Hom.toImage_imageι D.jU]
    exact D.jU_proj i
  have h2 : X.homOfLE (D.hU0le i) ≫ D.j i =
      X.homOfLE (D.hU0le i) ≫ (D.j i).toImage ≫ ZiIota D i := by
    rw [Scheme.Hom.toImage_imageι]
  calc ZiIota D i (pi D i (D.jU.toImage y))
      = (qi D i) (D.jU.toImage y) := by rw [← Scheme.Hom.comp_apply, pi_spec D i]
    _ = (D.jU.toImage ≫ qi D i) y := rfl
    _ = (X.homOfLE (D.hU0le i) ≫ (D.j i).toImage ≫ ZiIota D i) y := by rw [h1, h2]
    _ = ZiIota D i ((D.j i).toImage ((X.homOfLE (D.hU0le i)) y)) := rfl

theorem jU_toImage_mem_Vi (D : ChowSetup A X f) (i : Fin D.m)
    (y : (D.U0 : Scheme.{u})) : D.jU.toImage y ∈ Vi D i := by
  rw [show Vi D i = (pi D i) ⁻¹ᵁ (Wi D i) from rfl, Scheme.Hom.mem_preimage,
    pi_apply_jU_toImage D i y]
  exact Scheme.Hom.mem_opensRange.mpr ⟨X.homOfLE (D.hU0le i) y, rfl⟩

theorem jU_toImage_range_le_S (D : ChowSetup A X f) :
    Set.range D.jU.toImage ⊆ Set.range (S D).ι := by
  rintro z ⟨y, rfl⟩
  have hmem : D.jU.toImage y ∈ (S D : Set (Z D)) := by
    rw [S, TopologicalSpace.Opens.coe_iSup]
    exact Set.mem_iUnion.mpr
      ⟨(⟨0, D.hm⟩ : Fin D.m), jU_toImage_mem_Vi D ⟨0, D.hm⟩ y⟩
  exact ⟨⟨D.jU.toImage y, hmem⟩, rfl⟩

/-- The canonical map `U0 ⟶ X'`. -/
noncomputable def u0ToX' (D : ChowSetup A X f) : (D.U0 : Scheme.{u}) ⟶ X' D :=
  IsOpenImmersion.lift (S D).ι D.jU.toImage D.jU_toImage_range_le_S

theorem u0ToX'_fac (D : ChowSetup A X f) :
    u0ToX' D ≫ (S D).ι = D.jU.toImage :=
  IsOpenImmersion.lift_fac _ _ _

theorem isSchemeTheoreticallyDominant_u0ToX' (D : ChowSetup A X f) :
    IsSchemeTheoreticallyDominant (u0ToX' D) := by
  haveI : IsSchemeTheoreticallyDominant D.jU.toImage := D.isSchemeTheoreticallyDominant_jU_toImage
  haveI : QuasiCompact D.jU.toImage := D.quasiCompact_jU_toImage
  exact isSchemeTheoreticallyDominant_lift_qc D.jU.toImage (S D) D.jU_toImage_range_le_S

/-- `U0` is dense in `X'`. -/
theorem denseRange_u0ToX' (D : ChowSetup A X f) : DenseRange (u0ToX' D) := by
  haveI : IsNoetherian X := D.hNoeth
  haveI : IsSchemeTheoreticallyDominant (u0ToX' D) := D.isSchemeTheoreticallyDominant_u0ToX'
  haveI : TopologicalSpace.NoetherianSpace (↑(D.U0) : Scheme.{u}) :=
    noetherianSpace_opensScheme D.U0
  haveI : QuasiCompact (u0ToX' D) := inferInstance
  exact (inferInstance : IsDominant (u0ToX' D)).denseRange

end ChowSetup

end Work.DSG2
