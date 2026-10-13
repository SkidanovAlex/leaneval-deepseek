import Mathlib
import Submission.Work.DSSEC.PSChart
import Submission.Work.DSSEC.PSChartGen
import Submission.Work.DSSEC.xiSecS_pair
import Submission.Work.DSG4a.phiU_comp
import Submission.Work.DSG4a.phiU_baseChange

namespace Work.DSSEC

attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry
universe u

section Compat

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {N : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- `phiU A X f U` is `f.appLE ⊤ U le_top` composed with the inverse of `ΓSpecIso`. -/
lemma phiU_eq_appLE (f : X ⟶ Spec (.of A)) (U : X.Opens) :
    DSMap.phiU A X f U =
      (f.appLE ⊤ U le_top).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) := by
  rw [DSMap.phiU]
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_assoc]
  rw [show DSMap.phi A X f =
      (Scheme.Hom.app f ⊤).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) from
    RingHom.ext fun a => Work.DSG4a.phiU_baseChange_phi_eq X f a]

/-- `appTop` of `Spec.map`. -/
lemma appTop_SpecMap {R S : CommRingCat} (θ : R ⟶ S) :
    (Spec.map θ).appTop = (Scheme.ΓSpecIso R).hom ≫ θ ≫ (Scheme.ΓSpecIso S).inv := by
  have h := Scheme.ΓSpecIso_naturality θ
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The structure map `A →+* Γ(ℙᴺ_A, DPS S)` obtained from `ℙᴺ_A ⟶ Spec A` factors through the
chart ring `Away (PGr A N) (tPS S)` via `awayToSection`. -/
theorem phiU_pspace_chart (S : Finset (Idx N)) (hS : S.Nonempty) :
    DSMap.phiU A (DSMap.PSpace A N) (DSMap.PSpace.toSpec A N) (DPS (A := A) (N := N) S)
      = ((Proj.awayToSection (DSMap.PGr A N) (tPS (A := A) S)).hom).comp
          (AtoAwayS (A := A) (N := N) S) := by
  have haff : IsAffineOpen (DPS (A := A) (N := N) S) := DPS_affine S hS
  -- Step 1: the open immersion `↑DPS S → ℙ` composed with `toSpecZero` is `basicOpenToSpec ≫ Spec.map`.
  have hspec : (DPS (A := A) (N := N) S).ι ≫ Proj.toSpecZero (DSMap.PGr A N) =
      Proj.basicOpenToSpec (DSMap.PGr A N) (tPS (A := A) S) ≫
        Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (DSMap.PGr A N)
          (Submonoid.powers (tPS (A := A) S)))) := by
    have h := Proj.awayι_toSpecZero (DSMap.PGr A N) (tPS (A := A) S) (tPS_mem S)
      (Finset.card_pos.mpr hS)
    rw [Proj.awayι, Category.assoc, Iso.inv_comp_eq] at h
    rwa [Proj.basicOpenIsoSpec_hom] at h
  -- Step 2: replacing `toSpecZero` by `toSpec` and `fromZeroRingHom` by `AtoAwayS`.
  have h2 : (DPS (A := A) (N := N) S).ι ≫ DSMap.PSpace.toSpec A N =
      Proj.basicOpenToSpec (DSMap.PGr A N) (tPS (A := A) S) ≫
        Spec.map (CommRingCat.ofHom (AtoAwayS (A := A) (N := N) S)) := by
    rw [DSMap.PSpace.toSpec, ← Category.assoc, hspec, Category.assoc]
    congr 1
    rw [← Spec.map_comp]
    have hAA : AtoAwayS (A := A) (N := N) S =
        (HomogeneousLocalization.fromZeroRingHom (DSMap.PGr A N)
          (Submonoid.powers (tPS (A := A) S))).comp (algebraMap A ↥(DSMap.PGr A N 0)) := by
      rw [AtoAwayS, algebraMap_PGr_zero]
    rw [hAA]
    rfl
  -- Step 3: reading the identity through the affine open `DPS S`.
  have h3 : haff.fromSpec ≫ DSMap.PSpace.toSpec A N =
      Spec.map (CommRingCat.ofHom (((Proj.awayToSection (DSMap.PGr A N) (tPS (A := A) S)).hom).comp
          (AtoAwayS (A := A) (N := N) S))) := by
    rw [← IsAffineOpen.isoSpec_inv_ι haff, Category.assoc, h2, Proj.basicOpenToSpec,
      ← IsAffineOpen.isoSpec_hom haff]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_assoc, ← Spec.map_comp]
    rfl
  -- Step 4: `fromSpec ≫ toSpec` is the ring hom `phiU`.
  have h4 : haff.fromSpec ≫ DSMap.PSpace.toSpec A N =
      Spec.map (CommRingCat.ofHom (DSMap.phiU A (DSMap.PSpace A N) (DSMap.PSpace.toSpec A N)
        (DPS (A := A) (N := N) S))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec (DSMap.PSpace.toSpec A N)
      (isAffineOpen_top (Spec (.of A))) haff (le_top : DPS (A := A) (N := N) S ≤ _)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [← h]
    rw [phiU_eq_appLE (DSMap.PSpace.toSpec A N) (DPS (A := A) (N := N) S)]
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    rfl
  -- Step 5: conclude by injectivity of `Spec.map` on `appTop`.
  have h5 : Spec.map (CommRingCat.ofHom (DSMap.phiU A (DSMap.PSpace A N)
        (DSMap.PSpace.toSpec A N) (DPS (A := A) (N := N) S))) =
      Spec.map (CommRingCat.ofHom (((Proj.awayToSection (DSMap.PGr A N) (tPS (A := A) S)).hom).comp
        (AtoAwayS (A := A) (N := N) S))) := by
    rw [← h4, h3]
  have h7 : CommRingCat.ofHom (DSMap.phiU A (DSMap.PSpace A N) (DSMap.PSpace.toSpec A N)
        (DPS (A := A) (N := N) S)) =
      CommRingCat.ofHom (((Proj.awayToSection (DSMap.PGr A N) (tPS (A := A) S)).hom).comp
        (AtoAwayS (A := A) (N := N) S)) :=
    Spec.map_injective h5
  exact RingHom.ext fun a => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h7) a

end Compat


/-! ## The identifications that assemble the proof -/

section Assembly

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {N : ℕ}

/-- `appLE` does not depend on the proof of the inequality. -/
lemma appLE_proof_irrel (i : X ⟶ DSMap.PSpace A N) (U : (DSMap.PSpace A N).Opens)
    (V : X.Opens) (e₁ e₂ : V ≤ i ⁻¹ᵁ U) : i.appLE U V e₁ = i.appLE U V e₂ := by
  simp only [Scheme.Hom.appLE]

/-- The image of `chartFracPS S l hl k` under `awayToSection` is the restriction of the
coordinate section `x_k/x_l` from `D₊(x_l)` to `DPS S`. -/
lemma awayToSection_chartFracPS (S : Finset (Idx N)) (l : Idx N) (hl : l ∈ S) (k : Idx N) :
    (Proj.awayToSection (DSMap.PGr A N) (tPS (A := A) S)).hom (chartFracPS (A := A) S l hl k)
      = ((DSMap.PSpace A N).presheaf.map
          (homOfLE (Proj.basicOpen_mono (DSMap.PGr A N) (MvPolynomial.X l.down) (tPS (A := A) S)
            ⟨∏ m ∈ S.erase l, MvPolynomial.X m.down, tPS_eq_mul (A := A) S l hl⟩)).op).hom
          (xiSecP (A := A) l k) := by
  have h := congrArg (fun φ => CommRingCat.Hom.hom φ (xiQ (A := A) l k))
    (Proj.awayMap_awayToSection (DSMap.PGr A N) (f := MvPolynomial.X l.down)
      (g := ∏ m ∈ S.erase l, MvPolynomial.X m.down) (gmem S l)
      (x := tPS (A := A) S) (hx := tPS_eq_mul (A := A) S l hl))
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h
  rw [← h, ← chartFracPS_eq]

/-- Pulling the chart coordinate `x_k/x_l` back along `i` gives `xiSecS`. -/
lemma appLE_chartFracPS (i : X ⟶ DSMap.PSpace A N) (S : Finset (Idx N)) (l : Idx N)
    (hl : l ∈ S) (k : Idx N)
    (e : (⨅ m ∈ S, DSMap.Mix2.chartCover i m) ≤ i ⁻¹ᵁ DPS (A := A) (N := N) S) :
    (i.appLE (DPS (A := A) (N := N) S) (⨅ m ∈ S, DSMap.Mix2.chartCover i m) e).hom
      ((Proj.awayToSection (DSMap.PGr A N) (tPS (A := A) S)).hom (chartFracPS (A := A) S l hl k))
      = xiSecS i S l hl k := by
  rw [awayToSection_chartFracPS]
  have hkey := congrArg (fun φ => CommRingCat.Hom.hom φ (xiSecP (A := A) l k))
    (Scheme.Hom.map_appLE (f := i) (e := e)
      (i := (homOfLE (Proj.basicOpen_mono (DSMap.PGr A N) (MvPolynomial.X l.down)
        (tPS (A := A) S) ⟨∏ m ∈ S.erase l, MvPolynomial.X m.down,
          tPS_eq_mul (A := A) S l hl⟩)).op))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hkey
  rw [hkey, ← xiSecS_eq_appLE i S l hl k]

/-- Naturality of the structure map: pulling `phiU A ℙ toSpec` back along `i` gives `phiU A X f`. -/
lemma appLE_phiU_pspace (f : X ⟶ Spec (.of A)) (i : X ⟶ DSMap.PSpace A N)
    (hif : i ≫ DSMap.PSpace.toSpec A N = f) (S : Finset (Idx N)) (a : A)
    (e : (⨅ m ∈ S, DSMap.Mix2.chartCover i m) ≤ i ⁻¹ᵁ DPS (A := A) (N := N) S) :
    (i.appLE (DPS (A := A) (N := N) S) (⨅ m ∈ S, DSMap.Mix2.chartCover i m) e).hom
      (DSMap.phiU A (DSMap.PSpace A N) (DSMap.PSpace.toSpec A N) (DPS (A := A) (N := N) S) a)
      = DSMap.phiU A X f (⨅ m ∈ S, DSMap.Mix2.chartCover i m) a := by
  rw [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [show (i.app (DPS (A := A) (N := N) S)).hom
        (DSMap.phiU A (DSMap.PSpace A N) (DSMap.PSpace.toSpec A N) (DPS (A := A) (N := N) S) a)
      = DSMap.phiU A X (i ≫ DSMap.PSpace.toSpec A N) (i ⁻¹ᵁ DPS (A := A) (N := N) S) a from
    Work.DSG4a.phiU_comp i (DSMap.PSpace.toSpec A N) (DPS (A := A) (N := N) S) a]
  rw [hif]
  exact DSMap.phiU_res A X f (homOfLE e) a

/-- The pullback map `Γ(ℙᴺ_A, DPS S) → Γ(X, U_S)` is surjective (closed immersion + affine open). -/
lemma appLE_surjective (i : X ⟶ DSMap.PSpace A N) (hi : IsClosedImmersion i)
    (S : Finset (Idx N)) (hS : S.Nonempty)
    (e : (⨅ m ∈ S, DSMap.Mix2.chartCover i m) ≤ i ⁻¹ᵁ DPS (A := A) (N := N) S) :
    Function.Surjective
      (i.appLE (DPS (A := A) (N := N) S) (⨅ m ∈ S, DSMap.Mix2.chartCover i m) e).hom := by
  haveI := hi
  have hB : Function.Surjective (X.presheaf.map (homOfLE e).op).hom := by
    have h1 : homOfLE e = eqToHom (preimage_DPS i S).symm := Subsingleton.elim _ _
    rw [h1]
    haveI : IsIso (X.presheaf.map (eqToHom (preimage_DPS i S).symm).op) := inferInstance
    exact (ConcreteCategory.bijective_of_isIso _).2
  have hA : Function.Surjective (i.app (DPS (A := A) (N := N) S)).hom :=
    Scheme.Hom.app_surjective i (DPS (A := A) (N := N) S) (DPS_affine S hS)
  have hcomp : (i.appLE (DPS (A := A) (N := N) S) (⨅ m ∈ S, DSMap.Mix2.chartCover i m) e).hom
      = (X.presheaf.map (homOfLE e).op).hom.comp (i.app (DPS (A := A) (N := N) S)).hom := by
    rw [Scheme.Hom.appLE, CommRingCat.hom_comp]
  rw [hcomp]
  exact hB.comp hA

/-- `awayToSection` is surjective (`basicOpenIsoAway`). -/
lemma awayToSection_surjective (S : Finset (Idx N)) (hS : S.Nonempty) :
    Function.Surjective (Proj.awayToSection (DSMap.PGr A N) (tPS (A := A) S)).hom := by
  haveI : IsIso (Proj.awayToSection (DSMap.PGr A N) (tPS (A := A) S)) := by
    rw [← Proj.basicOpenIsoAway_hom (DSMap.PGr A N) (tPS (A := A) S)
      (tPS_mem S) (Finset.card_pos.mpr hS)]
    infer_instance
  exact (ConcreteCategory.bijective_of_isIso _).2

/-- The comparison map `Γ(X, U_S) ← Γ(ℙᴺ_A, DPS S)` composed with its values on the generators
`x_k/x_l` is `eval₂Hom (phiU A X f U_S) (xiSecS ·)`. -/
lemma eval₂_xiSecS_eq (f : X ⟶ Spec (.of A)) (i : X ⟶ DSMap.PSpace A N)
    (hif : i ≫ DSMap.PSpace.toSpec A N = f) (S : Finset (Idx N)) (hS : S.Nonempty)
    (e : (⨅ m ∈ S, DSMap.Mix2.chartCover i m) ≤ i ⁻¹ᵁ DPS (A := A) (N := N) S) :
    MvPolynomial.eval₂Hom (DSMap.phiU A X f (⨅ m ∈ S, DSMap.Mix2.chartCover i m))
        (fun q : {l // l ∈ S} × Idx N => xiSecS i S q.1.1 q.1.2 q.2)
      = ((i.appLE (DPS (A := A) (N := N) S) (⨅ m ∈ S, DSMap.Mix2.chartCover i m) e).hom).comp
          (MvPolynomial.eval₂Hom
            (DSMap.phiU A (DSMap.PSpace A N) (DSMap.PSpace.toSpec A N) (DPS (A := A) (N := N) S))
            (fun q : {l // l ∈ S} × Idx N =>
              (Proj.awayToSection (DSMap.PGr A N) (tPS (A := A) S)).hom
                (chartFracPS (A := A) S q.1.1 q.1.2 q.2))) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
    exact (appLE_phiU_pspace f i hif S a e).symm
  · intro q
    rw [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
    exact (appLE_chartFracPS i S q.1.1 q.1.2 q.2 e).symm

/-- The `ℙᴺ_A`-side comparison map is `awayToSection` composed with the `Away`-side comparison. -/
lemma eval₂_pspace_eq (S : Finset (Idx N)) (hS : S.Nonempty) :
    MvPolynomial.eval₂Hom
        (DSMap.phiU A (DSMap.PSpace A N) (DSMap.PSpace.toSpec A N) (DPS (A := A) (N := N) S))
        (fun q : {l // l ∈ S} × Idx N =>
          (Proj.awayToSection (DSMap.PGr A N) (tPS (A := A) S)).hom
            (chartFracPS (A := A) S q.1.1 q.1.2 q.2))
      = ((Proj.awayToSection (DSMap.PGr A N) (tPS (A := A) S)).hom).comp
          (MvPolynomial.eval₂Hom (AtoAwayS (A := A) (N := N) S)
            (fun q : {l // l ∈ S} × Idx N =>
              chartFracPS (A := A) S q.1.1 q.1.2 q.2)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
    exact DFunLike.congr_fun (phiU_pspace_chart S hS) a
  · intro q
    rw [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, MvPolynomial.eval₂Hom_X']

end Assembly

/-- For `S` nonempty, `Γ(X, U_S)` is generated as an `A`-algebra by the chart coordinates
`x_k/x_l`, `l ∈ S` (this is what lets the geometric half of `SEC` define its comparison maps by
their values on the generators).  Route: `Scheme.Hom.app_surjective` on the affine open
`D₊(∏_{l∈S} X_l) ⊆ ℙᴺ_A` together with the generation of `↧(Away (PGr A N) (∏_{l∈S} X_l))` by
the elements `X_k/X_l` (the `Away.mk` description, `Away.mk_surjective`; for a single variable
this is `Work.DSG2.Phi_surjective`). -/
theorem adjoin_xiSecS_eq_top {A : Type u} [CommRing A] {X : Scheme.{u}} {N : ℕ}
    (f : X ⟶ Spec (.of A)) (i : X ⟶ DSMap.PSpace A N) (hi : IsClosedImmersion i)
    (hif : i ≫ DSMap.PSpace.toSpec A N = f) (S : Finset (Work.DSSEC.Idx N)) (hS : S.Nonempty) :
    Function.Surjective fun p : MvPolynomial ({l // l ∈ S} × Work.DSSEC.Idx N) A =>
      MvPolynomial.eval₂ (DSMap.phiU A X f (⨅ m ∈ S, DSMap.Mix2.chartCover i m))
        (fun q : {l // l ∈ S} × Work.DSSEC.Idx N =>
          Work.DSSEC.xiSecS i S q.1.1 q.1.2 q.2) p := by
  intro y
  have he : (⨅ m ∈ S, DSMap.Mix2.chartCover i m) ≤ i ⁻¹ᵁ DPS (A := A) (N := N) S :=
    le_of_eq (preimage_DPS i S).symm
  obtain ⟨z, hz⟩ := appLE_surjective i hi S hS he y
  have hsurj : Function.Surjective
      (MvPolynomial.eval₂Hom
        (DSMap.phiU A (DSMap.PSpace A N) (DSMap.PSpace.toSpec A N) (DPS (A := A) (N := N) S))
        (fun q : {l // l ∈ S} × Idx N =>
          (Proj.awayToSection (DSMap.PGr A N) (tPS (A := A) S)).hom
            (chartFracPS (A := A) S q.1.1 q.1.2 q.2))) := by
    rw [eval₂_pspace_eq S hS]
    exact (awayToSection_surjective S hS).comp (PSGen.awayGenPS_aux S hS)
  obtain ⟨p, hp⟩ := hsurj z
  refine ⟨p, ?_⟩
  change ⇑(MvPolynomial.eval₂Hom
        (DSMap.phiU A X f (⨅ m ∈ S, DSMap.Mix2.chartCover i m))
        (fun q : {l // l ∈ S} × Idx N => xiSecS i S q.1.1 q.1.2 q.2)) p = y
  rw [eval₂_xiSecS_eq f i hif S hS he, RingHom.comp_apply, hp, hz]


end Work.DSSEC
