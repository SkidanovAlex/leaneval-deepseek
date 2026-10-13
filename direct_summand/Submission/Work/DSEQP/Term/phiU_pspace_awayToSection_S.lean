import Mathlib
import Submission.Work.DSEQP.gf_defs
import Submission.Work.DSCHART.xiSec_surjective

/-!
# The structure map of `ℙᴺ_A` on the chart `D₊(x_S)`

For `S : Finset (Fin (N+1))` nonempty, the structure map

`A ⟶ Γ(ℙᴺ_A, D₊(x_S))`,   `xS S = ∏_{i ∈ S} X_i`,

of `ℙᴺ_A = Proj A[x₀,…,x_N]` restricted to the chart `D₊(x_S)` (which is exactly
`DSMap.phiU A (PSpace A N) (PSpace.toSpec A N) (Dcmp S)`) is the composite

`A ⟶ A[x₀,…,x_N]_0 ⟶ Away 𝒜 (x_S) ⟶ Γ(ℙᴺ_A, D₊(x_S))`

of the canonical map `AtoAway` into the chart ring (the degree-zero part of the localization
inverting `x_S`) with `Proj.awayToSection`, the canonical comparison
`Away 𝒜 f ⟶ Γ(Proj 𝒜, D₊(f))`.

This is the `Finset`-generalisation of `Work.DSCHART.phiU_pspace_toSpec_eq_awayToSection`, which
is the case `S = {j}` (`x_S = X_j`); the proof is the same one, carried out for an arbitrary
homogeneous form `f` of positive degree.  Everything needed on the way (the restriction map
`Γ(ℙᴺ_A, ⊤) → Γ(ℙᴺ_A, D₊(f))` described through the open immersion `awayι`, and the description
of `toSpecZero` on the chart) is stated below in that generality and then instantiated at
`f = x_S`.
-/

namespace Work.DSEQP.Term

universe a

open CategoryTheory AlgebraicGeometry

section Generic

variable {A : Type a} [CommRing A] {N : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- The restriction `Γ(ℙᴺ_A, ⊤) → Γ(ℙᴺ_A, D₊(f))` is the composite of the restriction along the
open immersion `D₊(f) ↪ ℙᴺ_A` with the identification of `Γ(D₊(f), 𝒪)` with the sections of the
open subscheme over `⊤`. -/
lemma pspace_restrict_eq_ι_topIso (f : MvPolynomial (Fin (N + 1)) A) :
    (Proj.basicOpen (DSMap.PGr A N) f).ι.appTop ≫
      (Proj.basicOpen (DSMap.PGr A N) f).topIso.hom
    = (DSMap.PSpace A N).presheaf.map
        (homOfLE (le_top : Proj.basicOpen (DSMap.PGr A N) f ≤
          (⊤ : (DSMap.PSpace A N).Opens))).op := by
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  rw [← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The open immersion `awayι 𝒜 f : Spec (Away 𝒜 f) ⟶ ℙᴺ_A` composed with the canonical
isomorphism `D₊(f) ≅ Spec (Away 𝒜 f)` is the inclusion of the chart `D₊(f)`. -/
lemma pspace_ι_eq_awayι (f : MvPolynomial (Fin (N + 1)) A) {m : ℕ}
    (hf : f ∈ DSMap.PGr A N m) (hm : 0 < m) :
    (Proj.basicOpen (DSMap.PGr A N) f).ι
      = (Proj.basicOpenIsoSpec (DSMap.PGr A N) f hf hm).hom
        ≫ Proj.awayι (DSMap.PGr A N) f hf hm := by
  rw [← Proj.basicOpenIsoSpec_inv_ι (DSMap.PGr A N) f hf hm, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- `Proj.basicOpenToSpec_app_top`, transported back along the canonical identification of the
sections of `D₊(f)` with those of the chart scheme `Spec (Away 𝒜 f)`. -/
lemma pspace_basicOpenToSpec_appTop_comp_topIso (f : MvPolynomial (Fin (N + 1)) A) :
    Scheme.Hom.appTop (Proj.basicOpenToSpec (DSMap.PGr A N) f)
        ≫ (Proj.basicOpen (DSMap.PGr A N) f).topIso.hom
      = (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away (DSMap.PGr A N) f))).hom
        ≫ Proj.awayToSection (DSMap.PGr A N) f := by
  rw [show Scheme.Hom.appTop (Proj.basicOpenToSpec (DSMap.PGr A N) f)
      = (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away (DSMap.PGr A N) f))).hom
        ≫ Proj.awayToSection (DSMap.PGr A N) f
        ≫ (Proj.basicOpen (DSMap.PGr A N) f).topIso.inv
      from Proj.basicOpenToSpec_app_top (DSMap.PGr A N) f]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- **The restriction map of `ℙᴺ_A` to the chart `D₊(f)` is `awayToSection` followed by the
inverse of the canonical identification `Spec (Away 𝒜 f) ≅ D₊(f)`.**

Here `f` is a homogeneous form of positive degree, so that `D₊(f)` is an affine chart of `ℙᴺ_A`
and `Γ(D₊(f), 𝒪) ≅ (𝒜_f)₀` via `awayToSection`. -/
lemma pspace_restrict_eq_awayToSection (f : MvPolynomial (Fin (N + 1)) A) {m : ℕ}
    (hf : f ∈ DSMap.PGr A N m) (hm : 0 < m) :
    (DSMap.PSpace A N).presheaf.map
        (homOfLE (le_top : Proj.basicOpen (DSMap.PGr A N) f ≤
          (⊤ : (DSMap.PSpace A N).Opens))).op
      = Scheme.Hom.appTop (Proj.awayι (DSMap.PGr A N) f hf hm)
        ≫ ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away (DSMap.PGr A N) f))).hom
          ≫ Proj.awayToSection (DSMap.PGr A N) f) := by
  rw [← pspace_restrict_eq_ι_topIso (A := A) (N := N) f, pspace_ι_eq_awayι f hf hm,
    Proj.basicOpenIsoSpec_hom, Scheme.Hom.comp_appTop, Category.assoc,
    pspace_basicOpenToSpec_appTop_comp_topIso (A := A) (N := N) f]

set_option backward.isDefEq.respectTransparency false in
/-- **`Proj.toSpecZero` restricted to the affine chart `D₊(f)`.**

`awayι 𝒜 f ≫ toSpecZero 𝒜` is by definition `Spec.map (fromZeroRingHom 𝒜 (powers f))`, and
unwinding the canonical identifications `Γ(Spec R) ≅ R` turns this into: the coordinate ring of the
chart, realised inside `Γ(ℙᴺ_A, D₊(f))`, receives the structure map of `ℙᴺ_A` through the
localization map `fromZeroRingHom 𝒜 (powers f)`. -/
lemma pspace_toSpecZero_appTop_comp_awayι_appTop (f : MvPolynomial (Fin (N + 1)) A) {m : ℕ}
    (hf : f ∈ DSMap.PGr A N m) (hm : 0 < m) :
    Scheme.Hom.appTop (Proj.toSpecZero (DSMap.PGr A N))
        ≫ Scheme.Hom.appTop (Proj.awayι (DSMap.PGr A N) f hf hm)
      = (Scheme.ΓSpecIso (CommRingCat.of ↥(DSMap.PGr A N 0))).hom
        ≫ CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (DSMap.PGr A N)
            (Submonoid.powers f))
        ≫ (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away (DSMap.PGr A N) f))).inv := by
  rw [← Scheme.Hom.comp_appTop, Proj.awayι_toSpecZero (DSMap.PGr A N) f hf hm]
  refine Eq.symm ?_
  calc (Scheme.ΓSpecIso (CommRingCat.of ↥(DSMap.PGr A N 0))).hom
        ≫ (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (DSMap.PGr A N)
            (Submonoid.powers f))
          ≫ (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away (DSMap.PGr A N) f))).inv)
      = (Scheme.ΓSpecIso (CommRingCat.of ↥(DSMap.PGr A N 0))).hom
        ≫ ((Scheme.ΓSpecIso (CommRingCat.of ↥(DSMap.PGr A N 0))).inv
          ≫ Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom
              (DSMap.PGr A N) (Submonoid.powers f))))) := by
        rw [Scheme.ΓSpecIso_inv_naturality]
    _ = Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom
            (DSMap.PGr A N) (Submonoid.powers f)))) := by
        rw [Iso.hom_inv_id_assoc]

end Generic

/-- **The structure map of `ℙᴺ_A` on the chart `D₊(x_S)`** (see the module docstring). -/
theorem phiU_pspace_awayToSection_S (A : Type a) [CommRing A] {N : ℕ}
    (S : Finset (Fin (N + 1))) (hS : S.Nonempty) :
    DSMap.phiU A (DSMap.PSpace A N) (DSMap.PSpace.toSpec A N)
        (Work.DSEQP.Dcmp (A := A) (N := N) S)
      = ((AlgebraicGeometry.Proj.awayToSection (DSMap.PGr A N) (Work.DSEQP.xS (A := A) S)).hom).comp
          (Work.DSEQP.AtoAway (A := A) (N := N) S) := by
  -- the structure map `A ⟶ Γ(ℙᴺ_A, ⊤)` factors through `Γ(Spec (A[x₀,…,x_N]_0), ⊤)`
  have hphi : DSMap.phi A (DSMap.PSpace A N) (DSMap.PSpace.toSpec A N)
      = ((Scheme.Hom.appTop (Proj.toSpecZero (DSMap.PGr A N))).hom).comp
          (((Scheme.ΓSpecIso (CommRingCat.of ↥(DSMap.PGr A N 0))).inv.hom).comp
            (algebraMap A ↥(DSMap.PGr A N 0))) := by
    rw [DSMap.PSpace.toSpec, Work.DSG1.phi_comp, Work.DSG1.gammaMap]
    rw [Work.DSCHART.phi_specMap (algebraMap A ↥(DSMap.PGr A N 0))]
  -- the restriction to `D₊(x_S)`, and `toSpecZero` on that chart
  have hrest := congrArg CommRingCat.Hom.hom
    (pspace_restrict_eq_awayToSection (A := A) (N := N) (Work.DSEQP.xS (A := A) S)
      (Work.DSEQP.xS_mem_homSub S) (Finset.card_pos.mpr hS))
  have happ0 := congrArg CommRingCat.Hom.hom
    (pspace_toSpecZero_appTop_comp_awayι_appTop (A := A) (N := N) (Work.DSEQP.xS (A := A) S)
      (Work.DSEQP.xS_mem_homSub S) (Finset.card_pos.mpr hS))
  apply RingHom.ext
  intro x
  rw [RingHom.comp_apply, DSMap.phiU, RingHom.comp_apply, hphi]
  simp only [RingHom.comp_apply]
  rw [hrest]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  have happ := DFunLike.congr_fun happ0 ((Scheme.ΓSpecIso (CommRingCat.of ↥(DSMap.PGr A N 0))).inv.hom
        (algebraMap A ↥(DSMap.PGr A N 0) x))
  rw [CommRingCat.hom_comp] at happ
  rw [RingHom.comp_apply] at happ
  rw [CommRingCat.hom_comp] at happ
  rw [RingHom.comp_apply] at happ
  rw [CommRingCat.hom_comp] at happ
  rw [RingHom.comp_apply] at happ
  rw [CommRingCat.hom_ofHom] at happ
  rw [happ]
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  congr 1

end Work.DSEQP.Term
