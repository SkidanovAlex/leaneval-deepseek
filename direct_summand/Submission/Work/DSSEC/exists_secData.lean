import Mathlib
import Submission.Work.DSSEC.Basic
import Submission.Work.DSCHART.Main
import Submission.Work.DSCHART.xiSec_self
import Submission.Work.DSSEC.xiSecS_pair
import Submission.Work.DSSEC.chartFrac_locRes
import Submission.Work.DSSEC.chartToCmp_injective
import Submission.Work.DSSEC.adjoin_xiSecS_eq_top
import Submission.Work.DSSEC.awayGenPSAlt

/-!
# DSSEC — the geometric half of node `SEC`: `Work.DSSEC.exists_secData`

This file proves `Work.DSSEC.exists_secData`: the `W[1/p]`-point `θ` of the chart
`U_j = X ∩ D₊(x_j)` together with homogeneous coordinates `t` produces the chart comparison
`Work.DSSEC.SecData` on nonempty index sets.

## Contents

* **Geometric input** (proved here, self-contained):
  * `Work.DSSEC.proj_basicOpen_isLocalizationElem` — on `Proj` of a graded ring, the basic open of
    the chart coordinate `g^m/f^{m'}` is `D₊(f) ∩ D₊(g)`;
  * `Work.DSSEC.basicOpen_xiSec` — hence on `X`, `X.basicOpen (xiSec i j k) = U_j ⊓ U_k`;
  * `Work.DSSEC.basicOpen_prod_xiSec` — for a finite set `S`,
    `X.basicOpen (∏_{l∈S} xiSec i j l) = U_j ⊓ ⋂_{l ∈ S} U_l`;
  * `Work.DSSEC.exists_lift_xiSecS_prod_aux` — since `U_j` is affine, `Γ(X, U_{S∪{j}})` is the
    localization of `Γ(X, U_j)` at the coordinates `x_l/x_j` (`l ∈ S`), so a ring hom out of
    `Γ(X, U_j)` inverting them extends;
  * `Work.DSSEC.isUnit_cmpOfW_theta_prod_xiSec_aux` — the images of those coordinates under
    `cmpOfW ∘ θ` are units of `W[1/(p·t_S)]` (from `htθ`).
* **Assembly**: the two `W`-algebras `Γ(X, U_S)` and `W[J/t_S]` are compared inside
  `W[1/(p·t_S)]`; the comparison lands in the chart ring because the range of
  `chartToCmp` is a subring containing the images of the generators, and it is `A`-linear and
  compatible with restrictions because `Γ(X, U_S)` is generated over `A` by the coordinates
  (`Work.DSSEC.adjoin_xiSecS_eq_top`).

The chart comparison produced by the proof is
`g_S := (chartToCmp p t S)⁻¹ ∘ (ρ_S ∘ res)`, where `ρ_S` is the localization of `cmpOfW ∘ θ`.
-/

attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

universe u v

namespace Work.DSSEC

open DSMap DSMap.Mix2

section ProjAux

/-- preimage of a basic open under `Spec.map`. -/
lemma spec_map_preimage_basicOpen {R S : CommRingCat} (φ : R ⟶ S) (r : R) :
    Spec.map φ ⁻¹ᵁ (PrimeSpectrum.basicOpen r) = PrimeSpectrum.basicOpen (φ.hom r) := by
  rw [AlgebraicGeometry.Spec.map_base]
  exact PrimeSpectrum.comap_basicOpen φ.hom r

lemma Scheme.Hom.preimage_comp' {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (W : Z.Opens) :
    (f ≫ g) ⁻¹ᵁ W = f ⁻¹ᵁ (g ⁻¹ᵁ W) := by
  rw [Scheme.Hom.comp_base]
  rfl

/-- **The basic open of the chart coordinate `g^m / f^{m'}` is `D₊(f) ∩ D₊(g)`.** -/
theorem proj_basicOpen_isLocalizationElem {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (f g : A) {m m' : ℕ} (hf : f ∈ 𝒜 m)
    (hg : g ∈ 𝒜 m') (hm : 0 < m) (hm' : 0 < m') :
    (Proj 𝒜).basicOpen ((Proj.basicOpenIsoAway 𝒜 f hf hm).hom
        (HomogeneousLocalization.Away.isLocalizationElem hf hg))
      = Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g := by
  have hU : IsAffineOpen (Proj.basicOpen 𝒜 f) := Proj.isAffineOpen_basicOpen 𝒜 f hf hm
  let e' : Spec ↧(HomogeneousLocalization.Away 𝒜 f) ≅ Spec ↑Γ(Proj 𝒜, Proj.basicOpen 𝒜 f) :=
    asIso (Spec.map (Proj.basicOpenIsoAway 𝒜 f hf hm).inv)
  have he'_hom : e'.hom = Spec.map (Proj.basicOpenIsoAway 𝒜 f hf hm).inv := asIso_hom _
  have hiso : hU.isoSpec = Proj.basicOpenIsoSpec 𝒜 f hf hm ≪≫ e' := by
    apply Iso.ext
    rw [Iso.trans_hom, he'_hom, Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec,
      IsAffineOpen.isoSpec_hom, Category.assoc]
    have h2 : Spec.map (Proj.awayToSection 𝒜 f) ≫
        Spec.map (Proj.basicOpenIsoAway 𝒜 f hf hm).inv = 𝟙 _ := by
      rw [← Spec.map_comp]
      have h3 : (Proj.basicOpenIsoAway 𝒜 f hf hm).inv ≫ Proj.awayToSection 𝒜 f = 𝟙 _ := by
        rw [← Proj.basicOpenIsoAway_hom]
        exact Iso.inv_hom_id _
      rw [h3, Spec.map_id]
    rw [h2, Category.comp_id]
  have hfrom : e'.hom ≫ hU.fromSpec = Proj.awayι 𝒜 f hf hm := by
    rw [← IsAffineOpen.isoSpec_inv_ι hU, hiso, Iso.trans_inv, Proj.awayι]
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_assoc]
  have hfrom' : Spec.map (Proj.basicOpenIsoAway 𝒜 f hf hm).inv ≫ hU.fromSpec
      = Proj.awayι 𝒜 f hf hm := by
    rw [← he'_hom, hfrom]
  have hpre : Proj.awayι 𝒜 f hf hm ⁻¹ᵁ
        (Proj 𝒜).basicOpen ((Proj.basicOpenIsoAway 𝒜 f hf hm).hom
          (HomogeneousLocalization.Away.isLocalizationElem hf hg))
      = PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem hf hg) := by
    rw [← hfrom', Scheme.Hom.preimage_comp', IsAffineOpen.fromSpec_preimage_basicOpen,
      spec_map_preimage_basicOpen]
    congr 1
    exact Iso.hom_inv_id_apply _ _
  have hpre2 : Proj.awayι 𝒜 f hf hm ⁻¹ᵁ Proj.basicOpen 𝒜 g
      = PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem hf hg) :=
    Proj.awayι_preimage_basicOpen 𝒜 hf hm hg hm'
  have hpre_all : Proj.awayι 𝒜 f hf hm ⁻¹ᵁ
        (Proj 𝒜).basicOpen ((Proj.basicOpenIsoAway 𝒜 f hf hm).hom
          (HomogeneousLocalization.Away.isLocalizationElem hf hg))
      = Proj.awayι 𝒜 f hf hm ⁻¹ᵁ Proj.basicOpen 𝒜 g :=
    hpre.trans hpre2.symm
  have himg := congrArg (fun W : (Spec ↧(HomogeneousLocalization.Away 𝒜 f)).Opens =>
    Proj.awayι 𝒜 f hf hm ''ᵁ W) hpre_all
  simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Proj.opensRange_awayι] at himg
  rw [← himg, inf_eq_right.mpr (Scheme.basicOpen_le _ _)]

end ProjAux

section XSide

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {N : ℕ}

/-- `i ⁻¹ᵁ (U ⊓ V) = i ⁻¹ᵁ U ⊓ i ⁻¹ᵁ V`. -/
lemma preimage_inf' (i : X ⟶ DSMap.PSpace A N) (U V : (DSMap.PSpace A N).Opens) :
    i ⁻¹ᵁ (U ⊓ V) = i ⁻¹ᵁ U ⊓ i ⁻¹ᵁ V := rfl

/-- **`X.basicOpen (xiSec i j k) = U_j ⊓ U_k`.** -/
lemma basicOpen_xiSec (i : X ⟶ DSMap.PSpace A N) (j k : Fin (N + 1)) :
    X.basicOpen (DSMap.Mix2.xiSec i j k) =
      DSMap.Mix2.chartCover i ⟨j⟩ ⊓ DSMap.Mix2.chartCover i ⟨k⟩ := by
  have hf := DSMap.Mix2.X_mem_PGr (A := A) j
  have hg := DSMap.Mix2.X_mem_PGr (A := A) k
  have hm : (0 : ℕ) < 1 := Nat.one_pos
  have hz : HomogeneousLocalization.Away.isLocalizationElem hf hg
      = HomogeneousLocalization.Away.mk (DSMap.PGr A N) hf 1 (MvPolynomial.X k)
          (by rw [one_smul]; exact hg) := by
    simp only [HomogeneousLocalization.Away.isLocalizationElem]
    rw [HomogeneousLocalization.ext_iff_val]
    simp [HomogeneousLocalization.Away.val_mk, pow_one]
  have hsec : DSMap.Mix2.xiSec i j k =
      (i.app (Proj.basicOpen (DSMap.PGr A N) (MvPolynomial.X j))).hom
        ((Proj.basicOpenIsoAway (DSMap.PGr A N) (MvPolynomial.X j) hf hm).hom
          (HomogeneousLocalization.Away.isLocalizationElem hf hg)) := by
    rw [hz, Proj.basicOpenIsoAway_hom]
    rfl
  rw [hsec, ← Scheme.preimage_basicOpen,
    proj_basicOpen_isLocalizationElem (DSMap.PGr A N) (MvPolynomial.X j) (MvPolynomial.X k)
      hf hg hm hm]
  rfl

/-- The basic open of the product of the chart coordinates `x_l/x_j`, `l ∈ S`. -/
lemma basicOpen_prod_xiSec (i : X ⟶ DSMap.PSpace A N) (S : Finset (Idx N)) (j : Fin (N + 1)) :
    X.basicOpen (∏ l ∈ S, DSMap.Mix2.xiSec i j l.down)
      = DSMap.Mix2.chartCover i ⟨j⟩ ⊓ ⨅ l ∈ S, DSMap.Mix2.chartCover i l := by
  classical
  induction S using Finset.induction with
  | empty =>
    rw [Finset.prod_empty, Scheme.basicOpen_one]
    simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul, ih, basicOpen_xiSec, Finset.iInf_insert]
    show (DSMap.Mix2.chartCover i ⟨j⟩ ⊓ DSMap.Mix2.chartCover i a)
        ⊓ (DSMap.Mix2.chartCover i ⟨j⟩ ⊓ ⨅ l ∈ S, DSMap.Mix2.chartCover i l)
      = DSMap.Mix2.chartCover i ⟨j⟩ ⊓
        (DSMap.Mix2.chartCover i a ⊓ ⨅ l ∈ S, DSMap.Mix2.chartCover i l)
    refine le_antisymm ?_ ?_
    · exact le_inf (le_trans inf_le_left inf_le_left)
        (le_inf (le_trans inf_le_left inf_le_right) (le_trans inf_le_right inf_le_right))
    · exact le_inf (le_inf inf_le_left (le_trans inf_le_right inf_le_left))
        (le_inf inf_le_left (le_trans inf_le_right inf_le_right))

/-- **The localization step of the geometric half of `SEC`**: a ring hom out of `Γ(X, U_j)` that
inverts the chart coordinates `x_l/x_j` (`l ∈ S`) extends to `Γ(X, U_{S ∪ {j}})`. -/
theorem exists_lift_xiSecS_prod_aux (i : X ⟶ DSMap.PSpace A N) (hi : IsClosedImmersion i)
    (S : Finset (Idx N)) (j : Fin (N + 1)) {T : Type u} [CommRing T]
    (g : Γ(X, DSMap.Mix2.chartCover i ⟨j⟩) →+* T)
    (hg : ∀ l ∈ S, IsUnit (g (DSMap.Mix2.xiSec i j l.down))) :
    ∃ φ : Γ(X, ⨅ m ∈ insert (⟨j⟩ : Idx N) S, DSMap.Mix2.chartCover i m) →+* T,
      ∀ x : Γ(X, DSMap.Mix2.chartCover i ⟨j⟩),
        φ ((X.presheaf.map (homOfLE (iInf_chartCover_le_single i
            (Finset.mem_insert_self (⟨j⟩ : Idx N) S))).op).hom x) = g x := by
  classical
  have hU : IsAffineOpen (DSMap.Mix2.chartCover i ⟨j⟩) :=
    DSMap.Mix2.chartCover_affine_proved i hi ⟨j⟩
  have hle : (⨅ m ∈ insert (⟨j⟩ : Idx N) S, DSMap.Mix2.chartCover i m)
      ≤ DSMap.Mix2.chartCover i ⟨j⟩ :=
    iInf_chartCover_le_single i (Finset.mem_insert_self (⟨j⟩ : Idx N) S)
  have hV : (⨅ m ∈ insert (⟨j⟩ : Idx N) S, DSMap.Mix2.chartCover i m)
      = X.basicOpen (∏ l ∈ S, DSMap.Mix2.xiSec i j l.down) := by
    rw [Finset.iInf_insert, basicOpen_prod_xiSec]
  letI : Algebra Γ(X, DSMap.Mix2.chartCover i ⟨j⟩)
      Γ(X, ⨅ m ∈ insert (⟨j⟩ : Idx N) S, DSMap.Mix2.chartCover i m) :=
    (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  haveI hloc : IsLocalization.Away (∏ l ∈ S, DSMap.Mix2.xiSec i j l.down)
      Γ(X, ⨅ m ∈ insert (⟨j⟩ : Idx N) S, DSMap.Mix2.chartCover i m) :=
    hU.isLocalization_of_eq_basicOpen (f := ∏ l ∈ S, DSMap.Mix2.xiSec i j l.down)
      (i := homOfLE hle) hV
  have hgunit : IsUnit (g (∏ l ∈ S, DSMap.Mix2.xiSec i j l.down)) := by
    rw [map_prod]
    exact Finset.prod_induction _ (fun x => IsUnit x) (fun a b ha hb => ha.mul hb) isUnit_one hg
  exact ⟨IsLocalization.Away.lift (∏ l ∈ S, DSMap.Mix2.xiSec i j l.down) hgunit,
    fun x => IsLocalization.Away.lift_eq _ _ x⟩

/-- **The images of the chart coordinates under `cmpOfW ∘ θ` are units.** -/
lemma isUnit_cmpOfW_theta_prod_xiSec_aux (i : X ⟶ DSMap.PSpace A N) (j : Fin (N + 1))
    {W : Type u} [CommRing W] (p : ℕ)
    (θ : Γ(X, DSMap.Mix2.chartCover i ⟨j⟩) →+* Localization.Away (p : W))
    (t : Idx N → W) (ht : IsUnit (algebraMap W (Localization.Away (p : W)) (t ⟨j⟩)))
    (htθ : ∀ k, k ≠ j → algebraMap W (Localization.Away (p : W)) (t ⟨k⟩) =
      algebraMap W _ (t ⟨j⟩) * θ (DSMap.Mix2.xiSec i j k))
    (S : Finset (Idx N)) :
    IsUnit ((Work.DSSEC.cmpOfW p t S).comp θ (∏ l ∈ S, DSMap.Mix2.xiSec i j l.down)) := by
  have hfac : ∀ l ∈ S, IsUnit ((Work.DSSEC.cmpOfW p t S).comp θ
      (DSMap.Mix2.xiSec i j l.down)) := by
    intro l hl
    by_cases hlj : l.down = j
    · have h1 : DSMap.Mix2.xiSec i j l.down = 1 := by
        rw [hlj]
        exact Work.DSCHART.xiSec_self i j
      rw [h1, map_one]
      exact isUnit_one
    · have hθl := htθ l.down hlj
      have h1 : algebraMap W (Work.DSSEC.cmpRing p t S) (t l) =
          algebraMap W (Work.DSSEC.cmpRing p t S) (t ⟨j⟩) *
            ((Work.DSSEC.cmpOfW p t S).comp θ) (DSMap.Mix2.xiSec i j l.down) := by
        have h2 := congrArg (Work.DSSEC.cmpOfW p t S) hθl
        simpa only [map_mul, RingHom.comp_apply, Work.DSSEC.cmpOfW_eq] using h2
      have hAl : IsUnit (algebraMap W (Work.DSSEC.cmpRing p t S) (t l)) :=
        Work.DSSEC.isUnit_cmp_t p t S hl
      rw [h1] at hAl
      exact (IsUnit.mul_iff.mp hAl).2
  rw [map_prod]
  exact Finset.prod_induction _ (fun x => IsUnit x) (fun a b ha hb => ha.mul hb) isUnit_one hfac

/-- Morphisms of the preorder category of opens with the same source and target are equal;
in particular `homOfLE` does not depend on its proof. -/
lemma homOfLE_congr {Y : Scheme.{u}} {U V : Y.Opens} (h₁ h₂ : U ≤ V) :
    homOfLE h₁ = homOfLE h₂ := Subsingleton.elim _ _

/-- The chart coordinates are compatible with the restriction maps `U_S → U_T` (`S ⊆ T`). -/
lemma xiSecS_restrict (i : X ⟶ DSMap.PSpace A N) {S T : Finset (Idx N)} (hST : S ⊆ T)
    (l : Idx N) (hl : l ∈ S) (k : Idx N) :
    (X.presheaf.map (homOfLE (iInf_chartCover_le i hST)).op).hom (xiSecS i S l hl k)
      = xiSecS i T l (hST hl) k := by
  simp only [xiSecS]
  have h : (X.presheaf.map (homOfLE (iInf_chartCover_le_single i hl)).op) ≫
      (X.presheaf.map (homOfLE (iInf_chartCover_le i hST)).op) =
      X.presheaf.map (homOfLE (iInf_chartCover_le_single i (hST hl))).op := by
    rw [← Functor.map_comp]
    exact congrArg (fun f => X.presheaf.map f) (Subsingleton.elim _ _)
  rw [← CommRingCat.comp_apply, h]

/-- The fraction identity of the chart coordinates, on any index set containing `l` and `m`. -/
lemma xiSecS_pair_finset (i : X ⟶ DSMap.PSpace A N) (S : Finset (Idx N)) (l m k : Idx N)
    (hl : l ∈ S) (hm : m ∈ S) :
    xiSecS i S m hm k * xiSecS i S l hl m = xiSecS i S l hl k := by
  have hsub : ({l, m} : Finset (Idx N)) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hl
    · rw [Finset.mem_singleton] at hx; exact hx ▸ hm
  have h := congrArg ((X.presheaf.map (homOfLE (iInf_chartCover_le i hsub)).op).hom)
    (xiSecS_pair i l m k)
  simp only [map_mul] at h
  rw [xiSecS_restrict i hsub m (by simp) k, xiSecS_restrict i hsub l (by simp) m,
    xiSecS_restrict i hsub l (by simp) k] at h
  simpa using h



/-- `chartToCmp` sends the image of `w : W` in the chart ring to the image of `w` in `cmpRing`. -/
lemma chartToCmp_algebraMap {W : Type u} [CommRing W] {ι : Type u} [DecidableEq ι] (p : ℕ)
    (t : ι → W) (S : Finset ι) (w : W) :
    Work.DSSEC.chartToCmp p t S (algebraMap W (DSMap.Mix2.chartRing t S) w)
      = algebraMap W (Work.DSSEC.cmpRing p t S) w := by
  show Work.DSSEC.cmpOfLoc p t S
      ((DSMap.Mix2.chartRing t S).val (algebraMap W (DSMap.Mix2.chartRing t S) w)) = _
  rw [AlgHom.commutes]
  exact Work.DSSEC.cmpOfLoc_eq p t S w

theorem adjoin_xiSecS_eq_top_self {A : Type u} [CommRing A] {X : Scheme.{u}} {N : ℕ}
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
    exact (awayToSection_surjective S hS).comp (Work.DSSEC.awayGenPSAlt S hS)
  obtain ⟨p, hp⟩ := hsurj z
  refine ⟨p, ?_⟩
  change ⇑(MvPolynomial.eval₂Hom
        (DSMap.phiU A X f (⨅ m ∈ S, DSMap.Mix2.chartCover i m))
        (fun q : {l // l ∈ S} × Idx N => xiSecS i S q.1.1 q.1.2 q.2)) p = y
  rw [eval₂_xiSecS_eq f i hif S hS he, RingHom.comp_apply, hp, hz]



/-- **Geometric half of node `SEC`**: the data of a `W[1/p]`-point of the chart
`U_j = X ∩ D₊(x_j)` (a ring hom `θ : Γ(X, U_j) → W[1/p]` compatible with `A → W`) together with
homogeneous coordinates `t_k ∈ W` satisfying `t_k = t_j · θ(x_k/x_j)` produce a comparison
`Γ(X, U_S) → W[J/t_S]`, `x_k/x_i ↦ t_k/t_i`, for every **nonempty** `S` (`Work.DSSEC.SecData`).

The route is the one described in the module docstring: the localization of `Γ(X, U_j)` at the
coordinates `x_l/x_j` (`l ∈ S`, `Work.DSSEC.exists_lift_xiSecS_prod_aux`, from the affineness of
the chart `U_j`), the images of `θ` in `W[1/(p·t_S)]` (`Work.DSSEC.isUnit_cmpOfW_theta_prod_xiSec_aux`)
and the identification of the two `W`-algebras through the injective comparison
`W[J/t_S] → W[1/(p·t_S)]` (`Work.DSSEC.chartToCmp_injective`), together with the compatibility of
the chart coordinates with restrictions (`Work.DSSEC.chartFrac_locRes`) and the generation of
`Γ(X, U_S)` by the coordinates (`Work.DSSEC.adjoin_xiSecS_eq_top`). -/
theorem exists_secData (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) (N : ℕ) (i : X ⟶ DSMap.PSpace A N) (hi : IsClosedImmersion i)
    (hif : i ≫ DSMap.PSpace.toSpec A N = f) (j : Fin (N + 1))
    (W : Type u) [CommRing W] (hW : IsSMulRegular W (p : W)) (ψ : A →+* W)
    (θ : Γ(X, DSMap.Mix2.chartCover i ⟨j⟩) →+* Localization.Away (p : W))
    (hθ : θ.comp (DSMap.phiU A X f (DSMap.Mix2.chartCover i ⟨j⟩)) = (algebraMap W _).comp ψ)
    (t : Work.DSSEC.Idx N → W)
    (ht : IsUnit (algebraMap W (Localization.Away (p : W)) (t ⟨j⟩)))
    (htθ : ∀ k, k ≠ j → algebraMap W (Localization.Away (p : W)) (t ⟨k⟩) =
      algebraMap W _ (t ⟨j⟩) * θ (DSMap.Mix2.xiSec i j k)) :
    Nonempty (Work.DSSEC.SecData A X f N i W ψ t) := by
  classical
  have hWn : IsSMulRegular W p := by
    simpa only [IsSMulRegular, smul_eq_mul, nsmul_eq_mul] using hW
  have key : ∀ (S : Finset (Idx N)) (hS : S.Nonempty),
      ∃ gS : Γ(X, ⨅ m ∈ S, DSMap.Mix2.chartCover i m) →+* chartRing t S,
        (∀ (l : Idx N) (hl : l ∈ S) (k : Idx N),
            gS (xiSecS i S l hl k) = ⟨chartFrac t S l hl k, chartFrac_mem t S l hl k⟩) ∧
        (gS.comp (DSMap.phiU A X f (⨅ m ∈ S, DSMap.Mix2.chartCover i m)) =
            (algebraMap W (chartRing t S)).comp ψ) := by
    intro S hS
    have hUj : IsAffineOpen (DSMap.Mix2.chartCover i ⟨j⟩) :=
      DSMap.Mix2.chartCover_affine_proved i hi ⟨j⟩
    have hle : (⨅ m ∈ insert (⟨j⟩ : Idx N) S, DSMap.Mix2.chartCover i m)
        ≤ DSMap.Mix2.chartCover i ⟨j⟩ :=
      iInf_chartCover_le_single i (Finset.mem_insert_self (⟨j⟩ : Idx N) S)
    have hSS' : S ⊆ insert (⟨j⟩ : Idx N) S := Finset.subset_insert _ _
    have hV : (⨅ m ∈ insert (⟨j⟩ : Idx N) S, DSMap.Mix2.chartCover i m)
        = X.basicOpen (∏ l ∈ S, DSMap.Mix2.xiSec i j l.down) := by
      rw [Finset.iInf_insert, basicOpen_prod_xiSec]
    letI : Algebra Γ(X, DSMap.Mix2.chartCover i ⟨j⟩)
        Γ(X, ⨅ m ∈ insert (⟨j⟩ : Idx N) S, DSMap.Mix2.chartCover i m) :=
      (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    haveI hloc : IsLocalization.Away (∏ l ∈ S, DSMap.Mix2.xiSec i j l.down)
        Γ(X, ⨅ m ∈ insert (⟨j⟩ : Idx N) S, DSMap.Mix2.chartCover i m) :=
      hUj.isLocalization_of_eq_basicOpen (f := ∏ l ∈ S, DSMap.Mix2.xiSec i j l.down)
        (i := homOfLE hle) hV
    have hg0unit : IsUnit (((Work.DSSEC.cmpOfW p t S).comp θ)
        (∏ l ∈ S, DSMap.Mix2.xiSec i j l.down)) :=
      isUnit_cmpOfW_theta_prod_xiSec_aux i j p θ t ht htθ S
    let ρ : Γ(X, ⨅ m ∈ insert (⟨j⟩ : Idx N) S, DSMap.Mix2.chartCover i m) →+*
        Work.DSSEC.cmpRing p t S :=
      IsLocalization.Away.lift (∏ l ∈ S, DSMap.Mix2.xiSec i j l.down) hg0unit
    have hρ : ∀ x : Γ(X, DSMap.Mix2.chartCover i ⟨j⟩),
        ρ ((X.presheaf.map (homOfLE hle).op).hom x)
          = (Work.DSSEC.cmpOfW p t S) (θ x) := fun x =>
      IsLocalization.Away.lift_eq _ _ x
    have hρj : ∀ m : Idx N,
        ρ (xiSecS i (insert (⟨j⟩ : Idx N) S) ⟨j⟩ (Finset.mem_insert_self _ _) m)
          = (Work.DSSEC.cmpOfW p t S) (θ (DSMap.Mix2.xiSec i j m.down)) := by
      intro m
      exact hρ (DSMap.Mix2.xiSec i j m.down)
    let res : Γ(X, ⨅ m ∈ S, DSMap.Mix2.chartCover i m) →+*
        Γ(X, ⨅ m ∈ insert (⟨j⟩ : Idx N) S, DSMap.Mix2.chartCover i m) :=
      (X.presheaf.map (homOfLE (iInf_chartCover_le i hSS')).op).hom
    have hAeq : ∀ x : Idx N, algebraMap W (Work.DSSEC.cmpRing p t S) (t x)
        = algebraMap W (Work.DSSEC.cmpRing p t S) (t ⟨j⟩) *
          (Work.DSSEC.cmpOfW p t S) (θ (DSMap.Mix2.xiSec i j x.down)) := by
      intro x
      by_cases hx : x.down = j
      · have hx' : x = (⟨j⟩ : Idx N) := by
          cases x with
          | up y => exact ULift.ext hx
        rw [hx']
        simp only [Work.DSCHART.xiSec_self, map_one, mul_one]
      · have h1 := congrArg (Work.DSSEC.cmpOfW p t S) (htθ x.down hx)
        simpa only [map_mul, Work.DSSEC.cmpOfW_eq] using h1
    have hval : ∀ (l : Idx N) (hl : l ∈ S) (k : Idx N),
        ρ (res (xiSecS i S l hl k))
          = Work.DSSEC.chartToCmp p t S ⟨chartFrac t S l hl k, chartFrac_mem t S l hl k⟩ := by
      intro l hl k
      have hres : res (xiSecS i S l hl k) = xiSecS i (insert (⟨j⟩ : Idx N) S) l (hSS' hl) k :=
        xiSecS_restrict i hSS' l hl k
      have h2 : ρ (res (xiSecS i S l hl k)) *
          (Work.DSSEC.cmpOfW p t S) (θ (DSMap.Mix2.xiSec i j l.down)) =
          (Work.DSSEC.cmpOfW p t S) (θ (DSMap.Mix2.xiSec i j k.down)) := by
        have hpair := xiSecS_pair_finset i (insert (⟨j⟩ : Idx N) S) ⟨j⟩ l k
          (Finset.mem_insert_self _ _) (hSS' hl)
        have h3 := congrArg ρ hpair
        simp only [map_mul] at h3
        rw [hρj l, hρj k, ← hres] at h3
        exact h3
      have h4 : ρ (res (xiSecS i S l hl k)) *
          algebraMap W (Work.DSSEC.cmpRing p t S) (t l) =
          algebraMap W (Work.DSSEC.cmpRing p t S) (t k) := by
        rw [hAeq l, hAeq k]
        have h5 : ρ (res (xiSecS i S l hl k)) *
            (algebraMap W (Work.DSSEC.cmpRing p t S) (t ⟨j⟩) *
              (Work.DSSEC.cmpOfW p t S) (θ (DSMap.Mix2.xiSec i j l.down)))
            = algebraMap W (Work.DSSEC.cmpRing p t S) (t ⟨j⟩) *
              (ρ (res (xiSecS i S l hl k)) *
                (Work.DSSEC.cmpOfW p t S) (θ (DSMap.Mix2.xiSec i j l.down))) := by
          ring
        rw [h5, h2]
      exact (Work.DSSEC.isUnit_cmp_t p t S hl).mul_right_cancel
        (h4.trans (Work.DSSEC.chartToCmp_chartFrac p t S l hl k).symm)
    have hphi : ∀ a : A,
        (ρ.comp res) (DSMap.phiU A X f (⨅ m ∈ S, DSMap.Mix2.chartCover i m) a)
          = Work.DSSEC.chartToCmp p t S (algebraMap W (chartRing t S) (ψ a)) := by
      intro a
      have h1 : res (DSMap.phiU A X f (⨅ m ∈ S, DSMap.Mix2.chartCover i m) a)
          = (X.presheaf.map (homOfLE hle).op).hom
              (DSMap.phiU A X f (DSMap.Mix2.chartCover i ⟨j⟩) a) := by
        rw [DSMap.phiU_res A X f (homOfLE (iInf_chartCover_le i hSS')) a,
          DSMap.phiU_res A X f (homOfLE hle) a]
      rw [RingHom.comp_apply, h1, hρ]
      have h2 := congrArg (fun φ : A →+* Localization.Away (p : W) => φ a) hθ
      simp only [RingHom.comp_apply] at h2
      simp only [h2, Work.DSSEC.cmpOfW_eq, chartToCmp_algebraMap]
    let Hpoly : MvPolynomial ({l // l ∈ S} × Idx N) A →+* DSMap.Mix2.chartRing t S :=
      MvPolynomial.eval₂Hom ((algebraMap W (DSMap.Mix2.chartRing t S)).comp ψ)
        (fun q : {l // l ∈ S} × Idx N =>
          ⟨chartFrac t S q.1.1 q.1.2 q.2, chartFrac_mem t S q.1.1 q.1.2 q.2⟩)
    have hHpolyC : ∀ a : A, Hpoly (MvPolynomial.C a)
        = algebraMap W (DSMap.Mix2.chartRing t S) (ψ a) := by
      intro a
      exact MvPolynomial.eval₂Hom_C _ _ a
    have hHpolyX : ∀ q : {l // l ∈ S} × Idx N, Hpoly (MvPolynomial.X q)
        = ⟨chartFrac t S q.1.1 q.1.2 q.2, chartFrac_mem t S q.1.1 q.1.2 q.2⟩ := by
      intro q
      exact MvPolynomial.eval₂Hom_X' _ _ q
    have hH : (Work.DSSEC.chartToCmp p t S).comp Hpoly
        = (ρ.comp res).comp
          (MvPolynomial.eval₂Hom (DSMap.phiU A X f (⨅ m ∈ S, DSMap.Mix2.chartCover i m))
            (fun q : {l // l ∈ S} × Idx N => xiSecS i S q.1.1 q.1.2 q.2)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, hHpolyC]
        rw [← hphi a, RingHom.comp_apply]
      · intro q
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', hHpolyX]
        rw [← hval q.1.1 q.1.2 q.2]
    have hmem : ∀ x : Γ(X, ⨅ m ∈ S, DSMap.Mix2.chartCover i m),
        (ρ.comp res) x ∈ (Work.DSSEC.chartToCmp p t S).range := by
      intro x
      obtain ⟨P, hP⟩ := adjoin_xiSecS_eq_top_self f i hi hif S hS x
      refine ⟨Hpoly P, ?_⟩
      have h2 := congrArg (fun (ψ' : MvPolynomial ({l // l ∈ S} × Idx N) A →+*
          Work.DSSEC.cmpRing p t S) => ψ' P) hH
      simp only [RingHom.comp_apply] at h2
      have hP' : (MvPolynomial.eval₂Hom (DSMap.phiU A X f (⨅ m ∈ S, DSMap.Mix2.chartCover i m))
          (fun q : {l // l ∈ S} × Idx N => xiSecS i S q.1.1 q.1.2 q.2)) P = x := hP
      rw [hP'] at h2
      exact h2
    have hinj : Function.Injective (Work.DSSEC.chartToCmp p t S) :=
      Work.DSSEC.chartToCmp_injective p t hWn S
    let cR : chartRing t S →+* (Work.DSSEC.chartToCmp p t S).range :=
      (Work.DSSEC.chartToCmp p t S).rangeRestrict
    have hbij : Function.Bijective cR :=
      ⟨fun a b h => hinj (congrArg Subtype.val h),
        (Work.DSSEC.chartToCmp p t S).rangeRestrict_surjective⟩
    let e : chartRing t S ≃+* (Work.DSSEC.chartToCmp p t S).range :=
      RingEquiv.ofBijective cR hbij
    let gS : Γ(X, ⨅ m ∈ S, DSMap.Mix2.chartCover i m) →+* chartRing t S :=
      e.symm.toRingHom.comp ((ρ.comp res).codRestrict (Work.DSSEC.chartToCmp p t S).range hmem)
    have hgspec : ∀ x, Work.DSSEC.chartToCmp p t S (gS x) = (ρ.comp res) x := by
      intro x
      set y := (ρ.comp res).codRestrict (Work.DSSEC.chartToCmp p t S).range hmem x with hy
      have h2 : cR (e.symm y) = y := by
        rw [← RingEquiv.ofBijective_apply cR hbij (e.symm y)]
        exact RingEquiv.apply_symm_apply e y
      have h3 := congrArg Subtype.val h2
      rw [RingHom.coe_rangeRestrict] at h3
      show Work.DSSEC.chartToCmp p t S (e.symm y) = (ρ.comp res) x
      rw [h3]
      rfl
    refine ⟨gS, ?_, ?_⟩
    · intro l hl k
      apply hinj
      rw [hgspec, RingHom.comp_apply, hval l hl k]
    · apply RingHom.ext
      intro a
      apply hinj
      rw [RingHom.comp_apply, hgspec, hphi a, RingHom.comp_apply]
  choose g hg using key
  refine ⟨g, fun S hS => (hg S hS).2, ?_⟩
  intro S T hS hST x
  have hT : T.Nonempty := hS.imp fun _ hm => hST hm
  obtain ⟨P, hP⟩ := adjoin_xiSecS_eq_top_self f i hi hif S hS x
  have hP' : (MvPolynomial.eval₂Hom (DSMap.phiU A X f (⨅ m ∈ S, DSMap.Mix2.chartCover i m))
      (fun q : {l // l ∈ S} × Idx N => xiSecS i S q.1.1 q.1.2 q.2)) P = x := hP
  have hcomp : ((g T hT).comp
        ((X.presheaf.map (homOfLE (iInf_chartCover_le i hST)).op).hom)).comp
        (MvPolynomial.eval₂Hom (DSMap.phiU A X f (⨅ m ∈ S, DSMap.Mix2.chartCover i m))
          (fun q : {l // l ∈ S} × Idx N => xiSecS i S q.1.1 q.1.2 q.2))
      = ((chartRes t hST).toRingHom.comp (g S hS)).comp
        (MvPolynomial.eval₂Hom (DSMap.phiU A X f (⨅ m ∈ S, DSMap.Mix2.chartCover i m))
          (fun q : {l // l ∈ S} × Idx N => xiSecS i S q.1.1 q.1.2 q.2)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have h1 := RingHom.congr_fun (hg T hT).2 a
      simp only [RingHom.comp_apply] at h1
      have h2 := RingHom.congr_fun (hg S hS).2 a
      simp only [RingHom.comp_apply] at h2
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      rw [DSMap.phiU_res A X f (homOfLE (iInf_chartCover_le i hST)) a, h1, h2]
      exact ((chartRes t hST).commutes (ψ a)).symm
    · intro q
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      rw [xiSecS_restrict i hST q.1.1 q.1.2 q.2]
      rw [(hg T hT).1 q.1.1 (hST q.1.2) q.2, (hg S hS).1 q.1.1 q.1.2 q.2]
      apply Subtype.ext
      show chartFrac t T q.1.1 (hST q.1.2) q.2
        = DSMap.Mix2.locRes t hST (chartFrac t S q.1.1 q.1.2 q.2)
      exact (chartFrac_locRes t hST q.1.1 q.1.2 q.2).symm
  have hfin := congrArg (fun φ => φ P) hcomp
  simp only [RingHom.comp_apply] at hfin
  rw [hP'] at hfin
  exact hfin


end XSide

end Work.DSSEC
