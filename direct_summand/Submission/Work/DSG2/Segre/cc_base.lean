import Mathlib
import Submission.Work.DSG2.Segre.Basic
import Submission.Work.DSG2.Segre.projChart_relation
import Submission.Work.DSG2.Segre.chartElemAll_surjective
import Submission.Work.DSG2.Segre.Triangle
import Submission.Work.DSG4c.ChartPushout.chartToPoly_surjective

/-!
# `Work.DSG2.Segre.charts_compat`

The chart-wise Segre maps `sigma k` for the two product charts `V k`, `V k'` agree on the
intersection `V k ∩ V k'` of the charts (the pullback of the two open inclusions).  This is the
compatibility needed to glue the `sigma k` into a single morphism `ℙ^a × ℙ^b ⟶ ℙ^N`.
-/

namespace Work.DSG2.Segre

universe u

open CategoryTheory AlgebraicGeometry Limits MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## The ring map associated with a morphism into an affine scheme

For `f : X ⟶ Spec R` we use `cc_rr R f : R →+* Γ(X, ⊤)`, the induced map on global sections
(composed with the canonical identification `R ≅ Γ(Spec R, ⊤)`).  It determines `f`
(`cc_rr_ext`) and is well behaved under composition and under `Spec.map`. -/

/-- The ring map `R →+* Γ(X, ⊤)` associated with `f : X ⟶ Spec R`. -/
noncomputable def cc_rr (X : Scheme.{u}) (R : Type u) [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom

lemma cc_rr_comp {X Y : Scheme.{u}} {R : Type u} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) (h : Y ⟶ X) :
    cc_rr Y R (h ≫ f) = (h.appTop).hom.comp (cc_rr X R f) := by
  rw [cc_rr, cc_rr, Scheme.Hom.comp_appTop]
  rfl

lemma cc_rr_ext {X : Scheme.{u}} {R : Type u} [CommRing R]
    {f g : X ⟶ Spec (CommRingCat.of R)} (h : cc_rr X R f = cc_rr X R g) : f = g := by
  refine AlgebraicGeometry.ext_to_Spec (CommRingCat.hom_ext ?_)
  simp only [Scheme.Γ_map_op]
  exact h

lemma cc_rr_specMap {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    cc_rr (Spec (CommRingCat.of S)) R (Spec.map (CommRingCat.ofHom φ)) =
      (((Scheme.ΓSpecIso (CommRingCat.of S)).inv).hom).comp φ := by
  rw [cc_rr, ← Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)]
  rfl

/-- `cc_rr` of a composite `h ≫ Spec.map φ` is `(cc_rr h).comp φ`. -/
lemma cc_rr_comp_specMap {Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (h : Y ⟶ Spec (CommRingCat.of S)) (φ : R →+* S) :
    cc_rr Y R (h ≫ Spec.map (CommRingCat.ofHom φ)) = (cc_rr Y S h).comp φ := by
  rw [cc_rr_comp, cc_rr_specMap, cc_rr]
  rfl

/-- `cc_rr` is compatible with the `A`-algebra structures when `f` is a morphism over
`Spec A`. -/
lemma cc_rr_algebraMap {X : Scheme.{u}} {A : Type u} [CommRing A] {R : Type u} [CommRing R]
    [Algebra A R] {f : X ⟶ Spec (CommRingCat.of R)} {g : X ⟶ Spec (CommRingCat.of A)}
    (h : f ≫ Spec.map (CommRingCat.ofHom (algebraMap A R)) = g) :
    (cc_rr X R f).comp (algebraMap A R) = cc_rr X A g := by
  ext a
  show (f.appTop).hom (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom (algebraMap A R a)) =
    (g.appTop).hom (((Scheme.ΓSpecIso (CommRingCat.of A)).inv).hom a)
  have h1 : (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom (algebraMap A R a)) =
      (Spec.map (CommRingCat.ofHom (algebraMap A R))).appTop.hom
        (((Scheme.ΓSpecIso (CommRingCat.of A)).inv).hom a) :=
    congrArg (fun (x : CommRingCat.of A ⟶ Γ(Spec (CommRingCat.of R), ⊤)) => x.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A R)))
  rw [h1]
  have h2 : (f.appTop).hom.comp
      (Spec.map (CommRingCat.ofHom (algebraMap A R))).appTop.hom = (g.appTop).hom := by
    rw [← h, Scheme.Hom.comp_appTop]
    rfl
  rw [← RingHom.comp_apply, h2]

/-- `Proj.awayι` only depends on the homogeneous element, not on the proofs of homogeneity and
of positivity of the degree. -/
lemma cc_awayι_congr {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜] {f : A} {m : ℕ} (hf hf' : f ∈ 𝒜 m)
    (hm hm' : 0 < m) :
    (Proj.awayι 𝒜 f hf hm : Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f)) ⟶
      Proj 𝒜) = Proj.awayι 𝒜 f hf' hm' := by
  rw [Subsingleton.elim hf hf', Subsingleton.elim hm hm']

/-! ## Chart inclusions and the chart-wise Segre maps -/

/-- The product chart inclusion followed by the second projection is the second chart
inclusion. -/
@[reassoc]
lemma cc_chartIncl_snd (A : Type u) [CommRing A] (a b : ℕ) (k : Fin (a+1) × Fin (b+1)) :
    chartIncl A a b k.1 k.2 ≫
        pullback.snd (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A)
        (A := chartRingA A a k.1) (B := chartRingB A b k.2)).toRingHom) ≫
        Work.DSG4c.chartι A b k.2 := by
  simp only [chartIncl]
  rw [Category.assoc, pullback.map, pullback.lift_snd, ← Category.assoc, pullbackSpecIso_inv_snd]
  rfl

/-- The value of the Segre chart ring map on a chart coordinate. -/
lemma cc_segreChart_chartElem (A : Type u) [CommRing A] (a b : ℕ)
    (k : Fin (a+1) × Fin (b+1))
    (j : Work.DSG4c.ChartPushout.chartIdx (segreN a b) (toIdx a b k)) :
    segreChart A a b k (Work.DSG4c.ChartPushout.chartElem A (segreN a b) (toIdx a b k) j) =
      segreElemA A a k.1 ((toIdx a b).symm j.1).1 ⊗ₜ[A]
        segreElemB A b k.2 ((toIdx a b).symm j.1).2 := by
  rw [segreChart, RingHom.comp_apply, Work.DSG4c.ChartPushout.polyToChart_chartElem]
  exact MvPolynomial.aeval_X _ j

/-- The value of the Segre chart ring map on a chart coordinate, in the "all coordinates"
formulation. -/
lemma cc_segreChart_chartElemAll (A : Type u) [CommRing A] (a b : ℕ)
    (k : Fin (a+1) × Fin (b+1)) (m : Fin (segreN a b + 1)) :
    segreChart A a b k
        (Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k) m) =
      segreElemA A a k.1 ((toIdx a b).symm m).1 ⊗ₜ[A]
        segreElemB A b k.2 ((toIdx a b).symm m).2 := by
  by_cases hm : m = toIdx a b k
  · subst hm
    rw [Work.DSG4c.ChartPushout.chartElemAll_self, map_one, Equiv.symm_apply_apply]
    simp only [segreElemA, segreElemB, Work.DSG4c.ChartPushout.chartElemAll_self]
    exact Algebra.TensorProduct.one_def
  · exact ((Work.DSG4c.ChartPushout.chartElem_eq_chartElemAll A (segreN a b) (toIdx a b k)
      ⟨m, hm⟩).symm ▸ cc_segreChart_chartElem A a b k ⟨m, hm⟩)

/-- `Away.isLocalizationElem` is the chart coordinate. -/
lemma cc_isLocalizationElem_chartElemAll (A : Type u) [CommRing A] (n : ℕ)
    (i i' : Fin (n+1)) :
    HomogeneousLocalization.Away.isLocalizationElem (Work.DSG4c.X_mem A n i)
        (Work.DSG4c.X_mem A n i') = Work.DSG4c.ChartPushout.chartElemAll A n i i' := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (MvPolynomial.X (R := A) i))
  rw [HomogeneousLocalization.Away.isLocalizationElem, Work.DSG4c.ChartPushout.chartElemAll,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk]
  simp [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_iff_eq_mul]

/-- The pullback of the `j`-th coordinate chart of `ℙⁿ` along the `i`-th chart inclusion. -/
lemma cc_chartι_preimage (A : Type u) [CommRing A] (n : ℕ) (i j : Fin (n+1)) :
    Work.DSG4c.chartι A n i ⁻¹ᵁ Proj.basicOpen (DSMap.PGr A n) (MvPolynomial.X j) =
      PrimeSpectrum.basicOpen (Work.DSG4c.ChartPushout.chartElemAll A n i j) := by
  simpa only [Work.DSG4c.chartι, cc_isLocalizationElem_chartElemAll A n i j] using
    Proj.awayι_preimage_basicOpen (DSMap.PGr A n) (Work.DSG4c.X_mem A n i) one_pos
      (Work.DSG4c.X_mem A n j) one_pos

/-- The preimage of a basic open of an affine scheme under `Spec.map`. -/
lemma cc_specMap_preimage_basicOpen {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (x : R) :
    Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ PrimeSpectrum.basicOpen x =
      PrimeSpectrum.basicOpen (φ x) :=
  rfl

/-- The product chart inclusion composed with the structure map is the structure map of the `k`-th
chart ring. -/
lemma cc_chartIncl_toSpec (A : Type u) [CommRing A] (a b : ℕ) (k : Fin (a+1) × Fin (b+1)) :
    chartIncl A a b k.1 k.2 ≫
        pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) ≫
          DSMap.PSpace.toSpec A a =
      Spec.map (CommRingCat.ofHom (algebraMap A (chartRing A a b k))) := by
  rw [← Category.assoc, chartIncl_fst, Category.assoc, Work.DSG4c.chartι_comp_toSpec,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← awayChart_algebraMap A a k.1]

/-- The structure map of the first chart is the structure map of the `k`-th chart ring. -/
lemma cc_chartIso_inv_toSpec (A : Type u) [CommRing A] (a b : ℕ) (k : Fin (a+1) × Fin (b+1)) :
    (chartIso A a b k).inv ≫ Spec.map (CommRingCat.ofHom (algebraMap A (chartRing A a b k))) =
      (V A a b k).ι ≫ pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) ≫
        DSMap.PSpace.toSpec A a := by
  apply (cancel_epi (chartIso A a b k).hom).mp
  rw [Iso.hom_inv_id_assoc, chartIso_hom_ι_assoc, cc_chartIncl_toSpec]

/-- The pullback of the `k'`-chart along the `k`-chart inclusion is the basic open of the product
coordinate. -/
lemma cc_chartIncl_preimage (A : Type u) [CommRing A] (a b : ℕ)
    (k k' : Fin (a+1) × Fin (b+1)) :
    chartIncl A a b k.1 k.2 ⁻¹ᵁ (V A a b k') =
      PrimeSpectrum.basicOpen (Work.DSG4c.ChartPushout.chartElemAll A a k.1 k'.1 ⊗ₜ[A]
        Work.DSG4c.ChartPushout.chartElemAll A b k.2 k'.2) := by
  have hleft (x : chartRingA A a k.1) :
      algebraMap (chartRingA A a k.1) (chartRing A a b k) x = x ⊗ₜ[A] 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  have hright (y : chartRingB A b k.2) :
      (Algebra.TensorProduct.includeRight (R := A) (A := chartRingA A a k.1)
        (B := chartRingB A b k.2)).toRingHom y = 1 ⊗ₜ[A] y :=
    Algebra.TensorProduct.includeRight_apply y
  rw [V, Scheme.Hom.preimage_inf]
  rw [← Scheme.Hom.comp_preimage, chartIncl_fst, ← Scheme.Hom.comp_preimage,
    cc_chartIncl_snd A a b k]
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  rw [cc_chartι_preimage, cc_chartι_preimage, cc_specMap_preimage_basicOpen,
    cc_specMap_preimage_basicOpen]
  rw [hleft, hright]
  show PrimeSpectrum.basicOpen (Work.DSG4c.ChartPushout.chartElemAll A a k.1 k'.1 ⊗ₜ[A] 1) ⊓
      PrimeSpectrum.basicOpen (1 ⊗ₜ[A] Work.DSG4c.ChartPushout.chartElemAll A b k.2 k'.2) =
    PrimeSpectrum.basicOpen (Work.DSG4c.ChartPushout.chartElemAll A a k.1 k'.1 ⊗ₜ[A]
      Work.DSG4c.ChartPushout.chartElemAll A b k.2 k'.2)
  rw [← PrimeSpectrum.basicOpen_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-! ## The data attached to the two charts -/


end Work.DSG2.Segre
