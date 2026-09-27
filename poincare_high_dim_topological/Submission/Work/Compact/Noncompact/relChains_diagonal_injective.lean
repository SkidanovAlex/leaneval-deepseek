import Mathlib
import Submission.Work.Cohomology.excision
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.exists_small_homotopy
import Submission.Work.Cohomology.cokerSmallLemmas
import Submission.Work.Cohomology.mv_shortExact
import Submission.Work.Cohomology.smallChains_homology_iso_int
import Submission.Work.Cohomology.exists_delta_affineSimplex
import Submission.Work.Cohomology.exists_iter_small
import Submission.Work.Cohomology.smallLift_cov
import Submission.Work.Compact.Noncompact.Basic
import Submission.Work.Compact.Noncompact.relMVDefs
import Submission.Work.Compact.Noncompact.rSupp_inf_eq

/-!
# Injectivity of the Mayer–Vietoris diagonal for relative chains

For `U, V ⊆ X` (open) the *relative Mayer–Vietoris* sequence of the pair `(X, U ∩ V)` is

`⋯ ⟶ Hₙ(X, U ∪ V) ⟶ Hₙ(X, U) ⊕ Hₙ(X, V) ⟶ Hₙ(X, U ∩ V) ⟶ Hₙ₋₁(X, U ∪ V) ⟶ ⋯`

so that the diagonal map `H_{k+1}(X, U ∩ V) ⟶ H_{k+1}(X, U) ⊕ H_{k+1}(X, V)` is injective as soon as
`H_{k+2}(X, U ∪ V) = 0`.  This is the form of Mayer–Vietoris exactness used in the proof of
Hatcher's Lemma 3.27 / Proposition 3.29 (local homology detects top classes).

The short exact sequence of chain complexes underlying the statement is

`0 ⟶ C_*(X)/C_*(U ∩ V) ⟶ C_*(X)/C_*(U) ⊞ C_*(X)/C_*(V) ⟶ C_*(X)/C^{U,V}_*(X) ⟶ 0`,

where `C^{U,V}_*(X) ⊆ C_*(X)` is the subcomplex of small chains (`Work.Cohomology.smallChains`).
The last term computes the relative chains of `(X, U ∪ V)` (the small-simplices theorem), which is
the statement `Work.Compact.Noncompact.isZero_homology_cokernel_smallToSing`.

## Main results

* `relMVShort`, `relMVShort_shortExact` — the relative Mayer–Vietoris short exact sequence;
* `relChains_diagonal_injective` — the injectivity of the diagonal.
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace Work.Compact.Noncompact

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Work.Cohomology
open scoped Simplicial

noncomputable section

variable {X : TopCat}

/-! ## Notation -/

/-- The relative chains of the pair `(X, S)`. -/
abbrev relCX (S : Set X) : ChainComplex (ModuleCat ℤ) ℕ := Work.Cohomology.relChains X S

/-- The biproduct `C_*(X)/C_*(U) ⊞ C_*(X)/C_*(V)`. -/
abbrev relProd (U V : Set X) : ChainComplex (ModuleCat ℤ) ℕ := relCX (X := X) U ⊞ relCX (X := X) V

/-- The cokernel of the inclusion of the small chains: `C_*(X)/C^{U,V}_*(X)`. -/
abbrev relQ (U V : Set X) : ChainComplex (ModuleCat ℤ) ℕ := cokernel (Work.Cohomology.smallToSing U V)

/-! ## The three maps of the relative Mayer–Vietoris sequence -/

/-- The first map: `C_*(X)/C_*(U∩V) ⟶ C_*(X)/C_*(U)`, induced by `U ∩ V ⊆ U`. -/
abbrev relMVLeft (U V : Set X) : relCX (X := X) (U ∩ V) ⟶ relCX (X := X) U :=
  relMap (X := X) (Set.inter_subset_left : U ∩ V ⊆ U)

/-- The first map, second component: `C_*(X)/C_*(U∩V) ⟶ C_*(X)/C_*(V)`. -/
abbrev relMVRightMap (U V : Set X) : relCX (X := X) (U ∩ V) ⟶ relCX (X := X) V :=
  relMap (X := X) (Set.inter_subset_right : U ∩ V ⊆ V)

/-- The diagonal `C_*(X)/C_*(U∩V) ⟶ C_*(X)/C_*(U) ⊞ C_*(X)/C_*(V)`. -/
abbrev relMVMap (U V : Set X) : relCX (X := X) (U ∩ V) ⟶ relProd (X := X) U V :=
  biprod.lift (relMVLeft U V) (relMVRightMap U V)

/-- The canonical map `C_*(X)/C_*(U) ⟶ coker(smallToSing U V)`. -/
abbrev relCokerMapU (U V : Set X) : relCX (X := X) U ⟶ relQ (X := X) U V :=
  cokernel.map (Work.Cohomology.inclChains X U) (Work.Cohomology.smallToSing U V)
    (Work.Cohomology.smallOfU U V) (𝟙 (Work.Cohomology.singularChains ℤ X))
    (by rw [Category.comp_id, Work.Cohomology.smallOfU_comp_smallToSing])

/-- The canonical map `C_*(X)/C_*(V) ⟶ coker(smallToSing U V)`. -/
abbrev relCokerMapV (U V : Set X) : relCX (X := X) V ⟶ relQ (X := X) U V :=
  cokernel.map (Work.Cohomology.inclChains X V) (Work.Cohomology.smallToSing U V)
    (Work.Cohomology.smallOfV U V) (𝟙 (Work.Cohomology.singularChains ℤ X))
    (by rw [Category.comp_id, Work.Cohomology.smallOfV_comp_smallToSing])

/-- The difference map `C_*(X)/C_*(U) ⊞ C_*(X)/C_*(V) ⟶ coker(smallToSing U V)`. -/
abbrev relCokerMap (U V : Set X) : relProd (X := X) U V ⟶ relQ (X := X) U V :=
  biprod.desc (relCokerMapU U V) (-(relCokerMapV U V))

/-! ## The compatibility of the maps -/

lemma cokernel_π_relCokerMapU (U V : Set X) :
    cokernel.π (Work.Cohomology.inclChains X U) ≫ relCokerMapU U V
      = 𝟙 (Work.Cohomology.singularChains ℤ X) ≫
        cokernel.π (Work.Cohomology.smallToSing U V) :=
  Work.Cohomology.cokernel_π_map _ _ _ _ _

lemma cokernel_π_relCokerMapV (U V : Set X) :
    cokernel.π (Work.Cohomology.inclChains X V) ≫ relCokerMapV U V
      = 𝟙 (Work.Cohomology.singularChains ℤ X) ≫
        cokernel.π (Work.Cohomology.smallToSing U V) :=
  Work.Cohomology.cokernel_π_map _ _ _ _ _

/-- The diagonal and the difference map are compatible with the canonical projections. -/
lemma relMVLeft_comp_relCokerMapU (U V : Set X) :
    relMVLeft U V ≫ relCokerMapU U V = relMVRightMap U V ≫ relCokerMapV U V := by
  have hA : cokernel.π (Work.Cohomology.inclChains X (U ∩ V)) ≫
      (relMVLeft U V ≫ relCokerMapU U V) = cokernel.π (Work.Cohomology.smallToSing U V) := by
    rw [← Category.assoc, cokernel_π_relMap, Category.id_comp, cokernel_π_relCokerMapU,
      Category.id_comp]
  have hB : cokernel.π (Work.Cohomology.inclChains X (U ∩ V)) ≫
      (relMVRightMap U V ≫ relCokerMapV U V) = cokernel.π (Work.Cohomology.smallToSing U V) := by
    rw [← Category.assoc, cokernel_π_relMap, Category.id_comp, cokernel_π_relCokerMapV,
      Category.id_comp]
  exact (cancel_epi (cokernel.π (Work.Cohomology.inclChains X (U ∩ V)))).1 (hA.trans hB.symm)

/-- The composite of the diagonal with the difference map is zero. -/
lemma relCokerMap_comp_relMVMap (U V : Set X) :
    relMVMap U V ≫ relCokerMap U V = 0 := by
  have h1 := relMVLeft_comp_relCokerMapU U V
  rw [relMVMap, relCokerMap, biprod.lift_desc, Preadditive.comp_neg, h1, add_neg_cancel]

/-- **The relative Mayer–Vietoris short complex** of the pair `(U, V)`. -/
def relMVShort (U V : Set X) : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (relMVMap U V) (relCokerMap U V) (relCokerMap_comp_relMVMap U V)

/-! ## Elementary consequences of the projection identities -/

/-- An element of the cokernel of a chain map lifts to the total complex. -/
lemma exists_cokernel_π_f_eq {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) (n : ℕ)
    (z : (cokernel φ).X n) : ∃ y : L.X n, ((cokernel.π φ).f n) y = z :=
  (ModuleCat.epi_iff_surjective ((cokernel.π φ).f n)).1 inferInstance z

/-- The `fst`-component of `relCokerMapU`. -/
lemma cokernel_π_inclChains_comp_relCokerMapU (U V : Set X) (n : ℕ) :
    (cokernel.π (Work.Cohomology.inclChains X U)).f n ≫ (relCokerMapU U V).f n
      = (cokernel.π (Work.Cohomology.smallToSing U V)).f n := by
  have h := HomologicalComplex.comp_f (cokernel.π (Work.Cohomology.inclChains X U))
    (relCokerMapU U V) n
  rw [cokernel_π_relCokerMapU U V] at h
  simpa only [Category.id_comp, HomologicalComplex.id_f, ModuleCat.hom_id,
    LinearMap.id_comp] using h.symm

lemma cokernel_π_inclChains_comp_relCokerMapV (U V : Set X) (n : ℕ) :
    (cokernel.π (Work.Cohomology.inclChains X V)).f n ≫ (relCokerMapV U V).f n
      = (cokernel.π (Work.Cohomology.smallToSing U V)).f n := by
  have h := HomologicalComplex.comp_f (cokernel.π (Work.Cohomology.inclChains X V))
    (relCokerMapV U V) n
  rw [cokernel_π_relCokerMapV U V] at h
  simpa only [Category.id_comp, HomologicalComplex.id_f, ModuleCat.hom_id,
    LinearMap.id_comp] using h.symm

/-- The `fst`-component of `relMVLeft`. -/
lemma cokernel_π_inclChains_comp_relMVLeft (U V : Set X) (n : ℕ) :
    (cokernel.π (Work.Cohomology.inclChains X (U ∩ V))).f n ≫ (relMVLeft U V).f n
      = (cokernel.π (Work.Cohomology.inclChains X U)).f n := by
  have h := HomologicalComplex.comp_f (cokernel.π (Work.Cohomology.inclChains X (U ∩ V)))
    (relMVLeft U V) n
  rw [cokernel_π_relMap (X := X) (Set.inter_subset_left : U ∩ V ⊆ U)] at h
  simpa only [Category.id_comp, HomologicalComplex.id_f, ModuleCat.hom_id,
    LinearMap.id_comp] using h.symm

lemma cokernel_π_inclChains_comp_relMVRightMap (U V : Set X) (n : ℕ) :
    (cokernel.π (Work.Cohomology.inclChains X (U ∩ V))).f n ≫ (relMVRightMap U V).f n
      = (cokernel.π (Work.Cohomology.inclChains X V)).f n := by
  have h := HomologicalComplex.comp_f (cokernel.π (Work.Cohomology.inclChains X (U ∩ V)))
    (relMVRightMap U V) n
  rw [cokernel_π_relMap (X := X) (Set.inter_subset_right : U ∩ V ⊆ V)] at h
  simpa only [Category.id_comp, HomologicalComplex.id_f, ModuleCat.hom_id,
    LinearMap.id_comp] using h.symm

/-! ## The degreewise short exactness -/

/-- The degreewise components of the relative Mayer–Vietoris short complex. -/
abbrev relMVShortEval (U V : Set X) (n : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk ((relMVMap U V).f n) ((relCokerMap U V).f n) (by
    rw [← HomologicalComplex.comp_f, relCokerMap_comp_relMVMap, HomologicalComplex.zero_f])

/-- The `inl`-component of `relCokerMap`, evaluated. -/
lemma relCokerMap_apply_inl (U V : Set X) (n : ℕ) (a : (relCX (X := X) U).X n) :
    ((relCokerMap U V).f n) (((biprod.inl : relCX (X := X) U ⟶ relProd (X := X) U V).f n) a)
      = ((relCokerMapU U V).f n) a := by
  rw [← ModuleCat.comp_apply,
    HomologicalComplex.biprod_inl_desc_f (relCokerMapU U V) (-(relCokerMapV U V)) n]

/-- The `inr`-component of `relCokerMap`, evaluated. -/
lemma relCokerMap_apply_inr (U V : Set X) (n : ℕ) (b : (relCX (X := X) V).X n) :
    ((relCokerMap U V).f n) (((biprod.inr : relCX (X := X) V ⟶ relProd (X := X) U V).f n) b)
      = ((-(relCokerMapV U V)).f n) b := by
  rw [← ModuleCat.comp_apply,
    HomologicalComplex.biprod_inr_desc_f (relCokerMapU U V) (-(relCokerMapV U V)) n]

/-- The `fst`-projection of `relMVMap`, evaluated. -/
lemma fst_relMVMap_apply (U V : Set X) (n : ℕ) (y : (relCX (X := X) (U ∩ V)).X n) :
    ((biprod.fst : relProd (X := X) U V ⟶ relCX (X := X) U).f n) (((relMVMap U V).f n) y)
      = ((relMVLeft U V).f n) y := by
  rw [← ModuleCat.comp_apply,
    HomologicalComplex.biprod_lift_fst_f (relMVLeft U V) (relMVRightMap U V) n]

/-- The `snd`-projection of `relMVMap`, evaluated. -/
lemma snd_relMVMap_apply (U V : Set X) (n : ℕ) (y : (relCX (X := X) (U ∩ V)).X n) :
    ((biprod.snd : relProd (X := X) U V ⟶ relCX (X := X) V).f n) (((relMVMap U V).f n) y)
      = ((relMVRightMap U V).f n) y := by
  rw [← ModuleCat.comp_apply,
    HomologicalComplex.biprod_lift_snd_f (relMVLeft U V) (relMVRightMap U V) n]

/-- **The kernel of the diagonal is zero, degreewise**: a chain whose image vanishes in both
`C_*(X)/C_*(U)` and `C_*(X)/C_*(V)` is supported in `U ∩ V`. -/
lemma relMVMap_f_eq_zero (U V : Set X) (n : ℕ) {x : (relCX (X := X) (U ∩ V)).X n}
    (hx : ((relMVMap U V).f n) x = 0) : x = 0 := by
  obtain ⟨ζ, hζ⟩ := exists_cokernel_π_f_eq (Work.Cohomology.inclChains X (U ∩ V)) n x
  have hfst : ((relMVLeft U V).f n) x = 0 := by
    rw [← fst_relMVMap_apply U V n x, hx, map_zero]
  have hsnd : ((relMVRightMap U V).f n) x = 0 := by
    rw [← snd_relMVMap_apply U V n x, hx, map_zero]
  have hζU : ((cokernel.π (Work.Cohomology.inclChains X U)).f n) ζ = 0 := by
    rw [← cokernel_π_inclChains_comp_relMVLeft U V n, ModuleCat.comp_apply, hζ]
    exact hfst
  have hζV : ((cokernel.π (Work.Cohomology.inclChains X V)).f n) ζ = 0 := by
    rw [← cokernel_π_inclChains_comp_relMVRightMap U V n, ModuleCat.comp_apply, hζ]
    exact hsnd
  have hmemU : ζ ∈ rSupp X U n := by
    show ζ ∈ LinearMap.range (((Work.Cohomology.inclChains X U).f n).hom)
    rw [LinearMap.mem_range]
    exact (Work.Cohomology.cokernel_pi_f_eq_zero_iff (Work.Cohomology.inclChains X U) n ζ).1 hζU
  have hmemV : ζ ∈ rSupp X V n := by
    show ζ ∈ LinearMap.range (((Work.Cohomology.inclChains X V).f n).hom)
    rw [LinearMap.mem_range]
    exact (Work.Cohomology.cokernel_pi_f_eq_zero_iff (Work.Cohomology.inclChains X V) n ζ).1 hζV
  have hmemA : ζ ∈ rSupp X (U ∩ V) n := by
    rw [← rSupp_inf_eq U V n]
    exact ⟨hmemU, hmemV⟩
  have hzero : ((cokernel.π (Work.Cohomology.inclChains X (U ∩ V))).f n) ζ = 0 :=
    (Work.Cohomology.cokernel_pi_f_eq_zero_iff (Work.Cohomology.inclChains X (U ∩ V)) n ζ).2
      (by
        show ζ ∈ LinearMap.range (((Work.Cohomology.inclChains X (U ∩ V)).f n).hom)
        rw [LinearMap.mem_range]
        exact LinearMap.mem_range.mp hmemA)
  rw [← hζ, hzero]

/-- **The relative Mayer–Vietoris short complex is short exact, degreewise.** -/
lemma relMVShortEval_shortExact (U V : Set X) (n : ℕ) : (relMVShortEval U V n).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    have hxw := Work.Cohomology.biprodX_total_apply (K := relCX (X := X) U)
      (L := relCX (X := X) V) x₂
    set a : (relCX (X := X) U).X n := ((biprod.fst : relProd (X := X) U V ⟶ relCX (X := X) U).f n) x₂
      with ha
    set b : (relCX (X := X) V).X n := ((biprod.snd : relProd (X := X) U V ⟶ relCX (X := X) V).f n) x₂
      with hb
    have hx : x₂ = ((biprod.inl : relCX (X := X) U ⟶ relProd (X := X) U V).f n) a
        + ((biprod.inr : relCX (X := X) V ⟶ relProd (X := X) U V).f n) b := hxw.symm
    have hcomp : ((relCokerMapU U V).f n) a = ((relCokerMapV U V).f n) b := by
      have h0 : ((relCokerMapU U V).f n) a + ((-(relCokerMapV U V)).f n) b = 0 := by
        rw [← relCokerMap_apply_inl U V n a, ← relCokerMap_apply_inr U V n b, ← map_add, ← hx]
        exact hx₂
      have hneg : ((-(relCokerMapV U V)).f n) b = -(((relCokerMapV U V).f n) b) := by
        rw [HomologicalComplex.neg_f_apply]
        rfl
      rw [hneg] at h0
      exact add_neg_eq_zero.mp h0
    obtain ⟨abar, habar⟩ := exists_cokernel_π_f_eq (Work.Cohomology.inclChains X U) n a
    obtain ⟨bbar, hbbar⟩ := exists_cokernel_π_f_eq (Work.Cohomology.inclChains X V) n b
    have hQabar : ((cokernel.π (Work.Cohomology.smallToSing U V)).f n) abar
        = ((relCokerMapU U V).f n) a := by
      calc ((cokernel.π (Work.Cohomology.smallToSing U V)).f n) abar
          = (((cokernel.π (Work.Cohomology.inclChains X U)).f n)
              ≫ (relCokerMapU U V).f n) abar := by
            rw [cokernel_π_inclChains_comp_relCokerMapU]
        _ = ((relCokerMapU U V).f n)
              (((cokernel.π (Work.Cohomology.inclChains X U)).f n) abar) :=
            ModuleCat.comp_apply _ _ _
        _ = ((relCokerMapU U V).f n) a := by rw [habar]
    have hQbbar : ((cokernel.π (Work.Cohomology.smallToSing U V)).f n) bbar
        = ((relCokerMapV U V).f n) b := by
      calc ((cokernel.π (Work.Cohomology.smallToSing U V)).f n) bbar
          = (((cokernel.π (Work.Cohomology.inclChains X V)).f n)
              ≫ (relCokerMapV U V).f n) bbar := by
            rw [cokernel_π_inclChains_comp_relCokerMapV]
        _ = ((relCokerMapV U V).f n)
              (((cokernel.π (Work.Cohomology.inclChains X V)).f n) bbar) :=
            ModuleCat.comp_apply _ _ _
        _ = ((relCokerMapV U V).f n) b := by rw [hbbar]
    have hdiff : ((cokernel.π (Work.Cohomology.smallToSing U V)).f n) (abar - bbar) = 0 := by
      rw [map_sub, hQabar, hQbbar, hcomp, sub_self]
    obtain ⟨c, hc⟩ := (Work.Cohomology.cokernel_pi_f_eq_zero_iff
      (Work.Cohomology.smallToSing U V) n (abar - bbar)).1 hdiff
    obtain ⟨p, q, hpq⟩ := Work.Cohomology.exists_smallOfU_sub_smallOfV U V n c
    have hu : ((Work.Cohomology.smallToSing U V).f n) (((Work.Cohomology.smallOfU U V).f n) p)
        = ((Work.Cohomology.inclChains X U).f n) p := by
      rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
        Work.Cohomology.smallOfU_comp_smallToSing]
    have hv : ((Work.Cohomology.smallToSing U V).f n) (((Work.Cohomology.smallOfV U V).f n) q)
        = ((Work.Cohomology.inclChains X V).f n) q := by
      rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f,
        Work.Cohomology.smallOfV_comp_smallToSing]
    have hpq' : ((Work.Cohomology.inclChains X U).f n) p - ((Work.Cohomology.inclChains X V).f n) q
        = abar - bbar := by
      rw [← hc, ← hpq, map_sub, hu, hv]
    set ζ : (Work.Cohomology.singularChains ℤ X).X n :=
      abar - ((Work.Cohomology.inclChains X U).f n) p with hζ
    have hζV : ζ = bbar - ((Work.Cohomology.inclChains X V).f n) q := by
      have h1 : (abar - ((Work.Cohomology.inclChains X U).f n) p)
          - (bbar - ((Work.Cohomology.inclChains X V).f n) q)
          = (abar - bbar) - (((Work.Cohomology.inclChains X U).f n) p
            - ((Work.Cohomology.inclChains X V).f n) q) := by abel
      have h2 : (abar - ((Work.Cohomology.inclChains X U).f n) p)
          - (bbar - ((Work.Cohomology.inclChains X V).f n) q) = 0 := by
        rw [h1, hpq', sub_self]
      exact sub_eq_zero.mp h2
    have hfstζ : ((cokernel.π (Work.Cohomology.inclChains X U)).f n) ζ = a := by
      rw [hζ, map_sub, habar]
      have hzero : ((cokernel.π (Work.Cohomology.inclChains X U)).f n)
          (((Work.Cohomology.inclChains X U).f n) p) = 0 :=
        (Work.Cohomology.cokernel_pi_f_eq_zero_iff (Work.Cohomology.inclChains X U) n _).2 ⟨p, rfl⟩
      rw [hzero, sub_zero]
    have hsndζ : ((cokernel.π (Work.Cohomology.inclChains X V)).f n) ζ = b := by
      rw [hζV, map_sub, hbbar]
      have hzero : ((cokernel.π (Work.Cohomology.inclChains X V)).f n)
          (((Work.Cohomology.inclChains X V).f n) q) = 0 :=
        (Work.Cohomology.cokernel_pi_f_eq_zero_iff (Work.Cohomology.inclChains X V) n _).2 ⟨q, rfl⟩
      rw [hzero, sub_zero]
    refine ⟨((cokernel.π (Work.Cohomology.inclChains X (U ∩ V))).f n) ζ, ?_⟩
    refine Work.Cohomology.biprodX_ext_apply ?_ ?_
    · calc ConcreteCategory.hom ((biprod.fst : relProd (X := X) U V ⟶ relCX (X := X) U).f n)
            (ConcreteCategory.hom ((relMVMap U V).f n)
              (ConcreteCategory.hom ((cokernel.π (Work.Cohomology.inclChains X (U ∩ V))).f n) ζ))
          = ConcreteCategory.hom ((relMVLeft U V).f n)
              (ConcreteCategory.hom ((cokernel.π (Work.Cohomology.inclChains X (U ∩ V))).f n) ζ) :=
            fst_relMVMap_apply U V n _
        _ = ConcreteCategory.hom (((cokernel.π (Work.Cohomology.inclChains X (U ∩ V))).f n)
              ≫ (relMVLeft U V).f n) ζ :=
            (ModuleCat.comp_apply _ _ _).symm
        _ = ConcreteCategory.hom ((cokernel.π (Work.Cohomology.inclChains X U)).f n) ζ := by
            rw [cokernel_π_inclChains_comp_relMVLeft]
            rfl
        _ = a := hfstζ
        _ = ConcreteCategory.hom ((biprod.fst : relProd (X := X) U V ⟶ relCX (X := X) U).f n) x₂ :=
            ha
    · calc ConcreteCategory.hom ((biprod.snd : relProd (X := X) U V ⟶ relCX (X := X) V).f n)
            (ConcreteCategory.hom ((relMVMap U V).f n)
              (ConcreteCategory.hom ((cokernel.π (Work.Cohomology.inclChains X (U ∩ V))).f n) ζ))
          = ConcreteCategory.hom ((relMVRightMap U V).f n)
              (ConcreteCategory.hom ((cokernel.π (Work.Cohomology.inclChains X (U ∩ V))).f n) ζ) :=
            snd_relMVMap_apply U V n _
        _ = ConcreteCategory.hom (((cokernel.π (Work.Cohomology.inclChains X (U ∩ V))).f n)
              ≫ (relMVRightMap U V).f n) ζ :=
            (ModuleCat.comp_apply _ _ _).symm
        _ = ConcreteCategory.hom ((cokernel.π (Work.Cohomology.inclChains X V)).f n) ζ := by
            rw [cokernel_π_inclChains_comp_relMVRightMap]
            rfl
        _ = b := hsndζ
        _ = ConcreteCategory.hom ((biprod.snd : relProd (X := X) U V ⟶ relCX (X := X) V).f n) x₂ :=
            hb
  · rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    have h : ((relMVMap U V).f n) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    exact sub_eq_zero.mp (relMVMap_f_eq_zero U V n h)
  · rw [ModuleCat.epi_iff_surjective]
    intro z
    obtain ⟨y, hy⟩ := exists_cokernel_π_f_eq (Work.Cohomology.smallToSing U V) n z
    refine ⟨((biprod.inl : relCX (X := X) U ⟶ relProd (X := X) U V).f n)
      (((cokernel.π (Work.Cohomology.inclChains X U)).f n) y), ?_⟩
    calc ConcreteCategory.hom ((relCokerMap U V).f n)
          (ConcreteCategory.hom ((biprod.inl : relCX (X := X) U ⟶ relProd (X := X) U V).f n)
            (ConcreteCategory.hom ((cokernel.π (Work.Cohomology.inclChains X U)).f n) y))
        = ConcreteCategory.hom ((relCokerMapU U V).f n)
            (ConcreteCategory.hom ((cokernel.π (Work.Cohomology.inclChains X U)).f n) y) :=
          relCokerMap_apply_inl U V n _
      _ = ConcreteCategory.hom (((cokernel.π (Work.Cohomology.inclChains X U)).f n)
            ≫ (relCokerMapU U V).f n) y := (ModuleCat.comp_apply _ _ _).symm
      _ = ConcreteCategory.hom ((cokernel.π (Work.Cohomology.smallToSing U V)).f n) y := by
          rw [cokernel_π_inclChains_comp_relCokerMapU]
      _ = z := hy

/-- **The relative Mayer–Vietoris short complex is short exact, degreewise** (in the form of the
degreewise evaluation). -/
lemma relMVShort_degreewise_shortExact (U V : Set X) (n : ℕ) :
    ((relMVShort U V).map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).ShortExact :=
  relMVShortEval_shortExact U V n

/-- **The relative Mayer–Vietoris short complex is short exact.** -/
theorem relMVShort_shortExact (U V : Set X) : (relMVShort U V).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => relMVShort_degreewise_shortExact U V n)

/-! ## The projections of the diagonal on homology -/

lemma homologyMap_fst_relMVMap (U V : Set X) (n : ℕ)
    (w : (relCX (X := X) (U ∩ V)).homology n) :
    (HomologicalComplex.homologyMap (biprod.fst : relProd (X := X) U V ⟶ relCX (X := X) U) n)
        ((HomologicalComplex.homologyMap (relMVMap U V) n) w)
      = relMapHom (X := X) (Set.inter_subset_left : U ∩ V ⊆ U) n w := by
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
    show relMVMap U V ≫ (biprod.fst : relProd (X := X) U V ⟶ relCX (X := X) U) = relMVLeft U V
      from biprod.lift_fst _ _]
  rfl

lemma homologyMap_snd_relMVMap (U V : Set X) (n : ℕ)
    (w : (relCX (X := X) (U ∩ V)).homology n) :
    (HomologicalComplex.homologyMap (biprod.snd : relProd (X := X) U V ⟶ relCX (X := X) V) n)
        ((HomologicalComplex.homologyMap (relMVMap U V) n) w)
      = relMapHom (X := X) (Set.inter_subset_right : U ∩ V ⊆ V) n w := by
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.homologyMap_comp,
    show relMVMap U V ≫ (biprod.snd : relProd (X := X) U V ⟶ relCX (X := X) V) = relMVRightMap U V
      from biprod.lift_snd _ _]
  rfl

/-- An element of `H_n(C_*(X)/C_*(U) ⊞ C_*(X)/C_*(V))` whose two projections vanish is zero. -/
lemma homology_eq_zero_of_fst_snd_eq_zero (U V : Set X) (n : ℕ)
    {w' : (relProd (X := X) U V).homology n}
    (h1 : (HomologicalComplex.homologyMap (biprod.fst : relProd (X := X) U V ⟶
      relCX (X := X) U) n) w' = 0)
    (h2 : (HomologicalComplex.homologyMap (biprod.snd : relProd (X := X) U V ⟶
      relCX (X := X) V) n) w' = 0) : w' = 0 := by
  have hid : (HomologicalComplex.homologyMap (biprod.fst : relProd (X := X) U V ⟶
        relCX (X := X) U) n)
      ≫ (HomologicalComplex.homologyMap (biprod.inl : relCX (X := X) U ⟶ relProd (X := X) U V) n)
      + (HomologicalComplex.homologyMap (biprod.snd : relProd (X := X) U V ⟶
        relCX (X := X) V) n)
      ≫ (HomologicalComplex.homologyMap (biprod.inr : relCX (X := X) V ⟶ relProd (X := X) U V) n)
      = 𝟙 ((relProd (X := X) U V).homology n) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_add, biprod.total, HomologicalComplex.homologyMap_id]
  have happ := congrArg (fun (φ : (relProd (X := X) U V).homology n ⟶
    (relProd (X := X) U V).homology n) => φ w') hid
  simp only [ModuleCat.hom_add, ModuleCat.hom_id, ModuleCat.hom_comp, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.id_apply] at happ
  rw [h1, h2, map_zero, map_zero, add_zero] at happ
  exact happ.symm

/-! ## Auxiliary lemmas: supports, restricted subdivision and the small chains -/

/-- **Descent.**  A morphism from the chains of a simplicial set which lands in a submodule on all
generators lands in it everywhere. -/
lemma mem_of_gen_chain {Y : SSet} {n : ℕ} (Q : Submodule ℤ (rCh X n))
    (T : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n ⟶ (Work.Cohomology.singularChains ℤ X).X n)
    (hgen : ∀ y : Y _⦋n⦌, ModuleCat.Hom.hom T (genSSet Y n y) ∈ Q) :
    ∀ c, ModuleCat.Hom.hom T c ∈ Q := by
  intro c
  letI : Module ℤ ((rCh X n) ⧸ Q) := Submodule.Quotient.module Q
  let q : (Work.Cohomology.singularChains ℤ X).X n ⟶ ModuleCat.of ℤ ((rCh X n) ⧸ Q) :=
    ModuleCat.ofHom (Submodule.mkQ Q)
  have hg : T ≫ q = 0 := by
    apply SSet.chainComplex_hom_ext (X := Y) (R := ModuleCat.of ℤ ℤ)
    intro y
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply, LinearMap.zero_apply]
    show Submodule.Quotient.mk (ModuleCat.Hom.hom T (genSSet Y n y)) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hgen y
  have h2 : ModuleCat.Hom.hom (T ≫ q) c = 0 := by
    rw [hg, ModuleCat.hom_zero, LinearMap.zero_apply]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  have h3 : ModuleCat.Hom.hom q = Submodule.mkQ Q := rfl
  rw [h3, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
  exact h2

/-- The two descriptions of the inclusion of a subspace agree. -/
lemma subtypeIncl_eq_inclUX (S : Set X) :
    Work.Cohomology.subtypeIncl X S = Work.Cohomology.inclUX S := by
  apply TopCat.ext
  intro x
  rfl

/-- The inclusion of chains, evaluated on a generator. -/
lemma inclChains_gen_apply (S : Set X) (n : ℕ) (σ : Simplex (TopCat.of S) n) :
    (Work.Cohomology.inclChains X S).f n (gen (TopCat.of S) n σ)
      = gen X n ((TopCat.toSSet.map (Work.Cohomology.subtypeIncl X S)).app
          (Opposite.op ⦋n⦌) σ) :=
  chainComplexMap_ι_apply (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X S)) n σ 1

/-- The image of a generator under the inclusion of chains lies in the support submodule. -/
lemma inclChains_f_gen_mem_rSupp (S : Set X) (n : ℕ) (σ : Simplex (TopCat.of S) n) :
    (Work.Cohomology.inclChains X S).f n (gen (TopCat.of S) n σ) ∈ rSupp X S n :=
  LinearMap.mem_range.mpr ⟨gen (TopCat.of S) n σ, rfl⟩

/-- A generator whose simplex lands in `S` is a chain supported in `S`. -/
lemma gen_mem_rSupp_of_range {S : Set X} {n : ℕ} {σ : Simplex X n}
    (hσ : Set.range (fun z : stdSimplex ℝ (Fin (n + 1)) =>
        Work.Homology.toSSetObjEquiv' X (Opposite.op ⦋n⦌) σ z) ⊆ S) :
    gen X n σ ∈ rSupp X S n := by
  obtain ⟨a, ha⟩ := exists_map_inclUX_of_range_subset S (Opposite.op ⦋n⦌) σ hσ
  have h1 : (Work.Cohomology.inclChains X S).f n (gen (TopCat.of S) n a) = gen X n σ := by
    rw [inclChains_gen_apply, subtypeIncl_eq_inclUX, ha]
  rw [← h1]
  exact inclChains_f_gen_mem_rSupp S n a

/-- Every small chain is supported in `U ∪ V`. -/
lemma smallToSing_mem_rSupp (U V : Set X) (n : ℕ) (c : (Work.Cohomology.smallChains U V).X n) :
    (Work.Cohomology.smallToSing U V).f n c ∈ rSupp X (U ∪ V) n := by
  refine mem_of_gen_chain (rSupp X (U ∪ V) n) ((Work.Cohomology.smallToSing U V).f n) ?_ c
  intro σ
  rw [show ModuleCat.Hom.hom ((Work.Cohomology.smallToSing U V).f n) (genSSet (smallSSet U V) n σ)
      = gen X n σ.1 from Work.Cohomology.smallToSing_gen σ]
  exact gen_mem_rSupp_of_range (by
    rcases σ.2 with h | h
    · exact fun y hy => Or.inl (h hy)
    · exact fun y hy => Or.inr (h hy))

/-- The small chains of the cover `{U, V}` are supported in `U ∪ V`. -/
lemma smallChainSubmodule_le_rSupp (U V : Set X) (n : ℕ) :
    Work.Cohomology.smallChainSubmodule U V n ≤ rSupp X (U ∪ V) n := by
  rintro c ⟨c', rfl⟩
  exact smallToSing_mem_rSupp U V n c'

/-- **A Lebesgue number for affine simplices, with the cover hypothesis restricted to the image of
the simplex.**  If the image of `σ` lies in `U ∪ V`, then every affine simplex of small enough mesh
is mapped into `U` or into `V`. -/
theorem exists_delta_affineSimplex_range {X : TopCat} (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (n : ℕ) (σ : Simplex X n)
    (hσ : Set.range (fun z : (Delta n : TopCat) => sdMap n σ z) ⊆ U ∪ V) :
    ∃ δ > 0, ∀ (k : ℕ) (v : Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))),
      meshVF v < δ → (Set.range (fun z : (Delta k : TopCat) => sdMap n σ (affineSimplex v z)) ⊆ U ∨
                      Set.range (fun z : (Delta k : TopCat) => sdMap n σ (affineSimplex v z)) ⊆ V) := by
  set f : Delta n ⟶ X := sdMap n σ with hf
  have hAB : f ⁻¹' U ∪ f ⁻¹' V = (Set.univ : Set (stdSimplex ℝ (Fin (n + 1)))) := by
    rw [Set.eq_univ_iff_forall]
    intro y
    rw [Set.mem_union, Set.mem_preimage, Set.mem_preimage, hf]
    exact hσ ⟨y, rfl⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_delta_openCover (Z := stdSimplex ℝ (Fin (n + 1)))
    (f ⁻¹' U) (f ⁻¹' V) (hU.preimage f.hom.continuous) (hV.preimage f.hom.continuous) hAB
  refine ⟨δ, hδpos, ?_⟩
  intro k v hv
  have hne : (Set.range (affineSimplex v)).Nonempty :=
    ⟨affineSimplex v (stdSimplex.vertex 0), Set.mem_range_self _⟩
  have hdiam : ∀ x ∈ Set.range (affineSimplex v), ∀ y ∈ Set.range (affineSimplex v),
      dist x y < δ := by
    rintro x ⟨s, rfl⟩ y ⟨t, rfl⟩
    exact lt_of_le_of_lt (dist_affineSimplex_le_meshVF v s t) hv
  rcases hδ _ hne hdiam with hU' | hV'
  · left
    rintro y ⟨z, rfl⟩
    exact hU' ⟨z, rfl⟩
  · right
    rintro y ⟨z, rfl⟩
    exact hV' ⟨z, rfl⟩

/-- **Refinement, with the cover hypothesis restricted to the simplex's image.**  If the image of
`σ` lies in `U ∪ V`, then some iterate of the subdivision sends its generator into the small
chains. -/
theorem exists_iter_small_range {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (n : ℕ) (σ : Simplex X n)
    (hσ : Set.range (fun z : (Delta n : TopCat) => sdMap n σ z) ⊆ U ∪ V) :
    ∃ N, IsSmallChain U V ((sdChainMapIter X N).f n (gen X n σ)) := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_delta_affineSimplex_range U V hU hV n σ hσ
  have hlt : ((n : ℝ) / (n + 1)) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδpos hlt
  refine ⟨N, ?_⟩
  rw [sdChainMapIter_gen X n N σ]
  rw [toChain_apply]
  rw [map_sum]
  refine IsSmallChain.sum _ _ fun v hv => ?_
  rw [map_zsmul]
  refine IsSmallChain.smul _ ?_
  refine isSmallChain_pushChain_gen_linSimplex n (sdMap n σ) δ (fun v hv => hδ n v hv) v ?_
  exact lt_of_le_of_lt (mesh_sdIterLC n N v hv) hN

/-- **Restricted refinement.**  Some iterate of the subdivision sends a chain supported in `U ∪ V`
into the small chains of the cover `{U, V}`. -/
theorem exists_iter_small_chain_rSupp_dev {X : TopCat} (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (n : ℕ) (c : rCh X n) (hc : c ∈ rSupp X (U ∪ V) n) :
    ∃ N, IsSmallChain U V ((sdChainMapIter X N).f n c) := by
  obtain ⟨a, ha⟩ := hc
  let P : Submodule ℤ (rCh X n) := ⨆ N, Submodule.comap
    (ModuleCat.Hom.hom ((sdChainMapIter X N).f n)) (Work.Cohomology.smallChainSubmodule U V n)
  have hgen : ∀ σ : Simplex (TopCat.of (U ∪ V : Set X)) n,
      ModuleCat.Hom.hom ((Work.Cohomology.inclChains X (U ∪ V)).f n)
        (gen (TopCat.of (U ∪ V : Set X)) n σ) ∈ P := by
    intro σ
    have hσ : Set.range (fun z : (Delta n : TopCat) =>
        sdMap n ((TopCat.toSSet.map (Work.Cohomology.inclUX (U ∪ V))).app
          (Opposite.op ⦋n⦌) σ) z) ⊆ U ∪ V := by
      rintro y ⟨z, rfl⟩
      rw [sdMap_map]
      exact (sdMap n σ z).2
    obtain ⟨N, hN⟩ := exists_iter_small_range U V hU hV n
      ((TopCat.toSSet.map (Work.Cohomology.inclUX (U ∪ V))).app (Opposite.op ⦋n⦌) σ) hσ
    refine le_iSup (fun N => Submodule.comap (ModuleCat.Hom.hom ((sdChainMapIter X N).f n))
      (Work.Cohomology.smallChainSubmodule U V n)) N ?_
    rw [Submodule.mem_comap]
    have h1 : ModuleCat.Hom.hom ((Work.Cohomology.inclChains X (U ∪ V)).f n)
        (gen (TopCat.of (U ∪ V : Set X)) n σ)
        = gen X n ((TopCat.toSSet.map (Work.Cohomology.inclUX (U ∪ V))).app
            (Opposite.op ⦋n⦌) σ) := by
      rw [inclChains_gen_apply, subtypeIncl_eq_inclUX]
    rw [h1]
    exact hN
  have hmem : ModuleCat.Hom.hom ((Work.Cohomology.inclChains X (U ∪ V)).f n) a ∈ P :=
    mem_of_gen_chain P ((Work.Cohomology.inclChains X (U ∪ V)).f n) hgen a
  rw [ha] at hmem
  have hdir : Directed (· ≤ ·) (fun N => Submodule.comap
      (ModuleCat.Hom.hom ((sdChainMapIter X N).f n))
      (Work.Cohomology.smallChainSubmodule U V n)) := by
    intro N M
    refine ⟨N + M, ?_, ?_⟩
    · rintro x hx
      rw [Submodule.mem_comap] at hx ⊢
      rw [sdChainMapIter_f_apply X N M n x]
      exact iter_sd_small U V M hx
    · rintro x hx
      rw [Submodule.mem_comap] at hx ⊢
      rw [show N + M = M + N from Nat.add_comm N M, sdChainMapIter_f_apply X M N n x]
      exact iter_sd_small U V N hx
  rw [Submodule.mem_iSup_of_directed _ hdir] at hmem
  obtain ⟨N, hN⟩ := hmem
  exact ⟨N, hN⟩

/-- **(El-Epi for chains supported in `U ∪ V`).**  A chain supported in `U ∪ V` whose boundary is
a small chain differs from a small chain by a boundary. -/
theorem exists_bdry_add_small_supp_dev {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (n : ℕ) {e : rCh X (n + 1)} (he : e ∈ rSupp X (U ∪ V) (n + 1))
    (hde : rbd X n e ∈ Work.Cohomology.smallChainSubmodule U V n) :
    ∃ (t : rCh X (n + 2)) (c : rCh X (n + 1)),
      c ∈ Work.Cohomology.smallChainSubmodule U V (n + 1) ∧ e = rbd X (n + 1) t + c := by
  obtain ⟨N, hN⟩ := exists_iter_small_chain_rSupp_dev U V hU hV (n + 1) e he
  obtain ⟨T, hT⟩ := Work.Cohomology.exists_small_homotopy X U V N
  refine ⟨-((T.hom (n + 1) (n + 2)).hom e),
    (sdChainMapIter X N).f (n + 1) e - (T.hom (n + 1 - 1) (n + 1)).hom
      (((Work.Cohomology.singularChains ℤ X).d (n + 1) (n + 1 - 1)).hom e), ?_, ?_⟩
  · exact Submodule.sub_mem _ hN (hT (n + 1 - 1)
      (((Work.Cohomology.singularChains ℤ X).d (n + 1) (n + 1 - 1)).hom e) hde)
  · have hform := Work.Cohomology.homotopy_apply_eq X N (n + 1) T e
    rw [map_neg, hform]
    abel

/-- **The elementwise form of the vanishing of the relative homology.**  If the relative homology
`H_{n+1}(X, S)` vanishes, then any chain whose boundary is supported in `S` differs from a chain
supported in `S` by a boundary. -/
theorem exists_bdry_add_of_isZero_dev {X : TopCat} (S : Set X) (n : ℕ)
    (h : IsZero ((Work.Cohomology.relChains X S).homology (n + 1)))
    {z : rCh X (n + 1)} (hz : rbd X n z ∈ rSupp X S n) :
    ∃ (w : rCh X (n + 2)) (e : rCh X (n + 1)),
      e ∈ rSupp X S (n + 1) ∧ z = rbd X (n + 1) w + e := by
  have hC : IsZero ((cokernel (Work.Cohomology.inclChains X S)).homology (n + 1)) := h
  set ζ : (cokernel (Work.Cohomology.inclChains X S)).X (n + 1) :=
    ((cokernel.π (Work.Cohomology.inclChains X S)).f (n + 1)) z with hζ
  have hcyc : ((cokernel (Work.Cohomology.inclChains X S)).d (n + 1) n) ζ = 0 := by
    have hcomm := congrArg (fun (φ : (Work.Cohomology.singularChains ℤ X).X (n + 1) ⟶
        (cokernel (Work.Cohomology.inclChains X S)).X n) => φ z)
      (HomologicalComplex.Hom.comm (cokernel.π (Work.Cohomology.inclChains X S)) (n + 1) n)
    simp only [ModuleCat.comp_apply] at hcomm
    rw [hζ, hcomm]
    exact (Work.Cohomology.cokernel_pi_f_eq_zero_iff (Work.Cohomology.inclChains X S) n _).2
      (LinearMap.mem_range.mp hz)
  have hex : ((cokernel (Work.Cohomology.inclChains X S)).sc' (n + 2) (n + 1) n).Exact :=
    (HomologicalComplex.exactAt_iff' (cokernel (Work.Cohomology.inclChains X S)) (n + 2) (n + 1) n
      (by simp) (by simp)).mp
      ((HomologicalComplex.exactAt_iff_isZero_homology (cokernel (Work.Cohomology.inclChains X S))
        (n + 1)).2 hC)
  obtain ⟨x₁, hx₁⟩ := (ShortComplex.moduleCat_exact_iff _).1 hex ζ hcyc
  obtain ⟨W, hW⟩ := exists_cokernel_π_f_eq (Work.Cohomology.inclChains X S) (n + 2) x₁
  have hcommW : ((cokernel (Work.Cohomology.inclChains X S)).d (n + 2) (n + 1))
      (((cokernel.π (Work.Cohomology.inclChains X S)).f (n + 2)) W)
      = ((cokernel.π (Work.Cohomology.inclChains X S)).f (n + 1))
          (((Work.Cohomology.singularChains ℤ X).d (n + 2) (n + 1)) W) := by
    have hcomm := congrArg (fun (φ : (Work.Cohomology.singularChains ℤ X).X (n + 2) ⟶
        (cokernel (Work.Cohomology.inclChains X S)).X (n + 1)) => φ W)
      (HomologicalComplex.Hom.comm (cokernel.π (Work.Cohomology.inclChains X S)) (n + 2) (n + 1))
    simpa only [ModuleCat.comp_apply] using hcomm
  have hdW : ((cokernel.π (Work.Cohomology.inclChains X S)).f (n + 1))
      (((Work.Cohomology.singularChains ℤ X).d (n + 2) (n + 1)) W) = ζ := by
    rw [← hcommW, hW]
    exact hx₁
  have hze : ((cokernel.π (Work.Cohomology.inclChains X S)).f (n + 1))
      (z - ((Work.Cohomology.singularChains ℤ X).d (n + 2) (n + 1)) W) = 0 := by
    rw [map_sub, show ((cokernel.π (Work.Cohomology.inclChains X S)).f (n + 1)) z = ζ from hζ.symm,
      hdW, sub_self]
  exact ⟨W, z - ((Work.Cohomology.singularChains ℤ X).d (n + 2) (n + 1)) W,
    (Work.Cohomology.cokernel_pi_f_eq_zero_iff (Work.Cohomology.inclChains X S) (n + 1) _).1 hze,
    by abel⟩

/-- **The vanishing of `H_n(C_*(X)/C^{U,V}_*(X))`.**  If the relative homology of the pair
`(X, U ∪ V)` vanishes in degree `n+1`, then so does the homology of the cokernel of the inclusion of
the small chains.  This is the relative form of the small-simplices theorem. -/
theorem isZero_homology_cokernel_smallToSing_dev {X : TopCat} (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (n : ℕ)
    (h : IsZero ((Work.Cohomology.relChains X (U ∪ V)).homology (n + 1))) :
    IsZero ((cokernel (Work.Cohomology.smallToSing U V)).homology (n + 1)) := by
  -- every cycle of the cokernel of `smallToSing` is a boundary
  have hbd : ∀ z : (cokernel (Work.Cohomology.smallToSing U V)).X (n + 1),
      ((cokernel (Work.Cohomology.smallToSing U V)).d (n + 1) n) z = 0 →
      ∃ b : (cokernel (Work.Cohomology.smallToSing U V)).X (n + 2),
        ((cokernel (Work.Cohomology.smallToSing U V)).d (n + 2) (n + 1)) b = z := by
    intro z hz
    obtain ⟨ζ, hζ⟩ := exists_cokernel_π_f_eq (Work.Cohomology.smallToSing U V) (n + 1) z
    have hdζ : rbd X n ζ ∈ Work.Cohomology.smallChainSubmodule U V n := by
      rw [Work.Cohomology.smallChainSubmodule, LinearMap.mem_range,
        ← Work.Cohomology.cokernel_pi_f_eq_zero_iff (Work.Cohomology.smallToSing U V) n]
      have hcomm := congrArg (fun (φ : (Work.Cohomology.singularChains ℤ X).X (n + 1) ⟶
          (cokernel (Work.Cohomology.smallToSing U V)).X n) => φ ζ)
        (HomologicalComplex.Hom.comm (cokernel.π (Work.Cohomology.smallToSing U V)) (n + 1) n)
      simp only [ModuleCat.comp_apply] at hcomm
      rw [← hcomm, hζ, hz]
    obtain ⟨W, e, heS, hze⟩ := exists_bdry_add_of_isZero_dev (U ∪ V) n h
      (smallChainSubmodule_le_rSupp U V n hdζ)
    have hdd : rbd X n (rbd X (n + 1) W) = 0 := by
      have h := HomologicalComplex.d_comp_d (Work.Cohomology.singularChains ℤ X) (n + 2) (n + 1) n
      have h2 := congrArg (fun (φ : (Work.Cohomology.singularChains ℤ X).X (n + 2) ⟶
          (Work.Cohomology.singularChains ℤ X).X n) => φ W) h
      simpa only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply, rbd] using h2
    have hde : rbd X n e ∈ Work.Cohomology.smallChainSubmodule U V n := by
      have hsplit : rbd X n e = rbd X n ζ := by
        have h2 : rbd X n ζ = rbd X n (rbd X (n + 1) W + e) := by rw [← hze]
        rw [map_add, hdd, zero_add] at h2
        exact h2.symm
      rw [hsplit]
      exact hdζ
    obtain ⟨t, c, hcT, hec⟩ := exists_bdry_add_small_supp_dev U V hU hV n heS hde
    have hζD : ζ = rbd X (n + 1) (W + t) + c := by
      rw [hze, hec, map_add]
      abel
    have hc0 : ((cokernel.π (Work.Cohomology.smallToSing U V)).f (n + 1)) c = 0 :=
      (Work.Cohomology.cokernel_pi_f_eq_zero_iff (Work.Cohomology.smallToSing U V) (n + 1) c).2
        (LinearMap.mem_range.mp hcT)
    have hcomm : ((cokernel (Work.Cohomology.smallToSing U V)).d (n + 2) (n + 1))
        (((cokernel.π (Work.Cohomology.smallToSing U V)).f (n + 2)) (W + t))
        = ((cokernel.π (Work.Cohomology.smallToSing U V)).f (n + 1)) (rbd X (n + 1) (W + t)) := by
      have h' := congrArg (fun (φ : (Work.Cohomology.singularChains ℤ X).X (n + 2) ⟶
          (cokernel (Work.Cohomology.smallToSing U V)).X (n + 1)) => φ (W + t))
        (HomologicalComplex.Hom.comm (cokernel.π (Work.Cohomology.smallToSing U V)) (n + 2) (n + 1))
      simpa only [ModuleCat.comp_apply, rbd] using h'
    refine ⟨((cokernel.π (Work.Cohomology.smallToSing U V)).f (n + 2)) (W + t), ?_⟩
    rw [hcomm]
    have h3 : ((cokernel.π (Work.Cohomology.smallToSing U V)).f (n + 1)) (rbd X (n + 1) (W + t)) = z := by
      have h4 : ((cokernel.π (Work.Cohomology.smallToSing U V)).f (n + 1)) ζ
          = ((cokernel.π (Work.Cohomology.smallToSing U V)).f (n + 1)) (rbd X (n + 1) (W + t))
            + ((cokernel.π (Work.Cohomology.smallToSing U V)).f (n + 1)) c := by
        rw [← map_add, ← hζD]
      rw [hζ, hc0, add_zero] at h4
      exact h4.symm
    exact h3
  -- conclude
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff]
  intro z hz
  exact hbd z hz

/-! ## The main theorem -/

theorem relChains_diagonal_injective {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (k : ℕ) (h : CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains X (U ∪ V)).homology (k + 2))) :
    Function.Injective (fun x : (Work.Cohomology.relChains X (U ∩ V)).homology (k + 1) =>
      (Work.Compact.Noncompact.relMapHom (X := X) (Set.inter_subset_left : U ∩ V ⊆ U) (k + 1) x,
       Work.Compact.Noncompact.relMapHom (X := X) (Set.inter_subset_right : U ∩ V ⊆ V) (k + 1) x)) := by
  haveI hQ : IsZero ((relQ (X := X) U V).homology (k + 2)) :=
    isZero_homology_cokernel_smallToSing_dev (X := X) U V hU hV (k + 1) h
  have hS : (relMVShort U V).ShortExact := relMVShort_shortExact U V
  have hex := hS.homology_exact₁ (k + 2) (k + 1) (by simp [ComplexShape.down])
  -- the kernel of the diagonal on homology is zero
  have hker : ∀ z : (relCX (X := X) (U ∩ V)).homology (k + 1),
      HomologicalComplex.homologyMap (relMVMap U V) (k + 1) z = 0 → z = 0 := by
    intro z hz
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 hex z hz
    haveI hsub : Subsingleton (↑((relMVShort U V).X₃.homology (k + 2))) :=
      (ModuleCat.isZero_iff_subsingleton).1 hQ
    have hy0 : y = 0 := Subsingleton.elim y 0
    rw [hy0, map_zero] at hy
    exact hy.symm
  intro x y hxy
  have hx1 : relMapHom (X := X) (Set.inter_subset_left : U ∩ V ⊆ U) (k + 1) x
      = relMapHom (X := X) (Set.inter_subset_left : U ∩ V ⊆ U) (k + 1) y := congrArg Prod.fst hxy
  have hx2 : relMapHom (X := X) (Set.inter_subset_right : U ∩ V ⊆ V) (k + 1) x
      = relMapHom (X := X) (Set.inter_subset_right : U ∩ V ⊆ V) (k + 1) y := congrArg Prod.snd hxy
  have hz1 : relMapHom (X := X) (Set.inter_subset_left : U ∩ V ⊆ U) (k + 1) (x - y) = 0 := by
    rw [map_sub, hx1, sub_self]
  have hz2 : relMapHom (X := X) (Set.inter_subset_right : U ∩ V ⊆ V) (k + 1) (x - y) = 0 := by
    rw [map_sub, hx2, sub_self]
  have hw : HomologicalComplex.homologyMap (relMVMap U V) (k + 1) (x - y) = 0 := by
    refine homology_eq_zero_of_fst_snd_eq_zero U V (k + 1) ?_ ?_
    · exact (homologyMap_fst_relMVMap U V (k + 1) (x - y)).trans hz1
    · exact (homologyMap_snd_relMVMap U V (k + 1) (x - y)).trans hz2
  exact sub_eq_zero.mp (hker (x - y) hw)

end

end Work.Compact.Noncompact
