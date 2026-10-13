/-
Area DSCOH (curric-46) — the normalization comparison: the comparison complexes as cochain
complexes, the comparison chain maps, and a general constructor of chain homotopies in `ℕ`-indexed
cochain complexes from degreewise data.

* `semiT P U` / `ordT P U` : the semi-ordered and ordered Čech complexes, built from
  `semiTerm`/`semiD` and `ordTerm`/`ordD` using the `d² = 0` computation
  `Work.DSCOH.Norm.semiD_ordD_comp`;
* `semiProjC`, `ordProjC`, `ordInclC` : the comparison maps as morphisms of cochain complexes, from
  `Work.DSCOH.Norm.projInclChain`;
* `homFam'` / `homotopyOfRaw` : `Homotopy.mk`-style data for `ℕ`-indexed cochain complexes: given
  components `hfun n : C.X (n+1) ⟶ D.X n` satisfying the homotopy relation in *every* degree,
  including the degree `0` identity `f.f 0 = C.d 0 1 ≫ hfun 0 + g.f 0`, they assemble into a
  Mathlib `Homotopy f g`.  (The degree `0` identity is not implied by the higher ones, so it has to
  be requested; this is the "augmentation" of the classical homotopy.)
-/
import Submission.Work.DSCOH.Norm.projInclChain
import Submission.Work.DSCOH.Norm.semiD_ordD_comp
import Submission.Work.DSCOH.Norm.cechComplexFunctor_d_comp
import Submission.Work.DSCOH.Norm.ordT_iso_altCech
import Submission.Work.DSCOH.AltCechComplex

namespace Work.DSCOH.Norm

open CategoryTheory Limits Opposite TopologicalSpace HomologicalComplex
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u v w

/-! ## Homotopies from degreewise data -/

section HomotopyOfRaw

variable {V : Type u} [Category.{v} V] [Preadditive V]

/-- The degreewise family of morphisms attached to data `hfun n : C.X (n+1) ⟶ D.X n`: the value
`hfun j` on the pair `(j+1, j)`, and zero elsewhere (with the index cast inserted). -/
noncomputable def homFam' (C D : CochainComplex V ℕ) (hfun : ∀ n, C.X (n + 1) ⟶ D.X n) :
    ∀ i j, (ComplexShape.up ℕ).Rel j i → (C.X i ⟶ D.X j) :=
  fun i j w => eqToHom (congrArg C.X w.symm) ≫ hfun j

lemma nullHomotopicMap'_homFam'_f_zero (C D : CochainComplex V ℕ)
    (hfun : ∀ n, C.X (n + 1) ⟶ D.X n) :
    (Homotopy.nullHomotopicMap' (homFam' C D hfun)).f 0 = C.d 0 1 ≫ hfun 0 := by
  rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right (k₁ := 0) (k₀ := 1)
    (r₁₀ := (rfl : (ComplexShape.up ℕ).Rel 0 1))
    (hk₁ := fun l hl => Nat.succ_ne_zero l hl)]
  simp only [homFam']
  simp

lemma nullHomotopicMap'_homFam'_f_succ (C D : CochainComplex V ℕ)
    (hfun : ∀ n, C.X (n + 1) ⟶ D.X n) (n : ℕ) :
    (Homotopy.nullHomotopicMap' (homFam' C D hfun)).f (n + 1) =
      C.d (n + 1) (n + 2) ≫ hfun (n + 1) + hfun n ≫ D.d n (n + 1) := by
  rw [Homotopy.nullHomotopicMap'_f (k₂ := n) (k₁ := n + 1) (k₀ := n + 2)
    (r₂₁ := (rfl : (ComplexShape.up ℕ).Rel n (n + 1)))
    (r₁₀ := (rfl : (ComplexShape.up ℕ).Rel (n + 1) (n + 2)))]
  simp only [homFam']
  simp

/-- **A chain homotopy from degreewise data**, for `ℕ`-indexed cochain complexes.

Given components `hfun n : C.X (n+1) ⟶ D.X n` satisfying the homotopy relation
`(f - g).f n = C.d n (n+1) ≫ hfun n + hfun (n-1) ≫ D.d (n-1) n` in every degree `n ≥ 1`, together
with the degree `0` identity `(f - g).f 0 = C.d 0 1 ≫ hfun 0`, the maps `f` and `g` are
homotopic. -/
noncomputable def homotopyOfRaw {C D : CochainComplex V ℕ} {f g : C ⟶ D}
    (hfun : ∀ n : ℕ, C.X (n + 1) ⟶ D.X n)
    (h0 : f.f 0 = C.d 0 1 ≫ hfun 0 + g.f 0)
    (hs : ∀ n : ℕ,
      f.f (n + 1) = C.d (n + 1) (n + 2) ≫ hfun (n + 1) + hfun n ≫ D.d n (n + 1) + g.f (n + 1)) :
    Homotopy f g := by
  have heq : Homotopy.nullHomotopicMap' (homFam' C D hfun) = f - g := by
    apply HomologicalComplex.hom_ext
    intro i
    rcases i with _ | n
    · rw [nullHomotopicMap'_homFam'_f_zero, HomologicalComplex.sub_f_apply, h0,
        add_sub_cancel_right]
    · rw [nullHomotopicMap'_homFam'_f_succ, HomologicalComplex.sub_f_apply, hs]
      abel
  exact Homotopy.equivSubZero.symm
    ((Homotopy.ofEq heq.symm).trans (Homotopy.nullHomotopy' (homFam' C D hfun)))

end HomotopyOfRaw

/-! ## The comparison complexes and chain maps -/

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {ι : Type w} [Fintype ι] [LinearOrder ι] [HasProducts (ModuleCat A)]

/-- The semi-ordered Čech complex (nondecreasing tuples). -/
noncomputable abbrev semiT (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) :
    CochainComplex (ModuleCat A) ℕ :=
  CochainComplex.of (semiTerm P U) (semiD P U) (fun n => (semiD_ordD_comp P U n).1)

/-- The ordered (alternating) Čech complex, in its tuple-indexed form (strictly increasing
tuples). -/
noncomputable abbrev ordT (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) :
    CochainComplex (ModuleCat A) ℕ :=
  CochainComplex.of (ordTerm P U) (ordD P U) (fun n => (semiD_ordD_comp P U n).2)

@[simp]
lemma semiT_d (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) (n : ℕ) :
    (semiT P U).d n (n + 1) = semiD P U n :=
  CochainComplex.of_d _ _ _

@[simp]
lemma ordT_d (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) (n : ℕ) :
    (ordT P U).d n (n + 1) = ordD P U n :=
  CochainComplex.of_d _ _ _

/-- The projection from Mathlib's unnormalized Čech complex onto the semi-ordered one, as a
morphism of cochain complexes. -/
noncomputable def semiProjC (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) :
    ((cechComplexFunctor U).obj P) ⟶ semiT P U :=
  CochainComplex.ofHom (X := (cechComplexFunctor U).obj P) (Y := semiT P U)
    (fun n => semiProj P U n) (fun n => by rw [semiT_d]; exact (projInclChain P U).1 n)

/-- The projection from the semi-ordered complex onto the ordered complex, as a morphism of
cochain complexes. -/
noncomputable def ordProjC (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) :
    semiT P U ⟶ ordT P U :=
  CochainComplex.ofHom (X := semiT P U) (Y := ordT P U)
    (fun n => ordProj P U n) (fun n => by rw [ordT_d, semiT_d]; exact (projInclChain P U).2.1 n)

/-- The inclusion of the ordered complex into the semi-ordered complex (identity on strictly
increasing tuples, zero on the other nondecreasing tuples), as a morphism of cochain complexes. -/
noncomputable def ordInclC (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) :
    ordT P U ⟶ semiT P U :=
  CochainComplex.ofHom (X := ordT P U) (Y := semiT P U)
    (fun n => ordIncl P U n) (fun n => by rw [semiT_d, ordT_d]; exact (projInclChain P U).2.2 n)

@[simp]
lemma semiProjC_f (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) (n : ℕ) :
    (semiProjC P U).f n = semiProj P U n := rfl

@[simp]
lemma ordProjC_f (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) (n : ℕ) :
    (ordProjC P U).f n = ordProj P U n := rfl

@[simp]
lemma ordInclC_f (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) (n : ℕ) :
    (ordInclC P U).f n = ordIncl P U n := rfl

end Work.DSCOH.Norm
