import Mathlib
import Submission.Work.Serre.CMidCollarDefs
import Submission.Work.Serre.DiscPair.relPairHomotopic
import Submission.Work.Serre.CsrSharp.Tools
import Submission.Work.Serre.CylCMidVan.relChainsR_excisionInterior

/-!
# The cone-pair isomorphism `H_*(A₀, A) ≅ H_*(Mid, M)` over `ℚ`

Let `q : C(X, B)`, `b : B`, `Mid = CMid q b = cylBot q ∪ (cylRetract q) ⁻¹' {b}`,
`M = Mid ∩ (cylRetract q) ⁻¹' {b}` (the fibre cone), `A₀ = cylBot q` (the bottom copy) and
`A = A₀ ∩ (cylRetract q) ⁻¹' {b}` (the fibre inside the bottom copy).  The inclusion of pairs
`(A₀, A) → (Mid, M)` induces an isomorphism on relative singular homology with rational
coefficients.  The proof factors it through the collar pair `(U, Ub)`, `U = Mid ∩ cylCollar q`:

* `(A₀, A) → (U, Ub)` is an isomorphism because the collar shrink `cylShrink` is a homotopy inverse
  of the inclusion (`relChainsRPairMap_midIncl_isIso`);
* `(U, Ub) → (Mid, M)` is an excision: the interiors of `M` and of `U` cover `Mid`
  (`CMidCollar.interior_union_eq_univ`), so this is
  `Work.Serre.CylCMidVan.relChainsR_excisionInterior`.

Both factors are `Work.Serre.relChainsRPairMap`s, so they compose by
`Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre
namespace CMidCollar

noncomputable section

variable {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]

/-! ## The collar shrink on `U` -/

/-- The underlying function of the projection of `U q b` to the collar. -/
def toCollarFun (q : C(X, B)) (b : B) : ↥(U q b) → ↥(cylCollar q) :=
  fun x => ⟨((x : ↥(Mid q b)) : cyl q), x.2⟩

@[simp] theorem toCollarFun_apply (q : C(X, B)) (b : B) (x : ↥(U q b)) :
    ((toCollarFun q b x : ↥(cylCollar q)) : cyl q) = ((x : ↥(Mid q b)) : cyl q) := rfl

theorem continuous_toCollarFun (q : C(X, B)) (b : B) : Continuous (toCollarFun q b) :=
  Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _

/-- The projection of the collar part `U q b` of the middle set to the collar. -/
def toCollar (q : C(X, B)) (b : B) : C(↥(U q b), ↥(cylCollar q)) :=
  ⟨toCollarFun q b, continuous_toCollarFun q b⟩

@[simp] theorem toCollar_apply (q : C(X, B)) (b : B) (x : ↥(U q b)) :
    toCollar q b x = toCollarFun q b x := rfl

/-- The underlying function of the collar shrink at time `1`, as a map of `U q b` into the bottom
copy. -/
def shrinkBotFun (q : C(X, B)) (b : B) : ↥(U q b) → ↥(cylBot q) :=
  fun x => cylShrinkToBot q (toCollar q b x)

@[simp] theorem shrinkBotFun_apply (q : C(X, B)) (b : B) (x : ↥(U q b)) :
    ((shrinkBotFun q b x : ↥(cylBot q)) : cyl q)
      = ((cylShrink q 1 (toCollar q b x) : ↥(cylCollar q)) : cyl q) := rfl

theorem continuous_shrinkBotFun (q : C(X, B)) (b : B) : Continuous (shrinkBotFun q b) :=
  (cylShrinkToBot q).continuous.comp (toCollar q b).continuous

/-- The collar shrink at time `1`, as a map of `U q b` into the bottom copy. -/
def shrinkBot (q : C(X, B)) (b : B) : C(↥(U q b), ↥(cylBot q)) :=
  ⟨shrinkBotFun q b, continuous_shrinkBotFun q b⟩

@[simp] theorem shrinkBot_apply (q : C(X, B)) (b : B) (x : ↥(U q b)) :
    shrinkBot q b x = shrinkBotFun q b x := rfl

/-- The fibre part of the collar maps into the fibre inside the bottom copy under the shrink. -/
theorem shrinkBot_mapsTo (q : C(X, B)) (b : B) :
    Set.MapsTo (shrinkBot q b) (Ub q b) (A q b) := by
  intro x hx
  rw [mem_A_iff]
  rw [shrinkBot_apply, shrinkBotFun_apply]
  exact (cylRetract_cylShrink q 1 (toCollar q b x)).trans ((mem_Ub_iff q b x).mp hx)

/-- The shrink of `U`, read as a self-map of `U`. -/
def shrinkEnd (q : C(X, B)) (b : B) : C(↥(U q b), ↥(U q b)) :=
  (inclAU q b).comp (shrinkBot q b)

@[simp] theorem shrinkEnd_apply (q : C(X, B)) (b : B) (x : ↥(U q b)) :
    ((shrinkEnd q b x : ↥(U q b)) : ↥(Mid q b))
      = ⟨((cylShrink q 1 (toCollar q b x) : ↥(cylCollar q)) : cyl q),
          cylShrink_mem_Mid q b 1 ((x : ↥(Mid q b)).2)⟩ := rfl

/-! ## The two homotopies of pairs -/

/-- The underlying function of the collar shrink of `U`, as a homotopy of `U`. -/
def homUFun (q : C(X, B)) (b : B) : unitInterval × ↥(U q b) → ↥(U q b) :=
  fun p => ⟨⟨((cylShrink q p.1 (toCollar q b p.2) : ↥(cylCollar q)) : cyl q),
      cylShrink_mem_Mid q b p.1
        (by simpa [toCollar, ContinuousMap.coe_mk] using ((p.2 : ↥(Mid q b)).2))⟩,
    (cylShrink q p.1 (toCollar q b p.2)).2⟩

@[simp] theorem homUFun_coe (q : C(X, B)) (b : B) (t : unitInterval) (x : ↥(U q b)) :
    (((homUFun q b (t, x) : ↥(U q b)) : ↥(Mid q b)) : cyl q)
      = ((cylShrink q t (toCollar q b x) : ↥(cylCollar q)) : cyl q) := rfl

theorem continuous_homUFun (q : C(X, B)) (b : B) : Continuous (homUFun q b) := by
  have hcont : Continuous fun p : unitInterval × ↥(U q b) =>
      ((cylShrink q p.1 (toCollar q b p.2) : ↥(cylCollar q)) : cyl q) := by
    have hEq : (fun p : unitInterval × ↥(U q b) =>
        ((cylShrink q p.1 (toCollar q b p.2) : ↥(cylCollar q)) : cyl q))
        = fun p : unitInterval × ↥(U q b) =>
            (((cylShrinkHomotopy q) (p.1, toCollar q b p.2) : ↥(cylCollar q)) : cyl q) := by
      funext p
      exact congrArg Subtype.val (cylShrinkHomotopy_apply q p.1 (toCollar q b p.2))
    rw [hEq]
    exact continuous_subtype_val.comp ((cylShrinkHomotopy q).continuous.comp
      ((ContinuousMap.prodMap (ContinuousMap.id unitInterval) (toCollar q b)).continuous))
  exact Continuous.subtype_mk
    (Continuous.subtype_mk hcont (fun p => cylShrink_mem_Mid q b p.1
      (by simpa [toCollar, ContinuousMap.coe_mk] using ((p.2 : ↥(Mid q b)).2))))
    (fun p => (cylShrink q p.1 (toCollar q b p.2)).2)

/-- The collar shrink of `U`, as a homotopy from the identity to the shrink at time `1`. -/
def homU (q : C(X, B)) (b : B) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(U q b)) (shrinkEnd q b) where
  toContinuousMap := ⟨homUFun q b, continuous_homUFun q b⟩
  map_zero_left := fun x => by
    refine Subtype.ext (Subtype.ext ?_)
    rw [homUFun_coe, cylShrink_zero, toCollar_apply, toCollarFun_apply]
    rfl
  map_one_left := fun x => by
    refine Subtype.ext (Subtype.ext ?_)
    rw [homUFun_coe, shrinkEnd_apply]

@[simp] theorem homU_apply (q : C(X, B)) (b : B) (t : unitInterval) (x : ↥(U q b)) :
    homU q b (t, x) = homUFun q b (t, x) := rfl

/-- The shrink homotopy of `U` stays inside the fibre part `Ub q b`. -/
theorem homU_mapsTo (q : C(X, B)) (b : B) (t : unitInterval) {x : ↥(U q b)}
    (hx : x ∈ Ub q b) : homU q b (t, x) ∈ Ub q b := by
  rw [mem_Ub_iff]
  rw [homU_apply, homUFun_coe]
  have hx' : (cylRetract q) ((toCollar q b x : ↥(cylCollar q)) : cyl q) = b := by
    rw [toCollar_apply, toCollarFun_apply]
    exact (mem_Ub_iff q b x).mp hx
  exact (cylRetract_cylShrink q t (toCollar q b x)).trans hx'

/-- The underlying function of the constant homotopy of the bottom copy. -/
def homBotFun (q : C(X, B)) (b : B) : unitInterval × ↥(cylBot q) → ↥(cylBot q) :=
  fun p => shrinkBot q b (inclAU q b p.2)

theorem continuous_homBotFun (q : C(X, B)) (b : B) : Continuous (homBotFun q b) :=
  (shrinkBot q b).continuous.comp ((inclAU q b).continuous.comp continuous_snd)

/-- The constant homotopy of the bottom copy, from `shrinkBot ∘ inclAU` to the identity. -/
def homBot (q : C(X, B)) (b : B) :
    ContinuousMap.Homotopy ((shrinkBot q b).comp (inclAU q b)) (ContinuousMap.id ↥(cylBot q)) where
  toContinuousMap := ⟨homBotFun q b, continuous_homBotFun q b⟩
  map_zero_left := fun x => rfl
  map_one_left := fun x => by
    refine Subtype.ext ?_
    rw [homBotFun, shrinkBot_apply, shrinkBotFun_apply]
    have hfix := cylShrink_fixes_bot q 1 (y := toCollar q b (inclAU q b x)) (by
      rw [toCollar_apply, toCollarFun_apply]
      exact x.2)
    exact congrArg (fun z : ↥(cylCollar q) => (z : cyl q)) hfix

@[simp] theorem homBot_apply (q : C(X, B)) (b : B) (t : unitInterval) (x : ↥(cylBot q)) :
    homBot q b (t, x) = homBotFun q b (t, x) := rfl

/-- The constant homotopy of the bottom copy stays inside the fibre part. -/
theorem homBot_mapsTo (q : C(X, B)) (b : B) (t : unitInterval) {x : ↥(cylBot q)}
    (hx : x ∈ A q b) : homBot q b (t, x) ∈ A q b := by
  rw [homBot_apply, homBotFun]
  exact shrinkBot_mapsTo q b (mapsTo_inclAU q b hx)

/-! ## The shrink isomorphism -/

/-- **The inclusion `(A₀, A) → (U, Ub)` is an isomorphism on relative rational homology**: the
collar shrink is a homotopy inverse of the inclusion. -/
theorem relChainsRPairMap_midIncl_isIso (q : C(X, B)) (b : B) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (A q b) (Ub q b) (inclAU q b)
        (mapsTo_inclAU q b)) n) := by
  have hcomp₁ : Work.Serre.relChainsRPairMap (A q b) (Ub q b) (inclAU q b)
        (mapsTo_inclAU q b)
      ≫ Work.Serre.relChainsRPairMap (Ub q b) (A q b) (shrinkBot q b)
        (shrinkBot_mapsTo q b)
      = Work.Serre.relChainsRPairMap (A q b) (A q b)
        ((shrinkBot q b).comp (inclAU q b))
        ((shrinkBot_mapsTo q b).comp (mapsTo_inclAU q b)) :=
    Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp (inclAU q b) (shrinkBot q b)
      (mapsTo_inclAU q b) (shrinkBot_mapsTo q b)
      (hg'' := (shrinkBot_mapsTo q b).comp (mapsTo_inclAU q b))
  have hcomp₂ : Work.Serre.relChainsRPairMap (Ub q b) (A q b) (shrinkBot q b)
        (shrinkBot_mapsTo q b)
      ≫ Work.Serre.relChainsRPairMap (A q b) (Ub q b) (inclAU q b) (mapsTo_inclAU q b)
      = Work.Serre.relChainsRPairMap (Ub q b) (Ub q b) (shrinkEnd q b)
        ((mapsTo_inclAU q b).comp (shrinkBot_mapsTo q b)) :=
    Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp (shrinkBot q b) (inclAU q b)
      (shrinkBot_mapsTo q b) (mapsTo_inclAU q b)
      (hg'' := (mapsTo_inclAU q b).comp (shrinkBot_mapsTo q b))
  have h1 : HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (A q b) (Ub q b) (inclAU q b) (mapsTo_inclAU q b)) n
      ≫ HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (Ub q b) (A q b) (shrinkBot q b)
          (shrinkBot_mapsTo q b)) n
      = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, hcomp₁,
      Work.Serre.DiscPair.relPairHomotopic (A := A q b) (B := A q b)
        ((shrinkBot_mapsTo q b).comp (mapsTo_inclAU q b)) (fun _ hx => hx) (homBot q b)
        (fun t u hu => homBot_mapsTo q b t hu) n,
      Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' (A q b) (fun _ hx => hx),
      HomologicalComplex.homologyMap_id]
  have h2 : HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (Ub q b) (A q b) (shrinkBot q b)
          (shrinkBot_mapsTo q b)) n
      ≫ HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (A q b) (Ub q b) (inclAU q b) (mapsTo_inclAU q b)) n
      = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, hcomp₂,
      ← Work.Serre.DiscPair.relPairHomotopic (A := Ub q b) (B := Ub q b)
        (f := ContinuousMap.id _) (fun _ hx => hx)
        ((mapsTo_inclAU q b).comp (shrinkBot_mapsTo q b)) (homU q b)
        (fun t x hx => homU_mapsTo q b t hx) n,
      Work.Serre.CsrSharp.Tools.relChainsRPairMap_id' (Ub q b) (fun _ hx => hx),
      HomologicalComplex.homologyMap_id]
  exact IsIso.mk ⟨_, h1, h2⟩

/-! ## The cone-pair isomorphism -/

/-- **The pair `(A₀, A) → (Mid, M)` is a rational homology isomorphism.**  It factors as
`(A₀, A) → (U, Ub) → (Mid, M)`, the first factor by the collar shrink
(`relChainsRPairMap_midIncl_isIso`) and the second by excision
(`Work.Serre.CylCMidVan.relChainsR_excisionInterior`, whose hypothesis is
`CMidCollar.interior_union_eq_univ`). -/
theorem conePairIso_mid (q : C(X, B)) (b : B) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (A q b) (M q b) (inclAC q b) (mapsTo_inclAC q b)) n) := by
  have hψ : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (Ub q b) (M q b) (inclUC q b)
        (mapsTo_inclUC q b)) n) := by
    rw [show Work.Serre.relChainsRPairMap (Ub q b) (M q b) (inclUC q b) (mapsTo_inclUC q b)
        = Work.Serre.relChainsRInclPairMap (TopCat.of ↥(Mid q b)) (U q b) (M q b) from rfl]
    exact Work.Serre.CylCMidVan.relChainsR_excisionInterior (U q b) (M q b)
      (interior_union_eq_univ q b) n
  have hφ : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (A q b) (Ub q b) (inclAU q b)
        (mapsTo_inclAU q b)) n) := relChainsRPairMap_midIncl_isIso q b n
  have hfac : Work.Serre.relChainsRPairMap (A q b) (Ub q b) (inclAU q b) (mapsTo_inclAU q b)
      ≫ Work.Serre.relChainsRPairMap (Ub q b) (M q b) (inclUC q b) (mapsTo_inclUC q b)
      = Work.Serre.relChainsRPairMap (A q b) (M q b) (inclAC q b) (mapsTo_inclAC q b) := by
    rw [Work.Serre.CsrSharp.Tools.relChainsRPairMap_comp (inclAU q b) (inclUC q b)
      (mapsTo_inclAU q b) (mapsTo_inclUC q b)
      (hg'' := (mapsTo_inclUC q b).comp (mapsTo_inclAU q b))]
    exact Work.Serre.CsrSharp.Tools.relChainsRPairMap_congr (inclUC_comp_inclAU q b) _ _
  haveI := hφ
  haveI := hψ
  have hcomp : CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (A q b) (Ub q b) (inclAU q b) (mapsTo_inclAU q b)
        ≫ Work.Serre.relChainsRPairMap (Ub q b) (M q b) (inclUC q b) (mapsTo_inclUC q b))
      n) := by
    rw [HomologicalComplex.homologyMap_comp]
    infer_instance
  rwa [hfac] at hcomp

end

end CMidCollar
end Work.Serre
