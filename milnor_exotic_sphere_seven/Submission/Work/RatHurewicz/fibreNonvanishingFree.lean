import Mathlib
import Submission.Work.Serre.C1Cyl
import Submission.Work.StemsB.Fibrations
import Submission.Work.Thom.Cohomology
import Submission.Work.Serre.Defs
import Submission.Work.Serre.fibreNonvanishing
import Submission.Work.Serre.fibreExcisionIso
import Submission.Work.Serre.ratPairBasic
import Submission.Work.Serre.B1Rel.Assembly
import Submission.Work.Serre.ratPairComparisonOneBoundary
import Submission.Work.Serre.DiscPair.isZero_conePairRelCoh
import Submission.Work.Serre.DiscPair.discCellStep
import Submission.Work.RatHurewicz.cylCMidHomologyDecompSucc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Fibre non-vanishing for a rationally spherical Serre fibration (the `IH`-free form)

Target: `Work.RatHurewicz.fibreNonvanishingFree`.  Write `M = cyl p`, `A = range (cylIncl p)`,
`Mb = (cylRetract p) ⁻¹' {b}`, `Ab = A ∩ Mb` and `C = A ∪ Mb = CMid p b`.  The target is:
the restriction `H^{r+1}(M,A;ℚ) → H^{r+1}(Mb,Ab;ℚ)` is injective.

## The reduction

The restriction factors as `H^{r+1}(M,A) → H^{r+1}(C,A) → H^{r+1}(Mb,Ab)`, the second map being the
excision isomorphism `Work.Serre.fibreExcisionIso` (proved).  The kernel of the first map is the
image of `H^{r+1}(M,C) → H^{r+1}(M,A)` (`Work.Serre.fibreNonvanishing_of_pieces`, proved).  Hence
the target follows from the **vanishing** `H^{r+1}(M,C;ℚ) = 0`
(`relCoh_cylCMid_isZero_free` below).

## The vanishing

The homology of the pair `(M,C)` is the (split) cofibre of the pair map `q : (E, p⁻¹b) → (B,{b})`
(`Work.RatHurewicz.cylCMidHomologyDecompSucc`, proved in parallel):

  `H_n(M, C; ℚ) ≅ coker(f_n) × ker(f_{n-1})`,  `f_n := H_n(E,p⁻¹b;ℚ) → H_n(B,{b};ℚ)`.

For `n = r+1`: `f_{r+1}` is *surjective* (`Work.Serre.ratPairComparisonOneBoundary`, proved, at
`f = r`; note that this only needs the fibre to be rationally acyclic in degrees `0 < j < r`, so it
applies in the range `r ≤ N` of the target) and `f_r` is an *isomorphism*
(`Work.Serre.B1Rel.relPairMapRat_isIso`, proved, with `R = r+1`, `φ = r`).  Hence
`H_{r+1}(M,C;ℚ) = 0`, and the field universal coefficient theorem
(`Work.Serre.DiscPair.isZero_relCoh_of_isZero_relH`, proved) dualises this to
`H^{r+1}(M,C;ℚ) = 0`.
-/

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **The vanishing of the relative cohomology of the cylinder modulo the union of the bottom copy
with the fibre cone** — the "transgression" statement, in the range `r ≤ N`. -/
theorem relCoh_cylCMid_isZero_free (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    {B : Type} [TopologicalSpace B] (hB : PathConnectedSpace B)
    {E : Type} [TopologicalSpace E] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) t))
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre p b))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (b : B) :
    CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl p)
      (Work.Serre.CMid p b)) := by
  classical
  -- the fibre data, at every point of the base
  have hfib : ∀ y : B, ∀ j : ℕ, 0 < j → j < r →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) j) :=
    fun y j hj hjr => hvan y j hj (by omega) (le_trans (le_of_lt hjr) hrN)
  have h0 : ∀ y : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p y)) 0
      ≅ ModuleCat.of ℚ ℚ) := fun y => by
    haveI := hpc y
    exact Work.Serre.ratH_zero_of_pathConnected (Work.StemsB.fibre p y)
  -- the pair map is surjective in degree `r + 1`
  have hsurj : Function.Surjective
      (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b) (r + 1)).hom := by
    rw [show r + 1 = 1 + r from by omega]
    exact Work.Serre.ratPairComparisonOneBoundary p hp b r hr hB (hpc b)
      (fun j hj hjl => hvan b j hj (by omega) (by omega))
  -- and injective in degree `r`
  haveI hiso : IsIso (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b) r) :=
    Work.Serre.B1Rel.relPairMapRat_isIso p hp b (r + 1) r (by omega) hfib h0 r (by omega)
  have hinj : Function.Injective
      (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b) r).hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  -- the cokernel vanishes
  have hcok : CategoryTheory.Limits.IsZero (CategoryTheory.Limits.cokernel
      (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b) (r + 1))) := by
    haveI : Epi (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b) (r + 1)) :=
      (ModuleCat.epi_iff_surjective _).mpr hsurj
    exact CategoryTheory.Limits.isZero_cokernel_of_epi _
  -- the kernel vanishes
  have hker : CategoryTheory.Limits.IsZero (CategoryTheory.Limits.kernel
      (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b) r)) := by
    haveI : Mono (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b) r) :=
      (ModuleCat.mono_iff_injective _).mpr hinj
    exact CategoryTheory.Limits.isZero_kernel_of_mono _
  -- the product vanishes
  have hprod : CategoryTheory.Limits.IsZero (ModuleCat.of ℚ
      (↥(CategoryTheory.Limits.cokernel
          (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b) (r + 1))) ×
        ↥(CategoryTheory.Limits.kernel
          (HomologicalComplex.homologyMap (Work.Serre.relPairMapRat p b) r)))) :=
    Work.Serre.DiscPair.isZero_prod hcok hker
  -- transport along the cofibre decomposition and dualise
  obtain ⟨e⟩ := cylCMidHomologyDecompSucc r hr p b
  exact Work.Serre.DiscPair.isZero_relCoh_of_isZero_relH (Work.Serre.CMid p b) (r + 1)
    (hprod.of_iso e)

/-- **The requested statement.** -/
theorem fibreNonvanishingFree (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    {B : Type} [TopologicalSpace B] (hB : PathConnectedSpace B)
    {E : Type} [TopologicalSpace E] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) t))
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre p b))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (b : B) :
    Function.Injective (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Work.Serre.cylRetract p) ⁻¹' {b}), Work.Serre.cyl p))
      {x : ↥((Work.Serre.cylRetract p) ⁻¹' {b}) |
        (x : Work.Serre.cyl p) ∈ Set.range (Work.Serre.cylIncl p)}
      (Set.range (Work.Serre.cylIncl p))
      (fun x hx => hx) ℚ (r + 1)).hom := by
  have hC : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl p)
      (Work.Serre.CMid p b)) :=
    relCoh_cylCMid_isZero_free r N hr hrN hB p hp hvan hpc hgen b
  have hexc : Function.Injective (Work.Thom.relCohMap (Work.Serre.cIncl p b)
      (Work.Serre.MBase p b) (Work.Serre.CBase p b) (fun _ hx => hx) ℚ (r + 1)).hom :=
    Work.Serre.fibreExcisionIso r N hr hrN hB p hp hvan hpc hgen b
  exact Work.Serre.fibreNonvanishing_of_pieces p b r hC hexc

end

end Work.RatHurewicz
