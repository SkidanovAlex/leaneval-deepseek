import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.fibreNonvanishing
import Submission.Work.Serre.fibreExcisionIso
import Submission.Work.Serre.TripleCohDefs
import Submission.Work.Serre.TripleCohLES
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Stems.fibrePieceSurj
import Submission.Work.Stems.fibrePieceRelIncl

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Injectivity of the fibre restriction of the relative Thom class

`Work.Stems.fibreRestrictionInjectiveOfPos` is the statement that the restriction of the relative
cohomology of the mapping cylinder `M = cyl q` modulo the bottom copy `A = range (cylIncl q)` to the
cone `P_b = (cylRetract q)⁻¹{b}` on the fibre over `b` is injective.

## The reduction (all steps below are formal, no new geometry)

Write `P = P_b`, `C = CMid q b = A ∪ P` (the middle set of the triple `A ⊆ C ⊆ M`).

1. **The map factors through the triple `A ⊆ C ⊆ M`.**  `relCohMap (P ↪ M)` is the composite of
   `relCohMap (cInclM) : H^{r+1}(M,C) → H^{r+1}(M,A)` (the triple map) with the excision map
   `H^{r+1}(C,A) → H^{r+1}(P,A∩P)`; the latter is injective (`Work.Serre.fibreExcisionIso`, proved),
   so it suffices that `relCohMap (cInclM)` vanishes, i.e. that `H^{r+1}(M,C;ℚ) = 0`
   (`Work.Serre.fibreNonvanishing_of_pieces`, proved, does this reduction for us).
2. **The vanishing `H^{r+1}(M,C;ℚ) = 0`.**  This is `hC` below, obtained from the two pieces
   `Work.Stems.fibrePieceSurj` (the restriction `H^r(M) → H^r(C)` is surjective, proved in
   `Submission/Work/Stems/fibrePieceSurj.lean`) and `Work.Stems.fibrePieceRelIncl`
   (the forgetful map `H^{r+1}(M,C) → H^{r+1}(M)` vanishes, proved in
   `Submission/Work/Stems/fibrePieceRelIncl.lean`) by the pair long exact sequence of
   `(M, C)` (`Work.Cohomology.pair_exact₁/₃`): surjectivity of `restr` forces the connecting map
   `pairδ` to vanish, hence `relIncl` is injective, and `relIncl = 0` on an injective map forces
   the source to be zero.  (This is the argument of
   `Submission/Work/RatHurewicz/fibreNonvanishingFree.lean`, reproduced here so that this file does
   not depend on the `sorry`-backed statement `fibreNonvanishingFree`.)
3. **The two pieces are the two halves of the rational Serre pair comparison.**  They are proved by
   the triple sequence of `P ⊆ C ⊆ M` together with the two identifications
   `H^n(M,P) ≅ H^n(B,{b})` (the retraction `cylRetract q` is a homotopy equivalence *of pairs*, with
   inverse `cylInr q` and the explicit homotopy `cylMoveHomotopy`, which preserves `P` because
   `cylRetract q ∘ cylMove q = cylRetract q`) and `H^n(C,P) ≅ H^n(A,A∩P) = H^n(E,F_b)` (excision),
   under which the two maps of the triple sequence become the edge maps
   `relCohMap q : H^n(B,{b}) → H^n(E,F_b)` (`n = r`: surjective, `Work.Serre.fibrePairMapSurj`,
   proved; `n = r+1`: injective, dual to the surjectivity of the pair map in degree `r+1`,
   `Work.Serre.ratPairComparisonBOneGeneral`, proved).
-/

namespace Work.Stems

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **The vanishing of the relative cohomology of the cylinder modulo the union of the bottom copy
with the fibre cone**, assembled from the two pieces by the pair sequence. -/
theorem relCoh_cylCMid_isZero {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (hB : PathConnectedSpace B) (q : C(X, B)) (hq : Work.StemsB.IsSerreFibration q)
    (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre q b))
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) t))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (b : B) :
    CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q)
      (Work.Serre.CMid q b)) := by
  classical
  set X : TopCat := TopCat.of (Work.Serre.cyl q) with hX
  set A : Set (Work.Serre.cyl q) := Work.Serre.CMid q b with hA
  have hsurj : Function.Surjective
      (HomologicalComplex.homologyMap (Work.Cohomology.restr ℚ X A) r).hom :=
    fibrePieceSurj hB q hq r N hr hrN hpc hvan hgen b
  have hzero : (HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℚ X A) (r + 1)).hom = 0 :=
    fibrePieceRelIncl hB q hq r N hr hrN hpc hvan hgen b
  have hex₃ := Work.Cohomology.pair_exact₃ ℚ X A r
  have hex₁ := Work.Cohomology.pair_exact₁ ℚ X A r
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex₃ hex₁
  have hδ0 : Work.Cohomology.pairδ ℚ X A r = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, hy⟩ := hsurj x
    have hx : x ∈ LinearMap.ker (Work.Cohomology.pairδ ℚ X A r).hom := by
      rw [← hex₃]
      exact ⟨y, hy⟩
    exact hx
  have hker : LinearMap.ker
      (HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℚ X A) (r + 1)).hom = ⊥ := by
    have h1 : LinearMap.range (Work.Cohomology.pairδ ℚ X A r).hom = ⊥ := by
      rw [hδ0]; simp
    rw [← hex₁, h1]
  refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y => ?_⟩
  have hinj : Function.Injective
      (HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℚ X A) (r + 1)).hom :=
    LinearMap.ker_eq_bot.mp hker
  have hxy : (HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℚ X A) (r + 1)).hom
      (x - y) = 0 := by
    rw [map_sub, hzero]; simp
  exact sub_eq_zero.mp (hinj (by rw [hxy, map_zero]))

/-- **The injectivity of the fibre restriction of the relative class of a spherical fibration**
(the requested statement; the hypothesis `hpos` is not needed, the vanishing of
`H^{r+1}(cyl q, CMid q b)` gives injectivity directly). -/
theorem fibreRestrictionInjectiveOfPos {B : Type} [TopologicalSpace B] {X : Type}
    [TopologicalSpace X]
    (hB : PathConnectedSpace B) (q : C(X, B)) (hq : Work.StemsB.IsSerreFibration q) (r N : ℕ)
    (hr : 1 ≤ r) (hrN : r + 1 ≤ N)
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre q b))
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) t))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (hpos : ¬ CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q)
        (Set.range (Work.Serre.cylIncl q))))
    (b : B) :
    Function.Injective (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥((Work.Serre.cylRetract q) ⁻¹' {b}), Work.Serre.cyl q))
      {x : ↥((Work.Serre.cylRetract q) ⁻¹' {b}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
      (Set.range (Work.Serre.cylIncl q))
      (fun x hx => hx) ℚ (r + 1)).hom := by
  have hrN' : r ≤ N := by omega
  have hC : CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q)
      (Work.Serre.CMid q b)) :=
    relCoh_cylCMid_isZero hB q hq r N hr hrN' hpc hvan hgen b
  have hexc : Function.Injective (Work.Thom.relCohMap (Work.Serre.cIncl q b)
      (Work.Serre.MBase q b) (Work.Serre.CBase q b) (fun _ hx => hx) ℚ (r + 1)).hom :=
    Work.Serre.fibreExcisionIso r N hr hrN' hB q hq hvan hpc hgen b
  exact Work.Serre.fibreNonvanishing_of_pieces q b r hC hexc

end

end Work.Stems
