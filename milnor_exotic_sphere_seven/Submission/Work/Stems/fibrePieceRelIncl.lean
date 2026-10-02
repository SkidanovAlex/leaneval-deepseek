import Mathlib
import Submission.Work.Serre.fibreNonvanishing
import Submission.Work.Serre.fibreExcisionIso
import Submission.Work.Serre.fibrePairMapSurj
import Submission.Work.Serre.ratPairComparisonBOneGeneral
import Submission.Work.Serre.TripleCohDefs
import Submission.Work.Serre.TripleCohLES
import Submission.Work.Cohomology.PairSequence
import Submission.Work.StemsB.RelCohMapPairHomotopyR
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.cylRelPi
import Submission.Work.Serre.isIso_relCohMap_excision_of_interior
import Submission.Work.Serre.fibrePairMapInject
import Submission.Work.Serre.CMidPairDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The forgetful map `H^{r+1}(cyl q, CMid q b; ℚ) → H^{r+1}(cyl q; ℚ)` vanishes

`Work.Stems.fibrePieceRelIncl` is the second of the two halves of the rational Serre pair
comparison for a fibration `q : C(X,B)` whose fibres are rationally concentrated in degree `r`
(`1 ≤ r`, `r ≤ N`): the map

`H^{r+1}(M, C; ℚ) ⟶ H^{r+1}(M; ℚ)`,  `M = cyl q`,  `C = CMid q b = range (cylIncl q) ∪ P`,
`P = (cylRetract q) ⁻¹' {b}`,

is zero.  Equivalently (exactness of the pair sequence of `(M,C)`) the restriction
`H^{r+1}(M; ℚ) → H^{r+1}(C; ℚ)` is injective.

## Route

Write `A = range (cylIncl q) ≅ X` for the bottom copy of the mapping cylinder, `P = cylPairU q b`
for the cone on the fibre over `b` and `C = A ∪ P = CMid q b`.  The forgetful map for the pair
`(M,C)` factors through the pair `(M,P)` (the triple `P ⊆ C ⊆ M`):

`relIncl_{M,C} = tripleIncl_{P⊆C} ≫ relIncl_{M,P}`,

so it suffices to know that `tripleIncl_{P⊆C} : H^{r+1}(M,C) → H^{r+1}(M,P)` vanishes.  By
exactness of the triple sequence (`Work.Serre.tripleCoh_exact₂_range`) this holds as soon as the
restriction `tripleRestr_{P⊆C} : H^{r+1}(M,P) → H^{r+1}(C, C∩P)` is injective.

For that, write `tripleRestr_{P⊆C}` as the pullback along the inclusion of pairs
`(C, C∩P) → (M, P)` and factor the map of pairs `cylIncl q : (X, q⁻¹b) → (M,P)` through it:

`cylIncl q = (X, q⁻¹b) --cylInclMid--> (C, C∩P) --midIncl--> (M, P)`.

The pullback along `cylIncl q` is injective: the retraction `cylRetract q` is a homotopy
equivalence of pairs `(M,P) ≃ (B,{b})` (with inverse `cylInr q` and the push-up homotopy
`cylMove q`, which preserves `P`), so `(cylRetract q)^*` is bijective
(`Work.StemsB.relCohMap_pairHomotopyR`), while

`(cylRetract q)^* ≫ (cylIncl q)^* = q^*`

is injective in degree `r+1` by the relative edge map `Work.Serre.fibrePairMapInject`
(the duality half of the rational Serre pair comparison).  A composite with an injective second
factor being injective, the pullback along the inclusion `(C,C∩P) → (M,P)` is injective too, which
is what we needed.

No geometric input beyond `Work.Serre.fibrePairMapInject` and the pair homotopy equivalence is
used: in particular the excision `H^*(C, C∩P) ≅ H^*(X, q⁻¹b)` is *not* needed.
-/

namespace Work.Stems

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]

/-- The pullback of relative cohomology does not depend on the proof that the relative part of the
source is carried into the relative part of the target. -/
theorem relCohMap_hcongr (f : C(X, B)) (A : Set X) (Bb : Set B)
    {h h' : ∀ x ∈ A, f x ∈ Bb} (R : Type) [CommRing R] (n : ℕ) :
    Work.Thom.relCohMap f A Bb h R n = Work.Thom.relCohMap f A Bb h' R n := by
  show HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of X)
    (X₂ := TopCat.of B) R A Bb (TopCat.ofHom f) h) n =
    HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of X)
    (X₂ := TopCat.of B) R A Bb (TopCat.ofHom f) h') n
  rw [Work.Thom.relComplexMap_hcongrA A Bb (TopCat.ofHom f) h h' R]

/-- The inclusion of the total space `X` into the "middle" set `CMid q b` of the mapping cylinder,
as a map of pairs `(X, q ⁻¹' {b}) → (CMid q b, P)`. -/
def cylInclMid (q : C(X, B)) (b : B) : C(X, ↥(Work.Serre.CMid q b)) :=
  ⟨fun x => ⟨Work.Serre.cylIncl q x, Or.inl ⟨x, rfl⟩⟩,
    Continuous.subtype_mk (Work.Serre.cylIncl q).continuous _⟩

theorem fibrePieceRelIncl {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (hB : PathConnectedSpace B) (q : C(X, B)) (hq : Work.StemsB.IsSerreFibration q)
    (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre q b))
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) t))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (b : B) :
    (HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℚ
      (TopCat.of (Work.Serre.cyl q)) (Work.Serre.CMid q b)) (r + 1)).hom = 0 := by
  have hPC : Work.Serre.CMidPair.cylPairU q b ⊆ Work.Serre.CMid q b := by
    rw [show Work.Serre.CMid q b = Work.Serre.CMidPair.cylPairA₂ q b from rfl]
    exact Set.subset_union_right
  -- (A) the retraction `cylRetract q` is a homotopy equivalence of pairs `(M,P) ≃ (B,{b})`
  have hret : Function.Bijective (Work.Thom.relCohMap (Work.Serre.cylRetract q)
      (Work.Serre.CMidPair.cylPairU q b) ({b} : Set B) (fun y hy => hy) ℚ (r + 1)).hom := by
    refine Work.StemsB.relCohMap_pairHomotopyR ℚ (Work.Serre.CMidPair.cylPairU q b) ({b} : Set B)
      (Work.Serre.cylRetract q) (Work.Serre.cylInr q) (fun y hy => hy) ?_
      (Work.Serre.cylMoveHomotopy q) ?_ ?_ ?_ (r + 1)
    · intro y hy
      show Work.Serre.cylRetract q (Work.Serre.cylInr q y) = b
      rw [show Work.Serre.cylRetract q (Work.Serre.cylInr q y) = y from rfl]
      exact hy
    · intro t x hx
      exact Work.Serre.CMidPair.cylMove_mem_cylPairU q b hx (Work.Serre.unitIntervalOneSub t)
    · exact { toContinuousMap := ⟨fun p : unitInterval × B => p.2, continuous_snd⟩
              map_zero_left := fun y => rfl
              map_one_left := fun y => rfl }
    · intro t y hy
      exact hy
  -- (B) the relative edge map of `q` is injective in degree `r+1`
  have hqinj : Function.Injective (Work.Thom.relCohMap q (q ⁻¹' {b}) ({b} : Set B)
      (fun x hx => hx) ℚ (r + 1)).hom :=
    Work.Serre.fibrePairMapInject r N hr hrN hB q hq hvan hpc hgen b
  -- (C) the pullbacks of `cylRetract q ∘ cylIncl q = q` compose to the pullback of `q`
  have hfac : Work.Thom.relCohMap (Work.Serre.cylRetract q) (Work.Serre.CMidPair.cylPairU q b)
        ({b} : Set B) (fun y hy => hy) ℚ (r + 1)
      ≫ Work.Thom.relCohMap (Work.Serre.cylIncl q) (q ⁻¹' {b})
        (Work.Serre.CMidPair.cylPairU q b)
        (fun x hx => by
          show ((Work.Serre.cylRetract q).comp (Work.Serre.cylIncl q)) x = b
          rw [DFunLike.congr_fun (Work.Serre.cylRetract_cylIncl q) x]
          exact hx) ℚ (r + 1)
      = Work.Thom.relCohMap q (q ⁻¹' {b}) ({b} : Set B) (fun x hx => hx) ℚ (r + 1) := by
    have h := Work.Thom.relCohMap_compA (q ⁻¹' {b}) (Work.Serre.CMidPair.cylPairU q b)
      ({b} : Set B) (Work.Serre.cylIncl q) (Work.Serre.cylRetract q) (fun y hy => hy)
      (fun y hy => hy)
      (fun x hx => (fun y hy => hy) ((Work.Serre.cylIncl q) x) ((fun y hy => hy) x hx)) ℚ (r + 1)
    rw [h]
    exact relCohMap_hcongr q (q ⁻¹' {b}) ({b} : Set B) ℚ (r + 1)
  have hfaclin : (Work.Thom.relCohMap (Work.Serre.cylIncl q) (q ⁻¹' {b})
        (Work.Serre.CMidPair.cylPairU q b)
        (fun x hx => by
          show ((Work.Serre.cylRetract q).comp (Work.Serre.cylIncl q)) x = b
          rw [DFunLike.congr_fun (Work.Serre.cylRetract_cylIncl q) x]
          exact hx) ℚ (r + 1)).hom.comp
      (Work.Thom.relCohMap (Work.Serre.cylRetract q) (Work.Serre.CMidPair.cylPairU q b)
        ({b} : Set B) (fun y hy => hy) ℚ (r + 1)).hom
      = (Work.Thom.relCohMap q (q ⁻¹' {b}) ({b} : Set B) (fun x hx => hx) ℚ (r + 1)).hom := by
    have := congrArg ModuleCat.Hom.hom hfac
    simpa [ModuleCat.hom_comp] using this
  -- (D) hence the pullback along `cylIncl q` is injective
  have hinclq : Function.Injective (Work.Thom.relCohMap (Work.Serre.cylIncl q) (q ⁻¹' {b})
      (Work.Serre.CMidPair.cylPairU q b)
      (fun x hx => by
        show ((Work.Serre.cylRetract q).comp (Work.Serre.cylIncl q)) x = b
        rw [DFunLike.congr_fun (Work.Serre.cylRetract_cylIncl q) x]
        exact hx) ℚ (r + 1)).hom := by
    intro a a' haa
    obtain ⟨c, hc⟩ := hret.2 (a - a')
    have h1 : (Work.Thom.relCohMap q (q ⁻¹' {b}) ({b} : Set B)
        (fun x hx => hx) ℚ (r + 1)).hom c = 0 := by
      rw [← hfaclin, LinearMap.comp_apply, hc, map_sub, haa, sub_self]
    have h2 : c = 0 := hqinj (by rw [h1, map_zero])
    have h3 : a - a' = 0 := by rw [← hc, h2, map_zero]
    exact sub_eq_zero.mp h3
  -- (E) the restriction `H^{r+1}(M,P) → H^{r+1}(C, C∩P)` of the triple is injective
  have hrestr : Function.Injective (HomologicalComplex.homologyMap (Work.Serre.tripleRestr ℚ
      (TopCat.of (Work.Serre.cyl q)) (Work.Serre.CMidPair.cylPairU q b)
      (Work.Serre.CMid q b) hPC) (r + 1)).hom := by
    have hw : (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(Work.Serre.CMid q b), Work.Serre.cyl q)).comp (cylInclMid q b)
        = Work.Serre.cylIncl q := by
      ext x; rfl
    have key : Function.Injective (Work.Thom.relCohMap
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(Work.Serre.CMid q b), Work.Serre.cyl q))
        {x : ↥(Work.Serre.CMid q b) | (x : Work.Serre.cyl q) ∈ Work.Serre.CMidPair.cylPairU q b}
        (Work.Serre.CMidPair.cylPairU q b) (fun x hx => hx) ℚ (r + 1)).hom := by
      have hfac3 := Work.Thom.relCohMap_compA (q ⁻¹' {b})
        {x : ↥(Work.Serre.CMid q b) | (x : Work.Serre.cyl q) ∈ Work.Serre.CMidPair.cylPairU q b}
        (Work.Serre.CMidPair.cylPairU q b) (cylInclMid q b)
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(Work.Serre.CMid q b), Work.Serre.cyl q))
        (fun x hx => hx) (fun y hy => hy) (fun x hx => hx) ℚ (r + 1)
      have hfac3lin : (Work.Thom.relCohMap (cylInclMid q b) (q ⁻¹' {b})
          {x : ↥(Work.Serre.CMid q b) | (x : Work.Serre.cyl q) ∈ Work.Serre.CMidPair.cylPairU q b}
          (fun x hx => hx) ℚ (r + 1)).hom.comp
          (Work.Thom.relCohMap
            (⟨Subtype.val, continuous_subtype_val⟩ :
              C(↥(Work.Serre.CMid q b), Work.Serre.cyl q))
            {x : ↥(Work.Serre.CMid q b) |
              (x : Work.Serre.cyl q) ∈ Work.Serre.CMidPair.cylPairU q b}
            (Work.Serre.CMidPair.cylPairU q b) (fun x hx => hx) ℚ (r + 1)).hom
        = (Work.Thom.relCohMap (Work.Serre.cylIncl q) (q ⁻¹' {b})
            (Work.Serre.CMidPair.cylPairU q b)
            (fun x hx => by
              show ((Work.Serre.cylRetract q).comp (Work.Serre.cylIncl q)) x = b
              rw [DFunLike.congr_fun (Work.Serre.cylRetract_cylIncl q) x]
              exact hx) ℚ (r + 1)).hom := by
        have h : Work.Thom.relCohMap
            (⟨Subtype.val, continuous_subtype_val⟩ :
              C(↥(Work.Serre.CMid q b), Work.Serre.cyl q))
            {x : ↥(Work.Serre.CMid q b) |
              (x : Work.Serre.cyl q) ∈ Work.Serre.CMidPair.cylPairU q b}
            (Work.Serre.CMidPair.cylPairU q b) (fun x hx => hx) ℚ (r + 1)
            ≫ Work.Thom.relCohMap (cylInclMid q b) (q ⁻¹' {b})
              {x : ↥(Work.Serre.CMid q b) |
                (x : Work.Serre.cyl q) ∈ Work.Serre.CMidPair.cylPairU q b}
              (fun x hx => hx) ℚ (r + 1)
            = Work.Thom.relCohMap (Work.Serre.cylIncl q) (q ⁻¹' {b})
              (Work.Serre.CMidPair.cylPairU q b) (fun x hx => hx) ℚ (r + 1) := by
          rw [hfac3]
          exact Work.Thom.relCohMap_congrA _ _ hw _ _ ℚ (r + 1)
        have := congrArg ModuleCat.Hom.hom h
        simpa [ModuleCat.hom_comp] using this
      intro x y hxy
      apply hinclq
      rw [← hfac3lin]
      simp only [LinearMap.comp_apply, hxy]
    exact key
  -- (F) exactness of the triple sequence turns this into the vanishing of the inclusion
  have hIncl0 : (HomologicalComplex.homologyMap (Work.Serre.tripleIncl ℚ
      (TopCat.of (Work.Serre.cyl q)) (Work.Serre.CMidPair.cylPairU q b)
      (Work.Serre.CMid q b) hPC) (r + 1)).hom = 0 := by
    have hexact := Work.Serre.tripleCoh_exact₂_range ℚ (TopCat.of (Work.Serre.cyl q))
      (Work.Serre.CMidPair.cylPairU q b) (Work.Serre.CMid q b) hPC (r + 1)
    have hker : (HomologicalComplex.homologyMap (Work.Serre.tripleRestr ℚ
        (TopCat.of (Work.Serre.cyl q)) (Work.Serre.CMidPair.cylPairU q b)
        (Work.Serre.CMid q b) hPC) (r + 1)).hom.ker = ⊥ :=
      LinearMap.ker_eq_bot.mpr hrestr
    have hrange : (HomologicalComplex.homologyMap (Work.Serre.tripleIncl ℚ
        (TopCat.of (Work.Serre.cyl q)) (Work.Serre.CMidPair.cylPairU q b)
        (Work.Serre.CMid q b) hPC) (r + 1)).hom.range = ⊥ := by
      rw [hexact, hker]
    exact LinearMap.range_eq_bot.mp hrange
  -- (G) assemble: `relIncl_{M,C} = tripleIncl_{P⊆C} ≫ relIncl_{M,P}`
  have hI : Work.Serre.tripleIncl ℚ (TopCat.of (Work.Serre.cyl q))
          (Work.Serre.CMidPair.cylPairU q b) (Work.Serre.CMid q b) hPC
        ≫ Work.Cohomology.relIncl ℚ (TopCat.of (Work.Serre.cyl q))
          (Work.Serre.CMidPair.cylPairU q b)
      = Work.Cohomology.relIncl ℚ (TopCat.of (Work.Serre.cyl q)) (Work.Serre.CMid q b) := by
    apply HomologicalComplex.hom_ext
    intro n
    rw [HomologicalComplex.comp_f, Work.Serre.tripleIncl_f, Work.Cohomology.relIncl_f,
      Work.Cohomology.relIncl_f]
    rfl
  rw [← hI, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, hIncl0, LinearMap.comp_zero]

end

end Work.Stems
