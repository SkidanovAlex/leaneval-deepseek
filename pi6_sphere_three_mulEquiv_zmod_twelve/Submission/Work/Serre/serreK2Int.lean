import Mathlib
import Submission.Work.Serre.cubePairDefs
import Submission.Work.Serre.rangeWhiteheadInclInt
import Submission.Work.Serre.cylRelPi
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Serre.cylJoinedIncl
import Submission.Work.Serre.RangeOne.rangeWhitehead
import Submission.Work.RatHurewicz.compression_of_relPiVanishing

namespace Work.Serre

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The map induced on integral singular homology by a continuous map. -/
abbrev intHomologyMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) :
    (Work.Cohomology.singularChains ℤ (TopCat.of X)).homology n ⟶
      (Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology n :=
  HomologicalComplex.homologyMap
    (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) n

/-- Functoriality of the integral homology map. -/
theorem intHomologyMap_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    intHomologyMap (g.comp f) n = intHomologyMap f n ≫ intHomologyMap g n := by
  have h1 : Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Z)
        (TopCat.ofHom (g.comp f)) =
      Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f) ≫
        Work.Cohomology.chainMap ℤ (TopCat.of Y) (TopCat.of Z) (TopCat.ofHom g) := by
    rw [TopCat.ofHom_comp]
    exact CategoryTheory.Functor.map_comp _ _ _
  unfold intHomologyMap
  rw [h1, HomologicalComplex.homologyMap_comp]

/-- A homotopy equivalence induces an isomorphism on integral homology in every degree. -/
theorem isIso_intHomologyMap_of_homotopyEquiv {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    IsIso (intHomologyMap e.toFun n) :=
  Work.Cohomology.homologyEquiv ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom e.toFun)
    (TopCat.ofHom e.invFun) (e.left_inv.some) (e.right_inv.some) n

/-- The inclusion of a subspace, written in the two vocabularies of the workspace. -/
theorem subtypeIncl_eq_ofHom_setIncl {Y : Type} [TopologicalSpace Y] (A : Set Y) :
    Work.Cohomology.subtypeIncl (TopCat.of Y) A =
      TopCat.ofHom (Work.RatHurewicz.setIncl A) := rfl

/-- **K2, integral form** (the integral analogue of the rational `Work.Serre.RangeOne.rangeWhitehead`
and `Work.Serre.serreK2`).  If `f : X → Y` is a bijection on `πᵢ` at every base point of `X` for
all `i ≤ M` (the `i = 0` clause included), then `f` induces an isomorphism on *integral* singular
homology in degrees `0 < i < M`.

Route: replace `f` by the inclusion `cylIncl f` of `X` into its mapping cylinder (a homotopy
equivalence via `Work.Serre.cylRetract`), use `Work.Serre.cylRelPi` followed by
`Work.RatHurewicz.compression_of_relPiVanishing` to obtain `CompressRel (cyl f) (range (cylIncl f))
d` for `d ≤ M`, then apply the integral range statement `Work.Serre.rangeWhiteheadInclInt` with
`M`, and transport along the homeomorphism of the bottom copy of the cylinder.  Degree `0` is
excluded from the conclusion (the `i = 0` clause of the hypothesis is still needed: it gives
`0`-connectivity of the pair). -/
theorem serreK2Int {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    (f : C(X, Y)) (M : ℕ)
    (h : ∀ (i : ℕ), i ≤ M → ∀ x₀ : X, Function.Bijective (Work.Serre.piMapN f i x₀)) :
    ∀ i : ℕ, 0 < i → i < M →
      IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) i) := by
  intro i _hi0 hiM
  by_cases hM : M ≤ 1
  · omega
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  set n : ℕ := M - 1 with hn
  -- relative homotopy data of the cylinder inclusion, at every base point
  have hrel : ∀ x : X, ∀ k : ℕ, k ≤ n →
      Subsingleton (Work.RatHurewicz.RelHomotopyGroup (cylIncl f) x k) :=
    fun x k hk => (cylRelPi f x n (fun i hi y => h i (by omega) y)).1 k (by omega)
  -- transport to the inclusion of the set-theoretic range
  have hset : ∀ a : ↥(Set.range (cylIncl f)), ∀ k : ℕ, k ≤ n →
      Subsingleton (Work.RatHurewicz.RelHomotopyGroup
        (Work.RatHurewicz.setIncl (Set.range (cylIncl f))) a k) := by
    intro a k hk
    obtain ⟨x, hx⟩ := a.2
    have hEq : (⟨cylIncl f x, x, rfl⟩ : ↥(Set.range (cylIncl f))) = a := Subtype.ext hx
    exact hEq ▸ (RangeOne.subsingleton_relPi_range_cylIncl f x k (hrel x k hk))
  -- the pair `(cyl f, range (cylIncl f))` is `0`-connected
  have hconn : ∀ y : cyl f, ∃ a : ↥(Set.range (cylIncl f)),
      Nonempty (Path y (a : cyl f)) :=
    RangeOne.cyl_joined_range f x₀ (h 0 (by omega) x₀)
  -- compression in degrees `≤ M`
  have hcomp : ∀ d : ℕ, d ≤ M → Work.RatHurewicz.CompressRel (cyl f)
      (Set.range (cylIncl f)) d := by
    have hc := Work.RatHurewicz.compression_of_relPiVanishing (Y := cyl f)
      (A := Set.range (cylIncl f)) n hconn (fun a k hk => hset a k hk)
    intro d hd
    exact hc d (by omega)
  -- integral range statement for the inclusion of the range
  have hsetiso : ∀ t : ℕ, t < M → IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of (cyl f)) (Set.range (cylIncl f))) t) :=
    rangeWhiteheadInclInt hcomp
  -- the corestriction homeomorphism `X ≃ₜ ↥(range (cylIncl f))`
  obtain ⟨e, he⟩ := cylHomeoExplicit f
  let ecm : C(X, ↥(Set.range (cylIncl f))) := e.toHomotopyEquiv.toFun
  have hcm : (Work.RatHurewicz.setIncl (Set.range (cylIncl f))).comp ecm = cylIncl f :=
    ContinuousMap.ext (fun x => he x)
  -- the factorisation of the chain map of `cylIncl f`
  have hchain' : Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of (cyl f))
        (TopCat.ofHom ((Work.RatHurewicz.setIncl (Set.range (cylIncl f))).comp ecm)) =
      Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of ↥(Set.range (cylIncl f)))
          (TopCat.ofHom ecm) ≫
        Work.Cohomology.chainMap ℤ (TopCat.of ↥(Set.range (cylIncl f))) (TopCat.of (cyl f))
          (TopCat.ofHom (Work.RatHurewicz.setIncl (Set.range (cylIncl f)))) := by
    rw [TopCat.ofHom_comp]
    exact CategoryTheory.Functor.map_comp _ _ _
  have hchain : Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of (cyl f))
        (TopCat.ofHom (cylIncl f)) =
      Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of ↥(Set.range (cylIncl f)))
          (TopCat.ofHom ecm) ≫
        Work.Cohomology.chainMap ℤ (TopCat.of ↥(Set.range (cylIncl f))) (TopCat.of (cyl f))
          (TopCat.ofHom (Work.RatHurewicz.setIncl (Set.range (cylIncl f)))) := by
    rw [show TopCat.ofHom (cylIncl f) =
        TopCat.ofHom ((Work.RatHurewicz.setIncl (Set.range (cylIncl f))).comp ecm) from
      congrArg TopCat.ofHom hcm.symm]
    exact hchain'
  -- `cylIncl f` is an integral homology isomorphism in the range
  have hcylincl : IsIso (intHomologyMap (cylIncl f) i) := by
    have hsplit : intHomologyMap (cylIncl f) i =
        intHomologyMap ecm i ≫
          intHomologyMap (Work.RatHurewicz.setIncl (Set.range (cylIncl f))) i := by
      unfold intHomologyMap
      rw [hchain, HomologicalComplex.homologyMap_comp]
    rw [hsplit]
    have h1 : IsIso (intHomologyMap ecm i) :=
      isIso_intHomologyMap_of_homotopyEquiv e.toHomotopyEquiv i
    have h2 : IsIso (intHomologyMap (Work.RatHurewicz.setIncl (Set.range (cylIncl f))) i) :=
      hsetiso i hiM
    haveI := h1
    haveI := h2
    infer_instance
  -- `cylRetract f` is a homotopy equivalence
  have hret : IsIso (intHomologyMap (cylRetract f) i) := by
    obtain ⟨E, hE⟩ := cylHomotopyEquivExplicit f
    have h := isIso_intHomologyMap_of_homotopyEquiv E i
    rwa [hE] at h
  -- assemble
  have hff : intHomologyMap (cylIncl f) i ≫ intHomologyMap (cylRetract f) i =
      intHomologyMap f i := by
    rw [← intHomologyMap_comp (cylIncl f) (cylRetract f) i, cylRetract_cylIncl f]
  change IsIso (intHomologyMap f i)
  rw [← hff]
  haveI := hcylincl
  haveI := hret
  infer_instance

end

end Work.Serre
