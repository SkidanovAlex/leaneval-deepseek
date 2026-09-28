import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.Models
import Submission.Work.Serre.pullbackFst_piMapN_bijective
import Submission.Work.Serre.serreK2
import Submission.Work.Serre.cohMapIsoOfRatHomologyIso
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Serre.cylRelPi
import Submission.Work.StemsB.CylMapGen
import Submission.Work.StemsB.AToolsR
import Submission.Work.StemsB.PairDeltaNaturalR
import Submission.Work.StemsB.ThomRatShim
import Submission.Work.Thom.Cohomology

/-!
# Base change of the Thom-cylinder condition along a map of bases

`Work.Serre.ThomCylAt r N q` is the conclusion of the CW-model Thom case at a fixed fibration
`q : C(X,Γ)`: the pair `(cyl q, range (cylIncl q))` carries a relative class `U ∈ H^{r+1}` whose
*mixed* cup product with the pullback along the retraction `cylRetract q` is an isomorphism in the
range `m + r + 1 ≤ N + 1`.

This file proves the **base-change transfer**: if `g : B' → B` is a weak equivalence through degree
`N + 2` (bijective on `π_i` for `i ≤ N + 2` at every point) and `B'` is nonempty, then the condition
for the pullback fibration `pullbackSnd q g : Pullback q g → B'` implies the condition for `q`.

The proof is the two-out-of-three argument along the map of pairs
`Φ : (cyl (pullbackSnd q g), range (cylIncl (pullbackSnd q g))) → (cyl q, range (cylIncl q))`
induced by the pullback square (`Work.StemsB.cylMapGen`).

* `Φ` is compatible with the retractions (`cylRetract q ∘ Φ = g ∘ cylRetract (pullbackSnd q g)`),
  so `CohMap Φ` is an isomorphism in degrees `≤ N + 2` because `g` is (`serreK2`).
* the *relative* pullback `relCohMap Φ` is bijective in degrees `1 ≤ m ≤ N + 1`.  This is the
  content of the pair long exact sequences: the two outer vertical maps of the ladder
  `(cyl q, A) → (cyl q', A')` are isomorphisms in a range — on the total spaces because
  `cylRetract` is a homotopy equivalence (`cylHomotopyEquivExplicit`), and on the subspaces
  because the induced map `A' → A` is `pullbackFst q g` up to the bottom-copy homeomorphisms
  `cylHomeoExplicit`, and `pullbackFst q g` is a rational cohomology isomorphism in degrees
  `≤ N + 1` by `pullbackFst_piMapN_bijective` + `serreK2`.  The elementary diagram chase that
  converts this into bijectivity of the relative map — one degree better than the naive five
  lemma, and exactly what the range `N + 2` buys — is `relCohMap_pullbackCylMap_bijective`.
* the transport of the cup-map property is the naturality of the mixed cup product
  (`mixedCupC_pairNaturalR`) together with the fact that `CohMap g` is an isomorphism in the
  degrees used.

The `N + 2` in the hypothesis is calibrated: the outer verticals are needed in degree `N + 1`.

## Why the transfers are stated via `IsIso` of `CohMap`

Everything is with `ℚ` coefficients, so a rational homology isomorphism is a rational cohomology
isomorphism in the same degree (`Work.Serre.cohMapIsoOfRatHomologyIso`).
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval Simplicial

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-! ## The pullback along the retraction of a mapping cylinder -/

/-- **`cylRetract p` induces an isomorphism on cohomology** (it is a homotopy equivalence,
`Work.Serre.cylHomotopyEquivExplicit`). -/
theorem isIso_cohMap_cylRetract {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (n : ℕ) : IsIso (Work.Thom.CohMap (cylRetract p) ℚ n) := by
  obtain ⟨he, hhe⟩ := cylHomotopyEquivExplicit p
  rw [← hhe]
  exact cohMapIsoOfRatHomologyIso he.toFun n (IsRatHomologyIso.of_homotopyEquiv he n)

/-! ## The map of mapping cylinders induced by the pullback square -/

section CylMap

variable {B' B X : Type} [TopologicalSpace B'] [TopologicalSpace B] [TopologicalSpace X]

/-- **The map of mapping cylinders induced by the pullback square** of `q` along `g`.  It is the
identity on the interval coordinate, `pullbackFst q g` on the source and `g` on the targets:
`Φ (u, t) = (pullbackFst q g u, t)` and `Φ b' = g b'`. -/
def pullbackCylMap (g : C(B', B)) (q : C(X, B)) :
    C(cyl (Work.StemsB.pullbackSnd q g), cyl q) :=
  Work.StemsB.cylMapGen (Work.StemsB.pullbackSnd q g) q (Work.StemsB.pullbackFst q g) g
    (fun u => (u.2).symm)

/-- `Φ` is compatible with the bottom copies. -/
theorem pullbackCylMap_cylIncl (g : C(B', B)) (q : C(X, B))
    (u : Work.StemsB.Pullback q g) :
    pullbackCylMap g q (cylIncl (Work.StemsB.pullbackSnd q g) u) =
      cylIncl q (Work.StemsB.pullbackFst q g u) :=
  congrFun (congrArg DFunLike.coe (Work.StemsB.cylIncl_comp_cylMapGen
    (Work.StemsB.pullbackSnd q g) q (Work.StemsB.pullbackFst q g) g (fun u => (u.2).symm))) u

/-- `Φ` is compatible with the retractions: `cylRetract q ∘ Φ = g ∘ cylRetract (pullbackSnd q g)`.
-/
theorem pullbackCylMap_retract (g : C(B', B)) (q : C(X, B)) :
    (cylRetract q).comp (pullbackCylMap g q) =
      g.comp (cylRetract (Work.StemsB.pullbackSnd q g)) :=
  Work.StemsB.cylRetract_comp_cylMapGen
    (Work.StemsB.pullbackSnd q g) q (Work.StemsB.pullbackFst q g) g (fun u => (u.2).symm)

theorem pullbackCylMap_retract_apply (g : C(B', B)) (q : C(X, B))
    (y : cyl (Work.StemsB.pullbackSnd q g)) :
    cylRetract q (pullbackCylMap g q y) =
      g (cylRetract (Work.StemsB.pullbackSnd q g) y) :=
  congrFun (congrArg DFunLike.coe (pullbackCylMap_retract g q)) y

/-- `Φ` carries the bottom copy of the source into the bottom copy of the target. -/
theorem pullbackCylMap_mapsTo (g : C(B', B)) (q : C(X, B))
    (y : cyl (Work.StemsB.pullbackSnd q g))
    (hy : y ∈ Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) :
    pullbackCylMap g q y ∈ Set.range (cylIncl q) := by
  obtain ⟨u, rfl⟩ := hy
  exact ⟨Work.StemsB.pullbackFst q g u, pullbackCylMap_cylIncl g q u⟩

end CylMap


/-! ## Elementary helpers -/

-- NOTE (area-owner fix, 2026-09-27): a local `abbrev subIncl {F} [TopologicalSpace F] (A : Set F) :
-- C(↥A, F)` used to be declared here (unused in this file).  It clashed with
-- `Work.Serre.subIncl` of `Submission/Work/Serre/TripleCohDefs.lean`, which made this module
-- *unimportable together with the triple LES* (`environment already contains
-- 'Work.Serre.subIncl._proof_1'`) — in particular `Submission/Work/Serre/All.lean` failed to build.
-- The duplicate has been deleted; the canonical one is the one in `TripleCohDefs.lean`.

/-- **The restriction of a map of pairs to the subspaces.** -/
def apartMap {F F' : Type} [TopologicalSpace F] [TopologicalSpace F'] (φ : C(F, F'))
    (A : Set F) (A' : Set F') (h : ∀ x ∈ A, φ x ∈ A') : C(↥A, ↥A') where
  toFun a := ⟨φ a.1, h a.1 a.2⟩
  continuous_toFun :=
    Continuous.subtype_mk (φ.continuous.comp continuous_subtype_val) (fun a => h a.1 a.2)

@[simp] theorem apartMap_coe {F F' : Type} [TopologicalSpace F] [TopologicalSpace F']
    (φ : C(F, F')) (A : Set F) (A' : Set F') (h : ∀ x ∈ A, φ x ∈ A') (a : ↥A) :
    ((apartMap φ A A' h a : ↥A') : F') = φ a.1 := rfl

/-- **A homeomorphism induces an isomorphism on cohomology.** -/
theorem isIso_CohMap_of_homeo_weakEquiv {F F' : Type} [TopologicalSpace F] [TopologicalSpace F']
    (e : F ≃ₜ F') (R : Type) [CommRing R] (n : ℕ) :
    IsIso (Work.Thom.CohMap (e : C(F, F')) R n) := by
  have h1 : (e : C(F, F')).comp (e.symm : C(F', F)) = ContinuousMap.id F' :=
    ContinuousMap.ext fun x => e.apply_symm_apply x
  have h2 : (e.symm : C(F', F)).comp (e : C(F, F')) = ContinuousMap.id F :=
    ContinuousMap.ext fun x => e.symm_apply_apply x
  refine IsIso.mk ⟨Work.Thom.CohMap (e.symm : C(F', F)) R n, ?_, ?_⟩
  · rw [← Work.Thom.CohMap_comp (f := (e.symm : C(F', F))) (g := (e : C(F, F'))), h1,
      Work.Thom.CohMap_id]
  · rw [← Work.Thom.CohMap_comp (f := (e : C(F, F'))) (g := (e.symm : C(F', F))), h2,
      Work.Thom.CohMap_id]

/-! ## `CohMap` of the cylinder map, from `CohMap g` -/

variable {B' B X : Type} [TopologicalSpace B'] [TopologicalSpace B] [TopologicalSpace X]

theorem isIso_cohMap_pullbackCylMap (g : C(B', B)) (q : C(X, B)) (n : ℕ)
    (h : IsIso (Work.Thom.CohMap g ℚ n)) :
    IsIso (Work.Thom.CohMap (pullbackCylMap g q) ℚ n) := by
  have heq : Work.Thom.CohMap (cylRetract q) ℚ n ≫
      Work.Thom.CohMap (pullbackCylMap g q) ℚ n =
      Work.Thom.CohMap g ℚ n ≫
        Work.Thom.CohMap (cylRetract (Work.StemsB.pullbackSnd q g)) ℚ n := by
    rw [← Work.Thom.CohMap_comp (f := pullbackCylMap g q) (g := cylRetract q),
      ← Work.Thom.CohMap_comp (f := cylRetract (Work.StemsB.pullbackSnd q g)) (g := g),
      pullbackCylMap_retract g q]
  haveI hq_ret : IsIso (Work.Thom.CohMap (cylRetract q) ℚ n) := isIso_cohMap_cylRetract q n
  haveI hq_ret' : IsIso (Work.Thom.CohMap
      (cylRetract (Work.StemsB.pullbackSnd q g)) ℚ n) :=
    isIso_cohMap_cylRetract (Work.StemsB.pullbackSnd q g) n
  haveI hcomp : IsIso (Work.Thom.CohMap (cylRetract q) ℚ n ≫
      Work.Thom.CohMap (pullbackCylMap g q) ℚ n) := by
    rw [heq]; exact IsIso.comp_isIso
  exact IsIso.of_isIso_comp_left (Work.Thom.CohMap (cylRetract q) ℚ n)
    (Work.Thom.CohMap (pullbackCylMap g q) ℚ n)

/-! ## The subspace map: `pullbackFst q g` up to the bottom-copy homeomorphisms -/

section Bottom

/-- The bottom-copy homeomorphism of a mapping cylinder. -/
def cylBotHomeo {P X : Type} [TopologicalSpace P] [TopologicalSpace X] (f : C(P, X)) :
    P ≃ₜ ↥(Set.range (cylIncl f)) := Classical.choose (cylHomeoExplicit f)

theorem cylBotHomeo_spec {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (f : C(P, X)) (p : P) :
    ((cylBotHomeo f p : ↥(Set.range (cylIncl f))) : cyl f) = cylIncl f p :=
  Classical.choose_spec (cylHomeoExplicit f) p

/-- The bottom-copy homeomorphism, as a continuous map (so that `Work.Thom.CohMap_comp`
applies to it directly). -/
abbrev cylBotHomeoC {P X : Type} [TopologicalSpace P] [TopologicalSpace X] (f : C(P, X)) :
    C(P, ↥(Set.range (cylIncl f))) := (cylBotHomeo f : _)

/-- **The subspace map of the pair map `Φ` is `pullbackFst q g` under the bottom-copy
homeomorphisms** (pointwise form). -/
theorem apartMap_pullbackCylMap_botHomeo (g : C(B', B)) (q : C(X, B))
    (u : Work.StemsB.Pullback q g) :
    (apartMap (pullbackCylMap g q) (Set.range (cylIncl (Work.StemsB.pullbackSnd q g)))
      (Set.range (cylIncl q)) (pullbackCylMap_mapsTo g q))
        (cylBotHomeo (Work.StemsB.pullbackSnd q g) u)
      = cylBotHomeo q (Work.StemsB.pullbackFst q g u) := by
  apply Subtype.ext
  show pullbackCylMap g q ((cylBotHomeo (Work.StemsB.pullbackSnd q g) u :
      ↥(Set.range (cylIncl (Work.StemsB.pullbackSnd q g)))) :
        cyl (Work.StemsB.pullbackSnd q g)) =
    ((cylBotHomeo q (Work.StemsB.pullbackFst q g u) : ↥(Set.range (cylIncl q))) : cyl q)
  rw [cylBotHomeo_spec, cylBotHomeo_spec, pullbackCylMap_cylIncl]

/-- The same identity, as an equality of continuous maps. -/
theorem apartMap_pullbackCylMap_comp_botHomeo (g : C(B', B)) (q : C(X, B)) :
    (apartMap (pullbackCylMap g q) (Set.range (cylIncl (Work.StemsB.pullbackSnd q g)))
        (Set.range (cylIncl q)) (pullbackCylMap_mapsTo g q)).comp
      (cylBotHomeoC (Work.StemsB.pullbackSnd q g))
      = (cylBotHomeoC q).comp (Work.StemsB.pullbackFst q g) := by
  apply ContinuousMap.ext
  intro u
  exact apartMap_pullbackCylMap_botHomeo g q u

end Bottom

/-- The subspace map of the pair map `Φ`. -/
abbrev apartPullbackCylMap {B' B X : Type} [TopologicalSpace B'] [TopologicalSpace B]
    [TopologicalSpace X] (g : C(B', B)) (q : C(X, B)) :
    C(↥(Set.range (cylIncl (Work.StemsB.pullbackSnd q g))), ↥(Set.range (cylIncl q))) :=
  apartMap (pullbackCylMap g q) (Set.range (cylIncl (Work.StemsB.pullbackSnd q g)))
    (Set.range (cylIncl q)) (pullbackCylMap_mapsTo g q)

/-- The key identity transporting the subspace map of `Φ` to `pullbackFst q g`. -/
theorem cohMap_apartPullbackCylMap_comp_botHomeo (g : C(B', B)) (q : C(X, B)) (m : ℕ) :
    Work.Thom.CohMap (apartPullbackCylMap g q) ℚ m ≫
      Work.Thom.CohMap (cylBotHomeoC (Work.StemsB.pullbackSnd q g)) ℚ m =
      Work.Thom.CohMap (cylBotHomeoC q) ℚ m ≫
        Work.Thom.CohMap (Work.StemsB.pullbackFst q g) ℚ m := by
  rw [← Work.Thom.CohMap_comp (f := cylBotHomeoC (Work.StemsB.pullbackSnd q g))
      (g := apartPullbackCylMap g q),
    ← Work.Thom.CohMap_comp (f := Work.StemsB.pullbackFst q g) (g := cylBotHomeoC q)]
  congr 1
  exact apartMap_pullbackCylMap_comp_botHomeo g q


/-! ## The cohomology of an empty space -/

theorem isEmpty_singularSimplex_of_isEmpty (Y : TopCat) [IsEmpty (↥Y)] (n : ℕ) :
    IsEmpty ((TopCat.toSSet.obj Y).obj (Opposite.op ⦋n⦌)) := by
  refine ⟨fun x => ?_⟩
  have hx := (TopCat.toSSetObjEquivT Y (Opposite.op ⦋n⦌)) x
  haveI : Nonempty (↑(stdSimplex ℝ (Fin ((Opposite.unop (Opposite.op ⦋n⦌)).len + 1)))) :=
    inferInstance
  exact isEmptyElim (hx (Classical.arbitrary _))

theorem isZero_singularChains_rat_of_isEmpty_weakEquiv (Y : TopCat) [IsEmpty (↥Y)] (n : ℕ) :
    IsZero ((Work.Cohomology.singularChains ℚ Y).X n) := by
  haveI := isEmpty_singularSimplex_of_isEmpty Y n
  exact Work.Cohomology.isZero_coproduct_of_isEmpty
    (fun _ : ((TopCat.toSSet.obj Y).obj (Opposite.op ⦋n⦌)) => ModuleCat.of ℚ ℚ)

theorem isZero_singularCochainComplex_rat_of_isEmpty (Y : TopCat) [IsEmpty (↥Y)] (n : ℕ) :
    IsZero ((Work.Cohomology.singularCochainComplex ℚ Y).X n) := by
  rw [← Work.Cohomology.dualComplex_singularChains ℚ Y, Work.Cohomology.dualComplex_X]
  exact Work.Cohomology.isZero_dualObj_of_isZero ℚ (Work.Cohomology.singularChains ℚ Y)
    (fun m => isZero_singularChains_rat_of_isEmpty_weakEquiv Y m) n

theorem isZero_homology_of_isZero_X {K : CochainComplex (ModuleCat ℚ) ℕ} (m : ℕ)
    (h : IsZero (K.X m)) : IsZero (K.homology m) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ h

/-- **The cohomology of an empty space vanishes in every degree.** -/
theorem isZero_coh_of_isEmpty_type {Y : Type} [TopologicalSpace Y] [IsEmpty Y] (n : ℕ) :
    IsZero (Work.Thom.Coh ℚ n Y) :=
  isZero_homology_of_isZero_X n (isZero_singularCochainComplex_rat_of_isEmpty (TopCat.of Y) n)

/-- **If the pullback of a Serre fibration along a `π₀`-surjective map is empty, then the total
space is empty.** -/
theorem isEmpty_of_isEmpty_pullback {B' B X : Type} [TopologicalSpace B'] [TopologicalSpace B]
    [TopologicalSpace X] (g : C(B', B)) (q : C(X, B)) (hq : Work.StemsB.IsSerreFibration q)
    (hB' : Nonempty B')
    (hg0 : ∀ x : B', Function.Bijective (Work.Serre.piMapN g 0 x))
    (hP : IsEmpty (Work.StemsB.Pullback q g)) : IsEmpty X := by
  refine ⟨fun x => ?_⟩
  obtain ⟨b'₀⟩ := hB'
  obtain ⟨b', ⟨γ⟩⟩ := exists_path_of_piMapN_zero_surjective g b'₀ (hg0 b'₀).2 (q x)
  obtain ⟨x', hx', _⟩ := exists_path_lift_of_isSerreFibration q hq rfl γ
  exact hP.elim ⟨(x', b'), hx'⟩

/-- **`pullbackFst q g` induces a rational cohomology isomorphism in degrees `≤ N + 1`.** -/
theorem isIso_cohMap_pullbackFst_of_le {B' B X : Type} [TopologicalSpace B'] [TopologicalSpace B]
    [TopologicalSpace X] (g : C(B', B)) (q : C(X, B))
    (hq : Work.StemsB.IsSerreFibration q) (N : ℕ) (hB' : Nonempty B')
    (hg : ∀ i : ℕ, i ≤ N + 2 → ∀ x : B', Function.Bijective (Work.Serre.piMapN g i x))
    (m : ℕ) (hm : m ≤ N + 1) :
    IsIso (Work.Thom.CohMap (Work.StemsB.pullbackFst q g) ℚ m) := by
  by_cases hne : Nonempty (Work.StemsB.Pullback q g)
  · have hbij : ∀ i : ℕ, i < N + 2 → ∀ x : Work.StemsB.Pullback q g,
        Function.Bijective (Work.Serre.piMapN (Work.StemsB.pullbackFst q g) i x) :=
      Work.Serre.pullbackFst_piMapN_bijective q g hq (N + 2) hg
    haveI : IsIso (ratHomologyMap (Work.StemsB.pullbackFst q g) m) :=
      serreK2 (Work.StemsB.Pullback q g) X (Work.StemsB.pullbackFst q g) (N + 2) hbij m
        (by omega)
    exact cohMapIsoOfRatHomologyIso (Work.StemsB.pullbackFst q g) m inferInstance
  · have hP : IsEmpty (Work.StemsB.Pullback q g) := not_nonempty_iff.mp hne
    have hX : IsEmpty X := isEmpty_of_isEmpty_pullback g q hq hB' (hg 0 (by omega)) hP
    haveI h1 : Subsingleton ↥(Work.Thom.Coh ℚ m X) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_coh_of_isEmpty_type (Y := X) m)
    haveI h2 : Subsingleton ↥(Work.Thom.Coh ℚ m (Work.StemsB.Pullback q g)) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (isZero_coh_of_isEmpty_type (Y := Work.StemsB.Pullback q g) m)
    exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ _⟩⟩

/-- **The subspace map of the pair map `Φ` induces a rational cohomology isomorphism in degrees
`≤ N + 1`.**  Under the bottom-copy homeomorphisms it is `pullbackFst q g`. -/
theorem isIso_cohMap_apartMap_of_le {B' B X : Type} [TopologicalSpace B'] [TopologicalSpace B]
    [TopologicalSpace X] (g : C(B', B)) (q : C(X, B))
    (hq : Work.StemsB.IsSerreFibration q) (N : ℕ) (hB' : Nonempty B')
    (hg : ∀ i : ℕ, i ≤ N + 2 → ∀ x : B', Function.Bijective (Work.Serre.piMapN g i x))
    (m : ℕ) (hm : m ≤ N + 1) :
    IsIso (Work.Thom.CohMap (apartPullbackCylMap g q) ℚ m) := by
  haveI h1 : IsIso (Work.Thom.CohMap (cylBotHomeoC q) ℚ m) :=
    isIso_CohMap_of_homeo_weakEquiv (cylBotHomeo q) ℚ m
  haveI h2 : IsIso (Work.Thom.CohMap (Work.StemsB.pullbackFst q g) ℚ m) :=
    isIso_cohMap_pullbackFst_of_le g q hq N hB' hg m hm
  haveI h3 : IsIso (Work.Thom.CohMap (cylBotHomeoC (Work.StemsB.pullbackSnd q g)) ℚ m) :=
    isIso_CohMap_of_homeo_weakEquiv (cylBotHomeo (Work.StemsB.pullbackSnd q g)) ℚ m
  haveI h4 : IsIso (Work.Thom.CohMap (apartPullbackCylMap g q) ℚ m ≫
      Work.Thom.CohMap (cylBotHomeoC (Work.StemsB.pullbackSnd q g)) ℚ m) := by
    rw [cohMap_apartPullbackCylMap_comp_botHomeo g q m]; exact IsIso.comp_isIso
  exact IsIso.of_isIso_comp_right (Work.Thom.CohMap (apartPullbackCylMap g q) ℚ m)
    (Work.Thom.CohMap (cylBotHomeoC (Work.StemsB.pullbackSnd q g)) ℚ m)


/-! ## The pair long exact sequence chase -/

section Chase

variable {B' B X : Type} [TopologicalSpace B'] [TopologicalSpace B] [TopologicalSpace X]
variable (g : C(B', B)) (q : C(X, B))

/-- **Naturality of the forgetful map** on the two pairs of the ladder. -/
theorem chase_natRelToAbs (n : ℕ)
    (z : Work.Thom.RelCoh ℚ (n + 1) (cyl q) (Set.range (cylIncl q))) :
    (Work.Thom.relToAbs ℚ (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (n + 1)).hom
        ((Work.Thom.relCohMap (pullbackCylMap g q) (Set.range (cylIncl (Work.StemsB.pullbackSnd q g)))
          (Set.range (cylIncl q)) (pullbackCylMap_mapsTo g q) ℚ (n + 1)).hom z) =
      (Work.Thom.CohMap (pullbackCylMap g q) ℚ (n + 1)).hom
        ((Work.Thom.relToAbs ℚ (Set.range (cylIncl q)) (n + 1)).hom z) := by
  have h := Work.Thom.relCohMap_relToAbs (pullbackCylMap g q)
    (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (Set.range (cylIncl q))
    (pullbackCylMap_mapsTo g q) ℚ (n + 1)
  have h2 := congrArg (fun F => ModuleCat.Hom.hom F z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- **Naturality of the connecting homomorphism** on the two pairs of the ladder. -/
theorem chase_natDelta (n : ℕ) (z : Work.Thom.Coh ℚ n (Set.range (cylIncl q))) :
    (Work.Thom.relCohMap (pullbackCylMap g q) (Set.range (cylIncl (Work.StemsB.pullbackSnd q g)))
        (Set.range (cylIncl q)) (pullbackCylMap_mapsTo g q) ℚ (n + 1)).hom
      ((Work.StemsB.pairδCR ℚ (Set.range (cylIncl q)) n).hom z) =
    (Work.StemsB.pairδCR ℚ (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) n).hom
      ((Work.Thom.CohMap (apartPullbackCylMap g q) ℚ n).hom z) :=
  Work.StemsB.pairDeltaNaturalR ℚ (pullbackCylMap g q) (Set.range (cylIncl (Work.StemsB.pullbackSnd q g)))
    (Set.range (cylIncl q)) (pullbackCylMap_mapsTo g q) n z

/-- The subspace inclusion of the source pair composed with the subspace map of `Φ` is `Φ`
composed with the subspace inclusion of the target pair. -/
theorem subIncl_comp_apartPullbackCylMap :
    (Work.Thom.subtypeMap (Set.range (cylIncl q))).comp (apartPullbackCylMap g q) =
      (pullbackCylMap g q).comp
        (Work.Thom.subtypeMap (Set.range (cylIncl (Work.StemsB.pullbackSnd q g)))) := by
  apply ContinuousMap.ext
  intro a
  rfl

/-- **Naturality of the restriction to the subspaces** on the two pairs of the ladder. -/
theorem chase_natSubtype (n : ℕ) (z : Work.Thom.Coh ℚ n (cyl q)) :
    (Work.Thom.CohMap (Work.Thom.subtypeMap (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))))
        ℚ n).hom ((Work.Thom.CohMap (pullbackCylMap g q) ℚ n).hom z) =
      (Work.Thom.CohMap (apartPullbackCylMap g q) ℚ n).hom
        ((Work.Thom.CohMap (Work.Thom.subtypeMap (Set.range (cylIncl q))) ℚ n).hom z) := by
  have h := congrArg (fun (w : C(↥(Set.range (cylIncl (Work.StemsB.pullbackSnd q g))), cyl q)) =>
      (Work.Thom.CohMap w ℚ n).hom z) (subIncl_comp_apartPullbackCylMap g q)
  rw [Work.Thom.CohMap_comp (f := apartPullbackCylMap g q)
        (g := Work.Thom.subtypeMap (Set.range (cylIncl q))),
      Work.Thom.CohMap_comp (f := Work.Thom.subtypeMap (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))))
        (g := pullbackCylMap g q)] at h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h.symm

/-- **The relative pullback along `Φ` is bijective in every degree `1 ≤ m ≤ K`** as soon as the two
outer vertical maps of the pair ladder are bijective up to degrees `K` and `K + 1` respectively.

This is the elementary diagram chase of the two long exact sequences of the pairs
`(cyl q, A)` and `(cyl q', A')`, done *by hand* rather than by the five lemma: the five lemma
applied to the four-term ladder would consume the outer isomorphisms one degree higher than
necessary, and the range here is sharp (the hypotheses are needed in degrees `≤ K` resp. `≤ K+1`).
The two halves of the chase are:

* injectivity: if `β z = 0` then `γ (i z) = 0`, so `i z = 0`, so `z = δ y`; then
  `δ' (φ_A^* y) = 0`, so `φ_A^* y = j' w`; writing `w = γ u` and using `j'γ = φ_A^* j` gives
  `φ_A^* y = φ_A^*(j u)`, so `y = j u` and `z = δ (j u) = 0`;
* surjectivity: given `s`, write `i' s = γ z`; then `j'(i's) = 0` gives `φ_A^*(j z) = 0`, so `j z = 0`
  and `z = i x₀`; the difference `s - β x₀` lies in `im δ'`, say `δ' t`, and `t = φ_A^* y`; hence
  `s = β (x₀ + δ y)`. -/
theorem relCohMap_pullbackCylMap_bijective (K : ℕ)
    (hA : ∀ m, m ≤ K → Function.Bijective
      (Work.Thom.CohMap (apartPullbackCylMap g q) ℚ m).hom)
    (hG : ∀ m, m ≤ K + 1 → Function.Bijective
      (Work.Thom.CohMap (pullbackCylMap g q) ℚ m).hom) :
    ∀ m, 1 ≤ m → m ≤ K → Function.Bijective
      (Work.Thom.relCohMap (pullbackCylMap g q)
        (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (Set.range (cylIncl q))
        (pullbackCylMap_mapsTo g q) ℚ m).hom := by
  intro m hm1 hmK
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hn1 : n ≤ K := by omega
  have hn2 : n + 1 ≤ K := by omega
  have hnK1 : n ≤ K + 1 := by omega
  have hn2K1 : n + 1 ≤ K + 1 := by omega
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · -- ## injectivity
    rw [← sub_eq_zero]
    have hz : (Work.Thom.relCohMap (pullbackCylMap g q)
        (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (Set.range (cylIncl q))
        (pullbackCylMap_mapsTo g q) ℚ (n + 1)).hom (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    have h1 : (Work.Thom.relToAbs ℚ (Set.range (cylIncl q)) (n + 1)).hom (a - b) = 0 := by
      have h := chase_natRelToAbs g q n (a - b)
      rw [hz] at h
      rw [map_zero] at h
      exact (hG (n + 1) hn2K1).1 (by rw [← h, map_zero])
    obtain ⟨y, hy⟩ : ∃ y, (Work.StemsB.pairδCR ℚ (Set.range (cylIncl q)) n).hom y = a - b := by
      have hmem : (a - b) ∈ LinearMap.range
          ((Work.StemsB.pairδCR ℚ (Set.range (cylIncl q)) n)).hom := by
        rw [Work.StemsB.pairKer₁R ℚ (Set.range (cylIncl q)) n]
        exact LinearMap.mem_ker.mpr h1
      exact LinearMap.mem_range.mp hmem
    have h3 : (Work.StemsB.pairδCR ℚ
        (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) n).hom
        ((Work.Thom.CohMap (apartPullbackCylMap g q) ℚ n).hom y) = 0 := by
      have h := chase_natDelta g q n y
      rw [hy] at h
      rw [hz] at h
      exact h.symm
    obtain ⟨w, hw⟩ : ∃ w, (Work.Thom.CohMap
        (Work.Thom.subtypeMap (Set.range (cylIncl (Work.StemsB.pullbackSnd q g)))) ℚ n).hom w =
        (Work.Thom.CohMap (apartPullbackCylMap g q) ℚ n).hom y := by
      have hmem : (Work.Thom.CohMap (apartPullbackCylMap g q) ℚ n).hom y ∈ LinearMap.range
          ((Work.Thom.CohMap (Work.Thom.subtypeMap
            (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))))) ℚ n).hom := by
        rw [← Work.StemsB.pairKer₃R ℚ (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) n]
        exact LinearMap.mem_ker.mpr h3
      exact LinearMap.mem_range.mp hmem
    obtain ⟨u, hu⟩ := (hG n hnK1).2 w
    have h6 : y = (Work.Thom.CohMap (Work.Thom.subtypeMap (Set.range (cylIncl q))) ℚ n).hom u :=
      (hA n hn1).1 (by rw [← hw, ← hu, chase_natSubtype g q n u])
    rw [← hy, h6]
    have h8 : (Work.Thom.CohMap (Work.Thom.subtypeMap (Set.range (cylIncl q))) ℚ n).hom u
        ∈ LinearMap.range ((Work.Thom.CohMap
          (Work.Thom.subtypeMap (Set.range (cylIncl q)))) ℚ n).hom :=
      LinearMap.mem_range.mpr ⟨u, rfl⟩
    rw [← Work.StemsB.pairKer₃R ℚ (Set.range (cylIncl q)) n] at h8
    exact LinearMap.mem_ker.mp h8
  · -- ## surjectivity
    obtain ⟨z, hz⟩ := (hG (n + 1) hn2K1).2
      ((Work.Thom.relToAbs ℚ (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (n + 1)).hom y)
    have h2 : (Work.Thom.CohMap (Work.Thom.subtypeMap
        (Set.range (cylIncl (Work.StemsB.pullbackSnd q g)))) ℚ (n + 1)).hom
        ((Work.Thom.relToAbs ℚ (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (n + 1)).hom y)
        = 0 := by
      have hmem : (Work.Thom.relToAbs ℚ
          (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (n + 1)).hom y ∈ LinearMap.range
          ((Work.Thom.relToAbs ℚ
            (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (n + 1))).hom :=
        LinearMap.mem_range.mpr ⟨y, rfl⟩
      rw [Work.StemsB.pairKer₂R ℚ
        (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (n + 1)] at hmem
      exact LinearMap.mem_ker.mp hmem
    have h3 : (Work.Thom.CohMap (Work.Thom.subtypeMap (Set.range (cylIncl q))) ℚ (n + 1)).hom z
        = 0 :=
      (hA (n + 1) hn2).1 (by rw [map_zero, ← chase_natSubtype g q (n + 1) z, hz, h2])
    obtain ⟨x0, hx0⟩ : ∃ x0, (Work.Thom.relToAbs ℚ (Set.range (cylIncl q)) (n + 1)).hom x0 = z := by
      have hmem : z ∈ LinearMap.range
          ((Work.Thom.relToAbs ℚ (Set.range (cylIncl q)) (n + 1))).hom := by
        rw [Work.StemsB.pairKer₂R ℚ (Set.range (cylIncl q)) (n + 1)]
        exact LinearMap.mem_ker.mpr h3
      exact LinearMap.mem_range.mp hmem
    have h5 : (Work.Thom.relToAbs ℚ
        (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (n + 1)).hom
        ((Work.Thom.relCohMap (pullbackCylMap g q)
          (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (Set.range (cylIncl q))
          (pullbackCylMap_mapsTo g q) ℚ (n + 1)).hom x0) =
        (Work.Thom.relToAbs ℚ
          (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (n + 1)).hom y := by
      rw [chase_natRelToAbs g q n x0, hx0, hz]
    obtain ⟨t, ht⟩ : ∃ t, (Work.StemsB.pairδCR ℚ
        (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) n).hom t =
        y - (Work.Thom.relCohMap (pullbackCylMap g q)
          (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (Set.range (cylIncl q))
          (pullbackCylMap_mapsTo g q) ℚ (n + 1)).hom x0 := by
      have hmem : (y - (Work.Thom.relCohMap (pullbackCylMap g q)
          (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (Set.range (cylIncl q))
          (pullbackCylMap_mapsTo g q) ℚ (n + 1)).hom x0) ∈ LinearMap.range
          ((Work.StemsB.pairδCR ℚ
            (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) n)).hom := by
        rw [Work.StemsB.pairKer₁R ℚ (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) n]
        exact LinearMap.mem_ker.mpr (by rw [map_sub, h5, sub_self])
      exact LinearMap.mem_range.mp hmem
    obtain ⟨y', hy'⟩ := (hA n hn1).2 t
    refine ⟨x0 + (Work.StemsB.pairδCR ℚ (Set.range (cylIncl q)) n).hom y', ?_⟩
    rw [map_add, chase_natDelta g q n y', hy', ht]
    abel

end Chase


/-! ## The naturality of the mixed cup product along the pair map -/

/-- The composite `(cylRetract q)^*` followed by `Φ^*` is `g^*` followed by `(cylRetract q')^*`. -/
theorem cohMap_cylRetract_comp_pullbackCylMap (g : C(B', B)) (q : C(X, B)) (m : ℕ) :
    (Work.Thom.CohMap (cylRetract q) ℚ m) ≫ (Work.Thom.CohMap (pullbackCylMap g q) ℚ m) =
      (Work.Thom.CohMap g ℚ m) ≫
        (Work.Thom.CohMap (cylRetract (Work.StemsB.pullbackSnd q g)) ℚ m) := by
  rw [← Work.Thom.CohMap_comp (f := pullbackCylMap g q) (g := cylRetract q),
    ← Work.Thom.CohMap_comp (f := cylRetract (Work.StemsB.pullbackSnd q g)) (g := g),
    pullbackCylMap_retract g q]

/-- **Naturality of the mixed cup product along `Φ`.**  For classes `U` on the `q`-side and `U'`
on the `q'`-side with `Φ^* U = U'`, the cup maps through the two retractions correspond under
`Φ^*`. -/
theorem mixedCup_comp_pullbackCylMap (g : C(B', B)) (q : C(X, B)) (r m : ℕ)
    (U : Work.Thom.RelCoh ℚ (r + 1) (cyl q) (Set.range (cylIncl q)))
    (U' : Work.Thom.RelCoh ℚ (r + 1) (cyl (Work.StemsB.pullbackSnd q g))
      (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))))
    (hU : (Work.Thom.relCohMap (pullbackCylMap g q)
      (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (Set.range (cylIncl q))
      (pullbackCylMap_mapsTo g q) ℚ (r + 1)).hom U = U') :
    (Work.Thom.relCohMap (pullbackCylMap g q)
        (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (Set.range (cylIncl q))
        (pullbackCylMap_mapsTo g q) ℚ (m + (r + 1))).hom ∘ₗ
      ((Work.Thom.mixedCupC ℚ (Set.range (cylIncl q)) m (r + 1)).flip U ∘ₗ
        (Work.Thom.CohMap (cylRetract q) ℚ m).hom)
    = ((Work.Thom.mixedCupC ℚ (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) m
          (r + 1)).flip U' ∘ₗ
        (Work.Thom.CohMap (cylRetract (Work.StemsB.pullbackSnd q g)) ℚ m).hom) ∘ₗ
      (Work.Thom.CohMap g ℚ m).hom := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.flip_apply]
  rw [Work.StemsB.mixedCupC_pairNaturalR ℚ (pullbackCylMap g q)
      (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (Set.range (cylIncl q))
      (pullbackCylMap_mapsTo g q) m (r + 1) ((Work.Thom.CohMap (cylRetract q) ℚ m).hom x) U,
    hU]
  have hx : (Work.Thom.CohMap (pullbackCylMap g q) ℚ m).hom
      ((Work.Thom.CohMap (cylRetract q) ℚ m).hom x)
      = (Work.Thom.CohMap (cylRetract (Work.StemsB.pullbackSnd q g)) ℚ m).hom
          ((Work.Thom.CohMap g ℚ m).hom x) := by
    have hk := congrArg (fun F => ModuleCat.Hom.hom F x)
      (cohMap_cylRetract_comp_pullbackCylMap g q m)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hk
  rw [hx]

/-! ## The target -/

theorem thomCylAtOfWeakEquivBase (r N : ℕ)
    {B' B : Type} [TopologicalSpace B'] [TopologicalSpace B] (g : C(B', B))
    {X : Type} [TopologicalSpace X] (q : C(X, B)) (hq : Work.StemsB.IsSerreFibration q)
    (hB' : Nonempty B')
    (hg : ∀ i : ℕ, i ≤ N + 2 → ∀ x : B', Function.Bijective (Work.Serre.piMapN g i x)) :
    Work.Serre.ThomCylAt r N (Work.StemsB.pullbackSnd q g) →
      Work.Serre.ThomCylAt r N q := by
  intro h
  obtain ⟨U', hU'⟩ := h
  by_cases hrN : r ≤ N
  · -- ## the non-vacuous case
    haveI hneB' : Nonempty B' := hB'
    haveI hgiso : ∀ m : ℕ, m ≤ N + 2 → IsIso (Work.Thom.CohMap g ℚ m) := by
      intro m hm
      haveI : IsIso (ratHomologyMap g m) :=
        serreK2 B' B g (N + 3) (fun i hi x => hg i (by omega) x) m (by omega)
      exact cohMapIsoOfRatHomologyIso g m inferInstance
    have hA : ∀ m : ℕ, m ≤ N + 1 → Function.Bijective
        (Work.Thom.CohMap (apartPullbackCylMap g q) ℚ m).hom := fun m hm =>
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp
        (isIso_cohMap_apartMap_of_le g q hq N hB' hg m hm)
    have hG : ∀ m : ℕ, m ≤ N + 2 → Function.Bijective
        (Work.Thom.CohMap (pullbackCylMap g q) ℚ m).hom := fun m hm =>
      (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp
        (isIso_cohMap_pullbackCylMap g q m (hgiso m hm))
    have hβbij := relCohMap_pullbackCylMap_bijective g q (N + 1) hA hG
    obtain ⟨U, hU⟩ := (hβbij (r + 1) (by omega) (by omega)).2 U'
    refine ⟨U, fun m hm => ?_⟩
    have hmN2 : m ≤ N + 2 := by omega
    have hmr1 : 1 ≤ m + r + 1 := by omega
    have hmrN : m + r + 1 ≤ N + 1 := by omega
    let Fm : Work.Thom.Coh ℚ m B →ₗ[ℚ]
        Work.Thom.RelCoh ℚ (m + (r + 1)) (cyl q) (Set.range (cylIncl q)) :=
      ((Work.Thom.mixedCupC ℚ (Set.range (cylIncl q)) m (r + 1)).flip U) ∘ₗ
        (Work.Thom.CohMap (cylRetract q) ℚ m).hom
    let Fm' : Work.Thom.Coh ℚ m B' →ₗ[ℚ]
        Work.Thom.RelCoh ℚ (m + (r + 1)) (cyl (Work.StemsB.pullbackSnd q g))
          (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) :=
      ((Work.Thom.mixedCupC ℚ (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) m
          (r + 1)).flip U') ∘ₗ
        (Work.Thom.CohMap (cylRetract (Work.StemsB.pullbackSnd q g)) ℚ m).hom
    let γm : Work.Thom.Coh ℚ m B →ₗ[ℚ] Work.Thom.Coh ℚ m B' := (Work.Thom.CohMap g ℚ m).hom
    let βm : Work.Thom.RelCoh ℚ (m + (r + 1)) (cyl q) (Set.range (cylIncl q)) →ₗ[ℚ]
        Work.Thom.RelCoh ℚ (m + (r + 1)) (cyl (Work.StemsB.pullbackSnd q g))
          (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) :=
      (Work.Thom.relCohMap (pullbackCylMap g q)
        (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (Set.range (cylIncl q))
        (pullbackCylMap_mapsTo g q) ℚ (m + (r + 1))).hom
    have hcomp : βm ∘ₗ Fm = Fm' ∘ₗ γm :=
      mixedCup_comp_pullbackCylMap g q r m U U' hU
    haveI hβiso : IsIso (ModuleCat.ofHom βm) := by
      rw [show ModuleCat.ofHom βm = Work.Thom.relCohMap (pullbackCylMap g q)
          (Set.range (cylIncl (Work.StemsB.pullbackSnd q g))) (Set.range (cylIncl q))
          (pullbackCylMap_mapsTo g q) ℚ (m + (r + 1)) from ModuleCat.ofHom_hom _]
      exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mpr
        (hβbij (m + r + 1) hmr1 hmrN)
    haveI hγiso : IsIso (ModuleCat.ofHom γm) := by
      rw [show ModuleCat.ofHom γm = Work.Thom.CohMap g ℚ m from ModuleCat.ofHom_hom _]
      exact hgiso m hmN2
    haveI hF'iso : IsIso (ModuleCat.ofHom Fm') := hU' m hm
    haveI h1 : IsIso (ModuleCat.ofHom (βm ∘ₗ Fm)) := by
      rw [congrArg (fun f => ModuleCat.ofHom f) hcomp, ModuleCat.ofHom_comp]
      exact IsIso.comp_isIso
    haveI h2 : IsIso (ModuleCat.ofHom Fm ≫ ModuleCat.ofHom βm) := by
      rw [← ModuleCat.ofHom_comp]
      exact h1
    exact IsIso.of_isIso_comp_right (ModuleCat.ofHom Fm) (ModuleCat.ofHom βm)
  · -- ## the vacuous case
    refine ⟨0, fun m hm => ?_⟩
    exfalso
    omega

end

end Work.Serre
