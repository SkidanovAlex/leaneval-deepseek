import Mathlib
import Submission.Work.RatHurewicz.trackSetup
import Submission.Work.Cohomology.homologyContractible

/-!
# The projection of the mapping track onto the source is injective on homology

For a continuous map `inc : X → Z`, the mapping track `Track inc`
(`Submission/Work/RatHurewicz/trackSetup.lean`) is the space of pairs `(x, γ)` with `γ` a path in
`Z` ending at `inc x`.  The projection `trackProj inc : Track inc → X`, `(x,γ) ↦ x`, is a homotopy
equivalence: the section `trackSec inc` sends `x` to `(x, const (inc x))`, one has
`trackProj ∘ trackSec = id` *on the nose*, and the other composite `trackSec ∘ trackProj` is
homotopic to the identity by the explicit deformation

`H (s, (x,γ)) = (x, t ↦ γ (convexComb 1 t s))`

(collapse the path `γ` onto its endpoint `γ 1 = inc x`).  Consequently the induced map on singular
homology in every degree is an isomorphism, hence in particular injective:

`Work.RatHurewicz.injective_homologyMap_trackProj`.

This is the ingredient with which `ker(H_{n+1}(F) → H_{n+1}(X))` is identified, for `F` the
homotopy fibre of `inc`, with `ker(H_{n+1}(F) → H_{n+1}(Track inc))` in
`Work.RatHurewicz.truncationHomologyTransfer_of_serre`.
-/

open scoped Topology unitInterval
open CategoryTheory

set_option linter.style.haveILetI false

namespace Work.RatHurewicz

noncomputable section

universe u

variable {X Z : Type u} [TopologicalSpace X] [TopologicalSpace Z]

/-- **The deformation of the mapping track onto the section of its projection.**  The homotopy
sends `(s, (x,γ))` to `(x, t ↦ γ (convexComb 1 t s))`; at `s = 0` this is the constant path at
`γ 1 = inc x`, at `s = 1` it is `γ`.  Hence `trackSec inc ∘ trackProj inc` is homotopic to the
identity of `Track inc`. -/
def trackProj_trackSec_homotopy (inc : C(X, Z)) :
    TopCat.Homotopy ((TopCat.ofHom (trackProj inc)) ≫ (TopCat.ofHom (trackSec inc)))
      (𝟙 (TopCat.of (Track inc))) := by
  -- the path `t ↦ γ (convexComb 1 t s)`, as a continuous function of `(s, (x,γ), t)`
  have hΛ : Continuous fun y : (I × Track inc) × I =>
      (y.1.2).1.2 (Set.Icc.convexComb (1 : I) y.2 y.1.1) := by
    refine continuous_eval.comp (Continuous.prodMk ?_ ?_)
    · exact continuous_snd.comp (continuous_subtype_val.comp
        (continuous_snd.comp continuous_fst))
    · exact Set.Icc.continuous_convexComb_prod.comp
        (continuous_const.prodMk (continuous_snd.prodMk (continuous_fst.comp continuous_fst)))
  let Λ : C((I × Track inc) × I, Z) := ⟨_, hΛ⟩
  -- curry it to a continuous family of paths
  let cur : C(I × Track inc, C(I, Z)) := Λ.curry
  have hcur : ∀ (y : I × Track inc) (t : I),
      cur y t = (y.2).1.2 (Set.Icc.convexComb (1 : I) t y.1) := fun y t =>
    ContinuousMap.curry_apply Λ y t
  -- the paths end at `inc x`, so they define points of the track
  have hmem : ∀ y : I × Track inc, cur y 1 = inc ((y.2).1.1) := by
    intro y
    rw [hcur y 1]
    have : Set.Icc.convexComb (1 : I) (1 : I) y.1 = 1 := Set.Icc.convexComb_eq 1 y.1
    rw [this]
    exact (y.2).2
  let xc : C(I × Track inc, X) :=
    ⟨fun y => (y.2).1.1,
      continuous_fst.comp (continuous_subtype_val.comp continuous_snd)⟩
  let pc : C(I × Track inc, X × C(I, Z)) := xc.prodMk cur
  have hH'cont : Continuous fun y : I × Track inc =>
      (⟨pc y, hmem y⟩ : Track inc) := Continuous.subtype_mk pc.continuous hmem
  let H' : C(I × Track inc, Track inc) := ⟨_, hH'cont⟩
  have hzero : ∀ x : Track inc, H' (0, x) = trackSec inc (trackProj inc x) := by
    intro x
    refine Subtype.ext (Prod.ext rfl ?_)
    show cur (0, x) = ContinuousMap.const I (inc x.1.1)
    ext t
    rw [hcur (0, x) t, Set.Icc.convexComb_zero]
    exact x.2
  have hone : ∀ x : Track inc, H' (1, x) = x := by
    intro x
    refine Subtype.ext (Prod.ext rfl ?_)
    show cur (1, x) = x.1.2
    ext t
    rw [hcur (1, x) t, Set.Icc.convexComb_one]
  refine ContinuousMap.Homotopy.mk H' ?_ ?_
  · intro x
    exact (hzero x).trans rfl
  · intro x
    exact hone x

/-- **The composite `trackProj ∘ trackSec` is the identity** (it is literally the identity map),
hence homotopic to it. -/
def trackSec_trackProj_homotopy (inc : C(X, Z)) :
    TopCat.Homotopy ((TopCat.ofHom (trackSec inc)) ≫ (TopCat.ofHom (trackProj inc)))
      (𝟙 (TopCat.of X)) where
  toContinuousMap := ⟨fun p : I × X => p.2, continuous_snd⟩
  map_zero_left := fun _ => rfl
  map_one_left := fun _ => rfl

/-- **The projection of the mapping track is injective on singular homology.**  It is even a
homotopy equivalence (with inverse `trackSec inc`), so the induced map on homology is an
isomorphism. -/
theorem injective_homologyMap_trackProj {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (inc : C(X, Z)) (n : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (Work.RatHurewicz.Track inc)) (TopCat.of X)
        (TopCat.ofHom (Work.RatHurewicz.trackProj inc))) n) := by
  haveI : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (Work.RatHurewicz.Track inc)) (TopCat.of X)
        (TopCat.ofHom (Work.RatHurewicz.trackProj inc))) n) :=
    Work.Cohomology.homologyEquiv ℤ (TopCat.of (Track inc)) (TopCat.of X)
      (TopCat.ofHom (trackProj inc)) (TopCat.ofHom (trackSec inc))
      (trackProj_trackSec_homotopy inc) (trackSec_trackProj_homotopy inc) n
  exact (CategoryTheory.ConcreteCategory.bijective_of_isIso _).1

end

end Work.RatHurewicz
