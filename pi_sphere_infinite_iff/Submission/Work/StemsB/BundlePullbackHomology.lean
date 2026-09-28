import Mathlib
import Submission.Work.StemsB.BundlePullback
import Submission.Work.StemsB.bundlePullback_homotopyEquiv
import Submission.Work.Cohomology.isZero_homology_of_homotopyEquiv

/-!
# The homology of the pullback of the path–loop fibration

`Submission/Work/StemsB/bundlePullback_homotopyEquiv.lean` proves that the pullback of the
path–loop fibration over a based-contractible parameter space `D` is homotopy equivalent to the
fibre `Path x₀ (s d₀)`.  This file turns that into the statement used by Step I of the
sphere-specific route to the crux (`CONTRACTS.md` §F1):

* `Work.StemsB.isZero_homology_of_homotopyEquiv_ring` — vanishing of singular homology is a
  homotopy invariant, for coefficients in an arbitrary commutative ring (the `ℤ` case is
  `Work.Cohomology.isZero_homology_of_homotopyEquiv`);
* `Work.StemsB.isZero_homology_bundlePullback_iff` — the rational homology of the pullback vanishes
  in degree `m` if and only if that of the fibre `Path x₀ (s d₀)` does.
-/

open scoped Topology

namespace Work.StemsB

open CategoryTheory CategoryTheory.Limits

/-- **Vanishing of singular homology is a homotopy invariant**, for coefficients in an arbitrary
commutative ring (the `ℤ` case is `Work.Cohomology.isZero_homology_of_homotopyEquiv`). -/
theorem isZero_homology_of_homotopyEquiv_ring (R : Type) [CommRing R] {X Y : TopCat}
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ)
    (h : CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains R Y).homology n)) :
    CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains R X).homology n) := by
  let f : X ⟶ Y := TopCat.ofHom e.toFun
  let g : Y ⟶ X := TopCat.ofHom e.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 X) := e.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 Y) := e.right_inv.some
  haveI : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap R X Y f) n) :=
    Work.Cohomology.homologyEquiv R X Y f g h1 h2 n
  exact CategoryTheory.Limits.IsZero.of_iso h
    (CategoryTheory.asIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap R X Y f) n))

/-- **The rational homology of the pullback of the path–loop fibration over a based-contractible
parameter space is that of the fibre**.  Immediate from `bundlePullback_homotopyEquiv` and the
homotopy invariance of the vanishing of singular homology. -/
theorem isZero_homology_bundlePullback_iff (X : Type) [TopologicalSpace X] (x₀ : X)
    (D : Type) [TopologicalSpace D] (s : ContinuousMap D X) (d₀ : D)
    (c : ContinuousMap (D × unitInterval) D)
    (hc0 : ∀ u, c (u, 0) = u) (hc1 : ∀ u, c (u, 1) = d₀) (hcb : ∀ t, c (d₀, t) = d₀)
    (m : ℕ) :
    CategoryTheory.Limits.IsZero
        ((Work.Cohomology.singularChains ℚ (TopCat.of (bundlePullback X x₀ D s))).homology m) ↔
      CategoryTheory.Limits.IsZero
        ((Work.Cohomology.singularChains ℚ (TopCat.of (Path x₀ (s d₀)))).homology m) := by
  obtain ⟨e⟩ := bundlePullback_homotopyEquiv X x₀ D s d₀ c hc0 hc1 hcb
  exact ⟨fun h => isZero_homology_of_homotopyEquiv_ring ℚ
      (X := TopCat.of (Path x₀ (s d₀))) (Y := TopCat.of (bundlePullback X x₀ D s)) e.symm m h,
    fun h => isZero_homology_of_homotopyEquiv_ring ℚ
      (X := TopCat.of (bundlePullback X x₀ D s)) (Y := TopCat.of (Path x₀ (s d₀))) e m h⟩

end Work.StemsB
