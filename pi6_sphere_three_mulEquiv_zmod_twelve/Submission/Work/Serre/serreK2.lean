import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Serre.serreE2b
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Serre.C1Pair
import Submission.Work.RatHurewicz.Excision
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.Serre.cylRelPi
import Submission.Work.Serre.cylJoinedIncl
import Submission.Work.Serre.rangeWhiteheadPair
import Submission.Work.Serre.hZeroOfPiZero

/-!
# K2: range-weak-equivalences induce rational homology isomorphisms

`Work.Serre.SerreK2` (blueprint ADDENDUM 2, K2) says: if `f : X → Y` is a bijection on `π_i` for all
`i < N` (at every base point) then `f` induces an isomorphism on rational homology in degrees `< N`.

The proof replaces `f` by the inclusion `cylIncl f : X → cyl f` of the source into its mapping
cylinder (`C1Cyl.lean`).  The composite `cylRetract f ∘ cylIncl f` is `f` and `cylRetract f` is a
homotopy equivalence (`cylHomotopyEquivExplicit`), so it suffices to prove the claim for
`cylIncl f`.

The hypothesis gives, at every base point `x : X` of the pair `(cyl f, X)`:
* `Work.Serre.cylJoinedIncl` — every point of `cyl f` is joined by a path to the bottom copy `X`
  (the `0`-connectivity of the pair, from the surjectivity of `π₀(f)`);
* `Work.Serre.cylRelPi` — the relative groups
  `RelHomotopyGroup (cylIncl f) x k = π_k(homotopyFibre (cylIncl f) x)` vanish for `k ≤ N - 2`, and
  the projection of the homotopy fibre to `X` is zero on `π_{N-1}`.
Those are exactly the hypotheses of `Work.Serre.rangeWhiteheadPair`, which gives the isomorphism in
degrees `1 ≤ j ≤ N - 1`; degree `0` is `Work.Serre.hZeroOfPiZero`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre

noncomputable section

/-- **K2 (blueprint ADDENDUM 2).**  An `N`-connected map induces an isomorphism on rational homology
in degrees `< N`. -/
theorem serreK2 : Work.Serre.SerreK2 := by
  intro X Y _ _ hne f N h j hj
  haveI : Nonempty X := hne
  obtain ⟨x₀⟩ := hne
  by_cases hj0 : j = 0
  · -- degree 0: only `π₀` is involved
    subst hj0
    exact hZeroOfPiZero f (fun x => h 0 (by omega) x)
  · -- `1 ≤ j ≤ N - 1`: the mapping cylinder route
    have hj1 : 1 ≤ j := by omega
    have hN : 2 ≤ N := by omega
    have hmap := ratHomologyMap_comp (cylIncl f) (cylRetract f) j
    rw [cylRetract_cylIncl f] at hmap
    rw [hmap]
    have h2 := rangeWhiteheadPair (N - 2) (cylIncl f)
      (cylJoinedIncl f (fun x => (h 0 (by omega) x).2))
      (fun a k hk => (cylRelPi f a (N - 2) (fun i hi y => h i (by omega) y)).1 k (by omega))
      (fun a x => (cylRelPi f a (N - 2) (fun i hi y => h i (by omega) y)).2 x)
    obtain ⟨E, hE⟩ := cylHomotopyEquivExplicit f
    have h1 : IsIso (ratHomologyMap E.toFun j) := IsRatHomologyIso.of_homotopyEquiv E j
    haveI : IsIso (ratHomologyMap (cylIncl f) j) := h2 j hj1 (by omega)
    haveI : IsIso (ratHomologyMap (cylRetract f) j) := by rwa [hE] at h1
    infer_instance

end

end Work.Serre
