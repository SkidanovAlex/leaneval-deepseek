import Mathlib
import Submission.Work.RatHurewicz.trackSetup
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.RatHurewicz.isHurewiczFibration_trackMap
import Submission.Work.RatHurewicz.trackFibreHomeo
import Submission.Work.RatHurewicz.subsingleton_relPiVanishing_of_path
import Submission.Work.RatHurewicz.relPiVanishingOfPiInjSurj
import Submission.Work.RatHurewicz.trackFibre_pathConnected
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.Serre.Models
import Submission.Work.Serre.piMap_fibreIncl_surjective_of_subsingleton
import Submission.Work.Serre.piMap_fibreIncl_surjective_pi1

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative homotopy groups of the mapping-track pair vanish in the stable range

For a continuous map `inc : X → Z` with mapping track `Track inc` (`Work.RatHurewicz.trackSetup`)
and track fibration `trackMap inc : Track inc → Z`, `(x,γ) ↦ γ 0`, whose fibre over `inc x₀` is
`trackFibre inc (inc x₀)`, the pair

  `(Track inc, trackFibre inc (inc x₀))`

models the pair `(X, F)` of `inc` with its homotopy fibre `F`.  The relative homotopy groups of this
pair, in the `RelHomotopyGroup` indexing

  `RelHomotopyGroup (setIncl (trackFibre inc (inc x₀))) a j = π_j (hofib (trackFibre inc (inc x₀) ↪ Track inc))`,

vanish in the stable range `j ≤ 2k - 2`, `j + 1 ≠ k`, as soon as the homotopy fibre of `inc` is
`k`-connected and `Z` is a range model of `K(π_k X, k)` up to degree `2k - 1`
(`Work.RatHurewicz.IsRangeKModel`).  This is the homotopy form of the stable-range Serre
comparison for the mapping track: the relative group `π_{j+1}(Track, trackFibre)` is `π_{j+1}(Z)`,
which vanishes exactly outside the single exceptional degree `k` (the degree in which the range
model carries `π_k X`), and the one remaining case `j + 1 = k` is genuinely excluded.

## The proof

Write `F := trackFibre inc (inc x₀)` (definitionally the fibre of the track fibration over `inc x₀`)
and let `a` be a point of `F`.  Since `F` is path connected (its `π₀` is trivial by the connectivity
hypothesis, transported along the homeomorphism `trackFibre_homeo` with the homotopy fibre of
`inc`), `Work.RatHurewicz.subsingleton_relPiVanishing_of_path` reduces the statement to the
canonical base point `a₀ = trackBase inc x₀`.

For that base point, `Work.RatHurewicz.relPiVanishingOfPiInjSurj` says that it suffices to know
that the inclusion `F ↪ Track inc` induces an **injection** on `π_j` and a **surjection** on
`π_{j+1}`.  Both are read off from the long exact homotopy sequence of the Hurewicz fibration
`trackMap inc` (`Work.StemsB.fibrationLES_of_isHurewiczFibration`, exactness supplied by
`Work.StemsB.LESExact`):

* surjectivity on `π_{j+1}`: exactness at `π_{j+1}(Track inc)` gives `im i_* = ker p_*`, and
  `p_* : π_{j+1}(Track inc) → π_{j+1}(Z)` is zero because `π_{j+1}(Z)` is a subsingleton
  (`j + 1 ≤ 2k - 1`, `j + 1 ≠ k`, from `IsRangeKModel`); this is
  `Work.Serre.piMap_fibreIncl_surjective_of_subsingleton` (and
  `Work.Serre.piMap_fibreIncl_surjective_pi1` in degree one);
* injectivity on `π_j`: exactness at `π_j(F)` writes `ker i_*` as the image of the connecting map
  `π_{j+1}(Z) → π_j(F)`, which is zero for the same reason; this is the helper
  `Work.RatHurewicz.injective_piMapN_fibreIncl_of_subsingleton` below.

In degree `j = 0` only the `π₀`-injectivity of the inclusion is needed, and it holds because `F`
is path connected.
-/

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- **Injectivity of the inclusion of the fibre on `π_{m+1}` when `π_{m+1}` of the base
vanishes.**

Let `p : E → B` be a map whose long exact homotopy sequence is available in the form
`Work.StemsB.FibrationLES p e₀` and let `F = p ⁻¹' {p e₀}`.  The exactness clause at `π_{m+1}(F)`
reads `im ∂ = ker i_*` for the connecting map `∂ : π_{m+2}(B) → π_{m+1}(F)`; if the source of `∂`
is a subsingleton then `∂ = 0`, so `ker i_*` is trivial, i.e. `i_* : π_{m+1}(F) → π_{m+1}(E)` is
injective.  (Stated with the unshifted `Work.Serre.piMapN` so that the degree is displayed
literally.) -/
theorem injective_piMapN_fibreIncl_of_subsingleton {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (m : ℕ) (hm : 1 ≤ m)
    (hfib : Work.StemsB.FibrationLES p e₀)
    (hB : Subsingleton (HomotopyGroup (Fin (m + 1)) B (p e₀))) :
    Function.Injective (Work.Serre.piMapN (Work.StemsB.fibreIncl p (p e₀)) m
      (Work.StemsB.fibrePoint p e₀)) := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  change Function.Injective (Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) m'
    (Work.StemsB.fibrePoint p e₀))
  obtain ⟨d, -, -, h3⟩ := hfib m'
  haveI := hB
  have hd0 : ∀ x, d x = 1 := fun x => by rw [Subsingleton.elim x 1, map_one]
  refine (injective_iff_map_eq_one (Work.StemsB.πmap (Work.StemsB.fibreIncl p (p e₀)) m'
    (Work.StemsB.fibrePoint p e₀))).mpr ?_
  intro z hz
  obtain ⟨w, hw⟩ := (h3 z).mp hz
  rw [← hw, hd0]

/-- The relative homotopy groups of the track pair vanish in the stable range, in the `RelHomotopyGroup` indexing: `RelHomotopyGroup (setIncl (trackFibre inc (inc x₀))) a j = π_j(hofib(trackFibre ↪ Track inc))` vanishes for `j ≤ 2k-2` with `j + 1 ≠ k`. -/
theorem trackRelPiVanishing {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (inc : C(X, Z)) (x₀ : X) (k : ℕ) (hk : 2 ≤ k)
    (hmodel : Work.RatHurewicz.IsRangeKModel k (2 * k - 1) (inc x₀))
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j)
      (Work.RatHurewicz.homotopyFibre inc x₀)
      (Work.RatHurewicz.homotopyFibreBasepoint inc x₀)))
    (j : ℕ) (hj : j ≤ 2 * k - 2) (hjk : j + 1 ≠ k) :
    ∀ a : ↥(Work.RatHurewicz.trackFibre inc (inc x₀)),
      Subsingleton (Work.RatHurewicz.RelHomotopyGroup
        (Work.RatHurewicz.setIncl (Work.RatHurewicz.trackFibre inc (inc x₀))) a j) := by
  have hFpath : PathConnectedSpace ↥(trackFibre inc (inc x₀)) :=
    trackFibre_pathConnected inc x₀ (hconn 0 (by omega))
  haveI := hFpath
  let a₀ : ↥(trackFibre inc (inc x₀)) :=
    ⟨trackBase inc x₀, trackBase_mem_trackFibre inc x₀⟩
  have hfib : Work.StemsB.FibrationLES (trackMap inc) (trackBase inc x₀) :=
    Work.StemsB.fibrationLES_of_isHurewiczFibration (trackMap inc)
      (isHurewiczFibration_trackMap inc) (trackBase inc x₀)
  have hpS : Work.StemsB.IsSerreFibration (trackMap inc) :=
    (isHurewiczFibration_trackMap inc).isSerreFibration
  have key : ∀ j : ℕ, j ≤ 2 * k - 2 → j + 1 ≠ k →
      Subsingleton (RelHomotopyGroup (setIncl (trackFibre inc (inc x₀))) a₀ j) := by
    intro j hj hjk
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · -- `j = 0`: the inclusion is injective on `π₀`, since the fibre is path connected
      subst h0
      have hZ0 : Subsingleton (HomotopyGroup (Fin 1) Z (trackMap inc (trackBase inc x₀))) :=
        hmodel 1 (by omega) (by omega)
      refine relPiVanishingOfPiInjSurj 0 a₀ ?_ ?_
      · haveI : Subsingleton (HomotopyGroup (Fin 0)
            ↥(trackFibre inc (inc x₀)) a₀) :=
          ⟨fun x y => (HomotopyGroup.pi0EquivZerothHomotopy (x := a₀)).injective
            (Subsingleton.elim _ _)⟩
        exact fun x y _ => Subsingleton.elim x y
      · exact Work.Serre.piMap_fibreIncl_surjective_pi1 (trackMap inc) hpS
          (trackBase inc x₀) hZ0
    · -- `j ≥ 1`: the two exactness clauses of the track fibration
      obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      have hZm : Subsingleton (HomotopyGroup (Fin (j' + 1 + 1)) Z
          (trackMap inc (trackBase inc x₀))) :=
        hmodel (j' + 1 + 1) (by omega) (by omega)
      refine relPiVanishingOfPiInjSurj (j' + 1) a₀ ?_ ?_
      · exact injective_piMapN_fibreIncl_of_subsingleton (trackMap inc) (trackBase inc x₀)
          (j' + 1) (by omega) hfib hZm
      · exact Work.Serre.piMap_fibreIncl_surjective_of_subsingleton (trackMap inc) hpS
          (trackBase inc x₀) (j' + 1) (by omega) hZm
  intro a
  exact subsingleton_relPiVanishing_of_path a₀ a
    (PathConnectedSpace.somePath a₀ a) j (key j hj hjk)

end

end Work.RatHurewicz
