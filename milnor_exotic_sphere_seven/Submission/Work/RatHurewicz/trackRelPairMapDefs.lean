import Mathlib
import Submission.Work.RatHurewicz.trackSetup
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.homotopyFibreMap_exists
import Submission.Work.Cohomology.localHomology
import Submission.Work.StemsB.PiMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The two maps induced by a map of pairs

This module fixes the vocabulary used by the delegated statement `relWhitehead_of_relPiBijective`
(the range form of Whitehead's theorem for pairs, the "relative `K2`" that Serre's exact sequence
in the stable range consumes): for a commutative square of inclusions

  `A ⊆ Y`, `A' ⊆ Y'`, `f : Y → Y'`, `g : A → A'` with `f ∘ incl = incl ∘ g`

we define

* `Work.RatHurewicz.relChainsOfPairMap` — the map of *relative chain complexes*
  `C_*(Y,A) → C_*(Y',A')` induced by the map of pairs, so that
  `HomologicalComplex.homologyMap (relChainsOfPairMap …) d` is the map on relative homology;
* `Work.RatHurewicz.relPiMapOfPair` — the map on the relative homotopy groups
  `π_n(homotopyFibre (setIncl A) a) → π_n(homotopyFibre (setIncl A') (g a))` induced by the
  canonical map of homotopy fibres `homotopyFibreMap`.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- The map of relative chain complexes induced by a map of pairs. -/
def relChainsOfPairMap {Y Y' : Type} [TopologicalSpace Y] [TopologicalSpace Y']
    (A : Set Y) (A' : Set Y') (f : C(Y, Y')) (g : C(↥A, ↥A')) (hg : ∀ a : ↥A, f a = g a) :
    Work.Cohomology.relChains (TopCat.of Y) A ⟶ Work.Cohomology.relChains (TopCat.of Y') A' :=
  Work.Cohomology.relChainsMapOf (TopCat.of Y) (TopCat.of Y') A A' (TopCat.ofHom f) (TopCat.ofHom g)
    (by ext a; exact hg a)

/-- The commutative square of a map of pairs, in the form required by `homotopyFibreMap`. -/
theorem pairMap_comp_eq {Y Y' : Type} [TopologicalSpace Y] [TopologicalSpace Y']
    (A : Set Y) (A' : Set Y') (f : C(Y, Y')) (g : C(↥A, ↥A')) (hg : ∀ a : ↥A, f a = g a) :
    f.comp (setIncl A) = (setIncl A').comp g := by
  ext a
  exact hg a

/-- The map of homotopy fibres induced by a map of pairs. -/
def pairFibreMap {Y Y' : Type} [TopologicalSpace Y] [TopologicalSpace Y']
    (A : Set Y) (A' : Set Y') (f : C(Y, Y')) (g : C(↥A, ↥A')) (hg : ∀ a : ↥A, f a = g a)
    (a : ↥A) :
    C(homotopyFibre (setIncl A) a, homotopyFibre (setIncl A') (g a)) :=
  homotopyFibreMap (setIncl A) (setIncl A') f g (pairMap_comp_eq A A' f g hg) a

/-- The map on relative homotopy groups induced by a map of pairs, in the `RelHomotopyGroup`
indexing: `RelHomotopyGroup (setIncl A) a (j+1) → RelHomotopyGroup (setIncl A') (g a) (j+1)`
(only the degrees `≥ 1` carry a group structure in this model). -/
noncomputable def relPiMapOfPair {Y Y' : Type} [TopologicalSpace Y] [TopologicalSpace Y']
    (A : Set Y) (A' : Set Y') (f : C(Y, Y')) (g : C(↥A, ↥A')) (hg : ∀ a : ↥A, f a = g a)
    (j : ℕ) (a : ↥A) :
    HomotopyGroup (Fin (j + 1)) (homotopyFibre (setIncl A) a)
        (homotopyFibreBasepoint (setIncl A) a) →*
      HomotopyGroup (Fin (j + 1)) (homotopyFibre (setIncl A') (g a))
        (pairFibreMap A A' f g hg a (homotopyFibreBasepoint (setIncl A) a)) :=
  Work.StemsB.πmap (pairFibreMap A A' f g hg a) j (homotopyFibreBasepoint (setIncl A) a)

end

end Work.RatHurewicz
