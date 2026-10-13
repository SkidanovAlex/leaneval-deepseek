/-
  WilE9 / Sharp — the strata of the corrected geometric input `Work.WilE9G.EffStratAE`, and the
  component-restricted extended sets built from them.

  `Work.WilE9.Sharp.EffStrat` is false (the lead's design
  `sources/wilkiesE3E9/wilkies_E3E9_gaps.md` §GAP 2, `not_effStrat`): an isolated-point component
  forces a `Good` stratum inside a single point, which the fibre-Jacobian condition contradicts.
  Its replacement `Work.WilE9G.EffStratAE` (proved from the frozen `E2_components` and
  `E5_strat` by subproject WilE9G) therefore:

  * lets each stratum carry a point `q` and uses only `connectedComponentIn E.X.set q`
    (`AEStratum.comp`);
  * leaves the number `m` of hidden fibre coordinates free;
  * guarantees covering only over the base points outside a null set `N ⊆ ℝⁿ` at which the piece
    has a finite fibre.

  This file fixes the vocabulary of that stratification: the strata (`AEStratum`), their used part
  (`AEStratum.comp`), the extended sets restricted to the components over `comp` (`exComp`,
  `exTsetC`) and the corresponding `*`-set (`TsetAE`, `EsetAE`).  The facts about them live in
  `Sharp/AE/`.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.Vocab

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-- A stratum of `Work.WilE9G.EffStratAE`: an `EffStratum n m` together with a base point `q`
(only the component of `E.X.set` through `q` is used) and a free number `m` of hidden fibre
coordinates. -/
abbrev AEStratum (n : ℕ) : Type := Σ m : ℕ, EffStratum n m × (Fin (n + (1 + m)) → ℝ)

namespace AEStratum

/-- The equation system of the stratum. -/
def E {n : ℕ} (A : AEStratum n) : EffStratum n A.1 := A.2.1

/-- The base point of the stratum. -/
def q {n : ℕ} (A : AEStratum n) : Fin (n + (1 + A.1)) → ℝ := A.2.2

/-- The part of the stratum that is used: the connected component of its set through `q`. -/
def comp {n : ℕ} (A : AEStratum n) : Set (Fin (n + (1 + A.1)) → ℝ) :=
  connectedComponentIn A.E.X.set A.q

end AEStratum

/-- **The component-restricted extended set of a stratum.**  The union of the components of the
extended set `exSemiPf n m E L` through the points whose stratum coordinates (`exStrat`) lie in
the stratum's component `connectedComponentIn E.X.set q`.

Only those components are used by E9's soundness direction: all their points have stratum
coordinates in that component (see `exStrat_image_componentIn` and
`exStrat_mem_comp_of_mem_exComp`), which is where the per-stratum hypothesis
"the stratum's component projects into `Z`" is available. -/
def exComp (n m : ℕ) (E : EffStratum n m) (q : Fin (n + (1 + m)) → ℝ) (L : List (Fin n)) :
    Set (Fin (Next n m) → ℝ) :=
  ⋃ z ∈ {z | z ∈ (exSemiPf n m E L).set ∧ exStrat z ∈ connectedComponentIn E.X.set q},
    connectedComponentIn (exSemiPf n m E L).set z

/-- The `ψ`-image of the `L`-th derivative graph over a stratum, restricted to the stratum's
component: the projection of `exComp` to the `(y, σ)`-coordinates. -/
def exTsetC (n m : ℕ) (E : EffStratum n m) (q : Fin (n + (1 + m)) → ℝ) (L : List (Fin n)) :
    Set (Fin (n + 1) → ℝ) :=
  projFirst (n + 1) (n + m + 3) '' exComp n m E q L

/-- **The `ψ`-image of the derivative graph over the strata `S`** (the corrected version of
`Tset`): the union over the strata of `exTsetC` of the stratum's component. -/
def TsetAE (n : ℕ) (S : List (AEStratum n)) (L : List (Fin n)) : Set (Fin (n + 1) → ℝ) :=
  ⋃ A ∈ S, exTsetC n A.1 A.E A.q L

/-- **The `Gen`-set of the E9 construction** (the corrected version of `Eset`): the closure of the
`psiV`-preimage of `TsetAE`. -/
def EsetAE (n : ℕ) (S : List (AEStratum n)) (L : List (Fin n)) : Set (Fin (n + 1) → ℝ) :=
  closure (WilkiesDesign.E.psiV ⁻¹' TsetAE n S L)

/-- The `exOut`-coordinates of the extended set of a stratum, for a single component: the
projection of one component of `exSemiPf n m E L` through a point `z`.  This is the shape in which
`E2_components` presents the components of `exComp`. -/
def exTsetZ (n m : ℕ) (E : EffStratum n m) (L : List (Fin n)) (z : Fin (Next n m) → ℝ) :
    Set (Fin (n + 1) → ℝ) :=
  projFirst (n + 1) (n + m + 3) '' connectedComponentIn (exSemiPf n m E L).set z

end Work.WilE9.Sharp
