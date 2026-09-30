/-
# The area `Space/`: everything in one import

This is the aggregator of the area `Space/`.  `import Submission.Work.Space.All` brings in

* `Work.Space.Assembly` — the topological assembly `M̂ = (M̄ ⊔ ⊔_v [-1,1]²×T_v)/~₃`, its instances
  (`TopologicalSpace`, `T2Space`, `CompactSpace`, `ConnectedSpace`), the closed embedding
  `M̄ ↪ M̂` and the openness criteria;
* `Work.Space.FinAtlas`, `Work.Space.ModelAtlas` — finite atlases with priority `chartAt`, the
  `ChartedSpace`/`IsManifold`/`SecondCountableTopology` instances, the metric `gM`, the
  `RiemannianBundle` and `IsContMDiffRiemannianBundle` instances, and
  `Work.Space.ModelAtlas.chartGram_is_model` (the hypothesis of `Work.Curvature.curvLe_of_models`);
* `Work.Space.Assembly.Aset`, `Bset`, `Aset_sup_Bset` and the homotopy equivalences
  `retrA`, `retrB`, `retrAB` of the Mayer–Vietoris cover;
* `Work.Space.RTData` — the one-stop class: a single `instance : RTData` yields every structure of
  `M̂` by typeclass inference;
* `Work.Space.Data`, `Work.Space.Constraints` — the exact numerical data (`δ_K = 1/5`, `s₁ = 11/10`,
  `R₀ = 7/2`, the lattices, the slopes, the `H`-representation of `Q̄`) and the parameter
  constraints (i)–(iii) of blueprint §1.
-/
import Mathlib
import Submission.Work.Space.Main
import Submission.Work.Space.Split.innerCore_homotopyEquiv
import Submission.Work.Space.Split.retrB_homotopyEquiv
import Submission.Work.Space.Split.retrA_homotopyEquiv
import Submission.Work.Space.Split.retrAB_homotopyEquiv
import Submission.Work.Space.Split.retrAB_compat
import Submission.Work.Space.Split.retrA_compat
import Submission.Work.Space.Data.slope_norm_ge

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open TopologicalSpace
open scoped Manifold ContDiff Topology Bundle
open Bundle

namespace Work.Space

/-! ### The retractions, in the form of the blueprint -/

/-- **`B` deformation retracts onto the cores `⊔_v T_v`** — the *explicit* homotopy equivalence
`Work.Space.Split.eBCompat` (forward map the collar projection `p ↦ 0`, inverse the core
inclusion, homotopy the straight-line collar scaling). -/
def retrB (a : Assembly) :
    ContinuousMap.HomotopyEquiv {x : a.Mhat // x ∈ a.Bset} (Σ v : Cusp, a.Torus v) :=
  Split.eBCompat a

/-- **`A` deformation retracts onto `M̄`** — the *explicit* homotopy equivalence
`Work.Space.Split.eACompat` (forward map the radial collapse `p ↦ p/‖p‖∞` followed by the gluing,
inverse the inclusion, homotopy the straight-line shell scaling). -/
def retrA (a : Assembly) :
    ContinuousMap.HomotopyEquiv {z : a.Mhat // z ∈ a.Aset} a.Mbar :=
  Split.eACompat a

/-- **`A ∩ B` deformation retracts onto the glued boundary `⊔_v ∂[-1,1]² × T_v`** — the *explicit*
homotopy equivalence `Work.Space.Split.eABCompat` (radial rescaling `p ↦ p/‖p‖∞` of the annulus).
The same map, with the boundary written as a subtype of `a.Y`, is
`Work.Space.Split.eABACompat`; it is the one used in `retrA_compat`. -/
def retrAB (a : Assembly) :
    ContinuousMap.HomotopyEquiv {z : a.Mhat // z ∈ a.Aset ∧ z ∈ a.Bset}
      (Σ v : Cusp, {p : SquarePt // sqNorm p = 1} × a.Torus v) :=
  Split.eABCompat a

/-- **The open collar `{‖p‖∞ < 1}` of the filling pieces deformation retracts onto the cores.** -/
def retrInnerCore (a : Assembly) :
    ContinuousMap.HomotopyEquiv {q : a.Y // q ∈ innerCore a.Torus} (Σ v : Cusp, a.Torus v) :=
  Classical.choice (Split.innerCore_homotopyEquiv a)

/-! ### The exact compatibilities of the explicit maps

The modules `Submission.Work.Space.Split.retrAB_compat` and `.../retrA_compat` prove, for the
*explicit* witnesses `Split.eABCompat`, `Split.eABACompat`, `Split.eBCompat`, `Split.eACompat`,
the equalities (not merely homotopies)

* `Work.Space.Split.eBCompat_comp_inclAB_B_eq` :
  `eBCompat ∘ (A∩B ↪ B) = projBdry ∘ eABCompat`;
* `Work.Space.Split.eACompat_comp_inclAB_A_eq` :
  `eACompat ∘ (A∩B ↪ A) = tauBdry ∘ eABACompat`.

Hence the Mayer--Vietoris maps of the two inclusions are identified with the projection onto `T_v`
and with the cusp parametrisation `τ`. -/

end Work.Space
