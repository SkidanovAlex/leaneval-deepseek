/-
# The dynamical Böttcher coordinate and the dynamical Nakane interface

The endgame's `EL` bridge works in the *dynamical* plane: for a parameter `c` it needs a
Böttcher coordinate `φ_c` of `T_c` together with `Work.Top.NakaneData (filledJulia c) (dynPhi c)`,
i.e. a homeomorphism of `ℂ \\ filledJulia c` onto the exterior disc, a continuous potential and
the potential tending to infinity.

**Branch warning.**  The product formula `Work.Bottcher.bottcher c` (principal branches) is *not*
a Böttcher coordinate in this sense: the Bottcher area's own `bottcher_comm_Tantibar_false`
exhibits `c = -15/2`, `z = -13/4` where
`bottcher c (T_c z) ≠ conj (bottcher c z)^2` (the factors differ by `exp (I π/4)`).
Consequently the object exported here is *not* `bottcher`, but the branch-free, canonical
choice of Böttcher coordinate supplied by `IsDynBottcher` and `isDynBottcher_unique` (the same
device by which `Work.ParamRays.Phi` is defined).  This is what `Work.Landing.landsAt` and the
`EL` bridge should use.

## Main definitions and results

* `Work.ParamRays.dynPhiOf c` : a Böttcher coordinate of `T_c` (junk `0` if none exists).
* `Work.ParamRays.dynPhi c` : the same, set to `0` on the filled Julia set.
* `Work.ParamRays.DynBottcherExists c`, `Work.ParamRays.DynBottcherHomeo c` : the held inputs
  (Böttcher's theorem in the dynamical plane).
* `Work.ParamRays.isDynBottcher_dynPhiOf`.
* `Work.ParamRays.dynNakane` : the dynamical Nakane interface `Top.NakaneData`.
-/
import Submission.Work.ParamRays.Interface
import Submission.Work.ParamRays.isDynBottcher_unique
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology ComplexConjugate
open Classical

namespace Work.ParamRays

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## The dynamical Böttcher coordinate -/

/-- Böttcher's theorem in the dynamical plane, as an input: `T_c` has a Böttcher coordinate.

**Scope.**  `IsDynBottcher c φ` (a coordinate on the *whole* escaping set) is satisfiable **iff
`c ∈ M*`**; for `c ∉ M*` this predicate is false for every `φ`.  Everything in the dynamical
Böttcher/landing theory (`dynPhi`, `DynBottcherHomeo`, `Work.Landing.landsAt`, `Work.EL.*`,
`Work.FSeed`'s ray arguments) is therefore used only at parameters `c ∈ M*`; the parameter-plane
theory off the mandelbar uses `Work.ParamRays.IsCritBottcher` (a coordinate on the critical
domain `Work.ParamRays.critDomain c`). -/
def DynBottcherExists (c : ℂ) : Prop := ∃ φ : ℂ → ℂ, IsDynBottcher c φ

/-- The **dynamical Böttcher coordinate** of `T_c`: the canonical Böttcher coordinate, chosen
from the (classically nonempty) set of functions satisfying `IsDynBottcher c`, with the junk value
`0` when no such function exists.  By `isDynBottcher_unique` the value at any escaping point is
independent of the choice. -/
noncomputable def dynPhiOf (c : ℂ) : ℂ → ℂ :=
  if h : DynBottcherExists c then Classical.choose h else 0

theorem isDynBottcher_dynPhiOf {c : ℂ} (h : DynBottcherExists c) :
    IsDynBottcher c (dynPhiOf c) := by
  rw [dynPhiOf, dif_pos h]
  exact Classical.choose_spec h

/-- The value of `dynPhiOf` at an escaping point is that of *every* Böttcher coordinate.  This is
the lemma that lets `Work.Landing.landsAt` (existentially quantified over Böttcher coordinates) be
evaluated at the single canonical coordinate `dynPhiOf c`. -/
theorem dynPhiOf_eq_of_isDynBottcher {c : ℂ} (h : DynBottcherExists c) {ψ : ℂ → ℂ}
    (hψ : IsDynBottcher c ψ) {z : ℂ} (hz : Escaping c z) : dynPhiOf c z = ψ z :=
  isDynBottcher_unique (isDynBottcher_dynPhiOf h) hψ hz

/-- The **dynamical Böttcher coordinate**, with the junk value `0` on the filled Julia set.

**Scope.**  Meaningful only for `c ∈ M*`: for `c ∉ M*` no `IsDynBottcher c φ` exists, so
`dynPhiOf c` is the junk value `0`. -/
noncomputable def dynPhi (c : ℂ) : ℂ → ℂ := fun z => if z ∈ filledJulia c then 0 else dynPhiOf c z

theorem dynPhi_eq_zero_of_mem {c z : ℂ} (hz : z ∈ filledJulia c) : dynPhi c z = 0 := by
  rw [dynPhi, if_pos hz]

theorem dynPhi_of_not_mem {c z : ℂ} (hz : z ∉ filledJulia c) : dynPhi c z = dynPhiOf c z := by
  rw [dynPhi, if_neg hz]

/-- The complement of the filled Julia set is the escaping set. -/
theorem compl_filledJulia (c : ℂ) : (filledJulia c)ᶜ = escapingSet c := by
  ext z
  simp [filledJulia, escapingSet, escaping_iff_not_bounded]

/-- **The dynamical Böttcher homeomorphism input** (Böttcher's theorem): the Böttcher coordinate
of `T_c` is a homeomorphism of the complement of the filled Julia set onto the exterior of the
unit disc, agreeing with `dynPhi`.  (The complement of the filled Julia set is the escaping set,
`compl_filledJulia`.) -/
def DynBottcherHomeo (c : ℂ) : Prop :=
  DynBottcherExists c ∧ ∃ e : ↥(filledJulia c)ᶜ ≃ₜ ↥Work.Top.exteriorDisc,
    ∀ z : ↥(filledJulia c)ᶜ, dynPhi c z = (e z : ℂ)

theorem DynBottcherHomeo.exists {c : ℂ} (h : DynBottcherHomeo c) : DynBottcherExists c :=
  h.1

theorem DynBottcherHomeo.homeo {c : ℂ} (h : DynBottcherHomeo c) :
    ∃ e : ↥(filledJulia c)ᶜ ≃ₜ ↥Work.Top.exteriorDisc,
      ∀ z : ↥(filledJulia c)ᶜ, dynPhi c z = (e z : ℂ) :=
  h.2

end Work.ParamRays
