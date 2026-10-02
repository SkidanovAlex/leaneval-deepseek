/-
# ELPull — the bridge from `ELTop`'s vocabulary (`Work.EL`) to this area's (`Work.ELPull`)

`ELTop/Defs.lean` develops the same plane-topology vocabulary under `Work.EL`, with the dynamical
Böttcher data *parameterised* by the Böttcher coordinate (`Work.EL.DynB c φ = NakaneData (K c)
(dynPhi c φ)`) and with `CoPair`/`RawPair` as two nested structures.  This file records what is
*definitionally identical* (so that an `ELTop` bundle can be fed to this area's lemmas without
glue) and provides the two record conversions for pairs.

* `T`, `arcLen`, `InArc`, `LandsN`, `angMul`, `CyclicStrict`, `polyCurve`, `polyRegion`,
  `PolyAdmissible`, `nearArc` have the *same bodies* in both namespaces, hence unify by `rfl`.
* the type `Work.ELPull.DynB c = Work.Top.NakaneData (K c) (Work.ParamRays.dynPhi c)` is the same
  type as `Work.EL.DynB c (Work.ParamRays.dynPhiOf c)` — see `dynB_ofEL` below, whose proof is
  `id` (the two `Φ`-arguments are the same function definitionally).
* `CoPair` is nested in `ELTop` (`RawPair` + the two landing proofs) and flat here; the conversions
  are `Work.ELPull.CoPair.ofEL` and `Work.ELPull.CoPair.toEL`.
* `RootParabolic` is *not* convertible by definition: this area's version carries the dynamical
  Böttcher data `hN` and the α-pairs `P`/`P_spec` (which `pb1Top`+`landsN_image` produce), so a
  `Work.EL.RootParabolic` must be extended with those to become a `Work.ELPull.RootParabolic`.
-/
import Submission.Work.ELTop.Defs
import Submission.Work.ELPull.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Classical Set Function Filter
open scoped Topology

namespace Work.ELPull

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- `ELTop`'s dynamical Böttcher data at the canonical Böttcher coordinate *is* this area's
`DynB c`: the two `Φ`-arguments are the same function, definitionally, so this is the identity. -/
def dynB_ofEL {c : ℂ} (hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)) : DynB c := hN

/-- The same in the other direction. -/
def dynB_toEL {c : ℂ} (hN : DynB c) : Work.EL.DynB c (Work.ParamRays.dynPhiOf c) := hN

namespace CoPair

/-- An `ELTop` co-landing pair, as a pair of this area. -/
def ofEL {c : ℂ} {hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)}
    (P : Work.EL.CoPair hN) : CoPair (dynB_ofEL hN) :=
  { a := P.a, b := P.b, y := P.y, lands_a := P.lands_a, lands_b := P.lands_b }

/-- A co-landing pair of this area, as an `ELTop` pair. -/
def toEL {c : ℂ} {hN : DynB c} (P : CoPair hN) : Work.EL.CoPair (dynB_toEL hN) :=
  { a := P.a, b := P.b, y := P.y, lands_a := P.lands_a, lands_b := P.lands_b }

@[simp] theorem ofEL_a {c : ℂ} {hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)}
    (P : Work.EL.CoPair hN) : (ofEL P).a = P.a := rfl

@[simp] theorem ofEL_b {c : ℂ} {hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)}
    (P : Work.EL.CoPair hN) : (ofEL P).b = P.b := rfl

@[simp] theorem ofEL_y {c : ℂ} {hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c)}
    (P : Work.EL.CoPair hN) : (ofEL P).y = P.y := rfl

end CoPair

end Work.ELPull
