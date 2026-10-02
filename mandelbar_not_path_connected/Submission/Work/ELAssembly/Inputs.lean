/-
# `ELAssembly` — the input bundle of the assembly

`Work.ELAssembly.AssemblyInputs c d fl` collects the named hypotheses of the assembly of
`Work.ELRig.Z1Nest`/`B2Data` at the parameter `c`, as described in `NOTES.md` §2.  It lives in its
own file (after `Chains.lean`) because the certificate geometry is stated at the *derived* pair
data `Work.ELAssembly.NestPairs.ofChains (chainInputs_of d hzero)`.
-/
import Mathlib
import Submission.Work.ELAssembly.Defs
import Submission.Work.ELAssembly.Chains
import Submission.Work.ELAssembly.ChainInputsOf

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The assembly inputs -/

/-- **The assembly inputs at `c`.**  The fields are the named hypotheses of the assembly of
`Work.ELRig.Z1Nest`/`B2Data` at `c`; the module docstring records the provider of each.  The
parameter `fl : Work.ELNest.FlowerData c d.z₁` is the flower (the specialised form of
`Work.FatouCoordFix.ParabolicFlowerFix`, obtained by `Work.ELNest.FlowerData.ofFatouCoord`); it is
a parameter rather than a field so that the caller's *own* flower (the `FlowerGlue` one) can be
put in, and so that the `isDefEq` blow-up of a `ParabolicFlower`-valued structure field is
avoided. -/
structure AssemblyInputs (c : ℂ) (d : Work.EL.RootParabolic c) (fl : Work.ELNest.FlowerData c d.z₁)
    where
  -- The bundle has **five** fields (2026-09-28): the reference level `L` with `hL` (free data),
  -- the tripod `T` at the branch point, the two-ray portrait `hzero` at `z₁`, and the side
  -- preservation `SP`.  The certificate `CertGeometry` and the portrait statement `Pa_far` used
  -- to be fields too; every field of the certificate is now a theorem of this area
  -- (`NOTES.md` §0.6), and so is `Pa_far` (`Work.ELAssembly.Pa_far_of`).
  /-- the reference level of the two nests. -/
  L : ℝ
  /-- the reference level is above `1`. -/
  hL : 1 < L
  /-- the tripod at the branch point `b₂` (the three rays of angles `22/63`, `25/63`, `37/63`
  landing at `T.y`). -/
  T : Work.EL.Tripod d.hN
  -- NOTE: the inverse branches `g` of `F c` on `Q̂₀` and `g6` of `f_c^6` on `Δ̂₀` are *derived*,
  -- not fields: they are `Work.ELAssembly.gQ`/`Work.ELAssembly.gD6`, defined by
  -- `Function.invFunOn` from the certified pull-backs `Work.ELAssembly.pullQ_bij`/
  -- `pullD_bij`, with their two defining properties (`gQ_left`/`gQ_mem`, `gD6_left`/`gD6_mem`).
  /-- **`hzero`**, the orbit portrait at the transported `c₀`: the only rays of angles in
  `Ico 0 1` landing at `z₁` are the two root rays (transported from the seed by the FQC QC
  conjugacy `Work.FQC.transfer_rays`). -/
  hzero : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
    (Work.EL.LandsN d.hN θ d.z₁ ↔ θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2)
  -- NOTE (2026-09-28): the certificate field `cert : CertGeometry …` has been **deleted**.
  -- Every field of the certificate is now derived (see `NOTES.md` §0.6 and
  -- `Submission/Work/ELAssembly/Derived/`), including the last one, `Dnest_cl`
  -- (`Work.ELAssembly.Dnest_cl_of`), so the bundle carries no certificate hypothesis at all.
  /-- the side preservation `Work.ELRig.sidePreserve_core` of the `α`-pair, in its exact form. -/
  SP : ∃ R : ℝ, ∀ u : ℂ, u.re < -R →
    (fl.Ψ u ∈ Work.EL.pairSide (alphaPairOf d) ↔
      fl.Ψ (u + 1) ∈ Work.EL.pairSide (alphaPairOf d))
  -- NOTE (2026-09-28): the field
  -- `Pa_far : fl.Pa ⊆ Work.EL.pairSide (alphaPairOf d)` has been **deleted**: it is now the
  -- theorem `Work.ELAssembly.Pa_far_of` (`Pa_far_of.lean`), derived from `d.wake` and
  -- `fl.enters_Pa` (see `NOTES.md` §0.6).
  -- NOTE: `curveF` (the invariance of the curve of the `α`-pair under `F c`) is *derived*, not a
  -- field: it is `Work.ELAssembly.curveF_of_alphaPair` (from `T^[10] αᵢ ≡ αᵢ` and `per_half`).
  -- NOTE: **NEST** (T6) is *derived*, not a field: with the orientation-complete statement (the
  -- near arc of `P` contained in the near arc of `Q`) it is `Work.ELAssembly.nest_side_of_nearArc`,
  -- a corollary of ELTop's `pairSide_subset_pairSideNear`; see `Assembly.lean`.  The older
  -- two-`InArc` form carried by the previous version of this bundle was *false* at `c₀`
  -- (`NOTES_FALSE_nest_side.md`, `Work.ELAssembly.nest_side_false`).

end Work.ELAssembly
