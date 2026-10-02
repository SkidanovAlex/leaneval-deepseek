/-
# `ELAssembly` — the input bundle of the assembly of `Z1Nest` and `B2Data` at `c₀`

The area `Submission/Work/ELAssembly/` assembles the two bundles of the equator-leak argument,

* `Work.ELRig.Z1Nest hN z₁ Pa` — the nest at the parabolic point `z₁` (`Z1.lean`), and
* `Work.ELRig.B2Data hN z₁` — the tripod at the branch point `b₂` (`B2.lean`),

from the (repaired) interface `Work.ELNest.NestData c`, and hence produces the leak
`∃ x, Ψ x ∉ K c` of `Work.EL.equatorLeak_parity` (`Main.lean`).  This file fixes the *input
bundle* of that assembly.

## What is derived and what is assumed

`Work.ELNest.NestData` has ~45 fields.  The following are **derived** by `Assembly.lean` (so they
are not part of the bundle):

| field | derivation |
|---|---|
| `P0`, `P0a`, `P0b`, `P0y` | from `d.rays` through `Work.ELTop.landsN_iff_landsAt` (`alphaPairOf`) |
| `sides_P0` | `Work.ELTop.pairSides`; the non-degeneracy `arcLen α₁ α₂ ≠ 0` is a rational check |
| `side_disj` | `PairSides.disjoint` |
| `Qp`, `Qpa`, `Qpb`, `Za`…`Zc` and their angle specs | the field `pairs : NestPairs d` (itself derivable from ELPull's two certified chains, `NestPairs.ofELPull`) |
| `b2`, `b2_lands`, `b2_lands'` | the field `T : Work.EL.Tripod d.hN` |
| `b2_fix` | from the three tripod rays (`Work.ELAssembly.b2_fix_of_lands`) |
| `b2_not_int` | a landing point of a ray is not interior (`Work.ELTop.landing_notMem_interior`) |
| `curveF` | `Work.ELAssembly.curveF_of_alphaPair` |
| `pot_F`, `pot_f6` | `Work.ELAssembly.pot_iterate` at `n = 10`, `n = 6` |
| `Q_adm` | `Work.ELAssembly.Q_adm_of` from the angle ranges and `Qne` |
| `b2_not_postcrit` (of `B2Data`) | `Work.ELAssembly.b2_not_postcrit_of_inputs` |

Everything else is a field of `AssemblyInputs c`.  Since §7 of `NOTES.md` there are only seven:
`L`, `hL` (free data), `T` (the tripod at `b₂`, class **C**), `hzero` (the two-ray portrait at the
transported `c₀`), the certificate geometry `cert` (below), `SP` (the side preservation
`Work.ELRig.sidePreserve_core`, live in ELRig, taken as a named hypothesis in its exact form) and
`Pa_far` (the petal in the wake side of the `α`-pair, class **C**).

Everything else that the older versions of this bundle carried is **derived** by
`Assembly.lean`: the `α`-pair, the pair sequences (`NestPairs.ofChains` from
`Work.ELAssembly.chainInputs_of`), the tripod fields, the inverse branches `g`/`g6` (the *defined*
branches `gQ`/`gD6`), all the pull-backs (`pbQ`, `pbD`), the holomorphy `g_diff`/`g6_diff`
(§7 of `NOTES.md`), the potential scalings, the admissibility of both nests, the nesting `P0 ⊆ Qp n`
(T2′), `Qne`/`z1_near_Q`/`base_shift`, and NEST (T6, `nest_side_of_nearArc`).

## `PortraitCount` and `hzero` (the orbit portrait at the transported `c₀`)

`hzero : ∀ θ ∈ Ico 0 1, LandsN θ z₁ ↔ θ = α₁ ∨ θ = α₂` is the two-ray portrait at `c₀`; the
design is to *transport* the seed's portrait along the FQC QC conjugacy
(`Work.FQC.transfer_rays`, rays to rays).  `Work.ELPull.PortraitCount` is **not** a hypothesis of
this bundle: it is *derived*, `Work.ELAssembly.portraitCount_of_crit` from `Work.SeedDyn`.  `hzero`
is the single portrait input left, and `Work.ELAssembly.hzero_of_transfer` reduces it to the
seed's own portrait.
## `PortraitCount` and `hzero` (the orbit portrait at the transported `c₀`)

`hzero : ∀ θ ∈ Ico 0 1, LandsN θ z₁ ↔ θ = α₁ ∨ θ = α₂` is the two-ray portrait at `c₀`; the
design is to *transport* the seed's portrait along the FQC QC conjugacy
(`Work.FQC.transfer_rays`, rays to rays).  `hcount : Work.ELPull.PortraitCount (DynB c)` is kept,
per the lead, as a **named hypothesis in its exact form** (`Submission/Work/ELPull/Defs.lean:316`)
with provider the area `SeedDyn`.  Neither is a field of `NestData`: they are inputs of ELPull's
`portrait_five`.
-/
import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELNest.Flower
import Submission.Work.ELNest.Qp_shift
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.landsN_iff_landsAt
import Submission.Work.ELTop.polyRegion_eq_inter_pairSideNear
import Submission.Work.ELTop.RigInput
import Submission.Work.ELPull.Defs
import Submission.Work.ELPull.OfEL
import Submission.Work.FatouCoordFix.Defs
import Submission.Work.ELRig.Defs

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

variable {c : ℂ}

/-! ## The pairs of the two nests, from the co-landing data -/

/-- The `α`-pair at `z₁`: the pair of root rays of the root-parabolic parameter `d`. -/
noncomputable def alphaPairOf (d : Work.EL.RootParabolic c) : Work.EL.CoPair d.hN where
  toRawPair := ⟨Work.EL.alpha1, Work.EL.alpha2, d.z₁⟩
  lands_a := (Work.ELTop.landsN_iff_landsAt d.hN d.bottcher Work.EL.alpha1 d.z₁).mpr d.rays.1
  lands_b := (Work.ELTop.landsN_iff_landsAt d.hN d.bottcher Work.EL.alpha2 d.z₁).mpr d.rays.2

@[simp] theorem alphaPairOf_a (d : Work.EL.RootParabolic c) :
    (alphaPairOf d).a = Work.EL.alpha1 := rfl

@[simp] theorem alphaPairOf_b (d : Work.EL.RootParabolic c) :
    (alphaPairOf d).b = Work.EL.alpha2 := rfl

@[simp] theorem alphaPairOf_y (d : Work.EL.RootParabolic c) : (alphaPairOf d).y = d.z₁ := rfl

/-- The `α`-pair is non-degenerate: `arcLen α₁ α₂ = 33/1023 ≠ 0`. -/
theorem arcLen_alpha_ne_zero : Work.EL.arcLen Work.EL.alpha1 Work.EL.alpha2 ≠ 0 := by
  rw [Work.EL.arcLen, Work.EL.alpha1, Work.EL.alpha2,
    Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
  norm_num

/-- The two-sidedness of the `α`-pair (ELTop's T6). -/
theorem sides_alphaPairOf (d : Work.EL.RootParabolic c) (hJ : Work.Top.JordanForm) :
    Work.EL.PairSides d.hN (alphaPairOf d) :=
  Work.ELTop.pairSides d.hN hJ _ arcLen_alpha_ne_zero

/-- The level-`n` pair of the nest at `z₁`, from the co-landing data. -/
noncomputable def QpOf (d : Work.EL.RootParabolic c)
    (coQ : ∀ n : ℕ, ∃ y : ℂ, Work.EL.LandsN d.hN (Work.ELNest.bAng' n) y ∧
      Work.EL.LandsN d.hN (Work.ELNest.bAng n + 1) y) (n : ℕ) : Work.EL.CoPair d.hN where
  toRawPair := ⟨Work.ELNest.bAng' n, Work.ELNest.bAng n + 1, (coQ n).choose⟩
  lands_a := (coQ n).choose_spec.1
  lands_b := (coQ n).choose_spec.2

@[simp] theorem QpOf_a (d : Work.EL.RootParabolic c) (coQ) (n : ℕ) :
    (QpOf d coQ n).a = Work.ELNest.bAng' n := rfl

@[simp] theorem QpOf_b (d : Work.EL.RootParabolic c) (coQ) (n : ℕ) :
    (QpOf d coQ n).b = Work.ELNest.bAng n + 1 := rfl

/-- The level-`n` arm-`A` pair, from the co-landing data. -/
noncomputable def ZaOf (d : Work.EL.RootParabolic c)
    (coZa : ∀ n : ℕ, ∃ y : ℂ, Work.EL.LandsN d.hN (Work.ELNest.armA1 n) y ∧
      Work.EL.LandsN d.hN (Work.ELNest.armA2 n) y) (n : ℕ) : Work.EL.CoPair d.hN where
  toRawPair := ⟨Work.ELNest.armA1 n, Work.ELNest.armA2 n, (coZa n).choose⟩
  lands_a := (coZa n).choose_spec.1
  lands_b := (coZa n).choose_spec.2

@[simp] theorem ZaOf_a (d : Work.EL.RootParabolic c) (coZa) (n : ℕ) :
    (ZaOf d coZa n).a = Work.ELNest.armA1 n := rfl

@[simp] theorem ZaOf_b (d : Work.EL.RootParabolic c) (coZa) (n : ℕ) :
    (ZaOf d coZa n).b = Work.ELNest.armA2 n := rfl

/-- The level-`n` arm-`B` pair, from the co-landing data. -/
noncomputable def ZbOf (d : Work.EL.RootParabolic c)
    (coZb : ∀ n : ℕ, ∃ y : ℂ, Work.EL.LandsN d.hN (Work.ELNest.armB1 n) y ∧
      Work.EL.LandsN d.hN (Work.ELNest.armB2 n) y) (n : ℕ) : Work.EL.CoPair d.hN where
  toRawPair := ⟨Work.ELNest.armB1 n, Work.ELNest.armB2 n, (coZb n).choose⟩
  lands_a := (coZb n).choose_spec.1
  lands_b := (coZb n).choose_spec.2

@[simp] theorem ZbOf_a (d : Work.EL.RootParabolic c) (coZb) (n : ℕ) :
    (ZbOf d coZb n).a = Work.ELNest.armB1 n := rfl

@[simp] theorem ZbOf_b (d : Work.EL.RootParabolic c) (coZb) (n : ℕ) :
    (ZbOf d coZb n).b = Work.ELNest.armB2 n := rfl

/-- The level-`n` arm-`C` pair, from the co-landing data (second angle with the wrap-around
lift `+1`). -/
noncomputable def ZcOf (d : Work.EL.RootParabolic c)
    (coZc : ∀ n : ℕ, ∃ y : ℂ, Work.EL.LandsN d.hN (Work.ELNest.armC1 n) y ∧
      Work.EL.LandsN d.hN (Work.ELNest.armC2 n + 1) y) (n : ℕ) : Work.EL.CoPair d.hN where
  toRawPair := ⟨Work.ELNest.armC1 n, Work.ELNest.armC2 n + 1, (coZc n).choose⟩
  lands_a := (coZc n).choose_spec.1
  lands_b := (coZc n).choose_spec.2

@[simp] theorem ZcOf_a (d : Work.EL.RootParabolic c) (coZc) (n : ℕ) :
    (ZcOf d coZc n).a = Work.ELNest.armC1 n := rfl

@[simp] theorem ZcOf_b (d : Work.EL.RootParabolic c) (coZc) (n : ℕ) :
    (ZcOf d coZc n).b = Work.ELNest.armC2 n + 1 := rfl

/-- The tripod at `b₂` underlying the tripod facts of `NestData`. -/
noncomputable def tripodOf (d : Work.EL.RootParabolic c) (b2 : ℂ)
    (h₁ : Work.EL.LandsN d.hN (22 / 63) b2) (h₂ : Work.EL.LandsN d.hN (25 / 63) b2)
    (h₃ : Work.EL.LandsN d.hN (37 / 63) b2) (h₁' : Work.EL.LandsN d.hN (22 / 63 + 1) b2) :
    Work.EL.Tripod d.hN :=
  ⟨b2, h₁, h₂, h₃, h₁'⟩


/-! ## The pairs of the two nests, with their angle specifications -/

/-- **The seven pair sequences of the two nests, with their certified angles.**

* `Qp n` — the level-`n` pair of the nest at `z₁`, of angles `(βₙ', βₙ + 1)`;
* `Za n`, `Zb n`, `Zc n` — the level-`n` arm pairs of the nest at `b₂`, of angles
  `(armA1 n, armA2 n)`, `(armB1 n, armB2 n)`, `(armC1 n, armC2 n + 1)`.

The angle specifications are part of the *data* (they are the certificate identifications
`Qpa`/`Qpb`/`Zaa`…`Zcb` of `Work.ELNest.NestData`), so that a caller may supply the pairs by any
means; `NestPairs.ofCoLanding` below builds them from the co-landing statements of the two ELPull
chains. -/
structure NestPairs (d : Work.EL.RootParabolic c) where
  /-- the level-`n` pair of the nest at `z₁`. -/
  Qp : ℕ → Work.EL.CoPair d.hN
  Qpa : ∀ n : ℕ, (Qp n).a = Work.ELNest.bAng' n
  Qpb : ∀ n : ℕ, (Qp n).b = Work.ELNest.bAng n + 1
  /-- the level-`n` arm-`A` pair. -/
  Za : ℕ → Work.EL.CoPair d.hN
  Zaa : ∀ n : ℕ, (Za n).a = Work.ELNest.armA1 n
  Zab : ∀ n : ℕ, (Za n).b = Work.ELNest.armA2 n
  /-- the level-`n` arm-`B` pair. -/
  Zb : ℕ → Work.EL.CoPair d.hN
  Zba : ∀ n : ℕ, (Zb n).a = Work.ELNest.armB1 n
  Zbb : ∀ n : ℕ, (Zb n).b = Work.ELNest.armB2 n
  /-- the level-`n` arm-`C` pair (second angle with the wrap-around lift `+1`). -/
  Zc : ℕ → Work.EL.CoPair d.hN
  Zca : ∀ n : ℕ, (Zc n).a = Work.ELNest.armC1 n
  Zcb : ∀ n : ℕ, (Zc n).b = Work.ELNest.armC2 n + 1

/-- **The pairs of the two nests, from the co-landing statements** (ELPull's `nest_pair_coLands`
and `armPair_coLands`, transported to the `Work.EL` vocabulary).  The pairs are the classical
choices of the common landing points, so the angle specifications hold by `rfl`. -/
noncomputable def NestPairs.ofCoLanding (d : Work.EL.RootParabolic c)
    (coQ : ∀ n : ℕ, ∃ y : ℂ, Work.EL.LandsN d.hN (Work.ELNest.bAng' n) y ∧
      Work.EL.LandsN d.hN (Work.ELNest.bAng n + 1) y)
    (coZa : ∀ n : ℕ, ∃ y : ℂ, Work.EL.LandsN d.hN (Work.ELNest.armA1 n) y ∧
      Work.EL.LandsN d.hN (Work.ELNest.armA2 n) y)
    (coZb : ∀ n : ℕ, ∃ y : ℂ, Work.EL.LandsN d.hN (Work.ELNest.armB1 n) y ∧
      Work.EL.LandsN d.hN (Work.ELNest.armB2 n) y)
    (coZc : ∀ n : ℕ, ∃ y : ℂ, Work.EL.LandsN d.hN (Work.ELNest.armC1 n) y ∧
      Work.EL.LandsN d.hN (Work.ELNest.armC2 n + 1) y) : NestPairs d where
  Qp := QpOf d coQ
  Qpa := fun n => QpOf_a d coQ n
  Qpb := fun n => QpOf_b d coQ n
  Za := ZaOf d coZa
  Zaa := fun n => ZaOf_a d coZa n
  Zab := fun n => ZaOf_b d coZa n
  Zb := ZbOf d coZb
  Zba := fun n => ZbOf_a d coZb n
  Zbb := fun n => ZbOf_b d coZb n
  Zc := ZcOf d coZc
  Zca := fun n => ZcOf_a d coZc n
  Zcb := fun n => ZcOf_b d coZc n

/-! ## The inverse branches, as `invFunOn` of the certified pull-backs

`g` (the inverse branch of `F c` on `Q̂₀`) and `g6` (the inverse branch of `f_c^6` on `Δ̂₀`) are
*defined* from the pull-back `Set.BijOn` fields `pbQ`/`pbD` rather than assumed: the two facts
`g_left`/`g_mem` (`F c (g z) = z` and `g z ∈ Q̂₁` for `z ∈ Q̂₀`) are then pure `Set.BijOn` API
(`Work.ELAssembly.gQ_left`/`gQ_mem`, `gD6_left`/`gD6_mem`), and only the holomorphy of the
branch remains a hypothesis. -/

/-- The inverse branch of `F c` on `Q̂₀`: the inverse of `F c` on `Q̂₁`, as an arbitrary inverse
(`Function.invFunOn`); the two defining properties relative to the certified pull-back `pbQ 0` are
`Work.ELAssembly.gQ_left` and `Work.ELAssembly.gQ_mem`. -/
noncomputable def gQ (c : ℂ) (d : Work.EL.RootParabolic c) (L : ℝ)
    (P0 : Work.EL.CoPair d.hN) (N : NestPairs d) : ℂ → ℂ :=
  Function.invFunOn (Work.EL.F c) (Work.EL.polyRegion [P0, N.Qp 1] (Work.ELNest.Qlev L 1))

/-- The inverse branch of `f_c^6` on `Δ̂₀`: the inverse of `f_c^6` on `Δ̂₁`, as an arbitrary
inverse (`Function.invFunOn`); the two defining properties relative to `pbD 0` are
`Work.ELAssembly.gD6_left` and `Work.ELAssembly.gD6_mem`. -/
noncomputable def gD6 (c : ℂ) {d : Work.EL.RootParabolic c} (L : ℝ) (N : NestPairs d) : ℂ → ℂ :=
  Function.invFunOn (Work.ELNest.F6 c)
    (Work.EL.polyRegion [N.Za 1, N.Zb 1, N.Zc 1] (Work.ELNest.Dlev L 1))

/-! ## The certificate geometry of the two nests -/

/- The structure `CertGeometry` used to live here; see the note below.  Its fields had the
following providers: `Qmem`/`Dmem` from `Work.ELTop.polyRegion_eq_inter_pairSideNear` (T2′),
`pbQ`/`pbD` from `Work.ELPull.polyPullback` (P4), `pot_F`/`pot_f6` from the potential scaling of
the Böttcher coordinate, and the geometric certificate C4–C8 — none of which is an input any
more. -/

-- NOTE (2026-09-28): the structure `CertGeometry` has been **deleted**.  Its ten fields were,
-- one by one, either derived (`Qp_disj`, `b2_mem_D`, `Dnest_sub`, `cutA_mem`, `cutB_mem`,
-- `cutC_mem` — and, before them, `Qmem`, `Dmem`, `Q_adm`, `D_adm`, `pbQ`, `pbD`, `g_*`, `g6_*`,
-- `hcvQ`, `hcvD`) or dead (`Qnear0`).  The last one, `Dnest_cl`, is
-- `Work.ELAssembly.Dnest_cl_of` (`Submission/Work/ELAssembly/Dnest_cl_of.lean`), so the
-- certificate is now **empty**: `Work.ELAssembly.AssemblyInputs` has no certificate field any
-- more (see `Inputs.lean` and `NOTES.md` §0.5/§0.6).

end Work.ELAssembly
