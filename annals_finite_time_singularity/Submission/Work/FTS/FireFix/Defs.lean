/-
# `Work.FTS.FireFix` — the physical reconstruction, fired correctly (design §1 and §5, item 7)

This is the **FireFix** area: the *corrected* firing of the fake-time regularity package into the
physical reconstruction, i.e. design items §1 and §5-item-7 of

  `Submission/Work/FTS/FTS_PHYS_BRIDGE.md`

The area owns the two theorems

* `Work.FTS.FireFix.blowupAt_of_physical'` — the generic physical reconstruction theorem with a
  **radius per strip** (`hbun : ∀ S ∈ Ioo 0 T, ∃ R, BSAdmissibleStripFull α ω R S`), no `hZ`/`hb`;
* `Work.FTS.FireFix.blowupAtTop_of_regPkg'` — the firing of the regularity package
  `RegPkgGal.RegPkg'` into `Work.FTS.Top.BlowupAt α C.T`.

## The four corrections of design §0 that this area implements

1. **The vorticity sign** (`def:Symmetry` of the audit, `Physical/SignConvention.lean`): the
   workspace's curl identity for a swirl field is
   `vorticity (psiField (ρ²Φ(ρ^p,θ))) = −(bslOp p Φ (ρ^p,θ)) • e_θ`, so the physical vorticity of
   the reconstruction is `ω := −physOmega α A B g C` (the *negated* field), with stream function
   `merPsi`; the scalar meridian equation is linear in the profile
   (`Work.FTS.MeridianDyn.MeridianEqOn.neg_left`), so `MeridianEqOn` transports.
2. **The factor `2` in the clock**: the meridian-residual computation forces `C.A = 2·A`
   (`hAeq`).
3. **`hZ` and `hb` are dropped**: the per-strip radius is supplied by
   `Work.FTS.Regularity.physVort_bundle` (one radius per fake-time strip, transported along the
   clock) instead of a uniform-in-`τ` support claim.
4. **`PressureReconstructionOn`** replaces the false `Work.LWP.PressureReconstruction`; and the
   *false* `Work.LWP.BiotSavartLaw` (proved false in Lean, `FTS_NOTBSL.lean.txt`) is replaced by
   `Work.FTS.BSSwirl.BiotSavartSwirl`.

## What is a hypothesis of what

The four "analytic inputs" are supplied by the sibling areas and enter the main theorem as
*hypotheses*, at the exact statements of the design:

* `Work.FTS.BSSwirl.BiotSavartSwirl` (proved by `BSSwirl`) — the curl/divergence of the
  Biot–Savart field of a compactly supported Hölder *swirl* vorticity;
* `Work.FTS.PressureOn.PressureReconstructionOn α` (proved by `PressureOn`) — the pressure;
* `Work.FTS.MeridianDyn.MeridianEqOn` (proved by `MeridianDyn`) — the meridian (scalar) form of
  the fake-time equation;
* `Work.FTS.RegPkgGal.RegPkg'` (proved by `RegPkgGal`) — the regularity package of the profile,
  with the *corrected* (Hölder) third Taylor clause of design correction 5.

## Contents of this module

* `Uax` — the open set on which the pointwise vorticity equation is available (the complement of
  the axis and of the plane), re-exported from `Work.FTS.PressureOn`;
* `Fam`, `merPsi` — the design's stream function of the reconstruction, in the meridian variables;
* the `abbrev`s `BiotSavartSwirl`, `PressureReconstructionOn`, `MeridianEqOn`, re-exported so
  that this area's statements read exactly like the design's.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.Physical.Defs
import Submission.Work.FTS.Physical.Omega
import Submission.Work.FTS.Physical.Meridian
import Submission.Work.FTS.Physical.BiotSavart
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.Top.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set
open scoped Topology NNReal ENNReal Matrix

set_option autoImplicit false

namespace Work.FTS.FireFix

/-- `ℝ³`, definitionally `Work.LWP.R3`, `Work.Cyl.R3`, `Work.FTS.Physical.R3`,
`Work.FTS.PressureOn.R3` and `Work.FTS.Top.R3`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- A family `(z,θ,τ) ↦ Φ z θ τ` of self-similar profiles.  Same as
`Work.FTS.Galerkin.Fam` and `Work.FTS.MeridianDyn.Fam`. -/
abbrev Fam : Type := ℝ → ℝ → ℝ → ℝ

/-! ## The open set of the pointwise vorticity equation -/

/-- **The complement of the singular set** (design §1): `ℝ³` minus the axis `x₀ = x₁ = 0` and the
plane `x₂ = 0`.  On it the polar coordinates are non-degenerate and the pointwise vorticity
equation `∂ₜω + (u·∇)ω = (ω·∇)u` is available; its complement is a null set.

Definitionally the `Uax` of `Work.FTS.PressureOn` (hence of the design), so that the local
vorticity equation below can be fed to `PressureReconstructionOn`. -/
abbrev Uax : Set R3 := Work.FTS.PressureOn.Uax

theorem mem_Uax_eq_PressureOn (x : R3) : x ∈ Uax ↔ x ∈ Work.FTS.PressureOn.Uax := Iff.rfl

/-- `Uax` is open. -/
theorem isOpen_Uax : IsOpen Uax := Work.FTS.PressureOn.isOpen_Uax

/-! ## The stream function of the reconstruction -/

/-- **The design's meridian stream function of the reconstruction**,

  `merPsi α A B Φ C r z t = ρ(r,z)² · (A(τ(t)))⁻¹ · Φ(ρ(r,z)^{3α}/B(τ(t)), θ(r,z), τ(t))`,

with `τ(t) = clockInv C t`, `ρ(r,z) = √(r²+z²)`, `θ(r,z) = arctan(z/r)`.

This is `Work.FTS.MeridianDyn.merPsi (3α) A B Φ C` — the definition of the *meridian bridge*
area, which is the area that proves the meridian equation `hmer` of the firing theorem below.
Note that the *odd extension in `θ`* of `Φ` (the design's `Φ̂`, formalised as
`Work.FTS.BSIdent.PhiOdd`) is the caller's choice of the family `Φ`: the natural instantiation
of the firing theorem passes `Φ := Φ̂`, so that the stream function is odd in `z` — as it must be
for the odd velocity (`BS` of an odd vorticity is odd).

The exponent argument is the profile exponent `pExp α = 3α` (design correction 1 and
`Work.FTS.Regularity.pExp`), so this reads as in the design. -/
noncomputable abbrev merPsi (α : ℝ) (A B : ℝ → ℝ) (Φ : Fam) (C : Work.FTS.Physical.PhysClock) :
    ℝ → ℝ → ℝ → ℝ :=
  Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp α) A B Φ C

theorem merPsi_apply (α : ℝ) (A B : ℝ → ℝ) (Φ : Fam) (C : Work.FTS.Physical.PhysClock) (r z t : ℝ) :
    merPsi α A B Φ C r z t
      = Work.Cyl.rhoP r z ^ 2 * (A (Work.FTS.Physical.clockInv C t))⁻¹
        * Φ (Work.Cyl.rhoP r z ^ Work.FTS.Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
            (Work.Cyl.thetaP r z) (Work.FTS.Physical.clockInv C t) := rfl

/-! ## The three named inputs, re-exported at the design's reading -/

/-- **The Biot–Savart law for swirl vorticity** (design §1, item 7a of the dispatch list), the
honest replacement for the false `Work.LWP.BiotSavartLaw`: for a compactly supported `α`-Hölder
swirl field `f(r,z) • e_θ` with `0 < α < 1`, the Biot–Savart velocity inverts the curl and is
divergence-free.  Proved by the `BSSwirl` area (`Work.FTS.BSSwirl.biotSavartSwirl`). -/
abbrev BiotSavartSwirl : Prop := Work.FTS.BSSwirl.BiotSavartSwirl

/-- **The pressure reconstruction of the physical solution** (design §1, item 5): from the
physical vorticity of a compactly supported swirl profile whose Biot–Savart velocity is jointly
`C^{1,α}` on the strips and which solves the pointwise vorticity equation on `Uax`, there is a
pressure `p`, jointly `C¹` on `ℝ³ × [0,T)`, with `∂ₜu + (u·∇)u + ∇p = 0` on `ℝ³ × (0,T)`.
Proved by the `PressureOn` area. -/
abbrev PressureReconstructionOn (α : ℝ≥0) : Prop := Work.FTS.PressureOn.PressureReconstructionOn α

/-- **The meridian (scalar) form of the fake-time equation on a time window** (design §1,
item 9): the pointwise vanishing of `Work.CoreResiduals.meridianResid` for `r > 0`, `z ≠ 0` and
`t ∈ (0,T)`.  Proved by the `MeridianDyn` area
(`Work.FTS.MeridianDyn.meridianEq_of_dynEq`). -/
abbrev MeridianEqOn (W ψ : ℝ → ℝ → ℝ → ℝ) (T : ℝ) : Prop :=
  Work.FTS.MeridianDyn.MeridianEqOn W ψ T

/-- **The corrected regularity package** (design §0 correction 5), the output of the `RegPkgGal`
area: `Work.FTS.Regularity.RegPkg` with the false Lipschitz angular clause replaced by the true
Hölder clause `|g z θ τ − g z θ' τ| ≤ K z² |θ − θ'|^α`. -/
abbrev RegPkg' (α : ℝ) (S : ℝ) (A B : ℝ → ℝ) (g : ℝ → ℝ → ℝ → ℝ) : Prop :=
  Work.FTS.RegPkgGal.RegPkg' α S A B g

end Work.FTS.FireFix
