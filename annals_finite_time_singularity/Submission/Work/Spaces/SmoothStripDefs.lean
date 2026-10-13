/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Spaces/SmoothStripDefs`: the corrected smoothness class for `EllHyp.smooth`

## Why a new class

`Submission/Work/FTS/EllipticEst/Defs.lean` re-scoped the field `EllHyp.smooth` from
`Work.Spaces.SmoothNbhd Ψ` to `Work.Spaces.SmoothInt Ψ`.  That re-scope is *too weak* for the
`F_*`-chain: the prover of
`FTS/EllipticEst/SmoothIntRescope/Fstar_smooth_of_EllHyp_smoothInt` refuted the resulting
statement "`F_*` is `C^m` on `(0,∞)`" with the datum

  `Ψ z θ := z² (z−1)⁶ e^{−z} · u / (u + (z−1)²)²`,  `u = π/2 − θ`,  `Ψ z 0 := 0`,  `α = 1/2`,

which satisfies `EllHyp α 0 F Ψ` in full (`SmoothInt`, `IsBslSol`, `HkMem`, `ZDecay`) but whose
`F_*` acquires a `log(1/ε)` singularity at `z = 1` (`ε = (z−1)²`), because the `θ`-integral of the
`bslOp` residue does not vanish along the parameter curve.  (`SmoothInt` constrains `Ψ` only on
the *open* strip `(-1,∞) × (0,π/2)`, so it says nothing about the `θ`-behaviour at
`θ = 0, π/2`, which is exactly where the `bslOp` boundary terms live.)

## The corrected class (and a warning about the first attempt)

The class below is recommended by `Mine/CutoffPieces/NOTES_SmoothIntRescope.md` option (ii),
**strengthened** by the requirement that the smoothness on the *full* neighbourhood
`(-1,∞) × (-1, π/2+1)` of the closed quadrant be *joint*.  The strengthening is necessary and was
checked against the refuting datum above: that datum has a pole at `u = -ε(z)`, i.e. at
`θ = π/2 + (z-1)²`, which lies **inside** `Ioo (-1) (π/2+1)`; hence it fails the `θ`-slice
component below, and a fortiori the joint component.  A class whose only joint requirement is on
the *open* strip `(0,π/2)` would **admit** the refuting datum and would therefore be
insufficient for the `F_*`-chain.

The honest `C^∞` order `Work.Stability.smoothOrder` is used throughout: `⊤ : ℕ∞ω` is the
*analytic* order in this Mathlib pin, which is why no cutoff datum can satisfy `SmoothNbhd`
(`Work.Spaces.SmoothNbhd f = ContDiffOn ℝ ⊤ (uncurry f) U`).

The truncation candidate `Ψ'` of the rescope note (which vanishes, flatly, near `θ ≤ 0` and near
`θ ≥ π/2`) satisfies `SmoothStrip`.

## Relation to the existing `Spaces.SmoothInt`

`SmoothStrip f → SmoothInt f` is **not** available as long as `SmoothInt`'s first conjunct is
phrased with `⊤` (the analytic order): `SmoothInt` demands *analyticity* on the open strip, which
`C^∞`-data (cutoffs!) do not have.  The consumers of `hHyp.smooth` use the `SmoothInt` *API* only
through order-weakening (`h.1.of_le le_top`), so the definition-site fix is to replace the two
`⊤`'s in `Work.Spaces.SmoothInt` / `Work.Spaces.SmoothNbhd` by `Work.Stability.smoothOrder`;
then `SmoothStrip → SmoothInt` and `SmoothNbhd → SmoothStrip` are both immediate, and the
`F_*`-chain becomes provable again.  `SmoothNbhd → SmoothStrip` *is* available here, and so is
`SmoothStrip → SmoothOpen` (the open-quadrant class of `OpenQDefs`).

## What is in this file

* the definition `SmoothStrip`;
* the projections `smoothStrip_uncurry` (joint on the full neighbourhood), `smoothStrip_strip`
  (on the open strip), `smoothStrip_thetaSlice`, `smoothStrip_zSlice`, and the finite-order
  weakenings `smoothStrip_uncurry_nat`, `smoothStrip_thetaSlice_nat`;
* `smoothStrip_of_smoothNbhd` (`SmoothNbhd → SmoothStrip`, i.e. every existing provider of
  `SmoothNbhd`-data still produces `SmoothStrip`-data);
* the **joint part of the `pth`-closure**, `smoothStrip_pth_uncurry` (and `smoothStrip_pz_uncurry`),
  which is the general open-set chain rule `Work.FTS.LocData.contDiffOn_pth` applied to the full
  neighbourhood; the two *slice* parts of the `pth`-closure are delegated
  (`FTS/EllipticEst/SmoothStrip/pth_thetaSlice`, `FTS/EllipticEst/SmoothStrip/pth_zSlice`).

(The older names of this file, `smoothStrip_strip_nat` and `smoothStrip_pth_strip`, are kept as
aliases at the end so that nothing that already refers to them breaks.)
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The corrected smoothness class** (rescope note option (ii), with the joint condition on the
full neighbourhood of the closed quadrant): `f` is `C^∞` (honest order, not analyticity) on
`(-1,∞) × (-1, π/2+1)`, jointly in `(z,θ)`; its `θ`-slices are `C^∞` on `Ioo (-1) (π/2+1)`
(one-sided at the boundary angles) and its `z`-slices are `C^∞` on `Ioi (-1)`.

The joint component already implies the two slice components (see the projections below); they
are recorded in the definition because they are what the consumers of the class use and because
they are the part that the truncation route supplies directly. -/
def SmoothStrip (f : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) ∧
    (∀ z ∈ Set.Ioi (-1),
      ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => f z θ) (Set.Ioo (-1) (Real.pi / 2 + 1))) ∧
    (∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ Work.Stability.smoothOrder (fun z => f z θ) (Set.Ioi (-1)))

/-- The joint component of `SmoothStrip`: `f` is `C^∞` on the full neighbourhood of the closed
quadrant, jointly in `(z,θ)`. -/
theorem smoothStrip_uncurry {f : ℝ → ℝ → ℝ} (h : SmoothStrip f) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) := h.1

/-- The open-strip restriction of the joint component. -/
theorem smoothStrip_strip {f : ℝ → ℝ → ℝ} (h : SmoothStrip f) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      (Set.Ioi (-1) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  h.1.mono fun p hp => ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩

/-- The `θ`-slice component of `SmoothStrip`. -/
theorem smoothStrip_thetaSlice {f : ℝ → ℝ → ℝ} (h : SmoothStrip f) {z : ℝ}
    (hz : z ∈ Set.Ioi (-1)) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => f z θ) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
  h.2.1 z hz

/-- The `z`-slice component of `SmoothStrip`. -/
theorem smoothStrip_zSlice {f : ℝ → ℝ → ℝ} (h : SmoothStrip f) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z => f z θ) (Set.Ioi (-1)) :=
  h.2.2 θ hθ

/-- `n ≤ smoothOrder` for every `n : ℕ`, in the `C^n`-order `ℕ∞ω`. -/
theorem natCast_le_smoothOrder (n : ℕ) :
    ((n : ℕ∞) : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
  rw [Work.Stability.smoothOrder]
  exact WithTop.coe_le_coe.mpr le_top

/-- `SmoothStrip` is preserved by a finite-order weakening (recorded for consumers that only
need finitely many derivatives). -/
theorem smoothStrip_uncurry_nat {f : ℝ → ℝ → ℝ} (h : SmoothStrip f) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) :=
  h.1.of_le (natCast_le_smoothOrder n)

/-- The `θ`-slice of `SmoothStrip`-data is `C^n` for every `n`. -/
theorem smoothStrip_thetaSlice_nat {f : ℝ → ℝ → ℝ} (h : SmoothStrip f) {z : ℝ}
    (hz : z ∈ Set.Ioi (-1)) (n : ℕ) :
    ContDiffOn ℝ n (fun θ => f z θ) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
  (h.2.1 z hz).of_le (natCast_le_smoothOrder n)

/-- **The joint component builds the class**: a function that is jointly `C^∞` on the full
neighbourhood of the closed quadrant is `SmoothStrip` (the two slice components follow by
composition with the two injections `θ ↦ (z,θ)`, `z ↦ (z,θ)`). -/
theorem smoothStrip_of_joint {f : ℝ → ℝ → ℝ}
    (h' : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1))) : SmoothStrip f := by
  refine ⟨h', fun z hz => ?_, fun θ hθ => ?_⟩
  · -- the `θ`-slice, by composition with `θ ↦ (z,θ)`
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => ((z, θ) : ℝ × ℝ))
        (Set.Ioo (-1) (Real.pi / 2 + 1)) := by fun_prop
    have hc := h'.comp h2 fun θ hθ => ⟨hz, hθ⟩
    simpa only [Function.comp_def, Function.uncurry] using hc
  · -- the `z`-slice, by composition with `z ↦ (z,θ)`
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => ((z, θ) : ℝ × ℝ))
        (Set.Ioi (-1)) := by fun_prop
    have hc := h'.comp h2 fun z hz =>
      ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
    simpa only [Function.comp_def, Function.uncurry] using hc

/-- **`SmoothNbhd`-data are `SmoothStrip`-data.**  This is what keeps every existing provider of
`SmoothNbhd Ψ` usable after the class correction: analyticity on the neighbourhood (the meaning
of `⊤` in this pin) is in particular honest `C^∞`. -/
theorem smoothStrip_of_smoothNbhd {f : ℝ → ℝ → ℝ} (h : Work.Spaces.SmoothNbhd f) :
    SmoothStrip f :=
  smoothStrip_of_joint (h.of_le (le_top))

/-- **The joint part of the `pth`-closure.**  `pth f = ∂_θ f` is `C^∞` on the full neighbourhood
whenever `f` is: this is the general open-set chain rule for the angular partial derivative,
`Work.FTS.LocData.contDiffOn_pth`, applied to the full neighbourhood. -/
theorem smoothStrip_pth_uncurry {f : ℝ → ℝ → ℝ} (h : SmoothStrip f) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pth f))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) :=
  Work.FTS.LocData.contDiffOn_pth (isOpen_Ioi.prod isOpen_Ioo) h.1

/-- The same for the radial partial derivative `pz f = ∂_z f`. -/
theorem smoothStrip_pz_uncurry {f : ℝ → ℝ → ℝ} (h : SmoothStrip f) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pz f))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) :=
  Work.FTS.LocData.contDiffOn_pz (isOpen_Ioi.prod isOpen_Ioo) h.1

/-- **The class is closed under `pth = ∂_θ`** (the joint part is `smoothStrip_pth_uncurry`, the
slice parts are its restrictions). -/
theorem smoothStrip_pth {f : ℝ → ℝ → ℝ} (h : SmoothStrip f) : SmoothStrip (Work.Spaces.pth f) :=
  smoothStrip_of_joint (smoothStrip_pth_uncurry h)

/-- **The class is closed under `pz = ∂_z`.** -/
theorem smoothStrip_pz {f : ℝ → ℝ → ℝ} (h : SmoothStrip f) : SmoothStrip (Work.Spaces.pz f) :=
  smoothStrip_of_joint (smoothStrip_pz_uncurry h)

/-! ## Compatibility names (kept from the first version of this file) -/

/-- The finite-order strip weakening under its original name. -/
theorem smoothStrip_strip_nat {f : ℝ → ℝ → ℝ} (h : SmoothStrip f) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi (-1) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  (smoothStrip_strip h).of_le (natCast_le_smoothOrder n)

/-- The `pth`-closure under its original name (joint part). -/
theorem smoothStrip_pth_strip {f : ℝ → ℝ → ℝ} (h : SmoothStrip f) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pth f))
      (Set.Ioi (-1) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  (smoothStrip_pth_uncurry h).mono fun p hp =>
    ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2, Real.pi_pos]⟩⟩

end Work.Spaces
