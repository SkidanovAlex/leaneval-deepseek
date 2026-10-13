/-
# `Work.FTS.LocDataExt` — the localised datum in the interior class `RegQ` (node N9-ext)

This is the *extension* chapter of the delivered node **N9** (`Submission/Work/FTS/LocData/`,
the localised data of the route), whose job is to put the localised datum

  `locG α L β (hLoc α) = locData α L β (hLoc α) - F_*  =  -zfar L F_* + β · hLoc α`

into the *interior regular class* `Work.FTS.Nonlin.RegQ` at order `5`, and to package the
result together with the two facts of N9 (`L₁₂(g)(0) = 0`, `|g|_{ℋ⁴} ≤ ε`) in exactly the
form that the a-priori bound `galerkin_bound` of the design
(`Submission/Work/FTS/N45_DESIGN_LEAD.md` §2.4, §4) consumes its datum.

## Why an extension is needed

`galerkin_bound` (design §4, L-N5.7) takes the datum `g₀` with

* `Work.FTS.LocData.DataAdm α g₀`  (smooth on the quadrant, vanishing on the angular
  boundary, vanishing to second order at the axis, and honestly in `ℋ⁴`),
* `Work.Construction.L12 g₀ 0 = 0`,
* `Work.FTS.Nonlin.RegQ α 4 g₀`  (`SmoothQuad ∧ HkMem α 4 ∧ BdryTraces α 4`),
* `Work.FTS.Nonlin.Xn α g₀ ≤ α ^ 2`.

N9 delivers the first two and the smallness of the `ℋ⁴`-norm, but **not** the class
`RegQ`: the vanishing of the integration-by-parts boundary terms (`BdryTraces`) and the
membership `HkMem` (which at order `5` is the design's `N9-ext` obligation, §6 of the design)
are new here.  The two N9 pieces are *reused*, not reproved: the smallness at `ε = α ^ 2` is
N9's `locData_small`.

## Contents of this module

The two radial factors of the perturbation, and the factorisations that let every estimate
treat the `z`- and `θ`-variables separately:

* `zfarR L` — the radial factor of the far part `zfar L F_*`, i.e.
  `zfar L F_* = (α/c)·Γ(θ)·zfarR L`;
* `locR α L β` — the radial factor of the perturbation, i.e.
  `locG α L β (hLoc α) = locR α L β (z)·Γ(θ)`.

Both `F_* = α(Γ(θ)/c)·FM.Fstar(z)` and `hLoc α = bumpZ(z)·Γ(θ)` are *separable*, so the
perturbation is too, and `D_z^j D_θ^i` of it acts on the two factors independently
(`SepFactor.lean`).  The vanishing of `locR` outside a compact interval in `z` is what makes
the radial weight `w = (1+z)²/z²` harmless and the boundary traces at `z = 0` and `z = ∞`
trivial.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.SmoothQuad_hLoc
import Submission.Work.FTS.LocData.SmoothQuad_locG
import Submission.Work.FTS.LocData.hLoc_vanishing
import Submission.Work.FTS.LocData.profileZeroFar_locData
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocDataExt

set_option autoImplicit false

/-- Functions of the self-similar variables `(z,θ)`, curried. -/
abbrev Fn : Type := ℝ → ℝ → ℝ

/-! ## The two radial factors -/

/-- **The radial factor of the far part of the profile**:
`zfarR L z = (1 - χ(z/L))·FM.Fstar z`, so that the far part of the reference profile is

  `zfar L F_* = (α/c)·Γ(θ)·zfarR L z`

(`zfar_Fstar_eq`).  It vanishes for `z ≤ L` (`χ(z/L) = 1` there) and for `z ≥ 2L`
(`χ = 0` there), so it is a compactly supported `C^∞` function of `z`. -/
noncomputable def zfarR (L : ℝ) : ℝ → ℝ :=
  fun z => (1 - Work.Stability.chi (z / L)) * Work.FM.Fstar z

@[simp] theorem zfarR_apply (L z : ℝ) :
    zfarR L z = (1 - Work.Stability.chi (z / L)) * Work.FM.Fstar z := rfl

/-- **The radial factor of the perturbation** `locG`:

  `locG α L β (hLoc α) = locR α L β (z)·Γ(θ)`,  `locR α L β z = -(α/c)·zfarR L z + β·bumpZ z`

where `bumpZ` is the radial factor `χ(4z-5)` of the bump `hLoc` (support `[3/4, 7/4]`). -/
noncomputable def locR (α L β : ℝ) : ℝ → ℝ :=
  fun z => -(α / Work.Spaces.c α) * zfarR L z + β * Work.FTS.LocData.bumpZ z

@[simp] theorem locR_apply (α L β z : ℝ) :
    locR α L β z = -(α / Work.Spaces.c α) * zfarR L z + β * Work.FTS.LocData.bumpZ z := rfl

/-! ## The factorisations -/

/-- **The far part is separable**: `zfar L F_* = (α/c)·Γ(θ)·zfarR L z`. -/
theorem zfar_Fstar_eq (α L : ℝ) :
    Work.Stability.zfar L (Work.Construction.Fstar α)
      = fun z θ => (α / Work.Spaces.c α) * zfarR L z * Work.Spaces.Gam α θ := by
  funext z θ
  rw [Work.Stability.zfar_apply, zfarR_apply, Work.Construction.Fstar]
  ring

/-- **The perturbation is separable**: `locG α L β (hLoc α) = locR α L β (z)·Γ(θ)`. -/
theorem locG_eq_locR_Gam (α L β : ℝ) :
    Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)
      = fun z θ => locR α L β z * Work.Spaces.Gam α θ := by
  funext z θ
  rw [Work.FTS.LocData.locG_apply, Work.FTS.LocData.locData_apply,
    Work.FTS.LocData.hLoc_apply, locR_apply, zfarR_apply, Work.Construction.Fstar]
  ring

/-- `zfarR L` vanishes for `z ≤ L`. -/
theorem zfarR_eq_zero_of_le {L z : ℝ} (hL : 0 < L) (hz0 : 0 ≤ z) (hz : z ≤ L) :
    zfarR L z = 0 := by
  have h1 : |z / L| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hz0 (le_of_lt hL)), div_le_one hL]
    exact hz
  rw [zfarR_apply, Work.Stability.chi_eq_one h1]
  ring

/-- **`zfarR L` is the plain profile beyond the far scale**: for `z ≥ 2L` the cut-off factor is
`1`, so the far part agrees with `FM.Fstar` there. -/
theorem zfarR_eq_FM_Fstar_of_ge {L z : ℝ} (hL : 0 < L) (hz : 2 * L ≤ z) :
    zfarR L z = Work.FM.Fstar z := by
  have h1 : 2 ≤ |z / L| := by
    rw [abs_of_nonneg (div_nonneg (by linarith) (le_of_lt hL)), le_div_iff₀ hL]
    linarith
  rw [zfarR_apply, Work.Stability.chi_eq_zero h1]
  ring

/-- The radial bump `bumpZ` of the localised datum vanishes for `z ≤ 3/4`. -/
theorem bumpZ_eq_zero_of_le {z : ℝ} (hz : z ≤ 3 / 4) :
    Work.FTS.LocData.bumpZ z = 0 := by
  rw [Work.FTS.LocData.bumpZ_apply, Work.Stability.chi_eq_zero]
  have h2 : |4 * z - 5| = -(4 * z - 5) := abs_of_nonpos (by linarith)
  rw [h2]; linarith

/-- The radial bump `bumpZ` of the localised datum vanishes for `z ≥ 7/4`. -/
theorem bumpZ_eq_zero_of_ge {z : ℝ} (hz : 7 / 4 ≤ z) :
    Work.FTS.LocData.bumpZ z = 0 := by
  rw [Work.FTS.LocData.bumpZ_apply, Work.Stability.chi_eq_zero]
  have h2 : |4 * z - 5| = 4 * z - 5 := abs_of_nonneg (by linarith)
  rw [h2]; linarith

/-- **`locR` vanishes near the axis**: for `z ≤ min L (3/4)` both summands vanish. -/
theorem locR_eq_zero_of_le {α L β z : ℝ} (hL : 0 < L) (hz0 : 0 ≤ z) (hzL : z ≤ L)
    (hzb : z ≤ 3 / 4) : locR α L β z = 0 := by
  rw [locR_apply, zfarR_eq_zero_of_le hL hz0 hzL, mul_zero, bumpZ_eq_zero_of_le hzb,
    mul_zero, add_zero]

/-- Beyond the far scale the bump has died, so `locR` is the (rescaled) plain profile. -/
theorem locR_eq_of_ge {α L β z : ℝ} (hL : 0 < L) (hz : 2 * L ≤ z) (hzb : 7 / 4 ≤ z) :
    locR α L β z = -(α / Work.Spaces.c α) * Work.FM.Fstar z := by
  rw [locR_apply, zfarR_eq_FM_Fstar_of_ge hL hz, bumpZ_eq_zero_of_ge hzb, mul_zero, add_zero]

/-! ## Smoothness of the separable pieces -/

/-- A function of `z` alone which is `C^∞` on `(-1,∞)` is in the class `SmoothQuad` of the
localised-data chapter. -/
theorem smoothQuad_of_fstOn {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ Work.Stability.smoothOrder f (Set.Ioi (-1))) :
    Work.FTS.LocData.SmoothQuad (fun z _ => f z) := by
  rw [Work.FTS.LocData.SmoothQuad]
  exact hf.comp contDiffOn_fst (fun p hp => hp.1)

/-- The angular factor `Γ` is `SmoothQuad`. -/
theorem smoothQuad_Gam (α : ℝ) :
    Work.FTS.LocData.SmoothQuad (fun _ θ => Work.Spaces.Gam α θ) :=
  Work.FTS.LocData.smoothQuad_of_snd (Work.FTS.LocData.contDiffOn_Gam_Ioo α)

/-- **A separable function `ρ(z)·Γ(θ)` is `SmoothQuad`** as soon as its radial factor is. -/
theorem smoothQuad_sepGam {ρ : ℝ → ℝ} {α : ℝ}
    (hρ : ContDiffOn ℝ Work.Stability.smoothOrder ρ (Set.Ioi (-1))) :
    Work.FTS.LocData.SmoothQuad (fun z θ => ρ z * Work.Spaces.Gam α θ) :=
  Work.FTS.LocData.smoothQuad_mul (smoothQuad_of_fstOn hρ) (smoothQuad_Gam α)

/-- The radial factor `zfarR L` is `C^∞` on `(-1,∞)`. -/
theorem contDiffOn_zfarR (L : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (zfarR L) (Set.Ioi (-1)) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => 1 - Work.Stability.chi (z / L)) (Set.Ioi (-1)) :=
    Work.FTS.LocData.ZFBase.contDiffOn_slice_oneSubChi L
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => Work.FM.Fstar z)
      (Set.Ioi (-1)) := Work.FTS.LocData.ZFBase.contDiffOn_slice_FM_Fstar
  exact h1.mul h2

/-- The radial factor `locR α L β` is `C^∞` on `(-1,∞)`. -/
theorem contDiffOn_locR (α L β : ℝ) :
    ContDiffOn ℝ Work.Stability.smoothOrder (locR α L β) (Set.Ioi (-1)) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => -(α / Work.Spaces.c α) * zfarR L z) (Set.Ioi (-1)) :=
    ContDiffOn.const_smul (-(α / Work.Spaces.c α)) (contDiffOn_zfarR L)
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => β * Work.FTS.LocData.bumpZ z) (Set.Ioi (-1)) :=
    ContDiffOn.const_smul β (Work.FTS.LocData.contDiff_bumpZ.contDiffOn)
  refine (h1.add h2).congr (fun z _ => ?_)
  rw [locR_apply]

/-- The perturbation `locG α L β (hLoc α)` is `SmoothQuad` (the same fact as
`Work.FTS.LocData.SmoothQuad_locG`, re-derived through the separable form). -/
theorem smoothQuad_locG (α L β : ℝ) :
    Work.FTS.LocData.SmoothQuad (Work.FTS.LocData.locG α L β (Work.FTS.LocData.hLoc α)) := by
  have h := smoothQuad_sepGam (α := α) (contDiffOn_locR α L β)
  rwa [← locG_eq_locR_Gam α L β] at h

end Work.FTS.LocDataExt
