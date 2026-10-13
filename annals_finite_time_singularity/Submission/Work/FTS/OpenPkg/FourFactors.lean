/-
# `Work.FTS.OpenPkg.FourFactors` — the `C⁴`-smoothness of the factors of the N4 pieces

The 27 summands `N0fix`, `N03g`, …, `N5ss` of the §8 assembly
(`Submission/Work/FTS/Nonlinear/Defs.lean`) are built by products, sums and constant multiples
of a small list of *factors*:

* the perturbation `g` and its operators `∂_θg`, `D_zg`, `D_θg` (`g` is `SmoothQuad`, hence
  `C^∞` on the open quadrant, in the applications);
* the fixed profile `F_* = Construction.Fstar α` and its operators `∂_θF_*`, `D_zF_*`;
* the radial functions `L₁₂(g)`, `L₁₂(F_*)`, `FK g`, `FK (F_*)`, `sin(2θ)`, `cos 2θ - sin²θ`,
  `sin²θ`;
* the residuals `Φ̃_g = PhiTil α g Φg` and `Φ̃_* = PhiTil α (F_* α) Φs` transported by
  `Rop`, `Uop`, `Vop`.

This file fixes the *interface*: the structure `FourFactors α g Φs Φg` collects the `C^4` facts
about the factors which make every piece a `C^4` function on the open quadrant.  The piece
lemmas (`Submission/Work/FTS/OpenPkg/Pieces4/…`) are then purely algebraic (`ContDiffOn.mul`,
`.const_mul`, `.add`, `.sub` and a `congr` along the definitional unfolding), and the
inhabitation of `FourFactors` from the a-priori data (`GalClass`, `StarPkgo`, `EllPkgGo`) is
`Work.FTS.OpenPkg.fourFactors_of_gal` in `Submission/Work/FTS/OpenPkg/C4Factors.lean`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.OpenPkg.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The open quadrant of the interior estimates: `(0,∞) × (0,π/2)`. -/
abbrev Q0 : Set (ℝ × ℝ) := Work.FTS.EllipticEst.Q0

/-- A radial function, as a function of the two self-similar variables. -/
abbrev Rad (R : ℝ → ℝ) : Fn := fun z (_ : ℝ) => R z

/-- **The `C⁴`-smoothness of the factors of the 27 pieces of the §8 assembly.** -/
structure FourFactors (α : ℝ) (g Φs Φg : Fn) : Prop where
  /-- the perturbation and its three first-order operators -/
  hg : ContDiffOn ℝ 4 (Function.uncurry g) Q0
  hpthg : ContDiffOn ℝ 4 (Function.uncurry (Work.Spaces.pth g)) Q0
  hDzg : ContDiffOn ℝ 4 (Function.uncurry (Work.Spaces.Dz g)) Q0
  hDthg : ContDiffOn ℝ 4 (Function.uncurry (Work.Spaces.Dth g)) Q0
  /-- the fixed profile `F_*` and its two operators -/
  hF : ContDiffOn ℝ 4 (Function.uncurry (Work.Construction.Fstar α)) Q0
  hpthF : ContDiffOn ℝ 4 (Function.uncurry (Work.Spaces.pth (Work.Construction.Fstar α))) Q0
  hDzF : ContDiffOn ℝ 4 (Function.uncurry (Work.Spaces.Dz (Work.Construction.Fstar α))) Q0
  /-- the four radial functions -/
  hL12g : ContDiffOn ℝ 4 (Function.uncurry (Rad (Work.Construction.L12 g))) Q0
  hL12F : ContDiffOn ℝ 4
    (Function.uncurry (Rad (Work.Construction.L12 (Work.Construction.Fstar α)))) Q0
  hFKg : ContDiffOn ℝ 4 (Function.uncurry (Rad (Work.Construction.FK g))) Q0
  hFKF : ContDiffOn ℝ 4
    (Function.uncurry (Rad (Work.Construction.FK (Work.Construction.Fstar α)))) Q0
  /-- the residuals transported by `Rop`, `Uop`, `Vop` -/
  hRopTg : ContDiffOn ℝ 4
    (Function.uncurry (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg))) Q0
  hUopTg : ContDiffOn ℝ 4
    (Function.uncurry (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg))) Q0
  hVopTg : ContDiffOn ℝ 4
    (Function.uncurry (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))) Q0
  hRopTs : ContDiffOn ℝ 4
    (Function.uncurry (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs))) Q0
  hUopTs : ContDiffOn ℝ 4
    (Function.uncurry (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs))) Q0
  hVopTs : ContDiffOn ℝ 4
    (Function.uncurry (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs))) Q0

/-! ## Elementary closure facts used by the piece lemmas -/

/-- `sin(2·)` is smooth on the quadrant. -/
theorem contDiffOn_s2_Q0 (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (fun (_ : ℝ) (θ : ℝ) => Real.sin (2 * θ))) Q0 :=
  ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn).of_le le_top

/-- `cos 2θ - sin²θ` is smooth on the quadrant. -/
theorem contDiffOn_c2m_Q0 (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (fun (_ : ℝ) (θ : ℝ) =>
      Real.cos (2 * θ) - Real.sin θ ^ 2)) Q0 :=
  (((Real.contDiff_cos.comp (contDiff_const.mul contDiff_snd)).sub
    ((Real.contDiff_sin.comp contDiff_snd).pow 2)).contDiffOn).of_le le_top

/-- `sin²θ` is smooth on the quadrant. -/
theorem contDiffOn_sin_sq_Q0 (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (fun (_ : ℝ) (θ : ℝ) => Real.sin θ ^ 2)) Q0 :=
  (((Real.contDiff_sin.comp contDiff_snd).pow 2).contDiffOn).of_le le_top

end Work.FTS.OpenPkg
