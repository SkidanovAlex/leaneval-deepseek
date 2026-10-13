import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.ContE1
import Submission.Work.FTS.GalFields.Norm.radA_Corr_contDiffOn_four

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TransO/ContDiffOn_E1_O` — `E1 α f` is `C³` on the open quadrant, on the *open* class

The transfer identity `D_θ(𝓛_Γ^T f) = 𝓛̂(D_θ f) + E1 α f` (`Transfer/Profiles.lean`)
introduces the defect

  `E1 α f z θ = (sin 2θ · Γ'(θ)) · radA α f z`,

a **separated** product of an angular factor of `θ` alone and a radial factor of `z` alone.
On the open coercivity class `CoerAdmO α f` (the class of the route's projected slices,
`EpsE4Thr/OpenClass.lean`) its two factors are of class `C³`:

* the angular factor `B(θ) = sin 2θ · Γ'(θ)` is `C³` on `(0,π/2)` because
  `Γ(θ) = (sin θ cos²θ)^{α/3}` is `C^∞` there (`Transfer.sinGam_contDiffOn_Ioo`);
* the radial factor `radA α f` is `C³` on `(0,∞)` because the nonlocal tail integral
  `L₁₂ f` is `C⁴` there — this is the *open* analogue
  `GalFields.Norm.radA_contDiffOn_four_of_smoothOpen` of the frozen
  `Transfer.radA_contDiffOn`, and it needs only `SmoothOpen f` and `HkMem α 5 f`, both of
  which `CoerAdmO α f` supplies.

The frozen twin of the present statement is `E1Parts.contDiffOn_uncurry_E1`, which is stated
on `CoerAdm` (hence demands `SmoothQuad`); that class is not reachable on the route
(`EpsE4Thr/OpenClass.lean`), which is exactly why this open-class version is needed.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The angular factor `B(θ) = sin 2θ·Γ'(θ)` of the transfer defect is `C³` on `(0,π/2)`.**

This is the angular half of `E1`; it is class-free (it does not involve the datum `f`).  The
proof is the one of `Work.FTS.CoercivityFix.Transfer.sinGam_contDiffOn_Ioo`: `Γ` is `C^∞` on
the open half-strip `z > 0, 0 < θ < π/2` (its base `sin θ · cos²θ` is positive there), so its
`D_θ`-derivative is `C^∞` as well, and it is recovered as the `z = 1` slice. -/
theorem contDiffOn_E1_ang (α : ℝ) :
    ContDiffOn ℝ 3
      (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ) (Set.Ioo 0 (π / 2)) :=
  Work.FTS.CoercivityFix.Transfer.sinGam_contDiffOn_Ioo α

/-- **The radial factor `radA α f` of the transfer defect is `C³` on `(0,∞)`.**

`CoerAdmO α f` supplies `SmoothOpen f` (the class-`C`-clause regularity of the route) and
`HkMem α 5 f`, which on `radA`'s definition
`radA α f z = −a(z)·L₁₂ f(z) + (b(z)/c(α))·L₁₂(Transport f)(0)` reduce the statement to
`L₁₂ f ∈ C⁴((0,∞))` — the open twin
`Work.FTS.GalFields.Norm.radA_contDiffOn_four_of_smoothOpen`. -/
theorem contDiffOn_E1_rad (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f) :
    ContDiffOn ℝ 3 (Work.FTS.CoercivityFix.Transfer.radA α f) (Set.Ioi (0 : ℝ)) :=
  (Work.FTS.GalFields.Norm.radA_contDiffOn_four_of_smoothOpen hα hα1 hf.1.1 hf.1.2.1).of_le
    (by norm_num)

/-- **The requested regularity**: the transfer defect `E1 α f` is `C³` on the open quadrant,
for every datum of the open coercivity class `CoerAdmO α f`.

`E1 α f z θ = B(θ)·radA α f z` is a separated product, so its joint `C³`-regularity on
`Qd = (0,∞) × (0,π/2)` follows from `contDiffOn_E1_ang` and `contDiffOn_E1_rad` by composing
with the two projections. -/
theorem ContDiffOn_E1_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f) :
    ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.CoercivityFix.Transfer.E1 α f))
      Work.Construction.Qd := by
  have hB : ContDiffOn ℝ 3
      (fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.Gam α) θ) (Set.Ioo 0 (π / 2)) :=
    contDiffOn_E1_ang α
  have hR : ContDiffOn ℝ 3 (Work.FTS.CoercivityFix.Transfer.radA α f) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_E1_rad α hα hα1 hf
  have hfun : Function.uncurry (Work.FTS.CoercivityFix.Transfer.E1 α f)
      = (fun p : ℝ × ℝ => Real.sin (2 * p.2) * deriv (Work.Spaces.Gam α) p.2)
        * (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.Transfer.radA α f p.1) := by
    funext p
    rcases p with ⟨z, θ⟩
    rfl
  rw [hfun]
  exact (hB.comp contDiffOn_snd (fun p hp => hp.2)).mul
    (hR.comp contDiffOn_fst (fun p hp => hp.1))

end Work.FTS.StrongEps.EpsE4Thr.TransO
