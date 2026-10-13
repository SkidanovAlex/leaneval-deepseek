/-
# `FTS/PhiStar/CoreAux/Fb_zpz.lean` — the shifted flat class `Fb` is stable under `f ↦ z ∂_z f`

`Work.FTS.PhiStar.Fb n K f` (see `CoreAux/Defs.lean`) is the pair of flat bounds
`F0 n K f` and `F0 n K (∂_θ f)`, i.e.

* `|(z+1)^k ∂_z^k D_θ^i f| ≤ K` for `k + i ≤ n`, and
* `|(z+1)^k ∂_z^k D_θ^i (∂_θ f)| ≤ K` for `k + i ≤ n`,

on the open quadrant `Q0 = (0,∞) × (0,π/2)`.  This file proves

`Fb (n+1) K f  →  Fb n ((n+1)·K) (fun z θ => z · ∂_z f z θ)`,

i.e. that the operator `D_z = z ∂_z` maps the class at order `n+1` into the class at order
`n`, with the constant multiplied by `n+1`.

**The two halves.**

* `F0 n ((n+1)K) (D_z f)`: exactly `F0_zpz` (`CoreAux/F0_zpz.lean`) applied to the hypothesis
  `hf.f0 : F0 (n+1) K f`.
* `F0 n ((n+1)K) (∂_θ (D_z f))`: on the open quadrant `∂_θ (z ∂_z f) = z · ∂_z (∂_θ f)`.  The
  factor `z` pulls out of `deriv` (`deriv_const_mul`), and the remaining unweighted Clairaut
  identity `∂_θ ∂_z f = ∂_z ∂_θ f` is `Work.Spaces.pz_pth_comm`, available at every interior
  point because `SmoothOpen f` gives `C²` of `uncurry f` there.  The identity holds only on
  `Q0` and `F0` only looks at `Q0`, so the transfer is made by `F0_congr`; the resulting bound
  is again an instance of `F0_zpz`, applied now to `∂_θ f` (smooth by `SmoothOpen.pth`) and to
  `hf.fd : F0 (n+1) K (∂_θ f)`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.CoreAux.F0_zpz
import Submission.Work.FTS.PhiStar.CoreAux.F0_congr

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The angular derivative of `z ∂_z f`**, on the open quadrant, for a datum smooth there:

`∂_θ (z ∂_z f) = z · ∂_z (∂_θ f)`.

The `z` factors out of `deriv` (`deriv_const_mul`), and the remaining identity
`∂_θ ∂_z f = ∂_z ∂_θ f` is Clairaut's theorem (`Work.Spaces.pz_pth_comm`), applicable at
`(z,θ) ∈ Q0` because `SmoothOpen f` in particular makes `uncurry f` `C²` near that point. -/
theorem pth_zpz_smoothOpen {f : ℝ → ℝ → ℝ} (hsf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (fun z θ => z * Work.Spaces.pz f z θ) z θ
        = z * Work.Spaces.pz (Work.Spaces.pth f) z θ := by
  intro z θ hz hθ hθ'
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ'⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsf 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have hcomm : Work.Spaces.pth (Work.Spaces.pz f) z θ
      = Work.Spaces.pz (Work.Spaces.pth f) z θ :=
    (Work.Spaces.pz_pth_comm hcd).symm
  calc Work.Spaces.pth (fun z θ => z * Work.Spaces.pz f z θ) z θ
      = deriv (fun θ' => z * Work.Spaces.pz f z θ') θ := rfl
    _ = z * deriv (fun θ' => Work.Spaces.pz f z θ') θ := deriv_const_mul_field z
    _ = z * Work.Spaces.pth (Work.Spaces.pz f) z θ := rfl
    _ = z * Work.Spaces.pz (Work.Spaces.pth f) z θ := by rw [hcomm]

theorem Fb_zpz {n : ℕ} {K : ℝ} {f : ℝ → ℝ → ℝ} (hK : 0 ≤ K) (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hf : Work.FTS.PhiStar.Fb (n + 1) K f) : Work.FTS.PhiStar.Fb n (((n : ℝ) + 1) * K) (fun z θ => z * Work.Spaces.pz f z θ) := by
  refine ⟨F0_zpz hK hsf hf.f0, ?_⟩
  refine F0_congr (pth_zpz_smoothOpen hsf) ?_
  exact F0_zpz hK hsf.pth hf.fd

end Work.FTS.PhiStar.CoreAux
