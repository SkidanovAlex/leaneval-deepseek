/-
# `FTS/PhiStar/CoreAux/Fb_add.lean` — the shifted flat class `Fb` is closed under addition

`Work.FTS.PhiStar.Fb n K f` (see `CoreAux/Defs.lean`) is the pair

* `F0 n K f`  — `|(z+1)^k ∂_z^k D_θ^i f| ≤ K` on `Q0 = (0,∞) × (0,π/2)` for `k + i ≤ n`, and
* `F0 n K (∂_θ f)` — the same for `∂_θ f`

(the *shifted* flat class, which is what products and the `WlInf` angular slot need).
This file proves that it is closed under pointwise addition with the additive constant
`K + K'`.

The two ingredients are already available:

* `Work.FTS.PhiStar.CoreAux.F0_add` — `F0` is closed under addition on `Q0` for `C^∞` data
  (`Work.FTS.EllipticEst.SmoothOpen`), with the iterated-operator additivity
  `pzIter_DthIter_add_Q0` in its proof;
* `Work.FTS.PhiStar.CoreAux.F0_congr` — `F0` only sees the restriction to the open quadrant,
  so it may be applied to a function which merely *agrees* with the sum there.

The only new pointwise input is the additivity of `∂_θ` on the `θ`-slices, i.e.
`∂_θ(f + g) = ∂_θ f + ∂_θ g` on `Q0`, which is the product-free instance of `deriv_add`
(both slices are `C^∞` at interior angles by `SmoothOpen.curry_θ`); the corresponding
statement for `∂_θ` of an *iterated* operator is not needed, because `F0_congr` transfers the
bound from the (definitionally summed) function `∂_θ f + ∂_θ g`, which is `SmoothOpen` since
`SmoothOpen.pth` preserves the class.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.PhiStar.CoreAux.F0_add
import Submission.Work.FTS.PhiStar.CoreAux.F0_congr
import Submission.Work.FTS.EllipticEst.OpenQDefs

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

/-! ## The `θ`-derivative of a sum -/

/-- **`∂_θ(f + g) = ∂_θ f + ∂_θ g` on the open quadrant** for `C^∞` data: the `θ`-slices are
differentiable at every interior angle, so `deriv_add` applies. -/
private theorem pth_add_Q0 {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.pth f z θ + Work.Spaces.pth g z θ := by
  intro z θ hz h1 h2
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h1, h2⟩
  have hd1 : DifferentiableAt ℝ (fun θ' : ℝ => f z θ') θ :=
    ((hf.curry_θ hz).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hd2 : DifferentiableAt ℝ (fun θ' : ℝ => g z θ') θ :=
    ((hg.curry_θ hz).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hff : (fun θ' : ℝ => f z θ' + g z θ')
      = (fun θ' : ℝ => f z θ') + (fun θ' : ℝ => g z θ') := by
    funext θ'; rfl
  simp only [Work.Spaces.pth]
  rw [hff]
  exact deriv_add hd1 hd2

/-! ## The main theorem -/

theorem Fb_add {n : ℕ} {K K' : ℝ} {f g : ℝ → ℝ → ℝ} (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g) (hf : Work.FTS.PhiStar.Fb n K f) (hg : Work.FTS.PhiStar.Fb n K' g) : Work.FTS.PhiStar.Fb n (K + K') (fun z θ => f z θ + g z θ) := by
  refine ⟨F0_add hsf hsg hf.f0 hg.f0, ?_⟩
  -- the `∂_θ`-part: `∂_θ(f + g)` agrees on `Q0` with the `SmoothOpen` sum `∂_θ f + ∂_θ g`
  have hsum : Work.FTS.PhiStar.F0 n (K + K')
      (fun z θ => Work.Spaces.pth f z θ + Work.Spaces.pth g z θ) :=
    F0_add hsf.pth hsg.pth hf.fd hg.fd
  exact F0_congr (pth_add_Q0 hsf hsg) hsum

end Work.FTS.PhiStar.CoreAux
