/-
# `FTS/PhiStar/CoreAux/F0_congr.lean` — the flat class `F0` only sees the open quadrant

`Work.FTS.PhiStar.F0 n K f` (see `CoreAux/Defs.lean`) bounds the mixed weighted derivatives
`(z+1)^k ∂_z^k D_θ^i f` (`k + i ≤ n`) **on the open quadrant** `Q0 = (0,∞) × (0,π/2)`.  Since

* `∂_z` and `∂_θ` are *local* operators (their value at a point depends only on the germ of the
  function at that point), and
* every point of `Q0` is an interior point of `Q0`,

two functions which agree on `Q0` have the same iterated weighted derivatives there.  Hence
`F0 n K` is a property of the restriction to `Q0` alone: if `f = g` on `Q0` and `F0 n K g` then
`F0 n K f`, with the *same* constant `K`.

The proof is a double congruence: at a point `(z,θ) ∈ Q0`,

* the `θ`-slice of `f` agrees with that of `g` on a neighbourhood of `θ` (still inside `Q0`),
  so `∂_θ`, hence `D_θ` and all its iterates, agree (`DthIter_congr_Q0`);
* likewise for the `z`-slice and `∂_z`, hence `∂_z`-iterates (`pzIter_congr_Q0`).

Nothing here is a `sorry` or an axiom.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.Spaces.Defs
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

/-! ## Congruence of the iterated operators on the open quadrant -/

/-- **`D_θ^i` only sees the germ in `θ`**:  if `f` and `g` agree on the open quadrant `Q0`, then
so do all their `D_θ`-iterates.

Induction on `i`:  `D_θ^{i+1} = sin(2θ)·∂_θ D_θ^i`, and `∂_θ` is unchanged when the `θ`-slice
is replaced by a function agreeing with it near `θ` (which stays inside `Q0` since `Q0` is open
in `θ`). -/
private lemma DthIter_congr_Q0 {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) Work.FTS.EllipticEst.Q0) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i f))
      (Function.uncurry (Work.Spaces.DthIter i g)) Work.FTS.EllipticEst.Q0 := by
  have hV : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  induction i with
  | zero => exact h
  | succ i ih =>
      intro p hp
      have hnb : ∀ᶠ θ' in 𝓝 p.2, (p.1, θ') ∈ Work.FTS.EllipticEst.Q0 :=
        (Continuous.prodMk_right p.1).continuousAt.eventually (hV.mem_nhds hp)
      have hslice : (fun θ' => Function.uncurry (Work.Spaces.DthIter i f) (p.1, θ'))
          =ᶠ[𝓝 p.2] (fun θ' => Function.uncurry (Work.Spaces.DthIter i g) (p.1, θ')) := by
        filter_upwards [hnb] with θ' hθ'
        exact ih hθ'
      show Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter i f) p.1 p.2
          = Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter i g) p.1 p.2
      rw [Work.Spaces.pth, Work.Spaces.pth]
      exact congrArg (fun t => Real.sin (2 * p.2) * t) hslice.deriv_eq

/-- **`∂_z^k` only sees the germ in `z`**:  if `f` and `g` agree on the open quadrant `Q0`, then
so do all their `∂_z`-iterates.

Induction on `k`: each step replaces the `z`-slice by a function agreeing with it near `z`
(still inside `Q0` since `Q0` is open in `z`) and uses that `deriv` respects eventual equality. -/
private lemma pzIter_congr_Q0 {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) Work.FTS.EllipticEst.Q0) (k : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pzIter k f))
      (Function.uncurry (Work.Spaces.pzIter k g)) Work.FTS.EllipticEst.Q0 := by
  have hV : IsOpen Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.isOpen_Q0
  induction k with
  | zero => exact h
  | succ n ih =>
      intro p hp
      have hnb : ∀ᶠ z' in 𝓝 p.1, (z', p.2) ∈ Work.FTS.EllipticEst.Q0 :=
        (Continuous.prodMk_left p.2).continuousAt.eventually (hV.mem_nhds hp)
      have hslice : (fun z' => Work.Spaces.pzIter n f z' p.2)
          =ᶠ[𝓝 p.1] (fun z' => Work.Spaces.pzIter n g z' p.2) := by
        filter_upwards [hnb] with z' hz'
        exact ih hz'
      simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pz, Function.uncurry]
        using hslice.deriv_eq

/-! ## The main lemma -/

theorem F0_congr {n : ℕ} {K : ℝ} {f g : ℝ → ℝ → ℝ} (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) (hg : Work.FTS.PhiStar.F0 n K g) : Work.FTS.PhiStar.F0 n K f := by
  intro k i hki z θ hz hθ hθ'
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ, hθ'⟩
  have hfg : Set.EqOn (Function.uncurry f) (Function.uncurry g) Work.FTS.EllipticEst.Q0 :=
    fun p hp => h p.1 p.2 hp.1 hp.2.1 hp.2.2
  have heq : Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ
      = Work.Spaces.pzIter k (Work.Spaces.DthIter i g) z θ :=
    pzIter_congr_Q0 (DthIter_congr_Q0 hfg i) k hmem
  rw [heq]
  exact hg k i hki z θ hz hθ hθ'

end Work.FTS.PhiStar.CoreAux
