/-
# `FTS/PhiStar/CoreAux/F0_add.lean` — the flat class `F0` is closed under addition

`Work.FTS.PhiStar.F0 n K f` (see `CoreAux/Defs.lean`) says that all the mixed weighted
derivatives `(z+1)^k ∂_z^k D_θ^i f` with `k + i ≤ n` are bounded by `K` on the open quadrant
`Q0 = (0,∞) × (0,π/2)`.  This file proves that `F0` is closed under pointwise addition, with
the additive constant `K + K'`.

The only analytic input is the **pointwise additivity of the iterated operators** on the open
quadrant for data which are `C^∞` there (`Work.FTS.EllipticEst.SmoothOpen`):

* `D_θ^i (f + g) = D_θ^i f + D_θ^i g` — this is `SmoothOpen.DthIter_add` of
  `Work/FTS/EllipticEst/SmoothOpenAdd.lean`;
* `∂_z^k (A + B) = ∂_z^k A + ∂_z^k B` — proved below inside `pzIter_DthIter_add_Q0`, by
  induction on `k`: the `∂_z`-step is `deriv_add`, using that the `z`-slices of
  `∂_z^k D_θ^i f` are differentiable at every `z > 0` (`SmoothOpen.hasDerivAt_slice`).  The
  two steps are combined into a single induction (rather than a separate locality lemma for
  `pzIter`) so that the eventual equality needed for `deriv` is produced on the spot.

Then `|(z+1)^k (A + B)| = |(z+1)^k A + (z+1)^k B| ≤ |(z+1)^k A| + |(z+1)^k B| ≤ K + K'`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.CoreAux.Defs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd

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

/-- **Additivity of `∂_z^k D_θ^i` on the open quadrant** for two data which are `C^∞` there:
`∂_z^k D_θ^i (f + g) = ∂_z^k D_θ^i f + ∂_z^k D_θ^i g` at every point of
`Q0 = (0,∞) × (0,π/2)`.

The induction is on `k`: the base case `k = 0` is the additivity of `D_θ^i`
(`SmoothOpen.DthIter_add`), and the step differentiates the (eventually equal) `z`-slices with
`deriv_add`, both summands being `C^∞` on the open quadrant. -/
theorem pzIter_DthIter_add_Q0 {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (i : ℕ) : ∀ k : ℕ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pzIter k (Work.Spaces.DthIter i (fun z θ => f z θ + g z θ)) z θ
        = Work.Spaces.pzIter k (Work.Spaces.DthIter i f) z θ
          + Work.Spaces.pzIter k (Work.Spaces.DthIter i g) z θ := by
  intro k
  induction k with
  | zero =>
      intro z θ hz h1 h2
      exact Work.FTS.EllipticEst.SmoothOpen.DthIter_add hf hg i z θ hz h1 h2
  | succ m ih =>
      intro z θ hz h1 h2
      have heq : (fun z' : ℝ =>
            Work.Spaces.pzIter m (Work.Spaces.DthIter i (fun z θ => f z θ + g z θ)) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.pzIter m (Work.Spaces.DthIter i f) z' θ
              + Work.Spaces.pzIter m (Work.Spaces.DthIter i g) z' θ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih z' θ hz' h1 h2
      have hd1 : DifferentiableAt ℝ
          (fun z' => Work.Spaces.pzIter m (Work.Spaces.DthIter i f) z' θ) z :=
        (((hf.DthIter i).pzIter m).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd2 : DifferentiableAt ℝ
          (fun z' => Work.Spaces.pzIter m (Work.Spaces.DthIter i g) z' θ) z :=
        (((hg.DthIter i).pzIter m).hasDerivAt_slice ⟨h1, h2⟩ hz).differentiableAt
      have hd : deriv (fun z' => Work.Spaces.pzIter m (Work.Spaces.DthIter i f) z' θ
            + Work.Spaces.pzIter m (Work.Spaces.DthIter i g) z' θ) z
          = deriv (fun z' => Work.Spaces.pzIter m (Work.Spaces.DthIter i f) z' θ) z
            + deriv (fun z' => Work.Spaces.pzIter m (Work.Spaces.DthIter i g) z' θ) z :=
        deriv_add hd1 hd2
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
      rw [heq.deriv_eq, hd]

theorem F0_add {n : ℕ} {K K' : ℝ} {f g : ℝ → ℝ → ℝ} (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g) (hf : Work.FTS.PhiStar.F0 n K f) (hg : Work.FTS.PhiStar.F0 n K' g) : Work.FTS.PhiStar.F0 n (K + K') (fun z θ => f z θ + g z θ) := by
  intro k i hki z θ hz h1 h2
  have hsum := pzIter_DthIter_add_Q0 hsf hsg i k z θ hz h1 h2
  rw [hsum, mul_add]
  exact le_trans (abs_add_le _ _)
    (add_le_add (hf k i hki z θ hz h1 h2) (hg k i hki z θ hz h1 h2))

end Work.FTS.PhiStar.CoreAux
