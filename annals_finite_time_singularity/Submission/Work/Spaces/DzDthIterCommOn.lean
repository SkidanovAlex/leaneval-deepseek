/-
Copyright: work module for the Elgindi finite-time singularity project.

# `D_z` commutes with every iterate of `D_θ`, on an open set

The curvilinear operators `D_z f = z ∂_z f` and `D_θ f = sin(2θ) ∂_θ f` commute at every
point where `f` is `C²`; this is `Work.Spaces.Dz_Dth_comm` in
`Submission.Work.Spaces.mixed_comm`.  Here we upgrade that pointwise identity to an
identity on an arbitrary *open* set `V` on which the (uncurried) function `g` is `C^∞`:

`D_z (D_θ^i g) = D_θ^i (D_z g)` on `V`, for every `i`.

Both operators are local, so once `V` is open and `g` is smooth on `V`, the identity is a
purely pointwise statement: at a point `y ∈ V` the function `g` is `C^∞` near `y`, hence
`D_θ^i g` is `C²` near `y` (by `DthIter_contDiffAt`), and the two sides may be compared
locally.  The induction on `i` needs one extra ingredient: the *θ*-derivative of two
functions that agree on an open set containing a point agree at that point.  That is the
first lemma below, a straightforward strengthening of `Work.Spaces.pth_congr` (which is
stated for the fixed open set `nbhU` of `SmoothNbhd`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.DthIter_contDiffAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

/-! ## Congruence of `pth` on an open set -/

/-- Functions that agree on an open set containing `(z,θ)` have the same `θ`-slice
derivative at `(z,θ)`. -/
lemma pth_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) {z θ : ℝ} (hz : (z, θ) ∈ V) :
    pth f z θ = pth f' z θ := by
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ V :=
    (Continuous.prodMk_right z).continuousAt.eventually (hV.mem_nhds hz)
  have hslice : (fun θ' => Function.uncurry f (z, θ')) =ᶠ[𝓝 θ]
      (fun θ' => Function.uncurry f' (z, θ')) := by
    filter_upwards [hnb] with θ' hθ'
    exact h hθ'
  simpa only [pth, Function.uncurry] using hslice.deriv_eq

/-- Functions that agree on an open set containing `(z,θ)` have the same `z`-slice
derivative at `(z,θ)`. -/
lemma pz_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : EqOn (Function.uncurry f) (Function.uncurry f') V) {z θ : ℝ} (hz : (z, θ) ∈ V) :
    pz f z θ = pz f' z θ := by
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
    (Continuous.prodMk_left θ).continuousAt.eventually (hV.mem_nhds hz)
  have hslice : (fun z' => Function.uncurry f (z', θ)) =ᶠ[𝓝 z]
      (fun z' => Function.uncurry f' (z', θ)) := by
    filter_upwards [hnb] with z' hz'
    exact h hz'
  simpa only [pz, Function.uncurry] using hslice.deriv_eq

/-! ## The commutation identity -/

/-- On an open set `V` on which `g` is `C^∞`, the operator `D_z` commutes with every
iterate of `D_θ`: `D_z (D_θ^i g) = D_θ^i (D_z g)` on `V`. -/
theorem DzDthIterCommOn {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ ⊤ (Function.uncurry g) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i g)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz g))) V := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      -- `g` is `C^∞` at `y`, hence so is `D_θ^i g`.
      have hgy : ContDiffAt ℝ ⊤ (Function.uncurry g) y := hg.contDiffAt (hV.mem_nhds hy)
      have hF : ContDiffAt ℝ ⊤ (Function.uncurry (DthIter i g)) y :=
        DthIter_contDiffAt g i hgy
      -- Move the outer `D_z` past the `D_θ` using Clairaut at `y`.
      have hcomm : Dz (Dth (DthIter i g)) y.1 y.2
          = Dth (Dz (DthIter i g)) y.1 y.2 :=
        Dz_Dth_comm (f := DthIter i g) (hF.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ ⊤))
      show Dz (Dth (DthIter i g)) y.1 y.2 = Dth (DthIter i (Dz g)) y.1 y.2
      rw [hcomm]
      -- The two functions now agree on the open set `V` by the induction hypothesis,
      -- so their `θ`-derivatives agree at `y`.
      show Real.sin (2 * y.2) * pth (Dz (DthIter i g)) y.1 y.2
          = Real.sin (2 * y.2) * pth (DthIter i (Dz g)) y.1 y.2
      rw [pth_congr_of_isOpen hV ih hy]

end Work.Spaces
