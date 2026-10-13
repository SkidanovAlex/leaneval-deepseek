import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The odd extension in `θ` does not change `bslOp` for `θ > 0`

The odd extension `PhiOdd Φ` of a self-similar family `Φ` agrees with `Φ` on the whole open
half-plane `θ > 0`.  Since `bslOp` is built from the partial derivatives `pz`, `pzIter 2`, `pth`
and `pthIter 2` — each of which is a *derivative in one variable at a fixed value of the other*,
hence depends only on the germ of the corresponding slice — the value of `bslOp` at a point
`(z,θ)` with `θ > 0` is unchanged by passing to the odd extension.

The proof is therefore pure germ bookkeeping:

* the `z`-slices at the fixed angle `θ > 0` are *equal as functions* (not merely eventually
  equal), so `pz` and `pzIter 2` agree;
* the `θ`-slices are equal on the open set `θ' > 0`, hence eventually equal near `θ`; this gives
  `pth` and, applied at every `θ' > 0`, also `pthIter 2` (via `Filter.EventuallyEq.deriv_eq`).

No differentiability hypothesis on `Φ` is needed: `deriv` is a total function and the two
functions being differentiated have the same germ.
-/

noncomputable section

open scoped Real Topology
open Filter

namespace Work.FTS.BSIdent.OddExt

variable {Φ : Work.FTS.BSIdent.Fam}

/-- For `θ > 0` the odd extension takes the value of the original family. -/
theorem PhiOdd_eq_self_of_pos {z θ τ : ℝ} (hθ : 0 < θ) :
    Work.FTS.BSIdent.PhiOdd Φ z θ τ = Φ z θ τ :=
  Work.FTS.BSIdent.PhiOdd_of_nonneg (le_of_lt hθ)

/-- The `θ`-slices of `PhiOdd Φ` and of `Φ` agree eventually near every `θ > 0`. -/
theorem PhiOdd_eventuallyEq_of_pos {z θ τ : ℝ} (hθ : 0 < θ) :
    (fun θ' => Work.FTS.BSIdent.PhiOdd Φ z θ' τ) =ᶠ[𝓝 θ] fun θ' => Φ z θ' τ :=
  (eventually_gt_nhds hθ).mono fun _ h' => PhiOdd_eq_self_of_pos (Φ := Φ) h'

/-- `∂_z` of the odd extension at `θ > 0`. -/
theorem pz_PhiOdd_of_pos {z θ τ : ℝ} (hθ : 0 < θ) :
    Work.Spaces.pz (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = Work.Spaces.pz (fun z' θ' => Φ z' θ' τ) z θ := by
  simp only [Work.Spaces.pz]
  rw [show (fun z' => Work.FTS.BSIdent.PhiOdd Φ z' θ τ) = fun z' => Φ z' θ τ from
    funext fun z' => PhiOdd_eq_self_of_pos (Φ := Φ) hθ]

/-- `∂_z^2` of the odd extension at `θ > 0`. -/
theorem pzIter_two_PhiOdd_of_pos {z θ τ : ℝ} (hθ : 0 < θ) :
    Work.Spaces.pzIter 2 (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = Work.Spaces.pzIter 2 (fun z' θ' => Φ z' θ' τ) z θ := by
  show deriv (fun z' => deriv (fun z'' => Work.FTS.BSIdent.PhiOdd Φ z'' θ τ) z') z
      = deriv (fun z' => deriv (fun z'' => Φ z'' θ τ) z') z
  rw [show (fun z' => deriv (fun z'' => Work.FTS.BSIdent.PhiOdd Φ z'' θ τ) z')
      = fun z' => deriv (fun z'' => Φ z'' θ τ) z' from
    funext fun z' => pz_PhiOdd_of_pos (Φ := Φ) (z := z') hθ]

/-- `∂_θ` of the odd extension at `θ > 0`. -/
theorem pth_PhiOdd_of_pos {z θ τ : ℝ} (hθ : 0 < θ) :
    Work.Spaces.pth (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = Work.Spaces.pth (fun z' θ' => Φ z' θ' τ) z θ := by
  simp only [Work.Spaces.pth]
  exact (PhiOdd_eventuallyEq_of_pos (Φ := Φ) (z := z) hθ).deriv_eq

/-- `∂_θ^2` of the odd extension at `θ > 0`. -/
theorem pthIter_two_PhiOdd_of_pos {z θ τ : ℝ} (hθ : 0 < θ) :
    Work.Spaces.pthIter 2 (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = Work.Spaces.pthIter 2 (fun z' θ' => Φ z' θ' τ) z θ := by
  show deriv (fun θ' => Work.Spaces.pth
        (fun z' θ'' => Work.FTS.BSIdent.PhiOdd Φ z' θ'' τ) z θ') θ
      = deriv (fun θ' => Work.Spaces.pth (fun z' θ'' => Φ z' θ'' τ) z θ') θ
  refine (Filter.EventuallyEq.deriv_eq ?_)
  exact (eventually_gt_nhds hθ).mono fun _ h' => pth_PhiOdd_of_pos (Φ := Φ) (z := z) h'

/-- `∂_θ(tan θ · ·)` of the odd extension at `θ > 0`. -/
theorem pth_tan_mul_PhiOdd_of_pos {z θ τ : ℝ} (hθ : 0 < θ) :
    Work.Spaces.pth (fun z' θ' => Real.tan θ' * Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = Work.Spaces.pth (fun z' θ' => Real.tan θ' * Φ z' θ' τ) z θ := by
  simp only [Work.Spaces.pth]
  refine (Filter.EventuallyEq.deriv_eq ?_)
  exact Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ (fun θ' : ℝ => Real.tan θ'))
    (PhiOdd_eventuallyEq_of_pos (Φ := Φ) (z := z) hθ)

/-- `Lzero` of the odd extension at `θ > 0`. -/
theorem Lzero_PhiOdd_of_pos {z θ τ : ℝ} (hθ : 0 < θ) :
    Work.Elliptic.Lzero (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = Work.Elliptic.Lzero (fun z' θ' => Φ z' θ' τ) z θ := by
  simp only [Work.Elliptic.Lzero, pthIter_two_PhiOdd_of_pos (Φ := Φ) hθ,
    pth_tan_mul_PhiOdd_of_pos (Φ := Φ) hθ, PhiOdd_eq_self_of_pos (Φ := Φ) hθ]

theorem bslOp_PhiOdd_of_pos {p : ℝ} {Φ : Work.FTS.BSIdent.Fam} {z θ τ : ℝ} (hθ : 0 < θ) :
    Work.Elliptic.bslOp p (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = Work.Elliptic.bslOp p (fun z' θ' => Φ z' θ' τ) z θ := by
  simp only [Work.Elliptic.bslOp_apply, pzIter_two_PhiOdd_of_pos (Φ := Φ) hθ,
    pz_PhiOdd_of_pos (Φ := Φ) hθ, Lzero_PhiOdd_of_pos (Φ := Φ) hθ]

end Work.FTS.BSIdent.OddExt
