import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceIdents
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.WeakSlice

set_option autoImplicit false

/-! ## The `Q0` instances of the open-set Clairaut identities

The generic modules `ThetaU/OpenSliceAux/{pth_DzIter_eqOn_of_isOpen,DthIter_DzIter_eqOn_of_isOpen}`
prove the Clairaut identities on an *arbitrary* open set `V` carrying the regularity class
`∀ n, ContDiffOn ℝ n (uncurry g) V`.  The open-quadrant class `SmoothOpen` is exactly that class
at `V = Q0` (`Work.FTS.EllipticEst.smoothOpen_iff_forall`), so the identities instantiate at
once; what is left is to read them pointwise at an interior point and to iterate `∂_θ` once
more, exactly as in the half-strip version `ThetaU.OpenSliceIdents.pth_DzIter_open` /
`pthIter_two_DzIter_open`. -/

/-- **`∂_θ (D_z^j f) = D_z^j (∂_θ f)` for an open-quadrant datum.**  Pointwise form of
`Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen` specialised to `Q0`. -/
theorem pth_DzIter_Q0 {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (j : ℕ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pth (Work.Spaces.DzIter j f) z θ
      = Work.Spaces.DzIter j (Work.Spaces.pth f) z θ := by
  have h := Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
    Work.FTS.EllipticEst.isOpen_Q0 (fun n => hf.forall n) j
  exact h (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)

/-- **The second `θ`-derivative commutes with `D_z^j` for an open-quadrant datum.**  Pointwise
form of `pthIter_two_DzIter_open` with `Q0` in place of the half-strip: `∂_θ` is compared
across `D_z^j` by `pth_DzIter_Q0` (applied to `∂_θ f`, which is again `SmoothOpen`), and the
two resulting functions agree on the open set `Q0`, so their `∂_θ` agree at the point
(`Work.Spaces.pth_congr_of_isOpen`). -/
theorem pthIter_two_DzIter_Q0 {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (j : ℕ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pthIter 2 (Work.Spaces.DzIter j f) z θ
      = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hEq : Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter j f)))
      (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.pth f)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 (fun n => hf.forall n) j
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  rw [Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq hmem]
  exact pth_DzIter_Q0 hf.pth j hz hθ

/-
**The second `θ`-derivative of the slice `θ' ↦ D_z^j f z θ'` is the slice of `D_z^j (∂_θ² f)`.**

At an interior point `(z,θ) ∈ Q0 = (0,∞) × (0,π/2)` of an open-quadrant datum
(`SmoothOpen f`, i.e. `C^∞` on `Q0`):

  `deriv (deriv (fun θ' => D_z^j f z θ')) θ = D_z^j (pthIter 2 f) z θ`.

This is `Work.FTS.EllipticEst.ThetaU.sliceV_DzIter_open` with the hypothesis `SmoothOpenθ f`
(C^∞ on the half-strip `(0,∞) × (-1, π/2+1)`) weakened to `SmoothOpen f` (C^∞ only on the open
quadrant) and the angle restricted to the interior; equivalently it is
`pthIter_two_DzIter_open` (same file) at interior points.

Route: the identity `∂_θ² (D_z^j f) = D_z^j (∂_θ² f)` is a Clairaut/commutation statement for
`∂_θ` and `D_z = z ∂_z`, both of which are local.  Two generic (arbitrary open set `V`)
ingredients are already proved and are the natural building blocks:
`Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen` and
`...OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen` (Clairaut for `D_θ`/`D_z` on `V`, with
`∀ n, ContDiffOn ℝ n (uncurry g) V` as the regularity class), together with
`Work.Spaces.pth_congr_of_isOpen` / `Work.Spaces.pz_congr_of_isOpen` (comparison of two
derivatives at a point from their equality on an open set) and the API of
`Submission.Work.FTS.EllipticEst.OpenQDefs` (`SmoothOpen.DzIter`, `SmoothOpen.pth`,
`SmoothOpen.DzIter`, `isOpen_Q0`, `SmoothOpen.hasDerivAt_slice_DzIter`).  The proof of the
existing half-strip version (`ThetaU.OpenSliceIdents.sliceV_DzIter_open`,
`pthIter_two_DzIter_open`, `pth_DzIter_open`) can be followed verbatim with `Q0` in place of
`halfStrip`; nothing needs the angular smoothness beyond `0` and `π/2`.
-/
theorem sliceV_DzIter_smoothOpen {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (j : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    deriv (deriv (fun θ' : ℝ => Work.Spaces.DzIter j f z θ')) θ
      = Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ := by
  show deriv (deriv (fun θ' : ℝ => Work.Spaces.DzIter j f z θ')) θ = _
  rw [show deriv (fun θ' : ℝ => Work.Spaces.DzIter j f z θ')
      = fun θ' => Work.Spaces.pth (Work.Spaces.DzIter j f) z θ' from rfl]
  rw [show deriv (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.DzIter j f) z θ') θ
      = Work.Spaces.pthIter 2 (Work.Spaces.DzIter j f) z θ from rfl]
  exact pthIter_two_DzIter_Q0 hf j hz hθ

end Work.FTS.EllSol.WeakSlice
