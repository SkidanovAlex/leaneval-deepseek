import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllSol.VopAux.SliceTraceDefs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
import Submission.Work.FTS.EllSol.WeakSlice.sliceV_DzIter_smoothOpen
import Submission.Work.FTS.EllipticEst.ThetaSliceIdent

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.VopAux

/-
# The single-slice functional of `D_z^j (∂_θ² f)` and of the second derivative of the slice agree

For `f` of class `C^∞` on the open quadrant, `z > 0` and interior angles `θ ∈ (0,π/2)`:

  `sliceW K α (fun θ' => D_z^j (pthIter 2 f) z θ') θ
     = sliceW K α (sliceV (fun θ' => D_z^j f z θ')) θ`,

where `sliceW K α u θ = (u θ)²thEta θ + ∑_{1≤i≤K}(L^i u θ)²thGam α θ` (see
`Submission/Work/FTS/EllSol/VopAux/SliceTraceDefs.lean`), `sliceV u = deriv (deriv u)` and
`pthIter 2 f = ∂_θ² f`.

This is the bridge that lets the single-slice estimate be applied to the `j`-th slice of `f` with
the datum taken from the `j`-th slice group of `∂_θ² f`.

ROUTE. First, the two functions of `θ'` agree at every `θ' ∈ (0,π/2)`:
`pthIter 2 (D_z^j f) z θ' = D_z^j (pthIter 2 f) z θ'` — the open-quadrant Clairaut identity,
which is `pth_DzIter_eqOn_of_isOpen` from
`Submission/Work/FTS/EllipticEst/ThetaU/OpenSliceAux/pth_DzIter_eqOn_of_isOpen.lean` applied twice
(it works for an arbitrary open set `V` with the raw `∀ n, ContDiffOn ℝ n` hypothesis; take
`V = Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)` and the open-quadrant smoothness of `f`; the hypothesis for the
second application, smoothness of `pth f`, comes from `SmoothOpen.pth`-style closure, which for the
raw `∀ n` hypothesis is `Work.FTS.LocData.contDiffOn_pth`). Since
`sliceV (fun θ' => D_z^j f z θ') = fun θ' => pthIter 2 (D_z^j f) z θ'` definitionally, the two
functions agree on the whole open interval `(0,π/2)`.
Second, two functions equal on the open interval have the same `L`-iterates at every interior
point: `deriv` is local, so `Filter.EventuallyEq.deriv_eq` (with `isOpen_Ioo.mem_nhds` at an
interior point) gives equality of the first derivatives on `(0,π/2)`, and induction on `i` gives
`LopIter i u₁ θ = LopIter i u₂ θ` for `θ ∈ (0,π/2)`. Both terms of `sliceW` are then equal,
including the zeroth-order terms `(u θ)²thEta θ`.

The first step is available ready-made: `Work.FTS.EllSol.WeakSlice.sliceV_DzIter_smoothOpen`
(`Submission/Work/FTS/EllSol/WeakSlice/sliceV_DzIter_smoothOpen.lean`) states exactly
`deriv (deriv (fun θ' => D_z^j f z θ')) θ' = D_z^j (∂_θ² f) z θ'` for a datum which is `C^∞` on
the open quadrant, i.e. for the `SmoothOpen f` obtained from `hf` by
`Work.FTS.EllipticEst.smoothOpen_iff_forall`.  The second step is the *locality* of the
functional: `sliceW` only sees the germ of its argument, since `LopIter m u θ = LopIter m v θ`
whenever `u =ᶠ[𝓝 θ] v` (`Work.FTS.EllipticEst.LopIter_congr_nhds`, proved by induction on `m`
from the locality of `deriv`).  Together with the agreement of the two functions at every
interior angle this closes the statement.
-/
/-- The single-slice functional `sliceW` only sees the germ of its argument: two functions which
agree near `θ` have the same value of `sliceW K α · θ`, because both the zeroth-order term and
every `L`-iterate are local. -/
lemma sliceW_congr_nhds {u v : ℝ → ℝ} {θ : ℝ} (h : u =ᶠ[𝓝 θ] v) (K : ℕ) (α : ℝ) :
    sliceW K α u θ = sliceW K α v θ := by
  have hθ : u θ = v θ := h.self_of_nhds
  rw [sliceW, sliceW, hθ]
  congr 1
  exact Finset.sum_congr rfl fun i _ =>
    congrArg (fun x => x ^ 2 * Work.FTS.EllipticEst.thGam α θ)
      (Work.FTS.EllipticEst.LopIter_congr_nhds h i)

theorem sliceW_pthIter2_eq_sliceW_sliceV (α : ℝ) (K j : ℕ) (f : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllSol.VopAux.sliceW K α
          (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ') θ
        = Work.FTS.EllSol.VopAux.sliceW K α
            (Work.FTS.EllipticEst.sliceV (fun θ' => Work.Spaces.DzIter j f z θ')) θ := by
  have hfS : Work.FTS.EllipticEst.SmoothOpen f :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mpr hf
  -- the two functions agree at every interior angle
  have hpt : ∀ θ' ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.Spaces.DzIter j (Work.Spaces.pthIter 2 f) z θ'
        = Work.FTS.EllipticEst.sliceV (fun θ'' => Work.Spaces.DzIter j f z θ'') θ' :=
    fun θ' hθ' =>
      (Work.FTS.EllSol.WeakSlice.sliceV_DzIter_smoothOpen hfS j hz hθ').symm
  intro θ hθ
  -- hence they agree near `θ`, and `sliceW` is local
  refine sliceW_congr_nhds (v := fun θ' => Work.FTS.EllipticEst.sliceV
      (fun θ'' => Work.Spaces.DzIter j f z θ'') θ') ?_ K α
  filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
  exact hpt θ' hθ'

end Work.FTS.EllSol.VopAux
