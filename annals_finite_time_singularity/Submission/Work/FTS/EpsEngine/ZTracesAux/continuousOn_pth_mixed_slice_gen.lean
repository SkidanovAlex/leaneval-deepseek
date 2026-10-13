import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXA1w.Helpers
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS.H2.LinfQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.ZTracesAux

/-!
# Continuity of the angular slice of `∂_θ (D_z^b D_θ^a f)`

Let `f` be of class `C^N` on the **open** quadrant `Q0 = (0,∞) × (0,π/2)` and let
`a + b + 1 ≤ N`.  Then for every fixed `s > 0` the angular slice

  `σ ↦ ∂_θ (D_z^b D_θ^a f) (s, σ)`

is continuous on `(0, π/2)`.

This is the general-`N` form of what the `C⁴`-versions of the slice calculus
(`Work.FTS_RegExport.RXA1w.continuousOn_pth_mixed_slice_aux`,
`Work.FTS_RegExport.C4.Dth_mixed_eq_C4`) provide, and it is what the finite-order engine
`Work.FTS.StrongEps.contDiffOn_uncurry_pth_fin` is designed for: the mixed slot
`D_z^b D_θ^a f` is `C¹` on the open quadrant `Q0` as soon as `f` is `C^{1+a+b}` there
(`Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_shift`), and *one* further `∂_θ` of a
`C¹` function on an open set is continuous on that set.  Restricting to the slice `z = s`
with `s > 0` (so that the slice lies in `Q0`) concludes.

No endpoint information at `θ = 0, π/2` is used or produced: the statement is genuinely an
*open-interval* one, consistent with `ContDiffOn` on the open quadrant.
-/

/-- **The angular slice of `∂_θ(D_z^bD_θ^a f)` is continuous on `(0,π/2)`.** -/
theorem continuousOn_pth_mixed_slice_gen {f : ℝ → ℝ → ℝ} {N : ℕ}
    (hF : ContDiffOn ℝ N (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (b a : ℕ) (hab : a + b + 1 ≤ N) {s : ℝ} (hs : 0 < s) :
    ContinuousOn (fun σ => Work.Spaces.pth (Work.Spaces.mixed b a f) s σ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  -- `f` is `C^{1+a+b}`, which is all that the identity `N ≥ a+b+1` gives us.
  have hab1 : 1 + a + b ≤ N := by omega
  have h1 : ContDiffOn ℝ (1 + a + b) (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    hF.of_le (Nat.cast_le.mpr hab1)
  -- hence the mixed slot `D_z^b D_θ^a f` is `C¹` on the open quadrant …
  have hG : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed b a f))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXA1w.contDiffOn_uncurry_mixed_shift
      Work.FTS.EllipticEst.isOpen_Q0 b a 1 h1
  -- … and therefore its `θ`-partial is `C⁰`, i.e. continuous, on the open quadrant.
  have hp : ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.mixed b a f)))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongEps.contDiffOn_uncurry_pth_fin Work.FTS.EllipticEst.isOpen_Q0 hG).continuousOn
  -- The slice `σ ↦ (s, σ)` maps `(0,π/2)` into `Q0` because `s > 0`.
  have hlin : ContinuousOn (fun σ : ℝ => (s, σ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hmaps : Set.MapsTo (fun σ : ℝ => (s, σ)) (Set.Ioo (0 : ℝ) (Real.pi / 2))
      Work.FTS.EllipticEst.Q0 := fun σ hσ => Work.FTS.EllipticEst.mem_Q0.mpr ⟨hs, hσ⟩
  refine (hp.comp hlin hmaps).congr (fun σ _ => rfl)

end Work.FTS.EpsEngine.ZTracesAux
