import Mathlib
import Submission.Work.Wilkies.CG.C4a.Spec
import Submission.Work.WilC4aRW.Main
import Submission.Work.WilC4aAL.SpecAlias
import Submission.Work.WilC4aP.Main
import Submission.Work.WilC4aTS.TS
import Submission.Work.WilC4aCS.CurveSelStep
import Submission.Work.WilE7.FrontierDropFromDimDrop
import Submission.Work.WilE7.FrontierCS.Defs
import Submission.Work.WilE7.FrontierCS.grid_cover
import Submission.Work.WilE7.FrontierCS.slice_reduction
import Submission.Work.WilE7.FrontierCS.restrict_chart
import Submission.Work.WilE7.FrontierCS.le_of_range_top
import Submission.Work.WilE7.FrontierCS.isOpen_fst_image_sliceSet
import Submission.Work.WilE7.FrontierCS.nondegZeros_not_accum
import Submission.Work.WilE7.FrontierCS.multiAffine_eq_zero
import Submission.Work.WilE7.FrontierCS.exists_real_det_ne_zero
import Submission.Work.WilE7.FrontierCS.exists_grid_det_ne_zero
import Submission.Work.WilE7.FrontierCS.exists_complement
import Submission.Work.WilE7.FrontierCS.mem_closure_preimage
import Submission.Work.WilE7.FrontierCS.exists_open_subset_of_finite_closed_cover
import Submission.Work.WilE7.FrontierCS.exists_mem_iInter_of_dense_in_open
import Submission.Work.WilE7.FrontierCS.analyticOnNhd_jacDet
import Submission.Work.WilE7.FrontierCS.jacDet_ne_zero_iff
import Submission.Work.WilE7.FrontierCS.eventually_ne_of_range_top

namespace Work.WilE7.FrontierDim

/-!
A cycle-free term of type `Work.WilE7.DimDrop`.

`Submission/Work/WilE7/FrontierDim/dimDrop_via_wpt.lean` proves the same statement with clean
axioms, but it imports `Submission/Work/WilE7/FrontierCS/Main`, and that file imports
`Submission.Work.WilE7.E7_fiber_cut_proved` — so the E7 target cannot use it (import cycle).

The final assembly of the CS-slice route lives in `Submission/Work/WilE7/FrontierCS/Main.lean`
(`dimDrop_of_curveSel`, `curveSel_all`, `dimDrop_proved`); its individual nodes live in the
cycle-free modules under `Submission/Work/WilE7/FrontierCS/` (`Defs`, `grid_cover`,
`slice_reduction`, `restrict_chart`, `le_of_range_top`, `isOpen_fst_image_sliceSet`,
`nondegZeros_not_accum`, `multiAffine_eq_zero`, `exists_real_det_ne_zero`,
`exists_grid_det_ne_zero`, `exists_complement`, `mem_closure_preimage`,
`exists_open_subset_of_finite_closed_cover`, `exists_mem_iInter_of_dense_in_open`,
`analyticOnNhd_jacDet`, `jacDet_ne_zero_iff`, `eventually_ne_of_range_top`).

The assembly of `FrontierCS/Main.lean` (its `dimDrop_of_curveSel` and `curveSel_all`) is
reproduced below verbatim, so that this module is cycle-free and the E7 target can import it.
-/

set_option autoImplicit false

open Classical Filter Topology
open scoped Topology
open WilkiesDesign.CG.C4a
open Work.WilE7.FrontierCS

noncomputable section

/-- **N9. `DimDrop` from curve selection**, reproduced cycle-free (nodes N1, N8, N9a, N9b are
proved in the imported modules under `Submission/Work/WilE7/FrontierCS/`). -/
theorem dimDrop_of_curveSelCS (hCS : ∀ n, CurveSel n) : Work.WilE7.DimDrop := by
  intro N j n G hG W hWZ hWopen hWrk γ hγ hγinj hγW hγrk
  by_cases hj : j = 0
  · -- `j = 0`: the codomain is the zero space, so `range = ⊤` always and `hγrk` is absurd.
    subst hj
    have htop : (fderiv ℝ G (γ 0)).range = ⊤ :=
      Submodule.eq_top_iff'.mpr fun x => by
        rw [Subsingleton.elim x 0]; exact Submodule.zero_mem _
    exact absurd hγrk.self_of_nhds (fun hcon => hcon htop)
  · have hj' : 0 < j := Nat.pos_of_ne_zero hj
    by_contra hlt
    rw [not_lt] at hlt
    -- `W` is nonempty, hence `j ≤ N`
    obtain ⟨s, hs⟩ := hγW.exists
    have hWne : W.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [h, closure_empty] at hs
      exact hs.1
    obtain ⟨w, hw⟩ := hWne
    have hjN : j ≤ N := le_of_range_top _ (hWrk w hw)
    obtain ⟨γ', hγ', hγ'inj, hγ'W⟩ :=
      restrict_chart (d := N - j) hlt hγ hγinj (P := fun z => z ∈ closure W \ W) hγW
    obtain ⟨g, hg, hacc⟩ :=
      slice_reduction (d := N - j) (by omega) hj' hG hWZ hWopen hWrk hγ' hγ'inj hγ'W
    exact nondegZeros_not_accum (hCS j) hg hacc

/-- **The delivered C4a curve selection in every dimension** (sorry-free closure term), so that no
hypothesis is added to `DimDrop`; reproduced cycle-free from the C4a deliverables. -/
theorem curveSel_allCS : ∀ n, CurveSel n := fun n =>
  Nat.rec CurveSel_zero
    (fun n ih => C4a_CS_step_proved C4a_RW_proved
      (C4a_arcLift_proved C4a_puiseux_proved) Work.WilC4aTS.C4a_TS1_proved n ih) n

/-- **`DimDrop` unconditionally**, from the delivered curve selection. -/
theorem dimDropCS : Work.WilE7.DimDrop :=
  dimDrop_of_curveSelCS curveSel_allCS

end

end Work.WilE7.FrontierDim
