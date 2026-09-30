/-
# The core layer of a filling piece lies in the range of the core coordinate inclusion of `M̂`

`Work.Cusp.coreCoordM a v tor W` (`Work.Cusp.Assembly`) is the coordinate inclusion of the core
chart of the `v`-th filling piece into the assembled space `M̂`:

  `coreCoordM a v tor W q = incW v (p(q), [y(q)])`,

where `(p(q), y(q)) = cuspInvCore v q` is the point of the cover `E2 × E2` of the filling piece
whose *Cartesian* core coordinates are `q ∈ coreBoxSect W` and `[y(q)]` is the class of the two
torus coordinates in `a.Torus v` (transported by the homeomorphism
`tor : a.Torus v ≃ₜ (Fin 2 → AddCircle 1)`).

This file proves the **core layer** instance of the cover at the level of a single filling piece:
every point of `M̂` whose layer parameter satisfies `‖p‖∞ < 1/12` (the core stratum, i.e. the core
disk `r < 1/2`) lies in the range of `coreCoordM a v tor W` for a suitable *local section* `W` of
the quotient `E2 → (ℝ/ℤ)²` in the `w`-coordinates — the same kind of `W` as in
`Work.Cusp.exists_section_box`, on which the `w`-coordinates determine the cusp coordinates modulo
`ℤ²`.

The point of the cover that maps to `incW v (p, y)` is the Cartesian core coordinate of `(p, y)`,
namely `q = ThetaCore v p w`, where `w ∈ E2` is any lift of `tor y` to `ℝ²`.  Indeed

* `cuspInvCore v (ThetaCore v p w) = (p, w)` (`Work.Cusp.cuspInvCore_ThetaCore`), so the layer point
  recovered by the chart is `p` and the recovered torus coordinates are `w`, whose class is `tor y`;
* `ThetaCore v p w` lies in the core box section: the radial coordinate is
  `r = 2 r_J ‖p‖∞ = 6 ‖p‖∞ < 6/12 = 1/2` (`Work.Cusp.radial_eq_inner`, valid because
  `‖p‖∞ < 1/12 ≤ 1/2`), and the last two coordinates are `wOf v w ∈ W`.

The layer `coreLayer = {q | ‖q.1‖∞ < 1/12}` is the core stratum of `Work.Cusp`, the one on which the
core charts (`Work.Cusp.coreChart` on the filling piece, and `Work.Cusp.coreChart` of
`Work.Cusp.ChartMhat` on `M̂`) cover the filling piece; the other two layer lemmas are
`Work.Cusp.polarLayer_subset_range_polarCoordM` and
`Work.Cusp.collarLayer_subset_range_cuspCoordMTop`.
-/
import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.exists_section_box
import Submission.Work.Cusp.exists_coreChartM
import Submission.Work.Cusp.cuspInvCore_ThetaCore
import Submission.Work.Cusp.cuspInvCore_mem_coreStratum
import Submission.Work.Cusp.ThetaCore_cuspInvCore
import Submission.Work.Cusp.radial_eq_inner

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Real InnerProductSpace

open Set Topology

namespace Work.Cusp

/-- `√((r cos θ)² + (r sin θ)²) = r` for `r ≥ 0`: the radial coordinate of the Cartesian core
coordinates `(r cos θ, r sin θ)`. -/
private lemma core_sqrt_sq_cos_sin {r θ : ℝ} (hr : 0 ≤ r) :
    Real.sqrt ((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) = r := by
  have h : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    have hs := Real.sin_sq_add_cos_sq θ
    nlinarith [hs]
  rw [h, Real.sqrt_sq_eq_abs, abs_of_nonneg hr]

theorem coreLayer_subset_range_coreCoordM (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (y : a.Torus v)
    (p : Work.Space.SquarePt) (hp : nrm (p : E2) < 1/12) :
    ∃ W : Set E2, IsOpen W ∧
      (∀ y' y'' : E2, wOf v y' ∈ W → wOf v y'' ∈ W →
        (∀ i, ((y' i : ℝ) : AddCircle (1 : ℝ)) = ((y'' i : ℝ) : AddCircle (1 : ℝ))) → y' = y'') ∧
      a.incW v (p, y) ∈ Set.range (coreCoordM a v tor W) := by
  -- a real lift `w` of the torus point `y` under `tor`
  have hlift : ∀ i : Fin 2, ∃ s : ℝ, (s : AddCircle (1 : ℝ)) = (tor y) i :=
    fun i => QuotientAddGroup.mk'_surjective _ _
  choose w0 hw0 using hlift
  set w : E2 := !₂[w0 0, w0 1] with hwdef
  have hw : ∀ i : Fin 2, ((w i : ℝ) : AddCircle (1 : ℝ)) = (tor y) i := by
    intro i; fin_cases i <;> simpa [hwdef] using hw0 _
  -- a local section `W` of the `w`-coordinates around `wOf v w`
  obtain ⟨W, hWopen, hWmem, hWsec⟩ := exists_section_box v w
  refine ⟨W, hWopen, hWsec, ?_⟩
  -- the Cartesian core coordinates of `(p, w)`
  set q : E4 := ThetaCore v (p : E2) w with hqdef
  have hIC : cuspInvCore v q = ((p : E2), w) := by
    rw [hqdef]; exact cuspInvCore_ThetaCore v (p : E2) w
  have hq0 : q 0 = radial v (p : E2) w * Real.cos (thetaAng v (p : E2) w) := by
    rw [hqdef]; simp [ThetaCore]
  have hq1 : q 1 = radial v (p : E2) w * Real.sin (thetaAng v (p : E2) w) := by
    rw [hqdef]; simp [ThetaCore]
  have hq23 : (!₂[q 2, q 3] : E2) = wOf v w := by
    rw [hqdef]; exact CoreChartM.ccm_thetaCore_coord23 v (p : E2) w
  have hp_le : nrm (p : E2) ≤ 1/2 := by linarith [nrm_nonneg (p : E2)]
  have hrad : radial v (p : E2) w = 6 * nrm (p : E2) := by
    rw [radial_eq_inner v (p : E2) w hp_le]; norm_num [rJ]
  have hrnn : 0 ≤ radial v (p : E2) w := by
    rw [hrad]; linarith [nrm_nonneg (p : E2)]
  -- `q` lies in the core box section
  have hq_sqrt : Real.sqrt (q 0 ^ 2 + q 1 ^ 2) < 1/2 := by
    rw [hq0, hq1, core_sqrt_sq_cos_sin hrnn, hrad]
    linarith
  have hq_w : (!₂[q 2, q 3] : E2) ∈ W := by rw [hq23]; exact hWmem
  have hqmem : q ∈ coreBoxSect W := ⟨hq_sqrt, hq_w⟩
  refine ⟨⟨q, hqmem⟩, ?_⟩
  have htor : tor.symm (fun i : Fin 2 => ((w i : ℝ) : AddCircle (1 : ℝ))) = y := by
    rw [show (fun i : Fin 2 => ((w i : ℝ) : AddCircle (1 : ℝ))) = tor y from funext hw,
      Homeomorph.symm_apply_apply]
  -- the class of the recovered coordinates is `y`, and the recovered layer point is `p`
  rw [CoreChartM.ccm_coreCoordM_eq_comp]
  have hgoal : CoreChartM.ccmFillProj a v tor (CoreChartM.ccmCoreInv v W ⟨q, hqmem⟩) = (p, y) := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun z : E2 × E2 => z.1) hIC
    · show tor.symm (fun i => (((cuspInvCore v q).2 i : ℝ) : AddCircle (1 : ℝ))) = y
      rw [congrArg (fun z : E2 × E2 => z.2) hIC]
      exact htor
  rw [show (a.incW v ∘ CoreChartM.ccmFillProj a v tor ∘ CoreChartM.ccmCoreInv v W) ⟨q, hqmem⟩
      = a.incW v (CoreChartM.ccmFillProj a v tor (CoreChartM.ccmCoreInv v W ⟨q, hqmem⟩)) from rfl,
    hgoal]

end Work.Cusp
