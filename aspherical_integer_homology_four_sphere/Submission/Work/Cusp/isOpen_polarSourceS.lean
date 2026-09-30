/-
# The source of the `(c,k)`-th polar chart is open

`polarSourceS v c k B` (`Work.Cusp.Charts`) is the set of points `z = (p,y)` of the `(p,y)`-cover of
the filling piece whose layer parameter is `> 1/24` (`r > 1/4`), whose direction `p` lies in the
`(c,k)`-shifted wedge `wedgeS c k`, and whose polar coordinates `ThetaPolarS v c p y` lie in `B`.

It is the intersection of three conditions, and it is open as soon as `B` is:

* `{z | z.1 ∈ wedgeS c k}` is the preimage under the (continuous) first projection of the open
  wedge `wedgeS c k` (`isOpen_wedgeS`);
* `{z | 1/24 < nrm z.1}` is the preimage under the continuous map `z ↦ nrm z.1`
  (`nrm_continuous`) of the open halfline `(1/24, ∞)`;
* on the intersection `s` of the two, the chart `ThetaPolarS v c` is continuous
  (`ThetaPolarS_continuousOn`), so the preimage of the open `B` is open *relative to `s`*
  (`ContinuousOn.isOpen_inter_preimage`).
-/
import Mathlib
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.ThetaPolarS_continuousOn
import Submission.Work.Cusp.isOpen_wedgeS
import Submission.Work.Cusp.nrm_continuous

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- **The source of the `(c,k)`-th polar chart is open.**  The wedge and the layer bound are open
conditions on `p`, and `ThetaPolarS v c` is continuous on the wedge, so the preimage of the open
target `B` is open relative to the wedge. -/
theorem isOpen_polarSourceS (v : Fin 5) (c : ℝ) (k : Fin 4) (B : Set E4) (hB : IsOpen B) :
    IsOpen (polarSourceS v c k B) := by
  have hwedge : IsOpen {z : E2 × E2 | z.1 ∈ wedgeS c k} :=
    (isOpen_wedgeS c k).preimage continuous_fst
  have hnrm : IsOpen {z : E2 × E2 | (1 : ℝ) / 24 < nrm z.1} :=
    isOpen_lt continuous_const (nrm_continuous.comp continuous_fst)
  have ht : IsOpen ({z : E2 × E2 | z.1 ∈ wedgeS c k} ∩ {z : E2 × E2 | (1 : ℝ) / 24 < nrm z.1}) :=
    hwedge.inter hnrm
  have hcont : ContinuousOn (fun z : E2 × E2 => ThetaPolarS v c z.1 z.2)
      ({z : E2 × E2 | z.1 ∈ wedgeS c k} ∩ {z : E2 × E2 | (1 : ℝ) / 24 < nrm z.1}) :=
    (ThetaPolarS_continuousOn v c k).mono Set.inter_subset_left
  rw [show polarSourceS v c k B = ({z : E2 × E2 | z.1 ∈ wedgeS c k} ∩
        {z : E2 × E2 | (1 : ℝ) / 24 < nrm z.1}) ∩
        (fun z : E2 × E2 => ThetaPolarS v c z.1 z.2) ⁻¹' B by
      ext z; simp [polarSourceS, and_assoc]]
  exact hcont.isOpen_inter_preimage ht hB

end Work.Cusp
