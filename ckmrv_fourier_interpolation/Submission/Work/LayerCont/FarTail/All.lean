/-
# The far side (`Re τ > 1`) of the first recurrence of the CKMRV layer — everything in one import

`Submission/Work/LayerCont/FarTail/` carries the **far side** of the first recurrence of the CKMRV
layer: the half-plane `1 < Re τ`, on which

* the pole `z = τ - 1` of the kernel has *positive* real part (so the left detour misses it and its
  residue is **not** cancelled — the chart is `paperLayer + sinSqC r · resCorr r` there), and
* the removable coincidence `ST⁻¹τ = -1/(τ-1)` has *negative* real part (so it is genuinely swept
  by the left detour at height `1/τ.im`, residue-free).

The pieces:

* `Work.LayerCont.FarTail.Defs` — `windowChart` (the chart
  `layerLowDouble + layerTruncAt + highPartAt` under a name) and the reduction
  `windowChart_eq_paperLayer_add_resCorr`.
* `Work.LayerCont.FarTail.Clean` — the far-side cleanliness of the contour from the local web
  classification (`clean_axis_of_web_re_gt_one`, `farClean_of_web`) and the far-side
  non-degeneracy of the translate pole (`jprime_ne_zero_far`).
* `Work.LayerCont.FarTail.CuspFar` — the far-side (*clean*) cusp expansion of the kernel
  `cusp_expansion_of_kernel_of_clean` (the `K ⊆ 𝒟` hypothesis of
  `Work.Asymptotics.cusp_expansion_of_kernel` replaced by the absence of coincidences), and the two
  tail-integrability statements `tail_integrableOn_of_clean` (far side) and
  `tail_integrableOn_of_mem_DomainD` (`𝒟`-side).
* `Work.LayerCont.FarTail.CoincFar` — `coinc_mem_openLeftRect_far`: the coincidence lies inside the
  swept left rectangle when `ε ≤ 1/8`, `16ε ≤ A₂s₀`, `16ε ≤ ξ₂s₀`.
* `Work.LayerCont.FarTail.FarGeom` — `far_orbit_rects`: on the far side the first swept rectangle
  is orbit-free and in the second the only possible orbit point is the coincidence, i.e. the two
  hypotheses `hcl₁, hcl₂` of `Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_far`.
* `Work.LayerCont.FarTail.FarIdentity` — `layerAt_eq_paperLayer_far` and `far_identity`: the
  far-side identity `windowChart = paperLayer + sinSqC r · resCorr r`.
* `Work.LayerCont.FarTail.Capstone` — `far_identity_data` (the chart with holomorphy, the
  `𝒟`-side agreement and the far-side identity on one ball) and
  `T2op_layerWindowContinuation`: the assembled **first recurrence**
  `T2op (windowChart · r) τ = -T2op (gaussTerm · r) τ`.
-/
import Submission.Work.LayerCont.FarTail.Defs
import Submission.Work.LayerCont.FarTail.Clean
import Submission.Work.LayerCont.FarTail.CuspFar
import Submission.Work.LayerCont.FarTail.CoincFar
import Submission.Work.LayerCont.FarTail.FarGeom
import Submission.Work.LayerCont.FarTail.FarIdentity
import Submission.Work.LayerCont.FarTail.Transfer
import Submission.Work.LayerCont.FarTail.Capstone
import Submission.Work.LayerCont.FarTail.CapstoneRev
