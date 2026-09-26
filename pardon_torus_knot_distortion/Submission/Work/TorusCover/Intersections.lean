import Submission.Work.TorusCover.ncard_standardTorusCurve_meridian
import Submission.Work.TorusCover.ncard_standardTorusCurve_longitude

/-!
# Intersection numbers of the standard `(p,q)` curve with meridians and longitudes

The standard `(p,q)` curve `t ↦ torusMap (p t) (q t)` winds `p` times around the longitude
direction and `q` times around the meridian direction of the torus of revolution.  Hence, over
one fundamental period `[0, 2π)`,

* it meets the meridian circle `{θ = const}` in exactly `p` points (the parameter `θ(t) = p t`
  takes each value modulo `2π` exactly `p` times), and
* it meets the longitude circle `{φ = const}` in exactly `q` points.

Since the curve meets both families of circles transversally, these geometric counts are also
the *algebraic* intersection numbers of the standard `(p,q)` curve with a meridian and with a
longitude respectively.

Main results (proved in the imported modules):

* `Work.TorusCover.ncard_standardTorusCurve_meridian`:
  `{t ∈ [0,2π) | standardTorusCurve p q t ∈ range (meridianCircle θ)}.ncard = p`;
* `Work.TorusCover.ncard_standardTorusCurve_longitude`:
  `{t ∈ [0,2π) | standardTorusCurve p q t ∈ range (longitudeCircle φ)}.ncard = q`.
-/
