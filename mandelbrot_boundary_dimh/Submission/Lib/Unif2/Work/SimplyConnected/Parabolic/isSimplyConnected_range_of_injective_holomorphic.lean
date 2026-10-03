import Mathlib
import Submission.Lib.Unif2.Work.Parabolic.Basic
import Submission.Lib.Unif2.Work.Parabolic.isOpenMap_of_injective_holomorphic

/-!
# The image of an injective holomorphic map from a simply connected Riemann surface

Let `X` be a Riemann surface (a complex one-manifold) which is Hausdorff and simply connected,
and let `g : X → ℂ` be holomorphic on all of `X` and injective.  Then the image `Set.range g`,
with the subspace topology inherited from `ℂ`, is simply connected.

The mathematics is:

* an injective holomorphic map on a Riemann surface is an **open map** — this is the open mapping
  theorem in the form `Work.Parabolic.isOpenMap_of_injective_holomorphic` (local constancy of `g`
  is excluded by injectivity, since a chart at any point of a complex one-manifold has a source
  containing more than one point, and the local open mapping theorem gives
  `𝓝 (g x) ≤ map g (𝓝 x)`);

* an injective, continuous and open map is an **open embedding**, hence in particular an
  **embedding** (`Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap`);

* simple connectivity is a homeomorphism invariant: for an embedding `g`, the image `g '' s` of a
  set `s` is simply connected iff `s` is (`Topology.IsEmbedding.isSimplyConnected_image`), and
  `Set.range g = g '' univ` while `Set.univ` is simply connected because `X` is.
-/

namespace Work.SimplyConnected.Parabolic

open Topology

theorem isSimplyConnected_range_of_injective_holomorphic {X : Type*} [TopologicalSpace X]
    [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    [SimplyConnectedSpace X] {g : X → ℂ} (hg : Submission.HolomorphicOnX g Set.univ)
    (hginj : Function.Injective g) : IsSimplyConnected (Set.range g) := by
  -- `g` is an open map (open mapping theorem for an injective holomorphic function)
  have hopen : IsOpenMap g := Work.Parabolic.isOpenMap_of_injective_holomorphic hg hginj
  -- hence, being continuous and injective, it is an embedding
  have hemb : Topology.IsEmbedding g :=
    (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hg.continuous hginj hopen).toIsEmbedding
  -- `Set.range g = g '' univ`, and simple connectivity is a homeomorphism invariant
  rw [← Set.image_univ, hemb.isSimplyConnected_image]
  -- `univ ⊆ X` is simply connected because `X` is
  exact (Homeomorph.Set.univ X).toHomotopyEquiv.simplyConnectedSpace

end Work.SimplyConnected.Parabolic
