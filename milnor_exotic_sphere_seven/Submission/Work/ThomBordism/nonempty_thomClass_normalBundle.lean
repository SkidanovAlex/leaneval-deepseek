import Mathlib
import Submission.Work.Tubular.NormalThom
import Submission.Work.ThomBordism.gaussClassifyingNDPad

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The normal bundle of an embedded oriented `8`-manifold has an integral Thom class

For a closed oriented smooth `8`-manifold `V ⊆ ℝ^{8+k}` (`E : EmbeddingData V (8+k)`) together
with normal data `ND : NormalData V k E.e`, the concrete Euclidean normal bundle
`Work.Tubular.normalBundle E ND` of rank `k ≥ 1` carries an integral Thom class
`U ∈ H^k(ν, ν∖0; ℤ)`.

The mathematical content is the orientability of the normal bundle, which enters through the
*Gauss map*: `V` and `ℝ^{8+k}` are oriented, so the complement of the tangent orientation orients
`ν`, and this is exactly what a map `V → G̃r_k(ℝ^{k+10})` into the **oriented** Grassmannian
records.  The two ingredients are the Pontryagin–Thom chapter's classifying data and the Thom
isomorphism theorem for bundles with positive-determinant transitions:

* `Work.ThomBordism.gaussClassifyingNDPad` — the Gauss classifying map `gauss : V.pt → OG k 10`
  of the *given* normal data, together with a bundle isomorphism
  `gauss^*(tautologicalBundle k 10) ≅ normalBundle E ND`;
* `Work.ThomBordism.Grassmann.det_coordChangeO_pos` — the tautological oriented bundle over the
  oriented Grassmannian has positive-determinant transitions;
* `Work.Tubular.exists_normalThomClass` — bundles with positive-determinant transitions (over a
  finite cover) have a Thom class, and the Thom class transports along bundle isomorphisms.

No orientability hypothesis on `ν` is needed as input: the orientation is produced by the Gauss
map, i.e. by the given embedding of an oriented manifold into oriented Euclidean space.
-/

namespace Work.ThomBordism

theorem nonempty_thomClass_normalBundle {V : Work.ThomBordism.Man8} {k : ℕ} (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) :
    Nonempty (Work.Thom.ThomClass (Work.Tubular.normalBundle E ND) k) := by
  obtain ⟨gauss, ⟨e⟩⟩ := gaussClassifyingNDPad E hk ND
  exact Work.Tubular.exists_normalThomClass (k := k) hk
    (γ := Work.ThomBordism.Grassmann.tautologicalBundle k 10)
    (fun i j x => Work.ThomBordism.Grassmann.det_coordChangeO_pos i j (x : _) x.2)
    gauss e

end Work.ThomBordism
