import Mathlib
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.ThomBordism.Grassmann.Grassmannian
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.orthFrameOrientation
import Submission.Work.ThomBordism.gaussClassifying

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# The Gauss/classifying map of an embedded `8`-manifold into the oriented Grassmannian

The geometric datum that the Pontryagin–Thom construction of this project never names is the Gauss
map of the *normal* bundle of an embedding `V ⊂ ℝ^{8+k}` into the oriented Grassmannian
`G̃r_k(ℝ^{k+8})`.  `NormalGaussData` (`PontryaginThom/Geometry.lean`) keeps it as *free data* (`G`
and `γ` abstract, `classifies` a field), and `NormalExists.lean` instantiates them with `G = V`,
`γ = ν` (the identity classification), which is enough for the *splitting* half of the normal-bundle
input but not for anything that must be computed against the *universal* Thom space `Th(γ)`.

That is the gap this file addresses: the Gauss map into the *actual* `G̃r_k(ℝ^{k+8})`, with the
classifying isomorphism.  Its content, split into the pieces that have to be built:

* (`G1`, done in the tree) the **frames**: `Work.Tubular.exists_euclidean_normalBundle` produces the
  Euclidean bundle `normalBundle E ND` of the embedding and, per chart `i` of the cover
  `CoverIdx V k`, the orthonormal frame `orthFrame E ND i x` of the normal plane `normalSpace E x`,
  with `orthFrame_orthonormal`, `span_orthFrame`, `orthFrame_mem`, `continuousOn_orthFrame`;
* (`G2`) the **pointwise Gauss map** `x ↦ ogMk k 8 (orthFrame E ND i x)` — needs the reindexing
  `Amb (k+8) ↔ Euc (8+k)` (`Stiefel k m = {f : Fin k → Amb (k+m) // Orthonormal ℝ f}`,
  `Grassmann/Frame.lean`) and the orientation bookkeeping for the ambient reindexing;
* (`G3`) the **`SO(k)`-compatibility on overlaps** (the reviewer's caveat).  The raw statement "the
  two Gram–Schmidt frames differ by an element of `SO(k)`" is **FALSE for even `k`**: multiplying a
  frame by a scalar `ε = ±1` changes the change-of-basis determinant by `(ε i · ε j)^k`, which is
  `1` for even `k`, so no sign correction can repair a pair of oppositely oriented frames — and the
  canonical frames of `exists_euclidean_normalBundle` do occur in oppositely oriented pairs (a
  reviewer's explicit `k = 2` counterexample: `ν = span(e₁+e₃, e₂+e₃)`, complement-pairs `{1,3}` and
  `{2,3}`, change of basis of determinant `−1`).  For **odd** `k` the sign correction *is* available
  and the statement is true (the determinant cocycle of the frames is a coboundary because `ν` is
  orientable, `Man8.c_fund` orienting `V` and the ambient space orienting `ν`; the parity of `k` then
  converts `(ε i x · ε j x)^k · det M = 1`).  Delegated this session as
  `Work.ThomBordism.orthFrameOrientation` (file `Submission/Work/ThomBordism/orthFrameOrientation.lean`):

  ```lean
  theorem orthFrameOrientation {V : Man8} {k : ℕ} (E : EmbeddingData V (8 + k))
      (ND : NormalData V k E.e) (hk : Odd k) :
      ∃ ε : (i : CoverIdx V k) → V.pt → ℝ,
        (∀ i x, ε i x = 1 ∨ ε i x = -1) ∧
        (∀ i, ContinuousOn (ε i) (ND.D.baseSet i)) ∧
        ∀ i j x (hx : x ∈ ND.D.baseSet i ∩ ND.D.baseSet j),
          ∃ A : SOk k, ∀ a, ε i x • orthFrame E ND i x a
            = ∑ b, A.1 b a • (ε j x • orthFrame E ND j x b)
  ```

  (For the *application* `k = 11` this is enough.  For general `k` — in particular even `k` — the
  correct statement is not a sign correction but a *gauge*: an orientation-consistent family of
  orthonormal frames, i.e. an oriented trivialisation of `ν` over the cover.);
  **`Work.ThomBordism.orthFrameOrientation` is PROVED** (file
  `Submission/Work/ThomBordism/orthFrameOrientation.lean`, with the supporting development in
  `Submission/Work/ThomBordism/OrthFrame/`, including `tangentFrameSigns` — the chart-atlas sign
  cocycle of `V` derived from `V.c_fund`).  What remains of `G3` for the gluing is only the
  bookkeeping that the corrected frames give the *same* point of `OG` (which needs `G2`: the ambient
  reindexing `Fin (8+k) ≃ Fin (k+8)`).
* (`G4`) the **gluing**: the chartwise maps patch to a global `C(V.pt, OG k 8)` (the `baseSet i`
  cover `V.pt`, `ND.D.mem_baseSet_at`; continuity is `continuousOn_orthFrame` + `ogMk`);
* (`G5`) the **classifying isomorphism** `bundleComap (tautologicalBundle k 8) gauss ≅ normalBundle E ND`
  (fibrewise the identity in the frame `orthFrame`, so it reduces to the compatibility of the two
  gluing data's `coordChange`s).

The main statement of the file, with the two halves separated so that `G5` (the "classifying" half)
can be built and delegated on its own, is `gaussMapGrassmann`; the reduction
`gaussMapGrassmann_of_classifying` shows that the Euclidean/normative half of the statement is
already in the tree and that exactly the pair (`G4`, `G5`) remains.

## The next delegation target (ingredient 2 of `ThomBordism/paddedTubeData.lean`)

The *other* unowned piece is the **explicit, natural comparison**
`Ψ : H^{k+8}(Th γ) ≅ H^{k+8}(Dγ,Sγ)`: `Grassmann/Torsion/ThomSpaceCohomologyCompare.lean` produces it
only as a `Nonempty` (a `Classical.choice` composite of `relCoh_equiv_cohomology_of_subsingleton`,
`relCohomology_iso_of_open_cover`, `bijective_relCohMap_of_homeomorphA`, `discPairIso`,
`puncturedDiscPairIso`), so its action on a class cannot be computed; what the assembly of the
padded tube data needs is *naturality of the Thom class under the Gauss bundle map*, i.e. (M2) of
`Tubular/PairingNotes.md` §4: from a bundle isomorphism `e : bundleComap Z f ≅ Z'` and a Thom class
`T` of `Z`, produce a Thom class `T'` of `Z'` with

  `T'.τ = (relCohMap e.toHomeomorph (zeroComplementCore _) (zeroComplementCore _) _ ℤ n).hom T.τ`.

**Trap (from `Tubular/PairingNotes.md` §6, do not rediscover):** naming the membership argument
`fun y hy => e.hom_ne_zero hy` inside `relCohMap` together with
`Work.Thom.cupMap_transfer_fwdA` blows up the elaborator (`deterministic timeout at whnf/isDefEq`,
at `maxHeartbeats = 16000000`); each ingredient alone elaborates.  The fix suggested there is to
state the transport with `Set.EqOn`/`MapsTo` hypotheses (or via a `Homeomorph` of pairs) so that the
caller never writes the membership term.
-/

open scoped Manifold ContDiff Topology

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The reduction: only the Gauss map and its classifying isomorphism remain.**

The Euclidean bundle of the embedding, its norm-preserving homeomorphism and the two "normative"
conjuncts are `Work.Tubular.exists_euclidean_normalBundle` (`normalBundle`, `eucNormalHomeomorph`,
`fibreNorm_eq_normalNorm`).  So `gaussMapGrassmann` is *equivalent* to (and here reduced to) the
statement that, for a suitable `NormalData` `ND` of the embedding, the tautological bundle over
`G̃r_k(ℝ^{k+8})` pulled back along some `gauss : V → G̃r_k(ℝ^{k+8})` is isomorphic to
`normalBundle E ND`.  The proof of that is `G4` (gluing the chartwise `ogMk` of `orthFrame`) plus
`G5` (the fibrewise-identity bundle isomorphism). -/
theorem gaussMapGrassmann_of_classifying (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (hk : 1 ≤ k)
    (h : ∃ (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
           (gauss : C(V.pt, Work.ThomBordism.Grassmann.OG k 8)),
           Nonempty (Work.Thom.BundleIso
             (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k 8) gauss)
             (Work.Tubular.normalBundle E ND))) :
    ∃ (ι : Type) (ν : Work.TangentClasses.RealBundle V.pt (EuclideanSpace ℝ (Fin k)) ι)
      (φ : ν.TotalSpace ≃ₜ Work.Tubular.NormalTotal E)
      (gauss : C(V.pt, Work.ThomBordism.Grassmann.OG k 8)),
      Work.Thom.IsEuclidean ν ∧
      (∀ p, Work.Thom.fibreNorm ν p = Work.Tubular.normalNorm E (φ p)) ∧
      Nonempty (Work.Thom.BundleIso
        (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k 8) gauss) ν) := by
  obtain ⟨ND, gauss, hc⟩ := h
  exact ⟨Work.ThomBordism.PontryaginThom.CoverIdx V k, Work.Tubular.normalBundle E ND,
    Work.Tubular.eucNormalHomeomorph E ND, gauss,
    Work.Tubular.isEuclidean_normalBundle E ND,
    fun p => Work.Tubular.fibreNorm_eq_normalNorm E ND p, hc⟩

/-- **The Gauss/classifying data of an embedding into the oriented Grassmannian.**

For a closed oriented smooth `8`-manifold `V` smoothly embedded in `ℝ^{8+k}` with injective
derivative, the normal bundle `ν` (as the Euclidean gluing datum of
`Work.Tubular.exists_euclidean_normalBundle`), together with its norm-preserving homeomorphism onto
the concrete normal total space, and a **Gauss map** `gauss : V → G̃r_k(ℝ^{k+8})` classifying it:
`ν ≅ gauss^*(γ)` for the tautological oriented `k`-plane bundle `γ` of the Grassmannian.

(Reviewed and approved by two reviewers; the statement is the honest existence of the Gauss map, and
it is *not* the free-data field of `NormalGaussData`.) -/
theorem gaussMapGrassmann (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (hk : 1 ≤ k) :
    ∃ (ι : Type) (ν : Work.TangentClasses.RealBundle V.pt (EuclideanSpace ℝ (Fin k)) ι)
      (φ : ν.TotalSpace ≃ₜ Work.Tubular.NormalTotal E)
      (gauss : C(V.pt, Work.ThomBordism.Grassmann.OG k 8)),
      Work.Thom.IsEuclidean ν ∧
      (∀ p, Work.Thom.fibreNorm ν p = Work.Tubular.normalNorm E (φ p)) ∧
      Nonempty (Work.Thom.BundleIso
        (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k 8) gauss) ν) :=
  gaussMapGrassmann_of_classifying E hk (gaussClassifying E hk)
end

end Work.ThomBordism
