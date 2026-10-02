import Submission.Work.Tubular.LocalDegree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The local degree at the collapse class: the connectedness hypotheses

`Work.Tubular.exists_localDegree_at_collapseRelK8` (`Submission/Work/Tubular/LocalDegree.lean`)
carries two connectivity hypotheses: `[PathConnectedSpace V.pt]` and `[ConnectedSpace V.pt]`.
Only the *second* is a genuine hypothesis about the manifold: a `Man8` is a charted space over the
locally path connected model space `EuclideanSpace ℝ (Fin 8)`, so a connected `Man8` is
automatically path connected (Mathlib: `ChartedSpace.locallyPathConnectedSpace` +
`PathConnectedSpace.of_locallyPathConnectedSpace`).

This file records that, and states the local degree with `[ConnectedSpace V.pt]` as the only
connectivity hypothesis (`Work.Tubular.exists_localDegree_at_collapseRelK8_of_connected`).

## The disconnected case

A general `Man8` need *not* be connected (`Work.ThomBordism.Man8`, `Submission/Work/ThomBordism/
Interface.lean`, has no connectivity field), and every consumer that quantifies over all `Man8`
(`Work.ThomBordism.tubeDataPerFamily`, `...FamilyTubeData`, `...ptAdditivity`) must then either
carry a connectivity hypothesis or split the manifold into its components.  The component-wise
form of the local degree,

  `exists_localDegree_at_collapseRelK8_all`,

is *not* proved here: it needs the additivity of the relative cohomology of the pair `(E, E∖0)`,
of the relative Kronecker pairing, of the mixed cup product and of the collapse class over the
finitely many clopen components of `V`, together with `V.c = ∑ᵢ εᵢ cᵢ` (which is what `Man8.c_fund`
forces at each component).  See §38 of `README.md` for the exact list.
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Limits
open scoped Topology

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

open Work.Cohomology

/-- A `Man8` is a charted space over the locally path connected model space
`EuclideanSpace ℝ (Fin 8)`, hence locally path connected. -/
lemma locallyPathConnectedSpace_of_man8 (V : Work.ThomBordism.Man8) :
    LocallyPathConnectedSpace V.pt :=
  ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 8)) V.pt

/-- **A connected `Man8` is path connected.** -/
theorem pathConnectedSpace_of_man8 (V : Work.ThomBordism.Man8) [ConnectedSpace V.pt] :
    PathConnectedSpace V.pt := by
  haveI : LocallyPathConnectedSpace V.pt := locallyPathConnectedSpace_of_man8 V
  exact PathConnectedSpace.of_locallyPathConnectedSpace

/-- **The local degree of the collapse class, in the world `(ν, ν∖0)`** — the statement of
`Work.Tubular.exists_localDegree_at_collapseRelK8` with `[ConnectedSpace V.pt]` as the *only*
connectivity hypothesis (`[PathConnectedSpace V.pt]` is derived from it, since a `Man8` is locally
path connected). -/
theorem exists_localDegree_at_collapseRelK8_of_connected {V : Work.ThomBordism.Man8}
    [ConnectedSpace V.pt] {k : ℕ} {E : EmbeddingData V (8 + k)} (hk : 1 ≤ k)
    {ι : Type} (Z : Work.TangentClasses.RealBundle V.pt (Fin k → ℝ) ι)
    (ψ : Z.TotalSpace ≃ₜ NormalTotal E)
    (hproj : ∀ p : Z.TotalSpace, NormalTotal.proj (ψ p) = p.1)
    (hlen : ∀ p : Z.TotalSpace, Work.Thom.fibreNorm Z p ≠ 0 ↔ normalNorm E (ψ p) ≠ 0)
    (hvec : ∀ x : V.pt, NormalTotal.vec (ψ (Work.Thom.zeroSection Z x)) = 0)
    (hZ : Nonempty (Work.Thom.ThomClass Z k))
    {ε : ℝ} {C : TubeChart E ε} (q : NormalSphSub E ε) (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube → g (OnePoint.some y) = OnePoint.some (normalBlowUp E ε (C.inv y))) :
    ∃ U : Work.Thom.RelCoh ℤ k (TopCat.of (NormalTotal E)) (normalNonzero E),
      ∀ x : Work.Thom.Coh ℤ 8 (TopCat.of (NormalTotal E)),
        relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
          ((Nat.add_comm 8 k) ▸ (mixedCup (TopCat.of (NormalTotal E)) (normalNonzero E) 8 k x U))
          (collapseRelK8 C g hg hR hbox)
        = kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
            ((Work.Thom.CohMap (zeroSectionNormal E) ℤ 8).hom x) V.c := by
  haveI : PathConnectedSpace V.pt := pathConnectedSpace_of_man8 V
  exact exists_localDegree_at_collapseRelK8 (V := V) (k := k) (E := E) hk Z ψ hproj hlen hvec hZ
    q hU hR hbox g hg hg2

end

end Work.Tubular
