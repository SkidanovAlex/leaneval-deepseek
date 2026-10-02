import Mathlib
import Submission.Work.ThomBordism.gaussClassifying
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.ThomBordism.gaussMapGrassmannPad

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Gauss classifying map of an embedded `8`-manifold, for *prescribed* normal data, padded

`Work.ThomBordism.gaussClassifying` produces a normal data `ND` of the embedding and, for *that*
`ND`, a Gauss map `gauss : V → G̃r_k(ℝ^{k+8})` classifying the normal bundle.  The Pontryagin–Thom
assembly of this project, however, is handed its normal data by the tubular-neighbourhood input, so
what it needs is the classifying map for the *given* `ND` — and, because the construction of the
Thom class takes place in a Grassmannian with at least two dimensions of slack, at the padded
dimension `OG k 10` (obtained from `OG k 8` by the iterated ambient inclusion
`Work.ThomBordism.inclusionBundleIso_iter`, whose pullback of the tautological bundle is the
tautological bundle of the smaller Grassmannian).

Nothing geometric is new here: the proof of `Work.ThomBordism.gaussClassifying` never uses any
property of the chosen normal data beyond `NormalData V k E.e` itself — the Gauss map
`Gauss.gauss E ND`, the charts `Gauss.gauss_eq_ogMk`, the gauge `Gauss.phiCLM` and the eight
compatibilities required by `Work.Thom.nonempty_bundleIso_of_gauge` are all stated for an
arbitrary `ND`.  So the same argument, with `gaussND E` replaced by the given `ND`, gives the
unpadded statement `gaussClassifyingND`, and the target follows by the ambient inclusion.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped Manifold ContDiff Topology

namespace Work.ThomBordism

open Work.ThomBordism.Gauss Work.ThomBordism.PontryaginThom Work.ThomBordism.Grassmann
open Work.Tubular

noncomputable section

/-- **The Gauss classifying map of a prescribed normal data** (dimension `8`): the argument of
`gaussClassifying` with the normal data fixed in advance. -/
theorem gaussClassifyingND {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) (hk : 1 ≤ k) (ND : NormalData V k E.e) :
    ∃ gauss : C(V.pt, OG k 8),
      Nonempty (Work.Thom.BundleIso
        (Work.Thom.bundleComap (tautologicalBundle k 8) gauss)
        (normalBundle E ND)) := by
  refine ⟨gauss E ND, ?_⟩
  refine Work.Thom.nonempty_bundleIso_of_gauge
    (Z := Work.Thom.bundleComap (tautologicalBundle k 8) (gauss E ND))
    (Z' := normalBundle E ND)
    (fun S t x => phiCLM E ND S t x)
    (fun S t x => phiInvCLM E ND S t x) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i i'
    exact continuousOn_phiCLM E ND i i'
  · intro i i'
    exact continuousOn_phiInvCLM E ND i i'
  · intro i t t' x hi ht ht'
    exact normalBundle_coordChange_comp_phiCLM E ND i t t' hi ht ht'
  · intro i t i' x hi hi' ht
    rw [Work.Thom.bundleComap_coordChange]
    exact phiCLM_comp_coordChangeO E ND i i' t hi hi' ht
  · intro i t t' x hi ht ht'
    exact phiInvCLM_comp_transFun E ND i t t' hi ht ht'
  · intro i t i' x hi hi' ht
    rw [Work.Thom.bundleComap_coordChange]
    exact coordChangeO_comp_phiInvCLM E ND i i' t hi hi' ht
  · intro i i' b v hx
    rw [← ContinuousLinearMap.comp_apply,
      phiInvCLM_comp_phiCLM E ND i i' hx.1
        (det_frameMatrix_orthFrame_ne_zero E ND i i' hx.2 hx.1),
      ContinuousLinearMap.one_apply]
  · intro i i' b v hx
    rw [← ContinuousLinearMap.comp_apply,
      phiCLM_comp_phiInvCLM E ND i i' hx.1
        (det_frameMatrix_orthFrame_ne_zero E ND i i' hx.2 hx.1),
      ContinuousLinearMap.one_apply]

/-- **The Gauss classifying map of a prescribed normal data, at the padded dimension `10`.**  The
unpadded map composed with the iterated ambient inclusion `G̃r_k(ℝ^{k+8}) → G̃r_k(ℝ^{k+10})`, whose
pullback of the tautological bundle is the tautological bundle of `G̃r_k(ℝ^{k+8})`. -/
theorem gaussClassifyingNDPad {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (hk : 1 ≤ k)
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) :
    ∃ gauss : C(V.pt, Work.ThomBordism.Grassmann.OG k 10),
      Nonempty (Work.Thom.BundleIso
        (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k 10) gauss)
        (Work.Tubular.normalBundle E ND)) := by
  obtain ⟨gauss₈, ⟨e₈⟩⟩ := gaussClassifyingND E hk ND
  obtain ⟨ψ, ⟨eψ⟩⟩ := inclusionBundleIso_iter k (a := 8) (b := 10) (by norm_num)
  refine ⟨ψ.comp gauss₈, ?_⟩
  obtain ⟨e₂⟩ := Work.Thom.BundleIso_comap_exists
    (Work.Thom.bundleComap (tautologicalBundle k 10) ψ) (tautologicalBundle k 8) eψ gauss₈
  have hcomp : Work.Thom.bundleComap
        (Work.Thom.bundleComap (tautologicalBundle k 10) ψ) gauss₈
      = Work.Thom.bundleComap (tautologicalBundle k 10) (ψ.comp gauss₈) :=
    Work.Thom.bundleComap_comp (tautologicalBundle k 10) ψ gauss₈
  exact ⟨(Work.Thom.BundleIso.ofEq hcomp.symm).trans (e₂.trans e₈)⟩

end

end Work.ThomBordism
