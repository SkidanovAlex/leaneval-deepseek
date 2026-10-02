import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.ThomBordism.TubeLocalDegree
import Submission.Work.ThomBordism.nfGenBasic
import Submission.Work.ThomBordism.nfRead_ne_zero
import Submission.Work.ThomBordism.frameClassDefs
import Submission.Work.ThomBordism.frameClass_eq
import Submission.Work.ThomBordism.span_frameClass
import Submission.Work.ThomBordism.stdThomGen_span
import Submission.Work.ThomBordism.tubeLocalDegreeGlobalSign
import Submission.Work.ThomBordism.fibreRes_gtdU_geom
import Submission.Work.Thom.relCohomology_euclidean_punctured

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fibre restriction of the canonical Thom class of the normal bundle

The datum of the last mile of `Work.ThomBordism.thomRational` is a Gauss/classifying map `G` of the
normal bundle of an embedding `E : V ↪ ℝ^{8+k}`, pinned by two clauses (`hbp`, `hvec`), together
with the canonical class

  `gtdU E ND G hgm = G^*(τ)`  (`τ` the tautological Thom class of `γ_{k,10}`),

and the oriented fibre generator

  `nfGen hk E ND x = (nfRead E ND x)^*(stdThomGen k)`.

**The fibre restriction of `gtdU` is `± nfGen`, with a *single* sign `s = ±1` for all data.**
The argument separates the geometry from the universal computation:

* `Work.ThomBordism.nfRes_gtdU_eq_frameClass` (geometry): on each fibre, `gtdU` restricts to the
  *frame reading* of the tautological Thom class,
  `nfRes E x k (gtdU …) = (nfRead E ND x)^*(frameClass k σ_x)`, where `σ_x` is the σ-corrected
  normal frame at `x`;
* `Work.ThomBordism.frameClass_eq` (universal, and the crux): `frameClass k σ` does not depend on
  the frame `σ` (homotopy invariance over the connected Stiefel manifold);
* `Work.ThomBordism.span_frameClass` and `Work.ThomBordism.stdThomGen_span`: both classes generate
  the standard pair `H^k(ℝ^k, ℝ^k∖0;ℤ) ≅ ℤ`, so they are `±` each other
  (`Work.ThomBordism.eq_pm_of_span_eq_top_of_iso`).

Since the same `frameClass k σ` is used for every datum, the sign is uniform, and the result is
`nfRes E x k (gtdU …) = s • nfGen hk E ND x` with `s = ±1` independent of the datum.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

open Work.ThomBordism.Grassmann

noncomputable section

/-- **The frame reading of the tautological Thom class is `±` the standard generator**, with a
single sign for all frames.  This is the universal comparison of the last mile. -/
theorem frameClass_eq_pm_stdThomGen (k : ℕ) (hk : 1 ≤ k) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ σ : Stiefel k 10,
      frameClass k σ = ε • stdThomGen k hk := by
  classical
  -- the standard pair is `ℤ` in degree `k`
  obtain ⟨e⟩ := Work.Thom.relCohomology_euclidean_punctured k hk k
  rw [if_pos rfl] at e
  let E : Work.Thom.RelCoh ℤ k (Amb k) (framePunct k) ≃ₗ[ℤ] ℤ :=
    e.toLinearEquiv.trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ)
  obtain ⟨σ₀⟩ := nonempty_stiefel k 10
  have h1 := span_frameClass k hk σ₀
  have h2 := stdThomGen_span k hk
  rcases eq_pm_of_span_eq_top_of_iso E h1 h2 with h | h
  · refine ⟨1, Or.inl rfl, fun σ => ?_⟩
    rw [frameClass_eq k hk σ σ₀, h, one_smul]
  · refine ⟨-1, Or.inr rfl, fun σ => ?_⟩
    rw [frameClass_eq k hk σ σ₀, h]
    simp

theorem fibreRes_gtdU_canonical (k : ℕ) (hk : 1 ≤ k) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
        (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
        (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
          (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
        (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
          G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
        (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
          = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
        (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
          = Work.PTGeometric.padEuc k 10 (by norm_num)
              (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
        (x : V.pt),
        nfRes E x k (Work.ThomBordism.gtdU E ND G hgm) = s • nfGen hk E ND x := by
  obtain ⟨ε, hε, hεeq⟩ := frameClass_eq_pm_stdThomGen k hk
  refine ⟨ε, hε, ?_⟩
  intro V _ E ND G hgm hbp hvec x
  let L : Work.Thom.RelCoh ℤ k (Amb k) (framePunct k) →ₗ[ℤ]
      Work.Thom.RelCoh ℤ k ↥(nfSet E x) (nfPunct E x) :=
    (Work.Thom.relCohMap (nfRead E ND x) (nfPunct E x) (framePunct k)
      (fun p hp => (mem_framePunct k _).mpr (nfRead_ne_zero hk E ND x p hp)) ℤ k).hom
  have hL : L (frameClass k (datumFrame E ND x)) = ε • nfGen hk E ND x := by
    have h1 : L (frameClass k (datumFrame E ND x)) = L (ε • stdThomGen k hk) := by
      rw [hεeq (datumFrame E ND x)]
    rw [h1, map_zsmul, nfGen_eq hk E ND x]
  rw [nfRes_gtdU_eq_frameClass hk E ND G hgm hbp hvec x]
  exact hL

end

end Work.ThomBordism
