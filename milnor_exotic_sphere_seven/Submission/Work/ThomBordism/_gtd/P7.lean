import Submission.Work.ThomBordism._gtd.P6
import Submission.Work.ThomBordism.gaussClassifyingNDPad
import Submission.Work.ThomBordism.Grassmann.InclGauge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open scoped Topology

namespace Work.ThomBordism.Grassmann

open Work.PTGeometric

noncomputable section

/-- The stabilisation inclusion `ogInclCM k m` pulls the tautological bundle back to the
tautological bundle (the explicit form of `inclusionBundleIso`). -/
theorem inclusionBundleIso_ogInclCM (k m : ℕ) :
    Nonempty (Work.Thom.BundleIso
      (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m))
      (tautologicalBundle k m)) := by
  refine Work.Thom.nonempty_bundleIso_of_gauge
    (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) (ogInclCM k m))
    (tautologicalBundle k m) (inclPhi k m) (inclPhiInv k m) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i t
    exact continuousOn_inclPhi i t
  · intro i t
    exact continuousOn_inclPhiInv i t
  · intro i t t' b hb1 hb2 hb3
    exact inclPhi_htgt i t t' b hb1 hb2 hb3
  · intro i t i' b hb1 hb2 hb3
    exact inclPhi_hsrc i i' t b hb1 hb2 hb3
  · intro i t t' b hb1 hb2 hb3
    exact inclPhi_htgtinv i t t' b hb1 hb2 hb3
  · intro i t i' b hb1 hb2 hb3
    exact inclPhi_hsrcinv i i' t b hb1 hb2 hb3
  · intro i i' b x hb
    exact inclPhi_hleft i i' b hb x
  · intro i i' b x hb
    exact inclPhi_hright i i' b hb x

end

end Work.ThomBordism.Grassmann

namespace Work.ThomBordism

open Work.ThomBordism.Gauss Work.ThomBordism.PontryaginThom Work.ThomBordism.Grassmann
open Work.Tubular

noncomputable section

/-- **The classifying property of the *explicit* Gauss map** (the non-`Classical.choose` form of
`gaussClassifyingND`). -/
theorem gaussClassifyingNDExplicit {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) (hk : 1 ≤ k) (ND : NormalData V k E.e) :
    Nonempty (Work.Thom.BundleIso
      (Work.Thom.bundleComap (tautologicalBundle k 8) (Gauss.gauss E ND))
      (normalBundle E ND)) := by
  refine Work.Thom.nonempty_bundleIso_of_gauge
    (Z := Work.Thom.bundleComap (tautologicalBundle k 8) (Gauss.gauss E ND))
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

/-- **The padded Gauss map classifies the normal bundle.**  The explicit Gauss map of the padded
σ-corrected normal frame has the normal bundle as the pullback of the tautological bundle. -/
theorem padGaussClassifies {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) (hk : 1 ≤ k) (ND : NormalData V k E.e) :
    Nonempty (Work.Thom.BundleIso
      (Work.Thom.bundleComap (tautologicalBundle k 10)
        (⟨padGaussFun E ND, continuous_padGaussFun E ND⟩ : C(V.pt, OG k 10)))
      (normalBundle E ND)) := by
  classical
  set ψ₂ : C(OG k 8, OG k 10) := (ogInclCM k 9).comp (ogInclCM k 8) with hψ₂
  obtain ⟨e₉⟩ := inclusionBundleIso_ogInclCM k 9
  obtain ⟨e₈⟩ := inclusionBundleIso_ogInclCM k 8
  obtain ⟨e₂⟩ := Work.Thom.BundleIso_comap_exists
    (Work.Thom.bundleComap (tautologicalBundle k 10) (ogInclCM k 9))
    (tautologicalBundle k 9) e₉ (ogInclCM k 8)
  have hcomp := Work.Thom.bundleComap_comp (tautologicalBundle k 10)
    (ogInclCM k 9) (ogInclCM k 8)
  have eψ : Work.Thom.BundleIso
      (Work.Thom.bundleComap (tautologicalBundle k 10) ψ₂) (tautologicalBundle k 8) :=
    (Work.Thom.BundleIso.ofEq hcomp.symm).trans (e₂.trans e₈)
  obtain ⟨e₂'⟩ := Work.Thom.BundleIso_comap_exists
    (Work.Thom.bundleComap (tautologicalBundle k 10) ψ₂) (tautologicalBundle k 8) eψ
    (Gauss.gauss E ND)
  have e₈b := Classical.choice (gaussClassifyingNDExplicit E hk ND)
  have hfun : (⟨padGaussFun E ND, continuous_padGaussFun E ND⟩ : C(V.pt, OG k 10))
      = ψ₂.comp (Gauss.gauss E ND) := by
    apply ContinuousMap.ext
    intro x
    exact congrFun (padGaussFun_eq_ogIncl E ND) x
  have hbridge : Work.Thom.bundleComap (tautologicalBundle k 10)
        (⟨padGaussFun E ND, continuous_padGaussFun E ND⟩ : C(V.pt, OG k 10))
      = Work.Thom.bundleComap (Work.Thom.bundleComap (tautologicalBundle k 10) ψ₂)
          (Gauss.gauss E ND) := by
    rw [hfun, hψ₂]
    exact (Work.Thom.bundleComap_comp (tautologicalBundle k 10)
      ((ogInclCM k 9).comp (ogInclCM k 8)) (Gauss.gauss E ND)).symm
  exact ⟨(Work.Thom.BundleIso.ofEq hbridge).trans (e₂'.trans e₈b)⟩

end

end Work.ThomBordism
