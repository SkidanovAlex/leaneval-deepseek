import Mathlib
import Submission.Work.ThomBordism.frameClassDefs
import Submission.Work.ThomBordism.Grassmann.deg8PathConnectedOG

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Independence of the frame reading of the tautological Thom class

`Work.ThomBordism.frameClass k σ` is the pullback of the tautological Thom class `τ` of
`γ = tautologicalBundle k 10` along the frame evaluation `frameEval σ` (a homeomorphism of pairs
`(ℝ^k, ℝ^k∖0) ≅ (γ_{ogMk σ}, γ_{ogMk σ}∖0)`).

**The class does not depend on the frame.**  The proof is homotopy invariance, with *no* orientation
bookkeeping:

* `V_k(ℝ^{k+10})` is path connected (`Work.ThomBordism.Grassmann.joined_frames`), so choose a path
  `γ` from `σ` to `σ'`;
* the two frame evaluations `frameEval σ = frameEval (γ 0)` and `frameEval σ' = frameEval (γ 1)`
  are homotopic *as maps of pairs* `(ℝ^k, ℝ^k∖0) → (γ, γ∖0)`, through
  `(t, v) ↦ frameEval (γ t) v`;
* hence `relCohMap (frameEvalMap k σ) = relCohMap (frameEvalMap k σ')`
  (`Work.Thom.relCohMap_homotopic`), and the two pullbacks of `τ` agree.

No orientation computation enters: the frame reading simultaneously trivialises the tautological
bundle *and* its orientation over the connected Stiefel manifold.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open CategoryTheory
open scoped Topology

namespace Work.ThomBordism

open Work.ThomBordism.Grassmann

noncomputable section

theorem frameClass_eq (k : ℕ) (hk : 1 ≤ k) (σ σ' : Stiefel k 10) :
    frameClass k σ = frameClass k σ' := by
  classical
  have hjoin : Joined σ σ' :=
    joined_frames k (Amb (k + 10)) (by simp [Amb]) σ σ'
  let γ : Path σ σ' := hjoin.somePath
  let Hfun : C(↥unitInterval × Amb k, (tautologicalBundle k 10).TotalSpace) :=
    ⟨fun p => frameEval k (γ p.1) p.2,
      (continuous_frameEval k).comp ((γ.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  let hhom : (frameEvalMap k (γ 0)).Homotopy (frameEvalMap k (γ 1)) :=
    ContinuousMap.Homotopy.mk Hfun (fun v => rfl) (fun v => rfl)
  have h_eq : hhom.toContinuousMap = Hfun := rfl
  have hHfun : ∀ (t : ↥unitInterval) (x : Amb k), Hfun (t, x) = frameEval k (γ t) x :=
    fun t x => rfl
  have hhom_mem : ∀ (t : ↥unitInterval) (x : Amb k), x ∈ framePunct k → hhom (t, x) ∈
      Work.Thom.zeroComplement (tautologicalBundle k 10) := by
    intro t x hx
    rw [← ContinuousMap.Homotopy.coe_toContinuousMap hhom]
    rw [show hhom.toContinuousMap (t, x) = Hfun (t, x) from
      congrArg (fun (g : C(↥unitInterval × Amb k,
        (tautologicalBundle k 10).TotalSpace)) => g (t, x)) h_eq]
    rw [hHfun t x]
    exact frameEvalMap_mem k (γ t) x hx
  have hrel := Work.Thom.relCohMap_homotopic (framePunct k)
    (Work.Thom.zeroComplement (tautologicalBundle k 10))
    (frameEvalMap_mem k (γ 0)) (frameEvalMap_mem k (γ 1)) hhom hhom_mem ℤ k
  have hK := congrArg (fun (φ : Work.Thom.RelCoh ℤ k (tautologicalBundle k 10).TotalSpace
      (Work.Thom.zeroComplement (tautologicalBundle k 10)) ⟶
      Work.Thom.RelCoh ℤ k (Amb k) (framePunct k)) =>
        φ.hom (tautologicalThomClass k 10).τ) hrel
  have h0 : frameClass k σ = frameClass k (γ 0) := by rw [Path.source γ]
  have h1 : frameClass k σ' = frameClass k (γ 1) := by rw [Path.target γ]
  rw [h0, h1]
  exact hK

end

end Work.ThomBordism
