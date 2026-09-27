import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.gapA.rotationFormula
import Submission.Work.Mostow.gapA.commutingRotation_eq_or_inv
import Submission.Work.Mostow.gapA.rotSetup
import Submission.Work.Mostow.gapA.screwDefs
import Submission.Work.Mostow.gapA.screwLine
import Submission.Work.Mostow.gapA.screwGeodParam
import Submission.Work.Mostow.gapA.affineOfDist
import Submission.Work.Mostow.gapA.screwLinear

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open scoped Matrix

noncomputable section

theorem screwScale {a b : Submission.Mostow.E 3} (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3)
    (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b)
    (g : LeanEval.Geometry.MostowRigidity.PO 3 1) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hmap : ∀ u : Submission.Mostow.E 3, u ∈ geodSet a b → g • u ∈ geodSet a b)
    (hg : ∀ u : Submission.Mostow.E 3, u ∈ geodSet a b → Submission.Mostow.hdist u (g • u) = ℓ) :
    ∃ ρ : ℝ, 0 < ρ ∧ _root_.Matrix.mulVec (Work.Mostow.emat g) (nvec a) = ρ • nvec a ∧
      _root_.Matrix.mulVec (Work.Mostow.emat g) (nvec b) = ρ⁻¹ • nvec b ∧ ρ + ρ⁻¹ = 2 * Real.cosh ℓ := by
  obtain ⟨hgeodmem, hsurj, hinj, hspanAB, hspan01, hprj⟩ := screwGeodParam ha hb hab
  obtain ⟨hkk_sq, hkk_pos, hneg, htime_pos, hpair, hlift_ax, hdist_ax⟩ := screwLine ha hb hab
  have hisom : ∀ u v : Submission.Mostow.E 3,
      Submission.Mostow.hdist (g • u) (g • v) = Submission.Mostow.hdist u v :=
    hI.2.2.2.2.2.2.1 g
  have hφ : ∀ s : ℝ, ∃ t : ℝ, g • axisPt a b s = axisPt a b t :=
    fun s => hsurj _ (hmap _ (hgeodmem s))
  let φ : ℝ → ℝ := fun s => Classical.choose (hφ s)
  have hφspec : ∀ s : ℝ, g • axisPt a b s = axisPt a b (φ s) :=
    fun s => Classical.choose_spec (hφ s)
  have hdistφ : ∀ s t : ℝ, |φ s - φ t| = |s - t| := by
    intro s t
    have h1 : Submission.Mostow.hdist (axisPt a b (φ s)) (axisPt a b (φ t))
        = Submission.Mostow.hdist (axisPt a b s) (axisPt a b t) := by
      rw [← hφspec s, ← hφspec t]
      exact hisom _ _
    rwa [hdist_ax (φ s) (φ t), hdist_ax s t] at h1
  have hself : ∀ s : ℝ, |φ s - s| = ℓ := by
    intro s
    have h1 : Submission.Mostow.hdist (axisPt a b s) (axisPt a b (φ s)) = ℓ := by
      rw [← hφspec s]
      exact hg (axisPt a b s) (hgeodmem s)
    rw [hdist_ax s (φ s)] at h1
    rwa [abs_sub_comm] at h1
  obtain ⟨c, hcabs, hceq⟩ := affineOfDist hdistφ hself
  have hLam : ∀ s : ℝ, _root_.Matrix.mulVec (Work.Mostow.emat g) (axisV a b s)
      = axisV a b (s + c) := by
    intro s
    calc _root_.Matrix.mulVec (Work.Mostow.emat g) (axisV a b s)
        = _root_.Matrix.mulVec (Work.Mostow.emat g) (Submission.Mostow.hlift (axisPt a b s)) := by
          rw [hlift_ax s]
      _ = Submission.Mostow.hlift (g • axisPt a b s) := Work.Mostow.emat_hlift g (axisPt a b s)
      _ = Submission.Mostow.hlift (axisPt a b (φ s)) := by rw [hφspec s]
      _ = axisV a b (φ s) := hlift_ax (φ s)
      _ = axisV a b (s + c) := by
          rw [hceq s]
          exact congrArg (axisV a b) (add_comm c s)
  obtain ⟨hA_eig, hB_eig⟩ := screwLinear ha hb hab g c hLam
  have hcosh : Real.cosh c = Real.cosh ℓ := by
    rw [← Real.cosh_abs c, hcabs]
  refine ⟨Real.exp c, Real.exp_pos c, hA_eig, hB_eig, ?_⟩
  rw [← Real.exp_neg c, ← hcosh, Real.cosh_eq]
  ring

end

end Work.Mostow.gapA
