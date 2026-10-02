import Submission.Work.PTGeometric.RieszProj.SmoothIntegrand
import Submission.Work.PTGeometric.RieszProj.contDiffOn_intervalIntegral
import Submission.Work.PTGeometric.RieszProj.Symm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Smoothness of the Riesz projection and of the retraction `Rmap`

The Riesz projection `Phi` is `C^∞` at every point `x₀` at which `contDen x₀ θ` is invertible for all
`θ ∈ [0, 2π]` (smoothness of the parametric contour integral); consequently the retraction
`Rmap = Phi ∘ symm` is `C^∞` on `good n k`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped ContDiff InnerProduct
open Set Function MeasureTheory

namespace Work.PTGeometric

noncomputable section

variable {n : ℕ}

/-- The adjoint of an operator, as a continuous linear map. -/
def adjointCLM (n : ℕ) : EndOp n →L[ℝ] EndOp n where
  toFun := fun A => A†
  map_add' A B := map_add _ _ _
  map_smul' c A := by
    rw [map_smulₛₗ]
    simp
  cont := continuous_adjoint_clm

lemma contDiff_adjoint : ContDiff ℝ ∞ (fun A : EndOp n => (A† : EndOp n)) :=
  (adjointCLM n).contDiff

lemma contDiff_symm : ContDiff ℝ ∞ (fun A : EndOp n => symm A) := by
  have h1 : ContDiff ℝ ∞ (fun A : EndOp n => A + A†) := contDiff_id.add contDiff_adjoint
  have h2 := h1.const_smul ((2:ℝ)⁻¹)
  simpa only [symm] using h2

/-- The Riesz projection is `C^∞` where the contour denominator is invertible. -/
lemma contDiffAt_Phi {x₀ : EndOp n}
    (h : ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), IsUnit (contDen x₀ θ)) :
    ContDiffAt ℝ ∞ Phi x₀ := by
  obtain ⟨s, hsopen, hx₀, J, hJopen, hJsub, hG⟩ := contIntegrand_contDiffOn_nhds h
  have hπ : (0:ℝ) ≤ 2 * Real.pi := by positivity
  have h1 : ContDiffOn ℝ ∞ (fun x : EndOp n => ∫ θ in (0:ℝ)..(2 * Real.pi), contIntegrand x θ) s :=
    RieszProj.contDiffOn_intervalIntegral (a := 0) (b := 2 * Real.pi) (J := J) (G := contIntegrand)
      hπ hsopen hJopen hJsub hG
  have h2 : ContDiffAt ℝ ∞ (fun x : EndOp n => ∫ θ in (0:ℝ)..(2 * Real.pi), contIntegrand x θ) x₀ :=
    h1.contDiffAt (hsopen.mem_nhds hx₀)
  exact h2.const_smul _

/-- Pointwise form: `Phi` is `C^∞` on the set where `contDen` is everywhere invertible. -/
lemma contDiffOn_Phi :
    ContDiffOn ℝ ∞ (fun x : EndOp n => Phi x)
      {x : EndOp n | ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), IsUnit (contDen x θ)} :=
  fun _ hx => (contDiffAt_Phi hx).contDiffWithinAt

/-- The retraction `Rmap = Phi ∘ symm` is `C^∞` on `good n k`. -/
lemma contDiffOn_Rmap (n k : ℕ) : ContDiffOn ℝ ∞ (fun A : EndOp n => Rmap A) (good n k) := by
  have hsymm : ContDiffOn ℝ ∞ (fun A : EndOp n => symm A) (good n k) :=
    (contDiff_symm (n := n)).contDiffOn
  refine (contDiffOn_Phi (n := n)).comp hsymm ?_
  intro A hA
  rw [mem_good_iff] at hA
  obtain ⟨P, hP, hAP⟩ := hA
  intro θ _
  exact isUnit_contDen (symm_isSymmetric A) (Cluster.of_dist hP hAP) θ

end

end Work.PTGeometric
