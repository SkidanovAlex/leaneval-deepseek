import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.ClassC.Gsing_add_mul_open
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.EllExist.Shift
import Submission.Work.FTS.EllSol.EllAux2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## A3 at an arbitrary level -/

/-- **A3 at an arbitrary level `K`**: `EllClassOk K` is closed under
`(g, Ψ) ↦ (g + c • g', Ψ + c • Ψ')` over the linear class `ClassC`. -/
theorem ellClassOk_add_gen (K : ℕ) {α : ℝ} (hα : 0 < α) {g g' Ψ Ψ' : Work.FTS.Galerkin.Fn}
    (c : ℝ)
    (hg : Work.FTS.ClassC.ClassC α g) (hg' : Work.FTS.ClassC.ClassC α g')
    (h : Work.FTS.EllExist.EllClassOk K α g Ψ)
    (h' : Work.FTS.EllExist.EllClassOk K α g' Ψ') :
    Work.FTS.EllExist.EllClassOk K α (g + c • g') (Ψ + c • Ψ') := by
  have hgadd : (g + c • g') = fun z θ => g z θ + c * g' z θ := by
    funext z θ; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hΨadd : (Ψ + c • Ψ') = fun z θ => Ψ z θ + c * Ψ' z θ := by
    funext z θ; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hcΨ' : (fun z θ => c * Ψ' z θ) = c • Ψ' := by
    funext z θ; simp only [Pi.smul_apply, smul_eq_mul]
  rw [hgadd, hΨadd]
  -- the two pieces of weak-class data
  have hshift : Work.FTS.EllipticEst.TT.EllWeakPos α K
      (Work.Elliptic.orthSource g)
      (fun z θ => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ)) := h.2.2
  have hshift' : Work.FTS.EllipticEst.TT.EllWeakPos α K
      (Work.Elliptic.orthSource g')
      (fun z θ => Ψ' z θ + Work.Elliptic.Gsing α g' z * Real.sin (2 * θ)) := h'.2.2
  -- the two sources are smooth on the open quadrant: they are `bslOp` of the shifted unknowns
  have hsoF : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) := by
    have hSso : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ)) :=
      Work.FTS.EllipticEst.smoothOpen_of_forall hshift.smooth
    exact (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hSso).congr
      (fun z θ hz h0 h1 => hshift.eq z hz θ h0 h1)
  have hsoF' : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g') := by
    have hSso : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => Ψ' z θ + Work.Elliptic.Gsing α g' z * Real.sin (2 * θ)) :=
      Work.FTS.EllipticEst.smoothOpen_of_forall hshift'.smooth
    exact (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hSso).congr
      (fun z θ hz h0 h1 => hshift'.eq z hz θ h0 h1)
  have hmemF0 : Work.Spaces.HkMem α 0 (Work.Elliptic.orthSource g) :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := K) (Nat.zero_le K)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsoF) hshift.memF
  have hmemF0' : Work.Spaces.HkMem α 0 (Work.Elliptic.orthSource g') :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := K) (Nat.zero_le K)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsoF') hshift'.memF
  -- the solvability condition of the combined source
  have horth : ∀ z, 0 < z → Work.Elliptic.Fstar
      (fun z θ => Work.Elliptic.orthSource g z θ + c * Work.Elliptic.orthSource g' z θ) z
      = 0 := by
    intro z hz
    rw [Work.FTS.EllSol.Fstar_add_mul
      (Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2 hsoF.continuousOn
        hmemF0 hz)
      (Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2 hsoF'.continuousOn
        hmemF0' hz),
      Work.FTS.EllExist.Fstar_orthSource_zero, Work.FTS.EllExist.Fstar_orthSource_zero]
    ring
  have hcl := Work.FTS.EllSol.EllWeakPos_add_mul hsoF hsoF' horth hshift hshift'
  -- congruence with the combination
  have hFcongr : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      (fun z θ => Work.Elliptic.orthSource g z θ + c * Work.Elliptic.orthSource g' z θ) z θ
        = Work.Elliptic.orthSource (fun z θ => g z θ + c * g' z θ) z θ := by
    intro z θ hz h0 h1
    exact (Work.FTS.EllSol.orthSource_add_mul_apply
      (Work.FTS.EllSol.Fstar_add_mul
        (slice_sinCos2_integrable hg.reg (classC_hkMem_zero hg) hz)
        (slice_sinCos2_integrable hg'.reg (classC_hkMem_zero hg') hz))).symm
  have hScongr : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      (fun z θ => (fun z θ => Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ)) z θ
          + c * (fun z θ => Ψ' z θ + Work.Elliptic.Gsing α g' z * Real.sin (2 * θ)) z θ) z θ
        = (fun z θ => (fun z θ => Ψ z θ + c * Ψ' z θ) z θ
            + Work.Elliptic.Gsing α (fun z θ => g z θ + c * g' z θ) z
              * Real.sin (2 * θ)) z θ := by
    intro z θ hz h0 h1
    show Ψ z θ + Work.Elliptic.Gsing α g z * Real.sin (2 * θ)
        + c * (Ψ' z θ + Work.Elliptic.Gsing α g' z * Real.sin (2 * θ))
      = Ψ z θ + c * Ψ' z θ
        + Work.Elliptic.Gsing α (fun z θ => g z θ + c * g' z θ) z * Real.sin (2 * θ)
    have hG := Gsing_add_mul_open hα c hz hg.reg (classC_hkMem_four hg) hg'.reg
      (classC_hkMem_four hg')
    rw [hG]
    ring
  have h0' : ∀ z, (fun z θ => (fun z θ => Ψ z θ + c * Ψ' z θ) z θ
      + Work.Elliptic.Gsing α (fun z θ => g z θ + c * g' z θ) z * Real.sin (2 * θ)) z 0 = 0 := by
    intro z
    show Ψ z 0 + c * Ψ' z 0
      + Work.Elliptic.Gsing α (fun z θ => g z θ + c * g' z θ) z * Real.sin (2 * 0) = 0
    rw [show (2 : ℝ) * 0 = 0 from by norm_num, Real.sin_zero,
      h.1.2.1 z, h'.1.2.1 z]
    ring
  have hpi' : ∀ z, (fun z θ => (fun z θ => Ψ z θ + c * Ψ' z θ) z θ
      + Work.Elliptic.Gsing α (fun z θ => g z θ + c * g' z θ) z
        * Real.sin (2 * θ)) z (π / 2) = 0 := by
    intro z
    show Ψ z (π / 2) + c * Ψ' z (π / 2)
      + Work.Elliptic.Gsing α (fun z θ => g z θ + c * g' z θ) z * Real.sin (2 * (π / 2)) = 0
    rw [show (2 : ℝ) * (π / 2) = π from by ring, Real.sin_pi,
      h.1.2.2.1 z, h'.1.2.2.1 z]
    ring
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_,
    Work.FTS.EllSol.EllWeakPos_congr_Q0 hcl hFcongr hScongr h0' hpi'⟩
  · -- the equation of the combined unknown
    intro z hz θ h0 h1
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩)
    have hb1 : Work.Elliptic.bslOp α (fun z θ => Ψ z θ + c * Ψ' z θ) z θ
        = Work.Elliptic.bslOp α Ψ z θ
          + Work.Elliptic.bslOp α (fun z θ => c * Ψ' z θ) z θ :=
      Work.Elliptic.bslOp_add α Ψ (fun z θ => c * Ψ' z θ) z θ hcos
        (Work.FTS.EllSol.smoothOpen_contDiffAt_two h.2.1 hz h0 h1)
        (Work.FTS.EllSol.smoothOpen_contDiffAt_two (h'.2.1.const_mul' c) hz h0 h1)
    have hb2 : Work.Elliptic.bslOp α (fun z θ => c * Ψ' z θ) z θ
        = c * Work.Elliptic.bslOp α Ψ' z θ := by
      have hs := Work.FTS.EllipticEst.LevelOneFts.CF.bslOp_smul α c Ψ' z θ
      rw [← hcΨ'] at hs
      exact hs
    rw [hb1, hb2, h.1.1 z hz θ h0 h1, h'.1.1 z hz θ h0 h1]
  · -- the Dirichlet value at `θ = 0`
    intro z
    show Ψ z 0 + c * Ψ' z 0 = 0
    rw [h.1.2.1 z, h'.1.2.1 z]
    ring
  · -- the Dirichlet value at `θ = π/2`
    intro z
    show Ψ z (π / 2) + c * Ψ' z (π / 2) = 0
    rw [h.1.2.2.1 z, h'.1.2.2.1 z]
    ring
  · -- the decay at `z → ∞`
    intro θ hθ
    have h1 := (h.1.2.2.2 θ hθ).add ((h'.1.2.2.2 θ hθ).const_mul c)
    simpa using h1
  · -- smoothness of the combined unknown
    exact Work.FTS.EllipticEst.smoothOpen_add h.2.1 (h'.2.1.const_mul' c)

end Work.FTS.ClassC
