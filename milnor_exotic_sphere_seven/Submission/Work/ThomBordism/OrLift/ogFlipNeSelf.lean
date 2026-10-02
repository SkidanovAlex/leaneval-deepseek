import Mathlib
import Submission.Work.ThomBordism.Grassmann.Grassmannian
import Submission.Work.ThomBordism._gtd.P1
import Submission.Work.ThomBordism.Signs.coordChangeO_ogFlip_mul_flipMat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Two elementary facts used by the oriented-lift construction

* `Work.ThomBordism.ol_continuous_ite_of_clopen`: a function which is defined by two continuous
  branches on a clopen partition is continuous.
* `Work.ThomBordism.ol_ogFlip_ne_self`: the orientation reversal `ogFlip` of the oriented
  Grassmannian has no fixed point when `k ≥ 1`.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped Topology Matrix
open Classical

namespace Work.ThomBordism

open Work.PTGeometric
open Work.ThomBordism.Grassmann

/-- **A function defined by two continuous branches on a clopen partition is continuous.** -/
theorem ol_continuous_ite_of_clopen {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} (hs : IsClopen s) {f g : X → Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => if x ∈ s then f x else g x := by
  rw [continuous_def]
  intro U hU
  have hpre : (fun x => if x ∈ s then f x else g x) ⁻¹' U
      = (s ∩ f ⁻¹' U) ∪ (sᶜ ∩ g ⁻¹' U) := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hpre]
  exact (hs.isOpen.inter (hU.preimage hf)).union (hs.isClosed.isOpen_compl.inter (hU.preimage hg))

/-- **The orientation reversal of `G̃r_k(ℝ^{k+m})` has no fixed point** for `k ≥ 1`. -/
theorem ol_ogFlip_ne_self {k m : ℕ} (hk : 0 < k) (x : OG k m) : ogFlip k m x ≠ x := by
  intro h
  obtain ⟨f, rfl⟩ := Quotient.exists_rep x
  rw [ogFlip_mk] at h
  obtain ⟨A, hA⟩ := Quotient.exact h
  let M : Matrix (Fin k) (Fin k) ℝ := A.1
  have hMdet : M.det = 1 := A.2.2
  have hA' : f.1 = soActFun M (soActFun (flipMat k) f.1) := by
    have h3 : f.1 = (A.act (⟨soActFun (flipMat k) f.1,
        orthonormal_soActFun (flipMat_transpose_mul k) f.2⟩ : Stiefel k m)).1 := by
      nth_rewrite 1 [hA]
      rfl
    have h4 : (A.act (⟨soActFun (flipMat k) f.1,
        orthonormal_soActFun (flipMat_transpose_mul k) f.2⟩ : Stiefel k m)).1
        = soActFun M (soActFun (flipMat k) f.1) := rfl
    exact h3.trans h4
  rw [soActFun_comp] at hA'
  obtain ⟨S, hS⟩ := exists_chartIdx_det_ne_zero f.1 f.2.linearIndependent
  have h5 : frameMatrix S f.1 = frameMatrix S f.1 * (flipMat k * M) := by
    conv_lhs => rw [hA']
    rw [frameMatrix_soActFun]
  have h6 := congrArg Matrix.det h5
  rw [Matrix.det_mul] at h6
  rw [Matrix.det_mul] at h6
  rw [Work.ThomBordism.Signs.CoordFlip.flipMat_det hk, hMdet, mul_one] at h6
  have h7 : (frameMatrix S f.1).det = 0 := by linarith
  exact hS h7

end Work.ThomBordism
