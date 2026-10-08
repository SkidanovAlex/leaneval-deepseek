import Mathlib
import Submission.Work.FeitSibley.CharQ.scriptS_eq_image
import Submission.Work.FeitSibley.CharQ.prodChar_mem_Irr
import Submission.Work.FeitSibley.CharQ.prodChar_Q1_kernel_iff
import Submission.Work.FeitSibley.Coherence.scriptSR_deg_Qcomm
import Submission.Work.CharCore.principalChar_mem_Irr
import Submission.Work.Induction.indFun_apply_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.FeitSibley.CharQ

theorem degree_D_scriptS {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (hlin : ∃ theta ∈ Work.CharCore.Irr ↥h.Q1, theta 1 = 1 ∧ theta ≠ (fun _ : ↥h.Q1 => 1)) :
    ∃ chi ∈ Work.FeitSibley.scriptS h.H h.Q1,
      chi 1 = (Nat.card h.D : ℂ) ∧
      ∀ psi ∈ Work.FeitSibley.scriptS h.H h.Q1,
        ∃ a : ℕ, psi 1 = (a : ℂ) * (Nat.card h.D : ℂ) := by
  classical
  obtain ⟨theta, hthetaIrr, htheta1, hthetane⟩ := hlin
  -- The trivial character of `S` (in `S × Q₁`), paired with the non-trivial linear `theta`.
  have hlamIrr : (fun _ : ↥h.S => (1 : ℂ)) ∈ Work.CharCore.Irr ↥h.S :=
    Work.CharCore.principalChar_mem_Irr
  have hphiIrr : h.prodChar (fun _ : ↥h.S => (1 : ℂ)) theta ∈ Work.CharCore.Irr ↥h.Q :=
    prodChar_mem_Irr h hlamIrr hthetaIrr
  have hphi1 : h.prodChar (fun _ : ↥h.S => (1 : ℂ)) theta 1 = 1 := by
    rw [h.prodChar_one, htheta1]; simp
  -- `prodChar lam theta` is non-trivial on `Q₁`, since `theta` is.
  have hwit : ∃ x : ↥h.Q, (x : G) ∈ h.Q1 ∧
      h.prodChar (fun _ : ↥h.S => (1 : ℂ)) theta x
        ≠ h.prodChar (fun _ : ↥h.S => (1 : ℂ)) theta 1 := by
    by_contra hcon
    push Not at hcon
    exact hthetane ((prodChar_Q1_kernel_iff h hlamIrr hthetaIrr).mp hcon)
  refine ⟨h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) theta), ?_, ?_, ?_⟩
  · rw [scriptS_eq_image]
    exact ⟨_, hphiIrr, hwit, rfl⟩
  · -- degree of the chosen character is `[H : Q] · 1 = |D|`
    have hdef : h.indQH (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) theta)
        = Work.Induction.indFun (h.Q.subgroupOf h.H)
            (pull h (h.prodChar (fun _ : ↥h.S => (1 : ℂ)) theta)) := rfl
    rw [hdef, Work.Induction.indFun_apply_one, Work.FeitSibley.Coherence.index_subgroupOf_Q h,
      pull_one, hphi1, mul_one]
  · intro psi hpsi
    rw [scriptS_eq_image] at hpsi
    obtain ⟨phi, hphiIrr, -, rfl⟩ := hpsi
    refine ⟨Work.CharCore.irrDeg phi, ?_⟩
    have hdef : h.indQH phi = Work.Induction.indFun (h.Q.subgroupOf h.H) (pull h phi) := rfl
    rw [hdef, Work.Induction.indFun_apply_one, Work.FeitSibley.Coherence.index_subgroupOf_Q h,
      pull_one, Work.CharCore.irrDeg_spec hphiIrr, mul_comm]

end Work.FeitSibley.CharQ
