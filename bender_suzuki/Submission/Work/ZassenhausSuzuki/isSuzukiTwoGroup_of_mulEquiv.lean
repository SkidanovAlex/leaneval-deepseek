import Submission.Work.ZassenhausSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `IsSuzukiTwoGroup` is invariant under isomorphism

Higman's notion of a Suzuki 2-group (`Submission.Blueprint.IsSuzukiTwoGroup`) is defined by
group-theoretic conditions, so it transports along a `MulEquiv`.  (Used to transfer the
statement from the two-step model `Work.Higman.AType` to this area's `A(K,θ)`.)
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

theorem isSuzukiTwoGroup_of_mulEquiv {P Q : Type} [Group P] [Finite P] [Group Q] [Finite Q]
    (e : P ≃* Q) (h : IsSuzukiTwoGroup Q) : IsSuzukiTwoGroup P := by
  obtain ⟨hP, hnab, hinv, ξ, hξ⟩ := h
  refine ⟨hP.of_equiv e.symm, ?_, ?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hnab
    exact ⟨e.symm x, e.symm y, fun hc => hxy (by simpa using congrArg e hc)⟩
  · obtain ⟨x, y, hx, hy, hne⟩ := hinv
    refine ⟨e.symm x, e.symm y, ?_, ?_, ?_⟩
    · simpa using hx
    · simpa using hy
    · intro hc; exact hne (by simpa using congrArg e hc)
  · refine ⟨e.trans (ξ.trans e.symm), ?_⟩
    intro x y hx hy
    obtain ⟨k, hk⟩ := hξ (e x) (e y) (by simpa using hx) (by simpa using hy)
    refine ⟨k, ?_⟩
    have key : ∀ (j : ℕ) (z : P),
        ((e.trans (ξ.trans e.symm)) ^ j) z = e.symm ((ξ ^ j) (e z)) := by
      intro j
      induction j with
      | zero => intro z; simp
      | succ j ih =>
        intro z
        rw [pow_succ, MulAut.mul_apply, ih (e.trans (ξ.trans e.symm) z)]
        congr 1
        rw [show e (e.trans (ξ.trans e.symm) z) = ξ (e z) from by
          rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]]
        rw [pow_succ, MulAut.mul_apply]
    rw [key k x, hk, MulEquiv.symm_apply_apply]

end Work.ZassenhausSuzuki
