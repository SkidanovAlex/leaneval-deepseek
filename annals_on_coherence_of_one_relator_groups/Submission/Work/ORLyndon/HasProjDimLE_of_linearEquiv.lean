import Mathlib
import Submission.Work.ORLyndon.ProjDim

namespace Work.ORLyndon

universe v

/-- `HasProjDimLE R M n` depends only on the isomorphism class of the module `M`: a linear
equivalence `M ≃ₗ[R] M'` carries a projective resolution of length at most `n` of `M` to one
of `M'` (use the same projective modules, and compose each map of the resolution with `e`;
the kernels change by a linear equivalence, so the induction on `n` goes through). -/
theorem HasProjDimLE_of_linearEquiv {R : Type*} [Ring R] {M M' : Type v} [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M') {n : ℕ}
    (h : Work.ORLyndon.HasProjDimLE R M n) : Work.ORLyndon.HasProjDimLE R M' n := by
  induction n generalizing M M' with
  | zero =>
    have hproj : Module.Projective R M := h
    exact Module.Projective.of_equiv' e
  | succ n ih =>
    obtain ⟨P, inst1, inst2, hP, f, hf, hker⟩ := h
    refine ⟨P, inst1, inst2, hP, e.toLinearMap.comp f, e.surjective.comp hf, ?_⟩
    have hk : LinearMap.ker (e.toLinearMap.comp f) = LinearMap.ker f := by
      ext x
      simp [LinearMap.mem_ker]
    rw [hk]
    exact hker

end Work.ORLyndon
