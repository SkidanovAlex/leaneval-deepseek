import Mathlib
import Submission.Work.ORLyndon.ProjDim

namespace Work.ORLyndon

universe v

/-- If a module admits a projective resolution of length at most `n`, then it admits one of
length at most `n + 1`: keep the first projective cover and apply the same increment to its
kernel (induction on `n`). The base case takes the identity cover of a projective module, whose
kernel is the zero (hence projective) module. -/
theorem HasProjDimLE.of_succ {R : Type*} [Ring R] {M : Type v} [AddCommGroup M]
    [Module R M] {n : ℕ} (h : HasProjDimLE R M n) : HasProjDimLE R M (n + 1) := by
  induction n generalizing M with
  | zero =>
    refine ⟨M, inferInstance, inferInstance, h, LinearMap.id, ?_, ?_⟩
    · exact fun x => ⟨x, rfl⟩
    · rw [LinearMap.ker_id]
      show Module.Projective R (⊥ : Submodule R M)
      infer_instance
  | succ k ih =>
    obtain ⟨P, i1, i2, hP, f, hf, hker⟩ := h
    exact ⟨P, i1, i2, hP, f, hf, ih hker⟩

/-- `HasProjDimLE R M m` is monotone in the bound `m`. -/
theorem HasProjDimLE_add {R : Type*} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    (d : ℕ) {m : ℕ} (h : HasProjDimLE R M m) : HasProjDimLE R M (m + d) := by
  induction d with
  | zero => simpa using h
  | succ d ih =>
    have h' : HasProjDimLE R M (m + d + 1) := HasProjDimLE.of_succ ih
    rwa [Nat.add_succ] at h'

theorem HasProjDimLE_mono {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {m n : ℕ} (hmn : m ≤ n) (h : Work.ORLyndon.HasProjDimLE R M m) :
    Work.ORLyndon.HasProjDimLE R M n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact HasProjDimLE_add d h

end Work.ORLyndon
