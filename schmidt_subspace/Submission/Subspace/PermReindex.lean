import Mathlib
import Submission.Subspace.ApproxSpace

/-!
# Reindexing the approximation spaces

If `σ` is a permutation of the coordinate set and `L' i k = L (σ i) (σ k)`,
`γ' i = γ (σ i)`, then the approximation space of `(L', γ')` is the reindexing of that of
`(L, γ)`: `x ∈ V'(Q) ↔ (x ∘ σ⁻¹) ∈ V(Q)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Submission.Subspace

/-- Reindexing the approximation spaces along a permutation of the coordinates. -/
lemma mem_approxSpace_perm {n : ℕ} (σ : Equiv.Perm (Fin (n+1)))
    (L : Fin (n+1) → Fin (n+1) → ℂ) (γ : Fin (n+1) → ℝ) (Q : ℝ)
    (x : Fin (n+1) → ℚ) :
    x ∈ approxSpace (fun i k => L (σ i) (σ k)) (fun i => γ (σ i)) Q
      ↔ (fun i => x (σ.symm i)) ∈ approxSpace L γ Q := by
  classical
  let Τ : (Fin (n+1) → ℚ) →ₗ[ℚ] (Fin (n+1) → ℚ) :=
    { toFun := fun x i => x (σ.symm i)
      map_add' := fun a b => by funext i; simp
      map_smul' := fun c a => by funext i; simp }
  have hΤinj : Function.Injective Τ := by
    intro a b hab
    funext i
    have := congrFun hab (σ i)
    simpa [Τ] using this
  have hT : ∀ y : Fin (n+1) → ℤ, Τ (intCastVec y) = intCastVec (fun i => y (σ.symm i)) := by
    intro y; funext i; simp [Τ, intCastVec]
  have hbox : ∀ y : Fin (n+1) → ℤ,
      ((fun i => y (σ.symm i)) ∈ approxBox L γ Q)
        ↔ (y ∈ approxBox (fun i k => L (σ i) (σ k)) (fun i => γ (σ i)) Q) := by
    intro y
    rw [mem_approxBox_iff, mem_approxBox_iff]
    constructor
    · intro h i
      have h1 : ‖(∑ j, L (σ i) j * ((y (σ.symm j) : ℤ) : ℂ))‖ ≤ Q ^ (γ (σ i)) := h (σ i)
      have e2 : (∑ j, L (σ i) j * ((y (σ.symm j) : ℤ) : ℂ))
          = ∑ k, L (σ i) (σ k) * ((y k : ℤ) : ℂ) := by
        rw [← Equiv.sum_comp σ (fun j => L (σ i) j * ((y (σ.symm j) : ℤ) : ℂ))]
        simp
      rwa [e2] at h1
    · intro h i
      have h1 : ‖(∑ k, L (σ (σ.symm i)) (σ k) * ((y k : ℤ) : ℂ))‖ ≤ Q ^ (γ (σ (σ.symm i))) :=
        h (σ.symm i)
      rw [Equiv.apply_symm_apply σ i] at h1
      have e2 : (∑ k, L i (σ k) * ((y k : ℤ) : ℂ))
          = ∑ j, L i j * ((y (σ.symm j) : ℤ) : ℂ) := by
        rw [← Equiv.sum_comp σ (fun j => L i j * ((y (σ.symm j) : ℤ) : ℂ))]
        simp
      rwa [e2] at h1
  have hset : Τ '' (intCastVec '' approxBox (fun i k => L (σ i) (σ k))
        (fun i => γ (σ i)) Q) = intCastVec '' approxBox L γ Q := by
    ext z
    constructor
    · rintro ⟨w, ⟨y, hyBox, rfl⟩, rfl⟩
      rw [hT y]
      exact ⟨fun i => y (σ.symm i), (hbox y).mpr hyBox, rfl⟩
    · rintro ⟨y, hyBox, rfl⟩
      refine ⟨intCastVec (fun i => y (σ i)), ⟨fun i => y (σ i), ?_, rfl⟩, ?_⟩
      · refine (hbox (fun i => y (σ i))).mp ?_
        rw [show (fun i => (fun i => y (σ i)) (σ.symm i)) = y from by funext i; simp]
        exact hyBox
      · rw [hT]; congr 1; funext i; simp
  have hmap : Submodule.map Τ (approxSpace (fun i k => L (σ i) (σ k))
      (fun i => γ (σ i)) Q) = approxSpace L γ Q := by
    simp only [approxSpace, Submodule.map_span, hset]
  rw [← hmap, Submodule.mem_map]
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rw [hΤinj hyx] at hy
    exact hy

end Submission.Subspace
