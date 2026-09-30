import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The hyperplane `{u : Fin n → ℚ | ∑ i, f i * u i = 0}` cut out by a nonzero functional `f`
has `ℚ`-dimension `n - 1`. -/
lemma finrank_ker_dot {n : ℕ} (f : Fin n → ℚ) (hf : f ≠ 0) :
    Module.finrank ℚ ↥(LinearMap.ker
      ((∑ i : Fin n, f i • LinearMap.proj i) : (Fin n → ℚ) →ₗ[ℚ] ℚ)) = n - 1 := by
  -- The functional `φ = ∑ i, f i • proj i` is nonzero as soon as `f` is: evaluating at the
  -- `j`-th standard basis vector recovers `f j`.
  have hφ : (∑ i : Fin n, f i • LinearMap.proj i : (Fin n → ℚ) →ₗ[ℚ] ℚ) ≠ 0 := by
    intro h
    apply hf
    funext j
    have key : (∑ i : Fin n, f i • LinearMap.proj i :
        (Fin n → ℚ) →ₗ[ℚ] ℚ) (Pi.single j 1) = f j := by
      rw [LinearMap.sum_apply]
      rw [Finset.sum_eq_single j]
      · simp [Pi.single_eq_same]
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    have h2 := congrArg (fun g : (Fin n → ℚ) →ₗ[ℚ] ℚ => g (Pi.single j 1)) h
    rw [key, LinearMap.zero_apply] at h2
    exact h2
  -- Rank–nullity for a nonzero functional into a field: the kernel has codimension `1`.
  have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
  rw [Module.finrank_pi ℚ, Fintype.card_fin] at h1
  omega

end Work.BW
