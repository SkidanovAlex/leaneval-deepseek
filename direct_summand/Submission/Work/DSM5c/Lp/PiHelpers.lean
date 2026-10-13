import Mathlib

/-!
# Helper lemmas about `I • ⊤` on products and under linear maps

* `Work.DSM5c.Lp.smul_top_pi` — `I • ⊤` of a finite product of modules is the product of the
  `I • ⊤` of the factors;
* `Work.DSM5c.Lp.map_smul_top_le` — a linear map carries `I • ⊤` into `I • ⊤`.

These are used to identify the kernel `p · (∏ᵢ Mᵢ)` of a termwise-surjective map of Čech complexes
with the product of the kernels.
-/

open scoped Pointwise

namespace Work.DSM5c.Lp

universe a

/-- `I • ⊤` of a finite product of modules is the product of the `I • ⊤` of the factors. -/
theorem smul_top_pi {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι] [Finite ι]
    {M : ι → Type a} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (I : Ideal R) :
    I • (⊤ : Submodule R ((i : ι) → M i)) =
      Submodule.pi Set.univ (fun i => I • (⊤ : Submodule R (M i))) := by
  refine le_antisymm ?_ ?_
  · refine Submodule.smul_le.2 (fun r hr x _ => ?_)
    rw [Submodule.mem_pi]
    intro i _
    simpa using Submodule.smul_mem_smul hr (Submodule.mem_top : x i ∈ (⊤ : Submodule R (M i)))
  · rw [← Submodule.iSup_map_single (p := fun i => I • (⊤ : Submodule R (M i)))]
    refine iSup_le (fun i => ?_)
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top

/-- A linear map carries `I • ⊤` into `I • ⊤`. -/
theorem map_smul_top_le {R : Type a} [CommRing R] {M : Type a} [AddCommGroup M] [Module R M]
    {N : Type a} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (I : Ideal R) :
    (I • (⊤ : Submodule R M)).map f ≤ I • (⊤ : Submodule R N) := by
  rw [Submodule.map_smul'']
  exact Submodule.smul_mono le_rfl le_top

/-- Membership in `I • ⊤` of a finite product: the product of the `I • ⊤` of the factors. -/
theorem mem_smul_top_pi_iff {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι] [Finite ι]
    {M : ι → Type a} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (I : Ideal R)
    (x : (i : ι) → M i) :
    x ∈ I • (⊤ : Submodule R ((i : ι) → M i)) ↔
      ∀ i, x i ∈ I • (⊤ : Submodule R (M i)) := by
  rw [smul_top_pi, Submodule.mem_pi]
  simp

end Work.DSM5c.Lp
