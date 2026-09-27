import Mathlib

namespace Work.Drive

/-- A linear map sends its own kernel to `⊥`. -/
lemma map_ker_eq_bot {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (LinearMap.ker f).map f = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro x ⟨y, hy, rfl⟩
  simpa using hy

/-- If `P.map f = ⊥` then `P` is contained in the kernel of `f`. -/
lemma le_ker_of_map_eq_bot {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) {P : Submodule R M}
    (h : P.map f = ⊥) : P ≤ LinearMap.ker f := by
  intro x hx
  rw [LinearMap.mem_ker]
  have hmem : f x ∈ P.map f := Submodule.mem_map_of_mem hx
  rw [h] at hmem
  simpa using hmem

/-- `map f` preserves infima of submodules that contain `ker f`. -/
lemma map_inf_of_le_ker {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) {A B : Submodule R M}
    (hA : LinearMap.ker f ≤ A) (_hB : LinearMap.ker f ≤ B) :
    (A ⊓ B).map f = A.map f ⊓ B.map f := by
  refine le_antisymm (Submodule.map_inf_le f) ?_
  intro z hz
  rw [Submodule.mem_inf] at hz
  obtain ⟨hzA, hzB⟩ := hz
  rw [Submodule.mem_map] at hzA hzB
  obtain ⟨a, ha, haz⟩ := hzA
  obtain ⟨b, hb, hbz⟩ := hzB
  rw [Submodule.mem_map]
  refine ⟨b, ⟨?_, hb⟩, hbz⟩
  have hmem : a - b ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sub, haz, hbz, sub_self]
  have hbA : b ∈ A := by
    have h₁ : a - (a - b) ∈ A := A.sub_mem ha (hA hmem)
    rwa [show a - (a - b) = b by abel] at h₁
  exact hbA

theorem inf_map_eq_bot_iff {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (π : E →L[ℝ] E') {v : E}
    (hker : LinearMap.ker π.toLinearMap = Submodule.span ℝ ({v} : Set E))
    (W : Fin 3 → Submodule ℝ E) (hW : ∀ k, Submodule.span ℝ ({v} : Set E) ≤ W k) :
    (Submodule.map π.toLinearMap (W 0) ⊓ Submodule.map π.toLinearMap (W 1) ⊓
        Submodule.map π.toLinearMap (W 2) = ⊥)
      ↔ W 0 ⊓ W 1 ⊓ W 2 = Submodule.span ℝ ({v} : Set E) := by
  have hker_le : ∀ k, LinearMap.ker π.toLinearMap ≤ W k := fun k => hker.le.trans (hW k)
  have hmap : (W 0 ⊓ W 1 ⊓ W 2).map π.toLinearMap
      = (W 0).map π.toLinearMap ⊓ (W 1).map π.toLinearMap ⊓ (W 2).map π.toLinearMap := by
    rw [map_inf_of_le_ker π.toLinearMap (le_inf (hker_le 0) (hker_le 1)) (hker_le 2),
        map_inf_of_le_ker π.toLinearMap (hker_le 0) (hker_le 1)]
  rw [← hmap]
  constructor
  · intro h
    refine le_antisymm ?_ (le_inf (le_inf (hW 0) (hW 1)) (hW 2))
    exact hker ▸ le_ker_of_map_eq_bot π.toLinearMap h
  · intro h
    rw [h, ← hker]
    exact map_ker_eq_bot π.toLinearMap

end Work.Drive
