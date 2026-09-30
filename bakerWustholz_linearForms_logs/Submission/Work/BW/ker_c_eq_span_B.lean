import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open BigOperators

namespace Work.BW

/-- If `c : Fin (r - 1) → Fin r → ℚ` has linearly independent rows and `B ≠ 0` lies in the
kernel of the corresponding linear map, then the kernel is exactly the line spanned by `B`. -/
theorem ker_c_eq_span_B {r : ℕ} (c : Fin (r - 1) → Fin r → ℚ) (hc : LinearIndependent ℚ c)
    (B : Fin r → ℤ) (hB : B ≠ 0) (hcB : ∀ m, ∑ i, c m i * (B i : ℚ) = 0) :
    ∀ u : Fin r → ℚ, (∀ m, ∑ i, c m i * u i = 0) →
      ∃ t : ℚ, u = fun i => t * (B i : ℚ) := by
  intro u hu
  -- View `c` as a matrix and the defining system as its `mulVecLin`.
  let M : Matrix (Fin (r - 1)) (Fin r) ℚ := fun m i => c m i
  have hrow : M.row = c := by funext m i; rfl
  have hL : LinearIndependent ℚ M.row := by rw [hrow]; exact hc
  -- The rank of `M` is the number of its (independent) rows, namely `r - 1`.
  have hrank : M.rank = r - 1 := by
    rw [LinearIndependent.rank_matrix hL, Fintype.card_fin]
  let f : (Fin r → ℚ) →ₗ[ℚ] (Fin (r-1) → ℚ) := M.mulVecLin
  have hf : ∀ v : Fin r → ℚ, f v = fun m => ∑ i, c m i * v i := by
    intro v
    funext m
    change M.mulVec v m = ∑ i, c m i * v i
    rw [Matrix.mulVec_apply]
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  -- `B` cast to `ℚ` is a nonzero element of the kernel.
  let Bq : Fin r → ℚ := fun i => (B i : ℚ)
  have hBq_ne : Bq ≠ 0 := by
    intro h0
    apply hB
    funext i
    have h1 : Bq i = 0 := by simpa using congr_fun h0 i
    simp only [Bq] at h1
    exact_mod_cast h1
  have hBq_ker : Bq ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, hf]
    funext m
    simpa [Bq] using hcB m
  have hfinrange : Module.finrank ℚ (LinearMap.range f) = r - 1 := by
    change M.rank = r - 1
    exact hrank
  -- Rank-nullity forces the kernel to be one-dimensional.
  have hnull : Module.finrank ℚ (LinearMap.ker f) = 1 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker f
    rw [hfinrange, Module.finrank_fin_fun] at hrn
    have hle : Module.finrank ℚ (LinearMap.ker f) ≤ 1 := by omega
    have hge : 1 ≤ Module.finrank ℚ (LinearMap.ker f) := by
      rw [Submodule.one_le_finrank_iff]
      intro hbot
      rw [hbot] at hBq_ker
      exact hBq_ne (by simpa using hBq_ker)
    omega
  have hker_eq : LinearMap.ker f = ℚ ∙ Bq :=
    eq_span_singleton_of_mem_of_finrank_eq_one hnull hBq_ker hBq_ne
  have hu_ker : u ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, hf]
    funext m
    simpa using hu m
  rw [hker_eq] at hu_ker
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hu_ker
  exact ⟨t, by rw [← ht]; funext i; simp [Bq]⟩

end Work.BW
