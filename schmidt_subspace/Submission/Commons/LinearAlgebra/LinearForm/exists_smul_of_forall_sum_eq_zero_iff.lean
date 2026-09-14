import Mathlib.LinearAlgebra.Dual.Lemmas

namespace Commons.LinearAlgebra.LinearForm

open LinearMap

/-- Two linear forms `x ↦ ∑ i, b i * x i` on `ι → K` (with `ι` finite) have the same zero set
if and only if they are proportional; here we only need the forward direction, assuming the
second form is nonzero. -/
theorem exists_smul_of_forall_sum_eq_zero_iff {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    (b₁ b₂ : ι → K) (h₂ : b₂ ≠ 0)
    (h : ∀ x : ι → K, (∑ i, b₁ i * x i = 0) ↔ (∑ i, b₂ i * x i = 0)) :
    ∃ c : K, b₁ = c • b₂ := by
  classical
  -- `h₂` is not needed for the argument below, but we record it to keep the connection
  -- with the hypothesis: `b₂ ≠ 0`.
  have _hb₂ : b₂ ≠ 0 := h₂
  let l : (ι → K) → (ι → K) →ₗ[K] K := fun b =>
    { toFun := fun x => ∑ i, b i * x i
      map_add' := by
        intro x y
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        congr 1
        ext i
        ring }
  have l_apply : ∀ (b x : ι → K), l b x = ∑ i, b i * x i := fun _ _ => rfl
  have hker : (l b₁).ker = (l b₂).ker := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker, l_apply, l_apply]
    exact h x
  have hmem : l b₁ ∈ Submodule.span K {l b₂} := by
    have hrange : (Set.range (fun _ : Unit => l b₂)) = {l b₂} := Set.range_const
    rw [← hrange]
    apply mem_span_of_iInf_ker_le_ker (ι := Unit) (L := fun _ => l b₂) (K := l b₁)
    rw [iInf_unique]
    rw [hker]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨c, ?_⟩
  funext i
  have hsingle : ∀ (b : ι → K), l b (Pi.single i (1 : K)) = b i := by
    intro b
    rw [l_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have := LinearMap.congr_fun hc (Pi.single i (1 : K))
  rw [LinearMap.smul_apply, hsingle, hsingle] at this
  exact this.symm

end Commons.LinearAlgebra.LinearForm