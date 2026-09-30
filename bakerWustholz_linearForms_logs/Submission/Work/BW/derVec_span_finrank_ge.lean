import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Dimension lower bound for the span of the vectors `b k • c j - b j • c k`.

If `b k ≠ 0`, the family `(b k • c j - b j • c k)_j` spans a space of dimension at least
`finrank (span (range c)) - 1`: indeed `span (range c) ≤ span (range (b k • c · - b · • c k)) ⊔ ℚ ∙ c k`,
and the latter has dimension at most `dim span (range (b k • c · - b · • c k)) + 1`. -/
lemma finrank_span_smul_sub_ge {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℚ E]
    [FiniteDimensional ℚ E] (c : ι → E) (b : ι → ℚ) (k : ι) (hbk : b k ≠ 0) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range c)) - 1 ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range (fun j => b k • c j - b j • c k))) := by
  classical
  have hVC : Submodule.span ℚ (Set.range c) ≤
      Submodule.span ℚ (Set.range (fun j => b k • c j - b j • c k)) ⊔
        Submodule.span ℚ ({c k} : Set E) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hder : b k • c j - b j • c k ∈
        Submodule.span ℚ (Set.range (fun j => b k • c j - b j • c k)) :=
      Submodule.subset_span ⟨j, rfl⟩
    have hck : c k ∈ Submodule.span ℚ ({c k} : Set E) :=
      Submodule.subset_span (Set.mem_singleton _)
    have hmem : (b k)⁻¹ • (b k • c j - b j • c k) ∈
        Submodule.span ℚ (Set.range (fun j => b k • c j - b j • c k)) ⊔
          Submodule.span ℚ ({c k} : Set E) :=
      Submodule.smul_mem _ _ (Submodule.mem_sup_left hder)
    have hmem2 : ((b k)⁻¹ * b j) • c k ∈
        Submodule.span ℚ (Set.range (fun j => b k • c j - b j • c k)) ⊔
          Submodule.span ℚ ({c k} : Set E) :=
      Submodule.smul_mem _ _ (Submodule.mem_sup_right hck)
    have heq : c j = (b k)⁻¹ • (b k • c j - b j • c k) + ((b k)⁻¹ * b j) • c k := by
      rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hbk, one_smul]
      abel
    rw [heq]
    exact add_mem hmem hmem2
  have hC1 : Module.finrank ℚ (Submodule.span ℚ ({c k} : Set E)) ≤ 1 := by
    by_cases hx : c k = 0
    · rw [hx, Submodule.span_zero_singleton, finrank_bot]
      omega
    · rw [finrank_span_singleton hx]
  have hmain : Module.finrank ℚ (Submodule.span ℚ (Set.range c)) ≤
      Module.finrank ℚ (Submodule.span ℚ (Set.range (fun j => b k • c j - b j • c k))) + 1 := by
    have h1 := Submodule.finrank_mono hVC
    have h2 := Submodule.finrank_add_le_finrank_add_finrank
      (Submodule.span ℚ (Set.range (fun j => b k • c j - b j • c k)))
      (Submodule.span ℚ ({c k} : Set E))
    omega
  omega

theorem derVec_span_finrank_ge {n r : ℕ} (L : Fin r → Fin n → ℤ) (b : Fin n → ℤ) (k : Fin n)
    (hL : LinearIndependent ℚ (fun j i => (L j i : ℚ))) (hbk : b k ≠ 0) :
    r - 1 ≤ Module.finrank ℚ
      (Submodule.span ℚ (Set.range (fun j : Fin n => fun i : Fin r => (derVec b k L j i : ℚ)))) := by
  classical
  let M : Matrix (Fin r) (Fin n) ℚ := fun i j => (L i j : ℚ)
  have hcol : Module.finrank ℚ (Submodule.span ℚ (Set.range M.col)) = r := by
    rw [← Matrix.rank_eq_finrank_span_cols M]
    simpa using LinearIndependent.rank_matrix (M := M) (R := ℚ) hL
  have hbkQ : (b k : ℚ) ≠ 0 := by exact_mod_cast hbk
  have h := finrank_span_smul_sub_ge (c := M.col) (b := fun j => (b j : ℚ)) (k := k) hbkQ
  have hpoint : (fun j : Fin n => (b k : ℚ) • M.col j - (b j : ℚ) • M.col k)
      = (fun j : Fin n => fun i : Fin r => (derVec b k L j i : ℚ)) := by
    funext j i
    simp only [Matrix.col_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, derVec]
    push_cast
    ring
  rw [hpoint, hcol] at h
  exact h

end Work.BW
