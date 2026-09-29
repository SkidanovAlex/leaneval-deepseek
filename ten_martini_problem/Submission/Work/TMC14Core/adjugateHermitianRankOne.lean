/-
# Adjugate of a Hermitian matrix with a kernel vector is rank one

If `N` is a Hermitian `n × n` matrix over `ℂ` and `v ≠ 0` is a vector in the kernel of `N`
(as a linear map, `N v = 0`), then

  `adjugate N = c • v v*`

for a suitable scalar `c : ℂ`, where `v v*` is the rank-one matrix `Matrix.vecMulVec v (star v)`.

## Proof

Write `A = adjugate N`.  Since `N v = 0` and `v ≠ 0`, the matrix `N` is singular, so
`det N = 0` and hence `N * A = 0 = A * N`.  Consequently every column of `A` lies in
`ker N`.

If `A = 0` we are done with `c = 0`.  Otherwise some entry of `A` is nonzero, i.e. some
`(n-1) × (n-1)` minor of a row-updated matrix is nonzero, which forces `rank N ≥ n - 1`
(contrapositive of `adjugate_eq_zero_of_rank_le`).  By rank–nullity `ker N` is then
`1`-dimensional, and since it contains the nonzero vector `v` we get `ker N = span v`.
So every column of `A` is a multiple of `v`: `A i j = g j * v i` for some vector `g`.

Finally `A` is Hermitian (adjugate of a Hermitian matrix is Hermitian), so
`g j * v i = conj (g i) * conj (v j)`.  Choosing `i₀` with `v i₀ ≠ 0` gives
`g j = (conj (g i₀) / v i₀) * conj (v j)`, i.e. `A = c • vecMulVec v (star v)` with
`c = conj (g i₀) / v i₀`.
-/
import Mathlib

namespace Work.TMC14Core

open Matrix

/-- Replacing the `j`-th row of a square matrix by an arbitrary vector increases its rank by
at most one. -/
lemma rank_updateRow_le {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) (w : Fin n → ℂ) :
    (N.updateRow j w).rank ≤ N.rank + 1 := by
  have hdecomp : N.updateRow j w = N + vecMulVec (Pi.single j 1) (w - N j) := by
    ext a b
    rw [Matrix.updateRow_apply, Matrix.add_apply, Matrix.vecMulVec_apply]
    by_cases h : a = j
    · subst h; simp
    · simp [h]
  rw [hdecomp]
  set E := vecMulVec (Pi.single j 1) (w - N j) with hE
  have h1 : (N + E).rank ≤ Module.finrank ℂ ↥(N.mulVecLin.range ⊔ E.mulVecLin.range) := by
    rw [Matrix.rank, Matrix.mulVecLin_add]
    exact Submodule.finrank_mono (LinearMap.range_add_le _ _)
  have h2 : Module.finrank ℂ ↥(N.mulVecLin.range ⊔ E.mulVecLin.range) ≤ N.rank + E.rank := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq N.mulVecLin.range E.mulVecLin.range
    simp only [Matrix.rank]
    omega
  have h4 : E.rank ≤ 1 := by rw [hE]; exact Matrix.rank_vecMulVec_le _ _
  omega

/-- If the rank of an `n × n` matrix is at most `n - 2`, then all its `(n-1) × (n-1)` minors
vanish, i.e. its adjugate is zero. -/
lemma adjugate_eq_zero_of_rank_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : M.rank + 2 ≤ n) :
    M.adjugate = 0 := by
  ext i j
  rw [Matrix.adjugate_apply]
  apply Matrix.det_eq_zero_of_not_linearIndependent_rows
  intro hli
  -- `M.updateRow j (Pi.single i 1)` has `n` linearly independent rows, hence rank `n`, but its
  -- rank is at most `M.rank + 1 ≤ n - 1`.
  have hrank0 := LinearIndependent.rank_matrix hli
  simp only [Fintype.card_fin] at hrank0
  have hrank : (M.updateRow j (Pi.single i 1)).rank = n := hrank0
  have hle : (M.updateRow j (Pi.single i 1)).rank ≤ M.rank + 1 :=
    rank_updateRow_le M j (Pi.single i 1)
  omega

theorem adjugateHermitianRankOne {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (hN : N.IsHermitian)
    (v : Fin n → ℂ) (hv : v ≠ 0) (hNv : N.mulVec v = 0) :
    ∃ c : ℂ, N.adjugate = c • Matrix.vecMulVec v (star v) := by
  cases n with
  | zero => exact ⟨0, by rw [Matrix.adjugate_fin_zero, zero_smul]⟩
  | succ m =>
    -- A nonzero coordinate of `v`.
    have hv' : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    obtain ⟨i0, hi0⟩ := hv'
    -- `N` is singular.
    have hdet : N.det = 0 :=
      Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hNv
        (mem_nonZeroDivisors_of_ne_zero hi0)
    have hNA : N * N.adjugate = 0 := by rw [Matrix.mul_adjugate, hdet, zero_smul]
    have hAh : N.adjugate.IsHermitian := hN.adjugate
    by_cases hA0 : N.adjugate = 0
    · exact ⟨0, by rw [hA0, zero_smul]⟩
    -- Every column of `N.adjugate` lies in `ker N`.
    have hvker : v ∈ LinearMap.ker N.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hNv
    have hspan_le : Submodule.span ℂ ({v} : Set (Fin (m + 1) → ℂ)) ≤ LinearMap.ker N.mulVecLin := by
      rw [Submodule.span_le]
      rintro x rfl
      exact hvker
    have hcol : ∀ j, (fun k => N.adjugate k j) ∈ LinearMap.ker N.mulVecLin := by
      intro j
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      have hmv : N *ᵥ (fun k => N.adjugate k j) = (N * N.adjugate) *ᵥ (Pi.single j 1) := by
        rw [show (fun k => N.adjugate k j) = N.adjugate.col j from rfl, ← Matrix.mulVec_mulVec,
          Matrix.mulVec_single_one]
      rw [hmv, hNA, Matrix.zero_mulVec]
    -- `N.adjugate ≠ 0` forces `rank N ≥ n - 1 = m`.
    have hrank : m ≤ N.rank := by
      by_contra hc
      rw [not_le] at hc
      exact hA0 (adjugate_eq_zero_of_rank_le N (by omega))
    -- Rank–nullity, plus `v ∈ ker N`, gives `dim ker N = 1`.
    have hrn := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrn
    have hr : N.rank = Module.finrank ℂ ↥(LinearMap.range N.mulVecLin) := rfl
    rw [← hr] at hrn
    have hkerdim : Module.finrank ℂ ↥(LinearMap.ker N.mulVecLin) = 1 := by
      have hge : 1 ≤ Module.finrank ℂ ↥(LinearMap.ker N.mulVecLin) := by
        calc 1 = Module.finrank ℂ ↥(Submodule.span ℂ ({v} : Set (Fin (m + 1) → ℂ))) :=
              (finrank_span_singleton hv).symm
          _ ≤ Module.finrank ℂ ↥(LinearMap.ker N.mulVecLin) := Submodule.finrank_mono hspan_le
      omega
    have hker : LinearMap.ker N.mulVecLin = Submodule.span ℂ ({v} : Set (Fin (m + 1) → ℂ)) := by
      symm
      apply Submodule.eq_of_le_of_finrank_eq hspan_le
      rw [finrank_span_singleton hv, hkerdim]
    -- Write the columns of `N.adjugate` as multiples of `v`.
    choose g hg using fun j => Submodule.mem_span_singleton.mp (hker ▸ hcol j)
    have hij : ∀ i j, N.adjugate i j = g j * v i := by
      intro i j
      have h := congr_fun (hg j) i
      simp only [Pi.smul_apply, smul_eq_mul] at h
      exact h.symm
    -- Hermiticity of `N.adjugate` pins down `g`.
    have heq : ∀ i j, g j * v i = star (g i) * star (v j) := by
      intro i j
      rw [← hij i j, ← hAh.apply i j, hij j i, star_mul]
      ring
    refine ⟨star (g i0) / v i0, ?_⟩
    have hgj : ∀ j, g j = star (g i0) / v i0 * star (v j) := by
      intro j
      rw [div_mul_eq_mul_div, eq_div_iff hi0]
      exact heq i0 j
    ext i j
    rw [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, hij i j, hgj j, smul_eq_mul]
    ring

end Work.TMC14Core
