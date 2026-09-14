import Mathlib
import Submission.Subspace.MaxRankFinal
import Submission.Subspace.ApproxSpace

/-!
# Reindexing the maximal-rank finiteness theorem

`Submission.Subspace.maximal_rank_finiteness` is stated for matrices indexed by `Fin (n+1)`.
For the rank descent we need it for the *compound* matrix, whose index type is
`Set.powersetCard (Fin N) r` (a finite type of cardinality `C(N,r)`).  This file transports the
statement to an arbitrary finite index type.

The transport is elementary: reindexing the coordinates by an equivalence `e : ι' ≃ ι` turns
`approxBox L γ Q` into `approxBox (L.submatrix e e) (γ ∘ e) Q`, and consequently `approxSpace` is
carried along the linear equivalence `piEquiv e : (ι → ℚ) ≃ₗ (ι' → ℚ)`, `v ↦ v ∘ e`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Submission.Subspace

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- Reindexing the coordinates: `v ↦ v ∘ e`. -/
noncomputable def piEquiv (e : ι' ≃ ι) : (ι → ℚ) ≃ₗ[ℚ] (ι' → ℚ) where
  toFun v := v ∘ ⇑e
  invFun w := w ∘ ⇑e.symm
  map_add' v w := by funext i; simp [Pi.add_apply, Function.comp_apply]
  map_smul' a v := by funext i; simp [Function.comp_apply]
  left_inv v := by funext i; simp [Function.comp_apply]
  right_inv w := by funext i; simp [Function.comp_apply]

@[simp] lemma piEquiv_apply (e : ι' ≃ ι) (v : ι → ℚ) (i : ι') :
    piEquiv e v i = v (e i) := rfl

/-- Reindexing the box. -/
lemma mem_approxBox_submatrix_equiv (e : ι' ≃ ι) (L : Matrix ι ι ℂ) (γ : ι → ℝ) (Q : ℝ)
    (y : ι' → ℤ) :
    (y ∈ approxBox (L.submatrix e e) (γ ∘ e) Q) ↔ (y ∘ e.symm) ∈ approxBox L γ Q := by
  have hsum : ∀ (i : ι) (y : ι' → ℤ),
      (∑ j : ι', L i (e j) * (y j : ℂ)) = ∑ k : ι, L i k * ((y ∘ e.symm) k : ℂ) := by
    intro i y
    have := Equiv.sum_comp e (fun k : ι => L i k * ((y ∘ e.symm) k : ℂ))
    simpa [Function.comp_apply] using this
  constructor
  · intro h k
    have hk := h (e.symm k)
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply, Function.comp_apply] at hk
    rw [hsum k y] at hk
    exact hk
  · intro h i
    have hk := h (e i)
    simp only [Matrix.submatrix_apply, Function.comp_apply]
    rw [hsum (e i) y]
    exact hk

/-- Reindexing the approximation box, as a set. -/
lemma image_intCastVec_approxBox_submatrix_equiv (e : ι' ≃ ι) (L : Matrix ι ι ℂ)
    (γ : ι → ℝ) (Q : ℝ) :
    (fun v : ι → ℚ => v ∘ ⇑e) '' (intCastVec '' approxBox L γ Q)
      = intCastVec '' approxBox (L.submatrix e e) (γ ∘ e) Q := by
  ext v
  constructor
  · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨y ∘ e, ?_, ?_⟩
    · rw [mem_approxBox_submatrix_equiv e L γ Q (y ∘ ⇑e)]
      have hcomp : (y ∘ ⇑e) ∘ ⇑e.symm = y := by funext i; simp [Function.comp_apply]
      rw [hcomp]
      exact hy
    · funext i
      simp only [intCastVec, Function.comp_apply]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨intCastVec (y ∘ e.symm), ⟨y ∘ e.symm,
      (mem_approxBox_submatrix_equiv e L γ Q y).mp hy, rfl⟩, ?_⟩
    funext i
    simp only [intCastVec, Function.comp_apply]
    rw [Equiv.symm_apply_apply]

/-- **`approxSpace` is carried along the reindexing.** -/
theorem approxSpace_submatrix_equiv (e : ι' ≃ ι) (L : Matrix ι ι ℂ) (γ : ι → ℝ) (Q : ℝ) :
    approxSpace (L.submatrix e e) (γ ∘ e) Q
      = Submodule.map (piEquiv e : (ι → ℚ) →ₗ[ℚ] (ι' → ℚ)) (approxSpace L γ Q) := by
  unfold approxSpace
  rw [Submodule.map_span]
  change Submodule.span ℚ (intCastVec '' approxBox (L.submatrix e e) (γ ∘ e) Q)
      = Submodule.span ℚ ((fun v : ι → ℚ => v ∘ ⇑e) '' (intCastVec '' approxBox L γ Q))
  rw [image_intCastVec_approxBox_submatrix_equiv]

/-- Mapping a submodule and back. -/
lemma map_symm_map (φ : (ι → ℚ) ≃ₗ[ℚ] (ι' → ℚ)) (s : Submodule ℚ (ι → ℚ)) :
    Submodule.map (φ.symm : (ι' → ℚ) →ₗ[ℚ] (ι → ℚ))
      (Submodule.map (φ : (ι → ℚ) →ₗ[ℚ] (ι' → ℚ)) s) = s := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    simpa using hz
  · intro x hx
    exact ⟨φ x, Submodule.mem_map_of_mem hx, by simp⟩

/-- The `ℚ`-dimension is invariant under mapping along a linear equivalence. -/
lemma finrank_map_linearEquiv (φ : (ι → ℚ) ≃ₗ[ℚ] (ι' → ℚ)) (s : Submodule ℚ (ι → ℚ)) :
    Module.finrank ℚ (s.map (φ : (ι → ℚ) →ₗ[ℚ] (ι' → ℚ))) = Module.finrank ℚ s := by
  refine le_antisymm (Submodule.finrank_map_le _ _) ?_
  have h2 := Submodule.finrank_map_le (φ.symm : (ι' → ℚ) →ₗ[ℚ] (ι → ℚ))
    (Submodule.map (φ : (ι → ℚ) →ₗ[ℚ] (ι' → ℚ)) s)
  rwa [map_symm_map φ s] at h2

/-- **The maximal-rank finiteness theorem for an arbitrary finite index type.** -/
theorem maximal_rank_finiteness_reindex [DecidableEq ι] (L : Matrix ι ι ℂ) (hL : L.det ≠ 0)
    (hLa : ∀ i j, IsAlgebraic ℚ (L i j))
    (γ : ι → ℝ) (hγ1 : ∀ i, γ i ≤ 1) (hsum : ∑ i, γ i < 0) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∃ S : Set (Submodule ℚ (ι → ℚ)), S.Finite ∧
      ∀ Q : ℝ, Q₀ ≤ Q → Module.finrank ℚ (approxSpace L γ Q) = Fintype.card ι - 1 →
        approxSpace L γ Q ∈ S := by
  classical
  by_cases hcard : Fintype.card ι ≤ 1
  · refine ⟨1, le_refl 1, {⊥}, Set.finite_singleton _, fun Q _ hfr => ?_⟩
    have h0 : Fintype.card ι - 1 = 0 := by omega
    rw [h0] at hfr
    rw [(Submodule.finrank_eq_zero).mp hfr]
    exact Set.mem_singleton _
  · push_neg at hcard
    have hn : 1 ≤ Fintype.card ι - 1 := by omega
    set e : Fin (Fintype.card ι - 1 + 1) ≃ ι :=
      (finCongr (by omega : Fintype.card ι - 1 + 1 = Fintype.card ι)).trans
        (Fintype.equivFin ι).symm with he
    have hL' : (L.submatrix e e).det ≠ 0 := by
      rw [Matrix.det_submatrix_equiv_self e L]; exact hL
    have hLa' : ∀ i j : Fin (Fintype.card ι - 1 + 1), IsAlgebraic ℚ (L (e i) (e j)) :=
      fun i j => hLa (e i) (e j)
    have hγ'1 : ∀ i : Fin (Fintype.card ι - 1 + 1), (γ ∘ ⇑e) i ≤ 1 := fun i => hγ1 (e i)
    have hsum' : ∑ i : Fin (Fintype.card ι - 1 + 1), (γ ∘ ⇑e) i < 0 := by
      rw [show (∑ i : Fin (Fintype.card ι - 1 + 1), (γ ∘ ⇑e) i) = ∑ i : ι, γ i from
        Equiv.sum_comp e γ]
      exact hsum
    obtain ⟨Q₀, hQ₀1, S', hS'fin, hS'⟩ :=
      maximal_rank_finiteness hn (L.submatrix e e) hL' hLa' (γ ∘ ⇑e) hγ'1 hsum'
    refine ⟨Q₀, hQ₀1,
      (fun V => Submodule.map ((piEquiv e).symm :
        (Fin (Fintype.card ι - 1 + 1) → ℚ) →ₗ[ℚ] (ι → ℚ)) V) '' S', ?_, ?_⟩
    · exact hS'fin.image _
    · intro Q hQ hfr
      have hfr' : Module.finrank ℚ (approxSpace (L.submatrix e e) (γ ∘ ⇑e) Q)
          = Fintype.card ι - 1 := by
        rw [approxSpace_submatrix_equiv, finrank_map_linearEquiv]
        exact hfr
      refine ⟨approxSpace (L.submatrix e e) (γ ∘ ⇑e) Q, hS' Q hQ hfr', ?_⟩
      rw [approxSpace_submatrix_equiv]
      exact map_symm_map (piEquiv e) (approxSpace L γ Q)

end Submission.Subspace
