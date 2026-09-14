import Mathlib
import Submission.Subspace.ApproxSpace
import Submission.Subspace.Stage3
import Submission.Commons.LinearAlgebra.Matrix.cauchy_binet

/-!
# First steps of the rank descent

The rank descent (Evertse's Theorem B) needs the *successive minima* of the approximation
domain.  Its first analytic input is the lower bound `λ_N ≥ Q^{ε/(2N)}` on the largest
successive minimum, which says that the *scaled* box `λ·Π(Q)` (the box with bounds
`λ Q^{c_i}`) has `ℚ`-rank `< N` for all `λ ≤ Q^{ε/(2N)}`.  Here we prove this from the
already-established rank bound `no_independent_int_points_of_small_domain`: the box with
exponents `c_i + ε/(2N)` (whose exponent sum is `-ε/2 < 0`) has rank `< N` for `Q` large, and
`λ·Π(Q)` is contained in it.

`ε := -∑ i, c i > 0` and `N = Fintype.card σ`.
-/

open scoped BigOperators

namespace Submission.Subspace

variable {σ : Type*} [Fintype σ]

/-- **`λ_N ≥ Q^{ε/(2N)}`.**  For `∑ c i = -ε < 0` and all `λ ≤ Q^{ε/(2N)}` (with `Q` large), the
scaled approximation domain `{y : ‖L i y‖ ≤ λ Q^{c i} ∀ i}` has `ℚ`-rank `< |σ|`. -/
theorem scaled_box_rank_lt (hσ : 2 ≤ Fintype.card σ)
    (L : σ → σ → ℂ) (ind : LinearIndependent ℂ L) (c : σ → ℝ) (hc : ∑ i, c i < 0) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q → ∀ t : ℝ, 0 < t →
      t ≤ Q ^ (-(∑ i, c i) / (2 * (Fintype.card σ : ℝ))) →
      Module.finrank ℚ (Submodule.span ℚ (intCastVec ''
        {y : σ → ℤ | ∀ i, ‖(∑ j, L i j * (y j : ℂ))‖ ≤ t * Q ^ (c i)})) < Fintype.card σ := by
  classical
  haveI : Nonempty σ := Fintype.card_pos_iff.mp (by omega)
  have hNpos : (0 : ℝ) < (Fintype.card σ : ℝ) := by exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty σ›)
  set ε : ℝ := -(∑ i, c i) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  set c' : σ → ℝ := fun i => c i + ε / (2 * (Fintype.card σ : ℝ)) with hc'def
  have hc'sum : ∑ i, c' i = -ε / 2 := by
    rw [hc'def, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card σ : ℝ) ≠ 0 := ne_of_gt hNpos
    field_simp
    ring
  have hc'neg : ∑ i, c' i < 0 := by rw [hc'sum]; linarith
  obtain ⟨Q₁, hQ₁1, hQ₁⟩ := no_independent_int_points_of_small_domain hσ L ind c' hc'neg
  refine ⟨max Q₁ 1, le_max_right _ _, ?_⟩
  intro Q hQ t ht htQ
  have hQ1 : 1 ≤ Q := le_trans (le_max_right _ _) hQ
  have hQpos : 0 < Q := lt_of_lt_of_le one_pos hQ1
  have hQ₁Q : Q₁ ≤ Q := le_trans (le_max_left _ _) hQ
  -- the box with exponents `c'` has rank `< |σ|`
  have hrank' : Module.finrank ℚ (Submodule.span ℚ (intCastVec ''
      {y : σ → ℤ | ∀ i, ‖(∑ j, L i j * (y j : ℂ))‖ ≤ Q ^ (c' i)})) < Fintype.card σ := by
    by_contra hcon
    push_neg at hcon
    have hfr : Module.finrank ℚ (Submodule.span ℚ (intCastVec ''
        {y : σ → ℤ | ∀ i, ‖(∑ j, L i j * (y j : ℂ))‖ ≤ Q ^ (c' i)})) = Fintype.card σ := by
      refine le_antisymm ?_ hcon
      rw [← Module.finrank_fintype_fun_eq_card (R := ℚ) (η := σ)]
      exact Submodule.finrank_le _
    obtain ⟨g, hgbox, hgli⟩ := exists_fin_box_independent (Fintype.card σ)
      {y : σ → ℤ | ∀ i, ‖(∑ j, L i j * (y j : ℂ))‖ ≤ Q ^ (c' i)}
      (Submodule.span ℚ (intCastVec '' {y : σ → ℤ | ∀ i, ‖(∑ j, L i j * (y j : ℂ))‖ ≤ Q ^ (c' i)}))
      Submodule.subset_span rfl hfr
    let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
    refine hQ₁ Q hQ₁Q ⟨fun i j => g (e i) j, ?_, ?_⟩
    · exact hgli.comp e e.injective
    · intro i k
      exact hgbox (e i) k
  -- the scaled box is contained in the box with exponents `c'`
  refine lt_of_le_of_lt (Submodule.finrank_mono ?_) hrank'
  refine Submodule.span_mono (Set.image_mono ?_)
  intro y hy
  intro i
  have h1 : t * Q ^ (c i) ≤ Q ^ (c' i) := by
    have h2 : t ≤ Q ^ (ε / (2 * (Fintype.card σ : ℝ))) := by
      rwa [hεdef] at htQ
    have h3 : Q ^ (ε / (2 * (Fintype.card σ : ℝ))) * Q ^ (c i) = Q ^ (c' i) := by
      rw [hc'def]
      rw [← Real.rpow_add hQpos]
      congr 1
      ring
    calc t * Q ^ (c i) ≤ Q ^ (ε / (2 * (Fintype.card σ : ℝ))) * Q ^ (c i) :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (le_of_lt hQpos) _)
      _ = Q ^ (c' i) := h3
  exact le_trans (hy i) h1

/-! ## The compound matrix (the matrix of `∧^r L` in the standard basis of `∧^r ℚ^N`) -/

/-- Index type of the coordinates of `∧^r (Fin N → ℚ)`: the `r`-element subsets of `Fin N`. -/
abbrev WedgeIdx (N r : ℕ) := {S : Finset (Fin N) // S.card = r}

/-- The `r`-th compound matrix of `A`: its `(T,S)` entry is the minor of `A` with rows `T` and
columns `S` (in increasing order).  This is the matrix of the induced map
`∧^r A : ∧^r (Fin N → ℚ) → ∧^r (Fin N → ℚ)` in the standard bases `e_S = ⋀_{s ∈ S} e_s`. -/
noncomputable def compMat {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) (r : ℕ) :
    Matrix (WedgeIdx N r) (WedgeIdx N r) ℚ :=
  fun T S => (A.submatrix (T.1.orderEmbOfFin T.2) (S.1.orderEmbOfFin S.2)).det

/-- The compound construction is multiplicative (Cauchy–Binet). -/
theorem compMat_mul {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℚ) (r : ℕ) :
    compMat (A * B) r = compMat A r * compMat B r := by
  classical
  ext T S
  rw [compMat, Matrix.mul_apply]
  exact Commons.LinearAlgebra.Matrix.cauchy_binet A B T.1 S.1 T.2 S.2


end Submission.Subspace
