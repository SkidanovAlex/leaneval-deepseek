import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Commons.GeometryOfNumbers.Box.rank_bound_small_body

namespace Commons.GeometryOfNumbers.Box

open Finset Matrix

/-- Hadamard-type bound for complex determinants:
`|det M| ≤ ∑_π ∏_i |M (π i) i|`, from the Leibniz formula. -/
lemma det_norm_le_sum {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    ‖M.det‖ ≤ ∑ σ : Equiv.Perm n, ∏ i, ‖M (σ i) i‖ := by
  rw [Matrix.det_apply']
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
  rw [norm_mul, norm_prod]
  have h1 : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
    rw [Complex.norm_intCast, ← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one]
  rw [h1, one_mul]

theorem rank_bound_small_body_complex {σ : Type*} [Fintype σ] [Nonempty σ]
    (A : (σ → ℂ) →ₗ[ℂ] (σ → ℂ)) (hA : Function.Injective A)
    (c : σ → ℝ) (hc : ∑ i, c i < 0) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
      ¬ ∃ y : σ → (σ → ℤ),
        LinearIndependent ℂ (fun i => (fun j => (y i j : ℂ))) ∧
        ∀ i k, ‖(A (fun j => (y i j : ℂ))) k‖ ≤ Q ^ (c k) := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : Matrix σ σ ℂ, M.mulVec = ⇑A :=
    ⟨LinearMap.toMatrix' A, by funext v; exact LinearMap.toMatrix'_mulVec A v⟩
  have hdetM : M.det ≠ 0 := by
    have hMinj : Function.Injective M.mulVec := by rw [hM]; exact hA
    have hunit : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hMinj
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det M).mp hunit)
  have hA_apply : ∀ (w : σ → ℂ) (k : σ), (A w) k = ∑ j, M k j * w j := by
    intro w k
    have h1 : A w = M.mulVec w := by rw [hM]
    rw [h1]
    simp only [Matrix.mulVec, dotProduct]
  set S : ℝ := ∑ i, c i with hSdef
  have hSneg : S < 0 := by rw [hSdef]; exact hc
  set N : ℝ := (Fintype.card (Equiv.Perm σ) : ℝ) with hNdef
  have hNpos : 0 < N := by
    rw [hNdef]
    have : 0 < Fintype.card (Equiv.Perm σ) := Fintype.card_pos_iff.mpr ⟨1⟩
    exact_mod_cast this
  obtain ⟨Q₀, hQ₀1, hQ₀⟩ :=
    eventually_rpow_mul_lt (δ := ‖M.det‖) hSneg hNpos (norm_pos_iff.mpr hdetM)
  refine ⟨Q₀, hQ₀1, fun Q hQ => ?_⟩
  rintro ⟨y, hyind, hybound⟩
  have hQpos : 0 < Q := lt_of_lt_of_le one_pos (le_trans hQ₀1 hQ)
  set Y : Matrix σ σ ℤ := Matrix.of (fun i j => y i j) with hYdef
  set YC : Matrix σ σ ℂ := (Int.castRingHom ℂ).mapMatrix Y with hYCdef
  set B : Matrix σ σ ℂ := Matrix.of (fun i k => (A (fun j => (y i j : ℂ))) k) with hBdef
  have hyc : ∀ i j, YC i j = (y i j : ℂ) := by
    intro i j; simp [YC, Y, Matrix.map]
  have hYCdet_ne : YC.det ≠ 0 := by
    have hli : LinearIndependent ℂ YC.row := by
      have h : YC.row = fun i => fun j => (y i j : ℂ) := by
        funext i j; simp [YC, Y, Matrix.map]
      rw [h]; exact hyind
    have hunit := Matrix.linearIndependent_rows_iff_isUnit.mp hli
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det YC).mp hunit)
  have hYCdet : YC.det = (Y.det : ℂ) := by
    have hh := (RingHom.map_det (Int.castRingHom ℂ) Y).symm
    simpa [YC] using hh
  have hYdet : Y.det ≠ 0 := by
    intro hz
    exact hYCdet_ne (by rw [hYCdet, hz, Int.cast_zero])
  have hYC_ge : 1 ≤ ‖YC.det‖ := by
    rw [hYCdet, Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hYdet
  have hB_eq : B = YC * Mᵀ := by
    ext i k
    have hBik : B i k = (A (fun j => (y i j : ℂ))) k := rfl
    rw [hBik, hA_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.transpose_apply, hyc]
    ring
  have hdetB : B.det = YC.det * M.det := by
    rw [hB_eq, Matrix.det_mul, Matrix.det_transpose]
  have hlower : ‖M.det‖ ≤ ‖B.det‖ := by
    rw [hdetB, norm_mul]
    calc ‖M.det‖ = 1 * ‖M.det‖ := (one_mul _).symm
      _ ≤ ‖YC.det‖ * ‖M.det‖ := mul_le_mul_of_nonneg_right hYC_ge (norm_nonneg _)
  have hprod : ∏ i, Q ^ (c i) = Q ^ S := by
    have hh := (Real.rpow_sum_of_pos hQpos c Finset.univ).symm
    simpa [hSdef] using hh
  have hhigh : ‖B.det‖ ≤ N * Q ^ S := by
    calc ‖B.det‖ ≤ ∑ σ : Equiv.Perm σ, ∏ i, ‖B (σ i) i‖ := det_norm_le_sum B
      _ ≤ ∑ σ : Equiv.Perm σ, ∏ i, Q ^ (c i) := by
            refine Finset.sum_le_sum (fun s _ => ?_)
            refine Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ?_)
            exact hybound (s i) i
      _ = N * Q ^ S := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hNdef, hprod]
  have hlt : ‖B.det‖ < ‖M.det‖ := lt_of_le_of_lt hhigh (hQ₀ Q hQ)
  exact not_lt_of_ge hlower hlt

end Commons.GeometryOfNumbers.Box