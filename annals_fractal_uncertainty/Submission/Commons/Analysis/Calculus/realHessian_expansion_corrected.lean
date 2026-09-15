import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Laplacian

namespace Commons.Analysis.Calculus

open scoped Topology

private lemma re_mul_conj (z w : ℂ) : (z * star w).re = z.re * w.re + z.im * w.im := by
  rw [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]; ring

private lemma im_mul_conj (z w : ℂ) : (z * star w).im = z.im * w.re - z.re * w.im := by
  rw [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]; ring

private lemma bilin_apply {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (B : M →ₗ[ℝ] M →ₗ[ℝ] ℝ) (x₁ x₂ y₁ y₂ : M) (c₁ c₂ d₁ d₂ : ℝ) :
    B (c₁ • x₁ + c₂ • x₂) (d₁ • y₁ + d₂ • y₂) =
      c₁ * d₁ * B x₁ y₁ + c₁ * d₂ * B x₁ y₂ + c₂ * d₁ * B x₂ y₁ + c₂ * d₂ * B x₂ y₂ := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

private lemma bilin_sum_sum {ι : Type*} [Fintype ι] {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (B : M →ₗ[ℝ] M →ₗ[ℝ] ℝ) (u v : ι → M) :
    B (∑ i, u i) (∑ j, v j) = ∑ i, ∑ j, B (u i) (v j) := by
  simp only [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]

private lemma w_decomp {d : ℕ} (w : Fin d → ℂ) :
    w = ∑ j, ((w j).re • (Pi.single j (1:ℂ) : Fin d → ℂ) + (w j).im • (Pi.single j Complex.I : Fin d → ℂ)) := by
  funext k
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
    rw [Complex.real_smul, Complex.real_smul, mul_one]
    exact (Complex.re_add_im (w k)).symm
  · intro b _ hb
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero, add_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

private lemma Iw_decomp {d : ℕ} (w : Fin d → ℂ) :
    Complex.I • w = ∑ j, ((-(w j).im) • (Pi.single j (1:ℂ) : Fin d → ℂ) + (w j).re • (Pi.single j Complex.I : Fin d → ℂ)) := by
  funext k
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
    rw [Complex.real_smul, Complex.real_smul, mul_one]
    rw [smul_eq_mul, Complex.I_mul]
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
  · intro b _ hb
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero, add_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

private lemma bilinExpansion {d : ℕ} (B : (Fin d → ℂ) →ₗ[ℝ] (Fin d → ℂ) →ₗ[ℝ] ℝ)
    (w : Fin d → ℂ) :
    B w w + B (Complex.I • w) (Complex.I • w) =
      ∑ j, ∑ k,
        (Complex.re (w j * star (w k)) *
            (B (Pi.single j (1:ℂ)) (Pi.single k (1:ℂ)) +
             B (Pi.single j Complex.I) (Pi.single k Complex.I))
         - Complex.im (w j * star (w k)) *
            (B (Pi.single j (1:ℂ)) (Pi.single k Complex.I) -
             B (Pi.single j Complex.I) (Pi.single k (1:ℂ)))) := by
  have hww : B w w = ∑ j, ∑ k,
      B ((w j).re • (Pi.single j (1:ℂ) : Fin d → ℂ) + (w j).im • (Pi.single j Complex.I : Fin d → ℂ))
        ((w k).re • (Pi.single k (1:ℂ) : Fin d → ℂ) + (w k).im • (Pi.single k Complex.I : Fin d → ℂ)) := by
    conv_lhs => rw [w_decomp w]
    exact bilin_sum_sum B _ _
  have hIwIw : B (Complex.I • w) (Complex.I • w) = ∑ j, ∑ k,
      B ((-(w j).im) • (Pi.single j (1:ℂ) : Fin d → ℂ) + (w j).re • (Pi.single j Complex.I : Fin d → ℂ))
        ((-(w k).im) • (Pi.single k (1:ℂ) : Fin d → ℂ) + (w k).re • (Pi.single k Complex.I : Fin d → ℂ)) := by
    conv_lhs => rw [Iw_decomp w]
    exact bilin_sum_sum B _ _
  rw [hww, hIwIw]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  rw [bilin_apply, bilin_apply, re_mul_conj, im_mul_conj]
  ring

-- Corrected form of the real-Hessian / Hermitian-Hessian identity on `ℂᵈ`.
-- Writing `B = D²φ(z)` and `e j = Pi.single j 1`, `f j = Pi.single j Complex.I`, and
-- `w = Σ_j (a_j • e_j + b_j • f_j)` with `a_j = (w j).re`, `b_j = (w j).im` (so that
-- `Complex.I • w = Σ_j (-b_j • e_j + a_j • f_j)`), bilinearity gives
--   `B w w + B (I•w) (I•w)
--      = Σ_{j,k} [ (a_j a_k + b_j b_k) (B (e_j) (e_k) + B (f_j) (f_k))
--                  + (a_j b_k - b_j a_k) (B (e_j) (f_k) - B (f_j) (e_k)) ]`,
-- while `Re (w_j * star (w_k)) = a_j a_k + b_j b_k` and
-- `Im (w_j * star (w_k)) = b_j a_k - a_j b_k`.  Hence the identity below.  It needs no symmetry
-- of `B`; the version WITHOUT the `Complex.im` term is false (e.g. `d = 2`,
-- `φ z = (z 0).re * (z 1).im`, `z = 0`, `w = ![1, Complex.I]`: left side `2`, right side `0`).
-- Everything reduces to `bilinearIteratedFDerivTwo`, `LinearMap.map_sum`, `LinearMap.map_add`,
-- `LinearMap.map_smul` and `Complex.re_add_im`.
theorem realHessian_expansion_corrected {d : ℕ} (φ : (Fin d → ℂ) → ℝ) (z w : Fin d → ℂ) :
    (iteratedFDeriv ℝ 2 φ z) ![w, w] + (iteratedFDeriv ℝ 2 φ z) ![Complex.I • w, Complex.I • w]
    = ∑ j, ∑ k,
        (Complex.re (w j * star (w k)) *
            ((iteratedFDeriv ℝ 2 φ z) ![Pi.single j (1:ℂ), Pi.single k (1:ℂ)]
             + (iteratedFDeriv ℝ 2 φ z) ![Pi.single j Complex.I, Pi.single k Complex.I])
          - Complex.im (w j * star (w k)) *
            ((iteratedFDeriv ℝ 2 φ z) ![Pi.single j (1:ℂ), Pi.single k Complex.I]
             - (iteratedFDeriv ℝ 2 φ z) ![Pi.single j Complex.I, Pi.single k (1:ℂ)])) := by
  simp only [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  exact bilinExpansion (bilinearIteratedFDerivTwo ℝ φ z) w

end Commons.Analysis.Calculus