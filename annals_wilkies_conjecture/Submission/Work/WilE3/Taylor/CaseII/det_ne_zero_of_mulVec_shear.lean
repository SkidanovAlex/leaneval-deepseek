import Mathlib

namespace Work.WilE3.Taylor.CaseII

theorem det_ne_zero_of_mulVec_shear {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (L : (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ)) (i₀ : Fin k) (D : ℝ) (hD : D ≠ 0)
    (hL : Function.Injective L)
    (hrow : ∀ ξ : Fin k → ℝ, A.mulVec ξ = fun i => if i = i₀ then L ξ i₀ else D * L ξ i) :
    A.det ≠ 0 := by
  -- It suffices to show that `A.mulVec` is injective.
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro ξ η hξη
  -- The difference `ξ - η` is killed by `A.mulVec`.
  have hsub : A.mulVec (ξ - η) = 0 := by
    rw [Matrix.mulVec_sub, hξη, sub_self]
  -- Reading off coordinates gives `L (ξ - η) = 0`: at `i₀` directly, elsewhere using `D ≠ 0`.
  have hcoord : ∀ i : Fin k,
      (if i = i₀ then L (ξ - η) i₀ else D * L (ξ - η) i) = 0 := by
    intro i
    have h0 : (A.mulVec (ξ - η)) i = 0 := by rw [hsub]; rfl
    have h := congr_fun (hrow (ξ - η)) i
    rw [h] at h0
    simpa using h0
  have hLzero : L (ξ - η) = 0 := by
    funext i
    by_cases hi : i = i₀
    · rw [hi]
      simpa using hcoord i₀
    · have h := hcoord i
      simp only [ite_eq_right hi] at h
      exact (mul_eq_zero.mp h).resolve_left hD
  -- Injectivity of `L` then gives `ξ = η`.
  have hz : ξ - η = 0 := hL (by rw [hLzero, map_zero])
  exact sub_eq_zero.mp hz

end Work.WilE3.Taylor.CaseII
