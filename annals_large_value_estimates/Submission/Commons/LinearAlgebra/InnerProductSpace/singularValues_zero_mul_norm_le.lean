import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Module InnerProductSpace
open scoped InnerProductSpace

namespace Commons.LinearAlgebra.InnerProductSpace

theorem re_inner_le_eigenvalues_zero
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (h : 0 < finrank 𝕜 E) (x : E) :
    RCLike.re ⟪T x, x⟫_𝕜 ≤ hT.eigenvalues rfl ⟨0, h⟩ * ‖x‖ ^ 2 := by
  haveI : NeZero (finrank 𝕜 E) := ⟨Nat.pos_iff_ne_zero.mp h⟩
  have hkey : RCLike.re ⟪T x, x⟫_𝕜
      = ∑ i, hT.eigenvalues rfl i * ‖⟪x, hT.eigenvectorBasis rfl i⟫_𝕜‖ ^ 2 := by
    rw [← OrthonormalBasis.sum_inner_mul_inner (hT.eigenvectorBasis rfl) (T x) x, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hT x (hT.eigenvectorBasis rfl i), hT.apply_eigenvectorBasis rfl i, inner_smul_right]
    rw [← RCLike.conj_conj ⟪hT.eigenvectorBasis rfl i, x⟫_𝕜, inner_conj_symm x]
    rw [mul_assoc, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
  rw [hkey]
  conv_rhs => rw [← OrthonormalBasis.sum_sq_norm_inner_left (hT.eigenvectorBasis rfl) x,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone rfl (Fin.zero_le i))
      (by positivity)

theorem singularValues_zero_mul_norm_le
    {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [FiniteDimensional 𝕜 F] (T : E →ₗ[𝕜] F) (x : E) :
    ‖T x‖ ≤ T.singularValues 0 * ‖x‖ := by
  by_cases h : 0 < finrank 𝕜 E
  · have hle := re_inner_le_eigenvalues_zero (T := T.adjoint ∘ₗ T)
      T.isSymmetric_adjoint_comp_self h x
    have hinner : RCLike.re ⟪(T.adjoint ∘ₗ T) x, x⟫_𝕜 = ‖T x‖ ^ 2 := by
      rw [LinearMap.comp_apply, T.adjoint_inner_left, inner_self_eq_norm_sq]
    have hsq : ‖T x‖ ^ 2 ≤ T.singularValues 0 ^ 2 * ‖x‖ ^ 2 := by
      rw [hinner] at hle
      rwa [← T.sq_singularValues_of_lt rfl h] at hle
    have hsq' : ‖T x‖ ^ 2 ≤ (T.singularValues 0 * ‖x‖) ^ 2 := by
      rw [mul_pow]; exact hsq
    exact le_of_sq_le_sq hsq' (mul_nonneg (T.singularValues_nonneg 0) (norm_nonneg x))
  · have h0 : finrank 𝕜 E = 0 := Nat.eq_zero_of_not_pos h
    haveI : Subsingleton E := (Module.finrank_zero_iff).mp h0
    rw [Subsingleton.elim x 0]
    simp

end Commons.LinearAlgebra.InnerProductSpace