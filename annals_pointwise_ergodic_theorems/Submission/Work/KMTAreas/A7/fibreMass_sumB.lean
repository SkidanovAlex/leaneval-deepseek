/-
# The `L¹`-mass bound for the `φ̃`-column of the Leibniz expansion of the §6 symbol

This file proves `fibreMass_sumB`, the `φ̃_N`-half of the Leibniz (product rule) expansion of the
derivative of the §6 fibre symbol `φ_N ⊗ φ̃_N · weylAvg`.  For `i₂ ≤ 2` it asserts

`∑_{b' ≤ i₂} C(i₂,b') · N^{d b'} · ∫ ‖∂^{i₂-b'} φ̃_N‖ ≤ Cψ · λ₂^{1-i₂} · (1 + λ₂ N^d)^{i₂}`,

`d = P.natDegree`, `λ₂ = 2^{dk₂}/2^{d Log N}` the frequency radius of the second bump and `Cψ` the
`L¹`-constant of its derivatives (`FibreMassAux.fibBumpCψ`).  The bound is *sharp*: each integral is
bounded by `Cψ · λ₂^{1-m}` (`FibreMassAux.fibBumpCψ_bound` with `lopsN = λ₂⁻¹`) and the sum over
`b'` is then exactly the binomial expansion of `(1 + λ₂N^d)^{i₂}` times `λ₂^{1-i₂}`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.FibreMassHbdDefs

namespace Work.KMTAreas.A7

open Finset

/-- The `L¹`-bound of `FibreMassAux.fibBumpCψ_bound` for the `m`-th derivative of `φ̃_N`,
rewritten with the frequency radius `λ₂ = lopsN⁻¹` so that it composes with the Leibniz expansion
of the symbol: `∫ ‖∂^m φ̃_N‖ ≤ Cψ · λ₂^{1-m}`, `m ≤ 2`. -/
theorem int_iteratedDeriv_varphitildeN_le (P : Polynomial ℤ) (N k₂ m : ℕ) (hm : m ≤ 2) :
    (∫ η : ℝ, ‖iteratedDeriv m (varphitildeN P.natDegree N k₂) η‖)
      ≤ fibBumpCψ P * (fibLam₂ P N k₂) ^ ((1 : ℤ) - (m : ℤ)) := by
  have hLam : fibLam₂ P N k₂ = (Work.KMTPlan.A6.lopsN P.natDegree N k₂)⁻¹ :=
    fibLam₂_eq_inv P N k₂
  refine (fibBumpCψ_bound P N k₂ m hm).trans (le_of_eq ?_)
  rw [hLam]
  congr 1
  rcases eq_or_ne m 0 with hm0 | hm0
  · subst hm0
    rw [show (((0 : ℕ) : ℝ) - 1) = (-1 : ℝ) by norm_num, Real.rpow_neg_one,
      show (1 : ℤ) - ((0 : ℕ) : ℤ) = (1 : ℤ) by norm_num, zpow_one]
  · have hpos : 0 < m := Nat.pos_of_ne_zero hm0
    rw [show (m : ℝ) - 1 = ((m - 1 : ℕ) : ℝ) by exact (Nat.cast_pred hpos).symm,
      Real.rpow_natCast,
      show (1 : ℤ) - (m : ℤ) = -(((m - 1 : ℕ)) : ℤ) by rw [Nat.cast_pred hpos]; ring]
    rw [zpow_neg, zpow_natCast, inv_pow, inv_inv]

theorem fibreMass_sumB (P : Polynomial ℤ) (N k₂ : ℕ) (i₂ : ℕ) (hi₂ : i₂ ≤ 2) :
    (∑ b' ∈ Finset.range (i₂ + 1), (i₂.choose b' : ℝ) * (N : ℝ) ^ ((P.natDegree : ℤ) * (b' : ℤ))
        * (∫ η : ℝ, ‖iteratedDeriv (i₂ - b') (varphitildeN P.natDegree N k₂) η‖))
      ≤ fibBumpCψ P * (fibLam₂ P N k₂) ^ ((1 : ℤ) - (i₂ : ℤ))
          * (1 + fibLam₂ P N k₂ * (N : ℝ) ^ P.natDegree) ^ i₂ := by
  -- the three abbreviations of the statement
  set la := fibLam₂ P N k₂ with hla
  have hlapos : 0 < la := by rw [hla]; exact fibLam₂_pos P N k₂
  have hlane : la ≠ 0 := ne_of_gt hlapos
  set DD := (N : ℝ) ^ P.natDegree with hDD
  set CA := fibBumpCψ P with hCA
  -- the binomial expansion of `(1 + λ₂ N^d)^{i₂}`
  have hbin : (1 + la * DD) ^ i₂
      = ∑ b' ∈ Finset.range (i₂ + 1), (i₂.choose b' : ℝ) * (la * DD) ^ b' := by
    rw [add_comm 1 (la * DD), add_pow]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [one_pow, mul_one]
    exact mul_comm _ _
  -- the termwise `L¹`-bound
  have hterm : ∀ b' ∈ Finset.range (i₂ + 1),
      (i₂.choose b' : ℝ) * (N : ℝ) ^ ((P.natDegree : ℤ) * (b' : ℤ))
        * (∫ η : ℝ, ‖iteratedDeriv (i₂ - b') (varphitildeN P.natDegree N k₂) η‖)
      ≤ (i₂.choose b' : ℝ) * (N : ℝ) ^ ((P.natDegree : ℤ) * (b' : ℤ))
        * (CA * la ^ ((1 : ℤ) - ((i₂ - b' : ℕ) : ℤ))) := by
    intro b' hb'
    have hb'le : b' ≤ i₂ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb')
    have hm : i₂ - b' ≤ 2 := by omega
    refine mul_le_mul_of_nonneg_left
      (int_iteratedDeriv_varphitildeN_le P N k₂ (i₂ - b') hm) ?_
    have h1 : (0 : ℝ) ≤ (i₂.choose b' : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (N : ℝ) ^ ((P.natDegree : ℤ) * (b' : ℤ)) :=
      zpow_nonneg (Nat.cast_nonneg N) _
    exact mul_nonneg h1 h2
  -- the identification of each term with the corresponding term of the binomial sum
  have htermEq : ∀ b' ∈ Finset.range (i₂ + 1),
      (i₂.choose b' : ℝ) * (N : ℝ) ^ ((P.natDegree : ℤ) * (b' : ℤ))
        * (CA * la ^ ((1 : ℤ) - ((i₂ - b' : ℕ) : ℤ)))
      = (CA * la ^ ((1 : ℤ) - (i₂ : ℤ))) * ((i₂.choose b' : ℝ) * (la * DD) ^ b') := by
    intro b' hb'
    have hb'le : b' ≤ i₂ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb')
    have hkey : (N : ℝ) ^ ((P.natDegree : ℤ) * (b' : ℤ))
          * la ^ ((1 : ℤ) - ((i₂ - b' : ℕ) : ℤ))
        = la ^ ((1 : ℤ) - (i₂ : ℤ)) * (la * DD) ^ b' := by
      have hN : (N : ℝ) ^ ((P.natDegree : ℤ) * (b' : ℤ)) = DD ^ b' := by
        rw [hDD]
        rw [show (P.natDegree : ℤ) * (b' : ℤ) = ((P.natDegree * b' : ℕ) : ℤ) by
          push_cast; ring]
        rw [zpow_natCast, pow_mul]
      have hexp : (1 : ℤ) - ((i₂ - b' : ℕ) : ℤ) = ((1 : ℤ) - (i₂ : ℤ)) + (b' : ℤ) := by
        rw [Nat.cast_sub hb'le]; ring
      have hla' : la ^ ((1 : ℤ) - ((i₂ - b' : ℕ) : ℤ))
          = la ^ ((1 : ℤ) - (i₂ : ℤ)) * la ^ b' := by
        rw [hexp, zpow_add₀ hlane, zpow_natCast]
      rw [hN, hla', mul_pow]
      ring
    calc (i₂.choose b' : ℝ) * (N : ℝ) ^ ((P.natDegree : ℤ) * (b' : ℤ))
            * (CA * la ^ ((1 : ℤ) - ((i₂ - b' : ℕ) : ℤ)))
        = ((i₂.choose b' : ℝ) * CA)
            * ((N : ℝ) ^ ((P.natDegree : ℤ) * (b' : ℤ)) * la ^ ((1 : ℤ) - ((i₂ - b' : ℕ) : ℤ))) := by
          ring
      _ = ((i₂.choose b' : ℝ) * CA)
            * (la ^ ((1 : ℤ) - (i₂ : ℤ)) * (la * DD) ^ b') := by rw [hkey]
      _ = (CA * la ^ ((1 : ℤ) - (i₂ : ℤ))) * ((i₂.choose b' : ℝ) * (la * DD) ^ b') := by
          ring
  calc (∑ b' ∈ Finset.range (i₂ + 1), (i₂.choose b' : ℝ) * (N : ℝ) ^ ((P.natDegree : ℤ) * (b' : ℤ))
          * (∫ η : ℝ, ‖iteratedDeriv (i₂ - b') (varphitildeN P.natDegree N k₂) η‖))
      ≤ ∑ b' ∈ Finset.range (i₂ + 1), (i₂.choose b' : ℝ) * (N : ℝ) ^ ((P.natDegree : ℤ) * (b' : ℤ))
          * (CA * la ^ ((1 : ℤ) - ((i₂ - b' : ℕ) : ℤ))) := Finset.sum_le_sum hterm
    _ = ∑ b' ∈ Finset.range (i₂ + 1),
          (CA * la ^ ((1 : ℤ) - (i₂ : ℤ))) * ((i₂.choose b' : ℝ) * (la * DD) ^ b') :=
        Finset.sum_congr rfl htermEq
    _ = (CA * la ^ ((1 : ℤ) - (i₂ : ℤ)))
          * ∑ b' ∈ Finset.range (i₂ + 1), (i₂.choose b' : ℝ) * (la * DD) ^ b' := by
        rw [Finset.mul_sum]
    _ = (CA * la ^ ((1 : ℤ) - (i₂ : ℤ))) * (1 + la * DD) ^ i₂ := by rw [← hbin]

end Work.KMTAreas.A7
