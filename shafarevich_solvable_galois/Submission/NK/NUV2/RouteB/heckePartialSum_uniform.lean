import Mathlib
import Submission.NK.HeckeL.Basic
import Submission.NK.HeckeL.Artin
import Submission.NK.NUV2.HeckeLCoeff.heckeCoeff_partial_sum_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Hecke's partial-sum estimate, in the uniform (`∃ θ < 1`) form

If the ideals of a number field are equidistributed in the ray classes of `U` with a power-saving
error `O(X^θ)`, `θ < 1` — the *correct* form of the equidistribution crux, see
`Submission/Work/NUV2/RouteB/CRUX_IS_FALSE_NOTES.md` — then the partial sums of the coefficients
`heckeCoeff` of the Hecke `L`-series of a non-trivial character `χ` are `O(N^θ)`.

This is the form of Hecke's partial-sum estimate that Abel summation
(`NK.NUV2.HeckeLAbel.tendsto_LSeries_of_partial_sum_bound`) consumes: it does not need the sharp
exponent `1 - 1/[K:ℚ]`, which is false for arbitrary `S`.

The proof is the same grouping of the partial sums by norm and then by ray class as in
`NK.NUV2.HeckeLCoeff.heckeCoeff_partial_sum_bound`, with the sharp hypothesis replaced by the
uniform one: since `χ ≠ 1` the sum `∑_c χ(c)` vanishes, so only the *differences* of the class
counts survive, and those are `O(X^θ)` by hypothesis.
-/

set_option autoImplicit false
open NumberField
open scoped BigOperators Classical

namespace NK.NUV2.RouteB

/-- **Hecke's partial-sum bound** (`∃ θ < 1` form) from the uniform equidistribution of ideals
in ray classes. -/
theorem heckePartialSum_of_uniformCount (K : Type) [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K))
    [Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (χ : NK.HeckeL.RayChar K U) (hχ : χ ≠ 1)
    (hC : ∃ (C θ : ℝ), 0 < C ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ c₁ c₂ : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
        |((Nat.card {𝔞 : Ideal (𝓞 K) //
              𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
              NK.HeckeL.classOfIdeal K U 𝔞 = c₁ ∧ Ideal.absNorm 𝔞 ≤ X} : ℝ)
        - (Nat.card {𝔞 : Ideal (𝓞 K) //
              𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
              NK.HeckeL.classOfIdeal K U 𝔞 = c₂ ∧ Ideal.absNorm 𝔞 ≤ X} : ℝ))|
      ≤ C * X ^ θ) :
    ∃ (C' θ' : ℝ), 0 < C' ∧ 0 ≤ θ' ∧ θ' < 1 ∧ ∀ N : ℕ, 1 ≤ N →
      ‖∑ k ∈ Finset.Icc 1 N, NK.HeckeL.heckeCoeff K U S χ k‖ ≤ C' * (N : ℝ) ^ θ' := by
  classical
  letI : Fintype (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) := Fintype.ofFinite _
  obtain ⟨C, θ, hCpos, hθ0, hθ1, hCbd⟩ := hC
  refine ⟨max 1 ((Nat.card (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) : ℝ) * C), θ,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), hθ0, hθ1, fun N hN => ?_⟩
  have hsum : ∑ k ∈ Finset.Icc 1 N, NK.HeckeL.heckeCoeff K U S χ k
      = ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
          (NK.NUV2.HeckeLCoeff.classCount K U S N c : ℂ) * χ.toComplex c := by
    calc ∑ k ∈ Finset.Icc 1 N, NK.HeckeL.heckeCoeff K U S χ k
        = ∑ k ∈ Finset.Icc 1 N, ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
            (NK.NUV2.HeckeLCoeff.fibreClassCount K U S k c : ℂ) * χ.toComplex c := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [NK.NUV2.HeckeLCoeff.heckeCoeff_eq_sum_normFibre K U S χ k,
            NK.NUV2.HeckeLCoeff.sum_normFibre_eq K U S χ k]
      _ = ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
            ∑ k ∈ Finset.Icc 1 N, (NK.NUV2.HeckeLCoeff.fibreClassCount K U S k c : ℂ)
              * χ.toComplex c := Finset.sum_comm
      _ = ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
            (∑ k ∈ Finset.Icc 1 N, (NK.NUV2.HeckeLCoeff.fibreClassCount K U S k c : ℂ))
              * χ.toComplex c := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [← Finset.sum_mul]
      _ = ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
            (NK.NUV2.HeckeLCoeff.classCount K U S N c : ℂ) * χ.toComplex c := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          refine congrArg (fun x : ℂ => x * χ.toComplex c) ?_
          rw [NK.NUV2.HeckeLCoeff.classCount_eq_sum K U S N c, Nat.cast_sum]
  have hzero : ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
      (NK.NUV2.HeckeLCoeff.classCount K U S N 1 : ℂ) * χ.toComplex c = 0 := by
    rw [← Finset.mul_sum, NK.NUV2.HeckeLCoeff.sum_toComplex_eq_zero K U χ hχ, mul_zero]
  have hdiff : ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
        (NK.NUV2.HeckeLCoeff.classCount K U S N c : ℂ) * χ.toComplex c
      = ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
        ((NK.NUV2.HeckeLCoeff.classCount K U S N c : ℂ)
          - (NK.NUV2.HeckeLCoeff.classCount K U S N 1 : ℂ)) * χ.toComplex c := by
    rw [← sub_eq_zero]
    calc (∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
            (NK.NUV2.HeckeLCoeff.classCount K U S N c : ℂ) * χ.toComplex c)
          - ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
            ((NK.NUV2.HeckeLCoeff.classCount K U S N c : ℂ)
              - (NK.NUV2.HeckeLCoeff.classCount K U S N 1 : ℂ)) * χ.toComplex c
        = ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
            ((NK.NUV2.HeckeLCoeff.classCount K U S N c : ℂ) * χ.toComplex c
              - ((NK.NUV2.HeckeLCoeff.classCount K U S N c : ℂ)
                - (NK.NUV2.HeckeLCoeff.classCount K U S N 1 : ℂ)) * χ.toComplex c) :=
          (Finset.sum_sub_distrib _ _).symm
      _ = ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
            (NK.NUV2.HeckeLCoeff.classCount K U S N 1 : ℂ) * χ.toComplex c :=
          Finset.sum_congr rfl (fun c _ => by ring)
      _ = 0 := hzero
  have hbd : ∀ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
      ‖((NK.NUV2.HeckeLCoeff.classCount K U S N c : ℂ)
        - (NK.NUV2.HeckeLCoeff.classCount K U S N 1 : ℂ)) * χ.toComplex c‖
        ≤ C * (N : ℝ) ^ θ := by
    intro c
    have hnorm : ‖((NK.NUV2.HeckeLCoeff.classCount K U S N c : ℂ)
        - (NK.NUV2.HeckeLCoeff.classCount K U S N 1 : ℂ))‖
        = |(NK.NUV2.HeckeLCoeff.classCount K U S N c : ℝ)
          - (NK.NUV2.HeckeLCoeff.classCount K U S N 1 : ℝ)| := by
      have hcast : ((NK.NUV2.HeckeLCoeff.classCount K U S N c : ℂ)
          - (NK.NUV2.HeckeLCoeff.classCount K U S N 1 : ℂ))
          = ((((NK.NUV2.HeckeLCoeff.classCount K U S N c : ℝ)
            - (NK.NUV2.HeckeLCoeff.classCount K U S N 1 : ℝ)) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcast]
      exact RCLike.norm_ofReal _
    rw [norm_mul, NK.HeckeL.RayChar.norm_toComplex_apply_eq_one, mul_one, hnorm]
    have h := hCbd (N : ℝ) (by exact_mod_cast hN) c 1
    rw [← NK.NUV2.HeckeLCoeff.classCount_eq_natCard K U S N c,
      ← NK.NUV2.HeckeLCoeff.classCount_eq_natCard K U S N 1] at h
    exact h
  calc ‖∑ k ∈ Finset.Icc 1 N, NK.HeckeL.heckeCoeff K U S χ k‖
      = ‖∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
          (NK.NUV2.HeckeLCoeff.classCount K U S N c : ℂ) * χ.toComplex c‖ := by rw [hsum]
    _ = ‖∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
          ((NK.NUV2.HeckeLCoeff.classCount K U S N c : ℂ)
            - (NK.NUV2.HeckeLCoeff.classCount K U S N 1 : ℂ)) * χ.toComplex c‖ := by
        rw [hdiff]
    _ ≤ ∑ c : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U, C * (N : ℝ) ^ θ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun c _ => hbd c))
    _ = ((Nat.card (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) : ℝ) * C)
          * (N : ℝ) ^ θ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
        ring
    _ ≤ max 1 ((Nat.card (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) : ℝ) * C)
          * (N : ℝ) ^ θ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg N) _)

end NK.NUV2.RouteB
