import Mathlib

/-!
# Separation of the lattice `Q⁻²𝒪_K`

A nonzero algebraic integer `x ∈ 𝓞 K` has algebraic norm a nonzero integer, hence
`|N(x)| ≥ 1`; writing `|N(x)|` as the product of `‖σ x‖` over all `ℚ`-embeddings
`σ : K → ℂ`, some embedding has modulus `≥ 1`.  Consequently the nonzero elements of the
fractional ideal `Q⁻² 𝒪_K` each have some infinite-place norm `≥ 1/Q²`, while every `u` with
`Q² u ∈ 𝓞 K` lies in that ideal.
-/

set_option linter.style.haveILetI false

namespace Work.Lattice

open scoped nonZeroDivisors
open NumberField

/-- A product of nonnegative reals, all `< 1`, over a nonempty finite type is `< 1`. -/
private lemma prod_lt_one_of_forall_lt_one {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i < 1) :
    ∏ i, f i < 1 := by
  classical
  obtain ⟨a⟩ := (inferInstance : Nonempty ι)
  rw [← Finset.prod_erase_mul Finset.univ f (Finset.mem_univ a)]
  have hle : ∏ i ∈ Finset.univ.erase a, f i ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => h0 i) (fun i _ => (h1 i).le)
  calc (∏ i ∈ Finset.univ.erase a, f i) * f a ≤ 1 * f a :=
        mul_le_mul_of_nonneg_right hle (h0 a)
    _ = f a := one_mul _
    _ < 1 := h1 a

/-- A nonzero algebraic integer has a complex embedding of modulus at least `1`: its rational
norm is a nonzero integer, and it is the product of the moduli of its embeddings. -/
private lemma exists_one_le_norm_embedding (K : Type*) [Field K] [NumberField K]
    (x : 𝓞 K) (hx : x ≠ 0) : ∃ σ : K →ₐ[ℚ] ℂ, 1 ≤ ‖σ (x : K)‖ := by
  haveI : Nonempty (K →ₐ[ℚ] ℂ) :=
    ⟨RingHom.equivRatAlgHom K ℂ (Classical.choice (inferInstance : Nonempty (K →+* ℂ)))⟩
  have habs : (1 : ℝ) ≤ |(Algebra.norm ℚ (x : K) : ℝ)| := by
    have hZ : Algebra.norm ℤ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
    have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ x| := Int.one_le_abs hZ
    have h2 : (1 : ℚ) ≤ |Algebra.norm ℚ (x : K)| := by
      rw [← Algebra.coe_norm_int (K := K) x, ← Int.cast_abs]
      exact_mod_cast h1
    exact_mod_cast h2
  have hprod : |(Algebra.norm ℚ (x : K) : ℝ)| = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ (x : K)‖ := by
    have h := congrArg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ (x : K))
    simpa using h
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hlt := prod_lt_one_of_forall_lt_one (fun σ : K →ₐ[ℚ] ℂ => ‖σ (x : K)‖)
    (fun σ => norm_nonneg _) hcon
  rw [← hprod] at hlt
  exact absurd habs (not_le.mpr hlt)

theorem Separation (K : Type*) [Field K] [NumberField K] [NumberField.IsCMField K]
    (Q : ℕ) (hQ : 0 < Q) (U : Finset K)
    (hU : ∀ u ∈ U, ∃ w : 𝓞 K, (w : K) = (Q : K) ^ 2 * u) :
    ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      (∀ u ∈ U, u ∈ (I : Set K)) ∧
      (∀ β ∈ (I : Set K), β ≠ 0 → ∃ w : InfinitePlace K,
        1 / (Q : ℝ) ^ 2 ≤ mixedEmbedding.normAtPlace w (mixedEmbedding K β)) := by
  classical
  have hQK : (Q : K) ≠ 0 := Nat.cast_ne_zero.mpr hQ.ne'
  have hq0 : (Q : K) ^ 2 ≠ 0 := pow_ne_zero 2 hQK
  have hqpos : (0 : ℝ) < (Q : ℝ) ^ 2 := by positivity
  refine ⟨toPrincipalIdeal (𝓞 K) K (Units.mk0 (((Q : K) ^ 2)⁻¹) (inv_ne_zero hq0)), ?_, ?_⟩
  · intro u hu
    obtain ⟨v, hv⟩ := hU u hu
    rw [coe_toPrincipalIdeal]
    refine (FractionalIdeal.mem_coe).mpr ?_
    change u ∈ FractionalIdeal.spanSingleton (𝓞 K)⁰ (((Q : K) ^ 2)⁻¹)
    rw [FractionalIdeal.mem_spanSingleton]
    refine ⟨v, ?_⟩
    rw [Algebra.smul_def]
    change (v : K) * ((Q : K) ^ 2)⁻¹ = u
    rw [hv]
    field_simp
  · intro β hβ hβ0
    rw [coe_toPrincipalIdeal] at hβ
    change β ∈ FractionalIdeal.spanSingleton (𝓞 K)⁰ (((Q : K) ^ 2)⁻¹) at hβ
    rw [FractionalIdeal.mem_spanSingleton] at hβ
    obtain ⟨z, hz⟩ := hβ
    rw [Algebra.smul_def] at hz
    change (z : K) * ((Q : K) ^ 2)⁻¹ = β at hz
    have hzK : (z : K) = (Q : K) ^ 2 * β := by
      calc (z : K) = (z : K) * (((Q : K) ^ 2)⁻¹ * (Q : K) ^ 2) := by
            rw [inv_mul_cancel₀ hq0, mul_one]
        _ = ((z : K) * ((Q : K) ^ 2)⁻¹) * (Q : K) ^ 2 := by ring
        _ = β * (Q : K) ^ 2 := by rw [hz]
        _ = (Q : K) ^ 2 * β := by ring
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hzK
      rw [show ((0 : 𝓞 K) : K) = 0 from rfl] at hzK
      exact hβ0 ((mul_eq_zero.mp hzK.symm).resolve_left hq0)
    obtain ⟨σ, hσ⟩ := exists_one_le_norm_embedding K z hz0
    refine ⟨InfinitePlace.mk σ.toRingHom, ?_⟩
    rw [mixedEmbedding.normAtPlace_apply, InfinitePlace.apply]
    show 1 / (Q : ℝ) ^ 2 ≤ ‖σ β‖
    rw [div_le_iff₀ hqpos]
    have h2 : ‖σ ((Q : K) ^ 2)‖ = (Q : ℝ) ^ 2 := by
      rw [map_pow, map_natCast, norm_pow, Complex.norm_natCast]
    have hkey : ‖σ (z : K)‖ = ‖σ β‖ * (Q : ℝ) ^ 2 := by
      rw [hzK, map_mul, norm_mul, h2]
      ring
    linarith [hσ, hkey]

end Work.Lattice
