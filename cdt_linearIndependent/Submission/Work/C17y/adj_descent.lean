import Mathlib
import Submission.Work.C17.adjoint_defs
import Submission.Work.C17adj.adjoint_base_change

/-!
# Descent of the divisor bound from `ℂ(x)` to `ℚ(x)`

This module is a re-namespaced copy of `Submission/Work/C17adj/divisor_descent.lean` (same proofs,
with every reference to the base-change homomorphism `T` of `Work.C17adj.adjoint_base_change`
qualified).  The copy is needed because the module `Submission.Work.C17adj.adjoint_divisor_boundC`
(required here for the divisor bound over `ℂ`) declares a lemma `eq_sum_fin_seven` in the namespace
`Work.C17adj`, so that the original `divisor_descent` can no longer be imported together with it.

The content: if `γ ∈ ℚ(x)` becomes a polynomial `p ∈ ℂ[x]` under the base change, then `γ` is
already a polynomial, with `γ.num.map = p`; consequently a `ℂ(x)`-factorisation
`toC β · DadjC = Npoly_C` descends to `β · Dadj = Npoly` over `ℚ`.
-/

namespace Work.C17y

open Polynomial

noncomputable section

/-- The base change `ℚ → ℂ` is injective. -/
theorem inj_algebraMap_rat_complex : Function.Injective (algebraMap ℚ ℂ) := by
  intro a b hab
  exact Rat.cast_injective hab

/-- **Descent.**  If the base change of `γ ∈ ℚ(x)` is the polynomial `p ∈ ℂ[X]`, then
`γ = algebraMap γ.num` with `γ.num ∈ ℚ[X]` the image of `p` under the base change. -/
theorem toC_descent (γ : RatFunc ℚ) (p : Polynomial ℂ)
    (h : Work.C17adj.T γ = algebraMap (Polynomial ℂ) (RatFunc ℂ) p) :
    γ = algebraMap (Polynomial ℚ) (RatFunc ℚ) γ.num ∧ γ.num.map (algebraMap ℚ ℂ) = p := by
  have hf : Function.Injective (algebraMap ℚ ℂ) := inj_algebraMap_rat_complex
  have hdne : γ.denom.map (algebraMap ℚ ℂ) ≠ 0 := fun h0 =>
    RatFunc.denom_ne_zero γ (Polynomial.map_injective _ hf (by simpa using h0))
  have key : algebraMap (Polynomial ℂ) (RatFunc ℂ) (γ.num.map (algebraMap ℚ ℂ))
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) p
        * algebraMap (Polynomial ℂ) (RatFunc ℂ) (γ.denom.map (algebraMap ℚ ℂ)) := by
    refine (div_eq_iff (RatFunc.algebraMap_ne_zero hdne)).mp ?_
    rw [← h]
    conv_rhs => rw [← RatFunc.num_div_denom γ]
    rw [map_div₀, Work.C17adj.T_algebraMap, Work.C17adj.T_algebraMap]
  have hND : γ.num.map (algebraMap ℚ ℂ) = p * γ.denom.map (algebraMap ℚ ℂ) := by
    apply RatFunc.algebraMap_injective ℂ
    rw [map_mul]
    exact key
  have hcop : IsCoprime (γ.denom.map (algebraMap ℚ ℂ)) (γ.num.map (algebraMap ℚ ℂ)) := by
    obtain ⟨a, b, hab⟩ := RatFunc.isCoprime_num_denom γ
    refine ⟨b.map (algebraMap ℚ ℂ), a.map (algebraMap ℚ ℂ), ?_⟩
    have h2 := congrArg (Polynomial.map (algebraMap ℚ ℂ)) hab
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one] at h2
    rw [add_comm]
    exact h2
  have hunit : IsUnit (γ.denom.map (algebraMap ℚ ℂ)) :=
    hcop.isUnit_of_dvd ⟨p, by rw [hND, mul_comm]⟩
  have hunitd : IsUnit γ.denom := (Polynomial.isUnit_map (p := γ.denom) (algebraMap ℚ ℂ)).mp hunit
  obtain ⟨r, -, hr⟩ := (Polynomial.isUnit_iff).mp hunitd
  have hr1 : r = 1 := by
    have hmon : (Polynomial.C r).Monic := by rw [hr]; exact RatFunc.monic_denom γ
    simpa [Polynomial.Monic, Polynomial.leadingCoeff_C] using hmon
  have hd1 : γ.denom = 1 := by rw [← hr, hr1, Polynomial.C_1]
  refine ⟨?_, ?_⟩
  · have hnum := RatFunc.num_div_denom γ
    rw [hd1, map_one, div_one] at hnum
    exact hnum.symm
  · rw [hND, hd1, Polynomial.map_one, mul_one]

/-- A polynomial over `ℚ` whose base change is a polynomial of degree `≤ 6` is the `Fin 7`-sum of
its own coefficients. -/
theorem eq_sum_fin_seven (q : Polynomial ℚ) (p : Polynomial ℂ)
    (h : q.map (algebraMap ℚ ℂ) = p) (hp : ∀ m, 7 ≤ m → p.coeff m = 0) :
    q = ∑ k : Fin 7, Polynomial.C (q.coeff k) * Polynomial.X ^ (k : ℕ) := by
  have hf : Function.Injective (algebraMap ℚ ℂ) := inj_algebraMap_rat_complex
  have hqcoeff : ∀ m, 7 ≤ m → q.coeff m = 0 := by
    intro m hm
    have h1 : (q.map (algebraMap ℚ ℂ)).coeff m = 0 := by rw [h]; exact hp m hm
    rw [Polynomial.coeff_map] at h1
    exact hf (by simpa using h1)
  have hnd : q.natDegree ≤ 6 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun N hN => hqcoeff N (by omega))
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow q]
  rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (q.coeff i) * Polynomial.X ^ i) 7]
  refine Finset.sum_subset ?_ ?_
  · rw [Finset.range_subset_range]; omega
  · intro x hx7 hxnot
    simp only [Finset.mem_range] at hx7 hxnot
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < x),
      Polynomial.C_0, zero_mul]

/-- The numerator of `Σ_{k<7} n_k X^k` has vanishing coefficients in degree `≥ 7`. -/
theorem coeff_sum_fin_seven (n : Fin 7 → ℂ) :
    ∀ m, 7 ≤ m → (∑ k : Fin 7, Polynomial.C (n k) * Polynomial.X ^ (k : ℕ)).coeff m = 0 := by
  intro m hm
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Polynomial.coeff_C_mul_X_pow]
  exact if_neg (by have := k.isLt; omega)

/-- **Descent of the divisor bound.** -/
theorem divisor_descent (β : RatFunc ℚ) (n : Fin 7 → ℂ)
    (h : Work.C17.toC β * Work.C17.DadjC
      = ∑ k : Fin 7, algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (n k) * Polynomial.X ^ (k : ℕ))) :
    ∃ n' : Fin 7 → ℚ, β * algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj
      = ∑ k : Fin 7, algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C (n' k) * Polynomial.X ^ (k : ℕ)) := by
  set p : Polynomial ℂ := ∑ k : Fin 7, Polynomial.C (n k) * Polynomial.X ^ (k : ℕ) with hp
  set γ : RatFunc ℚ := β * algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj with hγ
  have hDadj : Work.C17adj.T (algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj)
      = Work.C17.DadjC := by
    rw [Work.C17adj.T_algebraMap]
    rfl
  have hT : Work.C17adj.T γ = algebraMap (Polynomial ℂ) (RatFunc ℂ) p := by
    rw [hγ, map_mul, hDadj, Work.C17adj.T_eq_toC β, hp, map_sum]
    exact h
  obtain ⟨hgamma, hmap⟩ := toC_descent γ p hT
  refine ⟨fun k => γ.num.coeff k, ?_⟩
  conv_lhs => rw [hgamma]
  rw [← map_sum]
  congr 1
  exact eq_sum_fin_seven γ.num p hmap (coeff_sum_fin_seven n)

end

end Work.C17y
