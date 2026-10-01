import Mathlib
import Submission.Commons.Algebra.Polynomial.eulerProduct_logDeriv_monic
import Submission.Commons.Algebra.Polynomial.exists_powerSums_of_recurrence
import Submission.Commons.Algebra.Polynomial.resultant_eq_norm_adjoinRoot
import Submission.Commons.FieldTheory.Polynomial.radical_deg_pos_of_monic_deg_pos
import Submission.Commons.NumberTheory.CharacterSum.mulchar_char_sum_extension_eq_psi_sum
import Submission.Commons.NumberTheory.CharacterSum.mulchar_sum_monic_resultant_eq_zero

namespace Commons.NumberTheory.CharacterSum

open Polynomial
open Classical
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The L-function of a multiplicative character

For a finite field `F`, a multiplicative character `χ : MulChar F ℂ` and a monic
`f ∈ F[X]`, define the "L-function coefficient weight"
`Ψ_f(A) = χ (-1)^{deg f · deg A} · χ (N_{F[X]/f} (A mod f))`.
On monic `A` this equals `χ (resultant A f)`; it is multiplicative on monic
polynomials with `Ψ_f 1 = 1`, so `Ψ_f` has an Euler product, whose logarithmic
derivative produces a linear recurrence for the power sums
`S_n = ∑_{d ∣ n} d · ∑_{P monic irreducible, deg P = d} Ψ_f(P)^{n/d}`.
The number of distinct "reciprocal roots" is at most `deg (radical f)`, which is
the content of the vanishing lemma `mulchar_sum_monic_resultant_eq_zero`. -/

/-- The monic polynomial `X^m + ∑_{i<m} c i · X^i` of degree `m`. -/
noncomputable def psiPoly (m : ℕ) (c : Fin m → F) : Polynomial F :=
  X ^ m + ∑ i : Fin m, C (c i) * X ^ (i : ℕ)

lemma psiPoly_natDegree (m : ℕ) (c : Fin m → F) : (psiPoly m c).natDegree = m := by
  rw [psiPoly, Polynomial.natDegree_add_eq_left_of_degree_lt]
  · simp
  · rw [Polynomial.degree_X_pow, Polynomial.degree_lt_iff_coeff_zero]
    intro k hk
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro h; exact absurd (h ▸ i.isLt) (not_lt.mpr hk)

lemma psiPoly_monic (m : ℕ) (c : Fin m → F) : (psiPoly m c).Monic := by
  rw [psiPoly]
  refine Polynomial.monic_X_pow_add ?_
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro k hk
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Polynomial.coeff_C_mul_X_pow, if_neg]
  intro h; exact absurd (h ▸ i.isLt) (not_lt.mpr hk)

lemma psiPoly_natDegree' (m : ℕ) (c : Fin m → F) :
    (X ^ m + ∑ i : Fin m, C (c i) * X ^ (i : ℕ) : Polynomial F).natDegree = m :=
  psiPoly_natDegree m c

/-- The `L`-function coefficient weight `Ψ_f(A) = χ (-1)^{deg f · deg A} · χ (N_{F[X]/f} (A))`. -/
noncomputable def psiChar (χ : MulChar F ℂ) (f : Polynomial F) (A : Polynomial F) : ℂ :=
  χ ((-1 : F) ^ (f.natDegree * A.natDegree)) * χ (Algebra.norm F (AdjoinRoot.mk f A))

lemma psiChar_one (χ : MulChar F ℂ) (f : Polynomial F) : psiChar χ f 1 = 1 := by
  rw [psiChar]; simp

lemma psiChar_mul (χ : MulChar F ℂ) (f : Polynomial F) :
    ∀ A B : Polynomial F, A.Monic → B.Monic →
      psiChar χ f (A * B) = psiChar χ f A * psiChar χ f B := by
  intro A B hA hB
  have hAB : (A * B).natDegree = A.natDegree + B.natDegree :=
    Polynomial.natDegree_mul hA.ne_zero hB.ne_zero
  have hnorm : (Algebra.norm F) (AdjoinRoot.mk f (A * B))
      = (Algebra.norm F) (AdjoinRoot.mk f A) * (Algebra.norm F) (AdjoinRoot.mk f B) := by
    rw [map_mul, map_mul]
  rw [psiChar, psiChar, psiChar, hAB, mul_add, pow_add, hnorm]
  simp only [map_mul]
  ring

/-- On every `A` (in particular monic `A`), `Ψ_f(A) = χ (resultant A f)`. -/
lemma psiChar_eq_chi_resultant (χ : MulChar F ℂ) (f : Polynomial F) (hf : f.Monic)
    (A : Polynomial F) : psiChar χ f A = χ (Polynomial.resultant A f) := by
  have h1 : Polynomial.resultant f A = Algebra.norm F (AdjoinRoot.mk f A) :=
    Commons.Algebra.Polynomial.resultant_eq_norm_adjoinRoot f hf A
  have h2 : Polynomial.resultant f A
      = (-1 : F) ^ (f.natDegree * A.natDegree) * Polynomial.resultant A f := by
    rw [Polynomial.resultant_comm]
  have hgg : (-1 : F) ^ (f.natDegree * A.natDegree) * (-1 : F) ^ (f.natDegree * A.natDegree)
      = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have h3 : Polynomial.resultant A f
      = (-1 : F) ^ (f.natDegree * A.natDegree) * Polynomial.resultant f A := by
    conv_rhs => rw [h2]
    rw [← mul_assoc, hgg, one_mul]
  rw [psiChar, ← h1, h3, map_mul]

/-- The `L`-polynomial coefficient `c n = ∑_{A monic, deg A = n} Ψ_f(A)`. -/
noncomputable def psiCcoef (χ : MulChar F ℂ) (f : Polynomial F) (n : ℕ) : ℂ :=
  ∑ c : Fin n → F, psiChar χ f (X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ))

/-- The L-function power sum `S n = ∑_{d ∣ n} d · ∑_{P monic irreducible, deg P = d} Ψ_f(P)^{n/d}`. -/
noncomputable def psiScoef (χ : MulChar F ℂ) (f : Polynomial F) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, (d : ℂ) * ∑ c : Fin d → F,
    if Irreducible (X ^ d + ∑ i : Fin d, C (c i) * X ^ (i : ℕ))
    then (psiChar χ f (X ^ d + ∑ i : Fin d, C (c i) * X ^ (i : ℕ))) ^ (n / d) else 0

/-- The logarithmic derivative of the Euler product, i.e. the linear recurrence relating `c`
and `S`. -/
lemma psiRecurrence (χ : MulChar F ℂ) (f : Polynomial F) (N : ℕ) (hN : 1 ≤ N) :
    ∑ m ∈ Finset.range N, psiCcoef χ f m * psiScoef χ f (N - m)
      = (N : ℂ) * psiCcoef χ f N := by
  have h := Commons.Algebra.Polynomial.eulerProduct_logDeriv_monic (psiChar χ f)
    (psiChar_one χ f) (psiChar_mul χ f) N hN
  simpa only [psiCcoef, psiScoef] using h

/-- The L-polynomial coefficients vanish beyond `deg (radical f)`; equivalently the
L-function is a polynomial of degree `< deg (radical f)`. -/
lemma psiCcoef_eq_zero {e : ℕ} (he : 2 ≤ e) (hdiv : e ∣ Fintype.card F - 1)
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) (hord : orderOf χ = e)
    (f : Polynomial F) (hf : f ≠ 0) (hmon : f.Monic)
    (hnd : ∀ p : ℕ, p.Prime → p ∣ e → ∀ (a : F) (h : Polynomial F),
      f ≠ Polynomial.C a * h ^ p)
    (n : ℕ) (hn : (UniqueFactorizationMonoid.radical f).natDegree ≤ n) :
    psiCcoef χ f n = 0 := by
  rw [psiCcoef]
  rw [Finset.sum_congr rfl (fun c _ => psiChar_eq_chi_resultant χ f hmon
    (X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)))]
  exact mulchar_sum_monic_resultant_eq_zero e he hdiv χ hχ hord f hf hmon hnd n hn

/-- Davenport--Hasse / Weil L-function power sums for a general multiplicative character:
for `e ≥ 2`, `e ∣ #F - 1`, `χ : MulChar F ℂ` of order `e`, `χ ≠ 1`, and `f ∈ F[X]` monic,
nonzero, not a constant multiple of a `p`-th power for any prime `p ∣ e`, the character sums
`S n = ∑_{a : E} χ (Algebra.norm F (f a))` over every degree-`n` extension `E/F` are the power
sums of at most `(radical f).natDegree` complex numbers. -/
theorem mulchar_char_sum_power_sums {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (e : ℕ) (he : 2 ≤ e) (hdiv : e ∣ Fintype.card F - 1)
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) (hord : orderOf χ = e)
    (f : Polynomial F) (hf : f ≠ 0) (hmon : f.Monic)
    (hnd : ∀ p : ℕ, p.Prime → p ∣ e → ∀ (a : F) (h : Polynomial F),
      f ≠ Polynomial.C a * h ^ p) :
    ∃ (t : ℕ) (_ : t ≤ (UniqueFactorizationMonoid.radical f).natDegree) (γ : Fin t → ℂ),
      ∀ (n : ℕ), 1 ≤ n → ∀ (E : Type*) [Field E] [Fintype E] [DecidableEq E] [Algebra F E]
        [Module.Finite F E] [Module.Free F E],
        Module.finrank F E = n →
        ((∑ a : E, χ (Algebra.norm F ((f.map (algebraMap F E)).eval a))) : ℂ)
          = - ∑ j : Fin t, γ j ^ n := by
  classical
  set D := (UniqueFactorizationMonoid.radical f).natDegree with hD
  have hf1 : f ≠ 1 := by
    intro h
    rw [h] at hnd
    obtain ⟨p, hp, hpe⟩ := Nat.exists_prime_and_dvd (by omega : e ≠ 1)
    exact hnd p hp hpe 1 1 (by simp)
  have hdeg1 : 1 ≤ f.natDegree := by
    rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
    · exact absurd ((hmon.natDegree_eq_zero).mp h0) hf1
    · exact hpos
  have hD1 : 1 ≤ D := by
    rw [hD]
    exact Commons.FieldTheory.Polynomial.radical_deg_pos_of_monic_deg_pos f hmon hdeg1
  have hvan : ∀ n, D ≤ n → psiCcoef χ f n = 0 := by
    intro n hn
    refine psiCcoef_eq_zero he hdiv χ hχ hord f hf hmon hnd n ?_
    rw [hD] at hn; exact hn
  set L : Polynomial ℂ := ∑ m ∈ Finset.range D, C (psiCcoef χ f m) * X ^ m with hLdef
  have hL_eq : L = ∑ m ∈ Finset.range D, C (psiCcoef χ f m) * X ^ m := rfl
  have hLcoeff : ∀ m, L.coeff m = psiCcoef χ f m := by
    intro m
    rcases lt_or_ge m D with hm | hm
    · rw [hL_eq, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single m]
      · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
      · intro b _ hb
        rw [Polynomial.coeff_C_mul_X_pow, if_neg]
        intro h; exact hb (by omega)
      · intro h; exact absurd (Finset.mem_range.mpr hm) h
    · rw [hvan m hm, hL_eq, Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero fun b hb => ?_
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      intro h
      exact absurd (Finset.mem_range.mp hb) (by omega)
  have hL0 : L.coeff 0 = 1 := by
    rw [hLcoeff, psiCcoef]
    have huniv : (Finset.univ : Finset (Fin 0 → F)) = {fun i => i.elim0} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      exact ⟨Finset.mem_univ _, fun b _ => by funext i; exact i.elim0⟩
    rw [huniv, Finset.sum_singleton]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, pow_zero]
    exact psiChar_one χ f
  have hS0 : psiScoef χ f 0 = 0 := by
    rw [psiScoef, Nat.divisors_zero, Finset.sum_empty]
  have hrec : ∀ n, 1 ≤ n → ∑ m ∈ Finset.range n, L.coeff m * psiScoef χ f (n - m)
      = (n : ℂ) * L.coeff n := by
    intro n hn
    calc ∑ m ∈ Finset.range n, L.coeff m * psiScoef χ f (n - m)
        = ∑ m ∈ Finset.range n, psiCcoef χ f m * psiScoef χ f (n - m) := by
          refine Finset.sum_congr rfl fun m _ => by rw [hLcoeff]
      _ = (n : ℂ) * psiCcoef χ f n := psiRecurrence χ f n hn
      _ = (n : ℂ) * L.coeff n := by rw [hLcoeff]
  obtain ⟨t, ht, γ, hγ⟩ :=
    Commons.Algebra.Polynomial.exists_powerSums_of_recurrence L hL0 (psiScoef χ f) hS0 hrec
  have hLne : L ≠ 0 := by intro h; rw [h] at hL0; simp at hL0
  have hLdeg : L.natDegree < D := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hLne]
    rw [← Polynomial.mem_degreeLT]
    rw [hL_eq]
    refine Submodule.sum_mem _ (fun m hm => ?_)
    rw [Polynomial.C_mul_X_pow_eq_monomial]
    exact Polynomial.monomial_coe_mem_degreeLT ⟨m, Finset.mem_range.mp hm⟩ _
  refine ⟨t, by omega, γ, ?_⟩
  intro n hn E _ _ _ _ _ _ hnE
  rw [Commons.NumberTheory.CharacterSum.mulchar_char_sum_extension_eq_psi_sum χ f hmon n hnE]
  have hkey : (∑ m ∈ n.divisors, (m : ℂ) * ∑ c : Fin m → F,
        if Irreducible (X ^ m + ∑ i : Fin m, C (c i) * X ^ (i : ℕ))
        then (χ ((-1 : F) ^ (f.natDegree * m)) *
                χ (Algebra.norm F (AdjoinRoot.mk f
                  (X ^ m + ∑ i : Fin m, C (c i) * X ^ (i : ℕ))))) ^ (n / m)
        else 0) = psiScoef χ f n := by
    rw [psiScoef]
    refine Finset.sum_congr rfl fun m hm => ?_
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : Irreducible (X ^ m + ∑ i : Fin m, C (c i) * X ^ (i : ℕ))
    · rw [if_pos hc, if_pos hc]
      congr 1
      rw [psiChar]
      congr 1
      rw [psiPoly_natDegree' m c]
    · rw [if_neg hc, if_neg hc]
  rw [hkey, hγ n hn]

end Commons.NumberTheory.CharacterSum
