/-
# Coefficient extraction for sums of monomials over a finite field

If two finite sums of monomials `∑ i, c i * x ^ (a i)` and `∑ k, d k * x ^ (b k)` agree for every
`x ≠ 0` in a finite field `E`, then the coefficients of each monomial `x ^ e` agree, i.e. the sums
of the `c i` over the `i` with `a i ≡ e (mod |E| - 1)` and similarly for `d`.  This is Lemma 2 c)
of App. VIII of Peterfalvi I, in the form needed for the automorphism computation of `B(n,1,ε)`.
-/
import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

noncomputable section

open Polynomial

namespace Work.Hering.AppVIII


/-- Grouping a sum of monomials by the residue class of the exponent. -/
theorem sum_monomial_group {E : Type*} [Field E] {ι : Type*} [Fintype ι] (N : ℕ) (hpos : 0 < N)
    (hxN : ∀ x : E, x ≠ 0 → x ^ N = 1) (a : ι → ℕ) (γ : ι → E) (x : E) (hx : x ≠ 0) :
    ∑ f ∈ Finset.range N, (∑ i ∈ Finset.univ.filter (fun i => a i % N = f), γ i) * x ^ f
      = ∑ i, γ i * x ^ (a i) := by
  have hxpow : ∀ n : ℕ, x ^ n = x ^ (n % N) := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n N]
    rw [pow_add, pow_mul, hxN x hx, one_pow, one_mul]
  calc ∑ f ∈ Finset.range N, (∑ i ∈ Finset.univ.filter (fun i => a i % N = f), γ i) * x ^ f
      = ∑ f ∈ Finset.range N,
          ∑ i ∈ Finset.univ.filter (fun i => a i % N = f), γ i * x ^ (a i % N) := by
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
    _ = ∑ i, γ i * x ^ (a i % N) :=
        Finset.sum_fiberwise_of_maps_to
          (fun i _ => Finset.mem_range.mpr (Nat.mod_lt (a i) hpos)) _
    _ = ∑ i, γ i * x ^ (a i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hxpow (a i)]

/-- The filter by the residue class `e` modulo `N` is the filter by `% N = e`. -/
theorem filter_modEq_eq_filter_mod {ι : Type*} [Fintype ι] {N e : ℕ} (he : e < N) (s : ι → ℕ) :
    Finset.univ.filter (fun i => s i ≡ e [MOD N]) = Finset.univ.filter (fun i => s i % N = e) := by
  refine Finset.filter_congr fun i _ => ?_
  rw [Nat.ModEq]
  constructor
  · intro hh
    rwa [Nat.mod_eq_of_lt he] at hh
  · intro hh
    rw [hh, Nat.mod_eq_of_lt he]

/-- **Coefficient extraction.**  If `∑ i, c i * x ^ (a i) = ∑ k, d k * x ^ (b k)` for all `x ≠ 0` in
a finite field `E`, then for each exponent residue `e` modulo `|E| - 1` the corresponding
coefficients agree. -/
theorem monomialCoeff {E : Type*} [Field E] [Fintype E] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℕ) (b : κ → ℕ) (c : ι → E) (d : κ → E)
    (h : ∀ x : E, x ≠ 0 → ∑ i, c i * x ^ (a i) = ∑ k, d k * x ^ (b k)) (e : ℕ)
    (he : e < Fintype.card E - 1) :
    ∑ i ∈ Finset.univ.filter (fun i => a i ≡ e [MOD (Fintype.card E - 1)]), c i =
      ∑ k ∈ Finset.univ.filter (fun k => b k ≡ e [MOD (Fintype.card E - 1)]), d k := by
  classical
  set N := Fintype.card E - 1 with hN
  have hpos : 0 < N := by
    have := Fintype.one_lt_card (α := E)
    omega
  have heN : e < N := he
  -- ## monomials only depend on the exponent modulo `N` on `Eˣ`
  have hxN : ∀ x : E, x ≠ 0 → x ^ N = 1 := by
    intro x hx
    rw [hN]
    exact FiniteField.pow_card_sub_one_eq_one x hx
  -- ## the identity, with both sides grouped by residues
  have hmain : ∀ x : E, x ≠ 0 →
      ∑ f ∈ Finset.range N, (∑ i ∈ Finset.univ.filter (fun i => a i % N = f), c i) * x ^ f
        = ∑ f ∈ Finset.range N,
            (∑ k ∈ Finset.univ.filter (fun k => b k % N = f), d k) * x ^ f := by
    intro x hx
    rw [sum_monomial_group N hpos hxN a c x hx, sum_monomial_group N hpos hxN b d x hx]
    exact h x hx
  -- ## the grouped coefficients
  set Ca : ℕ → E := fun f => ∑ i ∈ Finset.univ.filter (fun i => a i % N = f), c i with hCa
  set Cb : ℕ → E := fun f => ∑ k ∈ Finset.univ.filter (fun k => b k % N = f), d k with hCb
  -- ## evaluation of a linear combination of monomials
  have heval : ∀ (s : Finset ℕ) (γ : ℕ → E) (x : E),
      (∑ f ∈ s, C (γ f) * X ^ f : E[X]).eval x = ∑ f ∈ s, γ f * x ^ f := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro γ x; simp
    | insert f s hf ih => intro γ x; simp [Finset.sum_insert hf, ih]
  -- ## the polynomial of differences vanishes on `Eˣ`
  have hroot : ∀ u : Eˣ,
      (∑ f ∈ Finset.range N, C (Ca f - Cb f) * X ^ f : E[X]).eval (u : E) = 0 := by
    intro u
    rw [heval (Finset.range N) (fun f => Ca f - Cb f) (u : E)]
    have hterm : ∀ f ∈ Finset.range N,
        (Ca f - Cb f) * (u : E) ^ f = Ca f * (u : E) ^ f - Cb f * (u : E) ^ f :=
      fun f _ => sub_mul _ _ _
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hmain (u : E) u.ne_zero]
    exact sub_self _
  have hPzero : (∑ f ∈ Finset.range N, C (Ca f - Cb f) * X ^ f : E[X]) = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (∑ f ∈ Finset.range N, C (Ca f - Cb f) * X ^ f)
      (Finset.univ.image (fun u : Eˣ => (u : E))) ?_ ?_
    · intro x hx
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hx
      exact hroot u
    · have hdeg : (∑ f ∈ Finset.range N, C (Ca f - Cb f) * X ^ f : E[X]).natDegree ≤ N - 1 := by
        refine Polynomial.natDegree_sum_le_of_forall_le (s := Finset.range N) (n := N - 1) _
          fun f hf => ?_
        refine (Polynomial.natDegree_C_mul_X_pow_le _ f).trans ?_
        have := Finset.mem_range.mp hf
        omega
      rw [Finset.card_image_of_injective _ (fun u v huv => Units.ext huv), Finset.card_univ]
      rw [show Fintype.card Eˣ = N from by rw [Fintype.card_units, hN]]
      exact lt_of_le_of_lt hdeg (Nat.sub_lt hpos one_pos)
  -- ## coefficient comparison
  have hcoeff : ∀ f < N, Ca f = Cb f := by
    intro f hf
    have hc := congrArg (fun p : E[X] => p.coeff f) hPzero
    simp only [Polynomial.coeff_zero] at hc
    rw [Polynomial.finsetSum_coeff] at hc
    rw [Finset.sum_eq_single f] at hc
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl] at hc
      exact sub_eq_zero.mp hc
    · intro g _ hg
      rw [Polynomial.coeff_C_mul_X_pow, if_neg (fun hcon => hg hcon.symm)]
    · intro hf'
      exact absurd (Finset.mem_range.mpr hf) hf'
  -- ## conclude
  have h1 : Ca e = ∑ i ∈ Finset.univ.filter (fun i => a i ≡ e [MOD N]), c i := by
    rw [hCa, filter_modEq_eq_filter_mod (ι := ι) heN a]
  have h2 : Cb e = ∑ k ∈ Finset.univ.filter (fun k => b k ≡ e [MOD N]), d k := by
    rw [hCb, filter_modEq_eq_filter_mod (ι := κ) heN b]
  rw [← h1, ← h2]
  exact hcoeff e heN

end Work.Hering.AppVIII
