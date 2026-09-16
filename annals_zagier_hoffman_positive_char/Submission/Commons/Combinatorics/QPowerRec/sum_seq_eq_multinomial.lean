import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Multinomial

namespace Commons.Combinatorics.QPowerRec

open Polynomial Finset

set_option linter.unusedVariables false

/-- The product of `C (g i) * X ^ (v i)` over `i` is `C (∏ i, g i) * X ^ (∑ i, v i)`. -/
lemma prod_C_mul_X_pow {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (g : ι → R) (v : ι → ℕ) :
    ∏ i, (Polynomial.C (g i) * Polynomial.X ^ (v i))
      = Polynomial.C (∏ i, g i) * Polynomial.X ^ (∑ i, v i) := by
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]

/-- Extract the coefficient of degree `N` of a product of `C`-`X`-monomials. -/
lemma coeff_prod_C_mul_X_pow {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (g : ι → R) (v : ι → ℕ) (N : ℕ) :
    (∏ i, (Polynomial.C (g i) * Polynomial.X ^ (v i))).coeff N
      = if (∑ i, v i) = N then ∏ i, g i else 0 := by
  rw [prod_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
  by_cases h : (∑ i, v i) = N
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun hh => h hh.symm), if_neg h]

/-- Extract the coefficient of degree `N` of a product of powers of `C`-`X`-monomials. -/
lemma coeff_prod_pow_C_mul_X_pow {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (g : ι → R) (v : ι → ℕ) (k : ι → ℕ) (N : ℕ) :
    (∏ i, (Polynomial.C (g i) * Polynomial.X ^ (v i)) ^ (k i)).coeff N
      = if (∑ i, v i * k i) = N then ∏ i, g i ^ (k i) else 0 := by
  have h : ∏ i, (Polynomial.C (g i) * Polynomial.X ^ (v i)) ^ (k i)
      = ∏ i, (Polynomial.C (g i ^ k i) * Polynomial.X ^ (v i * k i)) := by
    apply Finset.prod_congr rfl; intro i _
    rw [mul_pow, ← Polynomial.C_pow, ← pow_mul]
  rw [h, coeff_prod_C_mul_X_pow]

/-- The multinomial theorem, graded by a weight function.

For a finite index type `ι`, a weight function `w : ι → ℕ` with `1 ≤ w i`, and coefficients
`c : ι → R`, the sum over ordered sequences of degree `N` (weighted by `∏ c`) equals the sum over
multiplicity vectors `b : ι → Fin (N+1)` satisfying `∑ i, b i * w i = N`, each counted with the
multinomial coefficient `Nat.multinomial univ b`. -/
theorem sum_pow_weighted_multinomial {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (w : ι → ℕ) (hw : ∀ i, 1 ≤ w i) (c : ι → R) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), ∑ a : Fin m → ι,
      (if (∑ i, w (a i)) = N then ∏ i, c (a i) else 0))
      = ∑ b : {b : ι → Fin (N + 1) // (∑ i, ((b i : ℕ)) * w i) = N},
          ((Nat.multinomial Finset.univ (fun i => ((b.1 i : ℕ))) : ℕ) : R) *
            ∏ i, c i ^ ((b.1 i : ℕ)) := by
  set F : R[X] := ∑ i, Polynomial.C (c i) * Polynomial.X ^ (w i) with hF
  set H : (ι → ℕ) → R := fun k =>
    if (∑ i, k i * w i) = N then ((Nat.multinomial Finset.univ k : ℕ) : R) * ∏ i, c i ^ (k i) else 0
    with hH
  have hA : ∀ m, (F^m).coeff N = ∑ a : Fin m → ι,
      (if (∑ i, w (a i)) = N then ∏ i, c (a i) else 0) := by
    intro m
    have h1 : F^m = ∑ p : Fin m → ι, ∏ i, (Polynomial.C (c (p i)) * Polynomial.X ^ (w (p i))) := by
      rw [hF, Fintype.sum_pow]
    rw [h1, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl; intro p _
    exact coeff_prod_C_mul_X_pow (fun i => c (p i)) (fun i => w (p i)) N
  have hB : ∀ m, (F^m).coeff N = ∑ k ∈ Finset.piAntidiag Finset.univ m, H k := by
    intro m
    have h2 : F^m = ∑ k ∈ Finset.piAntidiag Finset.univ m,
        (↑(Nat.multinomial Finset.univ k) : R[X]) *
          ∏ i ∈ Finset.univ, (Polynomial.C (c i) * Polynomial.X ^ (w i)) ^ (k i) := by
      rw [hF]; exact Finset.sum_pow_eq_sum_piAntidiag Finset.univ
        (fun i => Polynomial.C (c i) * Polynomial.X ^ (w i)) m
    rw [h2, Polynomial.finsetSum_coeff]
    apply Finset.sum_congr rfl; intro k _
    rw [hH]
    have hcast : (↑(Nat.multinomial Finset.univ k) : R[X])
        = Polynomial.C ((Nat.multinomial Finset.univ k : ℕ) : R) := by
      rw [← Polynomial.C_eq_natCast]
    rw [hcast, Polynomial.coeff_C_mul]
    have hprod : (∏ i ∈ Finset.univ, (Polynomial.C (c i) * Polynomial.X ^ (w i)) ^ (k i)).coeff N
        = if (∑ i, w i * k i) = N then ∏ i, c i ^ (k i) else 0 := by
      simpa using coeff_prod_pow_C_mul_X_pow (fun i => c i) (fun i => w i) k N
    rw [hprod]
    rw [show (∑ i, w i * k i) = (∑ i, k i * w i) from Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
    by_cases hC : (∑ i, k i * w i) = N
    · simp [hC]
    · simp [hC]
  have hL : (∑ m ∈ Finset.range (N + 1), ∑ a : Fin m → ι,
        (if (∑ i, w (a i)) = N then ∏ i, c (a i) else 0))
      = ∑ m ∈ Finset.range (N + 1), ∑ k ∈ Finset.piAntidiag Finset.univ m, H k := by
    apply Finset.sum_congr rfl; intro m _
    exact (hA m).symm.trans (hB m)
  set P : Finset (ι → ℕ) := Fintype.piFinset (fun _ : ι => Finset.range (N + 1)) with hP
  set P' : Finset (ι → ℕ) := P.filter (fun k => (∑ i, k i) ≤ N) with hP'
  have hR : (∑ b : {b : ι → Fin (N + 1) // (∑ i, ((b i : ℕ)) * w i) = N},
        ((Nat.multinomial Finset.univ (fun i => ((b.1 i : ℕ))) : ℕ) : R) *
          ∏ i, c i ^ ((b.1 i : ℕ)))
      = ∑ k ∈ P, H k := by
    have step1 : (∑ b : {b : ι → Fin (N + 1) // (∑ i, ((b i : ℕ)) * w i) = N},
          ((Nat.multinomial Finset.univ (fun i => ((b.1 i : ℕ))) : ℕ) : R) *
            ∏ i, c i ^ ((b.1 i : ℕ)))
        = ∑ b : ι → Fin (N + 1),
            (if (∑ i, ((b i : ℕ)) * w i) = N then
              ((Nat.multinomial Finset.univ (fun i => ((b i : ℕ))) : ℕ) : R) *
                ∏ i, c i ^ ((b i : ℕ)) else 0) := by
      have h1 := Finset.sum_subtype
        (F := inferInstance)
        (p := fun b : ι → Fin (N + 1) => (∑ i, ((b i : ℕ)) * w i) = N)
        (s := Finset.univ.filter (fun b : ι → Fin (N + 1) => (∑ i, ((b i : ℕ)) * w i) = N))
        (h := fun b => by simp)
        (f := fun b => ((Nat.multinomial Finset.univ (fun i => ((b i : ℕ))) : ℕ) : R) *
                ∏ i, c i ^ ((b i : ℕ)))
      rw [← h1, Finset.sum_filter]
    rw [step1]
    apply Finset.sum_bij (fun (b : ι → Fin (N + 1)) _ => fun i => ((b i : ℕ)))
    · intro b _
      rw [hP, Fintype.mem_piFinset]; intro i; rw [Finset.mem_range]; exact (b i).2
    · intro b1 _ b2 _ h
      funext i
      apply Fin.ext
      exact congrFun h i
    · intro k hk
      refine ⟨fun i => ⟨k i, ?_⟩, Finset.mem_univ _, ?_⟩
      · rw [hP, Fintype.mem_piFinset] at hk
        have := hk i; rw [Finset.mem_range] at this; exact this
      · rfl
    · intro b _
      rw [hH]
  have hPP : ∑ k ∈ P, H k = ∑ k ∈ P', H k := by
    refine (Finset.sum_subset (s₁ := P') (s₂ := P) (Finset.filter_subset _ _) ?_).symm
    intro x hxP hxP'
    simp only [hH]
    rw [if_neg]
    intro hcon
    have hxN : ¬ ((∑ i, x i) ≤ N) := by
      intro hle; exact hxP' (by rw [hP']; exact Finset.mem_filter.mpr ⟨hxP, hle⟩)
    have hge : N + 1 ≤ ∑ i, x i := by omega
    have hle2 : ∑ i, x i ≤ ∑ i, x i * w i :=
      Finset.sum_le_sum (fun i _ => by
        calc x i = x i * 1 := (mul_one (x i)).symm
          _ ≤ x i * w i := Nat.mul_le_mul_left _ (hw i))
    omega
  have hfiber : ∑ k ∈ P', H k
      = ∑ m ∈ Finset.range (N + 1), ∑ k ∈ P'.filter (fun k => (∑ i, k i) = m), H k := by
    refine (Finset.sum_fiberwise_of_maps_to (s := P') (t := Finset.range (N + 1))
      (g := fun k => ∑ i, k i) ?_ (fun k => H k)).symm
    intro k hk
    rw [Finset.mem_range]
    have := (Finset.mem_filter.mp hk).2
    omega
  have hset : ∀ m ∈ Finset.range (N + 1),
      P'.filter (fun k => (∑ i, k i) = m) = Finset.piAntidiag Finset.univ m := by
    intro m hm
    have hmN : m ≤ N := by rw [Finset.mem_range] at hm; omega
    ext k
    constructor
    · intro hk
      rw [Finset.mem_filter] at hk
      rw [Finset.mem_piAntidiag]
      exact ⟨hk.2, fun i _ => Finset.mem_univ i⟩
    · intro hk
      rw [Finset.mem_piAntidiag] at hk
      rw [Finset.mem_filter]
      refine ⟨?_, hk.1⟩
      rw [hP', Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [hP, Fintype.mem_piFinset]
        intro i
        rw [Finset.mem_range]
        have h1 : k i ≤ Finset.univ.sum k :=
          Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
        rw [hk.1] at h1
        omega
      · rw [hk.1]; exact hmN
  have hsum : ∑ k ∈ P, H k
      = ∑ m ∈ Finset.range (N + 1), ∑ k ∈ Finset.piAntidiag Finset.univ m, H k := by
    rw [hPP, hfiber]
    apply Finset.sum_congr rfl
    intro m hm
    rw [hset m hm]
  exact hL.trans (hsum.symm.trans hR.symm)

theorem sum_seq_eq_multinomial {R : Type*} [CommRing R] (q : ℕ) (hq : 1 ≤ q) (u : ℕ → R)
    (N B : ℕ) (hB : N + 1 ≤ B) :
    (∑ m ∈ Finset.range (N + 1), ∑ a : Fin m → Fin B,
      (if (∑ i, q ^ ((a i : ℕ))) = N then ∏ i, u ((a i : ℕ)) else 0))
      = ∑ b : {b : Fin B → Fin (N + 1) // (∑ i, ((b i : ℕ)) * q ^ (i : ℕ)) = N},
          ((Nat.multinomial Finset.univ (fun i => ((b.1 i : ℕ))) : ℕ) : R) *
            ∏ i : Fin B, u ((i : ℕ)) ^ ((b.1 i : ℕ)) := by
  exact sum_pow_weighted_multinomial (fun i : Fin B => q ^ (i : ℕ))
    (fun i => Nat.one_le_pow _ q (by omega)) (fun i : Fin B => u (i : ℕ)) N

end Commons.Combinatorics.QPowerRec