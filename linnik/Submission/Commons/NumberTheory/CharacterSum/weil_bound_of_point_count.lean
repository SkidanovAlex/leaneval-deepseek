import Mathlib
import Submission.Commons.NumberTheory.Stepanov.not_const_mul_pow_of_irreducible
import Submission.Commons.Analysis.Complex.pow_sum_norm_le_root_sum
import Submission.Commons.NumberTheory.CharacterSum.mulchar_char_sum_power_sums
import Submission.Commons.NumberTheory.CharacterSum.mulchar_char_sum_extension_bound
import Submission.Commons.NumberTheory.Polynomial.ncard_rootSet_algClosure_eq_natDegree_radical

namespace Commons.NumberTheory.CharacterSum

/-- **Weil's bound for multiplicative character sums, from the point-count (Stepanov) bound.**

Assume that the point count on the superelliptic curve `y ^ e = f x` is `≤ #F + C √#F`
uniformly over all finite fields `F` with `e ∣ #F - 1` and all monic `f` of degree `≤ d` whose
curve is irreducible.  Then for every multiplicative character `χ : MulChar F ℂ` of order
exactly `e` and every such `f`,

`‖∑_{x : F} χ (f x)‖ ≤ (#distinct roots of f) · √#F`.

This is the character-sum form of the Weil bound with the sharp coefficient given by the number
of distinct roots of `f` (equivalently, the degree of its squarefree part).  The point-count
hypothesis `hpc` is what the Stepanov/Weil theory over all finite fields provides; the derivation
is the standard "L-function / eigenvalue" argument:

* the `L`-function `∑_{A monic} χ (resultant A f) · u ^ (deg A)` is a polynomial of degree
  `< #distinct roots of f` (orthogonality of `χ` over `F[X]/(radical f)`), whose logarithmic
  derivative has power sums `S n = ∑_{a ∈ F_{q^n}} χ (N_{F_{q^n}/F} (f a))`, so
  `S n = - ∑_j γ_j ^ n` for at most `(#roots - 1)` complex numbers `γ_j`
  (`mulchar_char_sum_power_sums`);
* the Stepanov bound over the extensions gives `‖S n‖ ≤ C √q ^ n` uniformly
  (`mulchar_char_sum_extension_bound`), so each `‖γ_j‖ ≤ √q` (`pow_sum_norm_le_root_sum`);
* then `|S 1| ≤ (#roots) √q` and `S 1 = ∑_{x : F} χ (f x)`. -/
theorem weil_bound_of_point_count (e d : ℕ) (he : 2 ≤ e) (hd : 1 ≤ d)
    (hpc : ∃ C : ℝ, 0 < C ∧ ∀ {F : Type*} [Field F] [Fintype F], e ∣ Fintype.card F - 1 →
      ∀ (f : Polynomial F), f ≠ 0 → f.natDegree ≤ d → f.Monic →
      Irreducible (Polynomial.X ^ e - Polynomial.C f) →
      (({p : F × F | p.2 ^ e = f.eval p.1}.ncard : ℝ) ≤
        (Fintype.card F : ℝ) + C * Real.sqrt ((Fintype.card F : ℕ) : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ {F : Type*} [Field F] [Fintype F], e ∣ Fintype.card F - 1 →
      ∀ (χ : MulChar F ℂ), χ ≠ 1 → orderOf χ = e →
      ∀ (f : Polynomial F), f ≠ 0 → f.natDegree ≤ d → f.Monic →
      Irreducible (Polynomial.X ^ e - Polynomial.C f) →
      ‖∑ x : F, χ (f.eval x)‖ ≤
        ((f.rootSet (AlgebraicClosure F)).ncard : ℝ) * Real.sqrt ((Fintype.card F : ℕ) : ℝ) := by
  obtain ⟨Cb, hCbpos, hCb⟩ := mulchar_char_sum_extension_bound e d he hd
  refine ⟨Cb, hCbpos, ?_⟩
  intro F _ _ hdiv χ hχ hord f hf0 hfdeg hfmon hirr
  haveI : DecidableEq F := Classical.decEq F
  haveI : Fact (Nat.Prime (ringChar F)) := ⟨CharP.char_is_prime F (ringChar F)⟩
  have hnd := Commons.NumberTheory.Stepanov.not_const_mul_pow_of_irreducible e he f hf0 hfmon hirr
  obtain ⟨t, ht, γ, hγ⟩ := mulchar_char_sum_power_sums e he hdiv χ hχ hord f hf0 hfmon hnd
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by
    have : 0 < Fintype.card F := Fintype.card_pos
    exact_mod_cast this
  -- uniform `O(√q ^ n)` bound on the character sums over the degree-`n` extensions
  have hbound : ∀ n : ℕ, 0 < n → ‖∑ j : Fin t, γ j ^ n‖ ≤ Cb * (Real.sqrt (Fintype.card F)) ^ n := by
    intro n hn
    haveI : NeZero n := ⟨Nat.pos_iff_ne_zero.mp hn⟩
    let E := FiniteField.Extension F (ringChar F) n
    haveI : CharP E (ringChar F) :=
      charP_of_injective_ringHom (algebraMap F E).injective (ringChar F)
    haveI hFE : Fintype E := Fintype.ofFinite E
    haveI hDE : DecidableEq E := Classical.decEq E
    have hfin : Module.finrank F E = n := FiniteField.finrank_extension F (ringChar F) n
    have h1 := hγ n (by omega) E hfin
    have h2 := hCb (F := F) hdiv χ hχ hord f hfdeg hnd n (by omega) E hfin
    rw [h1, norm_neg] at h2
    exact h2
  have hroot := Commons.Analysis.Complex.pow_sum_norm_le_root_sum γ hCbpos (Real.sqrt_pos.mpr hqpos) hbound
  -- `S 1 = ∑_x χ (f x)`, computed over the degree-one extension `E₁`
  let E₁ := FiniteField.Extension F (ringChar F) 1
  haveI : CharP E₁ (ringChar F) :=
    charP_of_injective_ringHom (algebraMap F E₁).injective (ringChar F)
  haveI hFE₁ : Fintype E₁ := Fintype.ofFinite E₁
  haveI hDE₁ : DecidableEq E₁ := Classical.decEq E₁
  have hfin₁ : Module.finrank F E₁ = 1 := FiniteField.finrank_extension F (ringChar F) 1
  have hγ₁ := hγ 1 le_rfl E₁ hfin₁
  have hsumE₁ : (∑ a : E₁, χ (Algebra.norm F ((f.map (algebraMap F E₁)).eval a)))
      = ∑ a : F, χ (f.eval a) := by
    have hφ : F ≃ₐ[F] E₁ := FiniteField.algEquivExtension F (ringChar F) 1 F (by
      rw [Module.finrank_self])
    refine (Fintype.sum_equiv hφ.toEquiv (fun a : F => χ (f.eval a))
      (fun b : E₁ => χ (Algebra.norm F ((f.map (algebraMap F E₁)).eval b))) ?_).symm
    intro a
    have h2 : hφ.toEquiv a = algebraMap F E₁ a := by
      simpa using hφ.commutes a
    rw [h2, Polynomial.eval_map, Polynomial.eval₂_at_apply, Algebra.norm_algebraMap, hfin₁,
      pow_one]
  have hsum : ∑ x : F, χ (f.eval x) = - ∑ j : Fin t, γ j := by
    rw [← hsumE₁, hγ₁]
    simp
  have hcard : ((Fintype.card (Fin t) : ℕ) : ℝ) = (t : ℝ) := by simp
  have htr : (t : ℝ) ≤ ((f.rootSet (AlgebraicClosure F)).ncard : ℝ) := by
    have hC := Commons.NumberTheory.Polynomial.ncard_rootSet_algClosure_eq_natDegree_radical f hf0
    rw [hC]; exact_mod_cast ht
  calc ‖∑ x : F, χ (f.eval x)‖
      = ‖∑ j : Fin t, γ j‖ := by rw [hsum, norm_neg]
    _ ≤ (t : ℝ) * Real.sqrt (Fintype.card F) := by
        simpa [hcard] using hroot
    _ ≤ ((f.rootSet (AlgebraicClosure F)).ncard : ℝ) * Real.sqrt ((Fintype.card F : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right htr (Real.sqrt_nonneg _)

end Commons.NumberTheory.CharacterSum
