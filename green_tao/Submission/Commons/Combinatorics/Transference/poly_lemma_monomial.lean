import Mathlib
import Submission.Commons.Combinatorics.Transference.poly_lemma

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- Reindexing a product over `Fin (∑ i, a i)` as a product of powers over `Fin K`, using the
standard equivalence `(i : Fin K) × Fin (a i) ≃ Fin (∑ i, a i)`. -/
private lemma prod_fin_sum_pow {K : ℕ} (a : Fin K → ℕ) {M : Type*} [CommMonoid M]
    (g : Fin K → M) :
    (∏ j : Fin (∑ i : Fin K, a i), g ((finSigmaFinEquiv (m := K) (n := a)).symm j).1)
      = ∏ i : Fin K, g i ^ (a i) := by
  rw [Equiv.prod_comp (finSigmaFinEquiv (m := K) (n := a)).symm
        (fun s : (i : Fin K) × Fin (a i) => g s.1)]
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  show (∏ _y : Fin (a i), g i) = g i ^ (a i)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Monomial case of the polynomial lemma (Green–Tao Lemma 6.6).**  The pairing of `f`
with the monomial `∏_i 𝒟F_i^{a i}` is bounded by `‖f‖_{U^d}` times a constant. -/
theorem poly_lemma_monomial {p : ℕ} [Fact p.Prime] {d K : ℕ} (hd : 1 ≤ d) (f : ZMod p → ℝ)
    (F : Fin K → ZMod p → ℝ) (a : Fin K → ℕ) {ν τ : ZMod p → ℝ} (hν : ∀ x, 0 ≤ ν x)
    (hτ : ∀ x, 0 ≤ τ x) (hF : ∀ (j : Fin K) (x : ZMod p), |F j x| ≤ ν x) {Cm : ℝ}
    (hcorr : ∀ h : Fin d → ZMod p,
      (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p,
          ∏ ω : Fin d → Bool, ν (y + ∑ i, (if ω i then h i else 0))
        ≤ ∑ ω : Fin d → Bool, ∑ ω' ∈ Finset.univ.filter (fun ω' => ω ≠ ω'),
            τ ((∑ i, (if ω' i then h i else 0)) - (∑ i, (if ω i then h i else 0))))
    (hmom : (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ y : ZMod p, τ y ^ (∑ i, a i) ≤ Cm) :
    |((Fintype.card (ZMod p) : ℝ))⁻¹ *
        ∑ x : ZMod p, f x * ∏ i : Fin K, (davg d (F i) x) ^ (a i)|
      ≤ Unorm d f * (1 + ((2 ^ d * 2 ^ d : ℕ) : ℝ) ^ (∑ i, a i) * Cm) := by
  classical
  set e := finSigmaFinEquiv (m := K) (n := a) with he
  set F' : Fin (∑ i : Fin K, a i) → ZMod p → ℝ := fun j => F (e.symm j).1 with hF'def
  have hF'maj : ∀ (j : Fin (∑ i : Fin K, a i)) (x : ZMod p), |F' j x| ≤ ν x := by
    intro j x
    rw [hF'def]
    exact hF _ x
  have hprod : ∀ x : ZMod p, (∏ j : Fin (∑ i : Fin K, a i), davg d (F' j) x)
      = ∏ i : Fin K, (davg d (F i) x) ^ (a i) := by
    intro x
    rw [hF'def]
    exact prod_fin_sum_pow a (fun i => davg d (F i) x)
  have hkey := poly_lemma (p := p) (d := d) (K := ∑ i : Fin K, a i) hd f F' hν hτ hF'maj
    hcorr hmom
  have hgoal : (∑ x : ZMod p, f x * ∏ j : Fin (∑ i : Fin K, a i), davg d (F' j) x)
      = ∑ x : ZMod p, f x * ∏ i : Fin K, (davg d (F i) x) ^ (a i) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [hprod x]
  rwa [hgoal] at hkey

end Commons.Combinatorics.Transference
