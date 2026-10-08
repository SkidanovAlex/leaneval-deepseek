import Mathlib
import Submission.Work.BG.HatInjDefs

namespace Work.BG

open OddOrder.RepresentationTheory

/-! ## Preliminaries for the two-character form of Bender–Glauberman Lemma 1.8

The three ingredients are entirely elementary:

* `isIntegral_star_of_isIntegral` — complex conjugation preserves algebraic integers
  (it is a ring endomorphism of `ℂ`, and `ℤ ↪ ℂ` is fixed by it);
* `not_algIntModTwo_zero_natCast_of_odd` — an *odd* natural number is not `≡ 0 (mod 2)`.
  If `m = 2c` with `c` integral then `c = m/2` is a *rational* algebraic integer, hence an
  integer, forcing `m` even;
* `algIntModTwo_innerSum_of_pointwise` — the pointwise congruence `θ ≡ θ' (mod 2)` propagates
  to the unscaled inner products `Σ_k θ k · conj(θ' k) ≡ Σ_k θ k · conj(θ k) (mod 2)`. -/

/-- The complex conjugate of an algebraic integer is an algebraic integer: conjugation is a ring
endomorphism of `ℂ` fixing the image of `ℤ`. -/
theorem isIntegral_star_of_isIntegral {c : ℂ} (hc : IsIntegral ℤ c) : IsIntegral ℤ (star c) := by
  have h : ((starRingEnd ℂ).comp (algebraMap ℤ ℂ)).IsIntegralElem ((starRingEnd ℂ) c) :=
    RingHom.IsIntegralElem.map hc (starRingEnd ℂ)
  rw [show (starRingEnd ℂ).comp (algebraMap ℤ ℂ) = algebraMap ℤ ℂ from RingHom.ext_int _ _, 
    starRingEnd_apply] at h
  exact h

/-- Values of an irreducible character are algebraic integers. -/
theorem isIntegral_apply_of_irreducible {K : Type*} [Group K] [Finite K]
    {φ : ClassFunction K ℂ} (h : IsIrreducibleCharacter φ) (g : K) : IsIntegral ℤ (φ g) := by
  obtain ⟨V, _, _, _, ρ, _, hchar⟩ := h
  rw [congrFun hchar g]
  exact OddOrder.RepresentationTheory.character_isIntegral ρ g

/-- **An odd natural number is not `≡ 0 (mod 2)`** in the sense of `AlgIntModTwo`:
if `m = 2c` with `c` an algebraic integer, then `c = m/2` is a rational algebraic integer,
hence an integer, so `m` is even. -/
theorem not_algIntModTwo_zero_natCast_of_odd {m : ℕ} (hm : Odd m) :
    ¬ AlgIntModTwo (0 : ℂ) (m : ℂ) := by
  rintro ⟨c, hc, hc0⟩
  have h2 : (m : ℂ) = 2 * (-c) := by linear_combination -hc0
  have hc' : IsIntegral ℤ (-c) := hc.neg
  have hq : (-c : ℂ) = (((m : ℚ) / 2 : ℚ) : ℂ) := by
    rw [show (-c : ℂ) = (m : ℂ) / 2 by rw [h2]; ring]
    push_cast
    ring
  have hqint : IsIntegral ℤ ((m : ℚ) / 2) := IsIntegral.ratCast_iff.mp (hq ▸ hc')
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hqint
  have hz : (2 * y : ℤ) = (m : ℤ) := by
    have hcast : ((2 * y : ℤ) : ℚ) = (m : ℚ) := by
      push_cast
      linear_combination 2 * hy
    exact_mod_cast hcast
  obtain ⟨n, hn⟩ := hm
  omega

/-- Pointwise `θ ≡ θ' (mod 2)` implies the congruence of the **unscaled** inner products
`Σ_k θ k · conj(θ' k) ≡ Σ_k θ k · conj(θ k) (mod 2)`.

Indeed, writing `θ k - θ' k = 2 c k` with `c k` integral,
`Σ_k θ k · conj(θ' k) - Σ_k θ k · conj(θ k) = Σ_k θ k · conj(θ' k - θ k)
= -2 Σ_k θ k · conj(c k)`, and each `θ k · conj(c k)` is an algebraic integer. -/
theorem algIntModTwo_innerSum_of_pointwise {K : Type} [Group K] [Fintype K]
    {θ θ' : ClassFunction K ℂ} (hθ : IsIrreducibleCharacter θ)
    (hcong : ∀ k : K, AlgIntModTwo (θ k) (θ' k)) :
    AlgIntModTwo (ClassFunction.innerSum θ θ') (ClassFunction.innerSum θ θ) := by
  classical
  choose c hcint hceq using hcong
  have hpt : ∀ k : K, θ k * star (θ' k) - θ k * star (θ k) = -(2 * (θ k * star (c k))) := by
    intro k
    have hstar : star (θ' k) - star (θ k) = -(2 * star (c k)) := by
      have h : star (θ' k - θ k) = -(2 * star (c k)) := by
        rw [show θ' k - θ k = -(2 * c k) by linear_combination -(hceq k)]
        simp
      rwa [star_sub] at h
    calc θ k * star (θ' k) - θ k * star (θ k)
        = θ k * (star (θ' k) - star (θ k)) := by ring
      _ = θ k * (-(2 * star (c k))) := by rw [hstar]
      _ = -(2 * (θ k * star (c k))) := by ring
  refine ⟨-(∑ k : K, θ k * star (c k)), ?_, ?_⟩
  · exact (IsIntegral.sum _ (fun k _ => (isIntegral_apply_of_irreducible hθ k).mul
      (isIntegral_star_of_isIntegral (hcint k)))).neg
  · rw [ClassFunction.innerSum, ClassFunction.innerSum, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_neg_distrib, mul_neg, Finset.mul_sum]

open OddOrder.RepresentationTheory in
/-- Two irreducible characters of a finite group of **odd order** which agree modulo `2` at every
element are equal (Bender–Glauberman Lemma 1.8, two-character form).

Route: from `θ - θ' = 2φ` with `φ` integral-valued, the (unnormalised) inner products
`Σ_k θ k · conj (θ' k)` and `Σ_k θ k · conj (θ k) = |K|` are congruent modulo `2`; since `|K|` is odd
and `(θ, θ') ∈ {0,1}` (orthonormality), the congruence gives `(θ,θ') = 1`, i.e. `θ = θ'`. -/
theorem hatInjCongruentEq {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] (hK : Odd (Nat.card K))
    {θ θ' : ClassFunction K ℂ} (hθ : IsIrreducibleCharacter θ) (hθ' : IsIrreducibleCharacter θ')
    (hcong : ∀ k : K, Work.BG.AlgIntModTwo (θ k) (θ' k)) : θ = θ' := by
  by_contra hne
  -- the congruence of the unscaled inner products
  have hsum := algIntModTwo_innerSum_of_pointwise hθ hcong
  -- multiply by `|K|` to pass from `innerSum` to the normalised inner product
  have hmul : AlgIntModTwo ((Nat.card K : ℂ) * ClassFunction.inner θ θ')
      ((Nat.card K : ℂ) * ClassFunction.inner θ θ) := by
    rw [ClassFunction.card_mul_inner, ClassFunction.card_mul_inner]
    exact hsum
  -- orthonormality: `(θ,θ) = 1` and, since `θ ≠ θ'`, `(θ,θ') = 0`
  have h1 : ClassFunction.inner θ θ = 1 := by
    have := irreducibleCharacter_inner_eq_ite (⟨θ, hθ⟩ : IrreducibleCharacter K) ⟨θ, hθ⟩
    simpa using this
  have h2 : ClassFunction.inner θ θ' = 0 := by
    have := irreducibleCharacter_inner_eq_ite (⟨θ, hθ⟩ : IrreducibleCharacter K) ⟨θ', hθ'⟩
    rw [ite_eq_right (by intro hh; exact hne (Subtype.ext_iff.mp hh))] at this
    simpa using this
  rw [h1, h2, mul_zero, mul_one] at hmul
  -- `0 ≡ |K| (mod 2)` contradicts `|K|` odd
  exact not_algIntModTwo_zero_natCast_of_odd hK hmul

end Work.BG
