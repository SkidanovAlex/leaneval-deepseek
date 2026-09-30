import Mathlib
import Submission.Work.BW.RB.finite_extension_domain_height
import Submission.Work.BW.RB.mvpoly_dim_formula


/-!
# Catenarity of the polynomial ring `ℂ[σ]`

For prime ideals `p ≤ q` of `R = MvPolynomial σ ℂ` (with `σ` finite),

  `ht q ≤ ht p + ht (q ⧸ p)`,

the nontrivial direction of the catenary property of a polynomial ring over a field.

The proof uses the dimension formula for finitely generated domains over `ℂ`: for a finitely
generated `ℂ`-domain `D` and a prime `q`, `ht q + dim (D ⧸ q) = dim D`.  Applying it to `A = ℂ[σ]`
at `q` and `p`, and to `A ⧸ p` at `q ⧸ p` (using `(A ⧸ p) ⧸ (q ⧸ p) ≅ A ⧸ q`), then cancelling
`dim (A ⧸ q)` gives `ht q = ht p + ht (q ⧸ p)`.

The dimension formula itself is assembled here from two ingredients:
* `Work.BW.RB.mvpoly_dim_formula` : the formula for the polynomial ring `ℂ[σ]`;
* `Work.BW.RB.finite_extension_domain_height` : the invariance of heights and of the Krull
  dimension under a finite (= integral) injective extension of domains, together with Noether
  normalization (`exists_finite_inj_algHom_of_fg`).
-/

namespace Work.BW.RB

open MvPolynomial

/-- **The dimension formula for a finitely generated domain over `ℂ`.**  For a finitely generated
`ℂ`-domain `D` and a prime ideal `q`, `ht q + dim (D ⧸ q) = dim D`.

By Noether normalization `D` is a finite extension of a polynomial ring `A = ℂ[X₁,…,X_s]`; a
finite injective extension of domains preserves heights of primes and the Krull dimension
(`finite_extension_domain_height`), and the formula holds for the polynomial ring
(`mvpoly_dim_formula`). -/
private theorem fg_domain_dim_formula_self {D : Type*} [CommRing D] [IsDomain D] [Algebra ℂ D]
    [Algebra.FiniteType ℂ D] (q : Ideal D) [q.IsPrime] :
    ((q.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (D ⧸ q) = ringKrullDim D := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ D
  let A := MvPolynomial (Fin s) ℂ
  letI : Algebra A D := g.toRingHom.toAlgebra
  haveI : Module.Finite A D := hfin
  haveI : FaithfulSMul A D := (faithfulSMul_iff_algebraMap_injective A D).mpr hinj
  haveI : IsIntegrallyClosed A := inferInstance
  have key := finite_extension_domain_height (C := A) (S := D)
  have h1 := key.1 q
  have h2 := key.2.1 q
  have h3 := key.2.2
  have h4 := mvpoly_dim_formula (q.under A)
  rw [h1, h2, h4, h3]

/-- If `x : WithBot ℕ∞` is bounded above by a natural number and lies above `⊥`, then it is a
natural number. -/
private lemma exists_natCast_of_le {x : WithBot ℕ∞} {N : ℕ} (hx : x ≤ ((N : ℕ∞) : WithBot ℕ∞))
    (hb : ⊥ < x) : ∃ n : ℕ, x = ((n : ℕ∞) : WithBot ℕ∞) := by
  obtain h | ⟨k, hk⟩ := WithBot.exists.mp (show ∃ y, y = x from ⟨x, rfl⟩)
  · rw [h] at hb; exact absurd hb (lt_irrefl x)
  · have hkne : k ≠ ⊤ := by
      rintro rfl
      rw [← hk] at hx
      exact absurd (WithBot.coe_le_coe.mp hx) (not_le.mpr (ENat.coe_lt_top N))
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hkne
    exact ⟨n, by rw [← hk, ← hn]⟩

/-- **The catenary inequality for the polynomial ring `ℂ[σ]`.** -/
theorem mvPolynomial_catenary {σ : Type*} [Fintype σ]
    {p q : Ideal (MvPolynomial σ ℂ)} [p.IsPrime] [q.IsPrime] (h : p ≤ q) :
    q.height ≤ p.height + (q.map (Ideal.Quotient.mk p)).height := by
  -- The dimension formula for `A = ℂ[σ]`.
  have hA := fg_domain_dim_formula_self (D := MvPolynomial σ ℂ) q
  have hAp := fg_domain_dim_formula_self (D := MvPolynomial σ ℂ) p
  haveI : (q.map (Ideal.Quotient.mk p)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime h
  -- The dimension formula for `A ⧸ p` at the prime `q ⧸ p`.
  have hq := fg_domain_dim_formula_self (D := MvPolynomial σ ℂ ⧸ p) (q.map (Ideal.Quotient.mk p))
  have he : ringKrullDim ((MvPolynomial σ ℂ ⧸ p) ⧸ (q.map (Ideal.Quotient.mk p)))
      = ringKrullDim (MvPolynomial σ ℂ ⧸ q) := by
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup p q), sup_eq_right.mpr h]
  rw [he] at hq
  -- `dim A = card σ`.
  have hdimA : ringKrullDim (MvPolynomial σ ℂ) = ((Fintype.card σ : ℕ∞) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
    simp [Nat.card_eq_fintype_card]
  obtain ⟨nA, hnA⟩ : ∃ n : ℕ, ringKrullDim (MvPolynomial σ ℂ) = ((n : ℕ∞) : WithBot ℕ∞) :=
    ⟨Fintype.card σ, hdimA⟩
  -- The dimensions of the quotients are natural numbers.
  have hDq_le : ringKrullDim (MvPolynomial σ ℂ ⧸ q) ≤ ((Fintype.card σ : ℕ∞) : WithBot ℕ∞) := by
    rw [← hdimA]; exact ringKrullDim_quotient_le q
  have hDq_bot : ⊥ < ringKrullDim (MvPolynomial σ ℂ ⧸ q) := by
    haveI : Nontrivial (MvPolynomial σ ℂ ⧸ q) :=
      Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top' (I := q))
    exact lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞)) ringKrullDim_nonneg_of_nontrivial
  obtain ⟨dq, hdq⟩ := exists_natCast_of_le hDq_le hDq_bot
  have hDp_le : ringKrullDim (MvPolynomial σ ℂ ⧸ p) ≤ ((Fintype.card σ : ℕ∞) : WithBot ℕ∞) := by
    rw [← hdimA]; exact ringKrullDim_quotient_le p
  have hDp_bot : ⊥ < ringKrullDim (MvPolynomial σ ℂ ⧸ p) := by
    haveI : Nontrivial (MvPolynomial σ ℂ ⧸ p) :=
      Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top' (I := p))
    exact lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞)) ringKrullDim_nonneg_of_nontrivial
  obtain ⟨dp, hdp⟩ := exists_natCast_of_le hDp_le hDp_bot
  -- Rewrite everything into `ℕ∞`-valued equalities.
  rw [hdq, hnA] at hA
  rw [hdp, hnA] at hAp
  rw [hdq, hdp] at hq
  have hA' : q.height + (dq : ℕ∞) = (nA : ℕ∞) := by
    rw [← WithBot.coe_add, WithBot.coe_inj] at hA; exact hA
  have hAp' : p.height + (dp : ℕ∞) = (nA : ℕ∞) := by
    rw [← WithBot.coe_add, WithBot.coe_inj] at hAp; exact hAp
  have hq' : (q.map (Ideal.Quotient.mk p)).height + (dq : ℕ∞) = (dp : ℕ∞) := by
    rw [← WithBot.coe_add, WithBot.coe_inj] at hq; exact hq
  have key : q.height + (dq : ℕ∞) = (p.height + (q.map (Ideal.Quotient.mk p)).height)
      + (dq : ℕ∞) := by
    rw [hA', ← hAp', ← hq', add_assoc]
  exact le_of_eq (WithTop.add_right_cancel (ENat.coe_ne_top dq) key)

end Work.BW.RB
