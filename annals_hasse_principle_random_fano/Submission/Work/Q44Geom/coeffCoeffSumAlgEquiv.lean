import Mathlib

namespace Work.Q44Geom

open MvPolynomial

/-- The product-exponent equivalence sends `sumElim α m` to the pair `(α, m)`. -/
private lemma sumFinsupp_sumElim {σ τ : Type*} (α : σ →₀ ℕ) (m : τ →₀ ℕ) :
    Finsupp.sumFinsuppAddEquivProdFinsupp (Finsupp.sumElim α m) = (α, m) := by
  ext <;> simp

/-- The inverse of the product-exponent equivalence on a pair is `sumElim`. -/
private lemma sumElim_eq_symm {σ τ : Type*} (α : σ →₀ ℕ) (m : τ →₀ ℕ) :
    Finsupp.sumFinsuppAddEquivProdFinsupp.symm (α, m) = Finsupp.sumElim α m := by
  ext <;> simp

/-- Characterisation of the fibre of the product-exponent equivalence. -/
private lemma sumFinsupp_eq {σ τ : Type*} (e : σ ⊕ τ →₀ ℕ) (α : σ →₀ ℕ) (m : τ →₀ ℕ) :
    Finsupp.sumFinsuppAddEquivProdFinsupp e = (α, m) ↔ e = Finsupp.sumElim α m := by
  constructor
  · intro h
    have h2 : e = Finsupp.sumFinsuppAddEquivProdFinsupp.symm (α, m) := by
      have h3 := Finsupp.sumFinsuppAddEquivProdFinsupp.symm_apply_apply e
      rw [h] at h3
      exact h3.symm
    rwa [sumElim_eq_symm] at h2
  · intro h
    rw [h, sumFinsupp_sumElim]

/-- Coefficient extraction commutes with an `if` whose `else` branch vanishes. -/
private lemma coeff_ite_zero {τ : Type*} (h : Prop) [Decidable h] (p : MvPolynomial τ ℚ)
    (m : τ →₀ ℕ) :
    ((if h then p else 0 : MvPolynomial τ ℚ).coeff m) = if h then p.coeff m else 0 := by
  by_cases hh : h <;> simp [hh]

/-- `sumAlgEquiv` sends a monomial to the corresponding pair-monomial. -/
private lemma sumAlgEquiv_monomial {σ τ : Type*} (e : σ ⊕ τ →₀ ℕ) (c : ℚ) :
    sumAlgEquiv ℚ σ τ (monomial e c) =
      monomial (Finsupp.sumFinsuppAddEquivProdFinsupp e).1
        (monomial (Finsupp.sumFinsuppAddEquivProdFinsupp e).2 c) := by
  rw [sumAlgEquiv, AlgEquiv.trans_apply]
  simp only [MvPolynomial.monomial, AddMonoidAlgebra.lsingle_apply]
  rw [AddMonoidAlgebra.domCongr_single, AddMonoidAlgebra.curryAlgEquiv_single]

theorem coeffCoeffSumAlgEquiv {σ τ : Type*}
    (q : MvPolynomial (σ ⊕ τ) ℚ) (α : σ →₀ ℕ) (m : τ →₀ ℕ) :
    ((MvPolynomial.sumAlgEquiv ℚ σ τ q).coeff α).coeff m = q.coeff (Finsupp.sumElim α m) := by
  classical
  refine MvPolynomial.induction_on' q ?_ ?_
  · intro e c
    rw [sumAlgEquiv_monomial]
    simp only [MvPolynomial.coeff_monomial]
    rw [coeff_ite_zero]
    simp only [MvPolynomial.coeff_monomial]
    by_cases h1 : (Finsupp.sumFinsuppAddEquivProdFinsupp e).1 = α
    · rw [if_pos h1]
      have hiff : ((Finsupp.sumFinsuppAddEquivProdFinsupp e).2 = m) ↔
          (e = Finsupp.sumElim α m) := by
        constructor
        · intro h2; exact (sumFinsupp_eq e α m).mp (Prod.ext h1 h2)
        · intro h; rw [h, sumFinsupp_sumElim]
      by_cases h2 : (Finsupp.sumFinsuppAddEquivProdFinsupp e).2 = m
      · rw [if_pos h2, if_pos (hiff.mp h2)]
      · rw [if_neg h2, if_neg (fun hh => h2 (hiff.mpr hh))]
    · rw [if_neg h1]
      have : ¬(e = Finsupp.sumElim α m) :=
        fun h => h1 (congrArg Prod.fst ((sumFinsupp_eq e α m).mpr h))
      rw [if_neg this]
  · intro p r hp hr
    simp only [map_add, MvPolynomial.coeff_add, hp, hr]

end Work.Q44Geom
