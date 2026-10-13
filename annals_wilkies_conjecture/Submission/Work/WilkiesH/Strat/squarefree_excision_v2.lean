import Mathlib
import Submission.Work.WilkiesH.Tarski.definable_iff_polynomialSignSet
import Submission.Work.WilkiesH.Strat.exists_poly_data
import Submission.Work.WilkiesH.Strat.squarefree_root_lemma

set_option autoImplicit false
noncomputable section

namespace Work.WilkiesH.Strat

open Polynomial

/-! ## Reindexing `Fin μ ⊕ Fin 1` as `Option (Fin μ)` -/

/-- The bijection `Fin μ ⊕ Fin 1 ≃ Option (Fin μ)` sending `Sum.inl i` to `some i` and the unique
element of `Fin 1` to `none`. -/
def sumOptionEquiv (μ : ℕ) : Fin μ ⊕ Fin 1 ≃ Option (Fin μ) where
  toFun o := match o with
    | Sum.inl i => some i
    | Sum.inr _ => none
  invFun o := match o with
    | none => Sum.inr 0
    | some i => Sum.inl i
  left_inv o := by
    rcases o with i | j
    · rfl
    · rw [Sum.inr.injEq]; exact Subsingleton.elim _ _
  right_inv o := by
    rcases o with _ | i <;> rfl

/-- `ℝ[x_1,…,x_μ,t]` as the polynomial ring in `t` over `ℝ[x_1,…,x_μ]`; the variable `t` is
`Sum.inr 0` on the left and `Polynomial.X` on the right. -/
def sumEquiv (μ : ℕ) :
    MvPolynomial (Fin μ ⊕ Fin 1) ℝ ≃ₐ[ℝ] Polynomial (MvPolynomial (Fin μ) ℝ) :=
  (MvPolynomial.renameEquiv ℝ (sumOptionEquiv μ)).trans
    (MvPolynomial.optionEquivLeft ℝ (Fin μ))

/-- `pderiv` in the `none` variable of `MvPolynomial (Option σ) R` corresponds to
`Polynomial.derivative` under `MvPolynomial.optionEquivLeft`. -/
theorem optionEquivLeft_pderiv_none {R : Type*} [CommSemiring R] {σ : Type*}
    (p : MvPolynomial (Option σ) R) :
    MvPolynomial.optionEquivLeft R σ (MvPolynomial.pderiv none p) =
      Polynomial.derivative (MvPolynomial.optionEquivLeft R σ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    rw [MvPolynomial.pderiv_mul]
    cases n with
    | none =>
      simp only [MvPolynomial.pderiv_X_self, mul_one, map_add, map_mul, hp,
        MvPolynomial.optionEquivLeft_X_none, Polynomial.derivative_mul, Polynomial.derivative_X,
        mul_one]
    | some s =>
      simp only [MvPolynomial.pderiv_X_of_ne (i := none) (j := some s) (by simp), mul_zero,
        add_zero, map_mul, hp, MvPolynomial.optionEquivLeft_X_some, Polynomial.derivative_mul,
        Polynomial.derivative_C, mul_zero]

/-- The evaluation compatibility of `sumEquiv`. -/
theorem sumEquiv_eval (μ : ℕ) (G : MvPolynomial (Fin μ ⊕ Fin 1) ℝ) (u : Fin μ → ℝ) (t : ℝ) :
    MvPolynomial.eval (Sum.elim u (fun _ : Fin 1 => t)) G =
      Polynomial.eval t (Polynomial.map (MvPolynomial.eval u) (sumEquiv μ G)) := by
  have h := MvPolynomial.optionEquivLeft_elim_eval ℝ (Fin μ) u t
    (MvPolynomial.rename (sumOptionEquiv μ).toFun G)
  rw [MvPolynomial.eval_rename] at h
  have hcomp : (fun x : Option (Fin μ) => Option.elim x t u) ∘ (sumOptionEquiv μ).toFun
      = Sum.elim u (fun _ : Fin 1 => t) := by
    funext o
    rcases o with i | j <;> rfl
  rw [hcomp] at h
  simp only [sumEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply]
  exact h

/-- The derivative compatibility of `sumEquiv`. -/
theorem sumEquiv_pderiv (μ : ℕ) (G : MvPolynomial (Fin μ ⊕ Fin 1) ℝ) :
    sumEquiv μ (MvPolynomial.pderiv (Sum.inr 0) G) =
      Polynomial.derivative (sumEquiv μ G) := by
  have hinj : Function.Injective (⇑(sumOptionEquiv μ)) := (sumOptionEquiv μ).injective
  have h0 : (⇑(sumOptionEquiv μ)) (Sum.inr (0 : Fin 1)) = none := rfl
  simp only [sumEquiv, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply]
  rw [← MvPolynomial.pderiv_rename hinj (Sum.inr 0) G, h0]
  exact optionEquivLeft_pderiv_none _

theorem squarefree_excision_v2 {μ : ℕ} (Q : MvPolynomial (Fin μ ⊕ Fin 1) ℝ) (hQ : Q ≠ 0) :
    ∃ (G : MvPolynomial (Fin μ ⊕ Fin 1) ℝ) (l : MvPolynomial (Fin μ) ℝ), l ≠ 0 ∧
      ∀ u : Fin μ → ℝ, MvPolynomial.eval u l ≠ 0 →
        (∀ t : ℝ, MvPolynomial.eval (Sum.elim u (fun _ : Fin 1 => t)) G = 0 ↔
                  MvPolynomial.eval (Sum.elim u (fun _ : Fin 1 => t)) Q = 0) ∧
        (∀ t : ℝ, MvPolynomial.eval (Sum.elim u (fun _ : Fin 1 => t)) G = 0 →
           MvPolynomial.eval (Sum.elim u (fun _ : Fin 1 => t))
             (MvPolynomial.pderiv (Sum.inr 0) G) ≠ 0) := by
  classical
  have hQp : sumEquiv μ Q ≠ 0 :=
    fun h => hQ ((sumEquiv μ).injective (by simpa using h))
  obtain ⟨G0, D0, A0, B0, W0, n, c, γ, lam, hc, hγ, hlam, h1, h2, h3⟩ :=
    exists_poly_data (sumEquiv μ Q) hQp
  refine ⟨(sumEquiv μ).symm G0, c * γ * lam, mul_ne_zero (mul_ne_zero hc hγ) hlam, ?_⟩
  intro u hu
  have hc' : MvPolynomial.eval u c ≠ 0 := fun h => hu (by simp [h])
  have hγ' : MvPolynomial.eval u γ ≠ 0 := fun h => hu (by simp [h])
  have hlam' : MvPolynomial.eval u lam ≠ 0 := fun h => hu (by simp [h])
  let Qp : Polynomial ℝ := Polynomial.map (MvPolynomial.eval u) (sumEquiv μ Q)
  let Gp : Polynomial ℝ := Polynomial.map (MvPolynomial.eval u) G0
  let Dp : Polynomial ℝ := Polynomial.map (MvPolynomial.eval u) D0
  let Wp : Polynomial ℝ := Polynomial.map (MvPolynomial.eval u) W0
  let Ap : Polynomial ℝ := Polynomial.map (MvPolynomial.eval u) A0
  let Bp : Polynomial ℝ := Polynomial.map (MvPolynomial.eval u) B0
  have h1' : Polynomial.C (MvPolynomial.eval u c) * Qp = Dp * Gp := by
    have hh := congrArg (Polynomial.map (MvPolynomial.eval u)) h1
    simpa only [Qp, Dp, Gp, Polynomial.map_mul, Polynomial.map_C] using hh
  have h2' : Dp * Wp = Polynomial.C (MvPolynomial.eval u γ) * Gp ^ n := by
    have hh := congrArg (Polynomial.map (MvPolynomial.eval u)) h2
    simpa only [Dp, Wp, Gp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow] using hh
  have h3' : Polynomial.C (MvPolynomial.eval u lam) = Ap * Gp + Bp * Polynomial.derivative Gp := by
    have hh := congrArg (Polynomial.map (MvPolynomial.eval u)) h3
    simpa only [Ap, Bp, Gp, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      ← Polynomial.derivative_map] using hh
  obtain ⟨hr, hs⟩ := squarefree_root_lemma hc' hγ' hlam' h1' h2' h3'
  refine ⟨?_, ?_⟩
  · intro t
    rw [sumEquiv_eval μ Q u t, sumEquiv_eval μ ((sumEquiv μ).symm G0) u t,
      AlgEquiv.apply_symm_apply]
    exact hr t
  · intro t ht
    rw [sumEquiv_eval μ ((sumEquiv μ).symm G0) u t, AlgEquiv.apply_symm_apply] at ht
    rw [sumEquiv_eval μ (MvPolynomial.pderiv (Sum.inr 0) ((sumEquiv μ).symm G0)) u t,
      sumEquiv_pderiv, AlgEquiv.apply_symm_apply, ← Polynomial.derivative_map]
    exact hs t ht

end Work.WilkiesH.Strat
