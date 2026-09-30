import Mathlib
import Submission.Work.RB.faulhaber

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Partial sums of multivariable polynomials along a coordinate

For `Q : MvPolynomial (Fin (n+1)) ℚ` and `M : ℕ` we produce a polynomial `R` such that for every
`d : Fin (n+1) →₀ ℕ` with `M ≤ d 0`,

`R(d) = ∑_{k < d 0 - M} Q(M + k, d 1, …, d n)`.

The construction is the standard one: view `Q` as a polynomial in `X 0` with coefficients in
`ℚ[X 1, …, X n]` (via `MvPolynomial.finSuccEquiv`), replace each power `X ^ e` by the Faulhaber
polynomial for `∑_{k < t - M} (M + k) ^ e` (`Work.RB.exists_partial_sum_poly_shift`), and map back.
-/

namespace Work.RB

open MvPolynomial

/-- Evaluation of an `MvPolynomial` in `Fin (n+1)` variables factors through `finSuccEquiv`:
the `0`-th coordinate becomes the polynomial variable and the remaining coordinates evaluate the
coefficients. -/
theorem eval_finSuccEquiv {n : ℕ} (f : MvPolynomial (Fin (n+1)) ℚ) (x : Fin (n+1) → ℚ) :
    f.eval x = Polynomial.eval₂ (MvPolynomial.eval (fun j : Fin n => x j.succ)) (x 0)
      (MvPolynomial.finSuccEquiv ℚ n f) := by
  let ee : Fin (n+1) ≃ Option (Fin n) := _root_.finSuccEquiv n
  let g : Option (Fin n) → ℚ := fun o => Option.elim o (x 0) (fun j => x j.succ)
  have hg : g ∘ ee = x := by
    funext i
    exact Fin.cases (by simp [g, ee, _root_.finSuccEquiv_zero])
      (fun j => by simp [g, ee, _root_.finSuccEquiv_succ]) i
  have h1 : (MvPolynomial.eval g) (MvPolynomial.rename ee f) = f.eval x := by
    rw [MvPolynomial.eval_rename, hg]
  rw [← h1, MvPolynomial.optionEquivLeft_elim_eval, Polynomial.eval_map]
  congr 1

/-- Same evaluation identity, specialised to a point whose `0`-th coordinate is `a`. -/
theorem eval_at_update_zero {n : ℕ} (Q : MvPolynomial (Fin (n+1)) ℚ) (x : Fin (n+1) → ℚ)
    (a : ℚ) :
    Q.eval (Function.update x 0 a) =
      Polynomial.eval₂ (MvPolynomial.eval (fun j : Fin n => x j.succ)) a
        (MvPolynomial.finSuccEquiv ℚ n Q) := by
  rw [eval_finSuccEquiv]
  have h1 : (fun j : Fin n => Function.update x 0 a j.succ) = (fun j : Fin n => x j.succ) := by
    funext j; exact Function.update_of_ne (Fin.succ_ne_zero j) a x
  have h2 : Function.update x 0 a 0 = a := Function.update_self 0 a x
  rw [h1, h2]

/-- The Faulhaber polynomial for the shifted partial sums `∑_{k < t - M} (M + k) ^ e`. -/
noncomputable def shiftSumPoly (M e : ℕ) : Polynomial ℚ :=
  (exists_partial_sum_poly_shift (Polynomial.X ^ e) M).choose

theorem shiftSumPoly_spec (M e : ℕ) (t : ℕ) (ht : M ≤ t) :
    (shiftSumPoly M e).eval (t : ℚ) = ∑ k ∈ Finset.range (t - M), ((M + k : ℕ) : ℚ) ^ e := by
  have h := (exists_partial_sum_poly_shift (Polynomial.X ^ e) M).choose_spec t ht
  simpa [shiftSumPoly, Polynomial.eval_pow] using h

theorem eval₂_map_algebraMap_rat {B : Type*} [CommSemiring B] [Algebra ℚ B]
    (f : B →+* ℚ) (hf : f.comp (algebraMap ℚ B) = RingHom.id ℚ) (x : ℚ) (p : Polynomial ℚ) :
    Polynomial.eval₂ f x (p.map (algebraMap ℚ B)) = p.eval x := by
  rw [Polynomial.eval₂_map, hf, Polynomial.eval₂_id]

/-- The assembled polynomial in the `finSuccEquiv` picture: `X ^ e` is replaced by
`shiftSumPoly M e`. -/
noncomputable def mkSumPoly {B : Type*} [CommSemiring B] [Algebra ℚ B] (M : ℕ)
    (q : Polynomial B) : Polynomial B :=
  ∑ e ∈ q.support, Polynomial.C (q.coeff e) * (shiftSumPoly M e).map (algebraMap ℚ B)

theorem eval₂_mkSumPoly {B : Type*} [CommSemiring B] [Algebra ℚ B]
    (f : B →+* ℚ) (hf : f.comp (algebraMap ℚ B) = RingHom.id ℚ) (x : ℚ) (M : ℕ)
    (q : Polynomial B) :
    Polynomial.eval₂ f x (mkSumPoly M q) =
      ∑ e ∈ q.support, f (q.coeff e) * (shiftSumPoly M e).eval x := by
  rw [mkSumPoly, Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, eval₂_map_algebraMap_rat f hf]

theorem sumPoly {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) ℚ) (M : ℕ) :
    ∃ R : MvPolynomial (Fin (n + 1)) ℚ, ∀ d : Fin (n + 1) →₀ ℕ, M ≤ d 0 →
      R.eval (fun i => (d i : ℚ)) =
        ∑ k ∈ Finset.range (d 0 - M),
          Q.eval (Function.update (fun i => (d i : ℚ)) 0 ((M + k : ℕ) : ℚ)) := by
  classical
  refine ⟨(MvPolynomial.finSuccEquiv ℚ n).symm
      (mkSumPoly M ((MvPolynomial.finSuccEquiv ℚ n) Q)), ?_⟩
  intro d hd
  set x : Fin (n + 1) → ℚ := fun i => (d i : ℚ) with hx
  have hx0 : x 0 = ((d 0 : ℕ) : ℚ) := by rw [hx]
  have hf : (MvPolynomial.eval (fun j : Fin n => x j.succ)).comp
      (algebraMap ℚ (MvPolynomial (Fin n) ℚ)) = RingHom.id ℚ := by
    ext c; simp
  rw [eval_finSuccEquiv, AlgEquiv.apply_symm_apply,
    eval₂_mkSumPoly (f := MvPolynomial.eval (fun j : Fin n => x j.succ)) (hf := hf)]
  have hL : ∑ e ∈ ((MvPolynomial.finSuccEquiv ℚ n) Q).support,
        (MvPolynomial.eval (fun j : Fin n => x j.succ)) (((MvPolynomial.finSuccEquiv ℚ n) Q).coeff e) *
          (shiftSumPoly M e).eval (x 0)
      = ∑ e ∈ ((MvPolynomial.finSuccEquiv ℚ n) Q).support,
        (MvPolynomial.eval (fun j : Fin n => x j.succ)) (((MvPolynomial.finSuccEquiv ℚ n) Q).coeff e) *
          ∑ k ∈ Finset.range (d 0 - M), ((M + k : ℕ) : ℚ) ^ e := by
    refine Finset.sum_congr rfl (fun e he => ?_)
    rw [hx0, shiftSumPoly_spec M e (d 0) hd]
  have hR : (∑ k ∈ Finset.range (d 0 - M), Q.eval (Function.update x 0 ((M + k : ℕ) : ℚ)))
      = ∑ e ∈ ((MvPolynomial.finSuccEquiv ℚ n) Q).support,
        (MvPolynomial.eval (fun j : Fin n => x j.succ)) (((MvPolynomial.finSuccEquiv ℚ n) Q).coeff e) *
          ∑ k ∈ Finset.range (d 0 - M), ((M + k : ℕ) : ℚ) ^ e := by
    have step : ∀ k, Q.eval (Function.update x 0 ((M + k : ℕ) : ℚ)) =
        ∑ e ∈ ((MvPolynomial.finSuccEquiv ℚ n) Q).support,
          (MvPolynomial.eval (fun j : Fin n => x j.succ)) (((MvPolynomial.finSuccEquiv ℚ n) Q).coeff e) *
            (((M + k : ℕ)) : ℚ) ^ e := by
      intro k
      rw [eval_at_update_zero, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    rw [Finset.sum_congr rfl (fun k hk => step k), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e he => ?_)
    rw [← Finset.mul_sum]
  rw [hL, hR]

end Work.RB
