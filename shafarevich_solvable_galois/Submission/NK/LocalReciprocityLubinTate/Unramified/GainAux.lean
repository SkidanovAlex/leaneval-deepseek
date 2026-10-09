import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.NormOp
import Submission.NK.LocalReciprocityLubinTate.Unramified.LTGain
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary material for the Lubin–Tate gain lemma

This file collects the ring-theoretic infrastructure used by the proof of the *gain lemma*
`NK.LocalReciprocityLubinTate.Unramified.normOp_gain`.

The central object is the **`s`-parametrised norm operator**

`gainPoly P q t = Res_X (f(X) - Y, 1 + s·t(X)) ∈ (A[s])[Y]`,

where `f = LTpoly P q = P·X + X^q`.  Concretely, `gainPoly` is `normOp` computed over the
coefficient ring `A[s] = Polynomial A`, so that the variable `s` appears only in the coefficients
and the resultant `Y` is the outer variable.  Writing `G = gainPoly P q t`:

* `map_gainPoly` — base change of `G` along a ring hom `ψ : A[s] →+* R`;
* `dvd_eval_pow_of_coeff`, `map_evalRingHom_sub_one_mem_span` — the elementary coefficient
  estimates which turn `G ≡ 1 mod s` (together with the vanishing of the `s`-coefficient of `G`
  mod `P`) into `G(P^k) ≡ 1 mod P^(k+1)`.
-/

open Polynomial

namespace NK.LocalReciprocityLubinTate.Unramified

universe u v

variable {A : Type u} [CommRing A]

/-- `f(X) - Y ∈ (A[s][Y])[X]`, the first argument of the resultant defining `gainPoly`.  Here `s` is
the variable of `A[s]` and `Y` the variable of the outer polynomial ring. -/
noncomputable def gainF (P : A) (q : ℕ) : Polynomial (Polynomial (Polynomial A)) :=
  (((NK.LocalReciprocityLubinTate.LTpoly P q).map Polynomial.C).map Polynomial.C)
    - Polynomial.C (Polynomial.X : Polynomial (Polynomial A))

/-- `1 + s·t(X) ∈ A[s][X]`, the second argument of the resultant defining `gainPoly`. -/
noncomputable def hPoly (t : Polynomial A) : Polynomial (Polynomial A) :=
  1 + Polynomial.C (Polynomial.X : Polynomial A) * t.map Polynomial.C

/-- `(1 + s·t(X))` viewed in `(A[s][Y])[X]` (all coefficients constants). -/
noncomputable def gainH (t : Polynomial A) : Polynomial (Polynomial (Polynomial A)) :=
  (hPoly t).map Polynomial.C

/-- **The `s`-parametrised norm operator.**  `gainPoly P q t = Res_X(f(X) - Y, 1 + s·t(X))`, an
element of `(A[s])[Y]`, where `f = LTpoly P q`.  (The `X`-degree parameter of the resultant is
`q`, the `1 + s·t`-degree parameter is `(hPoly t).natDegree`.) -/
noncomputable def gainPoly (P : A) (q : ℕ) (t : Polynomial A) : Polynomial (Polynomial A) :=
  Polynomial.resultant (gainF P q) (gainH t) q (hPoly t).natDegree

/-- **Base change of the `s`-parametrised norm operator.**  For a ring hom `ψ : A[s] →+* R`, the
image of `gainPoly P q t` is the resultant of the base-changed factors. -/
theorem map_gainPoly {R : Type v} [CommRing R] (P : A) (q : ℕ) (t : Polynomial A)
    (ψ : Polynomial A →+* R) :
    Polynomial.map ψ (gainPoly P q t)
      = Polynomial.resultant
          ((((NK.LocalReciprocityLubinTate.LTpoly P q).map Polynomial.C).map ψ).map Polynomial.C
            - Polynomial.C (Polynomial.X : Polynomial R))
          (((hPoly t).map ψ).map Polynomial.C)
          q (hPoly t).natDegree := by
  have hX : (Polynomial.mapRingHom ψ) (Polynomial.X : Polynomial (Polynomial A)) = Polynomial.X :=
    Polynomial.map_X ψ
  have h1 : Polynomial.map ψ (gainPoly P q t)
      = Polynomial.resultant (Polynomial.map (Polynomial.mapRingHom ψ) (gainF P q))
          (Polynomial.map (Polynomial.mapRingHom ψ) (gainH t)) q (hPoly t).natDegree := by
    rw [show Polynomial.map ψ (gainPoly P q t)
        = (Polynomial.mapRingHom ψ) (gainPoly P q t) from rfl]
    rw [gainPoly]
    exact (Polynomial.resultant_map_map (gainF P q) (gainH t) q (hPoly t).natDegree
      (Polynomial.mapRingHom ψ)).symm
  rw [h1]
  have hF : Polynomial.map (Polynomial.mapRingHom ψ) (gainF P q)
      = (((NK.LocalReciprocityLubinTate.LTpoly P q).map Polynomial.C).map ψ).map Polynomial.C
        - Polynomial.C (Polynomial.X : Polynomial R) := by
    rw [gainF, Polynomial.map_sub, Polynomial.map_C, hX]
    congr 1
    rw [Polynomial.map_map, Polynomial.map_map, Polynomial.map_map, Polynomial.map_map,
      Polynomial.mapRingHom_comp_C]
  have hH : Polynomial.map (Polynomial.mapRingHom ψ) (gainH t)
      = ((hPoly t).map ψ).map Polynomial.C := by
    rw [gainH, Polynomial.map_map, Polynomial.map_map, Polynomial.mapRingHom_comp_C]
  rw [hF, hH]

/-! ## Coefficient estimates for the final step -/

/-- If `q.coeff 0 = 0` and `c ∣ q.coeff 1`, then `c ^ (k+1)` divides `(q.eval (c^k))`.  This is the
elementary estimate behind the gain lemma: the constant term of `q` vanishes, so `q.eval (c^k)` is
`c^k` times the evaluation of `q.divX`; and `(q.divX).eval c` is `(q.divX).coeff 0 = q.coeff 1`
modulo `c`. -/
theorem dvd_eval_pow_of_coeff {R : Type*} [CommRing R] (c : R) (k : ℕ) (hk : 1 ≤ k)
    (q : Polynomial R) (h0 : q.coeff 0 = 0) (h1 : c ∣ q.coeff 1) :
    c ^ (k + 1) ∣ Polynomial.eval (c ^ k) q := by
  have hq : Polynomial.eval (c ^ k) q = c ^ k * Polynomial.eval (c ^ k) q.divX := by
    calc Polynomial.eval (c ^ k) q
        = Polynomial.eval (c ^ k) (Polynomial.X * q.divX + Polynomial.C (q.coeff 0)) := by
            rw [Polynomial.X_mul_divX_add]
      _ = c ^ k * Polynomial.eval (c ^ k) q.divX + q.coeff 0 := by
            rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
      _ = c ^ k * Polynomial.eval (c ^ k) q.divX := by rw [h0, add_zero]
  have hdiv : c ∣ Polynomial.eval (c ^ k) q.divX := by
    have h2 : Polynomial.eval (c ^ k) q.divX
        = c ^ k * Polynomial.eval (c ^ k) q.divX.divX + q.coeff 1 := by
      calc Polynomial.eval (c ^ k) q.divX
          = Polynomial.eval (c ^ k) (Polynomial.X * q.divX.divX
              + Polynomial.C (q.divX.coeff 0)) := by rw [Polynomial.X_mul_divX_add]
        _ = c ^ k * Polynomial.eval (c ^ k) q.divX.divX + q.divX.coeff 0 := by
              rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
        _ = c ^ k * Polynomial.eval (c ^ k) q.divX.divX + q.coeff 1 := by
              rw [Polynomial.coeff_divX]
    rw [h2]
    exact dvd_add (dvd_mul_of_dvd_left (by simpa using pow_dvd_pow c hk) _) h1
  rw [hq]
  obtain ⟨w, hw⟩ := hdiv
  rw [hw, ← mul_assoc, ← pow_succ]
  exact dvd_mul_right _ _

/-- **The final coefficient estimate.**  Let `G ∈ A[s][Y]` be a polynomial whose value at `s = 0` is
`1` and whose `s`-linear coefficients are all divisible by `c`.  Then `G(c^k) ≡ 1` modulo
`c ^ (k+1)`, for `k ≥ 1`. -/
theorem map_evalRingHom_sub_one_mem_span {R : Type*} [CommRing R] (c : R) (k : ℕ) (hk : 1 ≤ k)
    (G : Polynomial (Polynomial R))
    (h0 : Polynomial.map (Polynomial.evalRingHom 0) G = 1)
    (h1 : ∀ j, c ∣ (G.coeff j).coeff 1) :
    Polynomial.map (Polynomial.evalRingHom (c ^ k)) G - 1
      ∈ Ideal.span ({Polynomial.C (c ^ (k + 1))} : Set (Polynomial R)) := by
  rw [← Polynomial.map_one (Polynomial.evalRingHom (c ^ k)), ← Polynomial.map_sub]
  rw [Ideal.mem_span_singleton]
  apply exists_eq_C_mul_of_coeff_dvd
  intro j
  rw [Polynomial.coeff_map]
  have hz : Polynomial.map (Polynomial.evalRingHom 0) (G - 1) = 0 := by
    rw [Polynomial.map_sub, h0, Polynomial.map_one, sub_self]
  have h0' : ((G - 1).coeff j).coeff 0 = 0 := by
    have h := congrArg (fun u : Polynomial R => u.coeff j) hz
    rw [Polynomial.coeff_map, Polynomial.coe_evalRingHom] at h
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simpa using h
  have h1' : c ∣ ((G - 1).coeff j).coeff 1 := by
    have hc : ((1 : Polynomial (Polynomial R)).coeff j).coeff 1 = 0 := by
      rw [Polynomial.coeff_one]
      by_cases hj : j = 0 <;> simp [hj, Polynomial.coeff_one]
    have heq : ((G - 1).coeff j).coeff 1 = (G.coeff j).coeff 1 := by
      rw [Polynomial.coeff_sub, Polynomial.coeff_sub, hc, sub_zero]
    rw [heq]
    exact h1 j
  exact dvd_eval_pow_of_coeff c k hk ((G - 1).coeff j) h0' h1'

end NK.LocalReciprocityLubinTate.Unramified
