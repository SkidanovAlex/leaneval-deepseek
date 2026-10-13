import Mathlib
import Submission.Work.WilE3.Realify.Defs

namespace Work.WilE3.Realify

open MvPolynomial
open WilkiesDesign.E

/-!
## Evaluation of the realification of a monomial

`monoNum N e m` is the image of the monomial `m` under the realification: the `N`-th
clearing power `(∏_j (1 + t_j²))^N` times (in the complexified target ring) the element

`∏_i (u_i + i v_i)^{m(inl i)} · ∏_j (e_j y_j z_j)^{m(inr j)} · ∏_j (1 + t_j²)^{N - m(inr j)}`.

Evaluating on the chain point `chainPt` and using the half-angle identity
`1 + 2 i tan θ - tan²θ = e^{2 i θ} (1 + tan²θ)` together with `e_j = e^{i cc_j}`, the
target theorem reduces the per-`j` factor `e_j y_j z_j` to `e^{ℓ_j} (1 + t_j²)`, so that
the `j`-products collapse to `∏_j e^{ℓ_j}^{m(inr j)} · Wval^N`.

This file supplies the three ingredients and then assembles them:

* `tan_exp_key` — the half-angle identity `1 + 2i t - t² = e^{2iθ}(1+t²)` for `t = tan θ`;
* `per_j_key`  — its complexified form, folding in `e^{i cc}` and `e^{i P}` into `e^{L}`;
* `eval_monoNum_expand` — the `simp`-level computation of `eval` on `monoNum`.
-/

/-- **Half-angle identity.** For real `θ` with `cos θ ≠ 0` and `t = tan θ`,
`1 + 2 i t - t² = e^{2 i θ} (1 + t²)` (both sides are `(1 + i t)²`). -/
lemma tan_exp_key (θ : ℝ) (hθ : Real.cos θ ≠ 0) :
    (1 : ℂ) + 2 * Complex.I * (Real.tan θ : ℂ) - (Real.tan θ : ℂ)^2
      = Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) * (1 + (Real.tan θ : ℂ)^2) := by
  have h1 : (1 : ℂ) + 2 * Complex.I * (Real.tan θ : ℂ) - (Real.tan θ : ℂ)^2
      = (1 + Complex.I * (Real.tan θ : ℂ))^2 := by
    ring_nf; simp only [Complex.I_sq]; ring
  have h3 : Complex.exp ((θ : ℂ) * Complex.I)
      = (Real.cos θ : ℂ) * (1 + Complex.I * (Real.tan θ : ℂ)) := by
    rw [Complex.exp_ofReal_mul_I]
    have hct : Real.cos θ * Real.tan θ = Real.sin θ := by
      rw [Real.tan_eq_sin_div_cos]; field_simp
    have hct' : (Real.cos θ : ℂ) * (Real.tan θ : ℂ) = (Real.sin θ : ℂ) := by
      rw [← Complex.ofReal_mul, hct]
    rw [show (Real.cos θ : ℂ) * (1 + Complex.I * (Real.tan θ : ℂ))
        = (Real.cos θ : ℂ) + ((Real.cos θ : ℂ) * (Real.tan θ : ℂ)) * Complex.I from by ring,
      hct']
  have h4 : (Real.cos θ : ℂ)^2 * (1 + (Real.tan θ : ℂ)^2) = 1 := by
    have hr : Real.cos θ ^ 2 * (1 + Real.tan θ ^ 2) = 1 := by
      rw [Real.tan_eq_sin_div_cos]; field_simp; nlinarith [Real.cos_sq_add_sin_sq θ]
    exact_mod_cast hr
  have h2 : Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((θ : ℂ) * Complex.I)^2 := by
    rw [show ((2 * θ : ℝ) : ℂ) * Complex.I = (θ:ℂ)*Complex.I + (θ:ℂ)*Complex.I from by
          push_cast; ring,
        Complex.exp_add, pow_two]
  rw [h1, h2, h3, mul_pow]
  rw [show (Real.cos θ : ℂ)^2 * (1 + Complex.I * (Real.tan θ : ℂ))^2 * (1 + (Real.tan θ : ℂ)^2)
        = (1 + Complex.I * (Real.tan θ : ℂ))^2
            * ((Real.cos θ : ℂ)^2 * (1 + (Real.tan θ : ℂ)^2)) from by ring, h4]
  ring

/-- **Complexified per-chain-function key identity.** With `e = e^{i cc}`, `L = ReL + iP`
and `t = tan ((P - cc)/2)`,
`e^{L} (1 + t²) = e · e^{ReL} · (1 + 2 i t - t²)`. -/
lemma per_j_key (cc P ReL : ℝ) (e : ℝ) (L : ℂ)
    (he : (e : ℂ) = Complex.exp ((cc : ℂ) * Complex.I))
    (hL : L = (ReL : ℂ) + (P : ℂ) * Complex.I)
    (hθ : Real.cos ((P - cc) / 2) ≠ 0) :
    Complex.exp L * (1 + (Real.tan ((P - cc) / 2) : ℂ)^2)
      = (e : ℂ) * (Real.exp ReL : ℂ)
        * (1 + 2 * Complex.I * (Real.tan ((P - cc) / 2) : ℂ)
           - (Real.tan ((P - cc) / 2) : ℂ)^2) := by
  have h2θ : (2 * ((P - cc) / 2) : ℝ) = P - cc := by ring
  have hkey := tan_exp_key ((P - cc) / 2) hθ
  rw [h2θ] at hkey
  have hexpP : Complex.exp ((cc : ℂ) * Complex.I) * Complex.exp (((P - cc : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((P : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hE : Complex.exp L = (e : ℂ) * (Real.exp ReL : ℂ)
      * Complex.exp (((P - cc : ℝ) : ℂ) * Complex.I) := by
    calc Complex.exp L
        = (Real.exp ReL : ℂ) * Complex.exp ((P : ℂ) * Complex.I) := by
            rw [hL, Complex.exp_add, Complex.ofReal_exp]
      _ = (Real.exp ReL : ℂ)
            * (Complex.exp ((cc : ℂ) * Complex.I)
                * Complex.exp (((P - cc : ℝ) : ℂ) * Complex.I)) := by
            rw [hexpP]
      _ = (e : ℂ) * (Real.exp ReL : ℂ) * Complex.exp (((P - cc : ℝ) : ℂ) * Complex.I) := by
            rw [he]; ring
  rw [hE, hkey]
  ring

/-- The chain exponent decomposes as `ReL + i P`: `∑_i a_{ji} (u_i + i v_i) + b_j`
is `(∑_i a_{ji} u_i + b_j) + i (∑_i a_{ji} v_i)`. -/
lemma L_decomp {k r : ℕ} (c : EAChain k r) (u v : Fin k → ℝ) (j : Fin r) :
    (∑ i, (c.a j i : ℂ) * ((u i : ℂ) + (v i : ℂ) * Complex.I) + (c.b j : ℂ))
    = ((∑ i, c.a j i * u i + c.b j : ℝ) : ℂ)
      + ((∑ i, c.a j i * v i : ℝ) : ℂ) * Complex.I := by
  push_cast
  simp only [mul_add, Finset.sum_add_distrib]
  rw [show (∑ x, (c.a j x : ℂ) * ((v x : ℂ) * Complex.I))
        = (∑ x, (c.a j x : ℂ) * (v x : ℂ)) * Complex.I from by
      rw [show (∑ x, (c.a j x : ℂ) * ((v x : ℂ) * Complex.I))
            = ∑ x, ((c.a j x : ℂ) * (v x : ℂ)) * Complex.I from
          Finset.sum_congr rfl (fun x _ => by ring),
          ← Finset.sum_mul]]
  ring

/-- **Computation of `eval` on `monoNum`.** Pushing `MvPolynomial.eval` at the chain point
`chainPt c cc u v` through the product defining `monoNum` leaves the explicit product of
the evaluated factors. -/
lemma eval_monoNum_expand {k r : ℕ} (c : EAChain k r) (cc e : Fin r → ℝ)
    (N : ℕ) (m : (Fin k ⊕ Fin r) →₀ ℕ) (u v : Fin k → ℝ) :
    MvPolynomial.eval (fun s => (chainPt c cc u v s : ℂ)) (monoNum (k := k) (r := r) N e m)
      = (∏ i : Fin k, (((u i : ℂ) + (v i : ℂ) * Complex.I)) ^ (m (Sum.inl i)))
        * (∏ j : Fin r, ((e j : ℂ) * (Real.exp (∑ i, c.a j i * u i + c.b j) : ℂ)
            * (1 + 2 * Complex.I * (Real.tan ((∑ i, c.a j i * v i - cc j) / 2) : ℂ)
               - (Real.tan ((∑ i, c.a j i * v i - cc j) / 2) : ℂ) ^ 2)) ^ (m (Sum.inr j)))
        * (∏ j : Fin r,
            (1 + (Real.tan ((∑ i, c.a j i * v i - cc j) / 2) : ℂ) ^ 2) ^ (N - m (Sum.inr j))) := by
  simp only [monoNum, map_mul, map_prod, map_pow, map_add, map_sub, map_one, map_ofNat,
    eval_X, eval_C, cU, cV, cY, cT, cW, cZ, cI,
    chainPt, Sum.elim_inl, Sum.elim_inr, mkPt, Fin.addCases_left, Fin.addCases_right,
    mul_comm Complex.I]

theorem eval_monoNum {k r : ℕ} (c : WilkiesDesign.E.EAChain k r) (cc e : Fin r → ℝ)
    (he : ∀ j, (e j : ℂ) = Complex.exp ((cc j : ℂ) * Complex.I))
    (N : ℕ) (m : (Fin k ⊕ Fin r) →₀ ℕ) (u v : Fin k → ℝ)
    (hcos : ∀ j, Real.cos ((∑ i, c.a j i * v i - cc j) / 2) ≠ 0)
    (hm : ∀ j, m (Sum.inr j) ≤ N) :
    MvPolynomial.eval (fun s => (chainPt c cc u v s : ℂ)) (monoNum (k := k) (r := r) N e m)
      = (∏ i : Fin k, ((u i : ℂ) + (v i : ℂ) * Complex.I) ^ (m (Sum.inl i)))
        * (∏ j : Fin r, (Complex.exp (∑ i, (c.a j i : ℂ) * ((u i : ℂ) + (v i : ℂ) * Complex.I)
              + (c.b j : ℂ))) ^ (m (Sum.inr j)))
        * ((Wval c cc v : ℝ) : ℂ) ^ N := by
  rw [eval_monoNum_expand c cc e N m u v]
  -- per-`j` rewrite `e_j y_j z_j = e^{ℓ_j} (1 + t_j²)`, then `(a * b)^m = a^m * b^m`
  have hA : ∀ j : Fin r,
      ((e j : ℂ) * (Real.exp (∑ i, c.a j i * u i + c.b j) : ℂ)
          * (1 + 2 * Complex.I * (Real.tan ((∑ i, c.a j i * v i - cc j) / 2) : ℂ)
             - (Real.tan ((∑ i, c.a j i * v i - cc j) / 2) : ℂ) ^ 2)) ^ (m (Sum.inr j))
      = (Complex.exp (∑ i, (c.a j i : ℂ) * ((u i : ℂ) + (v i : ℂ) * Complex.I)
            + (c.b j : ℂ))) ^ (m (Sum.inr j))
        * (1 + (Real.tan ((∑ i, c.a j i * v i - cc j) / 2) : ℂ) ^ 2) ^ (m (Sum.inr j)) := by
    intro j
    rw [← per_j_key (cc j) (∑ i, c.a j i * v i) (∑ i, c.a j i * u i + c.b j) (e j)
        (∑ i, (c.a j i : ℂ) * ((u i : ℂ) + (v i : ℂ) * Complex.I) + (c.b j : ℂ))
        (he j) (L_decomp c u v j) (hcos j), mul_pow]
  -- the `(1 + t_j²)^{m_j} · (1 + t_j²)^{N - m_j}` collapse to `(∏_j (1 + t_j²))^N`
  have hB : (∏ j : Fin r,
        (1 + (Real.tan ((∑ i, c.a j i * v i - cc j) / 2) : ℂ) ^ 2) ^ (m (Sum.inr j)))
      * (∏ j : Fin r,
        (1 + (Real.tan ((∑ i, c.a j i * v i - cc j) / 2) : ℂ) ^ 2) ^ (N - m (Sum.inr j)))
      = (∏ j : Fin r, (1 + (Real.tan ((∑ i, c.a j i * v i - cc j) / 2) : ℂ) ^ 2)) ^ N := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro j _
    rw [← pow_add, Nat.add_sub_of_le (hm j)]
  -- `Wval` is exactly the product of the `(1 + t_j²)`
  have hWval : ((Wval c cc v : ℝ) : ℂ)
      = ∏ j : Fin r, (1 + (Real.tan ((∑ i, c.a j i * v i - cc j) / 2) : ℂ) ^ 2) := by
    rw [Wval, Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro j _
    push_cast
    ring
  rw [Finset.prod_congr rfl (fun j _ => hA j), Finset.prod_mul_distrib, mul_assoc, mul_assoc,
    hB, hWval]
  ring

end Work.WilE3.Realify
