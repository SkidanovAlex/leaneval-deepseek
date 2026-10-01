import Mathlib
import Submission.Work.LinnikBurgess.critN_shifts
import Submission.Work.LinnikBurgess.critN_shifts_congr
import Submission.Work.LinnikBurgess.critN_pencil_alg

namespace Work.LinnikBurgess

open Polynomial

/-- **Pencil lemma.**

Let `f_a = ∏_l (X + a_l)`, `f_b = ∏_l (X + b_l)` be the two cubics attached to the triples
`a, b : Fin 3 → ℕ`, and let `y` be a point which is a `p`-adic unit for all six roots
(`UnitAt p y a b`).  If the Wronskian `critN a b = f_a' f_b - f_a f_b'` and its derivative both
vanish at `y` modulo `p^k`, then modulo `p^(k - v_p(2))` the two cubics lie in a pencil spanned
by one of them and the exact cube `(X - y)^3`:

`f_a ≡ c · f_b + (1 - c) · (X - y)^3 (mod p^(k - v_p 2))` with `c` a unit.

The exponent `k - v_p(2)` comes from the derivative condition: `critN'(y) = 2 (sh1(a) sh3(b) -
sh3(a) sh1(b))` carries a factor `2`. -/
theorem critN_pencil {p k : ℕ} [Fact p.Prime] (a b : Fin 3 → ℕ) (y : ℕ) (hy : UnitAt p y a b)
    (hN : ((p ^ k : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ))
    (hN' : ((p ^ k : ℕ) : ℤ) ∣ (Polynomial.derivative (critN a b)).eval (y : ℤ)) :
    ∃ c : ZMod (p ^ (k - padicValNat p 2)), IsUnit c ∧
      (cubicZ a).map (Int.castRingHom (ZMod (p ^ (k - padicValNat p 2))))
        = Polynomial.C c * (cubicZ b).map (Int.castRingHom (ZMod (p ^ (k - padicValNat p 2))))
          + Polynomial.C (1 - c)
            * (Polynomial.X - Polynomial.C (y : ZMod (p ^ (k - padicValNat p 2)))) ^ 3 := by
  -- Rewrite the two divisibility hypotheses in terms of the shifted elementary
  -- symmetric functions `sh1, sh2, sh3` of `(y + a l)` and `(y + b l)`.
  rw [critN_eval_shift] at hN
  rw [critN_deriv_eval_shift] at hN'
  -- Arithmetic part: the shifted symmetric functions become proportional mod `p^(k - v_p 2)`.
  obtain ⟨c, hcunit, h1c, h2c, h3c⟩ := critN_shifts_congr a b y hy hN hN'
  refine ⟨c, hcunit, ?_⟩
  -- Expand both cubics around the shift `y` and compare coefficients in `(X - y)`.
  rw [cubicZ_map_eq_prod_shift a y, cubicZ_map_eq_prod_shift b y]
  refine critN_pencil_alg (y : ZMod (p ^ (k - padicValNat p 2)))
    (fun l : Fin 3 => (y : ZMod (p ^ (k - padicValNat p 2)))
      + ((a l : ℕ) : ZMod (p ^ (k - padicValNat p 2))))
    (fun l : Fin 3 => (y : ZMod (p ^ (k - padicValNat p 2)))
      + ((b l : ℕ) : ZMod (p ^ (k - padicValNat p 2))))
    c ?_ ?_ ?_
  · simp only [sh1_cast_eq]
    exact h1c
  · simp only [sh2_cast_eq]
    exact h2c
  · simp only [sh3_cast_eq]
    exact h3c

end Work.LinnikBurgess
