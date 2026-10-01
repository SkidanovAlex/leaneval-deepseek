import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.critN_shifts
import Submission.Work.LinnikBurgess.critN_deriv2_eval_shift
import Submission.Work.LinnikBurgess.critN_crossCong_delta

/-!
# The triple-vanishing lemma: `p^(k - v_p 6) | Cont(v)`

This is the "TV" lemma of the Burgess route (`BURGESS_ROUTE_LEAD.md`, §2.2).  Let

* `f_a(X) = ∏_l (X + a_l) = cubicZ a` and `f_b(X) = ∏_l (X + b_l) = cubicZ b` be the two monic
  cubics attached to two triples `a, b : Fin 3 → ℕ`,
* `N = critN a b = f_a' f_b - f_a f_b'` their Wronskian,
* `y` a point which is a `p`-adic unit for all six roots (`UnitAt p y a b`),
* `Cont(v) = contAB a b = gcd_k |e_k(a) - e_k(b)|` the content (the gcd of the three differences of
  elementary symmetric functions).

If `N`, `N'` and `N''` all vanish at `y` modulo `p^k`, then `p^(k - v_p 6) | contAB a b`.

The proof has three ingredients.

1. *Evaluation at the shift.*  Writing `u = X - y` and expanding both cubics around `y`, the class of
   `A_i := sh_i y a = e_i(y + a)` (`A_i = B_i + Δ_i`), `B_i := sh_i y b`, one gets the three exact
   identities
   `N(y) = Δ₂B₃ - Δ₃B₂`, `N'(y) = 2(Δ₁B₃ - Δ₃B₁)`,
   `N''(y) = 2((Δ₁B₂ - Δ₂B₁) - 3Δ₃)`
   (`critN_eval_shift`, `critN_deriv_eval_shift`, `critN_deriv2_eval_shift`).  The factors `2` and
   `3` (i.e. `6`) are the origin of the loss `v_p(6)`.
2. *Pure arithmetic.*  `critN_crossCong_delta` turns those three congruences, together with the fact
   that `p ∤ B₃` (which holds because `y` is a unit at `p`), into
   `p^(k - v_p 6) | Δ_i` for `i = 1, 2, 3`.
3. *Undoing the shift.*  `Δ₁ = e₁(a) - e₁(b)`, `Δ₂ = 2y·Δ₁ + (e₂(a) - e₂(b))` and
   `Δ₃ = y²·Δ₁ + y·Δ₂ + (e₃(a) - e₃(b))`, so each difference `e_k(a) - e_k(b)` is an integer
   combination of the `Δ_i`; hence `p^(k - v_p 6)` divides all three of them, i.e. divides their gcd
   `contAB a b`.
-/

namespace Work.LinnikBurgess

open Polynomial

/-- If none of the `y + b l` is divisible by the prime `p`, then their product `sh3 y b` is
prime to `p`. -/
theorem not_dvd_sh3_of_unitAt {p y : ℕ} [Fact p.Prime] {b : Fin 3 → ℕ}
    (hy : ∀ l : Fin 3, ¬ p ∣ y + b l) : ¬ p ∣ sh3 y b := by
  intro hd
  have hp : p.Prime := Fact.out
  rw [sh3] at hd
  rcases hp.dvd_mul.mp hd with hd | hd
  · rcases hp.dvd_mul.mp hd with hd | hd
    · exact hy 0 hd
    · exact hy 1 hd
  · exact hy 2 hd

/-- The shift `y` cancels in the first difference of shifted elementary symmetric functions. -/
theorem sh1_sub_eq_esymm3 (a b : Fin 3 → ℕ) (y : ℕ) :
    (sh1 y a : ℤ) - (sh1 y b : ℤ) = esymm3 a 0 - esymm3 b 0 := by
  simp [sh1, esymm3]
  ring

/-- The second shifted difference, written through the unshifted one. -/
theorem sh2_sub_eq_esymm3 (a b : Fin 3 → ℕ) (y : ℕ) :
    (sh2 y a : ℤ) - (sh2 y b : ℤ)
      = 2 * (y : ℤ) * (esymm3 a 0 - esymm3 b 0) + (esymm3 a 1 - esymm3 b 1) := by
  simp [sh2, esymm3]
  ring

/-- The third shifted difference, written through the two unshifted ones. -/
theorem sh3_sub_eq_esymm3 (a b : Fin 3 → ℕ) (y : ℕ) :
    (sh3 y a : ℤ) - (sh3 y b : ℤ)
      = (y : ℤ) ^ 2 * (esymm3 a 0 - esymm3 b 0) + (y : ℤ) * (esymm3 a 1 - esymm3 b 1)
        + (esymm3 a 2 - esymm3 b 2) := by
  simp [sh3, esymm3]
  ring

/-- **Triple-vanishing lemma.**  If the Wronskian `critN a b = f_a' f_b - f_a f_b'` together with
its first two derivatives vanishes at a `p`-adic unit point `y` modulo `p^k`, then `p^(k - v_p 6)`
divides the content `contAB a b = gcd_k |e_k(a) - e_k(b)|`. -/
theorem critN_tripleVanish_content {p k : ℕ} [Fact p.Prime] (a b : Fin 3 → ℕ) (y : ℕ)
    (hy : UnitAt p y a b)
    (h0 : ((p ^ k : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ))
    (h1 : ((p ^ k : ℕ) : ℤ) ∣ (Polynomial.derivative (critN a b)).eval (y : ℤ))
    (h2 : ((p ^ k : ℕ) : ℤ) ∣ (Polynomial.derivative (Polynomial.derivative (critN a b))).eval (y : ℤ)) :
    p ^ (k - padicValNat p 6) ∣ contAB a b := by
  have hp : p.Prime := Fact.out
  -- Step 1: rewrite the three hypotheses through the shifted symmetric functions.
  rw [critN_eval_shift] at h0
  rw [critN_deriv_eval_shift] at h1
  rw [critN_deriv2_eval_shift] at h2
  -- The product `sh3 y b` is prime to `p`.
  have hB3 : ¬ (p : ℤ) ∣ (sh3 y b : ℤ) := by
    have hnd : ¬ p ∣ sh3 y b := not_dvd_sh3_of_unitAt (fun l => (hy l).2)
    rwa [Int.natCast_dvd_natCast]
  -- Step 2: the pure arithmetic lemma.
  obtain ⟨hd1, hd2, hd3⟩ := critN_crossCong_delta (p := p) (k := k) hB3 h0 h1 h2
  -- Step 3: undo the shift and pass to the content.
  have e1 : (sh1 y a : ℤ) - (sh1 y b : ℤ) = esymm3 a 0 - esymm3 b 0 :=
    sh1_sub_eq_esymm3 a b y
  have e2 : (sh2 y a : ℤ) - (sh2 y b : ℤ)
      = 2 * (y : ℤ) * (esymm3 a 0 - esymm3 b 0) + (esymm3 a 1 - esymm3 b 1) :=
    sh2_sub_eq_esymm3 a b y
  have e3 : (sh3 y a : ℤ) - (sh3 y b : ℤ)
      = (y : ℤ) ^ 2 * (esymm3 a 0 - esymm3 b 0) + (y : ℤ) * (esymm3 a 1 - esymm3 b 1)
        + (esymm3 a 2 - esymm3 b 2) :=
    sh3_sub_eq_esymm3 a b y
  have hD1 : ((p ^ (k - padicValNat p 6) : ℕ) : ℤ) ∣ esymm3 a 0 - esymm3 b 0 := by
    rw [← e1]; exact hd1
  have hD2 : ((p ^ (k - padicValNat p 6) : ℕ) : ℤ) ∣ esymm3 a 1 - esymm3 b 1 := by
    have hsum : ((p ^ (k - padicValNat p 6) : ℕ) : ℤ)
        ∣ 2 * (y : ℤ) * (esymm3 a 0 - esymm3 b 0) + (esymm3 a 1 - esymm3 b 1) := by
      rw [← e2]; exact hd2
    have hk : ((p ^ (k - padicValNat p 6) : ℕ) : ℤ)
        ∣ 2 * (y : ℤ) * (esymm3 a 0 - esymm3 b 0) :=
      dvd_mul_of_dvd_right hD1 (2 * (y : ℤ))
    have h := dvd_sub hsum hk
    have hs : 2 * (y : ℤ) * (esymm3 a 0 - esymm3 b 0) + (esymm3 a 1 - esymm3 b 1)
        - 2 * (y : ℤ) * (esymm3 a 0 - esymm3 b 0) = esymm3 a 1 - esymm3 b 1 := by ring
    rwa [hs] at h
  have hD3 : ((p ^ (k - padicValNat p 6) : ℕ) : ℤ) ∣ esymm3 a 2 - esymm3 b 2 := by
    have hsum : ((p ^ (k - padicValNat p 6) : ℕ) : ℤ)
        ∣ (y : ℤ) ^ 2 * (esymm3 a 0 - esymm3 b 0) + (y : ℤ) * (esymm3 a 1 - esymm3 b 1)
          + (esymm3 a 2 - esymm3 b 2) := by
      rw [← e3]; exact hd3
    have hk1 : ((p ^ (k - padicValNat p 6) : ℕ) : ℤ)
        ∣ (y : ℤ) ^ 2 * (esymm3 a 0 - esymm3 b 0) :=
      dvd_mul_of_dvd_right hD1 ((y : ℤ) ^ 2)
    have hk2 : ((p ^ (k - padicValNat p 6) : ℕ) : ℤ)
        ∣ (y : ℤ) * (esymm3 a 1 - esymm3 b 1) :=
      dvd_mul_of_dvd_right hD2 (y : ℤ)
    have hrest : ((p ^ (k - padicValNat p 6) : ℕ) : ℤ)
        ∣ (y : ℤ) ^ 2 * (esymm3 a 0 - esymm3 b 0) + (y : ℤ) * (esymm3 a 1 - esymm3 b 1) :=
      dvd_add hk1 hk2
    have h := dvd_sub hsum hrest
    have hs : (y : ℤ) ^ 2 * (esymm3 a 0 - esymm3 b 0) + (y : ℤ) * (esymm3 a 1 - esymm3 b 1)
        + (esymm3 a 2 - esymm3 b 2)
        - ((y : ℤ) ^ 2 * (esymm3 a 0 - esymm3 b 0) + (y : ℤ) * (esymm3 a 1 - esymm3 b 1))
        = esymm3 a 2 - esymm3 b 2 := by ring
    rwa [hs] at h
  have hn1 : p ^ (k - padicValNat p 6) ∣ (esymm3 a 0 - esymm3 b 0).natAbs := by
    simpa using (Int.natAbs_dvd_natAbs).mpr hD1
  have hn2 : p ^ (k - padicValNat p 6) ∣ (esymm3 a 1 - esymm3 b 1).natAbs := by
    simpa using (Int.natAbs_dvd_natAbs).mpr hD2
  have hn3 : p ^ (k - padicValNat p 6) ∣ (esymm3 a 2 - esymm3 b 2).natAbs := by
    simpa using (Int.natAbs_dvd_natAbs).mpr hD3
  rw [contAB]
  exact Nat.dvd_gcd hn1 (Nat.dvd_gcd hn2 hn3)

end Work.LinnikBurgess
