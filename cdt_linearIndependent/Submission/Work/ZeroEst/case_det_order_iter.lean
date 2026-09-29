import Mathlib
import Submission.Work.ZeroEst.one_var_defs

/-!
# Area Z: order drop under iterated `θ = q · d/dx`

`θ = q · d/dx` lowers the order of a power series by at most one at each application
(`Work.ZeroEst.order_theta_ge`, i.e. `ord S - 1 ≤ ord (θ S)`).  Iterating `k` times gives

`ord R - k ≤ ord (θᵏ R)`,

which in terms of `order.toNat` is exactly the statement proved here:

`((R.order.toNat - k : ℕ) : ℕ∞) ≤ (θ^[k] R).order`.

Note the convention of Mathlib's `PowerSeries.order`: `order 0 = ⊤`, so that
`order.toNat = 0` for the zero series; both the zero case and the case of a genuine
order are handled.
-/

namespace Work.ZeroEst

open PowerSeries Polynomial

/-- One step: if `↑a ≤ S.order`, then `↑(a - 1) ≤ (q · S').order`.  The hypothesis is kept in
the `ℕ∞`-coefficient form because that is what the induction below produces. -/
lemma order_iter_step (q : Polynomial ℚ) (S : ℚ⟦X⟧) (a : ℕ) (h : (a : ℕ∞) ≤ S.order) :
    ((a - 1 : ℕ) : ℕ∞) ≤ ((q : ℚ⟦X⟧) * PowerSeries.derivative (R := ℚ) S).order := by
  rcases eq_or_ne S 0 with hS | hS
  · subst hS; simp
  · have hc := PowerSeries.coe_toNat_order hS
    have h1 : (a : ℕ∞) ≤ (S.order.toNat : ℕ∞) := by rw [← hc] at h; exact h
    have ha : a ≤ S.order.toNat := by exact_mod_cast h1
    have key : ((S.order.toNat - 1 : ℕ) : ℕ∞) = (↑S.order.toNat : ℕ∞) - 1 :=
      ENat.natCast_sub _ 1
    calc ((a - 1 : ℕ) : ℕ∞) ≤ ((S.order.toNat - 1 : ℕ) : ℕ∞) := by
          exact_mod_cast (Nat.sub_le_sub_right ha 1)
      _ = (↑S.order.toNat : ℕ∞) - 1 := key
      _ = S.order - 1 := by rw [hc]
      _ ≤ (↑q * (PowerSeries.derivative (R := ℚ)) S).order := order_theta_ge q S

/-- `ord (θᵏ R) ≥ ord R - k`, in `order.toNat` form. -/
theorem case_det_order_iter (q : Polynomial ℚ) (R : PowerSeries ℚ) (k : ℕ) :
    ((R.order.toNat - k : ℕ) : ℕ∞) ≤
      ((fun S => (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) S)^[k] R).order := by
  induction k with
  | zero =>
      rcases eq_or_ne R 0 with h | h
      · subst h; simp
      · simpa using (le_of_eq (PowerSeries.coe_toNat_order h) : (↑R.order.toNat : ℕ∞) ≤ R.order)
  | succ k ih =>
      have h := order_iter_step q
        ((fun S => (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) S)^[k] R)
        (R.order.toNat - k) ih
      rw [Function.iterate_succ_apply', ← Nat.sub_sub]
      exact h

end Work.ZeroEst
