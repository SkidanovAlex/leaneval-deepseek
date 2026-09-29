import Mathlib
import Submission.Work.ZeroEst.case_det_order_sum
import Submission.Work.ZeroEst.case_det

namespace Work.ZeroEst2

/-!
# Order bound for a relation `d · g = Σₖ Lₖ · Rₖ`

Given power series `R : Fin r → ℚ⟦X⟧`, a nonzero series `g` of order `≤ N` and a nonzero
polynomial `d`, together with a relation `d · g = Σₖ Lₖ · Rₖ` (all `Lₖ` polynomials) and the
"descending order" hypothesis

`ord (R k₀) - (k - k₀) ≤ ord (R k)`  for all `k`,

the order of `R k₀` is bounded by `(r-1) + natDegree d + N`.

The argument is order arithmetic only: the left-hand side `d · g` has order
`ord d + ord g ≤ natDegree d + N`, while every summand `Lₖ · Rₖ` has order at least
`ord (R k₀) - (r - 1)`, since `ord (R k) ≥ ord (R k₀) - (k - k₀)` and `(k - k₀) ≤ r - 1`
plus `ord (L k) ≥ 0`.  The order of a sum dominates the minimum of the orders of its
summands (`Work.ZeroEst.case_det_order_sum`), which gives
`ord (R k₀) - (r-1) ≤ natDegree d + N`.
-/

/-- Order bound for the "Cramer" relation `d · g = ∑ₖ Lₖ · Rₖ` under a descending order
hypothesis on the `Rₖ`. -/
theorem order_bound_cramer {r : ℕ} (R : Fin r → PowerSeries ℚ) (g : PowerSeries ℚ)
    (d : Polynomial ℚ) (L : Fin r → Polynomial ℚ) (N : ℕ) (k₀ : Fin r)
    (hd : d ≠ 0) (hg : g ≠ 0) (hN : g.order ≤ (N : ℕ∞))
    (hord : ∀ k : Fin r,
      (((R k₀).order.toNat - ((k : ℕ) - (k₀ : ℕ)) : ℕ) : ℕ∞) ≤ (R k).order)
    (hid : (d : PowerSeries ℚ) * g = ∑ k, (L k : PowerSeries ℚ) * R k) :
    (R k₀).order.toNat ≤ (r - 1) + d.natDegree + N := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · -- `Fin 0` is empty
    subst hr
    exact Fin.elim0 k₀
  · -- upper bound on the order of the left-hand side `d · g`
    have hkey : ((d : PowerSeries ℚ) * g).order ≤ ((d.natDegree + N : ℕ) : ℕ∞) := by
      rw [PowerSeries.order_mul]
      calc (d : PowerSeries ℚ).order + g.order
          ≤ ((d.natDegree : ℕ) : ℕ∞) + (N : ℕ∞) :=
            add_le_add (Work.ZeroEst.order_coe_toNat_le d hd) hN
        _ = ((d.natDegree + N : ℕ) : ℕ∞) := by push_cast; ring
    -- lower bound on the order of the right-hand side, term by term
    have hlow : (((R k₀).order.toNat - (r - 1) : ℕ) : ℕ∞) ≤
        ((d : PowerSeries ℚ) * g).order := by
      rw [hid]
      refine Work.ZeroEst.case_det_order_sum Finset.univ
        (fun k : Fin r => (L k : PowerSeries ℚ) * R k)
        (((R k₀).order.toNat - (r - 1) : ℕ) : ℕ∞) ?_
      intro k _
      have hsub : (R k₀).order.toNat - (r - 1) ≤
          (R k₀).order.toNat - ((k : ℕ) - (k₀ : ℕ)) := by
        refine Nat.sub_le_sub_left ?_ _
        exact le_trans (Nat.sub_le _ _) (Nat.le_sub_one_of_lt k.isLt)
      calc (((R k₀).order.toNat - (r - 1) : ℕ) : ℕ∞)
          ≤ (((R k₀).order.toNat - ((k : ℕ) - (k₀ : ℕ)) : ℕ) : ℕ∞) := by exact_mod_cast hsub
        _ = (0 : ℕ∞) + (((R k₀).order.toNat - ((k : ℕ) - (k₀ : ℕ)) : ℕ) : ℕ∞) := by simp
        _ ≤ ((L k : PowerSeries ℚ)).order + (R k).order :=
            add_le_add (zero_le) (hord k)
        _ ≤ ((L k : PowerSeries ℚ) * R k).order := PowerSeries.le_order_mul _ _
    have hfin := ENat.natCast_le_natCast.mp (le_trans hlow hkey)
    omega

end Work.ZeroEst2
