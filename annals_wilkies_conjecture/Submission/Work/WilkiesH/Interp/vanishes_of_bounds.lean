import Mathlib
import Submission.Work.WilkiesH.Defs
import Submission.Work.WilkiesH.NT.abs_eval_ge_of_ne_zero

/-!
# Area I — the Liouville comparison of the interpolation step

This is the last, purely arithmetic step of BNZ Prop. 6.1: if a nonzero integer polynomial `P`
of degree `≤ d` with coefficients bounded by `N` satisfies, at a point `y'` near the chart,

* the *upper* bound `|P y'| ≤ Tm` (the Taylor bound, `Interp.poly_comp_taylor_bound`),
* the *Lipschitz* bound `|P y - P y'| ≤ G` (from `‖∇P‖ ≤ gradB`),

and `Tm + G` is smaller than the Liouville lower bound
`liouB = 1 / (monoCount (μ+1) d · N · H^{((μ+1)+1)·d·g})^g`,
then `P y = 0` for every `y` of degree `≤ g` and height `≤ H`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Interp

open WilkiesConjecture

/-- **The Liouville comparison.**  A nonzero integral polynomial of degree `≤ d` and
coefficients `≤ N` which is small at `y'` and `G`-close there to `y` must vanish at `y`,
provided `Tm + G` is below the Liouville bound for degree-`≤ g`, height-`≤ H` points. -/
theorem vanishes_of_bounds {μ d g H N : ℕ} (hH1 : 1 ≤ H) (hN1 : 1 ≤ N)
    (P : MvPolynomial (Fin (μ + 1)) ℤ) (hPne : P ≠ 0) (hdeg : P.totalDegree ≤ d)
    (hcoef : ∀ m ∈ P.support, |(P.coeff m : ℤ)| ≤ (N : ℤ))
    {y y' : Fin (μ + 1) → ℝ}
    (hy : y ∈ WilkiesConjecture.degreeHeightLE Set.univ g H)
    {Tm G : ℝ}
    (hT : |MvPolynomial.eval y' (P.map (Int.castRingHom ℝ))| ≤ Tm)
    (hG : |MvPolynomial.eval y (P.map (Int.castRingHom ℝ))
        - MvPolynomial.eval y' (P.map (Int.castRingHom ℝ))| ≤ G)
    (hineq : Tm + G < 1
      / ((Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (N : ℝ)
          * (H : ℝ) ^ (((μ + 1) + 1) * d * g)) ^ g) :
    MvPolynomial.eval y (P.map (Int.castRingHom ℝ)) = 0 := by
  by_contra hne
  obtain ⟨-, hint, hfin, hheight⟩ := hy
  have hliou := Work.WilkiesH.NT.abs_eval_ge_of_ne_zero (n := μ + 1) (d := d) (N := N)
    (g := g) (H := H) (Nat.succ_le_succ (Nat.zero_le μ)) hN1 hH1 P hdeg hcoef hint hfin hheight hne
  have hval : |MvPolynomial.eval y (P.map (Int.castRingHom ℝ))|
      ≤ |MvPolynomial.eval y' (P.map (Int.castRingHom ℝ))|
        + |MvPolynomial.eval y (P.map (Int.castRingHom ℝ))
            - MvPolynomial.eval y' (P.map (Int.castRingHom ℝ))| := by
    have h := abs_add_le (MvPolynomial.eval y' (P.map (Int.castRingHom ℝ)))
      (MvPolynomial.eval y (P.map (Int.castRingHom ℝ))
        - MvPolynomial.eval y' (P.map (Int.castRingHom ℝ)))
    simpa using h
  have h2 : |MvPolynomial.eval y (P.map (Int.castRingHom ℝ))| ≤ Tm + G :=
    le_trans hval (add_le_add hT hG)
  exact absurd (lt_of_le_of_lt (le_trans hliou h2) hineq) (lt_irrefl _)

end Work.WilkiesH.Interp
