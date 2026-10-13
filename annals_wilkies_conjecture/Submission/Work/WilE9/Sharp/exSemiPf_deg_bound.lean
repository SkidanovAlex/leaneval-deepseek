import Mathlib
import Submission.Work.WilE9.Sharp.ExtSystem
import Submission.Work.WilE9.Deg.iftP_totalDegree_le
import Submission.Work.WilE9.Sharp.clearNumDen_totalDegree_le
import Submission.Work.WilE9.Sharp.ExConsts
import Submission.Work.WilE9.Sharp.exSemiPf_bounds

/-
  `exSemiPf_deg_bound`: the degree of the extended semi-Pfaffian system, bounded by a polynomial
  in `(D, |L|, a₀)` where `D` is an *external* degree budget: the hypotheses are only `E.deg ≤ D`
  and `E.X.basics.length ≤ D + 1` (the number of disjuncts of the stratum is bounded by the
  budget, not by `E.deg + 1` as in `exSemiPf_bounds`).

  The estimate is `(exSemiPf n m E L).deg ≤ A3 n a₀ * (D+1)² * (|L|+1)`, i.e. the polynomial
  `Submission.Work.WilE9.Sharp.ExConsts.A3 n a₀ * (1+X₀)² (1+X₁)`.

  The ingredients are those of `Submission.Work.WilE9.Sharp.exSemiPf_bounds`:

  * `exBasic_deg_le`: one disjunct of the extended system has degree at most
    `5n + 10 + ∑_a atomDeg (h a) + atomDeg (exEq6 …) + B.deg`;
  * `atomDeg_exEq6_le`: the cleared equation has atom degree `≤ A2 n a₀ * (E.deg+2) * (|L|+1)`
    (`m` enters only through `m ≤ a₀`), whose proof rests on the degree bounds of `pbF`
    (`pbF_totalDegree_le`), of `pbQ` (`Deg.jQ_totalDegree_le`), of `pbP` (`Deg.iftP_totalDegree_le`)
    and of `clearPb` (`clearPb_totalDegree_le`);
  * `arith_bound`: the final numerical estimate with `D` in place of `E.deg`.

  Since `E.X.deg ≤ E.deg` and `E.deg ≤ D`, replacing every occurrence of `E.deg` by `D` (and the
  number of disjuncts by `D + 1`) only weakens the estimate.
-/
set_option maxHeartbeats 1000000

namespace Work.WilE9.Sharp

open WilkiesDesign WilkiesDesign.E

theorem exSemiPf_deg_bound (n a₀ : ℕ) : ∃ b : MvPolynomial (Fin 3) ℕ,
    ∀ (m : ℕ) (E : Work.WilE9.Sharp.EffStratum n m) (L : List (Fin n)) (D : ℕ),
      m ≤ a₀ → E.X.fmt ≤ a₀ → E.deg ≤ D → E.X.basics.length ≤ D + 1 →
      (Work.WilE9.Sharp.exSemiPf n m E L).deg ≤ b.eval ![D, L.length, a₀] := by
  refine ⟨MvPolynomial.C (A3 n a₀) * (1 + MvPolynomial.X (0 : Fin 3)) ^ 2
    * (1 + MvPolynomial.X (1 : Fin 3)), ?_⟩
  intro m E L D hm hfmt hD hlen
  -- the value of the polynomial at `![D, |L|, a₀]`
  have hEval : MvPolynomial.eval ![D, L.length, a₀]
      (MvPolynomial.C (A3 n a₀) * (1 + MvPolynomial.X (0 : Fin 3)) ^ 2
        * (1 + MvPolynomial.X (1 : Fin 3)))
      = A3 n a₀ * (D + 1) ^ 2 * (L.length + 1) := by
    simp [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_add,
      MvPolynomial.eval_X]
    ring
  rw [hEval]
  -- the two structural degree budgets of the stratum and of the cleared equation
  set S0 : ℕ := ∑ a : Fin (1 + m), atomDeg (E.h a) with hS0def
  set U : ℕ := atomDeg (exEq6 E.X.c E.h L) with hUdef
  have hS0_le : S0 ≤ E.deg := by rw [hS0def, EffStratum.deg]; omega
  have hXdegle : E.X.deg ≤ E.deg := by rw [EffStratum.deg]; omega
  have hXdegD : E.X.deg ≤ D := hXdegle.trans hD
  have hU_le : U ≤ A2 n a₀ * (E.deg + 2) * (L.length + 1) := by
    rw [hUdef]; exact atomDeg_exEq6_le n m a₀ E L hm
  have hUD : U ≤ A2 n a₀ * (D + 2) * (L.length + 1) := by
    refine hU_le.trans ?_
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega : E.deg + 2 ≤ D + 2))
  -- the degree of the extended system is the sum of the degrees of its disjuncts
  have hdeg_eq : (exSemiPf n m E L).deg
      = (E.X.basics.map (fun B => (exBasic E.X.c E.h L B).deg)).sum := by
    rw [SemiPf.deg, exSemiPf, List.map_map]; rfl
  have hsum : (E.X.basics.map (fun B => (exBasic E.X.c E.h L B).deg)).sum
      ≤ (E.X.basics.map (fun B => 5 * n + 10 + S0 + U + B.deg)).sum :=
    List.sum_le_sum (fun B _ => exBasic_deg_le E.X.c E.h L B S0 (le_of_eq hS0def.symm))
  have hsum2 : (E.X.basics.map (fun B => 5 * n + 10 + S0 + U + B.deg)).sum
      = E.X.basics.length * (5 * n + 10 + S0 + U) + E.X.deg := by
    rw [sum_map_add_const]
    rw [show (E.X.basics.map (fun B => B.deg)).sum = E.X.deg from rfl]
  rw [hdeg_eq]
  calc (E.X.basics.map (fun B => (exBasic E.X.c E.h L B).deg)).sum
      ≤ (E.X.basics.map (fun B => 5 * n + 10 + S0 + U + B.deg)).sum := hsum
    _ = E.X.basics.length * (5 * n + 10 + S0 + U) + E.X.deg := hsum2
    _ ≤ (D + 1) * (5 * n + 10 + D + U) + D := by
        have hc : 5 * n + 10 + S0 + U ≤ 5 * n + 10 + D + U := by omega
        have h1 : E.X.basics.length * (5 * n + 10 + S0 + U)
            ≤ (D + 1) * (5 * n + 10 + D + U) := Nat.mul_le_mul hlen hc
        omega
    _ ≤ (D + 1) * (5 * n + 10 + D + A2 n a₀ * (D + 2) * (L.length + 1)) + D :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_left hUD _)) _
    _ ≤ A3 n a₀ * (D + 1) ^ 2 * (L.length + 1) := arith_bound n a₀ D L.length

end Work.WilE9.Sharp
