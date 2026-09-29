import Mathlib
import Submission.Work.C17y.adj_setup
import Submission.Work.C17adj.adjoint_divisor_boundC
import Submission.Work.C17y.adj_descent
import Submission.Work.C17adj.Gpoly_eq_Epoly

/-!
# Assembly of `Work.C17y.adjoint_no_solution_rat`

The theorem `Work.C17y.adjoint_no_solution_rat` is the composition of

* the bridge `LBE a b B = Lst a b (B / P₂)` (`adj_setup`), turning the hypothesis of the theorem
  into the adjoint equation for `β = B/P₂`;
* the **divisor bound** over `ℂ` (`Work.C17adj.adjoint_divisor_boundC`): a solution `β` has
  `β·x⁶(x²−1)² = W` a polynomial of degree `≤ 6`;
* the **descent** (`Work.C17adj.divisor_descent`): `β·x⁶(x²−1)² = Npoly n` for some
  `n : Fin 7 → ℚ`;
* the **certificate** (`Work.C17adj.adjoint_clearing` + `Work.C17adj.Gpoly_eq_Epoly` +
  `Work.C17.linear_core`): `n = 0` and `c = 0`.

The certificate `Work.C17.linear_core` is taken as the explicit hypothesis `hcore` of
`adjoint_no_solution_rat_assembly` and supplied in `adjoint_no_solution_rat.lean` from the
self-contained snapshot `Submission/Work/C17y/adj_core.lean` (`Work.C17y.Core.linear_core`),
which is a copy of `Submission/Work/C17/adjoint_core.lean` with the repairs recorded there.
-/

namespace Work.C17y

open Polynomial

noncomputable section

/-- The linear-algebra certificate `Work.C17.linear_core`, as an explicit hypothesis. -/
def CoreHyp : Prop :=
  ∀ (a b : ℚ), Work.C17.AdmQ a b → ∀ (n : Fin 7 → ℚ) (c : Fin 6 → ℚ),
    Work.C17.Gpoly a b n c = 0 → (∀ k : Fin 7, n k = 0) ∧ (∀ i : Fin 6, c i = 0)

/-- **Assembly.**  Given the certificate `hcore`, the theorem `adjoint_no_solution_rat` holds. -/
theorem adjoint_no_solution_rat_assembly (hcore : CoreHyp)
    (a b : ℚ) (hA : Work.C17.AdmQ a b) (B : RatFunc ℚ) (c : Fin 6 → ℚ)
    (h : LBE a b B = ∑ i : Fin 6, ((c i : ℚ) : RatFunc ℚ) * rQ i) :
    B = 0 ∧ c = 0 := by
  classical
  set β : RatFunc ℚ := B / Work.C17.P2Q a b with hβdef
  -- ## 1. the hypothesis, in the shape of the adjoint operator, and with `y^{i-4}·y'` grouped
  have hform : LBE a b B
      = ∑ i : Fin 6, (c i : RatFunc ℚ) * Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ := by
    rw [h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rQ]; ring
  have hβeq : Lst a b β
      = ∑ i : Fin 6, (c i : RatFunc ℚ) * Work.C17.yQ ^ ((i : ℤ) - 4) * Work.C17.dyQ := by
    rw [hβdef]
    exact (LBE_eq_Lst_div a b B).symm.trans hform
  -- ## 2. base change to `ℂ`
  have hC := Work.C17adj.adjoint_base_change a b β c hβeq
  -- ## 3. the divisor bound over `ℂ`, then descent to `ℚ`
  obtain ⟨nC, hnC⟩ := Work.C17adj.adjoint_divisor_boundC a b hA (Work.C17.toC β)
    (fun i => ((c i : ℚ) : ℂ)) hC
  obtain ⟨n, hn⟩ := Work.C17y.divisor_descent β nC hnC
  have hNpoly : β * algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.Npoly n) := by
    rw [hn, Work.C17.Npoly, map_sum]
  have hDadj : (algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj : RatFunc ℚ) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Dadj_ne_zero'
  -- ## 4. the certificate
  have hβform : β = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17.Npoly n)
      / algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj :=
    (eq_div_iff hDadj).mpr hNpoly
  have hEpoly : Work.C17.Epoly a b n c = 0 :=
    Work.C17adj.adjoint_clearing a b n c β hβform hβeq
  have hGpoly : Work.C17.Gpoly a b n c = 0 := by
    rw [Work.C17adj.Gpoly_eq_Epoly]; exact hEpoly
  obtain ⟨hn0, hc0⟩ := hcore a b hA n c hGpoly
  -- ## 5. conclusion
  have hβzero : β = 0 := by
    have hz : β * algebraMap (Polynomial ℚ) (RatFunc ℚ) Work.C17.Dadj = 0 := by
      rw [hNpoly]
      simp [Work.C17.Npoly, hn0]
    exact (mul_eq_zero.mp hz).resolve_right hDadj
  have hBβ : B = Work.C17.P2Q a b * β := by
    rw [hβdef, mul_div_assoc', mul_div_cancel_left₀ _ (P2Q_ne_zero a b)]
  refine ⟨?_, funext fun i => hc0 i⟩
  rw [hBβ, hβzero, mul_zero]

end

end Work.C17y

namespace Work.C17y

/-- Shape check: the certificate `Work.C17.linear_core` (whose statement is `CoreHyp`) can be
passed to `adjoint_no_solution_rat_assembly`. -/
example (hcore : ∀ (a b : ℚ) (hA : Work.C17.AdmQ a b) (n : Fin 7 → ℚ) (c : Fin 6 → ℚ),
      Work.C17.Gpoly a b n c = 0 → (∀ k : Fin 7, n k = 0) ∧ (∀ i : Fin 6, c i = 0))
    (a b : ℚ) (hA : Work.C17.AdmQ a b) (B : RatFunc ℚ) (c : Fin 6 → ℚ)
    (h : LBE a b B = ∑ i : Fin 6, ((c i : ℚ) : RatFunc ℚ) * rQ i) : B = 0 ∧ c = 0 :=
  adjoint_no_solution_rat_assembly (fun a b hA n c hG => hcore a b hA n c hG) a b hA B c h

end Work.C17y
