/-
The "crack family": the one-parameter family of Descartes quadruples obtained by
alternately applying the two moves that keep a fixed tangent pair of coordinates.
If v = (a, b, c, d) is a Descartes quadruple, the quadruples obtained by
alternating the moves at coordinates 2 and 3 (starting with coordinate 2) are
    (a, b, f(0), f(1)), (a, b, f(2), f(3)), (a, b, f(4), f(5)), ...
where f(x) = (a+b)x² − (a+b+c−d)x + c   (the paper's Lemma "crackfamily").
-/
import Submission.Apollo.Defs
import Submission.Apollo.Descartes
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
open scoped Pointwise
open LocalGlobalApollonianCirclePackings

namespace Apollo

/-- the orbit is closed under every generator (S-move). -/
lemma gen_smul_mem_apOrbit (v : Fin 4 → ℤ) (hv : v ∈ apOrbit) (i : Fin 4) :
    gen i • v ∈ apOrbit := by
  rcases hv with ⟨g, hg, rfl⟩
  change ∃ g' : GL (Fin 4) ℤ, g' ∈ ApollonianGroup ∧ gen i • (g • q0v) = g' • q0v
  refine ⟨gen i * g, ?_⟩
  constructor
  · rw [apollonianGroup_eq_closure]
    have hgi : gen i ∈ Subgroup.closure gens :=
      Subgroup.subset_closure (k := gens) ⟨i, rfl⟩
    exact Subgroup.mul_mem (Subgroup.closure gens) hgi (by simpa [apollonianGroup_eq_closure] using hg)
  · rw [mul_smul]

/-- crack-family quadratic attached to the quadruple v with fixed pair of indices 0,1. -/
def crackPoly (v : Fin 4 → ℤ) (x : ℤ) : ℤ :=
  (v 0 + v 1) * x ^ 2 - (v 0 + v 1 + v 2 - v 3) * x + v 2

@[simp] lemma crackPoly_zero (v : Fin 4 → ℤ) : crackPoly v 0 = v 2 := by
  simp [crackPoly]

@[simp] lemma crackPoly_one (v : Fin 4 → ℤ) : crackPoly v 1 = v 3 := by
  simp [crackPoly]
  ring

/-- f(2t+2) = 2(a+b+f(2t+1)) - f(2t)  (pure algebra). -/
lemma crackPoly_inc2 (v : Fin 4 → ℤ) (t : ℤ) :
    crackPoly v (2 * t + 2) = 2 * (v 0 + v 1 + crackPoly v (2 * t + 1)) - crackPoly v (2 * t) := by
  unfold crackPoly
  ring

/-- f(2t+3) = 2(a+b+f(2t+2)) - f(2t+1)  (pure algebra). -/
lemma crackPoly_inc2b (v : Fin 4 → ℤ) (t : ℤ) :
    crackPoly v (2 * t + 3) = 2 * (v 0 + v 1 + crackPoly v (2 * t + 2)) - crackPoly v (2 * t + 1) := by
  unfold crackPoly
  ring

/-- the sequence of quadruples moving only coordinates 2 and 3, first coordinate 2. -/
def crackSeq (v : Fin 4 → ℤ) : ℕ → Fin 4 → ℤ
| 0 => v
| n + 1 => gen 3 • (gen 2 • crackSeq v n)

/-- moving coordinates 2 and 3 leaves coordinate 0 unchanged. -/
lemma crackSeq_fix0 (v : Fin 4 → ℤ) (n : ℕ) : crackSeq v n 0 = v 0 := by
  induction n with
  | zero => simp [crackSeq]
  | succ n ih =>
      rw [crackSeq, gen_smul_apply, if_neg, gen_smul_apply, if_neg]
      · exact ih
      · decide
      · decide

/-- moving coordinates 2 and 3 leaves coordinate 1 unchanged. -/
lemma crackSeq_fix1 (v : Fin 4 → ℤ) (n : ℕ) : crackSeq v n 1 = v 1 := by
  induction n with
  | zero => simp [crackSeq]
  | succ n ih =>
      rw [crackSeq, gen_smul_apply, if_neg, gen_smul_apply, if_neg]
      · exact ih
      · decide
      · decide

/-- coordinates 2 and 3 follow the quadratic f (joint induction). -/
lemma crackSeq23 (v : Fin 4 → ℤ) (n : ℕ) :
    crackSeq v n 2 = crackPoly v (2 * (n : ℤ)) ∧
      crackSeq v n 3 = crackPoly v (2 * (n : ℤ) + 1) := by
  induction n with
  | zero => simp [crackSeq]
  | succ n ih =>
      rw [crackSeq]
      have harg : 2 * (↑(n + 1) : ℤ) = 2 * (↑n : ℤ) + 2 := by omega
      have harg3 : 2 * (↑(n + 1) : ℤ) + 1 = 2 * (↑n : ℤ) + 3 := by omega
      -- values of gen 2 • u at coordinates 0..3
      have g0 : (gen 2 • crackSeq v n) 0 = v 0 := by
        rw [gen_smul_apply]
        rw [if_neg (show (0 : Fin 4) ≠ 2 by decide)]
        exact crackSeq_fix0 v n
      have g1 : (gen 2 • crackSeq v n) 1 = v 1 := by
        rw [gen_smul_apply]
        rw [if_neg (show (1 : Fin 4) ≠ 2 by decide)]
        exact crackSeq_fix1 v n
      have a2 : (gen 2 • crackSeq v n) 2 = crackPoly v (2 * (↑n : ℤ) + 2) := by
        rw [gen_smul_apply]
        rw [if_pos rfl]
        rw [Fin.sum_univ_four]
        simp [crackSeq_fix0 v n, crackSeq_fix1 v n, ih.1, ih.2]
        rw [crackPoly_inc2 v (↑n : ℤ)]
        ring
      have a3 : (gen 2 • crackSeq v n) 3 = crackPoly v (2 * (↑n : ℤ) + 1) := by
        rw [gen_smul_apply]
        rw [if_neg (show (3 : Fin 4) ≠ 2 by decide)]
        exact ih.2
      constructor
      · rw [gen_smul_apply]
        rw [if_neg (show (2 : Fin 4) ≠ 3 by decide)]
        rw [harg]
        exact a2
      · rw [gen_smul_apply]
        rw [if_pos rfl]
        rw [harg3]
        rw [Fin.sum_univ_four]
        simp [g0, g1, a2, a3]
        rw [crackPoly_inc2b v (↑n : ℤ)]
        ring

/-- coordinates 0 and 1 are fixed and 2,3 move along f. -/
theorem crackSeq_family (v : Fin 4 → ℤ) (n : ℕ) (i : Fin 4) :
    crackSeq v n i =
      if i = 0 then v 0 else if i = 1 then v 1
      else if i = 2 then crackPoly v (2 * (n : ℤ))
      else crackPoly v (2 * (n : ℤ) + 1) := by
  fin_cases i <;> simp [crackSeq_fix0, crackSeq_fix1, (crackSeq23 v n).1, (crackSeq23 v n).2]

/-- Every element of the crack family is Descartes whenever v is. -/
lemma crackSeq_descarates (v : Fin 4 → ℤ)
    (hv : (∑ j : Fin 4, v j) ^ 2 = 2 * ∑ j : Fin 4, (v j) ^ 2) (n : ℕ) :
    (∑ j : Fin 4, crackSeq v n j) ^ 2 = 2 * ∑ j : Fin 4, (crackSeq v n j) ^ 2 := by
  induction n with
  | zero => simpa [crackSeq] using hv
  | succ n ih =>
      change (∑ j : Fin 4, (gen 3 • (gen 2 • crackSeq v n)) j) ^ 2 =
        2 * ∑ j : Fin 4, ((gen 3 • (gen 2 • crackSeq v n)) j) ^ 2
      exact gen_smul_descarates 3 (gen 2 • crackSeq v n) (gen_smul_descarates 2 (crackSeq v n) ih)

/-- The crack family stays inside the orbit: if v ∈ apOrbit then crackSeq v n ∈ apOrbit. -/
lemma crackSeq_mem_apOrbit (v : Fin 4 → ℤ) (hv : v ∈ apOrbit) (n : ℕ) :
    crackSeq v n ∈ apOrbit := by
  induction n with
  | zero => simpa [crackSeq] using hv
  | succ n ih =>
      have h1 : gen 2 • crackSeq v n ∈ apOrbit := gen_smul_mem_apOrbit (crackSeq v n) ih 2
      simpa [crackSeq] using (gen_smul_mem_apOrbit (gen 2 • crackSeq v n) h1 3)


/-- each S-move is an involution. -/
lemma gen_smul_gen_smul (w : Fin 4 → ℤ) (i : Fin 4) : gen i • (gen i • w) = w := by
  rw [← mul_smul]
  have h : (gen i) * gen i = 1 := by
    fin_cases i <;> decide
  simpa [h] using (one_smul (GL (Fin 4) ℤ) w)

end Apollo
