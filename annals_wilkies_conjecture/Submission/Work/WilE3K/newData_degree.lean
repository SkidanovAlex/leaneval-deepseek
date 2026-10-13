/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): degree bookkeeping of one
  Khovanskii–Rolle elimination step `E ↦ E.newData y δ`.

  One elimination step (`Submission.Work.WilE3K/Elim.lean`) replaces the eliminated `arctan`
  equation by the *Rolle determinant* equation `E.rolleDetP - δ · E.prodPoly = 0` and the `n`
  exp-affine equations `E.G i` by themselves shifted by the value `y` of the remaining system, so
  the new system `E.newData y δ` has `n + 1` polynomial equations on the same ambient space.

  This file bounds the *degree sum* of the new system by `(N + 8)` times the old degree sum (plus
  the number `rt` of surviving `arctan` equations) — the input the recursion `ETB` needs.

  The assembly is the determinant estimate §1: every entry of the scaled Rolle matrix `E.rolleMatP`
  has total degree `≤ 2` on an `arctan` row and `≤ (E.G i).totalDegree` on the row of `E.G i`, so
  the determinant — a signed sum over permutations of products of one entry per *column* — has
  total degree at most `(N + 1) · (∑_i atomDeg (E.G i) + 2)`.  The two entry bounds, the degree of
  the scaling factor product `E.prodPoly` and the degree of the carried-over shifted equations are
  proved in the companion files

  * `Work.WilE3K.dTanPoly_totalDegree_le`,
  * `Work.WilE3K.dPoly_totalDegree_le`,
  * `Work.WilE3K.prodPoly_totalDegree_le`,
  * `Work.WilE3K.atomDeg_newG_succ_le`.
-/
import Mathlib
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE2.Lift
import Submission.Work.WilE3K.dTanPoly_totalDegree_le
import Submission.Work.WilE3K.dPoly_totalDegree_le
import Submission.Work.WilE3K.prodPoly_totalDegree_le
import Submission.Work.WilE3K.atomDeg_newG_succ_le

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

namespace ETData

variable {N rt n re : ℕ}

/-! ## §1. Degree of the Rolle determinant -/

/-- **Degree of the Rolle determinant.**  Every entry of `E.rolleMatP` has total degree `≤ 2` on an
`arctan` row (`Work.WilE3K.dTanPoly_totalDegree_le`) and `≤ (E.G i).totalDegree` on the row of
`E.G i` (`Work.WilE3K.dPoly_totalDegree_le`), and `(E.G i).totalDegree + 1 = atomDeg (E.G i)` is at
most `∑_k atomDeg (E.G k)`.  A determinant is a signed sum of products of one entry per column, so
its total degree is at most the number `N + 1` of columns times that column bound
(`Work.WilE2.Matrix.det_totalDegree_le`). -/
theorem totalDegree_rolleDetP_le (E : ETData N (rt + 1) n re) :
    (E.rolleDetP).totalDegree ≤ (N + 1) * ((∑ i, atomDeg (E.G i)) + 2) := by
  classical
  have hD : ∀ i : Fin n, (E.G i).totalDegree ≤ ∑ k, atomDeg (E.G k) := by
    intro i
    have h1 : atomDeg (E.G i) ≤ ∑ k : Fin n, atomDeg (E.G k) :=
      Finset.single_le_sum (s := Finset.univ) (f := fun k : Fin n => atomDeg (E.G k))
        (fun k _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [atomDeg] at h1
    omega
  have key : ∀ r c : Fin (N + 1),
      (E.rolleMatP r c).totalDegree ≤ (∑ i, atomDeg (E.G i)) + 2 := by
    intro r c
    rw [rolleMatP]
    simp only [Matrix.of_apply]
    by_cases hr : (r : ℕ) < rt + 1
    · rw [dite_eq_left hr]
      have h1 := Work.WilE3K.dTanPoly_totalDegree_le E (E.tanIndex r hr) c
      omega
    · rw [dite_eq_right hr]
      have h1 := Work.WilE3K.dPoly_totalDegree_le E c (E.G (E.freeIndex r (not_lt.mp hr)))
      have h2 := hD (E.freeIndex r (not_lt.mp hr))
      omega
  have hdet := Work.WilE2.Matrix.det_totalDegree_le E.rolleMatP
    (fun _ : Fin (N + 1) => (∑ i, atomDeg (E.G i)) + 2) key
  rw [rolleDetP]
  refine hdet.trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]

/-! ## §2. The new Rolle equation -/

/-- The new equation `E.rolleDetP - C δ * E.prodPoly` at index `0` of `E.newG`: the degree of the
Rolle determinant, plus the degree `2 (rt + 1)` of the scaling factor product. -/
theorem atomDeg_newG_zero_le (E : ETData N (rt + 1) n re) (y : Fin N → ℝ) (δ : ℝ) :
    atomDeg (E.newG y δ 0) ≤
      (N + 1) * ((∑ i, atomDeg (E.G i)) + 2) + 2 * (rt + 1) + 1 := by
  have h0 : E.newG y δ 0 = E.rolleDetP - MvPolynomial.C δ * E.prodPoly := by
    rw [newG]
    rw [dite_eq_left (show ((0 : Fin (n + 1)) : ℕ) = 0 from rfl)]
  rw [h0, atomDeg]
  have hprod : (MvPolynomial.C δ * E.prodPoly : EAPoly (N + 1) re).totalDegree ≤ 2 * (rt + 1) := by
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, Nat.zero_add]
    exact Work.WilE3K.prodPoly_totalDegree_le E
  have hsub : (E.rolleDetP - MvPolynomial.C δ * E.prodPoly : EAPoly (N + 1) re).totalDegree
      ≤ (N + 1) * ((∑ i, atomDeg (E.G i)) + 2) + 2 * (rt + 1) := by
    rw [sub_eq_add_neg]
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (E.totalDegree_rolleDetP_le).trans (Nat.le_add_right _ _)
    · rw [MvPolynomial.totalDegree_neg]
      exact hprod.trans (Nat.le_add_left _ _)
  omega

/-! ## §3. The arithmetic of the recursion step -/

/-- The numerical inequality behind the recursion step `(N, D) ↦ (N + 1, (N + 9) (D + 11))`:
all the slack sits in the factor `N + 8`. -/
theorem degree_arith (S N rt : ℕ) :
    (N + 1) * (S + 2) + 2 * (rt + 1) + 1 + S + rt ≤ (N + 8) * (S + (rt + 1) + 8) := by
  nlinarith [Nat.zero_le S, Nat.zero_le N, Nat.zero_le rt]

end ETData

/-- **Degree of one elimination step.**  The `n + 1` polynomial equations of `E.newData y δ` are
the Rolle equation `E.rolleDetP - C δ * E.prodPoly` and the `n` shifted old equations `E.G i - C y`
(`Work.WilE3K.atomDeg_newG_succ_le`); their degree sum grows by at most the factor `N + 8`. -/
theorem newData_degree {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re)
    (y : Fin N → ℝ) (δ : ℝ) :
    (∑ i, WilkiesDesign.E.atomDeg ((E.newData y δ).G i)) + rt ≤
      (N + 8) * ((∑ i, WilkiesDesign.E.atomDeg (E.G i)) + (rt + 1) + 8) := by
  rw [Fin.sum_univ_succ]
  refine (add_le_add (add_le_add ?_ ?_) le_rfl).trans (ETData.degree_arith _ N rt)
  · exact ETData.atomDeg_newG_zero_le E y δ
  · exact Finset.sum_le_sum (fun i _ => Work.WilE3K.atomDeg_newG_succ_le E y δ i)

end Work.WilE3K
