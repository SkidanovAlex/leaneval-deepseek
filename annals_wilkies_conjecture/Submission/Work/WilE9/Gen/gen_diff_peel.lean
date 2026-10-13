/-
  Work.WilE9.Gen.gen_diff_peel — peeling the `snoc`/`snocIt` layers of the chain points, and
  the total-degree bounds of the atoms of `gen_diff_defs`.
-/
import Submission.Work.WilE9.Gen.gen_diff_defs

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical Topology
namespace Work.WilE9.Gen

namespace DiffSet

open WilkiesDesign WilkiesDesign.E

/-! ## 3. Peeling one `snoc` / `snocIt` layer -/

lemma snoc_dvI5 (n : ℕ) (w : Fin (n + 1) → ℝ) (ε : ℝ) (k : Fin (n + 1)) :
    (Fin.snoc w ε : Fin (dd5 n) → ℝ) (dvI5 n k) = w (dvI6 n k) := by
  rw [dvI5]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) ε w (dvI6 n k)

lemma snoc_deI5 (n : ℕ) (w : Fin (n + 1) → ℝ) (ε : ℝ) :
    (Fin.snoc w ε : Fin (dd5 n) → ℝ) (deI5 n) = ε := by
  rw [deI5]
  exact Fin.snoc_last (α := fun _ => ℝ) ε w

lemma snoc_dvI4 (n : ℕ) (P : Fin (dd5 n) → ℝ) (δ : ℝ) (k : Fin (n + 1)) :
    (Fin.snoc P δ : Fin (dd4 n) → ℝ) (dvI4 n k) = P (dvI5 n k) := by
  rw [dvI4]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) δ P (dvI5 n k)

lemma snoc_ddI4 (n : ℕ) (P : Fin (dd5 n) → ℝ) (δ : ℝ) :
    (Fin.snoc P δ : Fin (dd4 n) → ℝ) (ddI4 n) = δ := by
  rw [ddI4]
  exact Fin.snoc_last (α := fun _ => ℝ) δ P

lemma snoc_deI4 (n : ℕ) (P : Fin (dd5 n) → ℝ) (δ : ℝ) :
    (Fin.snoc P δ : Fin (dd4 n) → ℝ) (deI4 n) = P (deI5 n) := by
  rw [deI4]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) δ P (deI5 n)

lemma snoc_dvI3 (n : ℕ) (P : Fin (dd4 n) → ℝ) (h : ℝ) (k : Fin (n + 1)) :
    (Fin.snoc P h : Fin (dd3 n) → ℝ) (dvI3 n k) = P (dvI4 n k) := by
  rw [dvI3]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) h P (dvI4 n k)

lemma snoc_dhI3 (n : ℕ) (P : Fin (dd4 n) → ℝ) (h : ℝ) :
    (Fin.snoc P h : Fin (dd3 n) → ℝ) (dhI3 n) = h := by
  rw [dhI3]
  exact Fin.snoc_last (α := fun _ => ℝ) h P

lemma snoc_ddI3 (n : ℕ) (P : Fin (dd4 n) → ℝ) (h : ℝ) :
    (Fin.snoc P h : Fin (dd3 n) → ℝ) (ddI3 n) = P (ddI4 n) := by
  rw [ddI3]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) h P (ddI4 n)

lemma snoc_deI3 (n : ℕ) (P : Fin (dd4 n) → ℝ) (h : ℝ) :
    (Fin.snoc P h : Fin (dd3 n) → ℝ) (deI3 n) = P (deI4 n) := by
  rw [deI3]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) h P (deI4 n)

lemma snocIt_dvI2 (n : ℕ) (P : Fin (dd3 n) → ℝ) (u : Fin n → ℝ) (k : Fin (n + 1)) :
    (Work.WilG0.snocIt (dd3 n) n P u) (dvI2 n k) = P (dvI3 n k) := by
  rw [dvI2]
  exact Work.WilG0.snocIt_castAdd (dd3 n) n P u (dvI3 n k)

lemma snocIt_dhI2 (n : ℕ) (P : Fin (dd3 n) → ℝ) (u : Fin n → ℝ) :
    (Work.WilG0.snocIt (dd3 n) n P u) (dhI2 n) = P (dhI3 n) := by
  rw [dhI2]
  exact Work.WilG0.snocIt_castAdd (dd3 n) n P u (dhI3 n)

lemma snocIt_deI2 (n : ℕ) (P : Fin (dd3 n) → ℝ) (u : Fin n → ℝ) :
    (Work.WilG0.snocIt (dd3 n) n P u) (deI2 n) = P (deI3 n) := by
  rw [deI2]
  exact Work.WilG0.snocIt_castAdd (dd3 n) n P u (deI3 n)

lemma snocIt_dxI2 (n : ℕ) (P : Fin (dd3 n) → ℝ) (u : Fin n → ℝ) (j : Fin n) :
    (Work.WilG0.snocIt (dd3 n) n P u) (dxI2 n j) = u j := by
  rw [dxI2]
  exact Work.WilG0.snocIt_natAdd (dd3 n) n P u j

lemma snoc_dvI1 (n : ℕ) (P : Fin (dd2 n) → ℝ) (y : ℝ) (k : Fin (n + 1)) :
    (Fin.snoc P y : Fin (dd1 n) → ℝ) (dvI1 n k) = P (dvI2 n k) := by
  rw [dvI1]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) y P (dvI2 n k)

lemma snoc_dyI1 (n : ℕ) (P : Fin (dd2 n) → ℝ) (y : ℝ) :
    (Fin.snoc P y : Fin (dd1 n) → ℝ) (dyI1 n) = y := by
  rw [dyI1]
  exact Fin.snoc_last (α := fun _ => ℝ) y P

lemma snoc_deI1 (n : ℕ) (P : Fin (dd2 n) → ℝ) (y : ℝ) :
    (Fin.snoc P y : Fin (dd1 n) → ℝ) (deI1 n) = P (deI2 n) := by
  rw [deI1]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) y P (deI2 n)

lemma snoc_dhI1 (n : ℕ) (P : Fin (dd2 n) → ℝ) (y : ℝ) :
    (Fin.snoc P y : Fin (dd1 n) → ℝ) (dhI1 n) = P (dhI2 n) := by
  rw [dhI1]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) y P (dhI2 n)

lemma snoc_dxI1 (n : ℕ) (P : Fin (dd2 n) → ℝ) (y : ℝ) (j : Fin n) :
    (Fin.snoc P y : Fin (dd1 n) → ℝ) (dxI1 n j) = P (dxI2 n j) := by
  rw [dxI1]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) y P (dxI2 n j)

lemma snoc_dvI0 (n : ℕ) (P : Fin (dd1 n) → ℝ) (v' : ℝ) (k : Fin (n + 1)) :
    (Fin.snoc P v' : Fin (dd0 n) → ℝ) (dvI0 n k) = P (dvI1 n k) := by
  rw [dvI0]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) v' P (dvI1 n k)

lemma snoc_dvpI0 (n : ℕ) (P : Fin (dd1 n) → ℝ) (v' : ℝ) :
    (Fin.snoc P v' : Fin (dd0 n) → ℝ) (dvpI0 n) = v' := by
  rw [dvpI0]
  exact Fin.snoc_last (α := fun _ => ℝ) v' P

lemma snoc_dyI0 (n : ℕ) (P : Fin (dd1 n) → ℝ) (v' : ℝ) :
    (Fin.snoc P v' : Fin (dd0 n) → ℝ) (dyI0 n) = P (dyI1 n) := by
  rw [dyI0]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) v' P (dyI1 n)

lemma snoc_deI0 (n : ℕ) (P : Fin (dd1 n) → ℝ) (v' : ℝ) :
    (Fin.snoc P v' : Fin (dd0 n) → ℝ) (deI0 n) = P (deI1 n) := by
  rw [deI0]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) v' P (deI1 n)

lemma snoc_dhI0 (n : ℕ) (P : Fin (dd1 n) → ℝ) (v' : ℝ) :
    (Fin.snoc P v' : Fin (dd0 n) → ℝ) (dhI0 n) = P (dhI1 n) := by
  rw [dhI0]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) v' P (dhI1 n)

lemma snoc_dxI0 (n : ℕ) (P : Fin (dd1 n) → ℝ) (v' : ℝ) (j : Fin n) :
    (Fin.snoc P v' : Fin (dd0 n) → ℝ) (dxI0 n j) = P (dxI1 n j) := by
  rw [dxI0]
  exact Fin.snoc_castSucc (α := fun _ => ℝ) v' P (dxI1 n j)


/-! ## 6. Degree bounds of the atoms -/

lemma totalDegree_P4a_le (n : ℕ) : (P4a n).totalDegree ≤ 1 := by
  rw [P4a]
  refine (MvPolynomial.totalDegree_add _ _).trans ?_
  rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
  simp

lemma totalDegree_P4b_le (n : ℕ) : (P4b n).totalDegree ≤ 1 := by
  rw [P4b]
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
  simp

lemma totalDegree_P7a_le (n : ℕ) : (P7a n).totalDegree ≤ 1 := by
  rw [P7a]
  exact le_of_eq (MvPolynomial.totalDegree_X _)

lemma totalDegree_P7b_le (n : ℕ) : (P7b n).totalDegree ≤ 1 := by
  rw [P7b]
  exact le_of_eq (MvPolynomial.totalDegree_X _)

lemma totalDegree_P7d_le (n : ℕ) : (P7d n).totalDegree ≤ 2 := by
  rw [P7d]
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  rw [MvPolynomial.totalDegree_X_pow, MvPolynomial.totalDegree_X_pow]
  simp

lemma totalDegree_lin_dd0 (n : ℕ) (a b : Fin (dd0 n)) :
    (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin (dd0 n)) ℝ).totalDegree ≤ 1 := by
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
  simp

lemma totalDegree_P5_le (n : ℕ) (i j : Fin n) : (P5 n i j).totalDegree ≤ 1 := by
  rw [P5]
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact le_of_eq (MvPolynomial.totalDegree_X _)
    · exact le_of_eq (MvPolynomial.totalDegree_X _)
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_X]
    have hC : (MvPolynomial.C (if j = i then (1 : ℝ) else 0) :
        MvPolynomial (Fin (dd2 n)) ℝ).totalDegree ≤ 0 :=
      le_of_eq (MvPolynomial.totalDegree_C _)
    omega

lemma totalDegree_P7c_le (n : ℕ) : (P7c n).totalDegree ≤ 4 := by
  rw [P7c]
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_X_pow, MvPolynomial.totalDegree_X_pow]
  · refine (MvPolynomial.totalDegree_pow _ _).trans ?_
    have h1 : (MvPolynomial.X (dvI0 n (Fin.last n)) * MvPolynomial.X (dhI0 n) -
        (MvPolynomial.X (dvpI0 n) - MvPolynomial.X (dyI0 n)) :
        MvPolynomial (Fin (dd0 n)) ℝ).totalDegree ≤ 2 := by
      refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
      · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
        rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
      · exact le_trans (totalDegree_lin_dd0 n (dvpI0 n) (dyI0 n)) (by norm_num)
    omega

end DiffSet

end Work.WilE9.Gen
