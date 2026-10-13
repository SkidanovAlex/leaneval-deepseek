import Mathlib
import Submission.Work.WilG4c.SliceNilDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

/-!
  `Work.WilG4c.ZpData_deg_le`: the degree bookkeeping for the pointwise fibre continuity shape
  `ZpShape p n` applied to the data `ZpData p n f D`.

  `OShape.deg` is purely syntactic: it adds `2` per `mem`-atom (for the substitution equation),
  adds `2` per `neg`-free atom, and the `posAtom Q` gadget has degree `2 + deg Q`.  Unfolding the
  shape `ZpShape` and the data `ZpData` therefore gives exactly

      `deg = (D + 2) + (e_ε + (e_δ + (e_ball + ((D + 2) + e_D))))`

  where `e_ε`, `e_δ`, `e_ball`, `e_D` are the total degrees of the four positivity gadgets,
  bounded respectively by `3`, `3`, `4`, `4` (each `posAtom Q` contributes `2 + deg Q`, and the
  gadget polynomials `ε`, `δ`, `δ² - Σ(y'_j-y_j)²`, `ε² - (v'-v)²` have degree `1`, `1`, `2`, `2`
  at worst).  The total is

      `(D + 2) + 3 + 3 + 4 + (D + 2) + 4 = 2 * D + 18`.

  The only step that is not a plain `simp`-unfolding is `forallIter` (the universal block over the
  cube coordinate `y'`), which is handled by `forallIter_deg`.
-/

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. Degree bounds for the gadget polynomials -/

/-- `(X i - X j)²` has total degree at most `2`. -/
private lemma totalDegree_X_sub_X_sq_le_two {m : ℕ} (i j : Fin m) :
    ((MvPolynomial.X i - MvPolynomial.X j) ^ 2 : MvPolynomial (Fin m) ℝ).totalDegree ≤ 2 := by
  have h1 : (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin m) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
    simp
  refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
  omega

/-- `(X i)²` has total degree at most `2`. -/
private lemma totalDegree_X_sq_le_two {m : ℕ} (i : Fin m) :
    ((MvPolynomial.X i) ^ 2 : MvPolynomial (Fin m) ℝ).totalDegree ≤ 2 := by
  refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
  rw [MvPolynomial.totalDegree_X]

/-- A sum of squares of differences of variables has total degree at most `2`. -/
private lemma totalDegree_sum_sq_le_two {m : ℕ} {ι : Type*} (s : Finset ι) (u v : ι → Fin m) :
    ((∑ i ∈ s, (MvPolynomial.X (u i) - MvPolynomial.X (v i)) ^ 2 :
      MvPolynomial (Fin m) ℝ)).totalDegree ≤ 2 := by
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  rw [Finset.sup_le_iff]
  intro i _
  exact totalDegree_X_sub_X_sq_le_two (u i) (v i)

/-- The polynomial `ε` has total degree at most `1`. -/
private lemma totalDegree_Peps_le (p n : ℕ) : (Peps p n).totalDegree ≤ 1 :=
  le_of_eq (by rw [Peps, MvPolynomial.totalDegree_X])

/-- The polynomial `δ` has total degree at most `1`. -/
private lemma totalDegree_Pdel_le (p n : ℕ) : (Pdel p n).totalDegree ≤ 1 :=
  le_of_eq (by rw [Pdel, MvPolynomial.totalDegree_X])

/-- The polynomial `δ² - Σ_j (y'_j - y_j)²` has total degree at most `2`. -/
private lemma totalDegree_Pball_le (p n : ℕ) : (Pball p n).totalDegree ≤ 2 := by
  rw [Pball]
  refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
  · exact totalDegree_X_sq_le_two _
  · exact totalDegree_sum_sq_le_two _ _ _

/-- The polynomial `ε² - (v' - v)²` has total degree at most `2`. -/
private lemma totalDegree_PD_le (p n : ℕ) : (PD p n).totalDegree ≤ 2 := by
  rw [PD]
  refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
  · exact totalDegree_X_sq_le_two _
  · exact totalDegree_X_sub_X_sq_le_two _ _

/-! ## 2. The `forallIter` step -/

/-- The degree of the universal block over the cube coordinate `y'` is the degree of its body
(`forallIter` does not change the data, hence not the degree). -/
private lemma deg_zpYBlock (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpYBlock p n).deg (zpYBlockData p n f D)
      = (zpBallImp p n).deg (zpBallImpData p n f D) :=
  forallIter_deg (Nc p n + 5) (n + 1) (zpBallImp p n) (zpBallImpData p n f D)

/-! ## 3. The degree of `ZpData` -/

/-- The degree of the shape `ZpShape p n` on the data `ZpData p n f D`, in terms of the four
positivity gadgets. -/
private theorem deg_ZpData (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (ZpShape p n).deg (ZpData p n f D)
      = (D + 2) + ((posAtom (Peps p n)).totalDegree + ((posAtom (Pdel p n)).totalDegree
          + ((posAtom (Pball p n)).totalDegree
              + ((D + 2) + (posAtom (PD p n)).totalDegree)))) := by
  simp only [ZpShape, ZpData, zpCont, zpContData, zpEpsEx, zpEps, zpEpsData, zpDeltaEx,
    zpDeltaExData, zpDelta, zpDeltaData, deg_zpYBlock, zpBallImp, zpBallImpData, zpVexists,
    zpVexistsData, zpInner, zpInnerData, OShape.deg]

/-- `Work.WilG4c.ZpData_deg_le`, proved in the `WilkG4c` shape namespace. -/
private theorem ZpData_deg_le_aux (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (D : ℕ) : (ZpShape p n).deg (ZpData p n f D) ≤ 2 * D + 18 := by
  have h1 := totalDegree_posAtom_le (Peps p n)
  have h2 := totalDegree_posAtom_le (Pdel p n)
  have h3 := totalDegree_posAtom_le (Pball p n)
  have h4 := totalDegree_posAtom_le (PD p n)
  have e1 := totalDegree_Peps_le p n
  have e2 := totalDegree_Pdel_le p n
  have e3 := totalDegree_Pball_le p n
  have e4 := totalDegree_PD_le p n
  have key := deg_ZpData p n f D
  omega

end Work.WilkG4c

namespace Work.WilG4c

theorem ZpData_deg_le (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (Work.WilkG4c.ZpShape p n).deg (Work.WilkG4c.ZpData p n f D) ≤ 2 * D + 18 :=
  Work.WilkG4c.ZpData_deg_le_aux p n f D

end Work.WilG4c
