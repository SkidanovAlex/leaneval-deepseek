/-
  annals_wilkies_conjecture, area C4aL (`C4a_lift`): the backward direction.

  Let `z` be a point of the piece `piece cc σ' P` lying over `t = z 0 ∈ (0,1)` and
  representing the value `y`.  Then `P` has a witness tuple at the point `(t⁻¹, y, cc)`:

  * `pieceF = 0` is a sum of squares, whence the cleared equation
    `Ppart cc (Fin.cons VC.big σ') P.totalDegree P z = 0`, and every `one`-coordinate
    satisfies `z j ^ 2 = 1`;
  * the strict inequalities of the piece give `z j ≠ 0` and `|z j| < 1` for every `big`
    coordinate and `|z j| < 1` for every `small` coordinate;
  * consequently the clearing factor `Kall` is nonzero on the piece and, multiplying the
    identity `Kall * Efun = Ppart` (`Kall_mul_Efun`) by it, the non-entire slice equation
    `Efun` vanishes;
  * each `rvE`-value is the `rexp` of the corresponding `valE`-value, so `Efun` is the
    `rexp`-polynomial `P` evaluated at the tuple of `valE`-values;
  * that tuple is `(t⁻¹, y, cc, w)` for the witness tuple `w` given by the last `m` piece
    coordinates.
-/
import Mathlib
import Submission.Work.WilC4aL.Main
import Submission.Work.WilC4aL.Kall_mul_Efun
import Submission.Work.WilC4aL.rvE_eq_rexp_valE

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilC4aL
open WilkiesDesign WilkiesDesign.CG.C4a
open scoped BigOperators

variable {k m : ℕ}

/-! ## 1. Vocabulary -/

/-- The case assignment of the piece `piece cc σ' P`: the `x`-coordinate is `big` (its piece
coordinate is `t = 1/x`), and the remaining coordinates follow `σ'`. -/
def rcCases {m : ℕ} (σ' : Fin (m + 1) → VC) : Fin (m + 2) → VC := Fin.cons VC.big σ'

/-! ## 2. The `pieceG` slots -/

theorem rc_pieceG_zero_zero {m : ℕ} (σ : Fin (m + 2) → VC) (z : Fin (m + 2) → ℝ) :
    pieceG σ 0 0 z = z 0 := by simp [pieceG]

theorem rc_pieceG_zero_one {m : ℕ} (σ : Fin (m + 2) → VC) (z : Fin (m + 2) → ℝ) :
    pieceG σ 0 1 z = 1 - z 0 := by simp [pieceG]

theorem rc_pieceG_succ_zero_of_big {m : ℕ} (σ : Fin (m + 2) → VC) (j : Fin (m + 1))
    (z : Fin (m + 2) → ℝ) (h : σ (Fin.succ j) = VC.big) :
    pieceG σ (Fin.succ j) 0 z = (z (Fin.succ j)) ^ 2 := by
  rw [show pieceG σ (Fin.succ j) 0 z =
      (if σ (Fin.succ j) = VC.small then 1 - (z (Fin.succ j)) ^ 2
       else if σ (Fin.succ j) = VC.one then 1 else (z (Fin.succ j)) ^ 2)
      from by simp [pieceG]]
  rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide)]

theorem rc_pieceG_succ_one_of_big {m : ℕ} (σ : Fin (m + 2) → VC) (j : Fin (m + 1))
    (z : Fin (m + 2) → ℝ) (h : σ (Fin.succ j) = VC.big) :
    pieceG σ (Fin.succ j) 1 z = 1 - (z (Fin.succ j)) ^ 2 := by
  rw [show pieceG σ (Fin.succ j) 1 z =
      (if σ (Fin.succ j) = VC.small then 1
       else if σ (Fin.succ j) = VC.one then 1 else 1 - (z (Fin.succ j)) ^ 2)
      from by simp [pieceG]]
  rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide)]

theorem rc_pieceG_succ_zero_of_small {m : ℕ} (σ : Fin (m + 2) → VC) (j : Fin (m + 1))
    (z : Fin (m + 2) → ℝ) (h : σ (Fin.succ j) = VC.small) :
    pieceG σ (Fin.succ j) 0 z = 1 - (z (Fin.succ j)) ^ 2 := by
  rw [show pieceG σ (Fin.succ j) 0 z =
      (if σ (Fin.succ j) = VC.small then 1 - (z (Fin.succ j)) ^ 2
       else if σ (Fin.succ j) = VC.one then 1 else (z (Fin.succ j)) ^ 2)
      from by simp [pieceG]]
  rw [if_pos h]

/-! ## 3. The coordinate facts of a point of a piece -/

/-- A point `z` of the piece `piece cc σ' P` over `t = z 0` satisfies the cleared equation,
and each of its coordinates is subject to the case prescribed by `σ'`. -/
theorem piece_coord_facts {k m : ℕ} (cc : Fin k → ℝ) (σ' : Fin (m + 1) → VC)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ) (z : Fin (m + 2) → ℝ)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hzt : z ∈ (piece cc σ' P).set) (hz0 : z 0 = t) :
    Ppart cc (rcCases σ') P.totalDegree P z = 0 ∧
    (∀ j : Fin (m + 2), (rcCases σ') j = VC.big → z j ≠ 0 ∧ |z j| < 1) ∧
    (∀ j : Fin (m + 2), (rcCases σ') j = VC.small → |z j| < 1) ∧
    (∀ j : Fin (m + 2), (rcCases σ') j = VC.one → z j ^ 2 = 1) := by
  have hgq : ∀ (i : Fin (m + 2)) (q : Fin 2), 0 < pieceG (rcCases σ') i q z := by
    intro i q
    have h := hzt.2 (finProdFinEquiv (i, q))
    simpa only [piece, rcCases, Equiv.symm_apply_apply, Prod.fst, Prod.snd] using h
  have hF : pieceF cc (rcCases σ') P.totalDegree P z = 0 := by
    have h := hzt.1
    simpa only [piece, rcCases] using h
  -- `pieceF` is a sum of squares
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin (m + 2))),
      0 ≤ (if (rcCases σ') i = VC.one then (z i ^ 2 - 1) ^ 2 else 0) := by
    intro i _
    split_ifs with h
    · exact sq_nonneg _
    · exact le_refl 0
  have hS : (∑ i : Fin (m + 2),
      (if (rcCases σ') i = VC.one then (z i ^ 2 - 1) ^ 2 else 0)) = 0 := by
    have hA : 0 ≤ (Ppart cc (rcCases σ') P.totalDegree P z) ^ 2 := sq_nonneg _
    have hB : 0 ≤ ∑ i : Fin (m + 2),
        (if (rcCases σ') i = VC.one then (z i ^ 2 - 1) ^ 2 else 0) :=
      Finset.sum_nonneg hnn
    rw [pieceF] at hF
    linarith
  have hPpart : Ppart cc (rcCases σ') P.totalDegree P z = 0 := by
    have hA : 0 ≤ (Ppart cc (rcCases σ') P.totalDegree P z) ^ 2 := sq_nonneg _
    have hB : 0 ≤ ∑ i : Fin (m + 2),
        (if (rcCases σ') i = VC.one then (z i ^ 2 - 1) ^ 2 else 0) :=
      Finset.sum_nonneg hnn
    rw [pieceF] at hF
    have h2 : (Ppart cc (rcCases σ') P.totalDegree P z) ^ 2 = 0 := by linarith
    exact sq_eq_zero_iff.mp h2
  have hone : ∀ j : Fin (m + 2), (rcCases σ') j = VC.one → z j ^ 2 = 1 := by
    intro j hj
    have h := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hS j (Finset.mem_univ j)
    rw [if_pos hj] at h
    have h2 : z j ^ 2 - 1 = 0 := sq_eq_zero_iff.mp h
    linarith
  refine ⟨hPpart, ?_, ?_, hone⟩
  · -- `big` coordinates
    intro j hj
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · have h0 : 0 < z 0 := by
        have h := hgq 0 0
        rwa [rc_pieceG_zero_zero] at h
      have h1 : z 0 < 1 := by
        have h := hgq 0 1
        rw [rc_pieceG_zero_one] at h
        linarith
      exact ⟨ne_of_gt h0, by rw [abs_of_pos h0]; exact h1⟩
    · have h0 : 0 < (z (Fin.succ j')) ^ 2 := by
        have h := hgq (Fin.succ j') 0
        rwa [rc_pieceG_succ_zero_of_big (σ := rcCases σ') (j := j') (z := z) hj] at h
      have h1 : (z (Fin.succ j')) ^ 2 < 1 := by
        have h := hgq (Fin.succ j') 1
        rw [rc_pieceG_succ_one_of_big (σ := rcCases σ') (j := j') (z := z) hj] at h
        linarith
      exact ⟨sq_pos_iff.mp h0, (sq_lt_one_iff_abs_lt_one (z (Fin.succ j'))).mp h1⟩
  · -- `small` coordinates
    intro j hj
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · have h0 : (rcCases σ') (0 : Fin (m + 2)) = VC.big := by simp [rcCases]
      rw [h0] at hj
      exact absurd hj (by decide)
    · have h : 0 < 1 - (z (Fin.succ j')) ^ 2 := by
        have h := hgq (Fin.succ j') 0
        rwa [rc_pieceG_succ_zero_of_small (σ := rcCases σ') (j := j') (z := z) hj] at h
      exact (sq_lt_one_iff_abs_lt_one (z (Fin.succ j'))).mp (by linarith)

/-! ## 4. The clearing factor is nonzero on the piece -/

theorem rc_Kall_ne_zero {k m : ℕ} (σ : Fin (m + 2) → VC) (D : ℕ) (z : Fin (m + 2) → ℝ)
    (hz : ∀ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m), bigSum σ x = true →
      z (Sum.elim coordOf coordOf x) ≠ 0) :
    Kall (k := k) σ D z ≠ 0 := by
  show (∏ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m), Kx σ D z x) ≠ 0
  refine Finset.prod_ne_zero_iff.mpr (fun x _ => ?_)
  by_cases hb : bigSum σ x = true
  · simp only [Kx, if_pos hb]
    exact pow_ne_zero _ (hz x hb)
  · simp only [Kx, if_neg hb]
    exact one_ne_zero

/-! ## 5. The index blocks -/

/-- Every index of `Fin (k + 2 + m)` is the `x`-index, the `y`-index, a constant index or a
witness index. -/
theorem rc_fin_cases {k m : ℕ} (i : Fin (k + 2 + m)) :
    i = idxX ∨ i = idxY ∨ (∃ j : Fin k, i = idxC j) ∨ (∃ j : Fin m, i = idxW j) := by
  have hi : (i : ℕ) < k + 2 + m := i.isLt
  rcases Nat.lt_or_ge (i : ℕ) 2 with h | h
  · rcases Nat.lt_or_ge (i : ℕ) 1 with h0 | h0
    · left
      refine Fin.ext ?_
      rw [val_idxX]
      omega
    · right; left
      refine Fin.ext ?_
      rw [val_idxY]
      omega
  · rcases Nat.lt_or_ge (i : ℕ) (k + 2) with hk | hk
    · right; right; left
      refine ⟨⟨(i : ℕ) - 2, by omega⟩, Fin.ext ?_⟩
      show (i : ℕ) = ((i : ℕ) - 2) + 2
      omega
    · right; right; right
      refine ⟨⟨(i : ℕ) - (k + 2), by omega⟩, Fin.ext ?_⟩
      show (i : ℕ) = (k + 2) + ((i : ℕ) - (k + 2))
      omega

/-! ## 6. The backward direction -/

theorem reconstruct {k m : ℕ} (cc : Fin k → ℝ) (σ' : Fin (m + 1) → VC)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ) (t y : ℝ)
    (z : Fin (m + 2) → ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hgood : (piece cc σ' P).Good) (hzt : z ∈ (piece cc σ' P).set) (hz0 : z 0 = t)
    (hrp : (piece cc σ' P).Rep z y) :
    ∃ w : Fin m → ℝ,
      WilkiesDesign.rexpPolyEval P
        (Fin.append (Fin.cons t⁻¹ (Fin.cons y cc) : Fin (k + 2) → ℝ) w) = 0 := by
  obtain ⟨hPpart, hbig, hsmall, hone⟩ := piece_coord_facts cc σ' P z t ht0 ht1 hzt hz0
  -- the total degree dominates the exponents, and inverted coordinates do not vanish
  have hD : ∀ d ∈ P.support, ∀ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m),
      bigSum (rcCases σ') x = true → d x ≤ P.totalDegree :=
    fun d hd x _ => exp_le_totalDegree hd x
  have hznz : ∀ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m),
      bigSum (rcCases σ') x = true → z (Sum.elim coordOf coordOf x) ≠ 0 := by
    intro x hx
    rcases x with i | i
    · have hxi : isBigB (rcCases σ') i = true := hx
      obtain ⟨j, hj, hbj⟩ := (isBigB_true_iff (rcCases σ') i).mp hxi
      have hcj : coordOf i = j := by simp only [coordOf, hj, Sum.elim_inr, id_eq]
      simp only [Sum.elim_inl, hcj]
      exact (hbig j hbj).1
    · simp only [bigSum_inr, Bool.false_eq_true] at hx
  -- the cleared equation vanishes, and the clearing factor is nonzero, so `Efun` vanishes
  have hKE : Kall (k := k) (rcCases σ') P.totalDegree z * Efun cc (rcCases σ') P z = 0 := by
    rw [Kall_mul_Efun cc (rcCases σ') P.totalDegree P z hD hznz, hPpart]
  have hKne : Kall (k := k) (rcCases σ') P.totalDegree z ≠ 0 :=
    rc_Kall_ne_zero (rcCases σ') P.totalDegree z hznz
  have hE : Efun cc (rcCases σ') P z = 0 := by
    rcases mul_eq_zero.mp hKE with h | h
    · exact absurd h hKne
    · exact h
  -- `Efun` is the `rexp`-polynomial evaluated at the tuple of piece values
  have hrv : ∀ i : Fin (k + 2 + m),
      rvE cc (rcCases σ') i z = rexp (valE cc (rcCases σ') i z) :=
    rvE_eq_rexp_valE cc (rcCases σ') z hbig hsmall hone
  have hEval : WilkiesDesign.rexpPolyEval P (fun i => valE cc (rcCases σ') i z) = 0 := by
    rw [← Efun_eq_rexpPolyEval cc (rcCases σ') P z (fun i => valE cc (rcCases σ') i z)
      (fun i => rfl) hrv, hE]
  -- the tuple of piece values is `(t⁻¹, y, cc, w)`
  have hzy_big : σ' 0 = VC.big → z 1 * y = 1 := by
    intro h
    have hinv : (piece cc σ' P).inv = true := by simp [piece, h]
    have h' : (if (piece cc σ' P).inv then z 1 * y = 1 else z 1 = y) := hrp
    rw [hinv] at h'
    simpa using h'
  have hzy_notbig : ¬ σ' 0 = VC.big → z 1 = y := by
    intro h
    have hinv : (piece cc σ' P).inv = false := by
      simp only [piece]
      rw [decide_eq_false_iff_not]
      exact h
    have h' : (if (piece cc σ' P).inv then z 1 * y = 1 else z 1 = y) := hrp
    rw [hinv] at h'
    simpa using h'
  have hvalX : valE cc (rcCases σ') idxX z = t⁻¹ := by
    rw [valE_idxX]
    have h0 : (rcCases σ') (0 : Fin (m + 2)) = VC.big := by simp [rcCases]
    rw [h0, hz0]
    simp
  have hvalY : valE cc (rcCases σ') idxY z = y := by
    rw [valE_idxY]
    have h1 : (rcCases σ') (1 : Fin (m + 2)) = σ' 0 := by
      rw [show (1 : Fin (m + 2)) = Fin.succ (0 : Fin (m + 1)) from
        (Fin.succ_zero_eq_one' (n := m + 1)).symm]
      simp only [rcCases, Fin.cons_succ]
    rw [h1]
    by_cases hb : σ' 0 = VC.big
    · rw [if_pos hb]
      exact inv_eq_of_mul_eq_one_right (hzy_big hb)
    · rw [if_neg hb]
      exact hzy_notbig hb
  have hEq : (fun i => valE cc (rcCases σ') i z)
      = Fin.append (Fin.cons t⁻¹ (Fin.cons y cc) : Fin (k + 2) → ℝ)
          (fun j => valE cc (rcCases σ') (Fin.natAdd (k + 2) j) z) := by
    funext i
    rcases rc_fin_cases i with h | h | ⟨j, h⟩ | ⟨j, h⟩
    · rw [h, hvalX, ← castAdd_zero_eq_idxX, append_castAdd_zero]
    · rw [h, hvalY, ← castAdd_succ_zero_eq_idxY, append_castAdd_succ_zero]
    · rw [h, valE_idxC, ← castAdd_succ_succ_eq_idxC, append_castAdd_succ_succ]
    · rw [h, ← natAdd_eq_idxW, append_natAdd]
  refine ⟨fun j => valE cc (rcCases σ') (Fin.natAdd (k + 2) j) z, ?_⟩
  rw [← hEq]
  exact hEval

end Work.WilC4aL
