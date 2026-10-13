/-
  `Work.WilC4aL.mkZ_mem`: the forward membership for the `C4a_lift` assembly.

  Given the case assignment `mkCases y w` of the slice point `(y, w)`, the constructed point
  `mkZ y w t` lies in the piece attached to that case assignment and represents `y`.

  The two mathematical inputs are
  * `Kall_mul_Efun` (the cleared equation identity): the piece equation `Ppart` is `Kall` times
    the substituted equation `Efun`;
  * `Efun_eq_rexpPolyEval`: `Efun` at the constructed point is the `rexp`-polynomial evaluation
    of `P` at `(t⁻¹, y, c, w)`, which vanishes by hypothesis.
-/
import Mathlib
import Submission.Work.WilC4aL.Main
import Submission.Work.WilC4aL.Kall_mul_Efun

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilC4aL
open WilkiesDesign WilkiesDesign.CG.C4a
open scoped BigOperators

variable {k m : ℕ}

/-! ## 0. The case assignment of the constructed slice point -/

/-- Case assignment of the piece attached to the slice point `(y, w)`: the `t`-coordinate `0`
is `big` (`x = 1/t > 1`), and coordinate `j+1` carries the case of `pairVec y w j`. -/
def mkSig {m : ℕ} (y : ℝ) (w : Fin m → ℝ) : Fin (m + 2) → VC :=
  Fin.cons VC.big (mkCases y w)

theorem mkSig_zero {m : ℕ} (y : ℝ) (w : Fin m → ℝ) : mkSig y w 0 = VC.big := by
  rw [mkSig, Fin.cons_zero]

theorem mkSig_succ {m : ℕ} (y : ℝ) (w : Fin m → ℝ) (j : Fin (m + 1)) :
    mkSig y w (Fin.succ j) = mkCases y w j := by
  rw [mkSig, Fin.cons_succ]

theorem mkSig_one {m : ℕ} (y : ℝ) (w : Fin m → ℝ) : mkSig y w 1 = caseOf y := by
  rw [mkSig, Fin.cons_one, mkCases_zero]

theorem mkSig_succ_succ {m : ℕ} (y : ℝ) (w : Fin m → ℝ) (j : Fin m) :
    mkSig y w (Fin.succ (Fin.succ j)) = caseOf (w j) := by
  rw [mkSig_succ y w (Fin.succ j), mkCases_succ y w j]

theorem pairVec_zero {m : ℕ} (y : ℝ) (w : Fin m → ℝ) : pairVec y w 0 = y := by
  simp [pairVec]

theorem pairVec_succ {m : ℕ} (y : ℝ) (w : Fin m → ℝ) (j : Fin m) :
    pairVec y w (Fin.succ j) = w j := by
  simp [pairVec]

/-! ## 1. The constructed point at the special coordinates -/

theorem mkZ_one {m : ℕ} (y t : ℝ) (w : Fin m → ℝ) :
    mkZ y w t 1 = (if caseOf y = VC.big then y⁻¹ else y) := by
  have h1 : (1 : Fin (m + 2)) = Fin.succ (0 : Fin (m + 1)) := rfl
  rw [h1, mkZ_succ]
  simp [pairVec]

theorem mkZ_succ_succ {m : ℕ} (y t : ℝ) (w : Fin m → ℝ) (j : Fin m) :
    mkZ y w t (Fin.succ (Fin.succ j)) = (if caseOf (w j) = VC.big then (w j)⁻¹ else w j) := by
  rw [mkZ_succ]
  simp [pairVec]

/-! ## 2. Case trichotomy and its consequences -/

theorem caseOf_cases {v : ℝ} :
    caseOf v = VC.small ∨ caseOf v = VC.one ∨ caseOf v = VC.big := by
  unfold caseOf
  split_ifs <;> simp

theorem caseOf_big_of_one_lt_abs {v : ℝ} (h : 1 < |v|) : caseOf v = VC.big := by
  have h1 : v ≠ 1 := by
    intro hv; rw [hv, abs_one] at h; exact absurd h (lt_irrefl 1)
  have h2 : v ≠ -1 := by
    intro hv; rw [hv, abs_neg, abs_one] at h; exact absurd h (lt_irrefl 1)
  have h3 : ¬ (|v| < 1) := not_lt.mpr (le_of_lt h)
  unfold caseOf
  rw [if_neg h1, if_neg h2, if_neg h3]

theorem abs_le_one_of_caseOf_ne_big {v : ℝ} (h : caseOf v ≠ VC.big) : |v| ≤ 1 := by
  by_contra hc
  exact h (caseOf_big_of_one_lt_abs (lt_of_not_ge hc))

/-! ## 3. The substitution values at the constructed point -/

theorem valE_mkSig_idxX {k m : ℕ} (cc : Fin k → ℝ) (y t : ℝ) (w : Fin m → ℝ) :
    valE cc (mkSig y w) (idxX (k := k) (m := m)) (mkZ y w t) = t⁻¹ := by
  rw [valE_idxX, mkSig_zero, if_pos rfl, mkZ_zero]

theorem valE_mkSig_idxY {k m : ℕ} (cc : Fin k → ℝ) (y t : ℝ) (w : Fin m → ℝ) :
    valE cc (mkSig y w) (idxY (k := k) (m := m)) (mkZ y w t) = y := by
  rw [valE_idxY, mkSig_one]
  by_cases hb : caseOf y = VC.big
  · rw [if_pos hb, mkZ_one, if_pos hb, inv_inv]
  · rw [if_neg hb, mkZ_one, if_neg hb]

theorem valE_mkSig_idxC {k m : ℕ} (cc : Fin k → ℝ) (y t : ℝ) (w : Fin m → ℝ) (j : Fin k) :
    valE cc (mkSig y w) (idxC (m := m) j) (mkZ y w t) = cc j := by
  rw [valE_idxC]

theorem valE_mkSig_idxW {k m : ℕ} (cc : Fin k → ℝ) (y t : ℝ) (w : Fin m → ℝ) (j : Fin m) :
    valE cc (mkSig y w) (idxW (k := k) j) (mkZ y w t) = w j := by
  rw [valE_idxW, mkSig_succ_succ]
  by_cases hb : caseOf (w j) = VC.big
  · rw [if_pos hb, mkZ_succ, pairVec_succ, if_pos hb, inv_inv]
  · rw [if_neg hb, mkZ_succ, pairVec_succ, if_neg hb]

theorem rvE_idxX {k m : ℕ} (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (z : Fin (m + 2) → ℝ) :
    rvE cc σ (idxX (k := k) (m := m)) z =
      (if σ 0 = VC.big then 0 else Real.exp (z 0)) := by
  simp only [rvE, piIdx_idxX, Sum.elim_inr]

theorem rvE_idxY {k m : ℕ} (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (z : Fin (m + 2) → ℝ) :
    rvE cc σ (idxY (k := k) (m := m)) z =
      (if σ 1 = VC.big then 0 else Real.exp (z 1)) := by
  simp only [rvE, piIdx_idxY, Sum.elim_inr]

theorem rvE_idxW {k m : ℕ} (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC) (z : Fin (m + 2) → ℝ)
    (j : Fin m) :
    rvE cc σ (idxW (k := k) j) z =
      (if σ (Fin.succ (Fin.succ j)) = VC.big then 0
        else Real.exp (z (Fin.succ (Fin.succ j)))) := by
  simp only [rvE, piIdx_idxW, Sum.elim_inr]

theorem rvE_mkSig_idxX {k m : ℕ} (cc : Fin k → ℝ) (y t : ℝ) (w : Fin m → ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) :
    rvE cc (mkSig y w) (idxX (k := k) (m := m)) (mkZ y w t) = rexp (t⁻¹) := by
  rw [rvE_idxX, mkSig_zero, if_pos rfl]
  exact (rexp_inv_of_abs_lt_one (abs_lt.mpr ⟨by linarith, ht1⟩) (ne_of_gt ht0)).symm

theorem rvE_mkSig_idxY {k m : ℕ} (cc : Fin k → ℝ) (y t : ℝ) (w : Fin m → ℝ) :
    rvE cc (mkSig y w) (idxY (k := k) (m := m)) (mkZ y w t) = rexp y := by
  rw [rvE_idxY, mkSig_one]
  by_cases hb : caseOf y = VC.big
  · rw [if_pos hb, rexp_of_one_lt_abs (caseOf_big hb)]
  · rw [if_neg hb, mkZ_one, if_neg hb, rexp_of_abs_le_one (abs_le_one_of_caseOf_ne_big hb)]

theorem rvE_mkSig_idxC {k m : ℕ} (cc : Fin k → ℝ) (y t : ℝ) (w : Fin m → ℝ) (j : Fin k) :
    rvE cc (mkSig y w) (idxC (m := m) j) (mkZ y w t) = rexp (cc j) := by
  rw [rvE_idxC]

theorem rvE_mkSig_idxW {k m : ℕ} (cc : Fin k → ℝ) (y t : ℝ) (w : Fin m → ℝ) (j : Fin m) :
    rvE cc (mkSig y w) (idxW (k := k) j) (mkZ y w t) = rexp (w j) := by
  rw [rvE_idxW, mkSig_succ_succ]
  by_cases hb : caseOf (w j) = VC.big
  · rw [if_pos hb, rexp_of_one_lt_abs (caseOf_big hb)]
  · rw [if_neg hb, mkZ_succ, pairVec_succ, if_neg hb,
        rexp_of_abs_le_one (abs_le_one_of_caseOf_ne_big hb)]

/-! ## 4. Nonvanishing and the `one`-coordinates of the constructed point -/

theorem mkZ_ne_zero_of_big {m : ℕ} (y t : ℝ) (w : Fin m → ℝ) (ht0 : 0 < t) :
    ∀ j : Fin (m + 2), mkSig y w j = VC.big → mkZ y w t j ≠ 0 := by
  intro j
  refine fin_two_cases (k := m) (C := fun j => mkSig y w j = VC.big → mkZ y w t j ≠ 0)
    ?_ ?_ ?_ j
  · intro _
    rw [mkZ_zero]
    exact ne_of_gt ht0
  · intro h
    have hb : caseOf y = VC.big := by rw [mkSig_succ, mkCases_zero] at h; exact h
    have hy : y ≠ 0 := by
      have h1 := caseOf_big hb
      intro h0; rw [h0, abs_zero] at h1; linarith
    rw [mkZ_succ, pairVec_zero, if_pos hb]
    exact inv_ne_zero hy
  · intro j h
    have hb : caseOf (w j) = VC.big := by rw [mkSig_succ_succ] at h; exact h
    have hw : w j ≠ 0 := by
      have h1 := caseOf_big hb
      intro h0; rw [h0, abs_zero] at h1; linarith
    rw [mkZ_succ, pairVec_succ, if_pos hb]
    exact inv_ne_zero hw

theorem mkZ_sq_of_one {m : ℕ} (y t : ℝ) (w : Fin m → ℝ) :
    ∀ j : Fin (m + 2), mkSig y w j = VC.one → (mkZ y w t j) ^ 2 = 1 := by
  intro j
  refine fin_two_cases (k := m) (C := fun j => mkSig y w j = VC.one → (mkZ y w t j) ^ 2 = 1)
    ?_ ?_ ?_ j
  · intro h
    rw [mkSig_zero] at h
    exact absurd h (by decide)
  · intro h
    have ho : caseOf y = VC.one := by rw [mkSig_succ, mkCases_zero] at h; exact h
    have hnb : ¬ (caseOf y = VC.big) := by rw [ho]; decide
    rw [mkZ_succ, pairVec_zero, if_neg hnb]
    exact caseOf_one ho
  · intro j h
    have ho : caseOf (w j) = VC.one := by rw [mkSig_succ_succ] at h; exact h
    have hnb : ¬ (caseOf (w j) = VC.big) := by rw [ho]; decide
    rw [mkZ_succ, pairVec_succ, if_neg hnb]
    exact caseOf_one ho

/-! ## 5. The inequalities of the piece -/

theorem pieceG_zero_zero {m : ℕ} (σ : Fin (m + 2) → VC) (z : Fin (m + 2) → ℝ) :
    pieceG σ 0 0 z = z 0 := by simp [pieceG]

theorem pieceG_zero_one {m : ℕ} (σ : Fin (m + 2) → VC) (z : Fin (m + 2) → ℝ) :
    pieceG σ 0 1 z = 1 - z 0 := by simp [pieceG]

/-- The coordinate inequality for a non-`t` coordinate: if `v` is the value of the coordinate
(so the coordinate itself is `v⁻¹` when `caseOf v = big`), the corresponding `pieceG` inequality
is strictly positive. -/
theorem coord_ineq (v : ℝ) (r : Fin 2) :
    0 < (if caseOf v = VC.small then
          (if (r : ℕ) = 0 then 1 - (if caseOf v = VC.big then v⁻¹ else v) ^ 2 else 1)
        else if caseOf v = VC.one then 1
        else if (r : ℕ) = 0 then (if caseOf v = VC.big then v⁻¹ else v) ^ 2
        else 1 - (if caseOf v = VC.big then v⁻¹ else v) ^ 2) := by
  rcases caseOf_cases (v := v) with hc | hc | hc
  · rw [if_pos hc]
    have hnb : ¬ (caseOf v = VC.big) := by rw [hc]; decide
    rw [if_neg hnb]
    by_cases hr : (r : ℕ) = 0
    · rw [if_pos hr]
      have hv2 : v ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one v).mpr (caseOf_small hc)
      linarith
    · rw [if_neg hr]
      norm_num
  · have hnb : ¬ (caseOf v = VC.small) := by rw [hc]; decide
    rw [if_neg hnb, if_pos hc]
    norm_num
  · have hnb1 : ¬ (caseOf v = VC.small) := by rw [hc]; decide
    have hnb2 : ¬ (caseOf v = VC.one) := by rw [hc]; decide
    rw [if_neg hnb1, if_neg hnb2]
    have hv : 1 < |v| := caseOf_big hc
    have hvz : v ≠ 0 := by intro h0; rw [h0, abs_zero] at hv; linarith
    have hiv : |v⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hv
    have hv2 : (v⁻¹) ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one v⁻¹).mpr hiv
    by_cases hr : (r : ℕ) = 0
    · rw [if_pos hr, if_pos hc]
      exact pow_two_pos_of_ne_zero (inv_ne_zero hvz)
    · rw [if_neg hr, if_pos hc]
      linarith

/-! ## 6. The target -/

theorem mkZ_mem {k m : ℕ} (cc : Fin k → ℝ) (y t : ℝ) (w : Fin m → ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ)
    (hP : WilkiesDesign.rexpPolyEval P
      (Fin.append (Fin.cons t⁻¹ (Fin.cons y cc) : Fin (k + 2) → ℝ) w) = 0) :
    (mkZ y w t ∈ (piece cc (mkCases y w) P).set) ∧
      (piece cc (mkCases y w) P).Rep (mkZ y w t) y := by
  have hval : ∀ i : Fin (k + 2 + m),
      valE cc (mkSig y w) i (mkZ y w t)
        = Fin.append (Fin.cons t⁻¹ (Fin.cons y cc) : Fin (k + 2) → ℝ) w i := by
    refine Fin.addCases (m := k + 2) (n := m) ?_ ?_
    · intro u
      refine fin_two_cases (k := k)
        (C := fun u => valE cc (mkSig y w) (Fin.castAdd m u) (mkZ y w t)
          = Fin.append (Fin.cons t⁻¹ (Fin.cons y cc) : Fin (k + 2) → ℝ) w
              (Fin.castAdd m u)) ?_ ?_ ?_ u
      · rw [append_castAdd_zero]
        exact valE_mkSig_idxX cc y t w
      · rw [append_castAdd_succ_zero]
        exact valE_mkSig_idxY cc y t w
      · intro j
        rw [append_castAdd_succ_succ]
        exact valE_mkSig_idxC cc y t w j
    · intro j
      rw [append_natAdd]
      exact valE_mkSig_idxW cc y t w j
  have hrv : ∀ i : Fin (k + 2 + m),
      rvE cc (mkSig y w) i (mkZ y w t)
        = rexp (Fin.append (Fin.cons t⁻¹ (Fin.cons y cc) : Fin (k + 2) → ℝ) w i) := by
    refine Fin.addCases (m := k + 2) (n := m) ?_ ?_
    · intro u
      refine fin_two_cases (k := k)
        (C := fun u => rvE cc (mkSig y w) (Fin.castAdd m u) (mkZ y w t)
          = rexp (Fin.append (Fin.cons t⁻¹ (Fin.cons y cc) : Fin (k + 2) → ℝ) w
              (Fin.castAdd m u))) ?_ ?_ ?_ u
      · rw [append_castAdd_zero]
        exact rvE_mkSig_idxX cc y t w ht0 ht1
      · rw [append_castAdd_succ_zero]
        exact rvE_mkSig_idxY cc y t w
      · intro j
        rw [append_castAdd_succ_succ]
        exact rvE_mkSig_idxC cc y t w j
    · intro j
      rw [append_natAdd]
      exact rvE_mkSig_idxW cc y t w j
  have hEfun : Efun cc (mkSig y w) P (mkZ y w t)
      = rexpPolyEval P (Fin.append (Fin.cons t⁻¹ (Fin.cons y cc) : Fin (k + 2) → ℝ) w) :=
    Efun_eq_rexpPolyEval cc (mkSig y w) P (mkZ y w t) _ hval hrv
  have hEfun0 : Efun cc (mkSig y w) P (mkZ y w t) = 0 := by
    rw [hEfun, hP]
  have hD : ∀ d ∈ P.support, ∀ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m),
      bigSum (mkSig y w) x = true → d x ≤ P.totalDegree :=
    fun d hd x _ => exp_le_totalDegree hd x
  have hz : ∀ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m),
      bigSum (mkSig y w) x = true → mkZ y w t (Sum.elim coordOf coordOf x) ≠ 0 := by
    intro x hx
    rcases x with i | i
    · have hb : isBigB (mkSig y w) i = true := hx
      obtain ⟨-, hbig⟩ := coordOf_big (mkSig y w) hb
      simpa [Sum.elim_inl] using mkZ_ne_zero_of_big y t w ht0 (coordOf i) hbig
    · exact absurd hx (by simp [bigSum])
  have hPpart : Ppart cc (mkSig y w) P.totalDegree P (mkZ y w t) = 0 := by
    have h := Kall_mul_Efun cc (mkSig y w) P.totalDegree P (mkZ y w t) hD hz
    rw [hEfun0, mul_zero] at h
    exact h.symm
  have hsum : (∑ j : Fin (m + 2),
      (if mkSig y w j = VC.one then ((mkZ y w t j) ^ 2 - 1) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero (fun j _ => ?_)
    by_cases hjo : mkSig y w j = VC.one
    · rw [if_pos hjo, mkZ_sq_of_one y t w j hjo]
      norm_num
    · rw [if_neg hjo]
  have hF : pieceF cc (mkSig y w) P.totalDegree P (mkZ y w t) = 0 := by
    rw [pieceF, hPpart, hsum]
    norm_num
  have key : ∀ j : Fin (m + 2), ∀ r : Fin 2,
      0 < pieceG (mkSig y w) j r (mkZ y w t) := by
    intro j
    refine fin_two_cases (k := m)
      (C := fun j => ∀ r : Fin 2, 0 < pieceG (mkSig y w) j r (mkZ y w t)) ?_ ?_ ?_ j
    · intro r
      by_cases hr : (r : ℕ) = 0
      · have hrz : r = (0 : Fin 2) := Fin.ext (by simpa using hr)
        rw [hrz, pieceG_zero_zero, mkZ_zero]
        exact ht0
      · have h1 : (r : ℕ) = 1 := by have := r.isLt; omega
        have hr1 : r = (1 : Fin 2) := Fin.ext (by simpa using h1)
        rw [hr1, pieceG_zero_one, mkZ_zero]
        linarith
    · intro r
      have hj0 : ¬ (((Fin.succ (0 : Fin (m + 1)) : Fin (m + 2))) : ℕ) = 0 := by simp
      rw [pieceG, if_neg hj0]
      rw [mkSig_succ, mkCases_zero, mkZ_succ, pairVec_zero]
      exact coord_ineq y r
    · intro j r
      have hj0 : ¬ (((Fin.succ (Fin.succ j) : Fin (m + 2))) : ℕ) = 0 := by simp
      rw [pieceG, if_neg hj0]
      rw [mkSig_succ, mkCases_succ, mkZ_succ, pairVec_succ]
      exact coord_ineq (w j) r
  refine ⟨?_, ?_⟩
  · simp only [LiftPiece.set, BasicSA, piece]
    exact ⟨hF, fun q => key _ _⟩
  · have hinv : (piece cc (mkCases y w) P).inv = decide (caseOf y = VC.big) := by
      simp only [piece, mkCases_zero]
    change (if (piece cc (mkCases y w) P).inv
      then mkZ y w t (1 : Fin (m + 2)) * y = 1 else mkZ y w t (1 : Fin (m + 2)) = y)
    rw [hinv, mkZ_one]
    by_cases hb : caseOf y = VC.big
    · have hy : y ≠ 0 := by
        have h1 := caseOf_big hb
        intro h0; rw [h0, abs_zero] at h1; linarith
      rw [if_pos (by simp [hb]), if_pos hb, inv_mul_cancel₀ hy]
    · rw [if_neg (by simp [hb]), if_neg hb]

end Work.WilC4aL
