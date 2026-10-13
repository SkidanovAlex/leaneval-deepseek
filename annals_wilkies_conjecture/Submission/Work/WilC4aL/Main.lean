/-
  annals_wilkies_conjecture, area C4aL (`C4a_lift`): the assembly.

  Given an `RExpExist` set `Y ⊆ ℝ^{k+2}`, a parameter `c : Fin k → ℝ`, and a defining
  polynomial `P` for `Y` (with `m` existential witnesses), we produce the finite list of
  pieces `pieceList c P` and prove the slice equivalence of `SliceLift`.

  The two non-elementary inputs are taken here as explicit hypotheses (`hE` = the cleared
  equation identity, `hG` = goodness of each piece); they are proved in
  `Submission/Work/WilC4aL/Kall_mul_Efun.lean` and `.../piece_good.lean` and supplied in
  `Submission/Work/WilC4aL/Target.lean`.
-/
import Submission.Work.WilC4aL.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilC4aL
open WilkiesDesign WilkiesDesign.CG.C4a
open scoped BigOperators

variable {k m : ℕ}

/-! ## 1. Case selection -/

/-- Case of a real number: `one` when `v ^ 2 = 1`, `small` when `|v| < 1`, else `big`. -/
def caseOf (v : ℝ) : VC :=
  if v = 1 then VC.one else if v = -1 then VC.one else
    if |v| < 1 then VC.small else VC.big

theorem caseOf_one {v : ℝ} (h : caseOf v = VC.one) : v ^ 2 = 1 := by
  unfold caseOf at h
  by_cases h1 : v = 1
  · rw [if_pos h1] at h
    rw [h1]; norm_num
  · rw [if_neg h1] at h
    by_cases h2 : v = -1
    · rw [if_pos h2] at h
      rw [h2]; norm_num
    · rw [if_neg h2] at h
      by_cases h3 : |v| < 1
      · rw [if_pos h3] at h
        exact absurd h (by simp)
      · rw [if_neg h3] at h
        exact absurd h (by simp)

theorem caseOf_small {v : ℝ} (h : caseOf v = VC.small) : |v| < 1 := by
  unfold caseOf at h
  by_cases h1 : v = 1
  · rw [if_pos h1] at h; exact absurd h (by simp)
  · rw [if_neg h1] at h
    by_cases h2 : v = -1
    · rw [if_pos h2] at h; exact absurd h (by simp)
    · rw [if_neg h2] at h
      by_cases h3 : |v| < 1
      · rw [if_pos h3] at h; exact h3
      · rw [if_neg h3] at h; exact absurd h (by simp)

theorem caseOf_big {v : ℝ} (h : caseOf v = VC.big) : 1 < |v| := by
  unfold caseOf at h
  by_cases h1 : v = 1
  · rw [if_pos h1] at h; exact absurd h (by simp)
  · rw [if_neg h1] at h
    by_cases h2 : v = -1
    · rw [if_pos h2] at h; exact absurd h (by simp)
    · rw [if_neg h2] at h
      by_cases h3 : |v| < 1
      · rw [if_pos h3] at h; exact absurd h (by simp)
      · rw [if_neg h3] at h
        have hge : 1 ≤ |v| := not_lt.mp h3
        rcases lt_or_eq_of_le hge with hlt | heq
        · exact hlt
        · exfalso
          rcases (abs_eq (zero_le_one' ℝ)).mp heq.symm with hv | hv
          · exact h1 hv
          · exact h2 hv

theorem caseOf_ne_big_of_not {v : ℝ} (hs : caseOf v ≠ VC.big) (ho : caseOf v ≠ VC.one) :
    caseOf v = VC.small := by
  unfold caseOf at hs ho ⊢
  split_ifs at hs ho ⊢ <;> simp_all

/-- The case assignment attached to the data `y`, `w` of a slice point. -/
def pairVec (y : ℝ) (w : Fin m → ℝ) : Fin (m + 1) → ℝ := Fin.cons y w

def mkCases (y : ℝ) (w : Fin m → ℝ) : Fin (m + 1) → VC :=
  fun j => caseOf (pairVec y w j)

/-- The piece point attached to `y`, `w`, `t`: coordinate `0` is `t`, later coordinates are
`v` or `v⁻¹`, whichever is bounded. -/
def mkZ (y : ℝ) (w : Fin m → ℝ) (t : ℝ) : Fin (m + 2) → ℝ :=
  Fin.cons t fun j => if mkCases y w j = VC.big then (pairVec y w j)⁻¹ else pairVec y w j

theorem mkZ_zero (y t : ℝ) (w : Fin m → ℝ) : mkZ y w t 0 = t := rfl

theorem mkZ_succ (y t : ℝ) (w : Fin m → ℝ) (j : Fin (m + 1)) :
    mkZ y w t (Fin.succ j) =
      if caseOf (pairVec y w j) = VC.big then (pairVec y w j)⁻¹ else pairVec y w j := by
  rw [mkZ, Fin.cons_succ, mkCases]

theorem mkCases_zero (y : ℝ) (w : Fin m → ℝ) : mkCases y w 0 = caseOf y := by
  simp only [mkCases, pairVec, Fin.cons_zero]

theorem mkCases_succ (y : ℝ) (w : Fin m → ℝ) (j : Fin m) :
    mkCases y w (Fin.succ j) = caseOf (w j) := by
  simp only [mkCases, pairVec, Fin.cons_succ]

/-- A nonzero index of `Fin (n+1)` is a successor. -/
theorem fin_succ_surj {n : ℕ} (j : Fin (n + 1)) (hj : j ≠ 0) : ∃ i : Fin n, j = Fin.succ i := by
  obtain ⟨p, hp⟩ := j
  match p with
  | 0 => exact absurd (Fin.ext rfl) hj
  | (q + 1) => exact ⟨⟨q, by omega⟩, Fin.ext rfl⟩

/-- A real number is `1`, `-1`, or has `|·| ≠ 1`. -/
theorem abs_eq_one_or {v : ℝ} : |v| = 1 → v = 1 ∨ v = -1 := fun h =>
  (abs_eq (zero_le_one' ℝ)).mp h

/-! ## 2. The slice-point assembly -/

theorem append_castAdd_zero (cc : Fin k → ℝ) (y t : ℝ) (w : Fin m → ℝ) :
    Fin.append (Fin.cons t⁻¹ (Fin.cons y cc)) w (Fin.castAdd m (0 : Fin (k + 2))) = t⁻¹ := by
  rw [Fin.append_left, Fin.cons_zero]

theorem append_castAdd_succ_zero (cc : Fin k → ℝ) (y t : ℝ) (w : Fin m → ℝ) :
    Fin.append (Fin.cons t⁻¹ (Fin.cons y cc)) w (Fin.castAdd m (Fin.succ (0 : Fin (k + 1)))) =
      y := by
  rw [Fin.append_left, Fin.cons_succ, Fin.cons_zero]

theorem append_castAdd_succ_succ (cc : Fin k → ℝ) (y t : ℝ) (w : Fin m → ℝ) (j : Fin k) :
    Fin.append (Fin.cons t⁻¹ (Fin.cons y cc)) w
      (Fin.castAdd m (Fin.succ (Fin.succ j))) = cc j := by
  rw [Fin.append_left, Fin.cons_succ, Fin.cons_succ]

theorem append_natAdd (cc : Fin k → ℝ) (y t : ℝ) (w : Fin m → ℝ) (j : Fin m) :
    Fin.append (Fin.cons t⁻¹ (Fin.cons y cc)) w (Fin.natAdd (k + 2) j) = w j := by
  rw [Fin.append_right]

theorem castAdd_zero_eq_idxX : Fin.castAdd m (0 : Fin (k + 2)) = idxX (k := k) (m := m) := rfl

theorem castAdd_succ_zero_eq_idxY :
    Fin.castAdd m (Fin.succ (0 : Fin (k + 1))) = idxY (k := k) (m := m) := rfl

theorem castAdd_succ_succ_eq_idxC (j : Fin k) :
    Fin.castAdd m (Fin.succ (Fin.succ j)) = idxC (m := m) j := rfl

theorem natAdd_eq_idxW (j : Fin m) : Fin.natAdd (k + 2) j = idxW (k := k) j := rfl

/-- `Efun` is the `rexp`-polynomial evaluation at the substituted tuple. -/
theorem Efun_eq_rexpPolyEval (cc : Fin k → ℝ) (σ : Fin (m + 2) → VC)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ) (z : Fin (m + 2) → ℝ)
    (q : Fin (k + 2 + m) → ℝ) (hval : ∀ i, valE cc σ i z = q i)
    (hrv : ∀ i, rvE cc σ i z = rexp (q i)) : Efun cc σ P z = rexpPolyEval P q := by
  have h : Sum.elim (fun i => valE cc σ i z) (fun i => rvE cc σ i z)
      = Sum.elim q (fun i => rexp (q i)) := by
    funext x
    rcases x with i | i
    · exact hval i
    · exact hrv i
  rw [Efun, rexpPolyEval, h]

end Work.WilC4aL
