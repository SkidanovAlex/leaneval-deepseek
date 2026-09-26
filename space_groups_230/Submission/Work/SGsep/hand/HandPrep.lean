import Submission.Work.SGsep.hand.HandDefs2
import Submission.Work.SGsep.hand.AxisTab
import Submission.Work.SGsep.PairAux
import Submission.Work.SGsep.PairAux2
import Submission.Work.SGsep.table_facts

/-!
# Preparatory lemmas for the handedness separation

Mechanical material: conversions between `Data.V3` and `IVec`, arithmetic of `Data.M3` on
vectors, unpacking of the axis check `AxisW.chkCore`, and extraction of the per-index axis data
from the kernel-checked table statement `axisTab_spec`.
-/

namespace Work.SGsep.Hand

open Work.SG
open Work.SG.Data
open Work.SGsep.Hand.Data

/-! ## `V3` / `IVec` conversions -/

/-- An `IVec` read as a `V3`. -/
def toV3 (v : IVec) : V3 := ⟨v 0, v 1, v 2⟩

@[simp] theorem toV3_toFun (v : V3) : toV3 v.toFun = v := by cases v; rfl

theorem toFun_toV3 (v : IVec) : (toV3 v).toFun = v := by funext i; fin_cases i <;> rfl

@[simp] theorem toV3_zero : toV3 (0 : IVec) = V3.zero := rfl

@[simp] theorem toV3_neg (v : IVec) : toV3 (-v) = V3.negate (toV3 v) := rfl

@[simp] theorem toV3_smul (k : Int) (v : IVec) : toV3 (k • v) = V3.smul k (toV3 v) := rfl

theorem dot_toV3 (u v : IVec) : V3.dot (toV3 u) (toV3 v) = u ⬝ᵥ v := by
  simp [V3.dot, toV3, dotProduct, Fin.sum_univ_three]

theorem toRealV_toV3 (v : IVec) : toRealV (toV3 v) = toRVec v := by
  funext i; fin_cases i <;> rfl

theorem toRealV_eq_toRVec (v : V3) : toRealV v = toRVec v.toFun := rfl

theorem toV3_ne_zero {v : IVec} (h : v ≠ 0) : toV3 v ≠ V3.zero := by
  intro hc
  refine h (funext fun i => ?_)
  have hx : (toV3 v).x = V3.zero.x := by rw [hc]
  have hy : (toV3 v).y = V3.zero.y := by rw [hc]
  have hz : (toV3 v).z = V3.zero.z := by rw [hc]
  fin_cases i
  · exact hx
  · exact hy
  · exact hz

theorem toV3_ne_zero' {v : IVec} (h : toV3 v ≠ V3.zero) : v ≠ 0 := by
  intro hc; exact h (by rw [hc]; rfl)

theorem prim_toV3 {v : IVec} (h : PrimIVec v) : V3.Prim (toV3 v) := by
  obtain ⟨β, hβ⟩ := h
  exact ⟨toV3 β, by rw [dot_toV3]; exact hβ⟩

theorem Prim_of_toV3 {v : IVec} (h : V3.Prim (toV3 v)) : PrimIVec v := by
  obtain ⟨β, hβ⟩ := h
  exact ⟨β.toFun, by rw [← dot_toV3, toV3_toFun]; exact hβ⟩

/-! ## Arithmetic of `M3` on vectors -/

theorem mulV_sub (A B : M3) (v : V3) :
    (M3.sub A B).mulV v = V3.sub (A.mulV v) (B.mulV v) := by
  apply V3.toFun_injective
  funext i
  fin_cases i <;> simp [M3.sub, M3.mulV, V3.sub, V3.toFun] <;> ring

theorem mulV_one (v : V3) : M3.one.mulV v = v := by
  apply V3.toFun_injective
  funext i
  fin_cases i <;> simp [M3.one, M3.mulV, V3.toFun]

theorem mulV_sub_one {A : M3} {v : V3} (h : A.mulV v = v) :
    (M3.sub A M3.one).mulV v = V3.zero := by
  apply V3.toFun_injective
  rw [mulV_sub, h, mulV_one]
  funext i
  fin_cases i <;> simp [V3.sub, V3.toFun, V3.zero]

theorem mulV_smul (A : M3) (k : Int) (v : V3) :
    A.mulV (V3.smul k v) = V3.smul k (A.mulV v) := by
  apply V3.toFun_injective
  funext i
  fin_cases i <;> simp [M3.mulV, V3.smul, V3.toFun] <;> ring

theorem mulV_toFun (A : M3) (v : V3) : (A.mulV v).toFun = A.toIMat.mulVec v.toFun := by
  funext i
  fin_cases i <;>
    simp [M3.mulV, M3.toIMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, V3.toFun]

theorem mulV_eq_zero_iff {A : M3} {v : V3} :
    A.mulV v = V3.zero ↔ A.toIMat.mulVec v.toFun = 0 := by
  constructor
  · intro h
    have h' : (A.mulV v).toFun = 0 := by rw [h]; funext i; fin_cases i <;> rfl
    rw [mulV_toFun] at h'
    exact h'
  · intro h
    apply V3.toFun_injective
    rw [mulV_toFun, h]
    funext i; fin_cases i <;> rfl

/-! ## Unpacking the axis check -/

theorem chkCore_facts {A : M3} {w : AxisW} (h : w.chkCore A = true) :
    w.m ≠ 0 ∧ (M3.sub A M3.one).mulV w.z = V3.zero ∧ V3.gcdV w.z = 1 ∧
    V3.cross (M3.row (M3.sub A M3.one) w.p) (M3.row (M3.sub A M3.one) w.q) =
      V3.smul w.m w.z ∧
    (w.eps = 1 ∨ w.eps = -1) ∧ M3.Symm (M3.form A w.z) = true ∧
    M3.psd (M3.smulM w.eps (M3.form A w.z)) = true := by
  rw [AxisW.chkCore] at h
  obtain ⟨h, hpsd⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, hsymm⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, heps⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, hcross⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h, hgcd⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hm0, hmulV⟩ := Bool.and_eq_true_iff.mp h
  have hm : w.m ≠ 0 := by
    intro hc
    rw [beq_iff_eq.mpr hc] at hm0
    exact Bool.false_ne_true hm0
  exact ⟨hm, beq_iff_eq.mp hmulV, beq_iff_eq.mp hgcd, beq_iff_eq.mp hcross,
    (by rcases Bool.or_eq_true_iff.mp heps with h | h
        · exact Or.inl (beq_iff_eq.mp h)
        · exact Or.inr (beq_iff_eq.mp h)), hsymm, hpsd⟩

theorem chkCore_z {A : M3} {w : AxisW} (h : w.chkCore A = true) :
    (M3.sub A M3.one).mulV w.z = V3.zero := (chkCore_facts h).2.1

theorem chkCore_gcd {A : M3} {w : AxisW} (h : w.chkCore A = true) : V3.gcdV w.z = 1 :=
  (chkCore_facts h).2.2.1

theorem chkCore_cross {A : M3} {w : AxisW} (h : w.chkCore A = true) :
    V3.cross (M3.row (M3.sub A M3.one) w.p) (M3.row (M3.sub A M3.one) w.q) =
      V3.smul w.m w.z := (chkCore_facts h).2.2.2.1

theorem chkCore_eps {A : M3} {w : AxisW} (h : w.chkCore A = true) :
    w.eps = 1 ∨ w.eps = -1 := (chkCore_facts h).2.2.2.2.1

theorem chkCore_psd {A : M3} {w : AxisW} (h : w.chkCore A = true) :
    M3.psd (M3.smulM w.eps (M3.form A w.z)) = true := (chkCore_facts h).2.2.2.2.2.2

/-! ## The axis table, per index -/

/-- The axis datum attached to the element `i` of representative `k`. -/
def axisAt (k : Fin 230) (i : Nat) : Option AxisW := (axisTab.getD k.val []).getD i none

theorem axisAt_spec {k : Fin 230} {i : Nat} (hi : i < (repArith k.val).n) :
    (match axisAt k i with
      | none => ¬ ((A3n k.val i).det = 1 ∧ 3 ≤ (A3n k.val i).ord)
      | some w => (A3n k.val i).det = 1 ∧ 3 ≤ (A3n k.val i).ord ∧
          w.chkCore (A3n k.val i) = true) := by
  have h3 : (match axisAt k i with
      | none => !((M3.det (A3n k.val i) == 1) && decide (3 ≤ M3.ord (A3n k.val i)))
      | some w => (M3.det (A3n k.val i) == 1) && decide (3 ≤ M3.ord (A3n k.val i)) &&
          w.chkCore (A3n k.val i)) = true := by
    unfold axisAt
    have h1 := axisTab_spec
    rw [List.all_eq_true] at h1
    have h2 := h1 k.val (List.mem_range.mpr k.isLt)
    rw [List.all_eq_true] at h2
    exact h2 i (List.mem_range.mpr hi)
  cases hx : axisAt k i with
  | none =>
      rw [hx] at h3
      intro hcon
      have hb : ((A3n k.val i).det == 1 && decide (3 ≤ (A3n k.val i).ord)) = true := by
        rw [Bool.and_eq_true_iff]
        exact ⟨beq_iff_eq.mpr hcon.1, decide_eq_true_eq.mpr hcon.2⟩
      rw [hb] at h3
      exact Bool.false_ne_true h3
  | some w =>
      rw [hx] at h3
      obtain ⟨h31, h32⟩ := Bool.and_eq_true_iff.mp h3
      obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h31
      exact ⟨beq_iff_eq.mp ha, of_decide_eq_true hb, h32⟩

/-- At a rotation the axis datum exists and passes the check. -/
theorem axisAt_rot {k : Fin 230} {i : Nat} (hi : i < (repArith k.val).n)
    (hrot : (A3n k.val i).det = 1 ∧ 3 ≤ (A3n k.val i).ord) :
    ∃ w, axisAt k i = some w ∧ w.chkCore (A3n k.val i) = true := by
  have h := axisAt_spec (k := k) (i := i) hi
  cases hx : axisAt k i with
  | none => rw [hx] at h; exact absurd hrot h
  | some w => rw [hx] at h; exact ⟨w, rfl, h.2.2⟩

/-- At a non-rotation the axis datum is `none`. -/
theorem axisAt_none {k : Fin 230} {i : Nat} (hi : i < (repArith k.val).n)
    (h : axisAt k i = none) : ¬ ((A3n k.val i).det = 1 ∧ 3 ≤ (A3n k.val i).ord) := by
  have h' := axisAt_spec (k := k) (i := i) hi
  rw [h] at h'; exact h'


/-! ## The column determinant -/

theorem detCols_eq_formula (u v w : Fin 3 → ℝ) :
    detCols u v w = u 0 * (v 1 * w 2 - v 2 * w 1) - v 0 * (u 1 * w 2 - u 2 * w 1) +
      w 0 * (u 1 * v 2 - u 2 * v 1) := by
  rw [detCols, Matrix.det_transpose, Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  simp
  ring

/-- Negating the third column of the orientation determinant. -/
theorem detCols_neg3 (u v w : Fin 3 → ℝ) :
    detCols u v (fun i => -w i) = -detCols u v w := by
  rw [detCols_eq_formula, detCols_eq_formula]
  ring

/-- Scaling the third column of the orientation determinant. -/
theorem detCols_smul3 (u v : Fin 3 → ℝ) (c : ℝ) (w : Fin 3 → ℝ) :
    detCols u v (fun i => c * w i) = c * detCols u v w := by
  rw [detCols_eq_formula, detCols_eq_formula]
  ring

theorem detCols_ofCols (u v w : V3) :
    M3.det (M3.ofCols u v w) = detCols (toRealV u) (toRealV v) (toRealV w) := by
  rw [detCols_eq_formula]
  simp only [M3.det, M3.ofCols, toRealV, toRVec, V3.toFun]
  push_cast
  ring

/-! ## Rows and the real/int cast of vectors -/

theorem dot_row_of_mulV_zero (A : M3) (j : Nat) (v : V3) (h : A.mulV v = V3.zero) :
    V3.dot (M3.row A j) v = 0 := by
  by_cases hj0 : j = 0
  · subst hj0
    have hx := congrArg V3.x h
    simpa [M3.row, M3.mulV, V3.dot, V3.zero] using hx
  · by_cases hj1 : j = 1
    · subst hj1
      have hy := congrArg V3.y h
      simpa [M3.row, M3.mulV, V3.dot, V3.zero, hj0] using hy
    · have hz := congrArg V3.z h
      simpa [M3.row, M3.mulV, V3.dot, V3.zero, hj0, hj1] using hz

@[simp] theorem toRealV_negate (v : V3) :
    toRealV (V3.negate v) = fun i => -(toRealV v i) := by
  funext i; fin_cases i <;> simp [V3.negate, V3.toFun, toRealV, toRVec]

@[simp] theorem toRealV_smul (c : Int) (v : V3) :
    toRealV (V3.smul c v) = fun i => (c : ℝ) * toRealV v i := by
  funext i; fin_cases i <;> simp [V3.smul, V3.toFun, toRealV, toRVec]

theorem toRealV_injective : Function.Injective toRealV := by
  intro u v h
  exact V3.toFun_injective (toRVec_injective h)

theorem Ah_mem {k : Fin 230} {i : Nat} (hi : i < (repArith k.val).n) :
    Ah k i ∈ arithRep (sgArith k) := by
  rw [← Work.SGsep.mem_Tk_iff]
  exact (PSep.mem_Tk_iff_exists k (Ah k i)).mpr ⟨i, hi, rfl⟩

@[simp] theorem toRealV_zero : toRealV (V3.zero) = 0 := by
  funext i; fin_cases i <;> simp [toRealV, toRVec, V3.toFun, V3.zero]

theorem toRealV_smul_eq (c : Int) (v : V3) : toRealV (V3.smul c v) = (c : ℝ) • toRealV v := by
  rw [toRealV_smul]; rfl

theorem toRealV_ne_zero {v : V3} (h : toRealV v ≠ 0) : v ≠ V3.zero := by
  intro hc; exact h (by rw [hc, toRealV_zero])

theorem toRealV_ne_zero' {v : V3} (h : v ≠ V3.zero) : toRealV v ≠ 0 := by
  intro hc
  exact h (toRealV_injective (by rw [hc, toRealV_zero]))

end Work.SGsep.Hand
