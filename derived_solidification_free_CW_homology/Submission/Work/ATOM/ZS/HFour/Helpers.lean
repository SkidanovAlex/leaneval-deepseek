import Mathlib
import Submission.Work.ATOM.ZS.HFour.Defs

/-!
# AREA ATOM / `ℤ[S]`: pointwise helpers for the closed cover of `(ℕ∪∞) × T'`

This file collects the elementary pointwise computations used to prove
`Work.ATOM.ZS.hFour_cover`: the values of `pr₂T`, `betaT` and `φ_P` on a point of `T' = tSet S`
over a finite index `j`, and the basic facts about levels of `a j` and of `e_{n(j)-1} a j`.

Everything here is sorry-free, so that it can be imported by the files proving the individual
cases of the cover.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid
open OnePoint

noncomputable section

namespace Work.ATOM.ZS

variable {S : LightProfinite.{0}} [Infinite S]

/-! ## The maps on `T'` -/

/-- `φ_P(k,∞) = ∞` for every `k`. -/
lemma phiPFun_infty_right (k : ℕ∪{∞}) : phiPFun S (k, (∞ : ℕ∪{∞})) = ∞ := by
  rcases k with _ | k
  · exact phiPFun_infty_left _
  · exact phiPFun_some_infty k

/-- The shift fixes `∞`. -/
lemma shift_infty : LightProfinite.shift (∞ : ℕ∪{∞}) = ∞ := rfl

/-- The shift is `n ↦ n+1` on finite points. -/
lemma shift_some (m : ℕ) :
    LightProfinite.shift (((m : ℕ) : ℕ∪{∞})) = (((m + 1 : ℕ) : ℕ∪{∞})) := rfl

/-- Over a finite index `j`, the second projection of `T'` is `a j`. -/
lemma pr₂T_of_finite (t : ↥(T' S)) {j : ℕ} (h : tProj S t = ((j : ℕ) : ℕ∪{∞})) :
    pr₂T S t = (levelData S).a j := by
  have h1 : t.1.1 = ((j : ℕ) : ℕ∪{∞}) := h
  have h2 := tSet_second_eq (S := S) t.2 h1
  have : pr₂T S t = t.1.2 := rfl
  rw [this]
  exact h2

/-- Over a finite index `j`, `β` is `e_{n(j)-1} a_j` (and `s₀` when `n(j) = 0`). -/
lemma betaT_of_finite (t : ↥(T' S)) {j : ℕ} (h : tProj S t = ((j : ℕ) : ℕ∪{∞})) :
    betaT S t = (if lvl S j = 0 then (levelData S).s₀ else
      e S (lvl S j - 1) ((levelData S).a j)) := by
  have h1 : t.1.1 = ((j : ℕ) : ℕ∪{∞}) := h
  have h2 := tSet_second_eq (S := S) t.2 h1
  have hp : t.1 = (((j : ℕ) : ℕ∪{∞}), (levelData S).a j) := Prod.ext h1 h2
  have : betaT S t = betaFun S t.1 := rfl
  rw [this, hp, betaFun_lvl]

/-- Over a finite index `j`, the underlying point of `T'` is `(j, a_j)`. -/
lemma T'_eq_of_finite (t : ↥(T' S)) {j : ℕ} (h : tProj S t = ((j : ℕ) : ℕ∪{∞})) :
    t.1 = (((j : ℕ) : ℕ∪{∞}), (levelData S).a j) :=
  Prod.ext (show t.1.1 = ((j : ℕ) : ℕ∪{∞}) from h)
    (tSet_second_eq (S := S) t.2 (show t.1.1 = ((j : ℕ) : ℕ∪{∞}) from h))

/-! ## Levels and the tower `e_n` -/

/-- `a j` lies in `A_{n(j)}`. -/
lemma a_mem_A (j : ℕ) : (levelData S).a j ∈ A S (lvl S j) :=
  (levelData S).lv_mem _ (levelData_a_mem j)

/-- If `n(j) ≤ m` then `e_m` fixes `a_j`. -/
lemma e_a_of_le {j m : ℕ} (h : lvl S j ≤ m) : e S m ((levelData S).a j) = (levelData S).a j :=
  e_fix_of_mem_A_of_le S h (a_mem_A j)

/-- Element form of the composition rule `e_a ≫ e_b = e_{min a b}`:
`e_b (e_a x) = e_{min a b} x`. -/
lemma e_comp_apply (a b : ℕ) (x : ↥S) : e S b (e S a x) = e S (min a b) x := by
  have h := ConcreteCategory.congr_hom ((levelData S).e_comp a b) x
  rw [ConcreteCategory.comp_apply] at h
  exact h

/-- `e_{n(j)-1} a_j` has level `< n(j)` (when `n(j) > 0`). -/
lemma lv_e_pred_a_lt (j : ℕ) (h : 0 < lvl S j) :
    (levelData S).lv (e S (lvl S j - 1) ((levelData S).a j)) < lvl S j := by
  have hle : (levelData S).lv (e S (lvl S j - 1) ((levelData S).a j)) ≤ lvl S j - 1 :=
    levelData_lv_le (y := e S (lvl S j - 1) ((levelData S).a j)) ⟨(levelData S).a j, rfl⟩
  omega

/-- `e_m` fixes `e_{n(j)-1} a_j` as soon as `n(j)-1 ≤ m`. -/
lemma e_e_pred_a_of_le {j m : ℕ} (h : lvl S j - 1 ≤ m) :
    e S m (e S (lvl S j - 1) ((levelData S).a j)) = e S (lvl S j - 1) ((levelData S).a j) := by
  rw [e_comp_apply, Nat.min_eq_left h]

/-- The base point is not in the enumeration. -/
lemma s0_notMem_range_a : (levelData S).s₀ ∉ Set.range (levelData S).a := by
  rintro ⟨j, hj⟩
  exact levelData_a_ne j hj

/-- Every `e_m` fixes the base point. -/
lemma e_s0 (m : ℕ) : e S m ((levelData S).s₀) = (levelData S).s₀ := (levelData S).e_fix m

/-! ## Values of `ψ` -/

/-- `ψ(n(j), a_j) = j`. -/
lemma psiFun_lvl_a (j : ℕ) :
    psiFun S (((lvl S j : ℕ) : ℕ∪{∞}), (levelData S).a j) = ((j : ℕ) : ℕ∪{∞}) :=
  psiFun_some_eq (lvl S j) (levelData_e_lvl_a j) rfl

/-- `ψ(m,x) = ∞` as soon as `e_m x` is not an enumerated point. -/
lemma psiFun_eq_infty_of_notMem (m : ℕ) {x : ↥S}
    (h : e S m x ∉ Set.range (levelData S).a) :
    psiFun S (((m : ℕ) : ℕ∪{∞}), x) = ∞ :=
  psiFun_some_eq_infty m (fun hc => h hc.1)

/-- `ψ(m,x) = ∞` as soon as `e_m x` does not have level `m`. -/
lemma psiFun_eq_infty_of_lv_ne (m : ℕ) {x : ↥S}
    (h : (levelData S).lv (e S m x) ≠ m) :
    psiFun S (((m : ℕ) : ℕ∪{∞}), x) = ∞ :=
  psiFun_some_eq_infty m (fun hc => h hc.2)

/-! ## The two `ψ`-terms of `h₄` over a finite fibre of `T'` -/

/-- **The `β`-term vanishes when `n(j) ≤ k`.**  For `t : T' S` over the finite index `j`,
`β t` is `e_{n(j)-1} a_j` (or `s₀` when `n(j) = 0`); it is fixed by `e_k` (since `n(j) ≤ k`), and
its level is `< n(j) ≤ k` (or it is the base point, which is not enumerated), so `ψ(k, β t) = ∞`. -/
lemma psiFun_betaT_eq_infty {j k : ℕ} (t : ↥(T' S))
    (hpj : tProj S t = ((j : ℕ) : ℕ∪{∞})) (h : lvl S j ≤ k) :
    psiFun S (((k : ℕ) : ℕ∪{∞}), betaT S t) = ∞ := by
  rw [betaT_of_finite t hpj]
  split_ifs with h0
  · exact psiFun_eq_infty_of_notMem k (by rw [e_s0]; exact s0_notMem_range_a)
  · refine psiFun_eq_infty_of_lv_ne k ?_
    rw [e_e_pred_a_of_le (by omega : lvl S j - 1 ≤ k)]
    exact ne_of_lt (lt_of_lt_of_le (lv_e_pred_a_lt j (by omega)) h)

/-- **The `pr₂`-term vanishes when `n(j) < k`.**  For `t : T' S` over the finite index `j`,
`pr₂ t = a_j` is fixed by `e_k` (since `n(j) ≤ k`) and has level `n(j) ≠ k`, so
`ψ(k, pr₂ t) = ∞`. -/
lemma psiFun_pr2T_eq_infty {j k : ℕ} (t : ↥(T' S))
    (hpj : tProj S t = ((j : ℕ) : ℕ∪{∞})) (h : lvl S j < k) :
    psiFun S (((k : ℕ) : ℕ∪{∞}), pr₂T S t) = ∞ := by
  rw [pr₂T_of_finite t hpj]
  refine psiFun_eq_infty_of_lv_ne k ?_
  rw [e_a_of_le (le_of_lt h)]
  exact ne_of_lt h

end Work.ATOM.ZS
