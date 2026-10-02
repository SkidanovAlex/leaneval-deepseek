import Mathlib
import Submission.Work.RatHurewicz.cubePinchDefs
import Submission.Work.Stems.HomAdd.PrismFaces
import Submission.Work.Stems.HomAdd.cl_rhoPos
import Submission.Work.Stems.HomAdd.cl_rhoNeg
import Submission.Work.RatHurewicz.GluingPinch.CutGen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The prism ("kill") construction for the homotopy addition theorem

For a `(k+1)`-cube `g` which is `x₀` on the `(k-1)`-skeleton (`SkCube k x₀ g`), the `(castSucc i, 1)`
face can be *killed* by composing with an explicit coordinate map `killCMPos k i` (and the
`(castSucc i, 0)` face by `killCMNeg k i`).  The killed cube is again an `SkCube`, its faces have
the same classes as those of `g` except that the killed face becomes the constant cube, and its top
face `(last, 1)` gains the factor `(cl F_{castSucc i, 1})^((-1)^{k-i})`.

Consequently the invariant

  `R g = (∏ j, (cl F_{j,0})^{s j 0} (cl F_{j,1})^{s j 1}) · cl F_{last,1} / cl F_{last,0}`,
  `s j b = (-1)^{j+b+k+1}`,

is unchanged by each kill; after killing all `2k` side faces the side faces are *literally* constant,
and then `R = 1` (the `last`-slices are a homotopy of based cubes from the bottom to the top face).
Hence `R g = 1` for every `SkCube`, and the theorem follows by group algebra.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz.GluingPinch

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-- A `(k+1)`-cube which is `x₀` on the `(k-1)`-skeleton (`Work.RatHurewicz.InSkel`). -/
def SkCube (k : ℕ) (x₀ : X) (g : C(IC (k + 1), X)) : Prop :=
  ∀ z : IC (k + 1), Work.RatHurewicz.InSkel k z → g z = x₀


/-! ## Elementary `clamp` facts -/

theorem clamp_eq_one_of_one_le {r : ℝ} (h : 1 ≤ r) : Work.Stems.Hur2.clamp r = 1 := by
  rw [Work.Stems.Hur2.clamp, Set.projIcc_of_right_le zero_le_one h]
  rfl

theorem clamp_eq_zero_of_nonpos {r : ℝ} (h : r ≤ 0) : Work.Stems.Hur2.clamp r = 0 := by
  rw [Work.Stems.Hur2.clamp, Set.projIcc_of_le_left zero_le_one h]
  rfl

/-! ## The kill maps -/

/-- The coordinate map of the `killPos` operation: the `castSucc i` coordinate is stretched to `1`
and the last coordinate multiplied by `1 - t` and clamped. -/
def killCMPos (k : ℕ) (i : Fin k) : C(IC (k + 1), IC (k + 1)) where
  toFun z := Function.update (Function.update z (Fin.castSucc i)
      (Work.Stems.Hur2.clamp (2 * ((z (Fin.castSucc i) : unitInterval) : ℝ)))) (Fin.last k)
      (z (Fin.last k) * Work.Stems.Hur2.clamp (2 - 2 * ((z (Fin.castSucc i) : unitInterval) : ℝ)))
  continuous_toFun := by
    apply Continuous.update
    · apply Continuous.update
      · exact continuous_id
      · exact Work.Stems.Hur2.continuous_clamp.comp (by fun_prop)
    · refine Continuous.mul (continuous_apply _) ?_
      refine Work.Stems.Hur2.continuous_clamp.comp ?_
      fun_prop

/-- The coordinate map of the `killNeg` operation. -/
def killCMNeg (k : ℕ) (i : Fin k) : C(IC (k + 1), IC (k + 1)) where
  toFun z := Function.update (Function.update z (Fin.castSucc i)
      (Work.Stems.Hur2.clamp (2 * ((z (Fin.castSucc i) : unitInterval) : ℝ) - 1))) (Fin.last k)
      (z (Fin.last k) * Work.Stems.Hur2.clamp (2 * ((z (Fin.castSucc i) : unitInterval) : ℝ)))
  continuous_toFun := by
    apply Continuous.update
    · apply Continuous.update
      · exact continuous_id
      · exact Work.Stems.Hur2.continuous_clamp.comp (by fun_prop)
    · refine Continuous.mul (continuous_apply _) ?_
      refine Work.Stems.Hur2.continuous_clamp.comp ?_
      fun_prop

@[simp] theorem killCMPos_apply (k : ℕ) (i : Fin k) (z : IC (k + 1)) :
    killCMPos k i z = Function.update (Function.update z (Fin.castSucc i)
      (Work.Stems.Hur2.clamp (2 * ((z (Fin.castSucc i) : unitInterval) : ℝ)))) (Fin.last k)
      (z (Fin.last k) * Work.Stems.Hur2.clamp
        (2 - 2 * ((z (Fin.castSucc i) : unitInterval) : ℝ))) := rfl

@[simp] theorem killCMNeg_apply (k : ℕ) (i : Fin k) (z : IC (k + 1)) :
    killCMNeg k i z = Function.update (Function.update z (Fin.castSucc i)
      (Work.Stems.Hur2.clamp (2 * ((z (Fin.castSucc i) : unitInterval) : ℝ) - 1))) (Fin.last k)
      (z (Fin.last k) * Work.Stems.Hur2.clamp
        (2 * ((z (Fin.castSucc i) : unitInterval) : ℝ))) := rfl

theorem killCMPos_apply_castSucc (k : ℕ) (i : Fin k) (z : IC (k + 1)) :
    killCMPos k i z (Fin.castSucc i)
      = Work.Stems.Hur2.clamp (2 * ((z (Fin.castSucc i) : unitInterval) : ℝ)) := by
  rw [killCMPos_apply, Function.update_apply, if_neg (Fin.castSucc_ne_last i),
    Function.update_apply, if_pos rfl]

theorem killCMPos_apply_last (k : ℕ) (i : Fin k) (z : IC (k + 1)) :
    killCMPos k i z (Fin.last k) = z (Fin.last k) * Work.Stems.Hur2.clamp
      (2 - 2 * ((z (Fin.castSucc i) : unitInterval) : ℝ)) := by
  rw [killCMPos_apply, Function.update_apply, if_pos rfl]

theorem killCMPos_apply_of_ne (k : ℕ) (i : Fin k) {j : Fin (k + 1)}
    (hji : j ≠ Fin.castSucc i) (hjl : j ≠ Fin.last k) (z : IC (k + 1)) :
    killCMPos k i z j = z j := by
  rw [killCMPos_apply, Function.update_apply, if_neg hjl, Function.update_apply, if_neg hji]

theorem killCMNeg_apply_castSucc (k : ℕ) (i : Fin k) (z : IC (k + 1)) :
    killCMNeg k i z (Fin.castSucc i)
      = Work.Stems.Hur2.clamp (2 * ((z (Fin.castSucc i) : unitInterval) : ℝ) - 1) := by
  rw [killCMNeg_apply, Function.update_apply, if_neg (Fin.castSucc_ne_last i),
    Function.update_apply, if_pos rfl]

theorem killCMNeg_apply_last (k : ℕ) (i : Fin k) (z : IC (k + 1)) :
    killCMNeg k i z (Fin.last k) = z (Fin.last k) * Work.Stems.Hur2.clamp
      (2 * ((z (Fin.castSucc i) : unitInterval) : ℝ)) := by
  rw [killCMNeg_apply, Function.update_apply, if_pos rfl]

theorem killCMNeg_apply_of_ne (k : ℕ) (i : Fin k) {j : Fin (k + 1)}
    (hji : j ≠ Fin.castSucc i) (hjl : j ≠ Fin.last k) (z : IC (k + 1)) :
    killCMNeg k i z j = z j := by
  rw [killCMNeg_apply, Function.update_apply, if_neg hjl, Function.update_apply, if_neg hji]

/-- The killed cube (killing the `(castSucc i, 1)` face). -/
def killPos (k : ℕ) (i : Fin k) (g : C(IC (k + 1), X)) : C(IC (k + 1), X) :=
  g.comp (killCMPos k i)

/-- The killed cube (killing the `(castSucc i, 0)` face). -/
def killNeg (k : ℕ) (i : Fin k) (g : C(IC (k + 1), X)) : C(IC (k + 1), X) :=
  g.comp (killCMNeg k i)

@[simp] theorem killPos_apply (k : ℕ) (i : Fin k) (g : C(IC (k + 1), X)) (z : IC (k + 1)) :
    killPos k i g z = g (killCMPos k i z) := rfl

@[simp] theorem killNeg_apply (k : ℕ) (i : Fin k) (g : C(IC (k + 1), X)) (z : IC (k + 1)) :
    killNeg k i g z = g (killCMNeg k i z) := rfl

/-! ## Elementary `clamp` computations at the two halves -/

theorem clamp_two (t : unitInterval) (h : 1 / 2 ≤ (t : ℝ)) :
    Work.Stems.Hur2.clamp (2 * (t : ℝ)) = 1 :=
  clamp_eq_one_of_one_le (by linarith)

theorem clamp_two_sub (t : unitInterval) (h : (t : ℝ) ≤ 1 / 2) :
    Work.Stems.Hur2.clamp (2 - 2 * (t : ℝ)) = 1 :=
  clamp_eq_one_of_one_le (by linarith)

theorem clamp_two_sub_symm (t : unitInterval) (h : 1 / 2 ≤ (t : ℝ)) :
    Work.Stems.Hur2.clamp (2 - 2 * (t : ℝ))
      = unitInterval.symm (Work.Stems.Hur2.clamp (2 * (t : ℝ) - 1)) := by
  have ht1 : (0 : ℝ) ≤ (t : ℝ) := (t.2).1
  have ht2 : (t : ℝ) ≤ 1 := (t.2).2
  have h1 : (2 - 2 * (t : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have h2 : (2 * (t : ℝ) - 1) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  rw [Work.Stems.Hur2.clamp_of_mem h1, Work.Stems.Hur2.clamp_of_mem h2]
  apply Subtype.ext
  simp only [unitInterval.coe_symm_eq]
  ring

theorem killCMPos_apply_left {k : ℕ} (i : Fin k) {z : IC (k + 1)}
    (hz : ((z (Fin.castSucc i) : unitInterval) : ℝ) ≤ 1 / 2) (j : Fin (k + 1)) :
    killCMPos k i z j = (if j = Fin.last k then z (Fin.last k)
      else if j = Fin.castSucc i
        then Work.Stems.Hur2.clamp (2 * ((z (Fin.castSucc i) : unitInterval) : ℝ))
      else z j) := by
  rw [killCMPos_apply, Function.update_apply, Function.update_apply, clamp_two_sub _ hz, mul_one]

theorem killCMPos_apply_right {k : ℕ} (i : Fin k) {z : IC (k + 1)}
    (hz : 1 / 2 ≤ ((z (Fin.castSucc i) : unitInterval) : ℝ)) (j : Fin (k + 1)) :
    killCMPos k i z j = (if j = Fin.last k
        then z (Fin.last k) * unitInterval.symm
          (Work.Stems.Hur2.clamp (2 * ((z (Fin.castSucc i) : unitInterval) : ℝ) - 1))
      else if j = Fin.castSucc i then 1
      else z j) := by
  rw [killCMPos_apply, Function.update_apply, Function.update_apply,
    clamp_two (z (Fin.castSucc i)) hz, clamp_two_sub_symm (z (Fin.castSucc i)) hz]

theorem killCMNeg_apply_left {k : ℕ} (i : Fin k) {z : IC (k + 1)}
    (hz : ((z (Fin.castSucc i) : unitInterval) : ℝ) ≤ 1 / 2) (j : Fin (k + 1)) :
    killCMNeg k i z j = (if j = Fin.last k
        then z (Fin.last k) * Work.Stems.Hur2.clamp (2 * ((z (Fin.castSucc i) : unitInterval) : ℝ))
      else if j = Fin.castSucc i then 0
      else z j) := by
  rw [killCMNeg_apply, Function.update_apply, Function.update_apply,
    clamp_eq_zero_of_nonpos (show 2 * ((z (Fin.castSucc i) : unitInterval) : ℝ) - 1 ≤ 0 by linarith)]

theorem killCMNeg_apply_right {k : ℕ} (i : Fin k) {z : IC (k + 1)}
    (hz : 1 / 2 ≤ ((z (Fin.castSucc i) : unitInterval) : ℝ)) (j : Fin (k + 1)) :
    killCMNeg k i z j = (if j = Fin.last k then z (Fin.last k)
      else if j = Fin.castSucc i
        then Work.Stems.Hur2.clamp (2 * ((z (Fin.castSucc i) : unitInterval) : ℝ) - 1)
      else z j) := by
  rw [killCMNeg_apply, Function.update_apply, Function.update_apply,
    clamp_two (z (Fin.castSucc i)) hz, mul_one]


/-! ## The killed cube is again an `SkCube` -/

theorem clamp_two_zero : Work.Stems.Hur2.clamp (2 * ((0 : unitInterval) : ℝ)) = 0 := by
  rw [show (2 : ℝ) * ((0 : unitInterval) : ℝ) = 0 by norm_num]
  exact Work.Stems.Hur2.clamp_zero

theorem clamp_two_one : Work.Stems.Hur2.clamp (2 * ((1 : unitInterval) : ℝ)) = 1 :=
  clamp_eq_one_of_one_le (by norm_num)

theorem clamp_two_mul_zero_sub_one :
    Work.Stems.Hur2.clamp (2 * ((0 : unitInterval) : ℝ) - 1) = 0 := by
  rw [show (2 : ℝ) * ((0 : unitInterval) : ℝ) - 1 = -1 by norm_num]
  exact clamp_eq_zero_of_nonpos (by norm_num)

/-- `z_{castSucc i} = 1` contradicts `t ≤ 1/2`. -/
theorem not_le_half_of_eq_one {k : ℕ} (i : Fin k) {z : IC (k + 1)}
    (h : z (Fin.castSucc i) = 1) : ¬(((z (Fin.castSucc i) : unitInterval) : ℝ) ≤ 1 / 2) := by
  intro ht
  have h1 : ((z (Fin.castSucc i) : unitInterval) : ℝ) = 1 := by simp [h]
  rw [h1] at ht
  norm_num at ht

/-- `z_{castSucc i} = 0` contradicts `1/2 ≤ t`. -/
theorem not_ge_half_of_eq_zero {k : ℕ} (i : Fin k) {z : IC (k + 1)}
    (h : z (Fin.castSucc i) = 0) : ¬(1 / 2 ≤ ((z (Fin.castSucc i) : unitInterval) : ℝ)) := by
  intro ht
  have h1 : ((z (Fin.castSucc i) : unitInterval) : ℝ) = 0 := by simp [h]
  rw [h1] at ht
  norm_num at ht

/-- If `z_{castSucc i}` is extreme and `t > 1/2` then it is `1`. -/
theorem extr_cs_of_gt {k : ℕ} (i : Fin k) {z : IC (k + 1)}
    (h : z (Fin.castSucc i) = 0 ∨ z (Fin.castSucc i) = 1)
    (ht : ¬(((z (Fin.castSucc i) : unitInterval) : ℝ) ≤ 1 / 2)) :
    z (Fin.castSucc i) = 1 := by
  rcases h with h | h
  · exact absurd (not_le.mp ht).le (not_ge_half_of_eq_zero i h)
  · exact h

/-- If `z_{castSucc i}` is extreme and `t ≤ 1/2` then it is `0`. -/
theorem extr_cs_of_le {k : ℕ} (i : Fin k) {z : IC (k + 1)}
    (h : z (Fin.castSucc i) = 0 ∨ z (Fin.castSucc i) = 1)
    (ht : ((z (Fin.castSucc i) : unitInterval) : ℝ) ≤ 1 / 2) :
    z (Fin.castSucc i) = 0 := by
  rcases h with h | h
  · exact h
  · exact absurd ht (not_le_half_of_eq_one i h)

/-- If the only possibly extreme coordinates of `z` are `castSucc i` and `last`, then (given that
`z` has two extreme coordinates) both of them are extreme. -/
theorem inSkel_pair {k : ℕ} (i : Fin k) {z : IC (k + 1)} (hz : Work.RatHurewicz.InSkel k z)
    (hno : ∀ r : Fin (k + 1), r ≠ Fin.castSucc i → r ≠ Fin.last k →
      ¬(z r = 0 ∨ z r = 1)) :
    (z (Fin.castSucc i) = 0 ∨ z (Fin.castSucc i) = 1) ∧
      (z (Fin.last k) = 0 ∨ z (Fin.last k) = 1) := by
  obtain ⟨p, q, hpq, hp, hq⟩ := hz
  have key : ∀ r : Fin (k + 1), r = Fin.castSucc i ∨ r = Fin.last k ∨ ¬(z r = 0 ∨ z r = 1) := by
    intro r
    by_cases h1 : r = Fin.castSucc i
    · exact Or.inl h1
    · by_cases h2 : r = Fin.last k
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (hno r h1 h2))
  have hp' := key p
  have hq' := key q
  constructor
  · rcases hp' with h | h | h
    · rw [← h]; exact hp
    · rcases hq' with h' | h' | h'
      · rw [← h']; exact hq
      · exact absurd (h.trans h'.symm) hpq
      · exact absurd hq h'
    · exact absurd hp h
  · rcases hp' with h | h | h
    · rcases hq' with h' | h' | h'
      · exact absurd (h.trans h'.symm) hpq
      · rw [← h']; exact hq
      · exact absurd hq h'
    · rw [← h]; exact hp
    · exact absurd hp h

theorem killCMPos_mem_InSkel {k : ℕ} (i : Fin k) {z : IC (k + 1)}
    (hz : Work.RatHurewicz.InSkel k z) : Work.RatHurewicz.InSkel k (killCMPos k i z) := by
  by_cases ht : ((z (Fin.castSucc i) : unitInterval) : ℝ) ≤ 1 / 2
  · -- left branch: every coordinate other than `castSucc i` is preserved
    have hpres : ∀ j : Fin (k + 1), j ≠ Fin.castSucc i → killCMPos k i z j = z j := by
      intro j hj
      by_cases hjl : j = Fin.last k
      · rw [hjl, killCMPos_apply_last, clamp_two_sub (z (Fin.castSucc i)) ht, mul_one]
      · rw [killCMPos_apply_of_ne k i hj hjl]
    have hE' : ∀ j : Fin (k + 1), (z j = 0 ∨ z j = 1) →
        (killCMPos k i z j = 0 ∨ killCMPos k i z j = 1) := by
      intro j hj
      by_cases hji : j = Fin.castSucc i
      · have h2 : z (Fin.castSucc i) = 0 ∨ z (Fin.castSucc i) = 1 := by rw [← hji]; exact hj
        have hzero : z (Fin.castSucc i) = 0 := extr_cs_of_le i h2 ht
        left
        rw [hji, killCMPos_apply_castSucc, hzero, clamp_two_zero]
      · rw [hpres j hji]; exact hj
    obtain ⟨p, q, hpq, hp, hq⟩ := hz
    exact ⟨p, q, hpq, hE' p hp, hE' q hq⟩
  · -- right branch: `castSucc i` becomes `1`
    have ht' : (1 : ℝ) / 2 < ((z (Fin.castSucc i) : unitInterval) : ℝ) := not_le.mp ht
    have hcs1 : killCMPos k i z (Fin.castSucc i) = 1 := by
      rw [killCMPos_apply_castSucc]
      exact clamp_eq_one_of_one_le (by linarith)
    by_cases hex : ∃ r : Fin (k + 1), r ≠ Fin.castSucc i ∧ r ≠ Fin.last k ∧
        (z r = 0 ∨ z r = 1)
    · obtain ⟨r, hr1, hr2, hr⟩ := hex
      exact ⟨Fin.castSucc i, r, (Ne.symm hr1), Or.inr hcs1, by
        rw [killCMPos_apply_of_ne k i hr1 hr2]; exact hr⟩
    · have hno : ∀ r : Fin (k + 1), r ≠ Fin.castSucc i → r ≠ Fin.last k →
          ¬(z r = 0 ∨ z r = 1) := fun r hr1 hr2 hr => hex ⟨r, hr1, hr2, hr⟩
      obtain ⟨hcsx, _⟩ := inSkel_pair i hz hno
      have hz1 : z (Fin.castSucc i) = 1 := extr_cs_of_gt i hcsx ht
      refine ⟨Fin.castSucc i, Fin.last k, Fin.castSucc_ne_last i, Or.inr hcs1, Or.inl ?_⟩
      rw [killCMPos_apply_last, hz1]
      rw [show (2 : ℝ) - 2 * ((1 : unitInterval) : ℝ) = 0 by norm_num,
        Work.Stems.Hur2.clamp_zero, mul_zero]

theorem killCMNeg_mem_InSkel {k : ℕ} (i : Fin k) {z : IC (k + 1)}
    (hz : Work.RatHurewicz.InSkel k z) : Work.RatHurewicz.InSkel k (killCMNeg k i z) := by
  by_cases ht : ((z (Fin.castSucc i) : unitInterval) : ℝ) ≤ 1 / 2
  · -- left branch: `castSucc i` becomes `0`
    have hcs0 : killCMNeg k i z (Fin.castSucc i) = 0 := by
      rw [killCMNeg_apply_castSucc]
      exact clamp_eq_zero_of_nonpos (by linarith)
    by_cases hex : ∃ r : Fin (k + 1), r ≠ Fin.castSucc i ∧ r ≠ Fin.last k ∧
        (z r = 0 ∨ z r = 1)
    · obtain ⟨r, hr1, hr2, hr⟩ := hex
      exact ⟨Fin.castSucc i, r, (Ne.symm hr1), Or.inl hcs0, by
        rw [killCMNeg_apply_of_ne k i hr1 hr2]; exact hr⟩
    · have hno : ∀ r : Fin (k + 1), r ≠ Fin.castSucc i → r ≠ Fin.last k →
          ¬(z r = 0 ∨ z r = 1) := fun r hr1 hr2 hr => hex ⟨r, hr1, hr2, hr⟩
      obtain ⟨hcsx, _⟩ := inSkel_pair i hz hno
      have hz0 : z (Fin.castSucc i) = 0 := extr_cs_of_le i hcsx ht
      refine ⟨Fin.castSucc i, Fin.last k, Fin.castSucc_ne_last i, Or.inl hcs0, Or.inl ?_⟩
      rw [killCMNeg_apply_last, hz0, clamp_two_zero, mul_zero]
  · -- right branch: `last` is unchanged, `castSucc i` becomes `clamp (2 t - 1)`
    have ht' : (1 : ℝ) / 2 < ((z (Fin.castSucc i) : unitInterval) : ℝ) := not_le.mp ht
    have hlastEq : killCMNeg k i z (Fin.last k) = z (Fin.last k) := by
      rw [killCMNeg_apply_last]
      rw [show Work.Stems.Hur2.clamp (2 * ((z (Fin.castSucc i) : unitInterval) : ℝ)) = 1 from
        clamp_eq_one_of_one_le (by linarith), mul_one]
    have hcs_of_one : z (Fin.castSucc i) = 1 →
        (killCMNeg k i z (Fin.castSucc i) = 0 ∨ killCMNeg k i z (Fin.castSucc i) = 1) := by
      intro h1
      right
      rw [killCMNeg_apply_castSucc, h1]
      rw [show (2 : ℝ) * ((1 : unitInterval) : ℝ) - 1 = 1 by norm_num,
        Work.Stems.Hur2.clamp_one]
    have hfree : ∀ r : Fin (k + 1), r ≠ Fin.castSucc i → r ≠ Fin.last k → (z r = 0 ∨ z r = 1) →
        (killCMNeg k i z r = 0 ∨ killCMNeg k i z r = 1) := by
      intro r hr1 hr2 hr
      rw [killCMNeg_apply_of_ne k i hr1 hr2]; exact hr
    by_cases hlastx : z (Fin.last k) = 0 ∨ z (Fin.last k) = 1
    · have hlast' : killCMNeg k i z (Fin.last k) = 0 ∨ killCMNeg k i z (Fin.last k) = 1 := by
        rw [hlastEq]; exact hlastx
      by_cases hex : ∃ r : Fin (k + 1), r ≠ Fin.castSucc i ∧ r ≠ Fin.last k ∧
          (z r = 0 ∨ z r = 1)
      · obtain ⟨r, hr1, hr2, hr⟩ := hex
        exact ⟨Fin.last k, r, (Ne.symm hr2), hlast', by
          rw [killCMNeg_apply_of_ne k i hr1 hr2]; exact hr⟩
      · have hno : ∀ r : Fin (k + 1), r ≠ Fin.castSucc i → r ≠ Fin.last k →
            ¬(z r = 0 ∨ z r = 1) := fun r hr1 hr2 hr => hex ⟨r, hr1, hr2, hr⟩
        obtain ⟨hcsx, _⟩ := inSkel_pair i hz hno
        have hz1 : z (Fin.castSucc i) = 1 := extr_cs_of_gt i hcsx ht
        exact ⟨Fin.last k, Fin.castSucc i, (Ne.symm (Fin.castSucc_ne_last i)), hlast',
          hcs_of_one hz1⟩
    · -- `last` is not extreme: the extreme coordinates are `castSucc i` or free
      obtain ⟨p, q, hpq, hp, hq⟩ := hz
      have hple : p ≠ Fin.last k := fun h => hlastx (by rw [← h]; exact hp)
      have hqle : q ≠ Fin.last k := fun h => hlastx (by rw [← h]; exact hq)
      rcases eq_or_ne p (Fin.castSucc i) with hp1 | hp1
      · have h2 : z (Fin.castSucc i) = 0 ∨ z (Fin.castSucc i) = 1 := by rw [← hp1]; exact hp
        refine ⟨Fin.castSucc i, q, (fun h => hpq (hp1.trans h)),
          hcs_of_one (extr_cs_of_gt i h2 ht), ?_⟩
        exact hfree q (fun h => hpq (hp1.trans h.symm)) hqle hq
      · rcases eq_or_ne q (Fin.castSucc i) with hq1 | hq1
        · have h2 : z (Fin.castSucc i) = 0 ∨ z (Fin.castSucc i) = 1 := by rw [← hq1]; exact hq
          exact ⟨p, Fin.castSucc i, hp1, hfree p hp1 hple hp,
            hcs_of_one (extr_cs_of_gt i h2 ht)⟩
        · exact ⟨p, q, hpq, hfree p hp1 hple hp, hfree q hq1 hqle hq⟩

/-! ## The killed cube is an `SkCube` -/

theorem SkCube.killPos {k : ℕ} (i : Fin k) {g : C(IC (k + 1), X)} (h : SkCube k x₀ g) :
    SkCube k x₀ (killPos k i g) := fun z hz => h _ (killCMPos_mem_InSkel i hz)

theorem SkCube.killNeg {k : ℕ} (i : Fin k) {g : C(IC (k + 1), X)} (h : SkCube k x₀ g) :
    SkCube k x₀ (killNeg k i g) := fun z hz => h _ (killCMNeg_mem_InSkel i hz)

/-! ## The killed faces are constant -/

/-- The cube `g` is `x₀` on the hyperplane `{z_{castSucc j} = cval b}`. -/
def killedAt {k : ℕ} (x₀ : X) (g : C(IC (k + 1), X)) (h : SkCube k x₀ g) (j : Fin k)
    (b : Fin 2) : Prop :=
  ∀ z : IC (k + 1), z (Fin.castSucc j) = cval b → g z = x₀

theorem killPos_killed {k : ℕ} (i : Fin k) (g : C(IC (k + 1), X)) (h : SkCube k x₀ g) :
    killedAt x₀ (killPos k i g) (SkCube.killPos i h) i 1 := by
  intro z hz
  show g (killCMPos k i z) = x₀
  refine h _ ⟨Fin.castSucc i, Fin.last k, Fin.castSucc_ne_last i, Or.inr ?_, Or.inl ?_⟩
  · rw [killCMPos_apply_castSucc, hz, cval_one, clamp_two_one]
  · rw [killCMPos_apply_last, hz, cval_one]
    rw [show (2 : ℝ) - 2 * ((1 : unitInterval) : ℝ) = 0 by norm_num,
      Work.Stems.Hur2.clamp_zero, mul_zero]

theorem killNeg_killed {k : ℕ} (i : Fin k) (g : C(IC (k + 1), X)) (h : SkCube k x₀ g) :
    killedAt x₀ (killNeg k i g) (SkCube.killNeg i h) i 0 := by
  intro z hz
  show g (killCMNeg k i z) = x₀
  refine h _ ⟨Fin.castSucc i, Fin.last k, Fin.castSucc_ne_last i, Or.inl ?_, Or.inl ?_⟩
  · rw [killCMNeg_apply_castSucc, hz, cval_zero, clamp_two_mul_zero_sub_one]
  · rw [killCMNeg_apply_last, hz, cval_zero, clamp_two_zero, mul_zero]

/-! ## The kills performed earlier are preserved -/

theorem killPos_preserves {k : ℕ} (i : Fin k) (g : C(IC (k + 1), X)) (h : SkCube k x₀ g)
    {j : Fin k} {b : Fin 2} (hne : ¬(j = i ∧ b = 1)) (H : killedAt x₀ g h j b) :
    killedAt x₀ (killPos k i g) (SkCube.killPos i h) j b := by
  intro z hz
  show g (killCMPos k i z) = x₀
  by_cases hji : j = i
  · have hb : b = 0 := by
      fin_cases b
      · rfl
      · exact absurd (⟨hji, rfl⟩ : j = i ∧ (1 : Fin 2) = 1) hne
    have hz' : z (Fin.castSucc i) = cval b := by rw [← hji]; exact hz
    refine H (killCMPos k i z) ?_
    rw [hji, killCMPos_apply_castSucc, hz', hb, cval_zero, clamp_two_zero]
  · refine H (killCMPos k i z) ?_
    rw [killCMPos_apply_of_ne k i (fun h' => hji (Fin.castSucc_injective k h'))
      (fun h' => Fin.castSucc_ne_last j h')]
    exact hz

theorem killNeg_preserves {k : ℕ} (i : Fin k) (g : C(IC (k + 1), X)) (h : SkCube k x₀ g)
    {j : Fin k} {b : Fin 2} (hne : ¬(j = i ∧ b = 0)) (H : killedAt x₀ g h j b) :
    killedAt x₀ (killNeg k i g) (SkCube.killNeg i h) j b := by
  intro z hz
  show g (killCMNeg k i z) = x₀
  by_cases hji : j = i
  · have hb : b = 1 := by
      fin_cases b
      · exact absurd (⟨hji, rfl⟩ : j = i ∧ (0 : Fin 2) = 0) hne
      · rfl
    have hz' : z (Fin.castSucc i) = cval b := by rw [← hji]; exact hz
    refine H (killCMNeg k i z) ?_
    rw [hji, killCMNeg_apply_castSucc, hz', hb, cval_one]
    rw [show (2 : ℝ) * ((1 : unitInterval) : ℝ) - 1 = 1 by norm_num,
      Work.Stems.Hur2.clamp_one]
  · refine H (killCMNeg k i z) ?_
    rw [killCMNeg_apply_of_ne k i (fun h' => hji (Fin.castSucc_injective k h'))
      (fun h' => Fin.castSucc_ne_last j h')]
    exact hz

end

end Work.RatHurewicz.GluingPinch
