import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.seed_mem_polyRegion
import Submission.Work.ELTop.notInArc_midNear

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

open Work.EL

/-! ## Pure real facts about the cyclic arc `InArc` -/

/-- `InArc` only depends on the angle of the point modulo `1`. -/
private theorem InArc_add_intCast (θ a b : ℝ) (n : ℤ) :
    Work.EL.InArc (θ + (n : ℝ)) a b ↔ Work.EL.InArc θ a b := by
  unfold Work.EL.InArc Work.EL.arcLen
  have h1 : Int.fract ((θ + (n : ℝ)) - a) = Int.fract (θ - a) := by
    have h : (θ + (n : ℝ)) - a = (θ - a) + (n : ℝ) := by ring
    rw [h, Int.fract_add_intCast]
  rw [h1]

/-- A point just *beyond* the closed arc `[a, b]` (with `a < b < a + 1`) is not in the open
arc `(a, b)`. -/
private theorem notInArc_of_between_right {a b y : ℝ} (hab : a < b) (hyb : b < y) (hya : y < a + 1) :
    ¬ Work.EL.InArc y a b := by
  have hlen : Work.EL.arcLen a b = b - a :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hfy : Int.fract (y - a) = y - a :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  intro h
  have := h.2
  rw [hlen, hfy] at this
  linarith

/-- A point just *before* the closed arc `[a, b]` (with `a < b < a + 1`) is not in the open
arc `(a, b)`. -/
private theorem notInArc_of_between_left {a b y : ℝ} (hab : a < b) (hya : y < a)
    (hyb : b - 1 < y) : ¬ Work.EL.InArc y a b := by
  have hlen : Work.EL.arcLen a b = b - a :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hfy : Int.fract (y - a) = y - a + 1 := by
    rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
  intro h
  have := h.2
  rw [hlen, hfy] at this
  linarith

/-- A real number in the open unit interval `(a, a+1)` is not congruent to `a` modulo `ℤ`. -/
private theorem ne_add_int_of_mem_unit {a y : ℝ} (h1 : a < y) (h2 : y < a + 1) (j : ℤ) :
    y ≠ a + (j : ℝ) := by
  intro h
  have hj : (j : ℝ) = y - a := by linarith
  have h0 : (0 : ℝ) < (j : ℝ) := by rw [hj]; linarith
  have h0' : (0 : ℤ) < j := by exact_mod_cast h0
  have h1' : (j : ℝ) < 1 := by rw [hj]; linarith
  have h1'' : j < (1 : ℤ) := by exact_mod_cast h1'
  omega

/-- A real number in `(a - 1, a)` is not congruent to `a` modulo `ℤ`. -/
private theorem ne_add_int_of_neg_unit {a y : ℝ} (h1 : y < a) (h2 : a - 1 < y) (j : ℤ) :
    y ≠ a + (j : ℝ) := by
  intro h
  have hj : (j : ℝ) = y - a := by linarith
  have h0 : (-1 : ℝ) < (j : ℝ) := by rw [hj]; linarith
  have h0' : (-1 : ℤ) < j := by exact_mod_cast h0
  have h1' : (j : ℝ) < 0 := by rw [hj]; linarith
  have h1'' : j < (0 : ℤ) := by exact_mod_cast h1'
  omega

/-- Integer translations preserve non-congruence. -/
private theorem ne_add_int_shift {y X : ℝ} (h : ∀ j : ℤ, y ≠ X + (j : ℝ)) (k j : ℤ) :
    y + (k : ℝ) ≠ X + (j : ℝ) := by
  intro hc
  refine h (j - k) ?_
  have hcast : ((j - k : ℤ) : ℝ) = (j : ℝ) - (k : ℝ) := by push_cast; ring
  rw [hcast]
  linarith

/-! ## The neighbourhood statement -/

theorem midNear_nearArc_nbhd {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : ℝ, (∃ k : ℤ, |x - (Work.EL.midNear ps + k)| < η) →
      (∀ P ∈ ps, ¬ Work.EL.InArc x P.a P.b) ∧
      (∀ P ∈ ps, ∀ k : ℤ, x ≠ P.a + k ∧ x ≠ P.b + k) := by
  obtain ⟨P₀, rest, rfl⟩ := List.exists_cons_of_ne_nil hA.ne
  have hpair : (P₀.a :: P₀.b :: rest.flatMap (fun P => [P.a, P.b])).Pairwise (· < ·) := by
    have := hA.cyc.2.1
    simpa [List.flatMap_cons] using this
  have hupper : ∀ x ∈ (P₀ :: rest).flatMap (fun P => [P.a, P.b]), x < P₀.a + 1 := by
    intro x hx
    have := hA.cyc.2.2 x hx
    have hhead : ((P₀ :: rest).flatMap (fun P => [P.a, P.b])).headD 0 = P₀.a := by
      simp [List.flatMap_cons]
    rwa [hhead] at this
  have hab : ∀ P ∈ P₀ :: rest, P.a < P.b :=
    midNear_a_lt_b_of_pairwise (P₀ :: rest) (fun P => P.a) (fun P => P.b) hA.cyc.2.1
  have hP0ab : P₀.a < P₀.b := hab P₀ (by simp)
  have hPb_bd : ∀ P ∈ P₀ :: rest, P.b < P₀.a + 1 :=
    fun P hP => hupper P.b (List.mem_flatMap.mpr ⟨P, hP, by simp⟩)
  cases rest with
  | nil =>
    have hb1 : P₀.b < P₀.a + 1 := hPb_bd P₀ (by simp)
    have hfract : Int.fract (P₀.a + 1 - P₀.b) = P₀.a + 1 - P₀.b :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hmval : Work.EL.midNear [P₀] = (P₀.a + P₀.b + 1) / 2 := by
      rw [Work.EL.midNear.eq_2, hfract]; ring
    refine ⟨(P₀.a + 1 - P₀.b) / 2, by linarith, ?_⟩
    rintro x ⟨k, hk⟩
    let y : ℝ := Work.EL.midNear [P₀] + (x - (Work.EL.midNear [P₀] + (k : ℝ)))
    have hy_abs : |y - Work.EL.midNear [P₀]| < (P₀.a + 1 - P₀.b) / 2 := by
      have h1 : y - Work.EL.midNear [P₀] = x - (Work.EL.midNear [P₀] + (k : ℝ)) := by
        dsimp only [y]; ring
      rw [h1]; exact hk
    have hy_gt : P₀.b < y := by
      have := (abs_lt.mp hy_abs).1; rw [hmval] at this; linarith
    have hy_lt : y < P₀.a + 1 := by
      have := (abs_lt.mp hy_abs).2; rw [hmval] at this; linarith
    have hx_eq' : x = y + (k : ℝ) := by dsimp only [y]; ring
    have hyarc : ¬ Work.EL.InArc y P₀.a P₀.b := notInArc_of_between_right hP0ab hy_gt hy_lt
    have hyA : ∀ j : ℤ, y ≠ P₀.a + (j : ℝ) :=
      fun j => ne_add_int_of_mem_unit (by linarith) hy_lt j
    have hyB : ∀ j : ℤ, y ≠ P₀.b + (j : ℝ) :=
      fun j => ne_add_int_of_mem_unit hy_gt (by linarith) j
    constructor
    · intro P hP
      have hPP0 : P = P₀ := by simpa using hP
      rw [hPP0, hx_eq']
      exact fun h => hyarc ((InArc_add_intCast y P₀.a P₀.b k).mp h)
    · intro P hP j
      have hPP0 : P = P₀ := by simpa using hP
      rw [hPP0, hx_eq']
      exact ⟨ne_add_int_shift hyA k j, ne_add_int_shift hyB k j⟩
  | cons Q tl =>
    have hpairQ : ((Q :: tl).flatMap (fun P => [P.a, P.b])).Pairwise (· < ·) :=
      (List.pairwise_cons.mp (List.pairwise_cons.mp hpair).2).2
    have hheadQ : ((Q :: tl).flatMap (fun P => [P.a, P.b])).headD 0 = Q.a := by
      simp [List.flatMap_cons]
    have hP0b_lt_Qa : P₀.b < Q.a :=
      (List.pairwise_cons.mp (List.pairwise_cons.mp hpair).2).1 Q.a (by simp)
    have hQa_bd : Q.a < P₀.a + 1 :=
      hupper Q.a (List.mem_flatMap.mpr ⟨Q, by simp, by simp⟩)
    have hfract : Int.fract (Q.a - P₀.b) = Q.a - P₀.b :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hmval : Work.EL.midNear (P₀ :: Q :: tl) = (P₀.b + Q.a) / 2 := by
      rw [Work.EL.midNear.eq_1, hfract]; ring
    refine ⟨(Q.a - P₀.b) / 2, by linarith, ?_⟩
    rintro x ⟨k, hk⟩
    let y : ℝ := Work.EL.midNear (P₀ :: Q :: tl) + (x - (Work.EL.midNear (P₀ :: Q :: tl) + (k : ℝ)))
    have hy_abs : |y - Work.EL.midNear (P₀ :: Q :: tl)| < (Q.a - P₀.b) / 2 := by
      have h1 : y - Work.EL.midNear (P₀ :: Q :: tl) = x - (Work.EL.midNear (P₀ :: Q :: tl) + (k : ℝ)) := by
        dsimp only [y]; ring
      rw [h1]; exact hk
    have hy_gt : P₀.b < y := by
      have := (abs_lt.mp hy_abs).1; rw [hmval] at this; linarith
    have hy_lt : y < Q.a := by
      have := (abs_lt.mp hy_abs).2; rw [hmval] at this; linarith
    have hx_eq' : x = y + (k : ℝ) := by dsimp only [y]; ring
    have hgood_y : (∀ P ∈ P₀ :: Q :: tl, ¬ Work.EL.InArc y P.a P.b) ∧
        (∀ P ∈ P₀ :: Q :: tl, ∀ j : ℤ, y ≠ P.a + (j : ℝ) ∧ y ≠ P.b + (j : ℝ)) := by
      constructor
      · intro P hP
        rcases List.mem_cons.mp hP with rfl | hP'
        · exact notInArc_of_between_right hP0ab hy_gt (by linarith)
        · have hPmem : P ∈ Q :: tl := hP'
          have hPa_bd : P.a < P₀.a + 1 :=
            hupper P.a (List.mem_flatMap.mpr ⟨P, List.mem_cons_of_mem P₀ hPmem, by simp⟩)
          have hQle : Q.a ≤ P.a := by
            have := headD_le_of_pairwise_lt (x := P.a) hpairQ (List.mem_flatMap.mpr ⟨P, hPmem, by simp⟩)
            rwa [hheadQ] at this
          exact notInArc_of_between_left (hab P (List.mem_cons_of_mem P₀ hPmem))
            (by linarith) (by linarith [hPb_bd P (List.mem_cons_of_mem P₀ hPmem), hP0ab, hy_gt])
      · intro P hP j
        rcases List.mem_cons.mp hP with rfl | hP'
        · exact ⟨ne_add_int_of_mem_unit (by linarith) (by linarith [hy_lt, hQa_bd]) j,
                 ne_add_int_of_mem_unit hy_gt (by linarith [hy_lt, hQa_bd, hP0ab]) j⟩
        · have hPmem : P ∈ Q :: tl := hP'
          have hPa_bd : P.a < P₀.a + 1 :=
            hupper P.a (List.mem_flatMap.mpr ⟨P, List.mem_cons_of_mem P₀ hPmem, by simp⟩)
          have hQle : Q.a ≤ P.a := by
            have := headD_le_of_pairwise_lt (x := P.a) hpairQ (List.mem_flatMap.mpr ⟨P, hPmem, by simp⟩)
            rwa [hheadQ] at this
          have hPab : P.a < P.b := hab P (List.mem_cons_of_mem P₀ hPmem)
          have hPb_bd' : P.b < P₀.a + 1 := hPb_bd P (List.mem_cons_of_mem P₀ hPmem)
          exact ⟨ne_add_int_of_neg_unit (by linarith) (by linarith [hPa_bd, hP0ab, hy_gt]) j,
                 ne_add_int_of_neg_unit (by linarith) (by linarith [hPb_bd', hP0ab, hy_gt]) j⟩
    constructor
    · intro P hP
      rw [hx_eq']
      exact fun h => hgood_y.1 P hP ((InArc_add_intCast y P.a P.b k).mp h)
    · intro P hP j
      rw [hx_eq']
      exact ⟨ne_add_int_shift (fun j => (hgood_y.2 P hP j).1) k j,
             ne_add_int_shift (fun j => (hgood_y.2 P hP j).2) k j⟩

end Work.ELTop
