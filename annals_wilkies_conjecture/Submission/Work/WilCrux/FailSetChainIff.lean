/-
  WilCrux — reductions of `fmChain` and `failSet` to their pointwise forms.
-/
import Mathlib
import Submission.Work.WilCrux.FailSetChainEq

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign

variable {a b : ℕ}

/-! ## Composition readings -/

theorem fm_comp_wpD (u : Fin (fmE a) → ℝ) (w : Fin (fmB a b) → ℝ) :
    (Work.WilG0.snocIt (fmE a) (fmB a b) u w) ∘ fmwpD a b = w ∘ fmwpB a b := by
  funext i; simp only [Function.comp_apply, fm_read_wpD]

theorem fm_comp_zD (u : Fin (fmE a) → ℝ) (w : Fin (fmB a b) → ℝ) :
    (Work.WilG0.snocIt (fmE a) (fmB a b) u w) ∘ fmzD a b = w ∘ fmzB a b := by
  funext j; simp only [Function.comp_apply, fm_read_zD]

theorem fm_comp_zpD (u : Fin (fmE a) → ℝ) (w : Fin (fmB a b) → ℝ) :
    (Work.WilG0.snocIt (fmE a) (fmB a b) u w) ∘ fmzpD a b = w ∘ fmzpB a b := by
  funext j; simp only [Function.comp_apply, fm_read_zpD]

/-! ## The values of `![y,y']` -/

theorem fm_vec2_zero (y y' : ℝ) : (![y, y'] : Fin 2 → ℝ) 0 = y := by simp
theorem fm_vec2_one (y y' : ℝ) : (![y, y'] : Fin 2 → ℝ) 1 = y' := by simp

/-! ## `fmChain` unwound -/

theorem fmChain_iff (T : Set (Fin ((a + b) + 1) → ℝ)) (X : Fin (a + 1) → ℝ) :
    X ∈ fmChain a b T ↔ 0 < X (Fin.last a) ∧ ∀ η : ℝ, 0 < η →
      ∃ w : Fin (fmB a b) → ℝ,
        Work.WilG0.snocIt (fmE a) (fmB a b) (fmsnoc a X η) w ∈ fmHyp a b ∧
        ∀ y y' : ℝ, Work.WilG0.snocIt (fmD a b) 2
          (Work.WilG0.snocIt (fmE a) (fmB a b) (fmsnoc a X η) w) ![y, y'] ∉ fmK a b T := by
  simp only [fmChain, fmPosEps, fmBset, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Set.mem_compl_iff, WilkiesDesign.projLast, not_exists]
  constructor
  · rintro ⟨hε, hnot⟩
    refine ⟨hε, fun η hη => ?_⟩
    have h2 : fmsnoc a X η ∈ fmA2 a b T := by
      by_contra hc
      refine hnot η ?_
      refine ⟨hc, ?_⟩
      show 0 < fmsnoc a X η (Fin.last (a + 1))
      rw [fmsnoc_last]; exact hη
    rw [fmA2, Work.WilG0.projLastIter_eq] at h2
    obtain ⟨w, hw⟩ := h2
    refine ⟨w, hw.2, fun y y' hyy => hw.1 ?_⟩
    rw [fmK1, projLastIter_two_eq]
    exact ⟨y, y', hyy⟩
  · rintro ⟨hε, h⟩
    refine ⟨hε, fun t => ?_⟩
    intro hmem
    have hpos : 0 < fmsnoc a X t (Fin.last (a + 1)) := hmem.2
    rw [fmsnoc_last] at hpos
    obtain ⟨w, hhyp, hK⟩ := h t hpos
    have hA2 : fmsnoc a X t ∈ fmA2 a b T := by
      rw [fmA2, Work.WilG0.projLastIter_eq]
      refine ⟨w, ?_, hhyp⟩
      intro hK1
      rw [fmK1, projLastIter_two_eq] at hK1
      obtain ⟨y, y', hyy⟩ := hK1
      exact hK y y' hyy
    exact hmem.1 hA2

/-! ## `fmK` unwound -/

theorem fmK_read (T : Set (Fin ((a + b) + 1) → ℝ)) (v : Fin (fmD a b) → ℝ) (y y' : ℝ) :
    Work.WilG0.snocIt (fmD a b) 2 v ![y, y'] ∈ fmK a b T ↔
      (Fin.snoc (Fin.append (v ∘ fmwpD a b) (v ∘ fmzD a b)) y ∈ T ∧
       Fin.snoc (Fin.append (v ∘ fmwpD a b) (v ∘ fmzpD a b)) y' ∈ T ∧
       |y - y'| < v (fmepsD a b)) := by
  simp only [fmK, fmAbsLt, Work.WilG5.coordPre, Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [fm_comp_e1, fm_comp_e2, fm_read_yN, fm_read_ypN, fm_read_epsN, fm_vec2_zero, fm_vec2_one]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h1, h2, by rw [abs_lt]; exact ⟨by linarith, by linarith⟩⟩
  · rintro ⟨h1, h2, h3⟩
    rw [abs_lt] at h3
    exact ⟨⟨h1, h2⟩, by linarith [h3.2], by linarith [h3.1]⟩

/-! ## The graph reduction -/

theorem fmK_fail_iff (f : (Fin (a + b) → ℝ) → ℝ) (i : Fin (a + b)) (v : Fin (fmD a b) → ℝ) :
    (∀ y y' : ℝ, Work.WilG0.snocIt (fmD a b) 2 v ![y, y'] ∉
        fmK a b (Work.WilG4b.derivGraph f i)) ↔
      ¬(Fin.append (v ∘ fmwpD a b) (v ∘ fmzD a b) ∈ Work.WilG4b.c1Loc f ∧
        Fin.append (v ∘ fmwpD a b) (v ∘ fmzpD a b) ∈ Work.WilG4b.c1Loc f ∧
        |Work.WilG4b.dDir f i (Fin.append (v ∘ fmwpD a b) (v ∘ fmzD a b)) -
         Work.WilG4b.dDir f i (Fin.append (v ∘ fmwpD a b) (v ∘ fmzpD a b))| <
          v (fmepsD a b)) := by
  have key : (∃ y y' : ℝ, Work.WilG0.snocIt (fmD a b) 2 v ![y, y'] ∈
      fmK a b (Work.WilG4b.derivGraph f i)) ↔
      (Fin.append (v ∘ fmwpD a b) (v ∘ fmzD a b) ∈ Work.WilG4b.c1Loc f ∧
        Fin.append (v ∘ fmwpD a b) (v ∘ fmzpD a b) ∈ Work.WilG4b.c1Loc f ∧
        |Work.WilG4b.dDir f i (Fin.append (v ∘ fmwpD a b) (v ∘ fmzD a b)) -
         Work.WilG4b.dDir f i (Fin.append (v ∘ fmwpD a b) (v ∘ fmzpD a b))| <
          v (fmepsD a b)) := by
    constructor
    · rintro ⟨y, y', hmem⟩
      rw [fmK_read] at hmem
      obtain ⟨hg1, hg2, hlt⟩ := hmem
      rw [Work.WilG4b.derivGraph, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at hg1 hg2
      refine ⟨hg1.1, hg2.1, ?_⟩
      rw [← hg1.2, ← hg2.2]; exact hlt
    · rintro ⟨hc1, hc2, hlt⟩
      refine ⟨Work.WilG4b.dDir f i (Fin.append (v ∘ fmwpD a b) (v ∘ fmzD a b)),
        Work.WilG4b.dDir f i (Fin.append (v ∘ fmwpD a b) (v ∘ fmzpD a b)), ?_⟩
      rw [fmK_read]
      refine ⟨?_, ?_, hlt⟩
      · rw [Work.WilG4b.derivGraph, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
        exact ⟨hc1, rfl⟩
      · rw [Work.WilG4b.derivGraph, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
        exact ⟨hc2, rfl⟩
  constructor
  · intro h hc
    obtain ⟨y, y', hyy⟩ := key.mpr hc
    exact h y y' hyy
  · intro h y y' hyy
    exact h (key.mp ⟨y, y', hyy⟩)

/-! ## Uncurrying `Fin (fmB a b) → ℝ` -/

theorem fm_curry_wpB (w' : Fin a → ℝ) (z z' : Fin b → ℝ) :
    (Fin.append (Fin.append w' z) z') ∘ fmwpB a b = w' := by
  funext i; simp only [Function.comp_apply, fmwpB, Fin.append_left]

theorem fm_curry_zB (w' : Fin a → ℝ) (z z' : Fin b → ℝ) :
    (Fin.append (Fin.append w' z) z') ∘ fmzB a b = z := by
  funext j; simp only [Function.comp_apply, fmzB, Fin.append_left, Fin.append_right]

theorem fm_curry_zpB (w' : Fin a → ℝ) (z z' : Fin b → ℝ) :
    (Fin.append (Fin.append w' z) z') ∘ fmzpB a b = z' := by
  funext j; simp only [Function.comp_apply, fmzpB, Fin.append_right]

theorem fm_exists_curry (P : (Fin a → ℝ) → (Fin b → ℝ) → (Fin b → ℝ) → Prop) :
    (∃ w : Fin (fmB a b) → ℝ, P (w ∘ fmwpB a b) (w ∘ fmzB a b) (w ∘ fmzpB a b)) ↔
      (∃ w' : Fin a → ℝ, ∃ z : Fin b → ℝ, ∃ z' : Fin b → ℝ, P w' z z') := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w ∘ fmwpB a b, w ∘ fmzB a b, w ∘ fmzpB a b, hw⟩
  · rintro ⟨w', z, z', hw⟩
    refine ⟨Fin.append (Fin.append w' z) z', ?_⟩
    have h1 : (Fin.append (Fin.append w' z) z') ∘ fmwpB a b = w' := by
      funext i; simp only [Function.comp_apply, fmwpB, Fin.append_left]
    have h2 : (Fin.append (Fin.append w' z) z') ∘ fmzB a b = z := by
      funext j; simp only [Function.comp_apply, fmzB, Fin.append_left, Fin.append_right]
    have h3 : (Fin.append (Fin.append w' z) z') ∘ fmzpB a b = z' := by
      funext j; simp only [Function.comp_apply, fmzpB, Fin.append_right]
    rw [h1, h2, h3]; exact hw

/-! ## Metric readings -/

theorem fm_dist_iff {n : ℕ} (u v : Fin n → ℝ) (η : ℝ) (hη : 0 < η) :
    dist u v < η ↔ ∀ i, |u i - v i| < η := by
  rw [dist_eq_norm, pi_norm_lt_iff hη]
  simp [Pi.sub_apply, Real.norm_eq_abs]

theorem fm_norm_iff {n : ℕ} (z : Fin n → ℝ) (η : ℝ) (hη : 0 < η) :
    ‖z‖ < η ↔ ∀ i, |z i| < η := by
  rw [pi_norm_lt_iff hη]
  simp [Real.norm_eq_abs]

theorem fm_ne_zero_iff {n : ℕ} (z : Fin n → ℝ) : z ≠ 0 ↔ ∃ i, z i ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    rw [not_exists] at hc
    exact h (funext fun i => by by_contra hh; exact hc i hh)
  · rintro ⟨i, hi⟩ hz
    exact hi (by simp [hz])

/-! ## `failSet` unwound -/

theorem failSet_iff (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (j : Fin b) (X : Fin (a + 1) → ℝ) :
    Fin.init X ∈ failSet G j (X (Fin.last a)) ↔
      ∀ η : ℝ, 0 < η → ∃ w' : Fin a → ℝ, ∃ z : Fin b → ℝ, ∃ z' : Fin b → ℝ,
        dist w' (Fin.init X) < η ∧ z ≠ 0 ∧ ‖z‖ < η ∧ z' ≠ 0 ∧ ‖z'‖ < η ∧
        ¬(Fin.append w' z ∈ Work.WilG4b.c1Loc (Work.WilG4c.famFun G) ∧
          Fin.append w' z' ∈ Work.WilG4b.c1Loc (Work.WilG4c.famFun G) ∧
          |Work.WilG4b.dDir (Work.WilG4c.famFun G) (Fin.natAdd a j) (Fin.append w' z) -
           Work.WilG4b.dDir (Work.WilG4c.famFun G) (Fin.natAdd a j) (Fin.append w' z')| <
            X (Fin.last a)) := by
  rw [failSet, Set.mem_compl_iff, goodSet, Set.mem_ofPred_eq]
  constructor
  · intro h η hη
    by_contra hc
    apply h
    refine ⟨η, hη, fun w' z z' h1 h2 h3 h4 h5 => ?_⟩
    by_contra hcon
    exact hc ⟨w', z, z', h1, h2, h3, h4, h5, hcon⟩
  · rintro h ⟨η, hη, hgood⟩
    obtain ⟨w', z, z', h1, h2, h3, h4, h5, hcon⟩ := h η hη
    exact hcon (hgood w' z z' h1 h2 h3 h4 h5)

end Work.WilCrux
