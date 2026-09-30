import Mathlib
import Submission.Work.RatHurewicz.Triad.Construct

/-!
# The stage induction of the preparation theorem

This file contains the two technical tools of the induction: the `Fintype` instance on the grid
cells, and the concatenation of homotopies.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Triad

open Work.ThomBordism.TwoSet

noncomputable section

variable {X : Type} [TopologicalSpace X] {B C : Set X} {x₀ : ↥(B ∩ C)} {n p q : ℕ}

section Fintype

/-- The grid has finitely many cells. -/
instance instFintypeCellIdx (j N : ℕ) : Fintype (CellIdx j N) := by
  classical
  refine Fintype.ofInjective
    (fun c : CellIdx j N =>
      (fun i => (⟨c.lo i, by have h1 := c.hle i; have h2 := c.hhi i; omega⟩ : Fin (N + 1)),
       fun i => (⟨c.hi i, by have h2 := c.hhi i; omega⟩ : Fin (N + 1)))) ?_
  intro a b h
  have h1 : a.lo = b.lo := funext fun i =>
    congrArg Fin.val (congrFun (congrArg Prod.fst h) i)
  have h2 : a.hi = b.hi := funext fun i =>
    congrArg Fin.val (congrFun (congrArg Prod.snd h) i)
  obtain ⟨alo, ahi, ahle, ahstep, ahhi⟩ := a
  obtain ⟨blo, bhi, bhle, bhstep, bhhi⟩ := b
  simp only at h1 h2
  obtain rfl : alo = blo := h1
  obtain rfl : ahi = bhi := h2
  rfl

end Fintype

section Concat

/-- The map at time `s` of a homotopy. -/
def sliceOf {A : Type} [TopologicalSpace A] {Y : Type} [TopologicalSpace Y]
    (Θ : C(A × I, Y)) (s : I) : C(A, Y) :=
  ⟨fun x => Θ (x, s), Θ.continuous.comp (continuous_id.prodMk continuous_const)⟩

@[simp] theorem sliceOf_apply {A : Type} [TopologicalSpace A] {Y : Type} [TopologicalSpace Y]
    (Θ : C(A × I, Y)) (s : I) (x : A) : sliceOf Θ s x = Θ (x, s) := rfl

/-- The first reparametrisation of the concatenation, `t ↦ min 1 (2t)`. -/
def phiOne (t : I) : I :=
  ⟨min 1 (2 * (t : ℝ)),
    ⟨le_min (by norm_num) (by have := t.2.1; linarith), min_le_left _ _⟩⟩

/-- The second reparametrisation of the concatenation, `t ↦ min 1 (max 0 (2t-1))`. -/
def phiTwo (t : I) : I :=
  ⟨min 1 (max 0 (2 * (t : ℝ) - 1)),
    ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩⟩

@[simp] theorem phiOne_val (t : I) : ((phiOne t : I) : ℝ) = min 1 (2 * (t : ℝ)) := rfl
@[simp] theorem phiTwo_val (t : I) : ((phiTwo t : I) : ℝ) = min 1 (max 0 (2 * (t : ℝ) - 1)) :=
  rfl

theorem continuous_phiOne : Continuous phiOne :=
  Continuous.subtype_mk (continuous_const.min (continuous_const.mul continuous_subtype_val)) _

theorem continuous_phiTwo : Continuous phiTwo :=
  Continuous.subtype_mk (continuous_const.min (continuous_const.max
    ((continuous_const.mul continuous_subtype_val).sub continuous_const))) _

theorem phiOne_zero : phiOne 0 = 0 := by
  apply Subtype.ext
  simp [phiOne_val]

theorem phiTwo_one : phiTwo 1 = 1 := by
  apply Subtype.ext
  simp only [phiTwo_val, Set.Icc.coe_one]
  norm_num


/-- **Concatenation of homotopies.** -/
theorem homotopyConcat {A : Type} [TopologicalSpace A] {Y : Type} [TopologicalSpace Y]
    {G₁ G₂ : C(A × I, Y)} (h : ∀ x, G₁ (x, 1) = G₂ (x, 0)) :
    ∃ G : C(A × I, Y), (∀ x, G (x, 0) = G₁ (x, 0)) ∧ (∀ x, G (x, 1) = G₂ (x, 1)) ∧
      (∀ s : I, (s : ℝ) ≤ 1 / 2 → ∀ x, G (x, s) = G₁ (x, phiOne s)) ∧
      (∀ s : I, 1 / 2 ≤ (s : ℝ) → ∀ x, G (x, s) = G₂ (x, phiTwo s)) := by
  classical
  have hcont : Continuous fun p : A × I =>
      if (p.2 : ℝ) ≤ 1 / 2 then G₁ (p.1, phiOne p.2) else G₂ (p.1, phiTwo p.2) := by
    refine Continuous.if_le ?_ ?_ (continuous_subtype_val.comp continuous_snd) continuous_const ?_
    · exact G₁.continuous.comp
        (Continuous.prodMk continuous_fst (continuous_phiOne.comp continuous_snd))
    · exact G₂.continuous.comp
        (Continuous.prodMk continuous_fst (continuous_phiTwo.comp continuous_snd))
    · intro p hp
      have h1 : phiOne p.2 = 1 := by
        apply Subtype.ext
        simp only [phiOne_val, Set.Icc.coe_one]
        have h5 : 2 * (p.2 : ℝ) = 1 := by linarith
        rw [h5, min_self]
      have h2 : phiTwo p.2 = 0 := by
        apply Subtype.ext
        simp only [phiTwo_val, Set.Icc.coe_zero]
        have h4 : 2 * (p.2 : ℝ) - 1 ≤ 0 := by linarith
        rw [max_eq_left h4, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
      show G₁ (p.1, phiOne p.2) = G₂ (p.1, phiTwo p.2)
      rw [h1, h2]
      exact h p.1
  refine ⟨⟨fun p => if (p.2 : ℝ) ≤ 1 / 2 then G₁ (p.1, phiOne p.2)
      else G₂ (p.1, phiTwo p.2), hcont⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    show (if (((0 : I)) : ℝ) ≤ 1 / 2 then G₁ (x, phiOne 0) else G₂ (x, phiTwo 0)) = G₁ (x, 0)
    rw [if_pos (by norm_num), phiOne_zero]
  · intro x
    show (if (((1 : I)) : ℝ) ≤ 1 / 2 then G₁ (x, phiOne 1) else G₂ (x, phiTwo 1)) = G₂ (x, 1)
    rw [if_neg (by norm_num), phiTwo_one]
  · intro s hs x
    show (if (s : ℝ) ≤ 1 / 2 then G₁ (x, phiOne s) else G₂ (x, phiTwo s)) = G₁ (x, phiOne s)
    rw [if_pos hs]
  · intro s hs x
    by_cases hc : (s : ℝ) ≤ 1 / 2
    · have hs1 : (s : ℝ) = 1 / 2 := le_antisymm hc hs
      show (if (s : ℝ) ≤ 1 / 2 then G₁ (x, phiOne s) else G₂ (x, phiTwo s)) = G₂ (x, phiTwo s)
      rw [if_pos hc]
      have hp1 : phiOne s = 1 := by
        apply Subtype.ext
        simp only [phiOne_val, Set.Icc.coe_one]
        have h5 : 2 * (s : ℝ) = 1 := by linarith
        rw [h5, min_self]
      have hp2 : phiTwo s = 0 := by
        apply Subtype.ext
        simp only [phiTwo_val, Set.Icc.coe_zero]
        have h5 : 2 * (s : ℝ) - 1 = 0 := by linarith
        rw [h5, max_self, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
      rw [hp1, hp2]
      exact h x
    · show (if (s : ℝ) ≤ 1 / 2 then G₁ (x, phiOne s) else G₂ (x, phiTwo s)) = G₂ (x, phiTwo s)
      rw [if_neg hc]

end Concat


end

end Work.RatHurewicz.Triad
