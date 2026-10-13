import Mathlib
import Submission.Work.WilG4c.AlBadParDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-- Cell case analysis keeping the base cell. -/
theorem isCell_cases' {m : ℕ} {κ : Set (Fin (m + 1) → ℝ)} (h : IsCell (m + 1) κ) :
    (∃ (τ : Set (Fin m → ℝ)) (_hτ : IsCell m τ) (f : (Fin m → ℝ) → ℝ), ContinuousOn f τ ∧
      ∀ z : Fin (m + 1) → ℝ, (z ∈ κ ↔ Fin.init z ∈ τ ∧ z (Fin.last m) = f (Fin.init z))) ∨
    (∃ (τ : Set (Fin m → ℝ)) (_hτ : IsCell m τ) (a b : (Fin m → ℝ) → EReal),
      ContinuousOn a τ ∧ ContinuousOn b τ ∧ (∀ x ∈ τ, a x < b x) ∧
      ∀ z : Fin (m + 1) → ℝ, (z ∈ κ ↔ Fin.init z ∈ τ ∧
        a (Fin.init z) < ((z (Fin.last m) : ℝ) : EReal) ∧
        ((z (Fin.last m) : ℝ) : EReal) < b (Fin.init z))) := by
  cases h with
  | graph hC f hf => exact Or.inl ⟨_, hC, f, hf, fun z => Iff.rfl⟩
  | band hC a b ha hb hab => exact Or.inr ⟨_, hC, a, b, ha, hb, hab, fun z => Iff.rfl⟩

/-- **Backup proof of the cell-fibre lemma**: the fibre of a cylindrical cell over the first `p`
coordinates is empty or a cell. -/
theorem fibSet_isCellOrEmpty_aux (p : ℕ) :
    ∀ (k : ℕ) (κ : Set (Fin (p + k) → ℝ)) (l : Fin p → ℝ),
      IsCell (p + k) κ → IsCellOrEmpty k (fibSet p k κ l) := by
  intro k
  induction k with
  | zero =>
    intro κ l _
    rcases Set.eq_empty_or_nonempty (fibSet p 0 κ l) with h | ⟨y, hy⟩
    · exact Or.inl h
    · refine Or.inr ?_
      have huniv : fibSet p 0 κ l = Set.univ := by
        rw [Set.eq_univ_iff_forall]
        intro w
        have hwy : w = y := funext (fun i => i.elim0)
        rw [hwy]; exact hy
      rw [huniv]
      exact IsCell.zero
  | succ k ih =>
    intro κ l hκ
    rcases isCell_cases' hκ with ⟨C, hC, f, hf, hiff⟩ | ⟨C, hC, a, b, ha, hb, hab, hiff⟩
    · rcases ih C l hC with hemp | hcell
      · refine Or.inl ?_
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨y, hy⟩
        have h1 : Fin.init y ∈ fibSet p k C l := by
          show apPt p k l (Fin.init y) ∈ C
          have h2 : Fin.init (apPt p (k + 1) l y) ∈ C :=
            ((hiff (apPt p (k + 1) l y)).mp hy).1
          rwa [apPt_init] at h2
        rw [hemp] at h1
        exact h1
      · refine Or.inr ?_
        have hset : fibSet p (k + 1) κ l =
              {z : Fin (k + 1) → ℝ | Fin.init z ∈ fibSet p k C l ∧
                z (Fin.last k) = f (apPt p k l (Fin.init z))} := by
          ext y
          simp only [fibSet, Set.mem_ofPred_eq, hiff, apPt_apply, init_append]
          rw [show (Fin.last (p.add k) : Fin (p + (k + 1))) = Fin.natAdd p (Fin.last k) from
              Fin.ext rfl, Fin.append_right]
        rw [hset]
        exact IsCell.graph hcell (fun y' => f (apPt p k l y'))
          (ContinuousOn.comp' hf (continuous_append l).continuousOn (fun _ hy' => hy'))
    · rcases ih C l hC with hemp | hcell
      · refine Or.inl ?_
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨y, hy⟩
        have h1 : Fin.init y ∈ fibSet p k C l := by
          show apPt p k l (Fin.init y) ∈ C
          have h2 : Fin.init (apPt p (k + 1) l y) ∈ C :=
            ((hiff (apPt p (k + 1) l y)).mp hy).1
          rwa [apPt_init] at h2
        rw [hemp] at h1
        exact h1
      · refine Or.inr ?_
        have hset : fibSet p (k + 1) κ l =
              {z : Fin (k + 1) → ℝ | Fin.init z ∈ fibSet p k C l ∧
                a (apPt p k l (Fin.init z)) < ((z (Fin.last k) : ℝ) : EReal) ∧
                ((z (Fin.last k) : ℝ) : EReal) < b (apPt p k l (Fin.init z))} := by
          ext y
          simp only [fibSet, Set.mem_ofPred_eq, hiff, apPt_apply, init_append]
          rw [show (Fin.last (p.add k) : Fin (p + (k + 1))) = Fin.natAdd p (Fin.last k) from
              Fin.ext rfl, Fin.append_right]
        rw [hset]
        exact IsCell.band hcell (fun y' => a (apPt p k l y')) (fun y' => b (apPt p k l y'))
          (ContinuousOn.comp' ha (continuous_append l).continuousOn (fun _ hy' => hy'))
          (ContinuousOn.comp' hb (continuous_append l).continuousOn (fun _ hy' => hy'))
          (fun y' hy' => hab (apPt p k l y') hy')

end Work.WilG4c
