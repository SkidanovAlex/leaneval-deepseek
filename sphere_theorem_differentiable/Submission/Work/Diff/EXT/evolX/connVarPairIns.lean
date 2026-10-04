import Mathlib
import Submission.Work.Diff.EXT.evolX.connVarPairDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Ballot of the insertion maps of the connection-variation pairing

The definitions are in `Submission.Work.Diff.EXT.evolX.connVarPairDefs`.  This module collects the
elementary (purely combinatorial) facts about the insertion maps `cvIns5`, `cvHins`, `cvHpos`,
`cvUslot0`, `cvUslot1` that are used to convert the value of the level-`a+1` tower at the inserted
tuple into the bound of `Work.Diff.EXT.evolX.connVar_pair_jets`:

* `cvHins_hpos` — the entry of the insertion at the position `cvHpos a ρ s` is `F s`;
* `cvHins_uslot0`, `cvHins_uslot1` — the two slots holding the frame vector;
* `cvHpos_injective` — the position map is injective;
* `cv_prod_univ_Hins` — the product of the norms over the slots of the insertion is the product over
  the arity-`3` block (the two frame slots contributing a factor `1` each).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.evolX

variable {α : Type*}

/-! ## The `5`-block -/

@[simp] theorem cvIns5_0 (Z : Fin 3 → α) (u : α) : cvIns5 Z u 0 = Z 0 := rfl
@[simp] theorem cvIns5_1 (Z : Fin 3 → α) (u : α) : cvIns5 Z u 1 = u := rfl
@[simp] theorem cvIns5_2 (Z : Fin 3 → α) (u : α) : cvIns5 Z u 2 = Z 1 := rfl
@[simp] theorem cvIns5_3 (Z : Fin 3 → α) (u : α) : cvIns5 Z u 3 = u := rfl
@[simp] theorem cvIns5_4 (Z : Fin 3 → α) (u : α) : cvIns5 Z u 4 = Z 2 := rfl

@[simp] theorem cvEven_val (t : Fin 3) : (cvEven t).val = 2 * t.val := rfl

@[simp] theorem cvEven_zero : cvEven 0 = 0 := by ext; simp [cvEven]

@[simp] theorem cvEven_one : cvEven 1 = 2 := by ext; simp [cvEven]

@[simp] theorem cvEven_two : cvEven 2 = 4 := by ext; simp [cvEven]

theorem cvEven_injective : Function.Injective cvEven := by
  intro t t' h
  have := congrArg Fin.val h
  simp only [cvEven_val] at this
  exact Fin.ext (by omega)

/-- The three *free* (even) slots of the `5`-block carry the three entries of `Z`. -/
theorem cvIns5_of_val (Z : Fin 3 → α) (u : α) (t : Fin 3) : cvIns5 Z u (cvEven t) = Z t := by
  fin_cases t <;> simp [cvIns5, cvEven]

/-! ## Valuations -/

@[simp] theorem cv_natAdd_val {n m : ℕ} (i : Fin m) : (Fin.natAdd n i).val = n + i.val := rfl

@[simp] theorem cv_castAdd_val {n m : ℕ} (i : Fin n) : (Fin.castAdd m i).val = i.val := rfl

/-! ## Evaluations of the insertion -/

theorem cvHins_left {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (u : α) (r : Fin a) :
    cvHins ρ F u (Fin.castAdd 5 r) = F (Fin.castAdd 3 r) := by
  simp [cvHins]

theorem cvHins_right {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (u : α) (j : Fin 5) :
    cvHins ρ F u (Fin.natAdd a j)
      = cvIns5 (fun t : Fin 3 => F (Fin.natAdd a (ρ t))) u j := by
  simp [cvHins]

theorem cvHpos_left {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (r : Fin a) :
    cvHpos a ρ (Fin.castAdd 3 r) = Fin.castAdd 5 r := by
  simp [cvHpos]

theorem cvHpos_natAdd {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (t : Fin 3) :
    cvHpos a ρ (Fin.natAdd a t) = Fin.natAdd a (cvEven (ρ.symm t)) := by
  simp [cvHpos]

theorem cvUslot0_eq (a : ℕ) : cvUslot0 a = Fin.natAdd a (1 : Fin 5) := rfl

theorem cvUslot1_eq (a : ℕ) : cvUslot1 a = Fin.natAdd a (3 : Fin 5) := rfl

theorem cvHins_uslot0 {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (u : α) :
    cvHins ρ F u (cvUslot0 a) = u := by
  rw [cvUslot0_eq, cvHins_right, cvIns5_1]

theorem cvHins_uslot1 {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (u : α) :
    cvHins ρ F u (cvUslot1 a) = u := by
  rw [cvUslot1_eq, cvHins_right, cvIns5_3]

/-- **The entry of the insertion at the position of `s` is `F s`.** -/
theorem cvHins_hpos {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (F : Fin (a + 3) → α) (u : α)
    (s : Fin (a + 3)) : cvHins ρ F u (cvHpos a ρ s) = F s := by
  revert s
  refine Fin.addCases (motive := fun s : Fin (a + 3) =>
    cvHins ρ F u (cvHpos a ρ s) = F s) ?_ ?_
  · intro r
    rw [cvHpos_left, cvHins_left]
  · intro t
    rw [cvHpos_natAdd, cvHins_right, cvIns5_of_val, Equiv.apply_symm_apply]

/-- **The position map is injective.** -/
theorem cvHpos_injective (a : ℕ) (ρ : Fin 3 ≃ Fin 3) : Function.Injective (cvHpos a ρ) := by
  intro s
  revert s
  refine Fin.addCases (motive := fun s : Fin (a + 3) =>
    ∀ s', cvHpos a ρ s = cvHpos a ρ s' → s = s') ?_ ?_
  · intro r s'
    revert s'
    refine Fin.addCases (motive := fun s' : Fin (a + 3) =>
      cvHpos a ρ (Fin.castAdd 3 r) = cvHpos a ρ s' → Fin.castAdd 3 r = s') ?_ ?_
    · intro r' h
      rw [cvHpos_left, cvHpos_left] at h
      exact congrArg (Fin.castAdd 3) (Fin.castAdd_injective a 5 h)
    · intro t h
      rw [cvHpos_left, cvHpos_natAdd] at h
      exfalso
      have hv := congrArg Fin.val h
      simp only [cv_castAdd_val, cv_natAdd_val, cvEven_val] at hv
      omega
  · intro t s'
    revert s'
    refine Fin.addCases (motive := fun s' : Fin (a + 3) =>
      cvHpos a ρ (Fin.natAdd a t) = cvHpos a ρ s' → Fin.natAdd a t = s') ?_ ?_
    · intro r h
      rw [cvHpos_natAdd, cvHpos_left] at h
      exfalso
      have hv := congrArg Fin.val h
      simp only [cv_castAdd_val, cv_natAdd_val, cvEven_val] at hv
      omega
    · intro t' h
      rw [cvHpos_natAdd, cvHpos_natAdd] at h
      have h2 : (cvEven (ρ.symm t)).val = (cvEven (ρ.symm t')).val := by
        have hv := congrArg Fin.val h
        simp only [cv_natAdd_val] at hv
        omega
      have h3 : (ρ.symm t).val = (ρ.symm t').val := by
        simp only [cvEven_val] at h2
        omega
      have h4 : ρ.symm t = ρ.symm t' := Fin.ext h3
      have h5 : t = t' := by
        rw [← Equiv.apply_symm_apply ρ t, h4, Equiv.apply_symm_apply ρ t']
      rw [h5]

/-- **Every slot of the insertion either is a position of the arity-`3` block or one of the two
frame slots.** -/
theorem cvHpos_cover {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (j : Fin (a + 5)) :
    (∃ s : Fin (a + 3), cvHpos a ρ s = j) ∨ j = cvUslot0 a ∨ j = cvUslot1 a := by
  revert j
  refine Fin.addCases (motive := fun j : Fin (a + 5) =>
    (∃ s : Fin (a + 3), cvHpos a ρ s = j) ∨ j = cvUslot0 a ∨ j = cvUslot1 a) ?_ ?_
  · intro r
    refine Or.inl ⟨Fin.castAdd 3 r, ?_⟩
    rw [cvHpos_left]
  · intro j5
    have h5 : ∀ t : Fin 3, cvHpos a ρ (Fin.natAdd a (ρ t)) = Fin.natAdd a (cvEven t) := by
      intro t
      rw [cvHpos_natAdd, Equiv.symm_apply_apply]
    fin_cases j5
    · refine Or.inl ⟨Fin.natAdd a (ρ 0), ?_⟩
      rw [h5 0]; rfl
    · refine Or.inr (Or.inl ?_)
      rw [cvUslot0_eq]; rfl
    · refine Or.inl ⟨Fin.natAdd a (ρ 1), ?_⟩
      rw [h5 1]; rfl
    · refine Or.inr (Or.inr ?_)
      rw [cvUslot1_eq]; rfl
    · refine Or.inl ⟨Fin.natAdd a (ρ 2), ?_⟩
      rw [h5 2]; rfl

/-! ## The product over the slots of the insertion -/

/-- **The product of the five slots of the `5`-block.** -/
theorem cv_prod_univ_five (ρ : Fin 3 ≃ Fin 3) (g : Fin 5 → ℝ) :
    (∏ j : Fin 5, g j) = (∏ t : Fin 3, g (cvEven (ρ.symm t))) * g 1 * g 3 := by
  have h1 : (∏ t : Fin 3, g (cvEven (ρ.symm t))) = ∏ t : Fin 3, g (cvEven t) := by
    refine Fintype.prod_equiv ρ.symm _ _ (fun t => ?_)
    rfl
  rw [h1, Fin.prod_univ_three, Fin.prod_univ_five]
  norm_num [cvEven]
  ring

/-- **The product over the slots of the insertion is the product over the arity-`3` block** (times the
two frame factors). -/
theorem cv_prod_univ_Hins {a : ℕ} (ρ : Fin 3 ≃ Fin 3) (g : Fin (a + 5) → ℝ) :
    (∏ j : Fin (a + 5), g j)
      = (∏ s : Fin (a + 3), g (cvHpos a ρ s)) * g (cvUslot0 a) * g (cvUslot1 a) := by
  have hsplit1 : (∏ j : Fin (a + 5), g j)
      = (∏ r : Fin a, g (Fin.castAdd 5 r)) * ∏ j : Fin 5, g (Fin.natAdd a j) :=
    Fin.prod_univ_add (M := ℝ) g
  have hsplit2 : (∏ s : Fin (a + 3), g (cvHpos a ρ s))
      = (∏ r : Fin a, g (cvHpos a ρ (Fin.castAdd 3 r)))
        * ∏ t : Fin 3, g (cvHpos a ρ (Fin.natAdd a t)) :=
    Fin.prod_univ_add (M := ℝ) (fun s : Fin (a + 3) => g (cvHpos a ρ s))
  rw [hsplit1, hsplit2, cvUslot0_eq, cvUslot1_eq]
  have h1 : (∏ r : Fin a, g (Fin.castAdd 5 r))
      = ∏ r : Fin a, g (cvHpos a ρ (Fin.castAdd 3 r)) := by
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [cvHpos_left]
  rw [h1]
  have h2 : (∏ j : Fin 5, g (Fin.natAdd a j))
      = (∏ t : Fin 3, g (cvHpos a ρ (Fin.natAdd a t))) * g (Fin.natAdd a 1)
        * g (Fin.natAdd a 3) := by
    rw [cv_prod_univ_five ρ (fun j : Fin 5 => g (Fin.natAdd a j))]
    have h3 : (∏ t : Fin 3, g (Fin.natAdd a (cvEven (ρ.symm t))))
        = ∏ t : Fin 3, g (cvHpos a ρ (Fin.natAdd a t)) := by
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [cvHpos_natAdd]
    rw [← h3]
  rw [h2]
  ring

end Work.Diff.EXT.evolX
