import Mathlib
import Submission.Work.Diff.EXT.reactBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The combinatorial bookkeeping of the monomial decomposition

This module proves `Work.Diff.EXT.Mono.fam_props_T2b`, the eight combinatorial facts about the index
maps `fam j f` of the monomial decomposition:

* the two direction assignments and the four slot positions are injective,
* their ranges are pairwise disjoint,
* they cover `Fin (4+j)`,
* consequently the product over `Fin (4+j)` splits as the product of the three blocks.

The proof is an induction on the length `j` of the word; everything is done on the explicit
recursive description of `fam` given by `fam_cons_true` / `fam_cons_false` and
`slotS_succ = fun t => (slotS j t).succ`.
-/

namespace Work.Diff.EXT.Mono

open scoped BigOperators

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

/-! ## Elementary facts about `Fin` -/

/-- The insertion of a new direction `0` at the beginning of the index assignment of a factor,
followed by the shift `succ` of all the old indices.  Spelling it out as a `def` fixes the type of
the (dependent) `Fin.cons` once and for all. -/
private def cs {n a : ℕ} (d : Fin a → Fin n) : Fin (a + 1) → Fin (n + 1) :=
  Fin.cons (0 : Fin (n + 1)) (fun r : Fin a => (d r).succ)

private lemma cs_zero {n a : ℕ} (d : Fin a → Fin n) : cs d 0 = 0 := rfl

private lemma cs_succ {n a : ℕ} (d : Fin a → Fin n) (i : Fin a) : cs d i.succ = (d i).succ := rfl

private lemma succ_fin_ne_zero {n : ℕ} (i : Fin n) : (i.succ : Fin (n + 1)) ≠ 0 := by
  intro h
  exact absurd (congrArg Fin.val h) (by simp)

private lemma zero_ne_succ_fin {n : ℕ} (i : Fin n) : (0 : Fin (n + 1)) ≠ i.succ :=
  fun h => succ_fin_ne_zero i h.symm

/-- The four slot positions are always injective. -/
theorem slotS_injective (j : ℕ) : Function.Injective (slotS j) := by
  intro a b h
  have hv := congrArg Fin.val h
  simp only [slotS] at hv
  exact Fin.ext (by omega)

/-- Composing an injective map with `succ` keeps it injective. -/
private lemma succ_inj_comp {n m : ℕ} {f : Fin n → Fin m} (hf : Function.Injective f) :
    Function.Injective (fun x : Fin n => (f x).succ) := by
  intro a b h
  exact hf (Fin.succ_inj.mp h)

/-- `cs d` is injective when `d` is. -/
private lemma injective_cs {n a : ℕ} {d : Fin a → Fin n} (hd : Function.Injective d) :
    Function.Injective (cs d) := by
  intro r r' h
  revert h
  refine Fin.cases ?_ ?_ r
  · refine Fin.cases ?_ ?_ r'
    · intro _; rfl
    · intro i; exact fun h => absurd h (zero_ne_succ_fin (d i))
  · intro i
    refine Fin.cases ?_ ?_ r'
    · intro h; exact absurd h (succ_fin_ne_zero (d i))
    · intro i' h
      have h' : d i = d i' := by
        simpa only [cs_zero, cs_succ, Fin.succ_inj] using h
      rw [hd h']

/-! ## The two induction steps -/

/-- **The successor step, `true` branch.** -/
private theorem step_true {j a b : ℕ} {d₁ : Fin a → Fin (4 + j)} {d₂ : Fin b → Fin (4 + j)}
    (h1 : Function.Injective d₁) (h2 : Function.Injective d₂)
    (h4 : ∀ r r', d₁ r ≠ d₂ r')
    (h5 : ∀ r t, d₁ r ≠ slotS j t)
    (h6 : ∀ r t, d₂ r ≠ slotS j t)
    (h7 : ∀ u : Fin (4 + j), (∃ r, d₁ r = u) ∨ (∃ r, d₂ r = u) ∨ (∃ t, slotS j t = u)) :
    Function.Injective (cs d₁) ∧
    Function.Injective (fun r : Fin b => (d₂ r).succ) ∧
    Function.Injective (slotS (j + 1)) ∧
    (∀ r r', cs d₁ r ≠ (fun r : Fin b => (d₂ r).succ) r') ∧
    (∀ r t, cs d₁ r ≠ slotS (j + 1) t) ∧
    (∀ r t, (fun r : Fin b => (d₂ r).succ) r ≠ slotS (j + 1) t) ∧
    (∀ u : Fin (4 + (j + 1)),
      (∃ r, cs d₁ r = u) ∨ (∃ r, (fun r : Fin b => (d₂ r).succ) r = u)
        ∨ (∃ t, slotS (j + 1) t = u)) := by
  rw [slotS_succ]
  refine ⟨injective_cs h1, succ_inj_comp h2,
    succ_inj_comp (slotS_injective j), ?_, ?_, ?_, ?_⟩
  · intro r r'
    refine Fin.cases ?_ ?_ r
    · intro h; exact absurd h (zero_ne_succ_fin (d₂ r'))
    · intro i h; exact h4 i r' (Fin.succ_inj.mp (by simpa only [cs_succ] using h))
  · intro r t
    refine Fin.cases ?_ ?_ r
    · intro h; exact zero_ne_succ_fin (slotS j t) h
    · intro i h; exact h5 i t (Fin.succ_inj.mp (by simpa only [cs_succ] using h))
  · intro r t h
    exact h6 r t (Fin.succ_inj.mp h)
  · intro u
    refine Fin.cases ?_ ?_ u
    · exact Or.inl ⟨0, by rw [cs_zero]⟩
    · intro m
      rcases h7 m with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨t, ht⟩
      · exact Or.inl ⟨r.succ, by rw [cs_succ, hr]⟩
      · exact Or.inr (Or.inl ⟨r, by show (d₂ r).succ = m.succ; rw [hr]⟩)
      · exact Or.inr (Or.inr ⟨t, by show (slotS j t).succ = m.succ; rw [ht]⟩)

/-- **The successor step, `false` branch.** -/
private theorem step_false {j a b : ℕ} {d₁ : Fin a → Fin (4 + j)} {d₂ : Fin b → Fin (4 + j)}
    (h1 : Function.Injective d₁) (h2 : Function.Injective d₂)
    (h4 : ∀ r r', d₁ r ≠ d₂ r')
    (h5 : ∀ r t, d₁ r ≠ slotS j t)
    (h6 : ∀ r t, d₂ r ≠ slotS j t)
    (h7 : ∀ u : Fin (4 + j), (∃ r, d₁ r = u) ∨ (∃ r, d₂ r = u) ∨ (∃ t, slotS j t = u)) :
    Function.Injective (fun r : Fin a => (d₁ r).succ) ∧
    Function.Injective (cs d₂) ∧
    Function.Injective (slotS (j + 1)) ∧
    (∀ r r', (fun r : Fin a => (d₁ r).succ) r ≠ cs d₂ r') ∧
    (∀ r t, (fun r : Fin a => (d₁ r).succ) r ≠ slotS (j + 1) t) ∧
    (∀ r t, cs d₂ r ≠ slotS (j + 1) t) ∧
    (∀ u : Fin (4 + (j + 1)),
      (∃ r, (fun r : Fin a => (d₁ r).succ) r = u) ∨ (∃ r, cs d₂ r = u)
        ∨ (∃ t, slotS (j + 1) t = u)) := by
  rw [slotS_succ]
  refine ⟨succ_inj_comp h1, injective_cs h2,
    succ_inj_comp (slotS_injective j), ?_, ?_, ?_, ?_⟩
  · intro r r'
    refine Fin.cases ?_ ?_ r'
    · intro h; exact absurd h (succ_fin_ne_zero (d₁ r))
    · intro i h; exact h4 r i (Fin.succ_inj.mp (by simpa only [cs_succ] using h))
  · intro r t h
    exact h5 r t (Fin.succ_inj.mp h)
  · intro r t
    refine Fin.cases ?_ ?_ r
    · intro h; exact zero_ne_succ_fin (slotS j t) h
    · intro i h; exact h6 i t (Fin.succ_inj.mp (by simpa only [cs_succ] using h))
  · intro u
    refine Fin.cases ?_ ?_ u
    · exact Or.inr (Or.inl ⟨0, by rw [cs_zero]⟩)
    · intro m
      rcases h7 m with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨t, ht⟩
      · exact Or.inl ⟨r, by show (d₁ r).succ = m.succ; rw [hr]⟩
      · exact Or.inr (Or.inl ⟨r.succ, by rw [cs_succ, hr]⟩)
      · exact Or.inr (Or.inr ⟨t, by show (slotS j t).succ = m.succ; rw [ht]⟩)

/-! ## The product identity -/

/-- **The product identity, `true` branch.** -/
private theorem prod_true {j a b : ℕ} (d₁ : Fin a → Fin (4 + j)) (d₂ : Fin b → Fin (4 + j))
    (h8 : ∀ B : Fin (4 + j) → ℝ,
      (∏ r : Fin a, B (d₁ r)) * (∏ r : Fin b, B (d₂ r)) * (∏ t : Fin 4, B (slotS j t))
        = ∏ r : Fin (4 + j), B r) :
    ∀ B : Fin (4 + (j + 1)) → ℝ,
      (∏ r : Fin (a + 1), B (cs d₁ r)) * (∏ r : Fin b, B ((d₂ r).succ))
        * (∏ t : Fin 4, B (slotS (j + 1) t)) = ∏ r : Fin (4 + (j + 1)), B r := by
  intro B
  have h1 : (∏ r : Fin (a + 1), B (cs d₁ r)) = B 0 * ∏ r : Fin a, B ((d₁ r).succ) := by
    rw [Fin.prod_univ_succ]
    simp only [cs_zero, cs_succ]
  have h2 : (∏ r : Fin (4 + (j + 1)), B r) = B 0 * ∏ r : Fin (4 + j), B r.succ :=
    Fin.prod_univ_succ B
  have h3 : (∏ t : Fin 4, B (slotS (j + 1) t)) = ∏ t : Fin 4, B ((slotS j t).succ) := by
    rw [slotS_succ]
  rw [h1, h2, h3, ← h8 (fun r : Fin (4 + j) => B r.succ)]
  ring

/-- **The product identity, `false` branch.** -/
private theorem prod_false {j a b : ℕ} (d₁ : Fin a → Fin (4 + j)) (d₂ : Fin b → Fin (4 + j))
    (h8 : ∀ B : Fin (4 + j) → ℝ,
      (∏ r : Fin a, B (d₁ r)) * (∏ r : Fin b, B (d₂ r)) * (∏ t : Fin 4, B (slotS j t))
        = ∏ r : Fin (4 + j), B r) :
    ∀ B : Fin (4 + (j + 1)) → ℝ,
      (∏ r : Fin a, B ((d₁ r).succ)) * (∏ r : Fin (b + 1), B (cs d₂ r))
        * (∏ t : Fin 4, B (slotS (j + 1) t)) = ∏ r : Fin (4 + (j + 1)), B r := by
  intro B
  have h1 : (∏ r : Fin (b + 1), B (cs d₂ r)) = B 0 * ∏ r : Fin b, B ((d₂ r).succ) := by
    rw [Fin.prod_univ_succ]
    simp only [cs_zero, cs_succ]
  have h2 : (∏ r : Fin (4 + (j + 1)), B r) = B 0 * ∏ r : Fin (4 + j), B r.succ :=
    Fin.prod_univ_succ B
  have h3 : (∏ t : Fin 4, B (slotS (j + 1) t)) = ∏ t : Fin 4, B ((slotS j t).succ) := by
    rw [slotS_succ]
  rw [h1, h2, h3, ← h8 (fun r : Fin (4 + j) => B r.succ)]
  ring

/-! ## The target -/

theorem fam_props_T2b : ∀ (j : ℕ) (f : Fin j → Bool),
    Function.Injective (Work.Diff.EXT.fam j f).1.2 ∧
      Function.Injective (Work.Diff.EXT.fam j f).2.2 ∧
      Function.Injective (Work.Diff.EXT.slotS j) ∧
      (∀ r r', (Work.Diff.EXT.fam j f).1.2 r ≠ (Work.Diff.EXT.fam j f).2.2 r') ∧
      (∀ r t, (Work.Diff.EXT.fam j f).1.2 r ≠ Work.Diff.EXT.slotS j t) ∧
      (∀ r t, (Work.Diff.EXT.fam j f).2.2 r ≠ Work.Diff.EXT.slotS j t) ∧
      (∀ u : Fin (4 + j),
        (∃ r, (Work.Diff.EXT.fam j f).1.2 r = u) ∨ (∃ r, (Work.Diff.EXT.fam j f).2.2 r = u)
          ∨ (∃ t, Work.Diff.EXT.slotS j t = u)) ∧
      (∀ B : Fin (4 + j) → ℝ,
        (∏ r : Fin (Work.Diff.EXT.fam j f).1.1, B ((Work.Diff.EXT.fam j f).1.2 r))
          * (∏ r : Fin (Work.Diff.EXT.fam j f).2.1, B ((Work.Diff.EXT.fam j f).2.2 r))
          * (∏ t : Fin 4, B (Work.Diff.EXT.slotS j t)) = ∏ r : Fin (4 + j), B r) := by
  intro j
  induction j with
  | zero =>
    intro f
    refine ⟨fun a _ _ => Fin.elim0 a, fun a _ _ => Fin.elim0 a, slotS_injective 0,
      fun a _ _ => Fin.elim0 a, fun a _ _ => Fin.elim0 a, fun a _ _ => Fin.elim0 a, ?_, ?_⟩
    · intro u
      exact Or.inr (Or.inr ⟨u, Fin.ext (by simp [Work.Diff.EXT.slotS])⟩)
    · intro B
      have h1 : (∏ r : Fin (Work.Diff.EXT.fam 0 f).1.1, B ((Work.Diff.EXT.fam 0 f).1.2 r)) = 1 := by
        simp only [Work.Diff.EXT.fam]
        exact Fin.prod_univ_zero _
      have h2 : (∏ r : Fin (Work.Diff.EXT.fam 0 f).2.1, B ((Work.Diff.EXT.fam 0 f).2.2 r)) = 1 := by
        simp only [Work.Diff.EXT.fam]
        exact Fin.prod_univ_zero _
      have h3 : (∏ t : Fin 4, B (Work.Diff.EXT.slotS 0 t)) = ∏ t : Fin 4, B t := by
        refine Finset.prod_congr rfl (fun t _ => ?_)
        rw [show Work.Diff.EXT.slotS 0 t = t from Fin.ext (by simp [Work.Diff.EXT.slotS])]
      rw [h1, h2, h3]
      ring
  | succ j ih =>
    intro f
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih (Fin.tail f)
    have htail : f = Fin.cons (f 0) (Fin.tail f) := (Fin.cons_self_tail f).symm
    cases h0 : f 0
    · -- the new direction is put into the second factor
      rw [htail, h0, fam_cons_false j (Fin.tail f)]
      obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := step_false h1 h2 h4 h5 h6 h7
      exact ⟨s1, s2, s3, s4, s5, s6, s7,
        prod_false (Work.Diff.EXT.fam j (Fin.tail f)).1.2 (Work.Diff.EXT.fam j (Fin.tail f)).2.2 h8⟩
    · -- the new direction is put into the first factor
      rw [htail, h0, fam_cons_true j (Fin.tail f)]
      obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := step_true h1 h2 h4 h5 h6 h7
      exact ⟨s1, s2, s3, s4, s5, s6, s7,
        prod_true (Work.Diff.EXT.fam j (Fin.tail f)).1.2 (Work.Diff.EXT.fam j (Fin.tail f)).2.2 h8⟩

end Work.Diff.EXT.Mono
