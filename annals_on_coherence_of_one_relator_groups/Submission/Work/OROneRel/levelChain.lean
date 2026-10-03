import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.wordOfDefs
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.normalClosure_step
import Submission.Work.OROneRel.decor_tlU_tlW_at

/-!
# The level windows of the two-letter one-relator complex, and the chain of their fundamental groups

This file is the combinatorial core of `Work.OROneRel.twoLetterFreiheitssatz`: the *band*
`D = window [0, pq]` of the `Z`-cover of `X = <a,b | (a^p b^q)^l>` has its `2`-cell attached along
the `l`-fold staircase of `u = a^p b^q`, and `D` is glued into the level complex `Y` by the line of
translates `t^i D`.

The plan (see `Submission/Work/OROneRel/NOTES_twoLetter_freiheitssatz_chain.md`) is to prove
`pi_1(D) -> pi_1(Y)` injective by a *chain* of window embeddings: for nested windows
`W' = [a,b] subset W` the quotient map `F (E_{W'}) / <<T_{W'} u R_{W'}>> -> F (E_W) / <<T_W u R_W>>`
is injective.  Each single step adds exactly two edges

  `e_1 = (a, b+1-q)`, `e_2 = (b, b+1)`     (upper step, `W = [a,b+1]`)

or

  `e_1 = (a, a-1)`, `e_2 = (b, a+p-1)`     (lower step, `W = [a-1,b]`)

and (when the new `2`-cell exists) one relator, whose attaching walk is an `l`-th power of a word
in which `e_1` and `e_2` occur exactly once.  The retraction that kills the new relator is the
general free-group lemma `Work.OROneRel.normalClosure_step`.

## Contents

* `Wedge` -- the edges of a level window;
* `Wedge_upper_add`, `Wedge_lower_add` -- the two new edges of a one-level step.
-/

namespace Work.OROneRel

noncomputable section

variable (p q : ℕ)

/-- **The edges of the level window `[a,b]`**: the edges of the level graph of the weight `tlW p q`
whose two endpoints lie in `[a,b]`. -/
def Wedge (a b : ℤ) : Set (Fin 2 × ℤ) := winE (tlW p q) a b

@[simp] theorem mem_Wedge {a b : ℤ} {e : Fin 2 × ℤ} :
    e ∈ Wedge p q a b ↔
      a ≤ e.2 ∧ e.2 ≤ b ∧ a ≤ e.2 + tlW p q e.1 ∧ e.2 + tlW p q e.1 ≤ b := Iff.rfl

/-- The `a`-edges of the level window `[a,b]`: the edges `(0,i)` with `i` in `[a, b-q]`. -/
theorem mem_Wedge_zero (a b i : ℤ) :
    ((0 : Fin 2), i) ∈ Wedge p q a b ↔ a ≤ i ∧ i + (q : ℤ) ≤ b := by
  rw [mem_Wedge]
  have h : tlW p q (0 : Fin 2) = (q : ℤ) := by simp [tlW]
  rw [h]
  constructor
  · intro h'
    exact ⟨h'.1, h'.2.2.2⟩
  · intro h'
    exact ⟨h'.1, by linarith [h'.1, h'.2], by linarith [h'.1, h'.2], h'.2⟩

/-- The `b`-edges of the level window `[a,b]`: the edges `(1,i)` with `i` in `[a+p, b]`. -/
theorem mem_Wedge_one (a b i : ℤ) :
    ((1 : Fin 2), i) ∈ Wedge p q a b ↔ a + (p : ℤ) ≤ i ∧ i ≤ b := by
  rw [mem_Wedge]
  have h : tlW p q (1 : Fin 2) = -(p : ℤ) := by simp [tlW]
  rw [h]
  constructor
  · intro h'
    exact ⟨by omega, h'.2.1⟩
  · intro h'
    exact ⟨by omega, h'.2, by omega, by omega⟩

/-- The windows are nested: `Wedge p q a b ⊆ Wedge p q a' b'` for `a' ≤ a` and `b ≤ b'`. -/
theorem Wedge_mono {a a' b b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b') :
    Wedge p q a b ⊆ Wedge p q a' b' := by
  intro e he
  rw [mem_Wedge] at he ⊢
  exact ⟨by linarith [he.1], by linarith [he.2.1], by linarith [he.2.2.1], by linarith [he.2.2.2]⟩

/-- **The upper step adds exactly the two edges `e_1 = (0, b+1-q)` and `e_2 = (1, b+1)`.** -/
theorem Wedge_upper_add (a b : ℤ) :
    Wedge p q a (b + 1) ⊆
      Wedge p q a b ∪ {((0 : Fin 2), b + 1 - (q : ℤ)), ((1 : Fin 2), b + 1)} := by
  rintro ⟨x, i⟩ he
  rw [mem_Wedge] at he
  fin_cases x
  · have h1 : a ≤ i := he.1
    have h3 : a ≤ i + (q : ℤ) := by simpa [tlW] using he.2.2.1
    have h4 : i + (q : ℤ) ≤ b + 1 := by simpa [tlW] using he.2.2.2
    by_cases h : i + (q : ℤ) ≤ b
    · exact Or.inl ((mem_Wedge_zero p q a b i).mpr ⟨h1, h⟩)
    · have h5 : i = b + 1 - (q : ℤ) := by omega
      exact Or.inr (Or.inl (by simp [h5]))
  · have h1 : a ≤ i := he.1
    have h2 : i ≤ b + 1 := he.2.1
    have h3 : a ≤ i + -(p : ℤ) := by simpa [tlW] using he.2.2.1
    by_cases h : i ≤ b
    · exact Or.inl ((mem_Wedge_one p q a b i).mpr ⟨by omega, h⟩)
    · have h5 : i = b + 1 := by omega
      exact Or.inr (Or.inr (by simp [h5]))

/-- **The lower step adds exactly the two edges `e_1 = (0, a-1)` and `e_2 = (1, a+p-1)`.** -/
theorem Wedge_lower_add (a b : ℤ) :
    Wedge p q (a - 1) b ⊆
      Wedge p q a b ∪ {((0 : Fin 2), a - 1), ((1 : Fin 2), a + (p : ℤ) - 1)} := by
  rintro ⟨x, i⟩ he
  rw [mem_Wedge] at he
  fin_cases x
  · have h1 : a - 1 ≤ i := he.1
    have h2 : i ≤ b := he.2.1
    have h3 : a - 1 ≤ i + (q : ℤ) := by simpa [tlW] using he.2.2.1
    have h4 : i + (q : ℤ) ≤ b := by simpa [tlW] using he.2.2.2
    by_cases h : a ≤ i
    · exact Or.inl ((mem_Wedge_zero p q a b i).mpr ⟨h, h4⟩)
    · have h5 : i = a - 1 := by omega
      exact Or.inr (Or.inl (by simp [h5]))
  · have h1 : a - 1 ≤ i := he.1
    have h2 : i ≤ b := he.2.1
    have h3 : a - 1 ≤ i + -(p : ℤ) := by simpa [tlW] using he.2.2.1
    have h4 : i + -(p : ℤ) ≤ b := by simpa [tlW] using he.2.2.2
    by_cases h : a + (p : ℤ) ≤ i
    · exact Or.inl ((mem_Wedge_one p q a b i).mpr ⟨h, h2⟩)
    · have h5 : i = a + (p : ℤ) - 1 := by omega
      exact Or.inr (Or.inr (by simp [h5]))

/-! ## The two new edges are not in the old window -/

theorem upper_e1_not_mem (b : ℤ) :
    (((0 : Fin 2), b + 1 - (q : ℤ)) : Fin 2 × ℤ) ∉ Wedge p q 0 b := by
  rw [mem_Wedge_zero]; omega

theorem upper_e2_not_mem (b : ℤ) :
    (((1 : Fin 2), b + 1) : Fin 2 × ℤ) ∉ Wedge p q 0 b := by
  rw [mem_Wedge_one]; omega

theorem lower_e1_not_mem (a : ℤ) :
    (((0 : Fin 2), a - 1) : Fin 2 × ℤ) ∉ Wedge p q a ((p : ℤ) * (q : ℤ)) := by
  rw [mem_Wedge_zero]; omega

theorem lower_e2_not_mem (a : ℤ) :
    (((1 : Fin 2), a + (p : ℤ) - 1) : Fin 2 × ℤ) ∉ Wedge p q a ((p : ℤ) * (q : ℤ)) := by
  rw [mem_Wedge_one]; omega

/-! ## The one-step chain -/

/-- **The upper one-step chain.**  Let `W' = [0,b]` and let `W = [0,b+1]` add the level `b+1`; let
`T` be the old tree (inside `W'`), `R` the old relators (words in the old edge group), and let the
new relator be `(A * of (0,b+1-q) * of (1,b+1) * B) ^ l` with `A, B` in the old edge group.  Then an
element of the old edge group lying in `<<T u {e_1} u {new relator} u R>>` already lies in
`<<T u R>>`. -/
theorem chain_step_up {l : ℕ} {b : ℤ} {A B : FreeGroup (Fin 2 × ℤ)}
    (hA : A ∈ Subgroup.closure (FreeGroup.of '' Wedge p q 0 b))
    (hB : B ∈ Subgroup.closure (FreeGroup.of '' Wedge p q 0 b))
    (hr : FreeGroup.mk (decor (tlW p q) (b + 1 - (p : ℤ) * (q : ℤ)) (wordOf (tlU p q ^ l))) =
      (A * FreeGroup.of ((0 : Fin 2), b + 1 - (q : ℤ)) *
        FreeGroup.of ((1 : Fin 2), b + 1) * B) ^ l)
    {T : Set (Fin 2 × ℤ)} (hT : T ⊆ Wedge p q 0 b)
    {R : Set (FreeGroup (Fin 2 × ℤ))}
    (hR : R ⊆ Subgroup.closure (FreeGroup.of '' Wedge p q 0 b))
    {y : FreeGroup (Fin 2 × ℤ)}
    (hy : y ∈ Subgroup.closure (FreeGroup.of '' Wedge p q 0 b))
    (hy' : y ∈ Subgroup.normalClosure
      (FreeGroup.of '' (T ∪ {((0 : Fin 2), b + 1 - (q : ℤ))}) ∪ R ∪
        {FreeGroup.mk (decor (tlW p q) (b + 1 - (p : ℤ) * (q : ℤ))
          (wordOf (tlU p q ^ l)))})) :
    y ∈ Subgroup.normalClosure (FreeGroup.of '' T ∪ R) := by
  set e₁ : Fin 2 × ℤ := ((0 : Fin 2), b + 1 - (q : ℤ)) with he₁
  set e₂ : Fin 2 × ℤ := ((1 : Fin 2), b + 1) with he₂
  have h12 : e₁ ≠ e₂ := by
    rw [he₁, he₂]
    intro h
    exact absurd (congrArg Prod.fst h) (by simp)
  have hcomp : Wedge p q 0 b ⊆ {e : Fin 2 × ℤ | e ≠ e₁ ∧ e ≠ e₂} := by
    intro e he
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [he₁] at h
      exact upper_e1_not_mem p q b (h ▸ he)
    · rw [he₂] at h
      exact upper_e2_not_mem p q b (h ▸ he)
  have mono : Subgroup.closure (FreeGroup.of '' Wedge p q 0 b) ≤
      Subgroup.closure (FreeGroup.of '' {e : Fin 2 × ℤ | e ≠ e₁ ∧ e ≠ e₂}) :=
    Subgroup.closure_mono (Set.image_mono hcomp)
  have hR' : (FreeGroup.of '' T ∪ R) ⊆
      Subgroup.closure (FreeGroup.of '' {e : Fin 2 × ℤ | e ≠ e₁ ∧ e ≠ e₂}) :=
    Set.union_subset
      (fun x hx => mono (Subgroup.subset_closure (Set.image_mono hT hx)))
      (fun x hx => mono (hR hx))
  have hy'' : y ∈ Subgroup.normalClosure
      ((FreeGroup.of '' T ∪ R) ∪ {FreeGroup.of e₁} ∪
        {(A * FreeGroup.of e₁ * 1 * FreeGroup.of e₂ * B) ^ l}) := by
    have h := hy'
    rw [hr] at h
    simp only [Set.image_union, Set.image_singleton] at h
    simpa only [Set.union_assoc, Set.union_comm, Set.union_left_comm, Set.union_right_comm,
      he₁, mul_one] using h
  exact normalClosure_step h12 (mono hA) (mono hB) (Subgroup.one_mem _) hR' l (mono hy) hy''

/-- **The lower one-step chain.**  The mirror of `chain_step_up`: passing from the window `[a,b]` to
`[a-1,b]`, the new relator is `(of (0,a-1) * C * of (1,a+p-1)) ^ l`, and both new letters occur
once; the retraction kills `e_1` and sends `e_2` to `C⁻¹` (together with the `1`s around). -/
theorem chain_step_down {l : ℕ} {a : ℤ} {C : FreeGroup (Fin 2 × ℤ)}
    (hC : C ∈ Subgroup.closure (FreeGroup.of '' Wedge p q a ((p : ℤ) * (q : ℤ))))
    (hr : FreeGroup.mk (decor (tlW p q) (a - 1) (wordOf (tlU p q ^ l))) =
      (FreeGroup.of ((0 : Fin 2), a - 1) * C *
        FreeGroup.of ((1 : Fin 2), a + (p : ℤ) - 1)) ^ l)
    {T : Set (Fin 2 × ℤ)} (hT : T ⊆ Wedge p q a ((p : ℤ) * (q : ℤ)))
    {R : Set (FreeGroup (Fin 2 × ℤ))}
    (hR : R ⊆ Subgroup.closure (FreeGroup.of '' Wedge p q a ((p : ℤ) * (q : ℤ))))
    {y : FreeGroup (Fin 2 × ℤ)}
    (hy : y ∈ Subgroup.closure (FreeGroup.of '' Wedge p q a ((p : ℤ) * (q : ℤ))))
    (hy' : y ∈ Subgroup.normalClosure
      (FreeGroup.of '' (T ∪ {((0 : Fin 2), a - 1)}) ∪ R ∪
        {FreeGroup.mk (decor (tlW p q) (a - 1) (wordOf (tlU p q ^ l)))})) :
    y ∈ Subgroup.normalClosure (FreeGroup.of '' T ∪ R) := by
  set e₁ : Fin 2 × ℤ := ((0 : Fin 2), a - 1) with he₁
  set e₂ : Fin 2 × ℤ := ((1 : Fin 2), a + (p : ℤ) - 1) with he₂
  have h12 : e₁ ≠ e₂ := by
    rw [he₁, he₂]
    intro h
    exact absurd (congrArg Prod.fst h) (by simp)
  have hcomp : Wedge p q a ((p : ℤ) * (q : ℤ)) ⊆ {e : Fin 2 × ℤ | e ≠ e₁ ∧ e ≠ e₂} := by
    intro e he
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [he₁] at h
      exact lower_e1_not_mem p q a (h ▸ he)
    · rw [he₂] at h
      exact lower_e2_not_mem p q a (h ▸ he)
  have mono : Subgroup.closure (FreeGroup.of '' Wedge p q a ((p : ℤ) * (q : ℤ))) ≤
      Subgroup.closure (FreeGroup.of '' {e : Fin 2 × ℤ | e ≠ e₁ ∧ e ≠ e₂}) :=
    Subgroup.closure_mono (Set.image_mono hcomp)
  have hR' : (FreeGroup.of '' T ∪ R) ⊆
      Subgroup.closure (FreeGroup.of '' {e : Fin 2 × ℤ | e ≠ e₁ ∧ e ≠ e₂}) :=
    Set.union_subset
      (fun x hx => mono (Subgroup.subset_closure (Set.image_mono hT hx)))
      (fun x hx => mono (hR hx))
  have hy'' : y ∈ Subgroup.normalClosure
      ((FreeGroup.of '' T ∪ R) ∪ {FreeGroup.of e₁} ∪
        {(1 * FreeGroup.of e₁ * C * FreeGroup.of e₂ * 1) ^ l}) := by
    have h := hy'
    rw [hr] at h
    simp only [Set.image_union, Set.image_singleton] at h
    simpa only [Set.union_assoc, Set.union_comm, Set.union_left_comm, Set.union_right_comm,
      he₁, one_mul, mul_one] using h
  exact normalClosure_step h12 (Subgroup.one_mem _) (Subgroup.one_mem _) (mono hC) hR' l
    (mono hy) hy''

/-! ## The level trees and the relator sets of the chain -/

/-- **The global tree of the level graph**: the band tree `T₀`, the `a`-edges below the band and the
`a`-edges above the band.  (Only `a`-edges outside the band are added, which is what makes every
one-level step add exactly one tree edge.) -/
def TallGlob (T₀ : Set (Fin 2 × ℤ)) : Set (Fin 2 × ℤ) :=
  T₀ ∪ {e : Fin 2 × ℤ | e.1 = 0 ∧ (e.2 < 0 ∨ (p : ℤ) * (q : ℤ) - (q : ℤ) < e.2)}

/-- The tree of the level window `[a,b]`: the part of the global tree inside the window. -/
def Wtree (T₀ : Set (Fin 2 × ℤ)) (a b : ℤ) : Set (Fin 2 × ℤ) := TallGlob p q T₀ ∩ Wedge p q a b

/-- The `2`-cell relators supported in the level window `[0,b]`. -/
def WrelUp (l : ℕ) (b : ℤ) : Set (FreeGroup (Fin 2 × ℤ)) :=
  {w | ∃ m : ℤ, 0 ≤ m ∧ m + (p : ℤ) * (q : ℤ) ≤ b ∧
      w = FreeGroup.mk (decor (tlW p q) m (wordOf (tlU p q ^ l)))}

/-- The `2`-cell relators supported in the level window `[a,pq]`. -/
def WrelDown (l : ℕ) (a : ℤ) : Set (FreeGroup (Fin 2 × ℤ)) :=
  {w | ∃ m : ℤ, a ≤ m ∧ m ≤ 0 ∧
      w = FreeGroup.mk (decor (tlW p q) m (wordOf (tlU p q ^ l)))}

/-- The tree of the window `[0,b]` gains exactly the edge `(0, b+1-q)` when `b` grows to `b+1`. -/
theorem Wtree_upper_step {T₀ : Set (Fin 2 × ℤ)} (hT₀ : T₀ ⊆ Wedge p q 0 ((p : ℤ) * (q : ℤ)))
    (hp : 1 ≤ p) {b : ℤ} (hb : (p : ℤ) * (q : ℤ) ≤ b) :
    Wtree p q T₀ 0 (b + 1) = Wtree p q T₀ 0 b ∪ {((0 : Fin 2), b + 1 - (q : ℤ))} := by
  ext e
  simp only [Wtree, Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨heT, heW⟩
    rcases Wedge_upper_add p q 0 b heW with h | h | h
    · exact Or.inl ⟨heT, h⟩
    · exact Or.inr h
    · exfalso
      rw [TallGlob] at heT
      rcases heT with hT | hT
      · have hmem : e ∈ Wedge p q 0 ((p : ℤ) * (q : ℤ)) := hT₀ hT
        rw [h] at hmem
        rw [mem_Wedge_one] at hmem
        omega
      · obtain ⟨h1, -⟩ := hT
        rw [h] at h1
        exact absurd h1 (by simp)
  · rintro (⟨heT, heW⟩ | rfl)
    · exact ⟨heT, Wedge_mono p q le_rfl (by omega) heW⟩
    · refine ⟨?_, ?_⟩
      · rw [TallGlob]
        right
        refine ⟨rfl, Or.inr ?_⟩
        omega
      · rw [mem_Wedge_zero]
        have hq1 : (q : ℤ) ≤ (p : ℤ) * (q : ℤ) := by
          have hp1 : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
          nlinarith [show (0 : ℤ) ≤ (q : ℤ) by positivity]
        omega

/-- The tree of the window `[a,pq]` gains exactly the edge `(0, a-1)` when `a` decreases to `a-1`. -/
theorem Wtree_lower_step {T₀ : Set (Fin 2 × ℤ)} (hT₀ : T₀ ⊆ Wedge p q 0 ((p : ℤ) * (q : ℤ)))
    (hp : 1 ≤ p) {a : ℤ} (ha : a ≤ 0) :
    Wtree p q T₀ (a - 1) ((p : ℤ) * (q : ℤ)) =
      Wtree p q T₀ a ((p : ℤ) * (q : ℤ)) ∪ {((0 : Fin 2), a - 1)} := by
  ext e
  simp only [Wtree, Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨heT, heW⟩
    rcases Wedge_lower_add p q a ((p : ℤ) * (q : ℤ)) heW with h | h | h
    · exact Or.inl ⟨heT, h⟩
    · exact Or.inr h
    · exfalso
      rw [TallGlob] at heT
      rcases heT with hT | hT
      · have hmem : e ∈ Wedge p q 0 ((p : ℤ) * (q : ℤ)) := hT₀ hT
        rw [h] at hmem
        rw [mem_Wedge_one] at hmem
        have : (0 : ℤ) + (p : ℤ) ≤ 0 + (p : ℤ) - 1 := by omega
        omega
      · obtain ⟨h1, -⟩ := hT
        rw [h] at h1
        exact absurd h1 (by simp)
  · rintro (⟨heT, heW⟩ | rfl)
    · exact ⟨heT, Wedge_mono p q (by omega) le_rfl heW⟩
    · refine ⟨?_, ?_⟩
      · rw [TallGlob]
        right
        exact ⟨rfl, Or.inl (by omega)⟩
      · rw [mem_Wedge_zero]
        have hq1 : (q : ℤ) ≤ (p : ℤ) * (q : ℤ) := by
          have hp1 : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
          nlinarith [show (0 : ℤ) ≤ (q : ℤ) by positivity]
        omega

/-- The relators of the window `[0,b]` are the relators of `[0,b-1]` plus the new one. -/
theorem WrelUp_step (l : ℕ) {b : ℤ} (hb : 0 ≤ b + 1 - (p : ℤ) * (q : ℤ)) :
    WrelUp p q l (b + 1) = WrelUp p q l b ∪
      {FreeGroup.mk (decor (tlW p q) (b + 1 - (p : ℤ) * (q : ℤ)) (wordOf (tlU p q ^ l)))} := by
  ext w
  simp only [WrelUp, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, hm0, hmb, rfl⟩
    by_cases h : m + (p : ℤ) * (q : ℤ) ≤ b
    · exact Or.inl ⟨m, hm0, h, rfl⟩
    · right
      have hm : m = b + 1 - (p : ℤ) * (q : ℤ) := by omega
      rw [hm]
  · rintro (⟨m, hm0, hmb, rfl⟩ | rfl)
    · exact ⟨m, hm0, by omega, rfl⟩
    · exact ⟨b + 1 - (p : ℤ) * (q : ℤ), by omega, by omega, rfl⟩

/-- The relators of the window `[a,pq]` are the relators of `[a+1,pq]` plus the new one. -/
theorem WrelDown_step (l : ℕ) {a : ℤ} (ha : a ≤ 1) :
    WrelDown p q l (a - 1) = WrelDown p q l a ∪
      {FreeGroup.mk (decor (tlW p q) (a - 1) (wordOf (tlU p q ^ l)))} := by
  ext w
  simp only [WrelDown, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, hm0, hma, rfl⟩
    by_cases h : a ≤ m
    · exact Or.inl ⟨m, h, hma, rfl⟩
    · right
      have hm : m = a - 1 := by omega
      rw [hm]
  · rintro (⟨m, hm0, hma, rfl⟩ | rfl)
    · exact ⟨m, by omega, hma, rfl⟩
    · exact ⟨a - 1, by omega, by omega, rfl⟩

/-! ## The iterated chain -/

/-- **The upper chain, iterated.**  From the window `[0,B]` (whose tree is `Wtree` and whose
relators are `WrelUp`) down to the band `[0,pq]`. -/
theorem chain_up_iterate (l : ℕ) (hp : 1 ≤ p) (_hq : 1 ≤ q) {T₀ : Set (Fin 2 × ℤ)}
    (hT₀ : T₀ ⊆ Wedge p q 0 ((p : ℤ) * (q : ℤ)))
    (hsup : ∀ {b : ℤ}, (p : ℤ) * (q : ℤ) ≤ b →
      WrelUp p q l b ⊆ Subgroup.closure (FreeGroup.of '' Wedge p q 0 b))
    (hwalk : ∀ {b : ℤ}, (p : ℤ) * (q : ℤ) ≤ b → ∃ A B : FreeGroup (Fin 2 × ℤ),
      A ∈ Subgroup.closure (FreeGroup.of '' Wedge p q 0 b) ∧
      B ∈ Subgroup.closure (FreeGroup.of '' Wedge p q 0 b) ∧
      FreeGroup.mk (decor (tlW p q) (b + 1 - (p : ℤ) * (q : ℤ)) (wordOf (tlU p q ^ l))) =
        (A * FreeGroup.of ((0 : Fin 2), b + 1 - (q : ℤ)) *
          FreeGroup.of ((1 : Fin 2), b + 1) * B) ^ l)
    {B : ℤ} (hB : (p : ℤ) * (q : ℤ) ≤ B) {y : FreeGroup (Fin 2 × ℤ)}
    (hy : y ∈ Subgroup.closure (FreeGroup.of '' Wedge p q 0 ((p : ℤ) * (q : ℤ)))) :
    y ∈ Subgroup.normalClosure (FreeGroup.of '' Wtree p q T₀ 0 B ∪ WrelUp p q l B) →
      y ∈ Subgroup.normalClosure
        (FreeGroup.of '' Wtree p q T₀ 0 ((p : ℤ) * (q : ℤ)) ∪ WrelUp p q l ((p : ℤ) * (q : ℤ))) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, B = (p : ℤ) * (q : ℤ) + n :=
    ⟨(B - (p : ℤ) * (q : ℤ)).toNat, by omega⟩
  clear hB
  induction n with
  | zero =>
    intro h
    simpa using h
  | succ n ihn =>
    intro h
    set b : ℤ := (p : ℤ) * (q : ℤ) + (n : ℤ) with hb
    rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 from by push_cast; ring] at h
    rw [show (p : ℤ) * (q : ℤ) + ((n : ℤ) + 1) = b + 1 from by rw [hb]; ring] at h
    have hb' : (p : ℤ) * (q : ℤ) ≤ b := by omega
    have hstep : Wtree p q T₀ 0 (b + 1) = Wtree p q T₀ 0 b ∪ {((0 : Fin 2), b + 1 - (q : ℤ))} :=
      Wtree_upper_step p q hT₀ hp hb'
    have hrstep : WrelUp p q l (b + 1) = WrelUp p q l b ∪
        {FreeGroup.mk (decor (tlW p q) (b + 1 - (p : ℤ) * (q : ℤ)) (wordOf (tlU p q ^ l)))} :=
      WrelUp_step p q l (by omega)
    rw [hstep, hrstep] at h
    obtain ⟨A, B, hA, hB, hr⟩ := hwalk hb'
    rw [← Set.union_assoc] at h
    have hyb : y ∈ Subgroup.closure (FreeGroup.of '' Wedge p q 0 b) :=
      Subgroup.closure_mono (Set.image_mono (Wedge_mono p q le_rfl (by omega))) hy
    have hres := chain_step_up p q (b := b) hA hB hr
      (T := Wtree p q T₀ 0 b) (fun e he => he.2)
      (R := WrelUp p q l b) (hsup hb') hyb h
    exact ihn hres

/-- **The lower chain, iterated.**  From the window `[a,pq]` down to the band `[0,pq]`. -/
theorem chain_down_iterate (l : ℕ) (hp : 1 ≤ p) (_hq : 1 ≤ q) {T₀ : Set (Fin 2 × ℤ)}
    (hT₀ : T₀ ⊆ Wedge p q 0 ((p : ℤ) * (q : ℤ)))
    (hsup : ∀ {a : ℤ}, a ≤ 0 →
      WrelDown p q l a ⊆ Subgroup.closure (FreeGroup.of '' Wedge p q a ((p : ℤ) * (q : ℤ))))
    (hwalk : ∀ {a : ℤ}, a ≤ 1 → ∃ C : FreeGroup (Fin 2 × ℤ),
      C ∈ Subgroup.closure (FreeGroup.of '' Wedge p q a ((p : ℤ) * (q : ℤ))) ∧
      FreeGroup.mk (decor (tlW p q) (a - 1) (wordOf (tlU p q ^ l))) =
        (FreeGroup.of ((0 : Fin 2), a - 1) * C *
          FreeGroup.of ((1 : Fin 2), a + (p : ℤ) - 1)) ^ l)
    {A : ℤ} (hA : A ≤ 0) {y : FreeGroup (Fin 2 × ℤ)}
    (hy : y ∈ Subgroup.closure (FreeGroup.of '' Wedge p q 0 ((p : ℤ) * (q : ℤ)))) :
    y ∈ Subgroup.normalClosure (FreeGroup.of '' Wtree p q T₀ A ((p : ℤ) * (q : ℤ)) ∪ WrelDown p q l A) →
      y ∈ Subgroup.normalClosure
        (FreeGroup.of '' Wtree p q T₀ 0 ((p : ℤ) * (q : ℤ)) ∪
          WrelDown p q l 0) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, A = -(n : ℤ) := ⟨(-A).toNat, by omega⟩
  clear hA
  induction n with
  | zero =>
    intro h
    simpa using h
  | succ n ihn =>
    intro h
    set a : ℤ := -(n : ℤ) with ha
    rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 from by push_cast; ring] at h
    rw [show -((n : ℤ) + 1) = a - 1 from by rw [ha]; ring] at h
    have ha' : a ≤ 0 := by omega
    have hstep : Wtree p q T₀ (a - 1) ((p : ℤ) * (q : ℤ)) =
        Wtree p q T₀ a ((p : ℤ) * (q : ℤ)) ∪ {((0 : Fin 2), a - 1)} :=
      Wtree_lower_step p q hT₀ hp ha'
    have hrstep : WrelDown p q l (a - 1) = WrelDown p q l a ∪
        {FreeGroup.mk (decor (tlW p q) (a - 1) (wordOf (tlU p q ^ l)))} :=
      WrelDown_step p q l (by omega)
    rw [hstep, hrstep] at h
    obtain ⟨C, hC, hr⟩ := hwalk (show a ≤ 1 by omega)
    rw [← Set.union_assoc] at h
    have hya : y ∈ Subgroup.closure (FreeGroup.of '' Wedge p q a ((p : ℤ) * (q : ℤ))) :=
      Subgroup.closure_mono (Set.image_mono (Wedge_mono p q (by omega) le_rfl)) hy
    have hres := chain_step_down p q (a := a) hC hr
      (T := Wtree p q T₀ a ((p : ℤ) * (q : ℤ))) (fun e he => he.2)
      (R := WrelDown p q l a) (hsup ha') hya h
    exact ihn hres

/-- The `2`-cell relators supported in the level window `[a,b]` (the general two-sided form). -/
def WrelGen (l : ℕ) (a b : ℤ) : Set (FreeGroup (Fin 2 × ℤ)) :=
  {w | ∃ m : ℤ, a ≤ m ∧ m + (p : ℤ) * (q : ℤ) ≤ b ∧
      w = FreeGroup.mk (decor (tlW p q) m (wordOf (tlU p q ^ l)))}

theorem WrelGen_step_up (l : ℕ) {a b : ℤ} (hb : a ≤ b + 1 - (p : ℤ) * (q : ℤ)) :
    WrelGen p q l a (b + 1) = WrelGen p q l a b ∪
      {FreeGroup.mk (decor (tlW p q) (b + 1 - (p : ℤ) * (q : ℤ)) (wordOf (tlU p q ^ l)))} := by
  ext w
  simp only [WrelGen, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, hm0, hmb, rfl⟩
    by_cases h : m + (p : ℤ) * (q : ℤ) ≤ b
    · exact Or.inl ⟨m, hm0, h, rfl⟩
    · right
      have hm : m = b + 1 - (p : ℤ) * (q : ℤ) := by omega
      rw [hm]
  · rintro (⟨m, hm0, hmb, rfl⟩ | rfl)
    · exact ⟨m, hm0, by omega, rfl⟩
    · exact ⟨b + 1 - (p : ℤ) * (q : ℤ), by omega, by omega, rfl⟩

theorem WrelGen_step_down (l : ℕ) {a b : ℤ} (hb : a - 1 + (p : ℤ) * (q : ℤ) ≤ b) :
    WrelGen p q l (a - 1) b = WrelGen p q l a b ∪
      {FreeGroup.mk (decor (tlW p q) (a - 1) (wordOf (tlU p q ^ l)))} := by
  ext w
  simp only [WrelGen, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, hm0, hmb, rfl⟩
    by_cases h : a ≤ m
    · exact Or.inl ⟨m, h, hmb, rfl⟩
    · right
      have hm : m = a - 1 := by omega
      rw [hm]
  · rintro (⟨m, hm0, hmb, rfl⟩ | rfl)
    · exact ⟨m, by omega, hmb, rfl⟩
    · exact ⟨a - 1, by omega, by omega, rfl⟩

/-- The tree of the window `[A,b]` with anchor `A` gains exactly the edge `(0, b+1-q)` when `b`
grows to `b+1`; the other new edge `(1,b+1)` is a `b`-edge and hence outside the global tree. -/
theorem Wtree_upper_step_gen {T₀ : Set (Fin 2 × ℤ)}
    (hT₀ : T₀ ⊆ Wedge p q 0 ((p : ℤ) * (q : ℤ))) (hp : 1 ≤ p) {A b : ℤ}
    (hA : A ≤ 0) (hb : (p : ℤ) * (q : ℤ) ≤ b) :
    Wtree p q T₀ A (b + 1) = Wtree p q T₀ A b ∪ {((0 : Fin 2), b + 1 - (q : ℤ))} := by
  have h := Wtree_upper_step (p := p) (q := q) (T₀ := T₀) hT₀ hp (b := b) hb
  ext e
  simp only [Wtree, Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff] at h ⊢
  constructor
  · rintro ⟨heT, heW⟩
    rcases Wedge_upper_add p q A b heW with h1 | h1 | h1
    · exact Or.inl ⟨heT, h1⟩
    · exact Or.inr h1
    · exfalso
      rw [TallGlob] at heT
      rcases heT with hT | hT
      · have hmem : e ∈ Wedge p q 0 ((p : ℤ) * (q : ℤ)) := hT₀ hT
        rw [h1] at hmem
        rw [mem_Wedge_one] at hmem
        omega
      · obtain ⟨h2, -⟩ := hT
        rw [h1] at h2
        exact absurd h2 (by simp)
  · rintro (⟨heT, heW⟩ | rfl)
    · exact ⟨heT, Wedge_mono p q (by omega) (by omega) heW⟩
    · refine ⟨?_, ?_⟩
      · rw [TallGlob]
        right
        exact ⟨rfl, Or.inr (by omega)⟩
      · rw [mem_Wedge_zero]
        have hq1 : (q : ℤ) ≤ (p : ℤ) * (q : ℤ) := by
          have hp1 : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
          nlinarith [show (0 : ℤ) ≤ (q : ℤ) by positivity]
        omega

/-- The tree of the window `[a,B]` loses the edge `(0,a)` when `a` decreases to `a-1` (the other
new edge `(1, a+p-1)` is a `b`-edge, outside the global tree). -/
theorem Wtree_lower_step_gen {T₀ : Set (Fin 2 × ℤ)}
    (hT₀ : T₀ ⊆ Wedge p q 0 ((p : ℤ) * (q : ℤ))) (hp : 1 ≤ p) {a B : ℤ}
    (ha : a ≤ 0) (hB : (p : ℤ) * (q : ℤ) ≤ B) :
    Wtree p q T₀ (a - 1) B = Wtree p q T₀ a B ∪ {((0 : Fin 2), a - 1)} := by
  ext e
  simp only [Wtree, Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨heT, heW⟩
    rcases Wedge_lower_add p q a B heW with h1 | h1 | h1
    · exact Or.inl ⟨heT, h1⟩
    · exact Or.inr h1
    · exfalso
      rw [TallGlob] at heT
      rcases heT with hT | hT
      · have hmem : e ∈ Wedge p q 0 ((p : ℤ) * (q : ℤ)) := hT₀ hT
        rw [h1] at hmem
        rw [mem_Wedge_one] at hmem
        omega
      · obtain ⟨h2, -⟩ := hT
        rw [h1] at h2
        exact absurd h2 (by simp)
  · rintro (⟨heT, heW⟩ | rfl)
    · exact ⟨heT, Wedge_mono p q (by omega) (by omega) heW⟩
    · refine ⟨?_, ?_⟩
      · rw [TallGlob]
        right
        exact ⟨rfl, Or.inl (by omega)⟩
      · rw [mem_Wedge_zero]
        have hq1 : (q : ℤ) ≤ (p : ℤ) * (q : ℤ) := by
          have hp1 : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
          nlinarith [show (0 : ℤ) ≤ (q : ℤ) by positivity]
        omega

/-! ## The general (two-sided) chain step -/

theorem upper_e1_not_mem_gen (A b : ℤ) :
    (((0 : Fin 2), b + 1 - (q : ℤ)) : Fin 2 × ℤ) ∉ Wedge p q A b := by
  rw [mem_Wedge_zero]; omega

theorem upper_e2_not_mem_gen (A b : ℤ) :
    (((1 : Fin 2), b + 1) : Fin 2 × ℤ) ∉ Wedge p q A b := by
  rw [mem_Wedge_one]; omega

/-- The upper one-step chain with an arbitrary lower anchor `A`: the window `[A,b+1]` is reduced to
`[A,b]`, the new edges being `(0,b+1-q)` and `(1,b+1)` and the new relator the one at level
`b+1-pq`. -/
theorem chain_step_up_gen {l : ℕ} {A b : ℤ} {A' B' : FreeGroup (Fin 2 × ℤ)}
    (hA' : A' ∈ Subgroup.closure (FreeGroup.of '' Wedge p q A b))
    (hB' : B' ∈ Subgroup.closure (FreeGroup.of '' Wedge p q A b))
    (hr : FreeGroup.mk (decor (tlW p q) (b + 1 - (p : ℤ) * (q : ℤ)) (wordOf (tlU p q ^ l))) =
      (A' * FreeGroup.of ((0 : Fin 2), b + 1 - (q : ℤ)) *
        FreeGroup.of ((1 : Fin 2), b + 1) * B') ^ l)
    {T : Set (Fin 2 × ℤ)} (hT : T ⊆ Wedge p q A b)
    {R : Set (FreeGroup (Fin 2 × ℤ))}
    (hR : R ⊆ Subgroup.closure (FreeGroup.of '' Wedge p q A b))
    {y : FreeGroup (Fin 2 × ℤ)}
    (hy : y ∈ Subgroup.closure (FreeGroup.of '' Wedge p q A b))
    (hy' : y ∈ Subgroup.normalClosure
      (FreeGroup.of '' (T ∪ {((0 : Fin 2), b + 1 - (q : ℤ))}) ∪ R ∪
        {FreeGroup.mk (decor (tlW p q) (b + 1 - (p : ℤ) * (q : ℤ))
          (wordOf (tlU p q ^ l)))})) :
    y ∈ Subgroup.normalClosure (FreeGroup.of '' T ∪ R) := by
  set e₁ : Fin 2 × ℤ := ((0 : Fin 2), b + 1 - (q : ℤ)) with he₁
  set e₂ : Fin 2 × ℤ := ((1 : Fin 2), b + 1) with he₂
  have h12 : e₁ ≠ e₂ := by
    rw [he₁, he₂]
    intro h
    exact absurd (congrArg Prod.fst h) (by simp)
  have hcomp : Wedge p q A b ⊆ {e : Fin 2 × ℤ | e ≠ e₁ ∧ e ≠ e₂} := by
    intro e he
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [he₁] at h
      exact upper_e1_not_mem_gen p q A b (h ▸ he)
    · rw [he₂] at h
      exact upper_e2_not_mem_gen p q A b (h ▸ he)
  have mono : Subgroup.closure (FreeGroup.of '' Wedge p q A b) ≤
      Subgroup.closure (FreeGroup.of '' {e : Fin 2 × ℤ | e ≠ e₁ ∧ e ≠ e₂}) :=
    Subgroup.closure_mono (Set.image_mono hcomp)
  have hR' : (FreeGroup.of '' T ∪ R) ⊆
      Subgroup.closure (FreeGroup.of '' {e : Fin 2 × ℤ | e ≠ e₁ ∧ e ≠ e₂}) :=
    Set.union_subset
      (fun x hx => mono (Subgroup.subset_closure (Set.image_mono hT hx)))
      (fun x hx => mono (hR hx))
  have hy'' : y ∈ Subgroup.normalClosure
      ((FreeGroup.of '' T ∪ R) ∪ {FreeGroup.of e₁} ∪
        {(A' * FreeGroup.of e₁ * 1 * FreeGroup.of e₂ * B') ^ l}) := by
    have h := hy'
    rw [hr] at h
    simp only [Set.image_union, Set.image_singleton] at h
    simpa only [Set.union_assoc, Set.union_comm, Set.union_left_comm, Set.union_right_comm,
      he₁, mul_one] using h
  exact normalClosure_step h12 (mono hA') (mono hB') (Subgroup.one_mem _) hR' l (mono hy) hy''

/-- **The upper chain with an arbitrary lower anchor.**  From the window `[A,B]` down to `[A,pq]`. -/
theorem chain_up_iterate_gen (l : ℕ) (hp : 1 ≤ p) (_hq : 1 ≤ q) {T₀ : Set (Fin 2 × ℤ)}
    (hT₀ : T₀ ⊆ Wedge p q 0 ((p : ℤ) * (q : ℤ)))
    (hsup : ∀ {a b : ℤ}, WrelGen p q l a b ⊆ Subgroup.closure (FreeGroup.of '' Wedge p q a b))
    (hwalk : ∀ {A b : ℤ}, A ≤ 0 → (p : ℤ) * (q : ℤ) ≤ b → ∃ A' B' : FreeGroup (Fin 2 × ℤ),
      A' ∈ Subgroup.closure (FreeGroup.of '' Wedge p q A b) ∧
      B' ∈ Subgroup.closure (FreeGroup.of '' Wedge p q A b) ∧
      FreeGroup.mk (decor (tlW p q) (b + 1 - (p : ℤ) * (q : ℤ)) (wordOf (tlU p q ^ l))) =
        (A' * FreeGroup.of ((0 : Fin 2), b + 1 - (q : ℤ)) *
          FreeGroup.of ((1 : Fin 2), b + 1) * B') ^ l)
    {A B : ℤ} (hA : A ≤ 0) (hB : (p : ℤ) * (q : ℤ) ≤ B) {y : FreeGroup (Fin 2 × ℤ)}
    (hy : y ∈ Subgroup.closure (FreeGroup.of '' Wedge p q A ((p : ℤ) * (q : ℤ)))) :
    y ∈ Subgroup.normalClosure (FreeGroup.of '' Wtree p q T₀ A B ∪ WrelGen p q l A B) →
      y ∈ Subgroup.normalClosure
        (FreeGroup.of '' Wtree p q T₀ A ((p : ℤ) * (q : ℤ)) ∪ WrelGen p q l A ((p : ℤ) * (q : ℤ))) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, B = (p : ℤ) * (q : ℤ) + n :=
    ⟨(B - (p : ℤ) * (q : ℤ)).toNat, by omega⟩
  clear hB
  induction n with
  | zero =>
    intro h
    simpa using h
  | succ n ihn =>
    intro h
    set b : ℤ := (p : ℤ) * (q : ℤ) + (n : ℤ) with hb
    rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 from by push_cast; ring] at h
    rw [show (p : ℤ) * (q : ℤ) + ((n : ℤ) + 1) = b + 1 from by rw [hb]; ring] at h
    have hb' : (p : ℤ) * (q : ℤ) ≤ b := by omega
    have hstep : Wtree p q T₀ A (b + 1) = Wtree p q T₀ A b ∪ {((0 : Fin 2), b + 1 - (q : ℤ))} :=
      Wtree_upper_step_gen p q hT₀ hp hA hb'
    have hrstep : WrelGen p q l A (b + 1) = WrelGen p q l A b ∪
        {FreeGroup.mk (decor (tlW p q) (b + 1 - (p : ℤ) * (q : ℤ)) (wordOf (tlU p q ^ l)))} :=
      WrelGen_step_up p q l (by omega)
    rw [hstep, hrstep] at h
    rw [← Set.union_assoc] at h
    obtain ⟨A', B', hA', hB', hr⟩ := hwalk hA hb'
    have hyb : y ∈ Subgroup.closure (FreeGroup.of '' Wedge p q A b) :=
      Subgroup.closure_mono (Set.image_mono (Wedge_mono p q le_rfl (by omega))) hy
    have hres := chain_step_up_gen p q (A := A) (b := b) hA' hB' hr
      (T := Wtree p q T₀ A b) (fun e he => he.2)
      (R := WrelGen p q l A b) (hsup) hyb h
    exact ihn hres

end

end Work.OROneRel
