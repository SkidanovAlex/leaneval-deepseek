import Mathlib
import Submission.Work.Peluse.UControl.card_I
import Submission.Work.Peluse.Ulower.Defs
import Submission.Work.Prop36SW.boxNorm_famIdx_le_of_le

/-!
# The extended index datum: adjoining two fresh slots at every level

When `Fintype.card (D.I (d-1)) ≤ 1` the top slot set `D.S (d-1)` has at most one element, so
Peluse's family `I_{d-1}` (the nonempty subsets of `D.S (d-1)`) has at most one member, and the §5
chain's entry — which needs the level-`1` window enlargement `H → H+1`, valid only at level `≥ 2`
— is unavailable.

The remedy is to *enlarge* the index datum: `extDatum D` is `D` with two fresh slots adjoined at
every level, `(extDatum D).S j = D.S j ⊕ Fin 2`.  Then every level has at least two slots, so
`Fintype.card ((extDatum D).I j) ≥ 3`, the chain applies to `extDatum D`, and the old datum sits
inside it through `Sum.inl` (`extIdx`), with the direction polynomials agreeing
(`dir_extDatum`).  The family average of `extDatum D` dominates that of `D` because the level-`S`
box norm dominates (a power of) the level-`1` box norm at any one of its directions
(`Work.Prop36SW.boxNormPow_level_raise_uniform`).

This file holds the construction and the direction identity; the comparison of the family averages
is in `Submission/Work/Peluse/Prop36SW/degenerateBranch.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse

noncomputable section

open Work.Peluse.UControl

/-- `extDatum D` is `D` with two fresh slots adjoined at every level: `(extDatum D).S j = D.S j ⊕ Fin 2`.
An old slot `s` is `Sum.inl s`, and the parent of `Sum.inl s` is the `Sum.inl`-image of the parent of
`s`; both fresh slots have the parent `{Sum.inr 0}`. -/
abbrev extDatum (D : IdxDatum) : IdxDatum where
  S := fun j => D.S j ⊕ Fin 2
  finS := fun _ => inferInstance
  decS := fun _ => inferInstance
  par := fun j s => s.elim
    (fun t => ⟨(D.par j t).1.image Sum.inl, Finset.image_nonempty.mpr (D.par j t).2⟩)
    (fun _ => ⟨{Sum.inr (0 : Fin 2)}, Finset.singleton_nonempty _⟩)

@[simp] lemma extDatum_S (D : IdxDatum) (j : ℕ) :
    (extDatum D).S j = (D.S j ⊕ Fin 2) := rfl

/-- The old slot `s`, seen in the extended datum. -/
abbrev extSlot (D : IdxDatum) (j : ℕ) (s : D.S j) : (extDatum D).S j := Sum.inl s

/-- The old index (nonempty subset) `ω`, seen in the extended datum. -/
def extIdx (D : IdxDatum) (j : ℕ) (ω : D.I j) : (extDatum D).I j :=
  ⟨ω.1.image Sum.inl, Finset.image_nonempty.mpr ω.2⟩

@[simp] lemma extIdx_val (D : IdxDatum) (j : ℕ) (ω : D.I j) :
    (extIdx D j ω).1 = ω.1.image Sum.inl := rfl

@[simp] lemma extDatum_par_inl (D : IdxDatum) (j : ℕ) (s : D.S (j + 1)) :
    (extDatum D).par j (Sum.inl s) = extIdx D j (D.par j s) := rfl

/-- The parameter family `b` of `extDatum D` extends the parameter family `a` of `D`. -/
def Matches (D : IdxDatum) (a : (j : ℕ) → D.S j → ℤ) (b : (j : ℕ) → (extDatum D).S j → ℤ) : Prop :=
  ∀ j s, b j (Sum.inl s) = a j s

/-- **The direction polynomials of the extended datum agree with those of `D`** on the old indices
and matching parameters. -/
theorem dir_extDatum (D : IdxDatum) (d : ℕ) (c : ℤ) :
    ∀ (j : ℕ) (ω : D.I j) (a : (j : ℕ) → D.S j → ℤ) (b : (j : ℕ) → (extDatum D).S j → ℤ),
      Matches D a b → (extDatum D).dir d c j (extIdx D j ω) b = D.dir d c j ω a := by
  intro j
  induction j with
  | zero => intro ω a b _; rfl
  | succ j ih =>
    intro ω a b h
    rw [IdxDatum.dir, extIdx_val, Finset.sum_image (g := Sum.inl)]
    · refine Finset.sum_congr rfl fun s _ => ?_
      rw [extDatum_par_inl, ih (D.par j s) a b h, h (j + 1) s]
    · intro x _ y _ hxy
      exact Sum.inl.inj hxy

/-- The family index of the extended datum has `2 ^ (|S j| + 2) - 1` elements, hence at least `3`. -/
theorem card_extS (D : IdxDatum) (j : ℕ) :
    Fintype.card ((extDatum D).S j) = Fintype.card (D.S j) + 2 := by
  show Fintype.card (D.S j ⊕ Fin 2) = Fintype.card (D.S j) + 2
  rw [Fintype.card_sum, Fintype.card_fin]

theorem card_extI (D : IdxDatum) (j : ℕ) :
    Fintype.card ((extDatum D).I j) = 2 ^ (Fintype.card (D.S j) + 2) - 1 := by
  rw [card_I, card_extS]

theorem three_le_card_extI (D : IdxDatum) (j : ℕ) : 3 ≤ Fintype.card ((extDatum D).I j) := by
  rw [card_extI]
  have : 0 ≤ Fintype.card (D.S j) := Nat.zero_le _
  have h2 : 2 ^ (0 + 2) ≤ 2 ^ (Fintype.card (D.S j) + 2) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem two_le_card_extI' (D : IdxDatum) (j : ℕ) : 2 ≤ Fintype.card ((extDatum D).I j) :=
  le_trans (by norm_num) (three_le_card_extI D j)

end

end Work.Peluse

namespace Work.Peluse

noncomputable section

open Work.Peluse.UControl

/-- The old coordinates of an extended parameter family. -/
def oldPart (D : IdxDatum) {l : ℕ} (β : (extDatum D).Idx l) : D.Idx l :=
  fun j s => β j (Sum.inl s)

/-- The new (fresh-slot) coordinates of an extended parameter family. -/
def newPart (D : IdxDatum) {l : ℕ} (β : (extDatum D).Idx l) : Fin l × Fin 2 → ℤ :=
  fun p => β p.1 (Sum.inr p.2)

/-- Assemble an extended parameter family from old and new coordinates. -/
def mkIdx (D : IdxDatum) {l : ℕ} (a : D.Idx l) (c : Fin l × Fin 2 → ℤ) : (extDatum D).Idx l :=
  fun j s => s.elim (fun t => a j t) (fun k => c (j, k))

@[simp] lemma oldPart_mkIdx (D : IdxDatum) {l : ℕ} (a : D.Idx l) (c : Fin l × Fin 2 → ℤ) :
    oldPart D (mkIdx D a c) = a := rfl

@[simp] lemma newPart_mkIdx (D : IdxDatum) {l : ℕ} (a : D.Idx l) (c : Fin l × Fin 2 → ℤ) :
    newPart D (mkIdx D a c) = c := by
  funext p; rfl

@[simp] lemma mkIdx_oldPart (D : IdxDatum) {l : ℕ} (β : (extDatum D).Idx l) :
    mkIdx D (oldPart D β) (newPart D β) = β := by
  funext j s; cases s with
  | inl t => rfl
  | inr k => rfl

lemma mkIdx_inj (D : IdxDatum) {l : ℕ} {a a' : D.Idx l} {c c' : Fin l × Fin 2 → ℤ}
    (h : mkIdx D a c = mkIdx D a' c') : a = a' ∧ c = c' :=
  ⟨by rw [← oldPart_mkIdx D a c, h, oldPart_mkIdx], by rw [← newPart_mkIdx D a c, h, newPart_mkIdx]⟩

/-- The box of the fresh coordinates. -/
def newBox (l H : ℕ) : Finset (Fin l × Fin 2 → ℤ) :=
  Fintype.piFinset (fun _ : Fin l × Fin 2 => Finset.Icc (-(H : ℤ)) (H : ℤ))

lemma mem_newBox {l H : ℕ} {c : Fin l × Fin 2 → ℤ} :
    c ∈ newBox l H ↔ ∀ p, -(H : ℤ) ≤ c p ∧ c p ≤ (H : ℤ) := by
  rw [newBox, Fintype.mem_piFinset]
  exact ⟨fun h p => Finset.mem_Icc.mp (h p), fun h p => Finset.mem_Icc.mpr (h p)⟩

/-- **The parameter box of the extended datum is the product of the old box and the fresh box.** -/
theorem mem_extParBox_iff (D : IdxDatum) (l H : ℕ) (β : (extDatum D).Idx l) :
    β ∈ (extDatum D).parBox l H ↔ oldPart D β ∈ D.parBox l H ∧ newPart D β ∈ newBox l H := by
  constructor
  · intro h
    rw [IdxDatum.mem_parBox] at h
    constructor
    · rw [IdxDatum.mem_parBox]
      intro j s
      exact h j (Sum.inl s)
    · rw [mem_newBox]
      intro p
      exact h p.1 (Sum.inr p.2)
  · rintro ⟨h1, h2⟩
    rw [IdxDatum.mem_parBox] at h1
    rw [mem_newBox] at h2
    rw [IdxDatum.mem_parBox]
    intro j s
    cases s with
    | inl t => exact h1 j t
    | inr k => exact h2 (j, k)

theorem extParBox_eq_image (D : IdxDatum) (l H : ℕ) :
    (extDatum D).parBox l H
      = ((D.parBox l H) ×ˢ newBox l H).image (fun p : D.Idx l × (Fin l × Fin 2 → ℤ) =>
          mkIdx D p.1 p.2) := by
  ext β
  rw [Finset.mem_image]
  constructor
  · intro h
    refine ⟨(oldPart D β, newPart D β), ?_, mkIdx_oldPart D β⟩
    rw [Finset.mem_product]
    exact (mem_extParBox_iff D l H β).mp h
  · rintro ⟨p, hp, rfl⟩
    rw [Finset.mem_product] at hp
    exact (mem_extParBox_iff D l H (mkIdx D p.1 p.2)).mpr ⟨hp.1, hp.2⟩

theorem card_extParBox (D : IdxDatum) (l H : ℕ) :
    ((extDatum D).parBox l H).card = (D.parBox l H).card * (newBox l H).card := by
  rw [extParBox_eq_image]
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_product _ _
  · intro x _ y _ hxy
    exact Prod.ext (mkIdx_inj D hxy).1 (mkIdx_inj D hxy).2

theorem sum_extParBox (D : IdxDatum) (l H : ℕ) (F : (extDatum D).Idx l → ℝ) :
    ∑ β ∈ (extDatum D).parBox l H, F β
      = ∑ p ∈ (D.parBox l H) ×ˢ newBox l H, F (mkIdx D p.1 p.2) := by
  rw [extParBox_eq_image]
  refine Finset.sum_image ?_
  intro x _ y _ hxy
  exact Prod.ext (mkIdx_inj D hxy).1 (mkIdx_inj D hxy).2

end

end Work.Peluse
