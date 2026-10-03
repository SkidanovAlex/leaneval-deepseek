import Mathlib
import Submission.Work.Peluse.UControl.HistInit

/-!
# The weight vector of a history state, and of its symbolic companion after one step

Peluse's weight vector `V j` (`Definition 4.3`) is attached to a history state `X : HistData d n`
by `HistData.weightH X j`, which is *defined* as the weight of the symbolic companion `X.toSym`
(`histWeightEq` is then `rfl`).

This file proves the **step** version: the weight of `X.step i₀ h₀ hh` (the history-indexed PET
step, which drops the constant slots, removes the `(i₀, false)` continuation and appends the new
Boolean parameter) agrees at every coordinate `j ≥ 1` with the weight of the *symbolic* PET step
`X.toSym.S.step ⟨(i₀,h₀),hh⟩` applied to the companion of `X`.

The mathematical content is a bijection of slot sets.  A slot of the sym-step is a pair
`((j, h), ε)` (a live slot `(j,h) ∈ X.H` together with the value of the new parameter), and it
corresponds to the slot `(j, Fin.snoc h ε)` of the history step; on this bijection the two slot
polynomials are the *same* term.  The two slot sets are not literally equal: the symbolic step
keeps the slots whose polynomial has degree `0` (`PetStateSym.step` has no access to the notion of
a "constant slot"), while `HistData.stepH` drops them.  Those dropped slots all have degree `0`,
so they are irrelevant at every coordinate `j ≥ 1` — which is exactly the hypothesis
`hj : 1 ≤ (j : ℕ)` of `histWeightStepEq`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

open Polynomial

variable {d n : ℕ}

noncomputable section

/-! ## A cardinality lemma for image-filters -/

/-- If `P : α → Prop` and `Q : β → Prop` correspond along a map `e : α → β` that is surjective onto
`{b // Q b}`, and if `f` and `g` correspond along `e`, then the images of the two filtered
universes have the same cardinality.  (The image sets are in fact equal.)  Only the forward
correspondence and the surjectivity are needed; no injectivity of `e` is required. -/
lemma card_image_filter_congr {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    {e : α → β} {f : α → γ} {g : β → γ} {P : α → Prop} {Q : β → Prop}
    [DecidablePred P] [DecidablePred Q] (hPQ : ∀ a, P a ↔ Q (e a)) (hfg : ∀ a, f a = g (e a))
    (hsurj : ∀ b, Q b → ∃ a, P a ∧ e a = b) :
    (((Finset.univ : Finset α).filter P).image f).card
      = (((Finset.univ : Finset β).filter Q).image g).card := by
  have hset : ((Finset.univ : Finset α).filter P).image f
      = ((Finset.univ : Finset β).filter Q).image g := by
    apply Finset.ext
    intro c
    rw [Finset.mem_image, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨e a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hPQ a).mp (Finset.mem_filter.mp ha).2⟩,
        (hfg a).symm⟩
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨a, hPa, rfl⟩ := hsurj b (Finset.mem_filter.mp hb).2
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPa⟩, hfg a⟩
  rw [hset]

/-! ## The slot bijection between the history step and the symbolic step -/

/-- The map from the slots of the history step `X.step i₀ h₀ hh` to the slots of the symbolic step
`X.toSym.S.step ⟨(i₀,h₀),hh⟩`: a slot `(j, h')` is sent to the pair `((j, Fin.init h'), h' (last))`
— i.e. its parent slot together with the value of the Boolean parameter that produced it. -/
def HistData.stepIdx (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) :
    ((X.step i₀ h₀ hh).toSym).S.ι → ((X.toSym).S.step ⟨(i₀, h₀), hh⟩).ι :=
  fun x => ⟨(⟨(x.1.1, Fin.init x.1.2), by
      have hx : x.1 ∈ X.stepH i₀ h₀ := x.2
      rw [HistData.stepH, Finset.mem_filter] at hx
      exact hx.2.1⟩, x.1.2 (Fin.last n)), by
    intro hEq
    have hx : x.1 ∈ X.stepH i₀ h₀ := x.2
    rw [HistData.stepH, Finset.mem_filter] at hx
    apply hx.2.2.1
    have hlast : x.1.2 (Fin.last n) = false := congrArg Prod.snd hEq
    have hinit : Fin.init x.1.2 = h₀ := by
      have := congrArg (fun z => (z.1 : X.toSym.S.ι).1.2) hEq
      simpa using this
    have hfst : x.1.1 = i₀ := by
      have := congrArg (fun z => (z.1 : X.toSym.S.ι).1.1) hEq
      simpa using this
    have hsnd : x.1.2 = Fin.snoc h₀ false := by
      have hself := Fin.snoc_init_self (q := x.1.2)
      rw [hinit, hlast] at hself
      exact hself.symm
    exact Prod.ext hfst hsnd⟩

/-- On the bijection `stepIdx`, the slot polynomials of the history step and of the symbolic step
are the *same* term. -/
lemma HistData.stepIdx_P (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) (x : ((X.step i₀ h₀ hh).toSym).S.ι) :
    ((X.toSym).S.step ⟨(i₀, h₀), hh⟩).P (X.stepIdx i₀ h₀ hh x) = X.stepQ i₀ h₀ x.1.1 x.1.2 := by
  simp only [HistData.stepIdx, PetStep.PetStateSym.step, HistData.stepQ, HistData.toSym]
  rfl

/-- The first component of the image of a slot under `stepIdx`. -/
lemma HistData.stepIdx_fst (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) (x : ((X.step i₀ h₀ hh).toSym).S.ι) :
    (X.stepIdx i₀ h₀ hh x).1.1.1 = (x.1.1, Fin.init x.1.2) := rfl

/-- The second component of the image of a slot under `stepIdx`. -/
lemma HistData.stepIdx_snd (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) (x : ((X.step i₀ h₀ hh).toSym).S.ι) :
    (X.stepIdx i₀ h₀ hh x).1.2 = x.1.2 (Fin.last n) := rfl

/-- **Surjectivity of the slot bijection at a coordinate `j ≥ 1`.**  Every slot of the symbolic step
whose polynomial has degree `j ≥ 1` is the image under `stepIdx` of a slot of the history step
(necessarily of degree `j` as well): the symbolic step keeps the slots of degree `0`, which the
history step drops, and those are exactly the ones excluded by `1 ≤ j`. -/
lemma HistData.stepIdx_surj (X : HistData d n) (i₀ : InitIdx d) (h₀ : Fin n → Bool)
    (hh : (i₀, h₀) ∈ X.H) {j : Fin (d + 1)} (hj : 1 ≤ (j : ℕ))
    (b : ((X.toSym).S.step ⟨(i₀, h₀), hh⟩).ι)
    (hb : (((X.toSym).S.step ⟨(i₀, h₀), hh⟩).P b).natDegree = (j : ℕ)) :
    ∃ a : ((X.step i₀ h₀ hh).toSym).S.ι,
      (X.stepQ i₀ h₀ a.1.1 a.1.2).natDegree = (j : ℕ) ∧ X.stepIdx i₀ h₀ hh a = b := by
  obtain ⟨⟨⟨⟨a₀, h₀'⟩, hmem⟩, ε⟩, hne⟩ := b
  have hPb : X.stepQ i₀ h₀ a₀ (Fin.snoc h₀' ε) = ((X.toSym).S.step ⟨(i₀, h₀), hh⟩).P
      ⟨(⟨(a₀, h₀'), hmem⟩, ε), hne⟩ := by
    simp only [HistData.stepQ, PetStep.PetStateSym.step, HistData.toSym, Fin.init_snoc,
      Fin.snoc_last]
  have h1deg : (X.stepQ i₀ h₀ a₀ (Fin.snoc h₀' ε)).natDegree = (j : ℕ) := by
    rw [hPb]
    exact hb
  have hdeg : 1 ≤ (X.stepQ i₀ h₀ a₀ (Fin.snoc h₀' ε)).natDegree := by
    omega
  have hmem' : (a₀, Fin.snoc h₀' ε) ∈ X.stepH i₀ h₀ := by
    rw [HistData.stepH, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_, hdeg⟩
    · rw [Fin.init_snoc]
      exact hmem
    · intro heq
      apply hne
      have h1 : a₀ = i₀ := (Prod.ext_iff.mp heq).1
      have h3a : h₀' = h₀ := by
        have := congrArg (fun z : InitIdx d × (Fin (n + 1) → Bool) => Fin.init z.2) heq
        simpa using this
      have h3b : ε = false := by
        have := congrArg (fun z : InitIdx d × (Fin (n + 1) → Bool) => z.2 (Fin.last n)) heq
        simpa using this
      exact Prod.ext (Subtype.ext (Prod.ext h1 h3a)) h3b
  refine ⟨⟨(a₀, Fin.snoc h₀' ε), hmem'⟩, h1deg, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    simp only [HistData.stepIdx, Fin.init_snoc]
  · simp only [HistData.stepIdx, Fin.snoc_last]

/-! ## The step identity for the weight vector -/

theorem histWeightStepEq {d n : ℕ} (X : Work.Peluse.UControl.HistData d n) (i₀ : Work.Peluse.UControl.InitIdx d) (h₀ : Fin n → Bool) (hh : (i₀, h₀) ∈ X.H) (j : Fin (d + 1)) (hj : 1 ≤ (j : ℕ)) : ((X.step i₀ h₀ hh).weightH j) = (((X.toSym).S.step ⟨(i₀, h₀), hh⟩).weight d j) := by
  simp only [HistData.weightH, HistData.toSym, HistData.step, PetStep.PetStateSym.weight]
  refine card_image_filter_congr (e := X.stepIdx i₀ h₀ hh)
    (f := fun i => (X.stepQ i₀ h₀ i.1.1 i.1.2).leadingCoeff)
    (g := fun i => (((X.toSym).S.step ⟨(i₀, h₀), hh⟩).P i).leadingCoeff)
    (P := fun i => (X.stepQ i₀ h₀ i.1.1 i.1.2).natDegree = (j : ℕ))
    (Q := fun i => (((X.toSym).S.step ⟨(i₀, h₀), hh⟩).P i).natDegree = (j : ℕ)) ?_ ?_ ?_
  · intro a
    rw [HistData.stepIdx_P]
    exact Iff.rfl
  · intro a
    exact (congrArg Polynomial.leadingCoeff (HistData.stepIdx_P X i₀ h₀ hh a)).symm
  · intro b hb
    exact X.stepIdx_surj i₀ h₀ hh hj b hb

end

end Work.Peluse.UControl
