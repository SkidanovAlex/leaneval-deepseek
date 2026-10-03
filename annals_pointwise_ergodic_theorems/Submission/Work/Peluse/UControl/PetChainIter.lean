import Mathlib
import Submission.Work.Peluse.UControl.petSymWeight
import Submission.Work.Peluse.UControl.petSymDropWeight
import Submission.Work.Peluse.UControl.petChainWF

/-!
# The PET chain, as a well-founded recursion on the symbolic states

`Work.Peluse.UControl.petChapter5Holds` needs the PET chain of Peluse's §4 (her Lemmas 4.7/4.8):
starting from the state of `LambdaMD`, iterate the PET step at a suitably chosen slot until all the
slot polynomials are *linear* in `y`; the terminal state's slot polynomials are then the datum's
direction family `A_{d-1}` and the terminal correlation is the average `linFamAvg` of the target.

This file builds the *combinatorial* half of that chain, on the symbolic states `PetStateSym k`
(polynomials over `MvPolynomial (Fin k) ℤ`, so that the degrees and leading coefficients are the
*generic* ones of Peluse's §4 — see `NOTES_petChapter5.md` §10):

* `SymState d` — a symbolic state together with the bound `d` on the degrees of its slots;
* `consts`, `dropC` — Peluse's `J_k = (J_{k-1}\{deg 0})×{0,1}\{…}`: the constant (in `y`) slots
  are dropped before each step (they are absorbed into the base function), because otherwise a
  constant slot `c` produces the new slot `c - Q_{i₀}` of degree `deg Q_{i₀}`, which can *replace*
  the leading coefficient that `i₀` loses and destroy the weight decrease (the trap of
  `NOTES_petChapter5.md` §8);
* `stepMin` — the PET step at a slot of least nonzero degree (Peluse's Lemma 4.4);
* `stepMin_lt`/`stepMin_lt_full` — the weight-vector strictly decreases, so the recursion
  terminates (`petChainWF`);  the point of `petLt_dropC` is that the decrease on the *dropped* state
  lifts to the original state, because the dropped state has no slot of degree `0`, so its weight at
  the coordinate `0` vanishes and the witness of `petLt` must sit at a coordinate `≥ 1`, where
  `petSymDropWeight` identifies the two weight vectors;
* `chain`/`chain_linear` — the recursion itself, and the fact that it stops only in a *linear*
  state.

The remaining obligations (see `NOTES_petChapter5_session12.md` §4) are the analytic chain
(`PetState.lam_step` applied along the same choices), the identification of the terminal directions
with the datum's `petDir`, and the striking fact that the number of steps and the terminal structure
depend only on `P` — which is what makes the target's `K ≤ K₀`, `Cst₀ ≤ Cst₁` (both produced before
the scale constant `A`) satisfiable.
-/

set_option autoImplicit false
open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace Work.Peluse.UControl

open Work.Peluse.UControl.PetStep

noncomputable section

/-- A symbolic PET state together with a bound on the degrees of its slot polynomials.  The bound is
the `d` of `PetChapter5` (the degree of the polynomial `P`), kept fixed along the chain. -/
structure SymState (d : ℕ) where
  nv : ℕ
  S : PetStateSym nv
  hd : ∀ i, (S.P i).natDegree ≤ d

namespace SymState

variable {d : ℕ}

/-- The slots whose shift is constant in `y`. -/
def consts (X : SymState d) : Finset X.S.ι :=
  Finset.univ.filter (fun i => (X.S.P i).natDegree = 0)

lemma mem_consts {X : SymState d} {i : X.S.ι} :
    i ∈ consts X ↔ (X.S.P i).natDegree = 0 := by
  simp [consts]

/-- The same state with the constant slots removed (the slots of `J_k` are absorbed into the base
function, which is why they must not take part in the PET step). -/
def dropC (X : SymState d) : SymState d where
  nv := X.nv
  S := PetStateSym.dropSym X.S (consts X)
  hd := fun i => X.hd i.1

lemma dropC_nc (X : SymState d) : ∀ i, 1 ≤ ((dropC X).S.P i).natDegree := by
  intro i
  have h : (X.S.P i.1).natDegree ≠ 0 :=
    fun h0 => (Finset.mem_compl.mp i.2) (mem_consts.mpr h0)
  have hd := X.hd i.1
  show 1 ≤ (X.S.P i.1).natDegree
  omega

/-- In a state without constant slots the weight vector vanishes at the coordinate `0`. -/
lemma weight_zero {k : ℕ} (Y : PetStateSym k) (hY : ∀ i, 1 ≤ (Y.P i).natDegree) (dd : ℕ) :
    Y.weight dd ⟨0, Nat.succ_pos dd⟩ = 0 := by
  rw [PetStateSym.weight, Finset.card_eq_zero, Finset.image_eq_empty]
  rw [Finset.filter_eq_empty_iff]
  intro i _ hi
  have := hY i
  simp only [Fin.val_zero] at hi
  omega

/-- A state is *linear* when every slot polynomial has degree at most `1` (this is the stopping
condition of the chain: Peluse's Lemma 4.9 terminates at the linear configuration). -/
def IsLinear (X : SymState d) : Prop := ∀ i, (X.S.P i).natDegree ≤ 1

/-- If the state is not linear then it has a nonconstant slot, so the state of the next step is
nonempty. -/
lemma dropC_nonempty (X : SymState d) (h : ¬ IsLinear X) :
    (Finset.univ : Finset (dropC X).S.ι).Nonempty := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp h
  have h2 : 2 ≤ (X.S.P i).natDegree := by omega
  refine ⟨⟨i, ?_⟩, Finset.mem_univ _⟩
  rw [Finset.mem_compl]
  intro hc
  have hc' := mem_consts.mp hc
  omega

/-- A slot of least degree in the dropped state. -/
noncomputable def minSlot (X : SymState d)
    (hE : (Finset.univ : Finset (dropC X).S.ι).Nonempty) : (dropC X).S.ι :=
  Classical.choose (Finset.exists_min_image (Finset.univ : Finset (dropC X).S.ι)
    (fun i => ((dropC X).S.P i).natDegree) hE)

lemma minSlot_le (X : SymState d) (hE : (Finset.univ : Finset (dropC X).S.ι).Nonempty)
    (i : (dropC X).S.ι) :
    ((dropC X).S.P (minSlot X hE)).natDegree ≤ ((dropC X).S.P i).natDegree :=
  (Classical.choose_spec (Finset.exists_min_image (Finset.univ : Finset (dropC X).S.ι)
    (fun i => ((dropC X).S.P i).natDegree) hE)).2 i (Finset.mem_univ i)

end SymState

/-! ## The degree bound is preserved by the step -/

lemma step_natDegree_le {k : ℕ} (Y : PetStateSym k) (i₀ : Y.ι) {d : ℕ}
    (hd : ∀ i, (Y.P i).natDegree ≤ d) (j : (Y.step i₀).ι) :
    ((Y.step i₀).P j).natDegree ≤ d := by
  have hmap1 : ((Y.P j.1.1).map (MvPolynomial.rename Fin.castSucc).toRingHom).natDegree ≤ d :=
    le_trans Polynomial.natDegree_map_le (hd j.1.1)
  have hmap2 : ((Y.P i₀).map (MvPolynomial.rename Fin.castSucc).toRingHom).natDegree ≤ d :=
    le_trans Polynomial.natDegree_map_le (hd i₀)
  let tt : Polynomial (MvPolynomial (Fin (k + 1)) ℤ) :=
    Polynomial.X + Polynomial.C (if j.1.2 then MvPolynomial.X (Fin.last k) else 0)
  have htt : tt.natDegree = 1 := Polynomial.natDegree_X_add_C _
  have hcomp : (((Y.P j.1.1).map (MvPolynomial.rename Fin.castSucc).toRingHom).comp tt).natDegree
        ≤ d := by
    refine le_trans Polynomial.natDegree_comp_le ?_
    rw [htt, mul_one]
    exact hmap1
  show (((Y.P j.1.1).map (MvPolynomial.rename Fin.castSucc).toRingHom).comp tt
      - (Y.P i₀).map (MvPolynomial.rename Fin.castSucc).toRingHom).natDegree ≤ d
  exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le hcomp hmap2)

/-! ## The PET step at a slot of least degree -/

namespace SymState

variable {d : ℕ}

/-- The PET step at a slot of least degree: drop the constant slots, then step. -/
noncomputable def stepMin (X : SymState d)
    (hE : (Finset.univ : Finset (dropC X).S.ι).Nonempty) : SymState d where
  nv := X.nv + 1
  S := (dropC X).S.step (minSlot X hE)
  hd := fun j => step_natDegree_le (dropC X).S (minSlot X hE) (dropC X).hd j

/-- The weight vector decreases at the coordinate of the least degree (`petSymWeight`). -/
theorem stepMin_lt (X : SymState d) (hE : (Finset.univ : Finset (dropC X).S.ι).Nonempty) :
    petLt (((dropC X).S.step (minSlot X hE)).weight d) ((dropC X).S.weight d) :=
  petSymWeight (dropC X).S (minSlot X hE) (dropC_nc X) (dropC X).hd
    (fun i _ => minSlot_le X hE i) rfl

/-- The weight vector of the dropped state and that of the original state agree above the coordinate
`0`. -/
lemma dropC_weight_eq {X : SymState d} {j : Fin (d + 1)} (hj : 1 ≤ (j : ℕ)) :
    (dropC X).S.weight d j = X.S.weight d j := by
  obtain ⟨n, hn⟩ := j
  have hjd : n ≤ d := Nat.lt_succ_iff.mp hn
  have h := petSymDropWeight X.S (consts X) (fun i hi => mem_consts.mp hi) hj hjd
  rw [show (⟨n, hn⟩ : Fin (d + 1)) = ⟨n, Nat.lt_succ_of_le hjd⟩ from Fin.ext rfl]
  exact h

/-- **Lifting the decrease through the dropping of the constants.**  If the weight vector of `W`
is strictly below that of the dropped state `dropC X`, then it is strictly below that of `X`: the
dropped state has no coordinates of degree `0` occupied, so the witness of `petLt` cannot sit at the
coordinate `0`, and above it the two weight vectors agree (`dropC_weight_eq`). -/
theorem petLt_dropC {X : SymState d} {W : Fin (d + 1) → ℕ}
    (h0 : (dropC X).S.weight d ⟨0, Nat.succ_pos d⟩ = 0)
    (h : petLt W ((dropC X).S.weight d)) : petLt W (X.S.weight d) := by
  obtain ⟨j, hj, hjk⟩ := h
  have hj1 : 1 ≤ (j : ℕ) := by
    rcases Nat.eq_zero_or_pos (j : ℕ) with hz | hpos
    · exfalso
      have hji : j = ⟨0, Nat.succ_pos d⟩ := Fin.ext hz
      rw [hji, h0] at hj
      omega
    · exact hpos
  refine ⟨j, ?_, ?_⟩
  · rw [← dropC_weight_eq (X := X) hj1]; exact hj
  · intro m hm
    rw [← dropC_weight_eq (X := X) (j := m) (by omega)]
    exact hjk m hm

/-- The chain step strictly lowers the weight vector of the *original* state, so the recursion
below terminates. -/
theorem stepMin_lt_full (X : SymState d) (hE : (Finset.univ : Finset (dropC X).S.ι).Nonempty) :
    petLt ((stepMin X hE).S.weight d) (X.S.weight d) :=
  petLt_dropC (SymState.weight_zero (dropC X).S (dropC_nc X) d) (stepMin_lt X hE)

end SymState

/-! ## The recursion -/

/-- The relation of the well-founded recursion: the weight vector strictly decreases. -/
def petRel (d : ℕ) : SymState d → SymState d → Prop :=
  fun Y X => petLt (Y.S.weight d) (X.S.weight d)

lemma petRel_wf (d : ℕ) : WellFounded (petRel d) :=
  InvImage.wf (fun X : SymState d => X.S.weight d) (petChainWF d)

namespace SymState

variable {d : ℕ}

/-- The body of the recursion: stop when the state is linear, otherwise step at a slot of least
degree. -/
noncomputable def chainF (d : ℕ) :
    (X : SymState d) → ((Y : SymState d) → petRel d Y X → SymState d) → SymState d :=
  fun X rec => if h : IsLinear X then X
    else rec (stepMin X (dropC_nonempty X h)) (stepMin_lt_full X (dropC_nonempty X h))

/-- **The PET chain**: iterate the step at a slot of least degree until the state is linear. -/
noncomputable def chain (d : ℕ) (X : SymState d) : SymState d :=
  WellFounded.fix (petRel_wf d) (chainF d) X

lemma chain_unfold (d : ℕ) (X : SymState d) :
    chain d X = chainF d X (fun Y _ => chain d Y) := by
  show WellFounded.fix (petRel_wf d) (chainF d) X = _
  rw [WellFounded.fix_eq]
  rfl

/-- The chain does nothing at a linear state. -/
lemma chain_eq_of (X : SymState d) (h : IsLinear X) : chain d X = X := by
  rw [chain_unfold]
  unfold chainF
  exact dif_pos h

/-- Outside the linear states the chain takes one PET step at a slot of least degree. -/
lemma chain_eq_not (X : SymState d) (h : ¬ IsLinear X) :
    chain d X = chain d (stepMin X (dropC_nonempty X h)) := by
  rw [chain_unfold]
  unfold chainF
  rw [dif_neg h]

/-- **The chain stops only in a linear state.** -/
theorem chain_linear (d : ℕ) (X : SymState d) : IsLinear (chain d X) := by
  induction X using WellFounded.induction (petRel_wf d) with
  | h X ih =>
    by_cases h : IsLinear X
    · rw [chain_eq_of X h]; exact h
    · rw [chain_eq_not X h]
      exact ih _ (stepMin_lt_full X (dropC_nonempty X h))

end SymState

end

end Work.Peluse.UControl
