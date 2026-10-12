import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.flatPieceRTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.tFold_eigen` — the mean folds are joint eigenvectors of the slot means

`Work.BoseFixB1.tFold V A S T l Φ` (`Submission/Work/BoseFixB1/flatPieceRTDefs`) is the fold of the
*mean parts* of the `(P,Q,R)`-slot operators over the slot list `l`: at each slot `i` of `l` it
applies `oneMean V A i` (if `i ∈ S`), `id − oneMean V A i` (if `i ∈ T`), or the identity
(otherwise), and returns the resulting state.

This module proves the eigen-statement for that fold, which is the mean-half of the joint spectral
decomposition of the `(P,Q,R)`-flat pieces: for continuous `Φ` the folded state `tFold V A S T l Φ`
is continuous, lies in the range of `oneMean V A i` for every slot `i ∈ l ∩ S`, and lies in the
kernel of `oneMean V A i` for every slot `i ∈ l ∩ T`.

The proof is an induction on the slot list.  Two elementary facts about the fold are used:

* `tFold_zero` — the fold of the zero state vanishes (this collapses the last term at the slots of
  `T`, once the eigen-relation of the tail has made the state `0`);
* `tFold_singleton_comm` — the slot-`j` mean commutes with the *one-slot* fold at a different slot
  `i`.  This is the `oneMean`-calculus of `flatPieceRTDefs` applied to the three possible one-slot
  operators: `oneMean_comm_continuous` (Fubini) for `oneMean i`, this commutation together with
  `oneMean_sub_of_continuous` for `id − oneMean i`, and nothing at all for the identity.

The continuity hypothesis of `tFold_singleton_comm` is exactly what the induction supplies: the
head operator is evaluated on the tail fold, which is continuous by the induction hypothesis, and
`oneMean` of a continuous state is continuous (`continuous_oneMean`).
-/

namespace Work.BoseFixB1

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

local notation "𝔼3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases Work.BoseFixB1S

set_option maxHeartbeats 1000000

/-! ## Two elementary lemmas about `tFold` -/

/-- The fold over a cons is the *one-slot* fold at the head slot applied to the tail fold. -/
theorem tFold_cons_eq_singleton {N : ℕ} (V : ℝ) (A : Set 𝔼3) (S T : Finset (Fin N))
    (i : Fin N) (l : List (Fin N)) (Ψ : X N → ℝ) :
    tFold V A S T (i :: l) Ψ = tFold V A S T [i] (tFold V A S T l Ψ) := rfl

/-- The mean fold of the zero state vanishes. -/
theorem tFold_zero {N : ℕ} (V : ℝ) (A : Set 𝔼3) (S T : Finset (Fin N)) (l : List (Fin N)) :
    tFold V A S T l (0 : X N → ℝ) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases hiS : i ∈ S
    · rw [tFold_cons_of_mem_S V A S T hiS l 0, ih, oneMean_zero V (A := A) i]
    · by_cases hiT : i ∈ T
      · rw [tFold_cons_of_mem_T V A S T hiS hiT l 0, ih, oneMean_zero V (A := A) i, sub_self]
      · rw [tFold_cons_of_notMem V A S T hiS hiT l 0, ih]

/-- **The slot-`j` mean commutes with the one-slot fold at a different slot `i`.**  The one-slot
fold at `i` is `oneMean i`, `id − oneMean i` or the identity according to whether `i ∈ S`, `i ∈ T`
or neither, and `oneMean j` (`j ≠ i`) commutes with each of the three under the continuity
hypothesis on `f` that makes all the slot integrals integrable. -/
theorem tFold_singleton_comm {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) {A : Set 𝔼3}
    (hA : MeasurableSet A) (hAc : A ⊆ acube ℓ) (S T : Finset (Fin N))
    {i j : Fin N} (hij : i ≠ j) {f : X N → ℝ} (hf : Continuous f) :
    oneMean V A j (tFold V A S T [i] f) = tFold V A S T [i] (oneMean V A j f) := by
  by_cases hiS : i ∈ S
  · rw [tFold_cons_of_mem_S V A S T hiS [], tFold_cons_of_mem_S V A S T hiS [], tFold_nil,
      tFold_nil]
    exact oneMean_comm_continuous hℓ hA hAc (i := j) (j := i) hij.symm hf
  · by_cases hiT : i ∈ T
    · rw [tFold_cons_of_mem_T V A S T hiS hiT [], tFold_cons_of_mem_T V A S T hiS hiT [],
        tFold_nil, tFold_nil]
      rw [oneMean_sub_of_continuous hℓ hAc j hf (continuous_oneMean hℓ hA hAc i hf),
        oneMean_comm_continuous hℓ hA hAc (i := j) (j := i) hij.symm hf]
    · rw [tFold_cons_of_notMem V A S T hiS hiT [], tFold_cons_of_notMem V A S T hiS hiT [],
        tFold_nil, tFold_nil]

/-! ## The eigen-statement -/

/-- The mean fold `tFold V A S T l Φ` (the fold of the slot means `oneMean i`, `id − oneMean i`,
`id` over the slot list `l`) is a joint eigenvector of the slot means: `oneMean i (tFold l Φ) =
tFold l Φ` for `i ∈ S ∩ l`, and `= 0` for `i ∈ T ∩ l`, and it is continuous for continuous `Φ`. -/
theorem tFold_eigen {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {S T : Finset (Fin N)} (hST : Disjoint S T) (l : List (Fin N)) (hl : l.Nodup)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Continuous Φ) :
    Continuous (Work.BoseFixB1.tFold V A S T l Φ)
      ∧ (∀ i ∈ l, i ∈ S → Work.BoseFixB1S.oneMean V A i (Work.BoseFixB1.tFold V A S T l Φ)
            = Work.BoseFixB1.tFold V A S T l Φ)
      ∧ (∀ i ∈ l, i ∈ T → Work.BoseFixB1S.oneMean V A i (Work.BoseFixB1.tFold V A S T l Φ) = 0) := by
  -- disjointness of `S` and `T` in the form needed at the slots of `T`
  have hST' : ∀ i, i ∈ T → i ∉ S := fun i hi => (Finset.disjoint_right.mp hST) hi
  -- the induction: continuity of the fold and the two eigen-relations at every slot of the list
  have key : ∀ l : List (Fin N), l.Nodup →
      Continuous (tFold V A S T l Φ)
      ∧ (∀ i ∈ l, i ∈ S → oneMean V A i (tFold V A S T l Φ) = tFold V A S T l Φ)
      ∧ (∀ i ∈ l, i ∈ T → oneMean V A i (tFold V A S T l Φ) = 0) := by
    intro l
    induction l with
    | nil =>
      intro _
      exact ⟨by simpa using hΦ, fun i hi => absurd hi List.not_mem_nil,
        fun i hi => absurd hi List.not_mem_nil⟩
    | cons i l ih =>
      intro hnd
      obtain ⟨hil, hndl⟩ := List.nodup_cons.mp hnd
      obtain ⟨hcont, hS, hT⟩ := ih hndl
      refine ⟨?_, ?_, ?_⟩
      · -- continuity: the three possible head operators preserve continuity
        by_cases hiS : i ∈ S
        · rw [tFold_cons_of_mem_S V A S T hiS]
          exact continuous_oneMean hℓ hA hAc i hcont
        · by_cases hiT : i ∈ T
          · rw [tFold_cons_of_mem_T V A S T hiS hiT]
            exact hcont.sub (continuous_oneMean hℓ hA hAc i hcont)
          · rw [tFold_cons_of_notMem V A S T hiS hiT]
            exact hcont
      · -- `oneMean k (tFold l Φ) = tFold l Φ` for a slot `k ∈ l ∩ S`
        intro k hk hkS
        rcases List.mem_cons.mp hk with hki' | hkl
        · -- `k = i`: the head operator at `i ∈ S` is `oneMean i`, which is idempotent
          rw [hki'] at hkS ⊢
          rw [tFold_cons_of_mem_S V A S T hkS]
          exact oneMean_idem hVeq hV.ne' i (tFold V A S T l Φ)
        · -- `k ∈ l`, `k ≠ i`: commute the slot mean `k` out of the head operator
          have hki : k ≠ i := fun h => hil (h ▸ hkl)
          have h1 : tFold V A S T (i :: l) Φ = tFold V A S T [i] (tFold V A S T l Φ) :=
            tFold_cons_eq_singleton V A S T i l Φ
          have h2 : oneMean V A k (tFold V A S T [i] (tFold V A S T l Φ))
              = tFold V A S T [i] (oneMean V A k (tFold V A S T l Φ)) :=
            tFold_singleton_comm hℓ hA hAc S T hki.symm hcont
          calc oneMean V A k (tFold V A S T (i :: l) Φ)
              = oneMean V A k (tFold V A S T [i] (tFold V A S T l Φ)) :=
                congrArg (fun g => oneMean V A k g) h1
            _ = tFold V A S T [i] (oneMean V A k (tFold V A S T l Φ)) := h2
            _ = tFold V A S T [i] (tFold V A S T l Φ) := by rw [hS k hkl hkS]
            _ = tFold V A S T (i :: l) Φ := h1.symm
      · -- `oneMean k (tFold l Φ) = 0` for a slot `k ∈ l ∩ T`
        intro k hk hkT
        rcases List.mem_cons.mp hk with hki' | hkl
        · -- `k = i`: the head operator at `i ∈ T` is `id − oneMean i`, killed by `oneMean i`
          rw [hki'] at hkT ⊢
          rw [tFold_cons_of_mem_T V A S T (hST' i hkT) hkT,
            oneMean_sub_of_continuous hℓ hAc i hcont (continuous_oneMean hℓ hA hAc i hcont),
            oneMean_idem hVeq hV.ne' i (tFold V A S T l Φ), sub_self]
        · -- `k ∈ l`, `k ≠ i`: commute the slot mean `k` out of the head operator
          have hki : k ≠ i := fun h => hil (h ▸ hkl)
          have h1 : tFold V A S T (i :: l) Φ = tFold V A S T [i] (tFold V A S T l Φ) :=
            tFold_cons_eq_singleton V A S T i l Φ
          have h2 : oneMean V A k (tFold V A S T [i] (tFold V A S T l Φ))
              = tFold V A S T [i] (oneMean V A k (tFold V A S T l Φ)) :=
            tFold_singleton_comm hℓ hA hAc S T hki.symm hcont
          calc oneMean V A k (tFold V A S T (i :: l) Φ)
              = oneMean V A k (tFold V A S T [i] (tFold V A S T l Φ)) :=
                congrArg (fun g => oneMean V A k g) h1
            _ = tFold V A S T [i] (oneMean V A k (tFold V A S T l Φ)) := h2
            _ = tFold V A S T [i] (0 : X N → ℝ) := by rw [hT k hkl hkT]
            _ = 0 := tFold_zero V A S T [i]
  exact key l hl

end

end Work.BoseFixB1
