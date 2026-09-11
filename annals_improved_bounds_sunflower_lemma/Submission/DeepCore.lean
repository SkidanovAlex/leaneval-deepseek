import Mathlib
import Submission.SunBasic
import Submission.Chi
import Submission.Deep

/-!
# The encoding (fixed-U step) for the petal estimate

We prove `fixed_U_step` from `Deep.lean` by a two-case encoding argument.
This file is under construction.
-/
open Finset
open scoped BigOperators
open Real

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-- candidate `X`-sets: members `A'` with `C ⊆ χ(A',U) ⊆ B` and `|χ(A',U)| = s` -/
noncomputable def tau (S : Finset (Finset α)) (U : Finset α) (C B : Finset α) (s : ℕ) : Finset (Finset α) :=
  S.filter (fun A' : Finset α => C ⊆ chi S U A' ∧ chi S U A' ⊆ B ∧ (chi S U A').card = s)

/-- the `φ` bound -/
noncomputable def phi (r : ℝ) (k : ℕ) (n v s t : ℕ) : ℝ :=
  (r ^ k) * ((rho * (v : ℝ) / (n : ℝ)) ^ s) / (((v : ℝ) * r / (n : ℝ)) ^ t)

/-- canonical `t`-subset of a set of size `s` (chosen by choice). -/
noncomputable def pick (C0 : Finset α) (t : ℕ) : Finset α :=
  if h : ∃ C, C ⊆ C0 ∧ C.card = t then Classical.choose h else ∅

lemma pick_spec {C0 : Finset α} {t : ℕ} (h : ∃ C, C ⊆ C0 ∧ C.card = t) :
    pick C0 t ⊆ C0 ∧ (pick C0 t).card = t := by
  unfold pick
  rw [dif_pos h]
  exact Classical.choose_spec h

lemma pick_card_le {C0 : Finset α} {t : ℕ} (h : t ≤ C0.card) :
    (pick C0 t).card = t := (pick_spec (Finset.exists_subset_card_eq h)).2

/-- members of `S` containing `T` -/
def containing (S : Finset (Finset α)) (T : Finset α) : Finset (Finset α) :=
  S.filter (fun A : Finset α => T ⊆ A)

lemma card_containing_le_spread {S : Finset (Finset α)} {X : Finset α} {k : ℕ} {r : ℝ}
    (hspread : ∀ T : Finset α, T ⊆ X → T.Nonempty →
      (#(S.filter (fun A : Finset α => T ⊆ A)) : ℝ) ≤ r ^ (k - T.card))
    {T : Finset α} (hTsub : T ⊆ X) (hTne : T.Nonempty) :
    (#(containing S T) : ℝ) ≤ r ^ (k - T.card) := by
  simpa [containing] using hspread T hTsub hTne

/-- `χ(A',U) ⊇ C` implies `A' ⊇ C` (since χ ⊆ A'). -/
lemma chi_sub_mem {S : Finset (Finset α)} {U A' C : Finset α} (hA' : A' ∈ S)
    (hC : C ⊆ chi S U A') : C ⊆ A' := by
  exact subset_trans hC (chi_subset (S := S) (U := U) (A := A') hA')

/-- `τ` is contained in the set of members containing `C`. -/
lemma tau_subset_containing {S : Finset (Finset α)} {U C B : Finset α} {s : ℕ} :
    tau S U C B s ⊆ containing S C := by
  intro A' hA'
  have hA'mem : A' ∈ S := (Finset.mem_filter.mp hA').1
  have hC : C ⊆ chi S U A' := (Finset.mem_filter.mp hA').2.1
  exact Finset.mem_filter.mpr ⟨hA'mem, chi_sub_mem (S := S) (U := U) hA'mem hC⟩

/-- spreadness bounds `τ` when `C` is nonempty and `C ⊆ X`. -/
lemma tau_card_le {S : Finset (Finset α)} {X U C B : Finset α} {k : ℕ} {r : ℝ} {s : ℕ}
    (hspread : ∀ T : Finset α, T ⊆ X → T.Nonempty →
      (#(S.filter (fun A : Finset α => T ⊆ A)) : ℝ) ≤ r ^ (k - T.card))
    (hCne : C.Nonempty) (hCX : C ⊆ X) :
    ((tau S U C B s).card : ℝ) ≤ r ^ (k - C.card) := by
  have hsub : tau S U C B s ⊆ containing S C := tau_subset_containing (S := S) (U := U)
  have hle : (tau S U C B s).card ≤ (containing S C).card := Finset.card_le_card hsub
  have hsp := card_containing_le_spread (S := S) (X := X) (k := k) (r := r) hspread (T := C) hCX hCne
  exact le_trans (by exact_mod_cast hle) hsp

end Submission.Sun
