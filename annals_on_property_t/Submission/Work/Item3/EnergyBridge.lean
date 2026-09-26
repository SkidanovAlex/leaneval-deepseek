import Submission.Work.Item3.EnergyStep
import Submission.Work.Item3.PowNoGenerator
import Submission.Work.ImageAggregate
import Submission.Work.AggregateBoundary
import Submission.Work.RebalanceProtocol

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
set_option autoImplicit false

/-!
# EnergyBridge: from the half-length-1 balanced configuration to the energy move

`Item3/EnergyStep.lean` proves that a half-length-1 balanced row with two
covering neighbours admits a single Nielsen move preserving `N` and strictly
decreasing the positional energy.  This module supplies the *aggregate*
bookkeeping that produces that covering data from the classical balanced
configuration: from an image aggregate `es` whose `j`-th factor is
`±α(a_p)` with word `A ++ B` of half-length 1, whose neighbours carry the
covering words `X ++ invRev A` and `invRev B ++ Z`, and whose factor list is
`SystemReduced` (no adjacent inverse factors — automatic for an aggregate of a
reduced word), the two neighbouring *rows* satisfy the hypotheses of
`energy_step_k1_cover`, including the degeneracy exclusion (`v ≠ p`, `u ≠ p`).

The remaining degenerate case `A = B` (the balanced element would be the
square of a generator) is excluded by `PowNoGenerator.sq_ne_of`.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- `mk` of a single-letter word is the generator or its inverse. -/
lemma mk_singleton_eq {n : ℕ} (i : Fin n) (s : Bool) :
    FreeGroup.mk [(i, s)] = if s then FreeGroup.of i else (FreeGroup.of i)⁻¹ := by
  cases s
  · simpa using mk_singleton_false i
  · simpa using mk_singleton_true i

/-- Two letters whose word `[a] ++ [b]` is reduced have equal generator part
only when they are equal. -/
lemma eq_of_fst_eq_of_reduced {n : ℕ} {a b : Fin n × Bool}
    (hred : FreeGroup.IsReduced ([a] ++ [b])) (h : a.1 = b.1) : a = b := by
  have hc := hred
  rw [show [a] ++ [b] = a :: b :: ([] : List (Fin n × Bool)) from rfl,
    FreeGroup.isReduced_cons_cons] at hc
  have h2 : a.2 = b.2 := hc.1 h
  cases a with
  | mk a1 a2 =>
    cases b with
    | mk b1 b2 =>
      simp only [Prod.mk.injEq] at h2 ⊢
      exact ⟨h, h2⟩

/-- **`a ≠ b` for a half-length-1 balanced factor.**  If `es[j] = ±α(a_p)` has
word `[a] ++ [b]` with `a.1 = b.1`, then `es[j]` is the square of a generator
(up to sign), hence `a_p = y * y` for some `y`, contradicting
`PowNoGenerator.sq_ne_of`. -/
lemma fst_ne_of_factor {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (p : Fin n)
    (a b : Fin n × Bool)
    (hred : FreeGroup.IsReduced ([a] ++ [b]))
    (hfac : α (FreeGroup.of p) = FreeGroup.mk ([a] ++ [b]) ∨
      (α (FreeGroup.of p))⁻¹ = FreeGroup.mk ([a] ++ [b])) :
    a.1 ≠ b.1 := by
  intro h
  have hab : a = b := eq_of_fst_eq_of_reduced hred h
  subst hab
  have hmk : FreeGroup.mk ([a] ++ [a]) = FreeGroup.mk [a] * FreeGroup.mk [a] :=
    FreeGroup.mul_mk
  rcases hfac with hfac | hfac
  · have h1 : α (FreeGroup.of p) = FreeGroup.mk [a] * FreeGroup.mk [a] := by
      rw [hfac, hmk]
    have h4 : FreeGroup.of p = (α⁻¹) (FreeGroup.mk [a] * FreeGroup.mk [a]) := by
      rw [← h1]
      simp
    have hmm : (α⁻¹) (FreeGroup.mk [a] * FreeGroup.mk [a]) =
        (α⁻¹) (FreeGroup.mk [a]) * (α⁻¹) (FreeGroup.mk [a]) :=
      map_mul (α⁻¹) (FreeGroup.mk [a]) (FreeGroup.mk [a])
    have h3 : FreeGroup.of p = (α⁻¹) (FreeGroup.mk [a]) * (α⁻¹) (FreeGroup.mk [a]) := by
      rw [h4, hmm]
    exact (sq_ne_of ((α⁻¹) (FreeGroup.mk [a])) p).1 h3.symm
  · have h2 : α (FreeGroup.of p) = (FreeGroup.mk [a])⁻¹ * (FreeGroup.mk [a])⁻¹ := by
      have hh : α (FreeGroup.of p) = (FreeGroup.mk ([a] ++ [a]))⁻¹ := by
        rw [← hfac]
        simp
      rw [hmk, mul_inv_rev] at hh
      exact hh
    have h4 : FreeGroup.of p =
        (α⁻¹) ((FreeGroup.mk [a])⁻¹ * (FreeGroup.mk [a])⁻¹) := by
      rw [← h2]
      simp
    have hmm : (α⁻¹) ((FreeGroup.mk [a])⁻¹ * (FreeGroup.mk [a])⁻¹) =
        (α⁻¹) ((FreeGroup.mk [a])⁻¹) * (α⁻¹) ((FreeGroup.mk [a])⁻¹) :=
      map_mul (α⁻¹) ((FreeGroup.mk [a])⁻¹) ((FreeGroup.mk [a])⁻¹)
    have h3 : FreeGroup.of p =
        (α⁻¹) ((FreeGroup.mk [a])⁻¹) * (α⁻¹) ((FreeGroup.mk [a])⁻¹) := by
      rw [h4, hmm]
    exact (sq_ne_of ((α⁻¹) ((FreeGroup.mk [a])⁻¹)) p).1 h3.symm

/-! ## The sign-parametrized energy moves

The balanced row's word is `[a] ++ [b]` when the balanced factor is
`+α(a_p)` and `invRev [b] ++ invRev [a]` when it is `-α(a_p)`.  The covering
data is in the *factor* halves `[a]`, `[b]`; the multiplier realizing the
classical move is always `mk ([a] ++ [b])`, which is `w_p` or `w_p⁻¹`
according to the sign.  The four lemmas below state the four (side,
orientation) cases with the sign as a `Bool` parameter. -/

/-- `mk (invRev [b] ++ invRev [a]) = (mk ([a] ++ [b]))⁻¹`. -/
lemma mk_invRev_pair {n : ℕ} (a b : Fin n × Bool) :
    FreeGroup.mk (FreeGroup.invRev [b] ++ FreeGroup.invRev [a]) =
      (FreeGroup.mk ([a] ++ [b]))⁻¹ := by
  have h1 : (FreeGroup.mk [b])⁻¹ = FreeGroup.mk (FreeGroup.invRev [b]) := FreeGroup.inv_mk
  have h2 : (FreeGroup.mk [a])⁻¹ = FreeGroup.mk (FreeGroup.invRev [a]) := FreeGroup.inv_mk
  rw [mk_mul_eq (FreeGroup.invRev [b]) (FreeGroup.invRev [a]), ← h1, ← h2,
    mk_mul_eq [a] [b], mul_inv_rev]

/-- Word of the balanced row in the two orientations. -/
lemma mk_balanced_word {n : ℕ} (a b : Fin n × Bool) (s : Bool) :
    (if s then FreeGroup.mk ([a] ++ [b]) else FreeGroup.mk (FreeGroup.invRev [b] ++ FreeGroup.invRev [a]))
      = if s then FreeGroup.mk ([a] ++ [b]) else (FreeGroup.mk ([a] ++ [b]))⁻¹ := by
  cases s
  · simp only [Bool.false_eq_true, if_false]
    rw [mk_invRev_pair]
  · simp

/-- **Left neighbour, `+` orientation.**  `w_v = X ++ invRev [a]`; the move is
`rho v p` (sign `+`) or `rhoNeg v p` (sign `-`); it preserves `N` and
decreases the energy whenever `lweight b < lweight a`. -/
theorem energy_Lplus {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (hres : NoEndCancel n α)
    {p v : Fin n} (hvp : v ≠ p) (a b : Fin n × Bool) (X : List (Fin n × Bool))
    (s : Bool) (hba : b.1.val < a.1.val)
    (hp : coordWord α p = if s then [a] ++ [b]
      else FreeGroup.invRev [b] ++ FreeGroup.invRev [a])
    (hv : coordWord α v = X ++ FreeGroup.invRev [a]) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) ≤ N α ∧ eEnergy (α * γ) < eEnergy α := by
  cases s
  · -- sign `-`: use `rhoNeg v p`
    simp only [Bool.false_eq_true, if_false] at hp
    have hmk : FreeGroup.mk (coordWord α p) = α (FreeGroup.of p) := FreeGroup.mk_toWord
    have hwp : (α (FreeGroup.of p))⁻¹ = FreeGroup.mk ([a] ++ [b]) := by
      rw [← hmk, hp, mk_invRev_pair, inv_inv]
    have hp' : (α (FreeGroup.of p)).toWord = FreeGroup.invRev [b] ++ FreeGroup.invRev [a] := hp
    have hv' : (α (FreeGroup.of v)).toWord = X ++ FreeGroup.invRev [a] := hv
    have hel : (α * rhoNeg v p hvp) (FreeGroup.of v) = FreeGroup.mk (X ++ [b]) := by
      rw [mul_rhoNeg_apply_self]
      rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of v)), hv', hwp, mk_rho_word]
    have hW : coordWord (α * rhoNeg v p hvp) v = FreeGroup.reduce (X ++ [b]) := by
      show ((α * rhoNeg v p hvp) (FreeGroup.of v)).toWord = _
      rw [hel, FreeGroup.toWord_mk]
    have hlen1' : (coordWord (α * rhoNeg v p hvp) v).length ≤ X.length + 1 := by
      rw [hW]
      calc (FreeGroup.reduce (X ++ [b])).length ≤ (X ++ [b]).length := reduce_length_le _
        _ = X.length + 1 := by rw [List.length_append]; simp
    have hlen0 : (coordWord α v).length = X.length + 1 := by
      rw [hv, List.length_append, invRev_singleton, List.length_singleton]
    have hmin := (noEndCancel_iff_local_min n α).mp hres
    have hNle : N α ≤ N (α * rhoNeg v p hvp) := hmin.2.1 v p hvp
    have habs : FreeGroup.norm (α (FreeGroup.of v)) ≤
        FreeGroup.norm (α (FreeGroup.of v) * (α (FreeGroup.of p))⁻¹) :=
      (N_le_N_mul_rhoNeg_iff α v p hvp).mp hNle
    have hNform := N_mul_rhoNeg α v p hvp
    have h2 : FreeGroup.norm (α (FreeGroup.of v) * (α (FreeGroup.of p))⁻¹) =
        (coordWord (α * rhoNeg v p hvp) v).length := by
      rw [← mul_rhoNeg_apply_self α v p hvp]
      rfl
    have hge : X.length + 1 ≤ (coordWord (α * rhoNeg v p hvp) v).length := by
      have h1 : FreeGroup.norm (α (FreeGroup.of v)) = X.length + 1 := hlen0
      omega
    have hlen_eq : (coordWord (α * rhoNeg v p hvp) v).length = X.length + 1 :=
      le_antisymm hlen1' hge
    have hWeq : coordWord (α * rhoNeg v p hvp) v = X ++ [b] := by
      rw [hW]
      refine reduce_eq_of_length_eq (X ++ [b]) ?_
      rw [← hW, hlen_eq, List.length_append, List.length_singleton]
    have hNeq : N (α * rhoNeg v p hvp) = N α := by
      have h1 : FreeGroup.norm (α (FreeGroup.of v)) = X.length + 1 := hlen0
      have h2' : FreeGroup.norm (α (FreeGroup.of v) * (α (FreeGroup.of p))⁻¹) = X.length + 1 := by
        rw [h2, hlen_eq]
      have h3 : FreeGroup.norm (α (FreeGroup.of v) * (α (FreeGroup.of p))⁻¹) =
          FreeGroup.norm (α (FreeGroup.of v)) := by rw [h1, h2']
      rw [hNform, h3]
      exact Nat.sub_add_cancel (norm_le_N α v)
    refine ⟨rhoNeg v p hvp, Subgroup.subset_closure (rhoNeg_mem_AutGen n hvp), le_of_eq hNeq, ?_⟩
    have hEu := eEnergy_mul_rhoNeg α v p hvp (coordWord (α * rhoNeg v p hvp) v) rfl
    rw [hWeq, hv] at hEu
    have e1 : wordEnergy (ebase n) (lweight) (X ++ FreeGroup.invRev [a]) =
        (ebase n) ^ 1 * wordEnergy (ebase n) (lweight) X + lweight a := by
      rw [wordEnergy_append, wordEnergy_invRev_singleton]
      simp
    have e2 : wordEnergy (ebase n) (lweight) (X ++ [b]) =
        (ebase n) ^ 1 * wordEnergy (ebase n) (lweight) X + lweight b := by
      rw [wordEnergy_append, wordEnergy_singleton]
      simp
    have hlt : wordEnergy (ebase n) (lweight) (X ++ [b]) <
        wordEnergy (ebase n) (lweight) (X ++ FreeGroup.invRev [a]) := by
      have hw : lweight b < lweight a := by unfold lweight; omega
      rw [e1, e2]
      omega
    omega
  · -- sign `+`: `energy_step_rho`
    simp only [if_true] at hp
    rcases energy_step_rho α hres hvp a b X hba hp hv with ⟨hE, hN⟩
    exact ⟨rho v p hvp, Subgroup.subset_closure (rho_mem_AutGen n hvp), le_of_eq hN, hE⟩

/-- **Left neighbour, `-` orientation.**  `w_v = [a] ++ invRev X`; the move is
`lamNeg v p` (sign `+`) or `lam v p` (sign `-`); it preserves `N` and
decreases the energy whenever `lweight b < lweight a`. -/
theorem energy_Lminus {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (hres : NoEndCancel n α)
    {p v : Fin n} (hvp : v ≠ p) (a b : Fin n × Bool) (X : List (Fin n × Bool))
    (s : Bool) (hba : b.1.val < a.1.val)
    (hp : coordWord α p = if s then [a] ++ [b]
      else FreeGroup.invRev [b] ++ FreeGroup.invRev [a])
    (hv : coordWord α v = [a] ++ FreeGroup.invRev X) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) ≤ N α ∧ eEnergy (α * γ) < eEnergy α := by
  have hlen0 : (coordWord α v).length = 1 + X.length := by
    rw [hv, List.length_append, List.length_singleton, FreeGroup.invRev_length]
  have hlen1 : (FreeGroup.reduce (FreeGroup.invRev [b] ++ FreeGroup.invRev X)).length ≤
      1 + X.length := by
    calc (FreeGroup.reduce (FreeGroup.invRev [b] ++ FreeGroup.invRev X)).length
        ≤ (FreeGroup.invRev [b] ++ FreeGroup.invRev X).length := reduce_length_le _
      _ = 1 + X.length := by
          rw [List.length_append, invRev_singleton, List.length_singleton,
            FreeGroup.invRev_length]
  have hlt : wordEnergy (ebase n) (lweight) (FreeGroup.invRev [b] ++ FreeGroup.invRev X) <
      wordEnergy (ebase n) (lweight) ([a] ++ FreeGroup.invRev X) := by
    have hw : lweight b < lweight a := by unfold lweight; omega
    have hpos := pow_ebase_pos (n := n) X.length
    rw [wordEnergy_append, wordEnergy_invRev_singleton, wordEnergy_append,
      wordEnergy_singleton, FreeGroup.invRev_length]
    have hmul : (ebase n) ^ X.length * lweight b < (ebase n) ^ X.length * lweight a :=
      Nat.mul_lt_mul_of_pos_left hw hpos
    omega
  cases s
  · -- sign `-`: `lam v p`
    simp only [Bool.false_eq_true, if_false] at hp
    have hmk : FreeGroup.mk (coordWord α p) = α (FreeGroup.of p) := FreeGroup.mk_toWord
    have hwp : α (FreeGroup.of p) = (FreeGroup.mk ([a] ++ [b]))⁻¹ := by
      rw [← hmk, hp, mk_invRev_pair]
    have hp' : (α (FreeGroup.of p)).toWord = FreeGroup.invRev [b] ++ FreeGroup.invRev [a] := hp
    have hv' : (α (FreeGroup.of v)).toWord = [a] ++ FreeGroup.invRev X := hv
    have hel : (α * lam v p hvp) (FreeGroup.of v) =
        FreeGroup.mk (FreeGroup.invRev [b] ++ FreeGroup.invRev X) := by
      rw [mul_lam_apply_self]
      rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hp', mk_invRev_pair,
        ← FreeGroup.mk_toWord (x := α (FreeGroup.of v)), hv']
      exact mk_lamNeg_word X a b
    have hW : coordWord (α * lam v p hvp) v =
        FreeGroup.reduce (FreeGroup.invRev [b] ++ FreeGroup.invRev X) := by
      show ((α * lam v p hvp) (FreeGroup.of v)).toWord = _
      rw [hel, FreeGroup.toWord_mk]
    have hmin := (noEndCancel_iff_local_min n α).mp hres
    have hNle : N α ≤ N (α * lam v p hvp) := hmin.2.2.1 v p hvp
    have hNform := N_mul_lam α v p hvp
    have habs : FreeGroup.norm (α (FreeGroup.of v)) ≤
        FreeGroup.norm ((α (FreeGroup.of p)) * (α (FreeGroup.of v))) :=
      (N_le_N_mul_lam_iff α v p hvp).mp hNle
    have h2 : FreeGroup.norm ((α (FreeGroup.of p)) * (α (FreeGroup.of v))) =
        (coordWord (α * lam v p hvp) v).length := by
      rw [← mul_lam_apply_self α v p hvp]
      rfl
    have hge : 1 + X.length ≤ (coordWord (α * lam v p hvp) v).length := by
      have h1 : FreeGroup.norm (α (FreeGroup.of v)) = 1 + X.length := hlen0
      omega
    have hlen_eq : (coordWord (α * lam v p hvp) v).length = 1 + X.length :=
      le_antisymm (le_trans (by rw [hW]; exact hlen1) (le_of_eq rfl)) hge
    have hWeq : coordWord (α * lam v p hvp) v =
        FreeGroup.invRev [b] ++ FreeGroup.invRev X := by
      rw [hW]
      refine reduce_eq_of_length_eq _ ?_
      rw [← hW, hlen_eq, List.length_append, invRev_singleton, List.length_singleton,
        FreeGroup.invRev_length]
    have hNeq : N (α * lam v p hvp) = N α := by
      have h1 : FreeGroup.norm (α (FreeGroup.of v)) = 1 + X.length := hlen0
      have h2' : FreeGroup.norm ((α (FreeGroup.of p)) * (α (FreeGroup.of v))) =
          1 + X.length := by rw [h2, hlen_eq]
      have h3 : FreeGroup.norm ((α (FreeGroup.of p)) * (α (FreeGroup.of v))) =
          FreeGroup.norm (α (FreeGroup.of v)) := by rw [h1, h2']
      rw [hNform, h3]
      exact Nat.sub_add_cancel (norm_le_N α v)
    refine ⟨lam v p hvp, Subgroup.subset_closure (lam_mem_AutGen n hvp), le_of_eq hNeq, ?_⟩
    have hEu := eEnergy_mul_lam α v p hvp (coordWord (α * lam v p hvp) v) rfl
    rw [hWeq, hv] at hEu
    omega
  · -- sign `+`: `lamNeg v p`
    simp only [if_true] at hp
    have hp' : (α (FreeGroup.of p)).toWord = [a] ++ [b] := hp
    have hv' : (α (FreeGroup.of v)).toWord = [a] ++ FreeGroup.invRev X := hv
    have hel : (α * lamNeg v p hvp) (FreeGroup.of v) =
        FreeGroup.mk (FreeGroup.invRev [b] ++ FreeGroup.invRev X) := by
      rw [mul_lamNeg_apply_self]
      rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of v)), hv',
        ← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hp']
      exact mk_lamNeg_word X a b
    have hW : coordWord (α * lamNeg v p hvp) v =
        FreeGroup.reduce (FreeGroup.invRev [b] ++ FreeGroup.invRev X) := by
      show ((α * lamNeg v p hvp) (FreeGroup.of v)).toWord = _
      rw [hel, FreeGroup.toWord_mk]
    have hmin := (noEndCancel_iff_local_min n α).mp hres
    have hNle : N α ≤ N (α * lamNeg v p hvp) := hmin.2.2.2 v p hvp
    have hNform := N_mul_lamNeg α v p hvp
    have habs : FreeGroup.norm (α (FreeGroup.of v)) ≤
        FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of v))) :=
      (N_le_N_mul_lamNeg_iff α v p hvp).mp hNle
    have h2 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of v))) =
        (coordWord (α * lamNeg v p hvp) v).length := by
      rw [← mul_lamNeg_apply_self α v p hvp]
      rfl
    have hge : 1 + X.length ≤ (coordWord (α * lamNeg v p hvp) v).length := by
      have h1 : FreeGroup.norm (α (FreeGroup.of v)) = 1 + X.length := hlen0
      omega
    have hlen_eq : (coordWord (α * lamNeg v p hvp) v).length = 1 + X.length :=
      le_antisymm (le_trans (by rw [hW]; exact hlen1) (le_of_eq rfl)) hge
    have hWeq : coordWord (α * lamNeg v p hvp) v =
        FreeGroup.invRev [b] ++ FreeGroup.invRev X := by
      rw [hW]
      refine reduce_eq_of_length_eq _ ?_
      rw [← hW, hlen_eq, List.length_append, invRev_singleton, List.length_singleton,
        FreeGroup.invRev_length]
    have hNeq : N (α * lamNeg v p hvp) = N α := by
      have h1 : FreeGroup.norm (α (FreeGroup.of v)) = 1 + X.length := hlen0
      have h2' : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of v))) =
          1 + X.length := by rw [h2, hlen_eq]
      have h3 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of v))) =
          FreeGroup.norm (α (FreeGroup.of v)) := by rw [h1, h2']
      rw [hNform, h3]
      exact Nat.sub_add_cancel (norm_le_N α v)
    refine ⟨lamNeg v p hvp, ?_, le_of_eq hNeq, ?_⟩
    · rw [← lam_inv_eq v p hvp]
      exact (AutClosure n).inv_mem (Subgroup.subset_closure (lam_mem_AutGen n hvp))
    · have hEu := eEnergy_mul_lamNeg α v p hvp (coordWord (α * lamNeg v p hvp) v) rfl
      rw [hWeq, hv] at hEu
      omega

/-- **Right neighbour, `+` orientation.**  `w_u = invRev [b] ++ Z`; the move is
`lam u p` (sign `+`) or `lamNeg u p` (sign `-`); it preserves `N` and
decreases the energy whenever `lweight a < lweight b`. -/
theorem energy_Rplus {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (hres : NoEndCancel n α)
    {p u : Fin n} (hup : u ≠ p) (a b : Fin n × Bool) (Z : List (Fin n × Bool))
    (s : Bool) (hab : a.1.val < b.1.val)
    (hp : coordWord α p = if s then [a] ++ [b]
      else FreeGroup.invRev [b] ++ FreeGroup.invRev [a])
    (hu : coordWord α u = FreeGroup.invRev [b] ++ Z) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) ≤ N α ∧ eEnergy (α * γ) < eEnergy α := by
  have hlen0 : (coordWord α u).length = 1 + Z.length := by
    rw [hu, List.length_append, invRev_singleton, List.length_singleton]
  have hlen1 : (FreeGroup.reduce ([a] ++ Z)).length ≤ 1 + Z.length := by
    calc (FreeGroup.reduce ([a] ++ Z)).length ≤ ([a] ++ Z).length := reduce_length_le _
      _ = 1 + Z.length := by rw [List.length_append, List.length_singleton]
  have hlt : wordEnergy (ebase n) (lweight) ([a] ++ Z) <
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev [b] ++ Z) := by
    have hw : lweight a < lweight b := by unfold lweight; omega
    have hpos := pow_ebase_pos (n := n) Z.length
    rw [wordEnergy_append, wordEnergy_singleton, wordEnergy_append,
      wordEnergy_invRev_singleton]
    have hmul : (ebase n) ^ Z.length * lweight a < (ebase n) ^ Z.length * lweight b :=
      Nat.mul_lt_mul_of_pos_left hw hpos
    omega
  cases s
  · -- sign `-`: `lamNeg u p`
    simp only [Bool.false_eq_true, if_false] at hp
    have hmk : FreeGroup.mk (coordWord α p) = α (FreeGroup.of p) := FreeGroup.mk_toWord
    have hwp : (α (FreeGroup.of p))⁻¹ = FreeGroup.mk ([a] ++ [b]) := by
      rw [← hmk, hp, mk_invRev_pair, inv_inv]
    have hp' : (α (FreeGroup.of p)).toWord = FreeGroup.invRev [b] ++ FreeGroup.invRev [a] := hp
    have hu' : (α (FreeGroup.of u)).toWord = FreeGroup.invRev [b] ++ Z := hu
    have hel : (α * lamNeg u p hup) (FreeGroup.of u) = FreeGroup.mk ([a] ++ Z) := by
      rw [mul_lamNeg_apply_self]
      rw [hwp, ← FreeGroup.mk_toWord (x := α (FreeGroup.of u)), hu']
      exact mk_lam_word Z a b
    have hW : coordWord (α * lamNeg u p hup) u = FreeGroup.reduce ([a] ++ Z) := by
      show ((α * lamNeg u p hup) (FreeGroup.of u)).toWord = _
      rw [hel, FreeGroup.toWord_mk]
    have hmin := (noEndCancel_iff_local_min n α).mp hres
    have hNle : N α ≤ N (α * lamNeg u p hup) := hmin.2.2.2 u p hup
    have hNform := N_mul_lamNeg α u p hup
    have habs : FreeGroup.norm (α (FreeGroup.of u)) ≤
        FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of u))) :=
      (N_le_N_mul_lamNeg_iff α u p hup).mp hNle
    have h2 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of u))) =
        (coordWord (α * lamNeg u p hup) u).length := by
      rw [← mul_lamNeg_apply_self α u p hup]
      rfl
    have hge : 1 + Z.length ≤ (coordWord (α * lamNeg u p hup) u).length := by
      have h1 : FreeGroup.norm (α (FreeGroup.of u)) = 1 + Z.length := hlen0
      omega
    have hlen_eq : (coordWord (α * lamNeg u p hup) u).length = 1 + Z.length :=
      le_antisymm (le_trans (by rw [hW]; exact hlen1) (le_of_eq rfl)) hge
    have hWeq : coordWord (α * lamNeg u p hup) u = [a] ++ Z := by
      rw [hW]
      refine reduce_eq_of_length_eq _ ?_
      rw [← hW, hlen_eq, List.length_append, List.length_singleton]
    have hNeq : N (α * lamNeg u p hup) = N α := by
      have h1 : FreeGroup.norm (α (FreeGroup.of u)) = 1 + Z.length := hlen0
      have h2' : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of u))) =
          1 + Z.length := by rw [h2, hlen_eq]
      have h3 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of u))) =
          FreeGroup.norm (α (FreeGroup.of u)) := by rw [h1, h2']
      rw [hNform, h3]
      exact Nat.sub_add_cancel (norm_le_N α u)
    refine ⟨lamNeg u p hup, ?_, le_of_eq hNeq, ?_⟩
    · rw [← lam_inv_eq u p hup]
      exact (AutClosure n).inv_mem (Subgroup.subset_closure (lam_mem_AutGen n hup))
    · have hEu := eEnergy_mul_lamNeg α u p hup (coordWord (α * lamNeg u p hup) u) rfl
      rw [hWeq, hu] at hEu
      omega
  · -- sign `+`: `lam u p`
    simp only [if_true] at hp
    have hp' : (α (FreeGroup.of p)).toWord = [a] ++ [b] := hp
    have hu' : (α (FreeGroup.of u)).toWord = FreeGroup.invRev [b] ++ Z := hu
    have hel : (α * lam u p hup) (FreeGroup.of u) = FreeGroup.mk ([a] ++ Z) := by
      rw [mul_lam_apply_self]
      rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hp',
        ← FreeGroup.mk_toWord (x := α (FreeGroup.of u)), hu']
      exact mk_lam_word Z a b
    have hW : coordWord (α * lam u p hup) u = FreeGroup.reduce ([a] ++ Z) := by
      show ((α * lam u p hup) (FreeGroup.of u)).toWord = _
      rw [hel, FreeGroup.toWord_mk]
    have hmin := (noEndCancel_iff_local_min n α).mp hres
    have hNle : N α ≤ N (α * lam u p hup) := hmin.2.2.1 u p hup
    have hNform := N_mul_lam α u p hup
    have habs : FreeGroup.norm (α (FreeGroup.of u)) ≤
        FreeGroup.norm ((α (FreeGroup.of p)) * (α (FreeGroup.of u))) :=
      (N_le_N_mul_lam_iff α u p hup).mp hNle
    have h2 : FreeGroup.norm ((α (FreeGroup.of p)) * (α (FreeGroup.of u))) =
        (coordWord (α * lam u p hup) u).length := by
      rw [← mul_lam_apply_self α u p hup]
      rfl
    have hge : 1 + Z.length ≤ (coordWord (α * lam u p hup) u).length := by
      have h1 : FreeGroup.norm (α (FreeGroup.of u)) = 1 + Z.length := hlen0
      omega
    have hlen_eq : (coordWord (α * lam u p hup) u).length = 1 + Z.length :=
      le_antisymm (le_trans (by rw [hW]; exact hlen1) (le_of_eq rfl)) hge
    have hWeq : coordWord (α * lam u p hup) u = [a] ++ Z := by
      rw [hW]
      refine reduce_eq_of_length_eq _ ?_
      rw [← hW, hlen_eq, List.length_append, List.length_singleton]
    have hNeq : N (α * lam u p hup) = N α := by
      have h1 : FreeGroup.norm (α (FreeGroup.of u)) = 1 + Z.length := hlen0
      have h2' : FreeGroup.norm ((α (FreeGroup.of p)) * (α (FreeGroup.of u))) =
          1 + Z.length := by rw [h2, hlen_eq]
      have h3 : FreeGroup.norm ((α (FreeGroup.of p)) * (α (FreeGroup.of u))) =
          FreeGroup.norm (α (FreeGroup.of u)) := by rw [h1, h2']
      rw [hNform, h3]
      exact Nat.sub_add_cancel (norm_le_N α u)
    refine ⟨lam u p hup, Subgroup.subset_closure (lam_mem_AutGen n hup), le_of_eq hNeq, ?_⟩
    have hEu := eEnergy_mul_lam α u p hup (coordWord (α * lam u p hup) u) rfl
    rw [hWeq, hu] at hEu
    omega

/-- **Right neighbour, `-` orientation.**  `w_u = invRev Z ++ [b]`; the move is
`rhoNeg u p` (sign `+`) or `rho u p` (sign `-`); it preserves `N` and
decreases the energy whenever `lweight a < lweight b`. -/
theorem energy_Rminus {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (hres : NoEndCancel n α)
    {p u : Fin n} (hup : u ≠ p) (a b : Fin n × Bool) (Z : List (Fin n × Bool))
    (s : Bool) (hab : a.1.val < b.1.val)
    (hp : coordWord α p = if s then [a] ++ [b]
      else FreeGroup.invRev [b] ++ FreeGroup.invRev [a])
    (hu : coordWord α u = FreeGroup.invRev Z ++ [b]) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) ≤ N α ∧ eEnergy (α * γ) < eEnergy α := by
  have hlen0 : (coordWord α u).length = Z.length + 1 := by
    rw [hu, List.length_append, List.length_singleton, FreeGroup.invRev_length]
  have hlen1 : (FreeGroup.reduce (FreeGroup.invRev Z ++ FreeGroup.invRev [a])).length ≤
      Z.length + 1 := by
    calc (FreeGroup.reduce (FreeGroup.invRev Z ++ FreeGroup.invRev [a])).length
        ≤ (FreeGroup.invRev Z ++ FreeGroup.invRev [a]).length := reduce_length_le _
      _ = Z.length + 1 := by
          rw [List.length_append, invRev_singleton, List.length_singleton,
            FreeGroup.invRev_length]
  have hlt : wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z ++ FreeGroup.invRev [a]) <
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z ++ [b]) := by
    have hw : lweight a < lweight b := by unfold lweight; omega
    have h1 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z ++ FreeGroup.invRev [a])
        = (ebase n) ^ 1 * wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z) + lweight a := by
      rw [wordEnergy_append, wordEnergy_invRev_singleton, invRev_singleton,
        List.length_singleton]
    have h2 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z ++ [b])
        = (ebase n) ^ 1 * wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z) + lweight b := by
      rw [wordEnergy_append, wordEnergy_singleton, List.length_singleton]
    rw [h1, h2]
    omega
  cases s
  · -- sign `-`: `rho u p`
    simp only [Bool.false_eq_true, if_false] at hp
    have hmk : FreeGroup.mk (coordWord α p) = α (FreeGroup.of p) := FreeGroup.mk_toWord
    have hwp : α (FreeGroup.of p) = (FreeGroup.mk ([a] ++ [b]))⁻¹ := by
      rw [← hmk, hp, mk_invRev_pair]
    have hp' : (α (FreeGroup.of p)).toWord = FreeGroup.invRev [b] ++ FreeGroup.invRev [a] := hp
    have hu' : (α (FreeGroup.of u)).toWord = FreeGroup.invRev Z ++ [b] := hu
    have hel : (α * rho u p hup) (FreeGroup.of u) =
        FreeGroup.mk (FreeGroup.invRev Z ++ FreeGroup.invRev [a]) := by
      rw [mul_rho_apply_self]
      rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of u)), hu', hwp]
      exact mk_rhoNeg_word Z a b
    have hW : coordWord (α * rho u p hup) u =
        FreeGroup.reduce (FreeGroup.invRev Z ++ FreeGroup.invRev [a]) := by
      show ((α * rho u p hup) (FreeGroup.of u)).toWord = _
      rw [hel, FreeGroup.toWord_mk]
    have hmin := (noEndCancel_iff_local_min n α).mp hres
    have hNle : N α ≤ N (α * rho u p hup) := hmin.1 u p hup
    have hNform := N_mul_rho α u p hup
    have habs : FreeGroup.norm (α (FreeGroup.of u)) ≤
        FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))) :=
      (N_le_N_mul_rho_iff α u p hup).mp hNle
    have h2 : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))) =
        (coordWord (α * rho u p hup) u).length := by
      rw [← mul_rho_apply_self α u p hup]
      rfl
    have hge : Z.length + 1 ≤ (coordWord (α * rho u p hup) u).length := by
      have h1 : FreeGroup.norm (α (FreeGroup.of u)) = Z.length + 1 := hlen0
      omega
    have hlen_eq : (coordWord (α * rho u p hup) u).length = Z.length + 1 :=
      le_antisymm (le_trans (by rw [hW]; exact hlen1) (le_of_eq rfl)) hge
    have hWeq : coordWord (α * rho u p hup) u =
        FreeGroup.invRev Z ++ FreeGroup.invRev [a] := by
      rw [hW]
      refine reduce_eq_of_length_eq _ ?_
      rw [← hW, hlen_eq, List.length_append, invRev_singleton, List.length_singleton,
        FreeGroup.invRev_length]
    have hNeq : N (α * rho u p hup) = N α := by
      have h1 : FreeGroup.norm (α (FreeGroup.of u)) = Z.length + 1 := hlen0
      have h2' : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))) =
          Z.length + 1 := by rw [h2, hlen_eq]
      have h3 : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))) =
          FreeGroup.norm (α (FreeGroup.of u)) := by rw [h1, h2']
      rw [hNform, h3]
      exact Nat.sub_add_cancel (norm_le_N α u)
    refine ⟨rho u p hup, Subgroup.subset_closure (rho_mem_AutGen n hup), le_of_eq hNeq, ?_⟩
    have hEu := eEnergy_mul_rho α u p hup (coordWord (α * rho u p hup) u) rfl
    rw [hWeq, hu] at hEu
    omega
  · -- sign `+`: `rhoNeg u p`
    simp only [if_true] at hp
    have hp' : (α (FreeGroup.of p)).toWord = [a] ++ [b] := hp
    have hu' : (α (FreeGroup.of u)).toWord = FreeGroup.invRev Z ++ [b] := hu
    have hel : (α * rhoNeg u p hup) (FreeGroup.of u) =
        FreeGroup.mk (FreeGroup.invRev Z ++ FreeGroup.invRev [a]) := by
      rw [mul_rhoNeg_apply_self]
      rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of u)), hu',
        ← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hp']
      exact mk_rhoNeg_word Z a b
    have hW : coordWord (α * rhoNeg u p hup) u =
        FreeGroup.reduce (FreeGroup.invRev Z ++ FreeGroup.invRev [a]) := by
      show ((α * rhoNeg u p hup) (FreeGroup.of u)).toWord = _
      rw [hel, FreeGroup.toWord_mk]
    have hmin := (noEndCancel_iff_local_min n α).mp hres
    have hNle : N α ≤ N (α * rhoNeg u p hup) := hmin.2.1 u p hup
    have hNform := N_mul_rhoNeg α u p hup
    have habs : FreeGroup.norm (α (FreeGroup.of u)) ≤
        FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))⁻¹) :=
      (N_le_N_mul_rhoNeg_iff α u p hup).mp hNle
    have h2 : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))⁻¹) =
        (coordWord (α * rhoNeg u p hup) u).length := by
      rw [← mul_rhoNeg_apply_self α u p hup]
      rfl
    have hge : Z.length + 1 ≤ (coordWord (α * rhoNeg u p hup) u).length := by
      have h1 : FreeGroup.norm (α (FreeGroup.of u)) = Z.length + 1 := hlen0
      omega
    have hlen_eq : (coordWord (α * rhoNeg u p hup) u).length = Z.length + 1 :=
      le_antisymm (le_trans (by rw [hW]; exact hlen1) (le_of_eq rfl)) hge
    have hWeq : coordWord (α * rhoNeg u p hup) u =
        FreeGroup.invRev Z ++ FreeGroup.invRev [a] := by
      rw [hW]
      refine reduce_eq_of_length_eq _ ?_
      rw [← hW, hlen_eq, List.length_append, invRev_singleton, List.length_singleton,
        FreeGroup.invRev_length]
    have hNeq : N (α * rhoNeg u p hup) = N α := by
      have h1 : FreeGroup.norm (α (FreeGroup.of u)) = Z.length + 1 := hlen0
      have h2' : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))⁻¹) =
          Z.length + 1 := by rw [h2, hlen_eq]
      have h3 : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))⁻¹) =
          FreeGroup.norm (α (FreeGroup.of u)) := by rw [h1, h2']
      rw [hNform, h3]
      exact Nat.sub_add_cancel (norm_le_N α u)
    refine ⟨rhoNeg u p hup, Subgroup.subset_closure (rhoNeg_mem_AutGen n hup), le_of_eq hNeq, ?_⟩
    have hEu := eEnergy_mul_rhoNeg α u p hup (coordWord (α * rhoNeg u p hup) u) rfl
    rw [hWeq, hu] at hEu
    omega

/-- **The half-length-1 energy step in factor-half covering form** (the form the
aggregate supplies).  `[a]`, `[b]` are the halves of the *factor's* word, the
balanced row's word is `[a] ++ [b]` (sign `true`) or `invRev [b] ++ invRev [a]`
(sign `false`), and the two neighbours cover in either orientation.  Exactly one
of the two neighbours then supplies an `N`-preserving, energy-descending
single move. -/
theorem energy_k1_factors {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p v u : Fin n} (hvp : v ≠ p) (hup : u ≠ p)
    (a b : Fin n × Bool) (X Z : List (Fin n × Bool)) (s : Bool) (hab : a.1 ≠ b.1)
    (hp : coordWord α p = if s then [a] ++ [b]
      else FreeGroup.invRev [b] ++ FreeGroup.invRev [a])
    (hv : coordWord α v = X ++ FreeGroup.invRev [a] ∨
      coordWord α v = [a] ++ FreeGroup.invRev X)
    (hu : coordWord α u = FreeGroup.invRev [b] ++ Z ∨
      coordWord α u = FreeGroup.invRev Z ++ [b]) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) ≤ N α ∧ eEnergy (α * γ) < eEnergy α := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · rcases hu with hu | hu
    · exact energy_Rplus α hres hup a b Z s hlt hp hu
    · exact energy_Rminus α hres hup a b Z s hlt hp hu
  · rcases hv with hv | hv
    · exact energy_Lplus α hres hvp a b X s hgt hp hv
    · exact energy_Lminus α hres hvp a b X s hgt hp hv

end Submission.Nielsen
