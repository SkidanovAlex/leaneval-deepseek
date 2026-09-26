import Submission.Work.NielsenEnergy
import Submission.Work.Item3.CovererCase

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
open scoped BigOperators
set_option autoImplicit false

/-!
# EnergyStep: the single-move energy descent for a half-length-1 balanced row

The Fall-II (balanced) phase of the Nielsen reduction is classically handled by
a *lexicographic* measure: the total reduced length `N` may be stuck (a
"peak", `LongArm.peak_counterexample`), but a single Nielsen move keeping `N`
fixed strictly decreases an **energy**, the place-weighted lexicographic
weight of the basis images read from the left (Bene, arXiv:1010.5275 §4; the
source's "Energie"; `NielsenEnergy.energy_terminates` already proves the
termination of the resulting lexicographic descent).

This module formalises that step for the base case of a *half-length-1*
balanced row `p`, whose word is the two distinct letters `[a] ++ [b]`, with
the two covering rows

    w_v = X ++ invRev [a]      (left neighbour, ending with `invRev a`),
    w_u = invRev [b] ++ Z      (right neighbour, beginning with `invRev b`)

(the half-length-1 `FallTwoConfig` shape).  The two elementary moves

    rho v p :  w_v ↦ w_v · w_p   (word `X ++ [b]`,   `N` preserved),
    lam u p :  w_u ↦ w_p · w_u   (word `[a] ++ Z`,   `N` preserved)

change the state energy by

    Δ_v = lweight b - lweight a,     Δ_u = (lweight a - lweight b) * ebase^{|Z|},

so *exactly one is negative*: if `lweight b < lweight a` the `rho` move
descends, otherwise the `lam` move does.  In a residual state (`NoEndCancel`)
both moves have `N (α * γ) = N α` (it cannot increase — the telescoping word
identity — and cannot decrease — local minimality), so the energy strictly
decreases at constant `N`.

This closes the `k = 1` branch of the Fall-II pin `hF` by a *single*
elementary move — no pass iteration, no index-advance/no-reappearance
argument.

## Main declarations

* `lweight`, `ebase` — letter rank and place-value base;
* `wordEnergy_append`, `wordEnergy_singleton` — the positional energy;
* `tupleEnergy_mul_rho` / `tupleEnergy_mul_lam` — energy update;
* `energy_step_rho` / `energy_step_lam` — the two moves;
* `energy_step_k1` — one of the two strictly descends.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-! ## The energy -/

/-- Letter rank: generator index plus one (inversion-invariant, so that
`invRev` of a letter has the same rank). -/
def lweight {n : ℕ} (l : Fin n × Bool) : ℕ := l.1.val + 1

/-- Place-value base of the energy: larger than every letter rank. -/
def ebase (n : ℕ) : ℕ := n + 2

/-- The state energy specialised to the letter rank `lweight` and the base
`ebase n`. -/
def eEnergy {n : ℕ} : MulAut (FreeGroup (Fin n)) → ℕ :=
  tupleEnergy n (ebase n) (fun l => lweight l)

/-! ## Positional energy lemmas -/

/-- The positional energy is additive over concatenation, with place-value
factor `B^{|W|}`. -/
lemma wordEnergy_append {α : Type*} (B : ℕ) (rank : α → ℕ)
    (X W : List α) :
    wordEnergy B rank (X ++ W) = B ^ W.length * wordEnergy B rank X + wordEnergy B rank W := by
  induction X with
  | nil => rw [List.nil_append, wordEnergy_nil]; simp
  | cons l t ih =>
      rw [List.cons_append, wordEnergy_cons, wordEnergy_cons, ih, List.length_append,
        pow_add]
      ring

lemma wordEnergy_singleton {α : Type*} (B : ℕ) (rank : α → ℕ) (l : α) :
    wordEnergy B rank [l] = rank l := by
  rw [wordEnergy_cons, wordEnergy_nil]
  simp

lemma lweight_invRev {n : ℕ} (l : Fin n × Bool) : lweight (l.1, !l.2) = lweight l := rfl

lemma wordEnergy_invRev_singleton {n : ℕ} (l : Fin n × Bool) :
    wordEnergy (ebase n) (lweight) (FreeGroup.invRev [l]) = lweight l := by
  rw [invRev_singleton, wordEnergy_singleton, lweight_invRev]

lemma one_le_ebase (n : ℕ) : 1 ≤ ebase n := by unfold ebase; omega

lemma pow_ebase_pos {n : ℕ} (k : ℕ) : 0 < (ebase n) ^ k :=
  pow_pos (by unfold ebase; omega) k

/-! ## The energy update under a single transvection -/

/-- Splitting a state energy at a coordinate. -/
lemma eEnergy_eq_sum_erase {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (v : Fin n) :
    eEnergy α =
      (∑ i ∈ (Finset.univ.erase v : Finset (Fin n)),
          wordEnergy (ebase n) (lweight) (coordWord α i)) +
        wordEnergy (ebase n) (lweight) (coordWord α v) := by
  unfold eEnergy tupleEnergy
  exact (Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun k => wordEnergy (ebase n) (lweight) (FreeGroup.toWord (α (FreeGroup.of k))))
    (Finset.mem_univ v)).symm

/-- **Energy update, `rho` move**: composing on the right by `rho i j` changes
only the `i`-th image, whose word becomes `W`. -/
lemma eEnergy_mul_rho {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (i j : Fin n)
    (hij : i ≠ j) (W : List (Fin n × Bool))
    (hW : coordWord (α * rho i j hij) i = W) :
    eEnergy (α * rho i j hij) + wordEnergy (ebase n) (lweight) (coordWord α i) =
      eEnergy α + wordEnergy (ebase n) (lweight) W := by
  rw [eEnergy_eq_sum_erase (α * rho i j hij) i, eEnergy_eq_sum_erase α i, hW]
  have hrest : (∑ k ∈ (Finset.univ.erase i : Finset (Fin n)),
      wordEnergy (ebase n) (lweight) (coordWord (α * rho i j hij) k)) =
      (∑ k ∈ (Finset.univ.erase i : Finset (Fin n)),
        wordEnergy (ebase n) (lweight) (coordWord α k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    rw [show coordWord (α * rho i j hij) k = coordWord α k from
      congrArg FreeGroup.toWord (mul_rho_apply_other (α := α) hij hki)]
  rw [hrest]
  ring

/-- **Energy update, `lam` move**: composing on the right by `lam i j` changes
only the `i`-th image, whose word becomes `W`. -/
lemma eEnergy_mul_lam {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (i j : Fin n)
    (hij : i ≠ j) (W : List (Fin n × Bool))
    (hW : coordWord (α * lam i j hij) i = W) :
    eEnergy (α * lam i j hij) + wordEnergy (ebase n) (lweight) (coordWord α i) =
      eEnergy α + wordEnergy (ebase n) (lweight) W := by
  rw [eEnergy_eq_sum_erase (α * lam i j hij) i, eEnergy_eq_sum_erase α i, hW]
  have hrest : (∑ k ∈ (Finset.univ.erase i : Finset (Fin n)),
      wordEnergy (ebase n) (lweight) (coordWord (α * lam i j hij) k)) =
      (∑ k ∈ (Finset.univ.erase i : Finset (Fin n)),
        wordEnergy (ebase n) (lweight) (coordWord α k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    rw [show coordWord (α * lam i j hij) k = coordWord α k from
      congrArg FreeGroup.toWord (mul_lam_apply_other (α := α) hij hki)]
  rw [hrest]
  ring

/-! ## The two moves -/

/-- Word identity for the `rho` move: `(X ++ invRev [a]) · ([a] ++ [b]) = X ++ [b]`
at the element level. -/
lemma mk_rho_word {n : ℕ} (X : List (Fin n × Bool)) (a b : Fin n × Bool) :
    FreeGroup.mk (X ++ FreeGroup.invRev [a]) * FreeGroup.mk ([a] ++ [b]) =
      FreeGroup.mk (X ++ [b]) := by
  have h1 : FreeGroup.mk (X ++ FreeGroup.invRev [a]) * FreeGroup.mk [a] = FreeGroup.mk X :=
    mul_mk_app_invRev X [a]
  have h2 : FreeGroup.mk ([a] ++ [b]) = FreeGroup.mk [a] * FreeGroup.mk [b] := by
    rw [FreeGroup.mul_mk]
  rw [h2, ← mul_assoc, h1, FreeGroup.mul_mk]

/-- Word identity for the `lam` move: `([a] ++ [b]) · (invRev [b] ++ Z) = [a] ++ Z`
at the element level. -/
lemma mk_lam_word {n : ℕ} (Z : List (Fin n × Bool)) (a b : Fin n × Bool) :
    FreeGroup.mk ([a] ++ [b]) * FreeGroup.mk (FreeGroup.invRev [b] ++ Z) =
      FreeGroup.mk ([a] ++ Z) := by
  have h1 : FreeGroup.mk [b] * FreeGroup.mk (FreeGroup.invRev [b] ++ Z) = FreeGroup.mk Z :=
    mul_mk_append_invRev (P := Z) (L := [b])
  have h2 : FreeGroup.mk ([a] ++ [b]) = FreeGroup.mk [a] * FreeGroup.mk [b] := by
    rw [FreeGroup.mul_mk]
  rw [h2, mul_assoc, h1, FreeGroup.mul_mk]

/-- **Energy update, `lamNeg` move**: composing on the right by `lamNeg i j`
changes only the `i`-th image, whose word becomes `W`. -/
lemma eEnergy_mul_lamNeg {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (i j : Fin n)
    (hij : i ≠ j) (W : List (Fin n × Bool))
    (hW : coordWord (α * lamNeg i j hij) i = W) :
    eEnergy (α * lamNeg i j hij) + wordEnergy (ebase n) (lweight) (coordWord α i) =
      eEnergy α + wordEnergy (ebase n) (lweight) W := by
  rw [eEnergy_eq_sum_erase (α * lamNeg i j hij) i, eEnergy_eq_sum_erase α i, hW]
  have hrest : (∑ k ∈ (Finset.univ.erase i : Finset (Fin n)),
      wordEnergy (ebase n) (lweight) (coordWord (α * lamNeg i j hij) k)) =
      (∑ k ∈ (Finset.univ.erase i : Finset (Fin n)),
        wordEnergy (ebase n) (lweight) (coordWord α k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    rw [show coordWord (α * lamNeg i j hij) k = coordWord α k from
      congrArg FreeGroup.toWord (mul_lamNeg_apply_other (α := α) hij hki)]
  rw [hrest]
  ring

/-- **Energy update, `rhoNeg` move**: composing on the right by `rhoNeg i j`
changes only the `i`-th image, whose word becomes `W`. -/
lemma eEnergy_mul_rhoNeg {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (i j : Fin n)
    (hij : i ≠ j) (W : List (Fin n × Bool))
    (hW : coordWord (α * rhoNeg i j hij) i = W) :
    eEnergy (α * rhoNeg i j hij) + wordEnergy (ebase n) (lweight) (coordWord α i) =
      eEnergy α + wordEnergy (ebase n) (lweight) W := by
  rw [eEnergy_eq_sum_erase (α * rhoNeg i j hij) i, eEnergy_eq_sum_erase α i, hW]
  have hrest : (∑ k ∈ (Finset.univ.erase i : Finset (Fin n)),
      wordEnergy (ebase n) (lweight) (coordWord (α * rhoNeg i j hij) k)) =
      (∑ k ∈ (Finset.univ.erase i : Finset (Fin n)),
        wordEnergy (ebase n) (lweight) (coordWord α k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    rw [show coordWord (α * rhoNeg i j hij) k = coordWord α k from
      congrArg FreeGroup.toWord (mul_rhoNeg_apply_other (α := α) hij hki)]
  rw [hrest]
  ring

/-! ## The two energy-descending moves -/

/-- A basis image is no longer than the total length. -/
lemma norm_le_N {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (i : Fin n) :
    FreeGroup.norm (α (FreeGroup.of i)) ≤ N α := by
  rw [N_eq_sum]
  have h : (∑ k : Fin n, FreeGroup.norm (α (FreeGroup.of k))) =
      (∑ k ∈ (Finset.univ.erase i : Finset (Fin n)),
          FreeGroup.norm (α (FreeGroup.of k))) + FreeGroup.norm (α (FreeGroup.of i)) :=
    (Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun k => FreeGroup.norm (α (FreeGroup.of k))) (Finset.mem_univ i)).symm
  rw [h]
  exact Nat.le_add_left _ _

/-- **`rho` move (half-length 1).**  In a residual state, a row `v` whose word
is `X ++ invRev [a]` and a row `p` whose word is the two letters `[a] ++ [b]`:
if `lweight b < lweight a` then right-composing by `rho v p` preserves `N` and
strictly decreases the state energy. -/
theorem energy_step_rho {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (hres : NoEndCancel n α)
    {p v : Fin n} (hvp : v ≠ p) (a b : Fin n × Bool) (X : List (Fin n × Bool))
    (hba : b.1.val < a.1.val)
    (hp : coordWord α p = [a] ++ [b])
    (hv : coordWord α v = X ++ FreeGroup.invRev [a]) :
    eEnergy (α * rho v p hvp) < eEnergy α ∧ N (α * rho v p hvp) = N α := by
  have hp' : (α (FreeGroup.of p)).toWord = [a] ++ [b] := hp
  have hv' : (α (FreeGroup.of v)).toWord = X ++ FreeGroup.invRev [a] := hv
  have hel : (α * rho v p hvp) (FreeGroup.of v) = FreeGroup.mk (X ++ [b]) := by
    rw [mul_rho_apply_self]
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of v)),
      ← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hv', hp']
    exact mk_rho_word X a b
  have hW : coordWord (α * rho v p hvp) v = FreeGroup.reduce (X ++ [b]) := by
    show ((α * rho v p hvp) (FreeGroup.of v)).toWord = _
    rw [hel, FreeGroup.toWord_mk]
  have hlen1' : (coordWord (α * rho v p hvp) v).length ≤ X.length + 1 := by
    rw [hW]
    calc (FreeGroup.reduce (X ++ [b])).length ≤ (X ++ [b]).length := reduce_length_le _
      _ = X.length + 1 := by rw [List.length_append]; simp
  have hlen0 : (coordWord α v).length = X.length + 1 := by
    rw [hv, List.length_append, invRev_singleton, List.length_singleton]
  have hmin := (noEndCancel_iff_local_min n α).mp hres
  have hNle : N α ≤ N (α * rho v p hvp) := hmin.1 v p hvp
  have hNform := N_mul_rho α v p hvp
  have habs : FreeGroup.norm (α (FreeGroup.of v)) ≤
      FreeGroup.norm (α (FreeGroup.of v) * α (FreeGroup.of p)) :=
    (N_le_N_mul_rho_iff α v p hvp).mp hNle
  have hge : X.length + 1 ≤ (coordWord (α * rho v p hvp) v).length := by
    have h1 : FreeGroup.norm (α (FreeGroup.of v)) = X.length + 1 := hlen0
    have h2 : FreeGroup.norm (α (FreeGroup.of v) * α (FreeGroup.of p)) =
        (coordWord (α * rho v p hvp) v).length := by
      rw [← mul_rho_apply_self α v p hvp]
      rfl
    omega
  have hlen_eq : (coordWord (α * rho v p hvp) v).length = X.length + 1 :=
    le_antisymm hlen1' hge
  have hWeq : coordWord (α * rho v p hvp) v = X ++ [b] := by
    rw [hW]
    refine reduce_eq_of_length_eq (X ++ [b]) ?_
    rw [← hW, hlen_eq, List.length_append, List.length_singleton]
  have hNeq : N (α * rho v p hvp) = N α := by
    have h1 : FreeGroup.norm (α (FreeGroup.of v)) = X.length + 1 := hlen0
    have h2 : FreeGroup.norm (α (FreeGroup.of v) * α (FreeGroup.of p)) = X.length + 1 := by
      have hh : FreeGroup.norm (α (FreeGroup.of v) * α (FreeGroup.of p)) =
          (coordWord (α * rho v p hvp) v).length := by
        rw [← mul_rho_apply_self α v p hvp]
        rfl
      rw [hh, hlen_eq]
    have h3 : FreeGroup.norm (α (FreeGroup.of v) * α (FreeGroup.of p)) =
        FreeGroup.norm (α (FreeGroup.of v)) := by rw [h1, h2]
    rw [hNform, h3]
    exact Nat.sub_add_cancel (norm_le_N α v)
  refine ⟨?_, hNeq⟩
  have hEu := eEnergy_mul_rho α v p hvp (coordWord (α * rho v p hvp) v) rfl
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

/-- **`lam` move (half-length 1).**  In a residual state, a row `u` whose word
is `invRev [b] ++ Z` and a row `p` whose word is the two letters `[a] ++ [b]`:
if `lweight a < lweight b` then right-composing by `lam u p` preserves `N` and
strictly decreases the state energy. -/
theorem energy_step_lam {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (hres : NoEndCancel n α)
    {p u : Fin n} (hup : u ≠ p) (a b : Fin n × Bool) (Z : List (Fin n × Bool))
    (hab : a.1.val < b.1.val)
    (hp : coordWord α p = [a] ++ [b])
    (hu : coordWord α u = FreeGroup.invRev [b] ++ Z) :
    eEnergy (α * lam u p hup) < eEnergy α ∧ N (α * lam u p hup) = N α := by
  have hp' : (α (FreeGroup.of p)).toWord = [a] ++ [b] := hp
  have hu' : (α (FreeGroup.of u)).toWord = FreeGroup.invRev [b] ++ Z := hu
  have hel : (α * lam u p hup) (FreeGroup.of u) = FreeGroup.mk ([a] ++ Z) := by
    rw [mul_lam_apply_self]
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of p)),
      ← FreeGroup.mk_toWord (x := α (FreeGroup.of u)), hp', hu']
    exact mk_lam_word Z a b
  have hW : coordWord (α * lam u p hup) u = FreeGroup.reduce ([a] ++ Z) := by
    show ((α * lam u p hup) (FreeGroup.of u)).toWord = _
    rw [hel, FreeGroup.toWord_mk]
  have hlen1' : (coordWord (α * lam u p hup) u).length ≤ 1 + Z.length := by
    rw [hW]
    calc (FreeGroup.reduce ([a] ++ Z)).length ≤ ([a] ++ Z).length := reduce_length_le _
      _ = 1 + Z.length := by rw [List.length_append]; simp
  have hlen0 : (coordWord α u).length = 1 + Z.length := by
    rw [hu, List.length_append, invRev_singleton, List.length_singleton]
  have hmin := (noEndCancel_iff_local_min n α).mp hres
  have hNle : N α ≤ N (α * lam u p hup) := hmin.2.2.1 u p hup
  have hNform := N_mul_lam α u p hup
  have habs : FreeGroup.norm (α (FreeGroup.of u)) ≤
      FreeGroup.norm (α (FreeGroup.of p) * α (FreeGroup.of u)) :=
    (N_le_N_mul_lam_iff α u p hup).mp hNle
  have hge : 1 + Z.length ≤ (coordWord (α * lam u p hup) u).length := by
    have h1 : FreeGroup.norm (α (FreeGroup.of u)) = 1 + Z.length := hlen0
    have h2 : FreeGroup.norm (α (FreeGroup.of p) * α (FreeGroup.of u)) =
        (coordWord (α * lam u p hup) u).length := by
      rw [← mul_lam_apply_self α u p hup]
      rfl
    omega
  have hlen_eq : (coordWord (α * lam u p hup) u).length = 1 + Z.length :=
    le_antisymm hlen1' hge
  have hWeq : coordWord (α * lam u p hup) u = [a] ++ Z := by
    rw [hW]
    refine reduce_eq_of_length_eq ([a] ++ Z) ?_
    rw [← hW, hlen_eq, List.length_append, List.length_singleton]
  have hNeq : N (α * lam u p hup) = N α := by
    have h1 : FreeGroup.norm (α (FreeGroup.of u)) = 1 + Z.length := hlen0
    have h2 : FreeGroup.norm (α (FreeGroup.of p) * α (FreeGroup.of u)) = 1 + Z.length := by
      have hh : FreeGroup.norm (α (FreeGroup.of p) * α (FreeGroup.of u)) =
          (coordWord (α * lam u p hup) u).length := by
        rw [← mul_lam_apply_self α u p hup]
        rfl
      rw [hh, hlen_eq]
    have h3 : FreeGroup.norm (α (FreeGroup.of p) * α (FreeGroup.of u)) =
        FreeGroup.norm (α (FreeGroup.of u)) := by rw [h1, h2]
    rw [hNform, h3]
    exact Nat.sub_add_cancel (norm_le_N α u)
  refine ⟨?_, hNeq⟩
  have hEu := eEnergy_mul_lam α u p hup (coordWord (α * lam u p hup) u) rfl
  rw [hWeq, hu] at hEu
  have e1 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev [b] ++ Z) =
      (ebase n) ^ Z.length * lweight b + wordEnergy (ebase n) (lweight) Z := by
    rw [wordEnergy_append, wordEnergy_invRev_singleton]
  have e2 : wordEnergy (ebase n) (lweight) ([a] ++ Z) =
      (ebase n) ^ Z.length * lweight a + wordEnergy (ebase n) (lweight) Z := by
    rw [wordEnergy_append, wordEnergy_singleton]
  have hlt : wordEnergy (ebase n) (lweight) ([a] ++ Z) <
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev [b] ++ Z) := by
    have hw : lweight a < lweight b := by unfold lweight; omega
    have hpos := pow_ebase_pos (n := n) Z.length
    rw [e1, e2]
    have hmul : (ebase n) ^ Z.length * lweight a < (ebase n) ^ Z.length * lweight b :=
      Nat.mul_lt_mul_of_pos_left hw hpos
    omega
  omega

/-- **The half-length-1 energy step.**  For a residual state, a row `p` with
two distinct-letters word `[a] ++ [b]`, a row `v` ending with `invRev [a]` and
a row `u` beginning with `invRev [b]`, one of the two elementary transvections
`rho v p` / `lam u p` preserves `N` and strictly decreases the energy — i.e.
the balanced-side move of the classical reduction exists at half-length 1. -/
theorem energy_step_k1 {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (hres : NoEndCancel n α)
    {p v u : Fin n} (hvp : v ≠ p) (hup : u ≠ p) (a b : Fin n × Bool)
    (X Z : List (Fin n × Bool)) (hab : a.1 ≠ b.1)
    (hp : coordWord α p = [a] ++ [b])
    (hv : coordWord α v = X ++ FreeGroup.invRev [a])
    (hu : coordWord α u = FreeGroup.invRev [b] ++ Z) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) ≤ N α ∧ eEnergy (α * γ) < eEnergy α := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · rcases energy_step_lam α hres hup a b Z hlt hp hu with ⟨hE, hN⟩
    exact ⟨lam u p hup, Subgroup.subset_closure (lam_mem_AutGen n hup), le_of_eq hN, hE⟩
  · rcases energy_step_rho α hres hvp a b X hgt hp hv with ⟨hE, hN⟩
    exact ⟨rho v p hvp, Subgroup.subset_closure (rho_mem_AutGen n hvp), le_of_eq hN, hE⟩

/-- Splitting a product of two `mk`s (element-level), with explicit lists. -/
lemma mk_mul_eq {n : ℕ} (A B : List (Fin n × Bool)) :
    FreeGroup.mk (A ++ B) = FreeGroup.mk A * FreeGroup.mk B :=
  (FreeGroup.mul_mk (L₁ := A) (L₂ := B)).symm

/-- Word identity for the `lamNeg` move: `(invRev [a]) · ([a] ++ invRev X) = invRev X`
at the element level. -/
lemma mk_lamNeg_atom {n : ℕ} (X : List (Fin n × Bool)) (a : Fin n × Bool) :
    (FreeGroup.mk [a])⁻¹ * FreeGroup.mk ([a] ++ FreeGroup.invRev X) =
      FreeGroup.mk (FreeGroup.invRev X) := by
  have h : (FreeGroup.mk [a])⁻¹ = FreeGroup.mk (FreeGroup.invRev [a]) := FreeGroup.inv_mk
  rw [h]
  exact mul_mk_invRev_prefix (P := FreeGroup.invRev X) (L := [a])

/-- Word identity for the `rhoNeg` move: `(invRev Z ++ [b]) · [b]⁻¹ = invRev Z`
at the element level. -/
lemma mk_rhoNeg_atom {n : ℕ} (Z : List (Fin n × Bool)) (b : Fin n × Bool) :
    FreeGroup.mk (FreeGroup.invRev Z ++ [b]) * (FreeGroup.mk [b])⁻¹ =
      FreeGroup.mk (FreeGroup.invRev Z) := by
  have h : FreeGroup.mk (FreeGroup.invRev Z ++ [b]) =
      FreeGroup.mk (FreeGroup.invRev Z) * FreeGroup.mk [b] := mk_mul_eq _ _
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

/-- Word identity for the `lamNeg` move applied at the balanced row: the new
element `w_p⁻¹ · w_v` has word `invRev [b] ++ invRev X`. -/
lemma mk_lamNeg_word {n : ℕ} (X : List (Fin n × Bool)) (a b : Fin n × Bool) :
    (FreeGroup.mk ([a] ++ [b]))⁻¹ * FreeGroup.mk ([a] ++ FreeGroup.invRev X) =
      FreeGroup.mk (FreeGroup.invRev [b] ++ FreeGroup.invRev X) := by
  have h1 : (FreeGroup.mk ([a] ++ [b]))⁻¹ =
      (FreeGroup.mk [b])⁻¹ * (FreeGroup.mk [a])⁻¹ := by
    rw [mk_mul_eq [a] [b], mul_inv_rev]
  have h2 : (FreeGroup.mk [b])⁻¹ = FreeGroup.mk (FreeGroup.invRev [b]) := FreeGroup.inv_mk
  rw [h1, h2, mul_assoc, mk_lamNeg_atom X a, mk_mul_eq (FreeGroup.invRev [b])
    (FreeGroup.invRev X)]

/-- Word identity for the `rhoNeg` move applied at the balanced row: the new
element `w_u · w_p⁻¹` has word `invRev Z ++ invRev [a]`. -/
lemma mk_rhoNeg_word {n : ℕ} (Z : List (Fin n × Bool)) (a b : Fin n × Bool) :
    FreeGroup.mk (FreeGroup.invRev Z ++ [b]) * (FreeGroup.mk ([a] ++ [b]))⁻¹ =
      FreeGroup.mk (FreeGroup.invRev Z ++ FreeGroup.invRev [a]) := by
  have h1 : (FreeGroup.mk ([a] ++ [b]))⁻¹ =
      (FreeGroup.mk [b])⁻¹ * (FreeGroup.mk [a])⁻¹ := by
    rw [mk_mul_eq [a] [b], mul_inv_rev]
  have h2 : (FreeGroup.mk [b])⁻¹ = FreeGroup.mk (FreeGroup.invRev [b]) := FreeGroup.inv_mk
  have h3 : (FreeGroup.mk [a])⁻¹ = FreeGroup.mk (FreeGroup.invRev [a]) := FreeGroup.inv_mk
  rw [h1, h2, h3, ← mul_assoc]
  rw [show FreeGroup.mk (FreeGroup.invRev Z ++ [b]) * FreeGroup.mk (FreeGroup.invRev [b]) =
      FreeGroup.mk (FreeGroup.invRev Z) from mk_rhoNeg_atom Z b]
  rw [mk_mul_eq (FreeGroup.invRev Z) (FreeGroup.invRev [a])]

/-- **`lamNeg` move (half-length 1).**  Left neighbour factor of the *negative*
orientation: the row `v` has word `[a] ++ invRev X`; if `lweight b < lweight a`
then right-composing by `lamNeg v p` preserves `N` and strictly decreases the
energy. -/
theorem energy_step_lamNeg {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (hres : NoEndCancel n α)
    {p v : Fin n} (hvp : v ≠ p) (a b : Fin n × Bool) (X : List (Fin n × Bool))
    (hba : b.1.val < a.1.val)
    (hp : coordWord α p = [a] ++ [b])
    (hv : coordWord α v = [a] ++ FreeGroup.invRev X) :
    eEnergy (α * lamNeg v p hvp) < eEnergy α ∧ N (α * lamNeg v p hvp) = N α := by
  have hp' : (α (FreeGroup.of p)).toWord = [a] ++ [b] := hp
  have hv' : (α (FreeGroup.of v)).toWord = [a] ++ FreeGroup.invRev X := hv
  have hel : (α * lamNeg v p hvp) (FreeGroup.of v) =
      FreeGroup.mk (FreeGroup.invRev [b] ++ FreeGroup.invRev X) := by
    rw [mul_lamNeg_apply_self]
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of v)),
      ← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hv', hp']
    exact mk_lamNeg_word X a b
  have hW : coordWord (α * lamNeg v p hvp) v =
      FreeGroup.reduce (FreeGroup.invRev [b] ++ FreeGroup.invRev X) := by
    show ((α * lamNeg v p hvp) (FreeGroup.of v)).toWord = _
    rw [hel, FreeGroup.toWord_mk]
  have hlen1' : (coordWord (α * lamNeg v p hvp) v).length ≤ 1 + X.length := by
    rw [hW]
    calc (FreeGroup.reduce (FreeGroup.invRev [b] ++ FreeGroup.invRev X)).length
        ≤ (FreeGroup.invRev [b] ++ FreeGroup.invRev X).length := reduce_length_le _
      _ = 1 + X.length := by
          rw [List.length_append, invRev_singleton, List.length_singleton,
            FreeGroup.invRev_length]
  have hlen0 : (coordWord α v).length = 1 + X.length := by
    rw [hv, List.length_append, List.length_singleton, FreeGroup.invRev_length]
  have hmin := (noEndCancel_iff_local_min n α).mp hres
  have hNle : N α ≤ N (α * lamNeg v p hvp) := hmin.2.2.2 v p hvp
  have hNform := N_mul_lamNeg α v p hvp
  have habs : FreeGroup.norm (α (FreeGroup.of v)) ≤
      FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * α (FreeGroup.of v)) :=
    (N_le_N_mul_lamNeg_iff α v p hvp).mp hNle
  have hge : 1 + X.length ≤ (coordWord (α * lamNeg v p hvp) v).length := by
    have h1 : FreeGroup.norm (α (FreeGroup.of v)) = 1 + X.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * α (FreeGroup.of v)) =
        (coordWord (α * lamNeg v p hvp) v).length := by
      rw [← mul_lamNeg_apply_self α v p hvp]
      rfl
    omega
  have hlen_eq : (coordWord (α * lamNeg v p hvp) v).length = 1 + X.length :=
    le_antisymm hlen1' hge
  have hWeq : coordWord (α * lamNeg v p hvp) v =
      FreeGroup.invRev [b] ++ FreeGroup.invRev X := by
    rw [hW]
    refine reduce_eq_of_length_eq (FreeGroup.invRev [b] ++ FreeGroup.invRev X) ?_
    rw [← hW, hlen_eq, List.length_append, invRev_singleton, List.length_singleton,
      FreeGroup.invRev_length]
  have hNeq : N (α * lamNeg v p hvp) = N α := by
    have h1 : FreeGroup.norm (α (FreeGroup.of v)) = 1 + X.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * α (FreeGroup.of v)) =
        1 + X.length := by
      have hh : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * α (FreeGroup.of v)) =
          (coordWord (α * lamNeg v p hvp) v).length := by
        rw [← mul_lamNeg_apply_self α v p hvp]
        rfl
      rw [hh, hlen_eq]
    have h3 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * α (FreeGroup.of v)) =
        FreeGroup.norm (α (FreeGroup.of v)) := by rw [h1, h2]
    rw [hNform, h3]
    exact Nat.sub_add_cancel (norm_le_N α v)
  refine ⟨?_, hNeq⟩
  have hEu := eEnergy_mul_lamNeg α v p hvp (coordWord (α * lamNeg v p hvp) v) rfl
  rw [hWeq, hv] at hEu
  have e1 : wordEnergy (ebase n) (lweight) ([a] ++ FreeGroup.invRev X) =
      (ebase n) ^ X.length * lweight a + wordEnergy (ebase n) (lweight) (FreeGroup.invRev X) := by
    rw [wordEnergy_append, wordEnergy_singleton, FreeGroup.invRev_length]
  have e2 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev [b] ++ FreeGroup.invRev X) =
      (ebase n) ^ X.length * lweight b + wordEnergy (ebase n) (lweight) (FreeGroup.invRev X) := by
    rw [wordEnergy_append, wordEnergy_invRev_singleton, FreeGroup.invRev_length]
  have hlt : wordEnergy (ebase n) (lweight) (FreeGroup.invRev [b] ++ FreeGroup.invRev X) <
      wordEnergy (ebase n) (lweight) ([a] ++ FreeGroup.invRev X) := by
    have hw : lweight b < lweight a := by unfold lweight; omega
    have hpos := pow_ebase_pos (n := n) X.length
    rw [e1, e2]
    have hmul : (ebase n) ^ X.length * lweight b < (ebase n) ^ X.length * lweight a :=
      Nat.mul_lt_mul_of_pos_left hw hpos
    omega
  omega

/-- **`rhoNeg` move (half-length 1).**  Right neighbour factor of the *negative*
orientation: the row `u` has word `invRev Z ++ [b]`; if `lweight a < lweight b`
then right-composing by `rhoNeg u p` preserves `N` and strictly decreases the
energy. -/
theorem energy_step_rhoNeg {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (hres : NoEndCancel n α)
    {p u : Fin n} (hup : u ≠ p) (a b : Fin n × Bool) (Z : List (Fin n × Bool))
    (hab : a.1.val < b.1.val)
    (hp : coordWord α p = [a] ++ [b])
    (hu : coordWord α u = FreeGroup.invRev Z ++ [b]) :
    eEnergy (α * rhoNeg u p hup) < eEnergy α ∧ N (α * rhoNeg u p hup) = N α := by
  have hp' : (α (FreeGroup.of p)).toWord = [a] ++ [b] := hp
  have hu' : (α (FreeGroup.of u)).toWord = FreeGroup.invRev Z ++ [b] := hu
  have hel : (α * rhoNeg u p hup) (FreeGroup.of u) =
      FreeGroup.mk (FreeGroup.invRev Z ++ FreeGroup.invRev [a]) := by
    rw [mul_rhoNeg_apply_self]
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of u)),
      ← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hu', hp']
    exact mk_rhoNeg_word Z a b
  have hW : coordWord (α * rhoNeg u p hup) u =
      FreeGroup.reduce (FreeGroup.invRev Z ++ FreeGroup.invRev [a]) := by
    show ((α * rhoNeg u p hup) (FreeGroup.of u)).toWord = _
    rw [hel, FreeGroup.toWord_mk]
  have hlen1' : (coordWord (α * rhoNeg u p hup) u).length ≤ Z.length + 1 := by
    rw [hW]
    calc (FreeGroup.reduce (FreeGroup.invRev Z ++ FreeGroup.invRev [a])).length
        ≤ (FreeGroup.invRev Z ++ FreeGroup.invRev [a]).length := reduce_length_le _
      _ = Z.length + 1 := by
          rw [List.length_append, invRev_singleton, List.length_singleton,
            FreeGroup.invRev_length]
  have hlen0 : (coordWord α u).length = Z.length + 1 := by
    rw [hu, List.length_append, List.length_singleton, FreeGroup.invRev_length]
  have hmin := (noEndCancel_iff_local_min n α).mp hres
  have hNle : N α ≤ N (α * rhoNeg u p hup) := hmin.2.1 u p hup
  have hNform := N_mul_rhoNeg α u p hup
  have habs : FreeGroup.norm (α (FreeGroup.of u)) ≤
      FreeGroup.norm (α (FreeGroup.of u) * (α (FreeGroup.of p))⁻¹) :=
    (N_le_N_mul_rhoNeg_iff α u p hup).mp hNle
  have hge : Z.length + 1 ≤ (coordWord (α * rhoNeg u p hup) u).length := by
    have h1 : FreeGroup.norm (α (FreeGroup.of u)) = Z.length + 1 := hlen0
    have h2 : FreeGroup.norm (α (FreeGroup.of u) * (α (FreeGroup.of p))⁻¹) =
        (coordWord (α * rhoNeg u p hup) u).length := by
      rw [← mul_rhoNeg_apply_self α u p hup]
      rfl
    omega
  have hlen_eq : (coordWord (α * rhoNeg u p hup) u).length = Z.length + 1 :=
    le_antisymm hlen1' hge
  have hWeq : coordWord (α * rhoNeg u p hup) u =
      FreeGroup.invRev Z ++ FreeGroup.invRev [a] := by
    rw [hW]
    refine reduce_eq_of_length_eq (FreeGroup.invRev Z ++ FreeGroup.invRev [a]) ?_
    rw [← hW, hlen_eq, List.length_append, invRev_singleton, List.length_singleton,
      FreeGroup.invRev_length]
  have hNeq : N (α * rhoNeg u p hup) = N α := by
    have h1 : FreeGroup.norm (α (FreeGroup.of u)) = Z.length + 1 := hlen0
    have h2 : FreeGroup.norm (α (FreeGroup.of u) * (α (FreeGroup.of p))⁻¹) =
        Z.length + 1 := by
      have hh : FreeGroup.norm (α (FreeGroup.of u) * (α (FreeGroup.of p))⁻¹) =
          (coordWord (α * rhoNeg u p hup) u).length := by
        rw [← mul_rhoNeg_apply_self α u p hup]
        rfl
      rw [hh, hlen_eq]
    have h3 : FreeGroup.norm (α (FreeGroup.of u) * (α (FreeGroup.of p))⁻¹) =
        FreeGroup.norm (α (FreeGroup.of u)) := by rw [h1, h2]
    rw [hNform, h3]
    exact Nat.sub_add_cancel (norm_le_N α u)
  refine ⟨?_, hNeq⟩
  have hEu := eEnergy_mul_rhoNeg α u p hup (coordWord (α * rhoNeg u p hup) u) rfl
  rw [hWeq, hu] at hEu
  have e1 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z ++ [b]) =
      (ebase n) ^ 1 * wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z) + lweight b := by
    rw [wordEnergy_append, wordEnergy_singleton]
    simp
  have e2 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z ++ FreeGroup.invRev [a]) =
      (ebase n) ^ 1 * wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z) + lweight a := by
    rw [wordEnergy_append, wordEnergy_invRev_singleton]
    simp
  have hlt : wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z ++ FreeGroup.invRev [a]) <
      wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z ++ [b]) := by
    have hw : lweight a < lweight b := by unfold lweight; omega
    rw [e1, e2]
    omega
  omega

/-- **The half-length-1 energy step, in covering form.**  It suffices that the
two neighbours *cover* the balanced row in either orientation: a row `v` whose
word is `X ++ invRev [a]` (ends with the inverse of the first half) or
`[a] ++ invRev X` (starts with the first half), and a row `u` whose word is
`invRev [b] ++ Z` (starts with the inverse of the second half) or
`invRev Z ++ [b]` (ends with the second half).  Whichever of `lweight b <
lweight a` / `lweight a < lweight b` holds, the corresponding neighbour
supplies the energy-descending move. -/
theorem energy_step_k1_cover {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p v u : Fin n} (hvp : v ≠ p) (hup : u ≠ p)
    (a b : Fin n × Bool) (X Z : List (Fin n × Bool)) (hab : a.1 ≠ b.1)
    (hp : coordWord α p = [a] ++ [b])
    (hv : coordWord α v = X ++ FreeGroup.invRev [a] ∨
      coordWord α v = [a] ++ FreeGroup.invRev X)
    (hu : coordWord α u = FreeGroup.invRev [b] ++ Z ∨
      coordWord α u = FreeGroup.invRev Z ++ [b]) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) ≤ N α ∧ eEnergy (α * γ) < eEnergy α := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · rcases hu with hu | hu
    · rcases energy_step_lam α hres hup a b Z hlt hp hu with ⟨hE, hN⟩
      exact ⟨lam u p hup, Subgroup.subset_closure (lam_mem_AutGen n hup), le_of_eq hN, hE⟩
    · rcases energy_step_rhoNeg α hres hup a b Z hlt hp hu with ⟨hE, hN⟩
      exact ⟨rhoNeg u p hup, Subgroup.subset_closure (rhoNeg_mem_AutGen n hup),
        le_of_eq hN, hE⟩
  · rcases hv with hv | hv
    · rcases energy_step_rho α hres hvp a b X hgt hp hv with ⟨hE, hN⟩
      exact ⟨rho v p hvp, Subgroup.subset_closure (rho_mem_AutGen n hvp), le_of_eq hN, hE⟩
    · rcases energy_step_lamNeg α hres hvp a b X hgt hp hv with ⟨hE, hN⟩
      refine ⟨lamNeg v p hvp, ?_, le_of_eq hN, hE⟩
      rw [← lam_inv_eq v p hvp]
      exact (AutClosure n).inv_mem (Subgroup.subset_closure (lam_mem_AutGen n hvp))

end Submission.Nielsen
