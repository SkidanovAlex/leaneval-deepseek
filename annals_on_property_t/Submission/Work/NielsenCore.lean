import Submission.Work.Nielsen
import Submission.Commons.GroupTheory.FreeGroup.norm_mul_cancel_last
import Submission.Commons.GroupTheory.FreeGroup.norm_mul_le_sub_two
import Submission.Commons.GroupTheory.FreeGroup.reduce_append_reduce
import Submission.Commons.GroupTheory.FreeGroup.reduce_invRev_append_self
import Submission.Commons.GroupTheory.FreeGroup.reduce_append_no_junction
import Submission.Commons.GroupTheory.FreeGroup.norm_mul_cancel_head
import Mathlib.GroupTheory.FreeGroup.Reduce

open Submission.FreeGroupAut
set_option autoImplicit false

/-!
# The combinatorial core of Nielsen's reduction

The induction step of Nielsen's theorem is reduced by `N_mul_rho` to the
following concrete question about reduced words: for the basis images
`wᵢ = α(xᵢ)` (each already reduced), if the tuple is not a signed permutation
then some pair `(i,j)` (or the sibling moves with `w_j⁻¹` and left
multiplication) satisfies `|wᵢ · wⱼ| < |wᵢ|`, in which case right composition
with the corresponding elementary generator strictly decreases `N`.

This file collects the letter-level machinery: first/last letters of reduced
words, and the cancellation lemmas relating `|u·v|` to the letters of `u`, `v`.
The generic word lemmas `norm_mul_cancel_last` and `norm_mul_le_sub_two` live
in the shared commons (fleet-proven); this file contains the local statements
that consume them.
-/

namespace Submission.Nielsen

noncomputable section

open scoped BigOperators
open FreeGroup

/-- First letter of the reduced word representing `x`. -/
def firstLetter {n : ℕ} (x : FreeGroup (Fin n)) : Option (Fin n × Bool) :=
  (FreeGroup.toWord x).head?

/-- Last letter of the reduced word representing `x`. -/
def lastLetter {n : ℕ} (x : FreeGroup (Fin n)) : Option (Fin n × Bool) :=
  (FreeGroup.toWord x).getLast?

/-- If the reduced word of `w` ends in `(a, c)`, then multiplying on the right
by the single letter of opposite parity cancels exactly that last letter. -/
lemma norm_mul_single_cancel {n : ℕ} (w : FreeGroup (Fin n)) (a : Fin n) (c : Bool)
    (L : List (Fin n × Bool)) :
    FreeGroup.toWord w = L ++ [(a, c)] →
    FreeGroup.norm (w * (if c then (FreeGroup.of a)⁻¹ else FreeGroup.of a)) =
      FreeGroup.norm w - 1 := by
  intro h
  exact Commons.GroupTheory.FreeGroup.norm_mul_cancel_last w a c L h

/-- A reduced word of positive length has positive norm. -/
lemma norm_pos_of_ne_one {n : ℕ} {w : FreeGroup (Fin n)} (hw : w ≠ 1) : 0 < FreeGroup.norm w := by
  by_contra h
  have h0 : FreeGroup.norm w = 0 := by omega
  exact hw (FreeGroup.norm_eq_zero.mp h0)

/-- The single-letter shortening step: if the image `w_j` of some generator is
the single letter inverse of the last letter of `w_i` (`i ≠ j`), then right
composition with `rho i j` strictly decreases the total length. -/
lemma single_letter_shortens {n : ℕ} (α : MulAut (FreeGroup (Fin n))) {i j : Fin n} (hij : i ≠ j)
    (a : Fin n) (c : Bool)
    (hwi : FreeGroup.toWord (α (FreeGroup.of i)) =
      (FreeGroup.toWord (α (FreeGroup.of i))).dropLast ++ [(a, c)])
    (hwj : FreeGroup.toWord (α (FreeGroup.of j)) = [(a, !c)]) :
    N (α * rho i j hij) < N α := by
  classical
  have hwjf : α (FreeGroup.of j) =
      (if c then (FreeGroup.of a)⁻¹ else FreeGroup.of a) := by
    exact (FreeGroup.toWord_inj).mp (by
      rw [hwj]
      cases c <;> simp [FreeGroup.toWord_inv, FreeGroup.invRev])
  have hcancel : FreeGroup.norm ((α (FreeGroup.of i)) * (α (FreeGroup.of j))) =
      FreeGroup.norm (α (FreeGroup.of i)) - 1 := by
    rw [hwjf]
    exact norm_mul_single_cancel (α (FreeGroup.of i)) a c
      (FreeGroup.toWord (α (FreeGroup.of i))).dropLast hwi
  have hN := N_mul_rho α i j hij
  rw [hN, hcancel]
  have hw_le : FreeGroup.norm (α (FreeGroup.of i)) ≤ N α := by
    rw [N_eq_sum]
    have hs := (Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun k : Fin n => FreeGroup.norm (α (FreeGroup.of k))) (Finset.mem_univ i))
    rw [← hs]
    exact Nat.le_add_left _ _
  have hpos : 0 < FreeGroup.norm (α (FreeGroup.of i)) := by
    apply norm_pos_of_ne_one
    intro h1
    have hw : FreeGroup.toWord (1 : FreeGroup (Fin n)) = [] := by simp
    rw [h1] at hwi
    rw [hw] at hwi
    simp at hwi
  omega
/-- Multi-letter absorption: if the reduced word of `w_i` ends with the reduced
word of `w_j⁻¹` (i.e. `toWord w_i = U ++ invRev (toWord w_j)` for some reduced
`U`), then `|w_i * w_j| = |w_i| - |w_j|`.  Consumes the commons lemmas
`reduce_append_reduce` and `reduce_invRev_append_self`. -/
lemma norm_mul_absorb_tail {n : ℕ} (w_i w_j : FreeGroup (Fin n))
    (hU : ∃ U : List (Fin n × Bool), FreeGroup.IsReduced U
      ∧ FreeGroup.toWord w_i = U ++ FreeGroup.invRev (FreeGroup.toWord w_j)) :
    FreeGroup.norm (w_i * w_j) = FreeGroup.norm w_i - FreeGroup.norm w_j := by
  classical
  rcases hU with ⟨U, hUred, hwi⟩
  let W := FreeGroup.toWord w_j
  have hWred : FreeGroup.IsReduced W := FreeGroup.IsReduced.of_reduce_eq (FreeGroup.reduce_toWord w_j)
  have hlen_wi : FreeGroup.norm w_i = U.length + W.length := by
    calc
      FreeGroup.norm w_i = (FreeGroup.toWord w_i).length := rfl
      _ = (U ++ FreeGroup.invRev W).length := by rw [hwi]
      _ = U.length + W.length := by simp [FreeGroup.invRev_length]
  have hlen_wj : FreeGroup.norm w_j = W.length := rfl
  have hmid : FreeGroup.reduce (U ++ (FreeGroup.invRev W ++ W)) = U := by
    calc
      FreeGroup.reduce (U ++ (FreeGroup.invRev W ++ W))
          = FreeGroup.reduce (FreeGroup.reduce U ++ FreeGroup.reduce (FreeGroup.invRev W ++ W)) := by
              rw [Commons.GroupTheory.FreeGroup.reduce_append_reduce U (FreeGroup.invRev W ++ W)]
      _ = FreeGroup.reduce (FreeGroup.reduce U ++ []) := by
              rw [Commons.GroupTheory.FreeGroup.reduce_invRev_append_self W hWred]
      _ = FreeGroup.reduce (FreeGroup.reduce U) := by
              rw [List.append_nil]
      _ = U := by
              rw [FreeGroup.IsReduced.reduce_eq hUred]
              rw [FreeGroup.IsReduced.reduce_eq hUred]
  have hprod : FreeGroup.norm (w_i * w_j) = U.length := by
    calc
      FreeGroup.norm (w_i * w_j) = (FreeGroup.toWord (w_i * w_j)).length := rfl
      _ = (FreeGroup.reduce (FreeGroup.toWord w_i ++ FreeGroup.toWord w_j)).length := by
              rw [FreeGroup.toWord_mul]
      _ = (FreeGroup.reduce (U ++ (FreeGroup.invRev W ++ W))).length := by
              congr 1
              rw [hwi]
              rw [List.append_assoc]
      _ = U.length := by rw [hmid]
  omega

/-- Multi-letter absorption step: if the image of `x_j` is absorbed (its inverse
spells the tail of the image of `x_i`, `i ≠ j`), then right composition with
`rho i j` strictly decreases the total length. -/
lemma multi_letter_absorb_shortens {n : ℕ} (α : MulAut (FreeGroup (Fin n))) {i j : Fin n}
    (hij : i ≠ j)
    (hU : ∃ U : List (Fin n × Bool), FreeGroup.IsReduced U
      ∧ FreeGroup.toWord (α (FreeGroup.of i)) =
          U ++ FreeGroup.invRev (FreeGroup.toWord (α (FreeGroup.of j))))
    (hwj : α (FreeGroup.of j) ≠ 1) :
    N (α * rho i j hij) < N α := by
  classical
  rcases hU with ⟨U, hUred, hwi⟩
  have habs := norm_mul_absorb_tail (α (FreeGroup.of i)) (α (FreeGroup.of j)) ⟨U, hUred, hwi⟩
  have hlen : FreeGroup.norm (α (FreeGroup.of i)) = U.length + FreeGroup.norm (α (FreeGroup.of j)) := by
    calc
      FreeGroup.norm (α (FreeGroup.of i)) = (FreeGroup.toWord (α (FreeGroup.of i))).length := rfl
      _ = (U ++ FreeGroup.invRev (FreeGroup.toWord (α (FreeGroup.of j)))).length := by rw [hwi]
      _ = U.length + (FreeGroup.toWord (α (FreeGroup.of j))).length := by
              simp [FreeGroup.invRev_length]
      _ = U.length + FreeGroup.norm (α (FreeGroup.of j)) := rfl
  have hwj_le_wi : FreeGroup.norm (α (FreeGroup.of j)) ≤ FreeGroup.norm (α (FreeGroup.of i)) := by
    omega
  have hwj_pos : 0 < FreeGroup.norm (α (FreeGroup.of j)) := norm_pos_of_ne_one hwj
  have hterm_le : ∀ k : Fin n, FreeGroup.norm (α (FreeGroup.of k)) ≤ N α := by
    intro k
    rw [N_eq_sum]
    have hs := (Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun t : Fin n => FreeGroup.norm (α (FreeGroup.of t))) (Finset.mem_univ k))
    rw [← hs]
    exact Nat.le_add_left _ _
  have hwi_le := hterm_le i
  have hwj_le := hterm_le j
  have hN := N_mul_rho α i j hij
  have hsub : N α - FreeGroup.norm (α (FreeGroup.of i))
        + (FreeGroup.norm (α (FreeGroup.of i)) - FreeGroup.norm (α (FreeGroup.of j)))
      = N α - FreeGroup.norm (α (FreeGroup.of j)) := by
    exact Nat.sub_add_sub_cancel hwi_le hwj_le_wi
  rw [hN, habs, hsub]
  omega
/-- First no-shortening orientation of the boundary-letter analysis: if the last
letter of `w_i` is NOT the inverse of the first letter of `w_j`, then no
junction cancellation occurs, so `|w_i * w_j| = |w_i| + |w_j|` (in particular
the right transvection `rho i j` does not shorten `w_i`). -/
lemma norm_mul_eq_add_of_no_junction_cancel {n : ℕ} (w_i w_j : FreeGroup (Fin n))
    (a : Fin n) (c : Bool) (b : Fin n) (d : Bool)
    (L : List (Fin n × Bool)) (M : List (Fin n × Bool))
    (hwi : FreeGroup.toWord w_i = L ++ [(a, c)])
    (hwj : FreeGroup.toWord w_j = (b, d) :: M)
    (hnc : (a, c) ≠ (b, !d)) :
    FreeGroup.norm (w_i * w_j) = FreeGroup.norm w_i + FreeGroup.norm w_j := by
  classical
  have hXred : FreeGroup.IsReduced (FreeGroup.toWord w_i) :=
    FreeGroup.IsReduced.of_reduce_eq (FreeGroup.reduce_toWord w_i)
  have hYred : FreeGroup.IsReduced (FreeGroup.toWord w_j) :=
    FreeGroup.IsReduced.of_reduce_eq (FreeGroup.reduce_toWord w_j)
  have hj : ∀ (a' : Fin n) (b' : Bool),
      List.getLast? (FreeGroup.toWord w_i) = some (a', b') →
      List.head? (FreeGroup.toWord w_j) = some (a', !b') → False := by
    intro a' b' hl hh
    have hlEq : some (a, c) = some (a', b') := by
      simpa [hwi] using hl
    have hhEq : some (b, d) = some (a', !b') := by
      simpa [hwj] using hh
    have hpair1 : (a, c) = (a', b') := Option.some.inj hlEq
    have hpair2 : (b, d) = (a', !b') := Option.some.inj hhEq
    have hneed : (a, c) = (b, !d) := by
      have ha' : a = a' := congrArg Prod.fst hpair1
      have hc : c = b' := congrArg Prod.snd hpair1
      have hb : b = a' := congrArg Prod.fst hpair2
      have hd : d = !b' := congrArg Prod.snd hpair2
      rw [ha', hb, hc, hd]
      simp
    exact hnc hneed
  have hred : FreeGroup.reduce (FreeGroup.toWord w_i ++ FreeGroup.toWord w_j)
      = FreeGroup.toWord w_i ++ FreeGroup.toWord w_j := by
    exact Commons.GroupTheory.FreeGroup.reduce_append_no_junction
      (FreeGroup.toWord w_i) (FreeGroup.toWord w_j) hXred hYred hj
  have htw : FreeGroup.toWord (w_i * w_j) = (L ++ [(a, c)]) ++ ((b, d) :: M) := by
    calc
      FreeGroup.toWord (w_i * w_j) = FreeGroup.reduce (FreeGroup.toWord w_i ++ FreeGroup.toWord w_j) :=
              FreeGroup.toWord_mul w_i w_j
      _ = FreeGroup.toWord w_i ++ FreeGroup.toWord w_j := hred
      _ = (L ++ [(a, c)]) ++ ((b, d) :: M) := by rw [hwi, hwj]
  calc
    FreeGroup.norm (w_i * w_j) = (FreeGroup.toWord (w_i * w_j)).length := by
            simp [FreeGroup.norm]
    _ = ((L ++ [(a, c)]) ++ ((b, d) :: M)).length := by rw [htw]
    _ = FreeGroup.norm w_i + FreeGroup.norm w_j := by
            simp [FreeGroup.norm, hwi, hwj, List.length_append]
            omega

/-- The contrapositive of the first orientation: if a right transvection shortens
(`|w_i * w_j| < |w_i|`), then the last letter of `w_i` is the inverse of the
first letter of `w_j`. -/
lemma shorten_forces_inverse_first_last {n : ℕ} (w_i w_j : FreeGroup (Fin n))
    (a : Fin n) (c : Bool) (b : Fin n) (d : Bool)
    (L : List (Fin n × Bool)) (M : List (Fin n × Bool))
    (hwi : FreeGroup.toWord w_i = L ++ [(a, c)])
    (hwj : FreeGroup.toWord w_j = (b, d) :: M)
    (hshort : FreeGroup.norm (w_i * w_j) < FreeGroup.norm w_i) :
    (a, c) = (b, !d) := by
  by_contra h
  have hadd := norm_mul_eq_add_of_no_junction_cancel w_i w_j a c b d L M hwi hwj h
  -- |w_i * w_j| = |w_i| + |w_j| ≥ |w_i|, contradicting the strict inequality
  omega
/-- Sibling orientation (left transvection): if the image `w_j` is the single
letter inverse of the FIRST letter of `w_i` (`i ≠ j`), then left composition
with `lam i j` (i.e. replacing `w_i` by `w_j * w_i`) cancels that first letter
and strictly decreases the total length. -/
lemma single_letter_left_shortens {n : ℕ} (α : MulAut (FreeGroup (Fin n))) {i j : Fin n}
    (hij : i ≠ j) (a : Fin n) (c : Bool) (M : List (Fin n × Bool))
    (hwi : FreeGroup.toWord (α (FreeGroup.of i)) = (a, !c) :: M)
    (hwj : FreeGroup.toWord (α (FreeGroup.of j)) = [(a, c)]) :
    N (α * lam i j hij) < N α := by
  classical
  have hwjf : α (FreeGroup.of j) =
      (if !c then (FreeGroup.of a)⁻¹ else FreeGroup.of a) := by
    exact (FreeGroup.toWord_inj).mp (by
      rw [hwj]
      cases c <;> simp [FreeGroup.toWord_inv, FreeGroup.invRev])
  have hcancel : FreeGroup.norm ((α (FreeGroup.of j)) * (α (FreeGroup.of i))) =
      FreeGroup.norm (α (FreeGroup.of i)) - 1 := by
    rw [hwjf]
    exact Commons.GroupTheory.FreeGroup.norm_mul_cancel_head
      (α (FreeGroup.of i)) a (!c) M hwi
  have hne : α (FreeGroup.of i) ≠ 1 := by
    intro h
    have hw : FreeGroup.toWord (1 : FreeGroup (Fin n)) = [] := by simp
    rw [h] at hwi
    rw [hw] at hwi
    simp at hwi
  have hpos : 0 < FreeGroup.norm (α (FreeGroup.of i)) := norm_pos_of_ne_one hne
  have hterm_le : ∀ k : Fin n, FreeGroup.norm (α (FreeGroup.of k)) ≤ N α := by
    intro k
    rw [N_eq_sum]
    have hs := (Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun t : Fin n => FreeGroup.norm (α (FreeGroup.of t))) (Finset.mem_univ k))
    rw [← hs]
    exact Nat.le_add_left _ _
  have hwi_le := hterm_le i
  have hN := N_mul_lam α i j hij
  rw [hN, hcancel]
  omega
/-- The `rhoNeg` sibling orientation: if the image `w_j` is the single letter
`(a, c)` and `w_i` ends with the same letter `(a, c)` (`i ≠ j`), then right
composition with the exponent-`-1` transvection `rhoNeg i j` (replacing `w_i`
by `w_i * w_j⁻¹`) cancels that last letter and strictly decreases `N`.
Mirrors `single_letter_shortens`, reusing `norm_mul_single_cancel`. -/
lemma single_letter_right_neg_shortens {n : ℕ} (α : MulAut (FreeGroup (Fin n))) {i j : Fin n}
    (hij : i ≠ j) (a : Fin n) (c : Bool) (L : List (Fin n × Bool))
    (hwi : FreeGroup.toWord (α (FreeGroup.of i)) = L ++ [(a, c)])
    (hwj : FreeGroup.toWord (α (FreeGroup.of j)) = [(a, c)]) :
    N (α * rhoNeg i j hij) < N α := by
  classical
  have hwjf : (α (FreeGroup.of j))⁻¹ =
      (if c then (FreeGroup.of a)⁻¹ else FreeGroup.of a) := by
    exact FreeGroup.toWord_injective (by
      rw [FreeGroup.toWord_inv]
      rw [hwj]
      cases c <;> simp [FreeGroup.toWord_inv, FreeGroup.invRev])
  have hcancel : FreeGroup.norm ((α (FreeGroup.of i)) * (α (FreeGroup.of j))⁻¹) =
      FreeGroup.norm (α (FreeGroup.of i)) - 1 := by
    rw [hwjf]
    exact norm_mul_single_cancel (α (FreeGroup.of i)) a c L hwi
  have hne : α (FreeGroup.of i) ≠ 1 := by
    intro h
    have hw : FreeGroup.toWord (1 : FreeGroup (Fin n)) = [] := by simp
    rw [h] at hwi
    rw [hw] at hwi
    simp at hwi
  have hpos : 0 < FreeGroup.norm (α (FreeGroup.of i)) := norm_pos_of_ne_one hne
  have hterm_le : ∀ k : Fin n, FreeGroup.norm (α (FreeGroup.of k)) ≤ N α := by
    intro k
    rw [N_eq_sum]
    have hs := (Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun t : Fin n => FreeGroup.norm (α (FreeGroup.of t))) (Finset.mem_univ k))
    rw [← hs]
    exact Nat.le_add_left _ _
  have hwi_le := hterm_le i
  have hN := N_mul_rhoNeg α i j hij
  rw [hN, hcancel]
  omega
/-- The `lamNeg` sibling orientation: if the image `w_j` is the single letter
`(a, c)` and `w_i` begins with the same letter `(a, c)` (`i ≠ j`), then right
composition with the exponent-`-1` left transvection `lamNeg i j` (replacing
`w_i` by `w_j⁻¹ * w_i`) cancels that first letter and strictly decreases `N`.
Mirrors `single_letter_right_neg_shortens`, reusing the commons head-cancel
lemma. -/
lemma single_letter_left_neg_shortens {n : ℕ} (α : MulAut (FreeGroup (Fin n))) {i j : Fin n}
    (hij : i ≠ j) (a : Fin n) (c : Bool) (M : List (Fin n × Bool))
    (hwi : FreeGroup.toWord (α (FreeGroup.of i)) = (a, c) :: M)
    (hwj : FreeGroup.toWord (α (FreeGroup.of j)) = [(a, c)]) :
    N (α * lamNeg i j hij) < N α := by
  classical
  have hwjf : (α (FreeGroup.of j))⁻¹ =
      (if c then (FreeGroup.of a)⁻¹ else FreeGroup.of a) := by
    exact FreeGroup.toWord_injective (by
      rw [FreeGroup.toWord_inv]
      rw [hwj]
      cases c <;> simp [FreeGroup.toWord_inv, FreeGroup.invRev])
  have hcancel : FreeGroup.norm ((α (FreeGroup.of j))⁻¹ * (α (FreeGroup.of i))) =
      FreeGroup.norm (α (FreeGroup.of i)) - 1 := by
    rw [hwjf]
    exact Commons.GroupTheory.FreeGroup.norm_mul_cancel_head
      (α (FreeGroup.of i)) a c M hwi
  have hne : α (FreeGroup.of i) ≠ 1 := by
    intro h
    have hw : FreeGroup.toWord (1 : FreeGroup (Fin n)) = [] := by simp
    rw [h] at hwi
    rw [hw] at hwi
    simp at hwi
  have hpos : 0 < FreeGroup.norm (α (FreeGroup.of i)) := norm_pos_of_ne_one hne
  have hterm_le : ∀ k : Fin n, FreeGroup.norm (α (FreeGroup.of k)) ≤ N α := by
    intro k
    rw [N_eq_sum]
    have hs := (Finset.sum_erase_add (Finset.univ : Finset (Fin n))
      (fun t : Fin n => FreeGroup.norm (α (FreeGroup.of t))) (Finset.mem_univ k))
    rw [← hs]
    exact Nat.le_add_left _ _
  have hwi_le := hterm_le i
  have hN := N_mul_lamNeg α i j hij
  rw [hN, hcancel]
  omega
/-- Generic list fact: dropping the last element of `L ++ [x]` gives `L`. -/
private lemma dropLast_append_singleton {β : Type*} (L : List β) (x : β) : (L ++ [x]).dropLast = L := by
  induction L with
  | nil => simp
  | cons a as ih =>
      cases as with
      | nil => simp
      | cons b bs => simp [List.dropLast, ih]

/-- No-shortening dichotomy for the last letter: if the image `w_j` is the
single letter `(a,c)` and neither the `rho` nor the `rhoNeg` right move
shortens, then `w_i` does not end in any letter with base `a`. -/
lemma no_right_shorten_last_base {n : ℕ} (α : MulAut (FreeGroup (Fin n))) {i j : Fin n}
    (hij : i ≠ j) (a : Fin n) (c : Bool) (L : List (Fin n × Bool)) (b : Fin n) (d : Bool)
    (hwi : FreeGroup.toWord (α (FreeGroup.of i)) = L ++ [(b, d)])
    (hwj : FreeGroup.toWord (α (FreeGroup.of j)) = [(a, c)])
    (hρ : ¬ N (α * rho i j hij) < N α)
    (hρN : ¬ N (α * rhoNeg i j hij) < N α) :
    b ≠ a := by
  intro hba
  subst b
  have hdc : d = c ∨ d = !c := by
    cases c <;> cases d <;> simp
  rcases hdc with hdc | hdnc
  · have hwi' : FreeGroup.toWord (α (FreeGroup.of i)) = L ++ [(a, c)] := by
      simpa [hdc] using hwi
    exact hρN (single_letter_right_neg_shortens (α := α) hij a c L hwi' hwj)
  · have hwi' : FreeGroup.toWord (α (FreeGroup.of i)) = L ++ [(a, !c)] := by
      simpa [hdnc] using hwi
    have hshort : N (α * rho i j hij) < N α := by
      apply single_letter_shortens (α := α) hij a (!c)
      · rw [hwi', dropLast_append_singleton]
      · simpa using hwj
    exact hρ hshort
/-- No-shortening dichotomy for the first letter (head sibling of
`no_right_shorten_last_base`): if the image `w_j` is the single letter `(a,c)`
and neither the `lam` nor the `lamNeg` left move shortens, then `w_i` does not
begin with any letter with base `a`. -/
lemma no_left_shorten_first_base {n : ℕ} (α : MulAut (FreeGroup (Fin n))) {i j : Fin n}
    (hij : i ≠ j) (a : Fin n) (c : Bool) (M : List (Fin n × Bool)) (b : Fin n) (d : Bool)
    (hwi : FreeGroup.toWord (α (FreeGroup.of i)) = (b, d) :: M)
    (hwj : FreeGroup.toWord (α (FreeGroup.of j)) = [(a, c)])
    (hl : ¬ N (α * lam i j hij) < N α)
    (hlN : ¬ N (α * lamNeg i j hij) < N α) :
    b ≠ a := by
  intro hba
  subst b
  have hdc : d = c ∨ d = !c := by
    cases c <;> cases d <;> simp
  rcases hdc with hdc | hdnc
  · have hwi' : FreeGroup.toWord (α (FreeGroup.of i)) = (a, c) :: M := by
      simpa [hdc] using hwi
    exact hlN (single_letter_left_neg_shortens (α := α) hij a c M hwi' hwj)
  · have hwi' : FreeGroup.toWord (α (FreeGroup.of i)) = (a, !c) :: M := by
      simpa [hdnc] using hwi
    exact hl (single_letter_left_shortens (α := α) hij a c M hwi' hwj)
/-- Boundary-avoidance, last-letter version: if the image `w_j` is the single
letter `(a,c)` and no right move shortens any pair `(i,j)`, `i ≠ j`, then the
last letter of every other image `w_i` has base different from `a`. -/
lemma no_shorten_single_last_avoids_base {n : ℕ} (α : MulAut (FreeGroup (Fin n))) {j : Fin n}
    (a : Fin n) (c : Bool)
    (hwj : FreeGroup.toWord (α (FreeGroup.of j)) = [(a, c)])
    (hminR : ∀ (i : Fin n) (hij : i ≠ j), ¬ N (α * rho i j hij) < N α)
    (hminRN : ∀ (i : Fin n) (hij : i ≠ j), ¬ N (α * rhoNeg i j hij) < N α)
    {i : Fin n} (hij : i ≠ j) {b : Fin n} {d : Bool} {L : List (Fin n × Bool)}
    (hwi : FreeGroup.toWord (α (FreeGroup.of i)) = L ++ [(b, d)]) :
    b ≠ a := by
  exact no_right_shorten_last_base (α := α) hij a c L b d hwi hwj
    (hminR i hij) (hminRN i hij)

/-- Boundary-avoidance, first-letter version: if the image `w_j` is the single
letter `(a,c)` and no left move shortens any pair `(i,j)`, `i ≠ j`, then the
first letter of every other image `w_i` has base different from `a`. -/
lemma no_shorten_single_first_avoids_base {n : ℕ} (α : MulAut (FreeGroup (Fin n))) {j : Fin n}
    (a : Fin n) (c : Bool)
    (hwj : FreeGroup.toWord (α (FreeGroup.of j)) = [(a, c)])
    (hminL : ∀ (i : Fin n) (hij : i ≠ j), ¬ N (α * lam i j hij) < N α)
    (hminLN : ∀ (i : Fin n) (hij : i ≠ j), ¬ N (α * lamNeg i j hij) < N α)
    {i : Fin n} (hij : i ≠ j) {b : Fin n} {d : Bool} {M : List (Fin n × Bool)}
    (hwi : FreeGroup.toWord (α (FreeGroup.of i)) = (b, d) :: M) :
    b ≠ a := by
  exact no_left_shorten_first_base (α := α) hij a c M b d hwi hwj
    (hminL i hij) (hminLN i hij)
/-- The fork lemma: under full minimality (no right or left move shortens any
pair), a single-letter image `w_j = (a,c)` forces every other image `w_i` to
avoid the base `a` at *both* ends.  This is the boundary conclusion that the
classical argument uses to fork into the signed picture vs. absorption. -/
lemma no_shorten_single_letter_boundary_avoid {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {j : Fin n} (a : Fin n) (c : Bool)
    (hwj : FreeGroup.toWord (α (FreeGroup.of j)) = [(a, c)])
    (hminR : ∀ (i : Fin n) (hij : i ≠ j), ¬ N (α * rho i j hij) < N α)
    (hminRN : ∀ (i : Fin n) (hij : i ≠ j), ¬ N (α * rhoNeg i j hij) < N α)
    (hminL : ∀ (i : Fin n) (hij : i ≠ j), ¬ N (α * lam i j hij) < N α)
    (hminLN : ∀ (i : Fin n) (hij : i ≠ j), ¬ N (α * lamNeg i j hij) < N α)
    {i : Fin n} (hij : i ≠ j) {b d b' d' : _} {L M : List (Fin n × Bool)}
    (hfirst : FreeGroup.toWord (α (FreeGroup.of i)) = (b, d) :: M)
    (hlast : FreeGroup.toWord (α (FreeGroup.of i)) = L ++ [(b', d')]) :
    b ≠ a ∧ b' ≠ a := by
  constructor
  · exact no_shorten_single_first_avoids_base (α := α) a c hwj hminL hminLN hij hfirst
  · exact no_shorten_single_last_avoids_base (α := α) a c hwj hminR hminRN hij hlast
end

end Submission.Nielsen
