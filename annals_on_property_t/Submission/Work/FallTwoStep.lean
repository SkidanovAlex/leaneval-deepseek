import Submission.Work.StrictDescent
import Submission.Work.T3RebalanceTuple
import Submission.Work.AggregateCoordinate
import Submission.Work.SystemReducedImage
import Submission.Work.Item3.RowInvariant
import Submission.Work.RebalanceProtocol

open Submission.Nielsen
open Submission.FreeGroupAut
open FreeGroup
open Commons.GroupTheory.FreeGroup
set_option autoImplicit false

/-!
# Fall-Two step: from a balanced configuration to a non-trivial move

`StrictDescent.FallTwoConfig α` is the balanced (Fall-II) configuration of an
automorphism: some standard generator `a_m` has an image-aggregate expression
with an interior confined factor `j` whose word splits into halves
`A ++ B` (`|A| = |B|`), the left neighbour covering `invRev A` from the right
and the right neighbour covering `invRev B` from the left:

    es[j-1].toWord = X ++ invRev A    es[j].toWord = A ++ B
    es[j+1].toWord = invRev B ++ Z

This module proves the *step existence* half of the Fall-II rebalancing run:
**every Fall-II configuration admits a non-trivial closure move that does not
increase the total length `N`** — the classical combination of a system
element with the balanced element `w_p` (`rhoNeg` for the ends-with-`B` /
`lam` for the begins-with-`B⁻¹` classes), which the rebalancing run applies
until a strict shortening reappears (`FallII.fallII_*_strict` fire when a
boundary cancellation develops).

The balanced factor is a basis image up to sign (`ImageAggregate`):
`es[j] = ±w_p`.  Geometry:

* `es[j] = +w_p` (own halves `A B`): the **right** neighbour factor
  `es[j+1]` begins with `invRev B`; if it is `+w_u`, `w_u` *begins with*
  `B⁻¹` and the combination is `lam u p`; if it is `-w_u`, `w_u` *ends with*
  `B` and the combination is `rhoNeg u p`.
* `es[j] = -w_p` (own halves `A' B' := (invRev B, invRev A)`): the **left**
  neighbour factor `es[j-1]` ends with `invRev A = B'`; if it is `+w_v`,
  `w_v` *ends with* `B'` (`rhoNeg v p`); if it is `-w_v`, `w_v` *begins with*
  `B'⁻¹` (`lam v p`).

The witness coordinate must differ from the balanced coordinate `p`
("ein anderes Element des Systems"): the mixed-sign coincidences are excluded
by `SystemReduced` (`witness_ne_right_minus`, `witness_ne_left_plus`); the
same-sign coincidences (`es[j+1] = es[j]` resp. `es[j-1] = es[j]`) would make
the reduced balanced word equal `invRev B ++ B` resp. `A ++ invRev A`, which
is impossible for the non-trivial factor of a `SystemReduced` aggregate —
proved directly here (`fallTwo_same_sign_right_degenerate`,
`fallTwo_same_sign_left_degenerate`), with no alignment hypotheses needed
(the covering words supply the halves).

The four word-level attach lemmas mirror `AggregateCoordinate.balanced_attach_*`
but consume the covering words of a `FallTwoConfig` directly (no
`Confined`/alignment hypotheses): each produces the corresponding
`N`-non-increasing closure move.  Assembled:

    fallTwo_step_nonstrict (hF : FallTwoConfig α) :
        ∃ γ, γ ∈ AutClosure n ∧ γ ≠ 1 ∧ N (α * γ) ≤ N α

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- A generator `a_i` of a free group is never trivial. -/
private lemma of_ne_one {n : ℕ} (i : Fin n) : FreeGroup.of i ≠ (1 : FreeGroup (Fin n)) := by
  intro h1
  have hw := congrArg (fun x : FreeGroup (Fin n) => x.toWord) h1
  have hof : (FreeGroup.of i).toWord = [(i, true)] := by
    rw [FreeGroup.toWord_of]
  rw [hof, FreeGroup.toWord_one] at hw
  simp at hw

/-- An automorphism that moves a basis generator is not the identity. -/
lemma aut_ne_one_of_moves_generator {n : ℕ} (α : MulAut (FreeGroup (Fin n))) {i : Fin n}
    (h : FreeGroup.of i ≠ α (FreeGroup.of i)) : α ≠ (1 : MulAut (FreeGroup (Fin n))) := by
  intro h1
  apply h
  have hc := congrArg (fun φ : MulAut (FreeGroup (Fin n)) => φ (FreeGroup.of i)) h1
  simpa using hc.symm

/-- `rhoNeg u p` moves the generator `u`, hence is not the identity. -/
lemma rhoNeg_ne_one {n : ℕ} (u p : Fin n) (hup : u ≠ p) :
    rhoNeg u p hup ≠ (1 : MulAut (FreeGroup (Fin n))) := by
  apply aut_ne_one_of_moves_generator (i := u)
  rw [rhoNeg_apply_self]
  intro h
  have h' := congrArg (fun x : FreeGroup (Fin n) => (FreeGroup.of u)⁻¹ * x) h
  -- (of u)⁻¹ * (of u * (of p)⁻¹) = (of u)⁻¹ * of u
  have hpinv : (FreeGroup.of p)⁻¹ = 1 := by
    -- simplify both sides of h'
    simpa [mul_assoc] using h'.symm
  have hp1 : FreeGroup.of p = 1 := by
    have hpp := congrArg (fun x : FreeGroup (Fin n) => x⁻¹) hpinv
    simpa using hpp
  exact of_ne_one p hp1

/-- `lam u p` moves the generator `u`, hence is not the identity. -/
lemma lam_ne_one {n : ℕ} (u p : Fin n) (hup : u ≠ p) :
    lam u p hup ≠ (1 : MulAut (FreeGroup (Fin n))) := by
  apply aut_ne_one_of_moves_generator (i := u)
  rw [lam_apply_self]
  intro h
  -- of p * of u = of u  ⟹  of p = 1 by cancelling `of u` on the right
  have h' := congrArg (fun x : FreeGroup (Fin n) => x * (FreeGroup.of u)⁻¹) h
  have hp1 : FreeGroup.of p = 1 := by
    simpa [mul_assoc] using h'
  exact of_ne_one p hp1

/-! ## Same-sign coincidences are excluded by reducedness (no alignment needed)

In the balanced state with covering words, the same-sign coincidences
`es[j+1] = es[j]` (resp. `es[j-1] = es[j]`) would force the reduced balanced
word to be `invRev B ++ B` (resp. `A ++ invRev A`), which reduces to the
empty word — impossible for the non-trivial factor of a `SystemReduced`
aggregate. -/

/-- Same-sign right coincidence forces the empty word:
`es[j+1] = es[j]` with the covering words implies `(es[j]).toWord = []`. -/
lemma fallTwo_same_sign_right_degenerate {n : ℕ} {es : List (FreeGroup (Fin n))}
    {j : ℕ} (hj : j < es.length) (hjk : j + 1 < es.length)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hr : (es[j + 1]).toWord = FreeGroup.invRev B ++ Z)
    (heq : es[j + 1] = es[j]) :
    (es[j]).toWord = [] := by
  have hc := congrArg (fun g : FreeGroup (Fin n) => g.toWord) heq
  rw [hr, hmid] at hc
  have he : A ++ B = FreeGroup.invRev B ++ Z := hc.symm
  have ht1 : (FreeGroup.invRev B ++ Z).take B.length = FreeGroup.invRev B := by
    rw [List.take_append_of_le_length (l₁ := FreeGroup.invRev B) (l₂ := Z)
      (i := B.length) (by rw [FreeGroup.invRev_length])]
    rw [← FreeGroup.invRev_length]
    exact List.take_length
  have htA : (A ++ B).take B.length = A := by
    rw [List.take_append_of_le_length (l₁ := A) (l₂ := B) (i := B.length) (by omega)]
    rw [← hAB]
    exact List.take_length
  have htake := congrArg (fun W : List (Fin n × Bool) => W.take B.length) he
  rw [htA] at htake
  rw [ht1] at htake
  have hA : A = FreeGroup.invRev B := htake
  have hword : (es[j]).toWord = FreeGroup.invRev B ++ B := by
    rw [hmid, hA]
  have hred : FreeGroup.IsReduced ((es[j]).toWord) := FreeGroup.isReduced_toWord (x := es[j])
  have hredB : FreeGroup.IsReduced (FreeGroup.invRev B ++ B) := by
    rw [hword] at hred
    exact hred
  have hrv : FreeGroup.reduce (FreeGroup.invRev B ++ B) = FreeGroup.invRev B ++ B :=
    FreeGroup.isReduced_iff_reduce_eq.mp hredB
  have hrc : FreeGroup.reduce (FreeGroup.invRev B ++ B) = [] :=
    FreeGroup.reduce_invRev_left_cancel (L := B)
  have hempty : FreeGroup.invRev B ++ B = [] := by
    rw [← hrv]
    exact hrc
  rw [hword, hempty]

/-- Same-sign left coincidence forces the empty word:
`es[j-1] = es[j]` with the covering words implies `(es[j]).toWord = []`. -/
lemma fallTwo_same_sign_left_degenerate {n : ℕ} {es : List (FreeGroup (Fin n))}
    {j : ℕ} (hj : j < es.length) (hm : j - 1 < es.length)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hl : (es[j - 1]).toWord = X ++ FreeGroup.invRev A)
    (heq : es[j - 1] = es[j]) :
    (es[j]).toWord = [] := by
  have hc := congrArg (fun g : FreeGroup (Fin n) => g.toWord) heq
  rw [hl, hmid] at hc
  have he : A ++ B = X ++ FreeGroup.invRev A := hc.symm
  have hlenX : X.length = B.length := by
    have hc' := congrArg List.length he
    rw [List.length_append, List.length_append, FreeGroup.invRev_length] at hc'
    omega
  have hd1 : (X ++ FreeGroup.invRev A).drop B.length = FreeGroup.invRev A := by
    have hle : B.length ≤ X.length := by omega
    rw [List.drop_append_of_le_length (l₁ := X) (l₂ := FreeGroup.invRev A)
      (i := B.length) hle]
    rw [← hlenX, List.drop_length]
    simp
  have hd2 : (A ++ B).drop B.length = B := by
    rw [List.drop_append_of_le_length (l₁ := A) (l₂ := B) (i := B.length) (by omega)]
    rw [← hAB, List.drop_length]
    simp
  have hdrop := congrArg (fun W : List (Fin n × Bool) => W.drop B.length) he
  rw [hd2] at hdrop
  rw [hd1] at hdrop
  have hB : B = FreeGroup.invRev A := hdrop
  have hword : (es[j]).toWord = A ++ FreeGroup.invRev A := by
    rw [hmid, hB]
  have hred : FreeGroup.IsReduced ((es[j]).toWord) := FreeGroup.isReduced_toWord (x := es[j])
  have hredA : FreeGroup.IsReduced (A ++ FreeGroup.invRev A) := by
    rw [hword] at hred
    exact hred
  have hrv : FreeGroup.reduce (A ++ FreeGroup.invRev A) = A ++ FreeGroup.invRev A :=
    FreeGroup.isReduced_iff_reduce_eq.mp hredA
  have hrc : FreeGroup.reduce (A ++ FreeGroup.invRev A) = [] :=
    reduce_append_invRev_self A
  have hempty : A ++ FreeGroup.invRev A = [] := by
    rw [← hrv]
    exact hrc
  rw [hword, hempty]

/-- Same-sign right coincidence is impossible for a non-trivial
`SystemReduced` aggregate: `u ≠ p` for the `+` balanced factor with a `+`
right neighbour. -/
theorem fallTwo_ne_right_plus {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n)))
    (hred : SystemReduced es) {j : ℕ} (hj : j < es.length) (hjk : j + 1 < es.length)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hr : (es[j + 1]).toWord = FreeGroup.invRev B ++ Z)
    {p u : Fin n} (hp : es[j] = α (FreeGroup.of p))
    (hu : es[j + 1] = α (FreeGroup.of u)) : u ≠ p := by
  intro hup
  have h1 : es[j] = 1 := by
    apply FreeGroup.toWord_eq_nil_iff.mp
    apply fallTwo_same_sign_right_degenerate (es := es) (j := j) hj hjk A B Z hAB hmid hr
    rw [hp, hu, hup]
  exact hred.1 (es[j]) (List.getElem_mem hj) h1

/-- Same-sign left coincidence is impossible for a non-trivial
`SystemReduced` aggregate: `v ≠ p` for the `-` balanced factor with a `-`
left neighbour. -/
theorem fallTwo_ne_left_minus {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n)))
    (hred : SystemReduced es) {j : ℕ} (hj : j < es.length) (hm : j - 1 < es.length)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hl : (es[j - 1]).toWord = X ++ FreeGroup.invRev A)
    {p v : Fin n} (hp : es[j] = (α (FreeGroup.of p))⁻¹)
    (hv : es[j - 1] = (α (FreeGroup.of v))⁻¹) : v ≠ p := by
  intro hvp
  have h1 : es[j] = 1 := by
    apply FreeGroup.toWord_eq_nil_iff.mp
    apply fallTwo_same_sign_left_degenerate (es := es) (j := j) hj hm A B X hAB hmid hl
    rw [hp, hv, hvp]
  exact hred.1 (es[j]) (List.getElem_mem hj) h1


/-! ## The four Fall-Two attach moves (covering words in hand)

Each lemma mirrors the corresponding `AggregateCoordinate.balanced_attach_*`
but takes the covering words (`hmid`, `hl`, `hr`) directly — the content of a
`FallTwoConfig` — instead of re-deriving them from a balanced state with
`Confined`/alignment hypotheses.  The witness coordinate (`u` from the right
neighbour for `es[j] = +w_p`, `v` from the left neighbour for `es[j] = -w_p`)
differs from `p` by `witness_ne_right_minus` / `witness_ne_left_plus`
(mixed-sign, via `SystemReduced`) or by `fallTwo_ne_right_plus` /
`fallTwo_ne_left_minus` (same-sign, via reducedness). -/

/-- Word of a basis image whose inverse is the balanced factor. -/
private lemma neg_image_word {n : ℕ} (g w : FreeGroup (Fin n))
    (A B : List (Fin n × Bool))
    (hbal : g.toWord = A ++ B) (hg : g⁻¹ = w) :
    w.toWord = FreeGroup.invRev B ++ FreeGroup.invRev A := by
  calc
    w.toWord = (g⁻¹).toWord := by rw [hg]
    _ = FreeGroup.invRev (g.toWord) := by rw [FreeGroup.toWord_inv]
    _ = FreeGroup.invRev (A ++ B) := by rw [hbal]
    _ = FreeGroup.invRev B ++ FreeGroup.invRev A := by rw [FreeGroup.invRev_append]

/-- **Attachment, `es[j] = +α(a_p)`, right neighbour `es[j+1] = -α(a_u)`**
(right neighbour factor begins with `invRev B`, so `w_u` ends with `B`):
the classical combination `w_u ↦ w_u · w_p⁻¹` is right composition by
`rhoNeg u p`; the total length does not increase. -/
theorem fallTwo_attach_right_minus {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hjk : j + 1 < es.length)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hr : (es[j + 1]).toWord = FreeGroup.invRev B ++ Z)
    {p u : Fin n} (hp : es[j] = α (FreeGroup.of p))
    (hu : es[j + 1] = (α (FreeGroup.of u))⁻¹) :
    N (α * rhoNeg u p (witness_ne_right_minus α es hred hj hjk hp hu)) ≤ N α := by
  have hpw : (α (FreeGroup.of p)).toWord = A ++ B := by
    rw [← hp]
    exact hmid
  have hw : (α (FreeGroup.of u)).toWord = FreeGroup.invRev Z ++ B := by
    have hwu : (α (FreeGroup.of u)) = (es[j + 1])⁻¹ := by
      rw [hu]
      simp
    calc
      (α (FreeGroup.of u)).toWord = ((es[j + 1])⁻¹).toWord := by rw [hwu]
      _ = FreeGroup.invRev (es[j + 1].toWord) := by rw [FreeGroup.toWord_inv]
      _ = FreeGroup.invRev (FreeGroup.invRev B ++ Z) := by rw [hr]
      _ = FreeGroup.invRev Z ++ B := by
          rw [FreeGroup.invRev_append]
          rw [FreeGroup.invRev_invRev]
  exact rebalance_move_N_le α (q := u) (p := p)
    (witness_ne_right_minus α es hred hj hjk hp hu) A B (FreeGroup.invRev Z) hAB hw hpw

/-- **Attachment, `es[j] = +α(a_p)`, right neighbour `es[j+1] = +α(a_u)`**
(`w_u` begins with `B⁻¹`): the combination `w_u ↦ w_p · w_u` is right
composition by `lam u p`; the total length does not increase. -/
theorem fallTwo_attach_right_plus {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hjk : j + 1 < es.length)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hr : (es[j + 1]).toWord = FreeGroup.invRev B ++ Z)
    {p u : Fin n} (hp : es[j] = α (FreeGroup.of p))
    (hu : es[j + 1] = α (FreeGroup.of u)) :
    N (α * lam u p (fallTwo_ne_right_plus α es hred hj hjk A B Z hAB hmid hr hp hu)) ≤ N α := by
  have hpw : (α (FreeGroup.of p)).toWord = A ++ B := by
    rw [← hp]
    exact hmid
  have hw : (α (FreeGroup.of u)).toWord = FreeGroup.invRev B ++ Z := by
    rw [← hu]
    exact hr
  exact rebalance_move_N_le_left α (q := u) (p := p)
    (fallTwo_ne_right_plus α es hred hj hjk A B Z hAB hmid hr hp hu) A B Z hAB hw hpw

/-- **Attachment, `es[j] = -(α(a_p))`, left neighbour `es[j-1] = +α(a_v)`**
(`w_p` has own halves `(invRev B, invRev A)`, and `w_v` ends with the second
half `invRev A`): the combination `w_v ↦ w_v · w_p⁻¹` is right composition by
`rhoNeg v p`; the total length does not increase. -/
theorem fallTwo_attach_left_plus {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hj0 : 0 < j) (hm : j - 1 < es.length)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hl : (es[j - 1]).toWord = X ++ FreeGroup.invRev A)
    {p v : Fin n} (hp : es[j] = (α (FreeGroup.of p))⁻¹)
    (hv : es[j - 1] = α (FreeGroup.of v)) :
    N (α * rhoNeg v p (witness_ne_left_plus α es hred hj hj0 hm hp hv)) ≤ N α := by
  let A' : List (Fin n × Bool) := FreeGroup.invRev B
  let B' : List (Fin n × Bool) := FreeGroup.invRev A
  have hpw : (α (FreeGroup.of p)).toWord = A' ++ B' := by
    have hwp : (es[j])⁻¹ = α (FreeGroup.of p) := by
      rw [hp]
      simp
    have hw := neg_image_word (g := es[j]) (w := α (FreeGroup.of p)) A B hmid hwp
    simpa [A', B'] using hw
  have hAB' : A'.length = B'.length := by
    unfold A' B'
    rw [FreeGroup.invRev_length]
    rw [FreeGroup.invRev_length]
    exact hAB.symm
  have hq : (α (FreeGroup.of v)).toWord = X ++ B' := by
    rw [← hv]
    simpa [B'] using hl
  exact rebalance_move_N_le α (q := v) (p := p)
    (witness_ne_left_plus α es hred hj hj0 hm hp hv) A' B' X hAB' hq hpw

/-- **Attachment, `es[j] = -(α(a_p))`, left neighbour `es[j-1] = -α(a_v)`**
(`w_v` begins with the inverse of the second half `invRev A`): the
combination `w_v ↦ w_p · w_v` is right composition by `lam v p`; the total
length does not increase. -/
theorem fallTwo_attach_left_minus {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hj0 : 0 < j) (hm : j - 1 < es.length)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hl : (es[j - 1]).toWord = X ++ FreeGroup.invRev A)
    {p v : Fin n} (hp : es[j] = (α (FreeGroup.of p))⁻¹)
    (hv : es[j - 1] = (α (FreeGroup.of v))⁻¹) :
    N (α * lam v p (fallTwo_ne_left_minus α es hred hj hm A B X hAB hmid hl hp hv)) ≤ N α := by
  let A' : List (Fin n × Bool) := FreeGroup.invRev B
  let B' : List (Fin n × Bool) := FreeGroup.invRev A
  have hpw : (α (FreeGroup.of p)).toWord = A' ++ B' := by
    have hwp : (es[j])⁻¹ = α (FreeGroup.of p) := by
      rw [hp]
      simp
    have hw := neg_image_word (g := es[j]) (w := α (FreeGroup.of p)) A B hmid hwp
    simpa [A', B'] using hw
  have hAB' : A'.length = B'.length := by
    unfold A' B'
    rw [FreeGroup.invRev_length]
    rw [FreeGroup.invRev_length]
    exact hAB.symm
  have hq : (α (FreeGroup.of v)).toWord = FreeGroup.invRev B' ++ FreeGroup.invRev X := by
    have hwv : (es[j - 1])⁻¹ = α (FreeGroup.of v) := by
      rw [hv]
      simp
    calc
      (α (FreeGroup.of v)).toWord = ((es[j - 1])⁻¹).toWord := by rw [hwv]
      _ = FreeGroup.invRev (es[j - 1].toWord) := by rw [FreeGroup.toWord_inv]
      _ = FreeGroup.invRev (X ++ FreeGroup.invRev A) := by rw [hl]
      _ = A ++ FreeGroup.invRev X := by
          rw [FreeGroup.invRev_append]
          rw [FreeGroup.invRev_invRev]
      _ = FreeGroup.invRev B' ++ FreeGroup.invRev X := by
          have h : FreeGroup.invRev B' = A := by
            unfold B'
            rw [FreeGroup.invRev_invRev]
          rw [h]
  exact rebalance_move_N_le_left α (q := v) (p := p)
    (fallTwo_ne_left_minus α es hred hj hm A B X hAB hmid hl hp hv) A' B' (FreeGroup.invRev X) hAB' hq hpw



/-! ## Bridge to the word-level coverability vocabulary

`RowInvariant.TwoSidedCoverable α q` is the word-level necessary condition
for `q` to be the balanced element of a half-absorption witness.  This
section proves the direction used by the reduction: an aggregate-balanced
configuration (`ExactlyHalfAbsorbed S p` — a confined interior factor
`es[j] = ±w_c` of the image aggregate of some `a_m` with covering words)
makes `c := S.row p` **word-level two-sidedly coverable**: the two covering
neighbour factors are basis images up to sign (`ImageAggregate`), and each
sign supplies one member of the corresponding covering class (ends/begins),
with the same-sign and mixed-sign coordinate coincidences excluded exactly as
in the attach section above.

Machine note (`FallTwoRunNotes.md`): the converse (word-coverable ⟹
aggregate-balanced) is FALSE — 11 fresh post-fixpoint states contain
coverable elements with no balanced candidate even at maximal detection — so
the bridge is one-directional: it is the contrapositive (no word-coverable at
row `< p` ⟹ no aggregate-balanced at row `< p`) that the row invariant and
the aggregate no-reappearance will consume. -/

/-- Same-sign left coincidence for the `+` balanced factor (`es[j-1] = +w_v`
next to `es[j] = +w_p`) is impossible: `v ≠ p`. -/
theorem fallTwo_ne_left_plus {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hm : j - 1 < es.length)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hl : (es[j - 1]).toWord = X ++ FreeGroup.invRev A)
    {p v : Fin n} (hp : es[j] = α (FreeGroup.of p))
    (hv : es[j - 1] = α (FreeGroup.of v)) : v ≠ p := by
  intro hvp
  have h1 : es[j] = 1 := by
    apply FreeGroup.toWord_eq_nil_iff.mp
    apply fallTwo_same_sign_left_degenerate (es := es) (j := j) hj hm A B X hAB hmid hl
    rw [hp, hv, hvp]
  exact hred.1 (es[j]) (List.getElem_mem hj) h1

/-- Same-sign right coincidence for the `-` balanced factor (`es[j+1] = -w_u`
next to `es[j] = -w_p`) is impossible: `u ≠ p`. -/
theorem fallTwo_ne_right_minus {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hjk : j + 1 < es.length)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hr : (es[j + 1]).toWord = FreeGroup.invRev B ++ Z)
    {p u : Fin n} (hp : es[j] = (α (FreeGroup.of p))⁻¹)
    (hu : es[j + 1] = (α (FreeGroup.of u))⁻¹) : u ≠ p := by
  intro hup
  have h1 : es[j] = 1 := by
    apply FreeGroup.toWord_eq_nil_iff.mp
    apply fallTwo_same_sign_right_degenerate (es := es) (j := j) hj hjk A B Z hAB hmid hr
    rw [hp, hu, hup]
  exact hred.1 (es[j]) (List.getElem_mem hj) h1

/-- Mixed-sign right selection for the `-` balanced factor: `es[j] = -w_p`
with right neighbour `es[j+1] = +w_u` forces `u ≠ p` (adjacent inverses). -/
theorem fallTwo_ne_right_mixed {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hjk : j + 1 < es.length)
    {p u : Fin n} (hp : es[j] = (α (FreeGroup.of p))⁻¹)
    (hu : es[j + 1] = α (FreeGroup.of u)) : u ≠ p := by
  intro hup
  have h : es[j + 1] = (es[j])⁻¹ := by
    rw [hu, hup, hp]
    simp
  exact hred.2 j hjk h


/-- Entries of a list at equal indices are equal. -/
private lemma getElem_index_congr {α : Type*} {l : List α} {i j : ℕ} (h : i = j)
    (hi : i < l.length) (hj : j < l.length) : l[i] = l[j] := by
  subst j
  rfl

/-- Mixed-sign left selection for the `+` balanced factor: `es[j] = +w_p`
with left neighbour `es[j-1] = -w_v` forces `v ≠ p` (adjacent inverses). -/
theorem fallTwo_ne_left_mixed {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hj0 : 0 < j) (hm : j - 1 < es.length)
    {p v : Fin n} (hp : es[j] = α (FreeGroup.of p))
    (hv : es[j - 1] = (α (FreeGroup.of v))⁻¹) : v ≠ p := by
  intro hvp
  have h : es[j] = (es[j - 1])⁻¹ := by
    rw [hp, hv, hvp]
    simp
  have hij : (j - 1) + 1 = j := by omega
  have hj' : (j - 1) + 1 < es.length := by omega
  have hcong : es[j] = es[(j - 1) + 1] := by
    apply getElem_index_congr (i := j) (j := (j - 1) + 1) (hi := hj) (hj := hj')
    omega
  rw [hcong] at h
  exact hred.2 (j - 1) hj' h

/-! ## Assembly: every Fall-Two configuration admits a non-trivial step -/

/-- **Fall-Two step existence.**  From a `FallTwoConfig α` (an interior
balanced factor `es[j] = ±w_p` of the image aggregate of some `a_m`, covered
exactly by its two neighbours), one of the four classical combination moves
(`rhoNeg`/`lam` of the covering witness with the balanced element) is a
**non-trivial closure move that does not increase the total length `N`** —
the single step of the Fall-II rebalancing run (`StrictDescent`'s `hF` pin
fires its strict cases via `FallII.fallII_*_strict` when a boundary
cancellation develops; this lemma supplies the non-strict propagation moves
the run applies while the index advances). -/
theorem fallTwo_step_nonstrict {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hF : FallTwoConfig α) :
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ γ ≠ 1 ∧ N (α * γ) ≤ N α := by
  classical
  rcases hF with ⟨m, j, hj, hj0, hj1, hconf, A, B, X, Z, hA, hAB, hX, hZ⟩
  let es : List (FreeGroup (Fin n)) := imageAggregate α m
  have hred : SystemReduced es := by
    simpa [es] using (SystemReduced_imageAggregate α m)
  have himg : ImageAggregate α es := by
    simpa [es] using (imageAggregate_isImageAggregate α m)
  have hjE : j < es.length := by simpa [es] using hj
  have hj1E : j + 1 < es.length := by simpa [es] using hj1
  have hmE : j - 1 < es.length := by omega
  have hmid : (es[j]).toWord = A ++ B := by simpa [es] using hA
  have hr : (es[j + 1]).toWord = FreeGroup.invRev B ++ Z := by simpa [es] using hZ
  have hl : (es[j - 1]).toWord = X ++ FreeGroup.invRev A := by simpa [es] using hX
  -- the balanced factor is a basis image up to sign
  have hp : ∃ p : Fin n, es[j] = α (FreeGroup.of p) ∨ es[j] = (α (FreeGroup.of p))⁻¹ :=
    himg (es[j]) (List.getElem_mem hjE)
  rcases hp with ⟨p, hpo⟩
  rcases hpo with hp | hp
  · -- es[j] = +w_p: combine the right neighbour
    have hu : ∃ u : Fin n, es[j + 1] = α (FreeGroup.of u) ∨
        es[j + 1] = (α (FreeGroup.of u))⁻¹ :=
      himg (es[j + 1]) (List.getElem_mem hj1E)
    rcases hu with ⟨u, huo⟩
    rcases huo with hu | hu
    · refine ⟨lam u p (fallTwo_ne_right_plus α es hred hjE hj1E A B Z hAB hmid hr hp hu), ?_, ?_, ?_⟩
      · exact lam_mem_closure (fallTwo_ne_right_plus α es hred hjE hj1E A B Z hAB hmid hr hp hu)
      · exact lam_ne_one u p (fallTwo_ne_right_plus α es hred hjE hj1E A B Z hAB hmid hr hp hu)
      · exact fallTwo_attach_right_plus α es hred hjE hj1E A B Z hAB hmid hr hp hu
    · refine ⟨rhoNeg u p (witness_ne_right_minus α es hred hjE hj1E hp hu), ?_, ?_, ?_⟩
      · exact rhoNeg_mem_closure (witness_ne_right_minus α es hred hjE hj1E hp hu)
      · exact rhoNeg_ne_one u p (witness_ne_right_minus α es hred hjE hj1E hp hu)
      · exact fallTwo_attach_right_minus α es hred hjE hj1E A B Z hAB hmid hr hp hu
  · -- es[j] = -w_p: combine the left neighbour
    have hv : ∃ v : Fin n, es[j - 1] = α (FreeGroup.of v) ∨
        es[j - 1] = (α (FreeGroup.of v))⁻¹ :=
      himg (es[j - 1]) (List.getElem_mem hmE)
    rcases hv with ⟨v, hvo⟩
    rcases hvo with hv | hv
    · refine ⟨rhoNeg v p (witness_ne_left_plus α es hred hjE hj0 hmE hp hv), ?_, ?_, ?_⟩
      · exact rhoNeg_mem_closure (witness_ne_left_plus α es hred hjE hj0 hmE hp hv)
      · exact rhoNeg_ne_one v p (witness_ne_left_plus α es hred hjE hj0 hmE hp hv)
      · exact fallTwo_attach_left_plus α es hred hjE hj0 hmE A B X hAB hmid hl hp hv
    · refine ⟨lam v p (fallTwo_ne_left_minus α es hred hjE hmE A B X hAB hmid hl hp hv), ?_, ?_, ?_⟩
      · exact lam_mem_closure (fallTwo_ne_left_minus α es hred hjE hmE A B X hAB hmid hl hp hv)
      · exact lam_ne_one v p (fallTwo_ne_left_minus α es hred hjE hmE A B X hAB hmid hl hp hv)
      · exact fallTwo_attach_left_minus α es hred hjE hj0 hmE A B X hAB hmid hl hp hv


/-! ## The eight covering-class witnesses of a balanced factor

For each orientation of the balanced factor (`es[j] = +w_p` with own halves
`A B`, or `es[j] = -w_p` with own halves `(invRev B, invRev A)`) and each
sign of the two covering neighbours, the neighbour supplies one member of the
corresponding covering class of the balanced element `p` (ends/begins), with
the coordinate-difference `u ≠ p` / `v ≠ p` supplied by the same-sign /
mixed-sign selection lemmas. -/

/-- `es[j] = +w_p`, left neighbour `es[j-1] = +w_v`: `w_v` ends with `invRev A`
and `v ≠ p`. -/
theorem plus_left_plus_witness {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hm : j - 1 < es.length)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hl : (es[j - 1]).toWord = X ++ FreeGroup.invRev A)
    {p v : Fin n} (hp : es[j] = α (FreeGroup.of p))
    (hv : es[j - 1] = α (FreeGroup.of v)) :
    v ≠ p ∧ EndsWithWord (coordWord α v) (FreeGroup.invRev A) := by
  constructor
  · exact fallTwo_ne_left_plus α es hred hj hm A B X hAB hmid hl hp hv
  · unfold coordWord
    rw [← hv]
    unfold EndsWithWord
    exact ⟨X, hl⟩

/-- `es[j] = +w_p`, left neighbour `es[j-1] = -w_v`: `w_v` begins with `A`
and `v ≠ p`. -/
theorem plus_left_minus_witness {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hj0 : 0 < j) (hm : j - 1 < es.length)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hl : (es[j - 1]).toWord = X ++ FreeGroup.invRev A)
    {p v : Fin n} (hp : es[j] = α (FreeGroup.of p))
    (hv : es[j - 1] = (α (FreeGroup.of v))⁻¹) :
    v ≠ p ∧ BeginsWithWord (coordWord α v) A := by
  constructor
  · exact fallTwo_ne_left_mixed α es hred hj hj0 hm hp hv
  · have hwv : (α (FreeGroup.of v)) = (es[j - 1])⁻¹ := by
      rw [hv]
      simp
    have hw : (α (FreeGroup.of v)).toWord = A ++ FreeGroup.invRev X := by
      calc
        (α (FreeGroup.of v)).toWord = ((es[j - 1])⁻¹).toWord := by rw [hwv]
        _ = FreeGroup.invRev (es[j - 1].toWord) := by rw [FreeGroup.toWord_inv]
        _ = FreeGroup.invRev (X ++ FreeGroup.invRev A) := by rw [hl]
        _ = A ++ FreeGroup.invRev X := by
            rw [FreeGroup.invRev_append]
            rw [FreeGroup.invRev_invRev]
    unfold coordWord
    unfold BeginsWithWord
    exact ⟨FreeGroup.invRev X, hw⟩

/-- `es[j] = +w_p`, right neighbour `es[j+1] = +w_u`: `w_u` begins with
`invRev B` and `u ≠ p`. -/
theorem plus_right_plus_witness {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hjk : j + 1 < es.length)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hr : (es[j + 1]).toWord = FreeGroup.invRev B ++ Z)
    {p u : Fin n} (hp : es[j] = α (FreeGroup.of p))
    (hu : es[j + 1] = α (FreeGroup.of u)) :
    u ≠ p ∧ BeginsWithWord (coordWord α u) (FreeGroup.invRev B) := by
  constructor
  · exact fallTwo_ne_right_plus α es hred hj hjk A B Z hAB hmid hr hp hu
  · unfold coordWord
    rw [← hu]
    unfold BeginsWithWord
    exact ⟨Z, hr⟩

/-- `es[j] = +w_p`, right neighbour `es[j+1] = -w_u`: `w_u` ends with `B`
and `u ≠ p`. -/
theorem plus_right_minus_witness {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hjk : j + 1 < es.length)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hr : (es[j + 1]).toWord = FreeGroup.invRev B ++ Z)
    {p u : Fin n} (hp : es[j] = α (FreeGroup.of p))
    (hu : es[j + 1] = (α (FreeGroup.of u))⁻¹) :
    u ≠ p ∧ EndsWithWord (coordWord α u) B := by
  constructor
  · exact witness_ne_right_minus α es hred hj hjk hp hu
  · have hwu : (α (FreeGroup.of u)) = (es[j + 1])⁻¹ := by
      rw [hu]
      simp
    have hw : (α (FreeGroup.of u)).toWord = FreeGroup.invRev Z ++ B := by
      calc
        (α (FreeGroup.of u)).toWord = ((es[j + 1])⁻¹).toWord := by rw [hwu]
        _ = FreeGroup.invRev (es[j + 1].toWord) := by rw [FreeGroup.toWord_inv]
        _ = FreeGroup.invRev (FreeGroup.invRev B ++ Z) := by rw [hr]
        _ = FreeGroup.invRev Z ++ B := by
            rw [FreeGroup.invRev_append]
            rw [FreeGroup.invRev_invRev]
    unfold coordWord
    unfold EndsWithWord
    exact ⟨FreeGroup.invRev Z, hw⟩

/-- `es[j] = -w_p`, left neighbour `es[j-1] = +w_v`: `w_v` ends with `invRev A`
and `v ≠ p`. -/
theorem minus_left_plus_witness {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hj0 : 0 < j) (hm : j - 1 < es.length)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hl : (es[j - 1]).toWord = X ++ FreeGroup.invRev A)
    {p v : Fin n} (hp : es[j] = (α (FreeGroup.of p))⁻¹)
    (hv : es[j - 1] = α (FreeGroup.of v)) :
    v ≠ p ∧ EndsWithWord (coordWord α v) (FreeGroup.invRev A) := by
  constructor
  · exact witness_ne_left_plus α es hred hj hj0 hm hp hv
  · unfold coordWord
    rw [← hv]
    unfold EndsWithWord
    exact ⟨X, hl⟩

/-- `es[j] = -w_p`, left neighbour `es[j-1] = -w_v`: `w_v` begins with `A`
and `v ≠ p`. -/
theorem minus_left_minus_witness {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hm : j - 1 < es.length)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hl : (es[j - 1]).toWord = X ++ FreeGroup.invRev A)
    {p v : Fin n} (hp : es[j] = (α (FreeGroup.of p))⁻¹)
    (hv : es[j - 1] = (α (FreeGroup.of v))⁻¹) :
    v ≠ p ∧ BeginsWithWord (coordWord α v) A := by
  constructor
  · exact fallTwo_ne_left_minus α es hred hj hm A B X hAB hmid hl hp hv
  · have hwv : (α (FreeGroup.of v)) = (es[j - 1])⁻¹ := by
      rw [hv]
      simp
    have hw : (α (FreeGroup.of v)).toWord = A ++ FreeGroup.invRev X := by
      calc
        (α (FreeGroup.of v)).toWord = ((es[j - 1])⁻¹).toWord := by rw [hwv]
        _ = FreeGroup.invRev (es[j - 1].toWord) := by rw [FreeGroup.toWord_inv]
        _ = FreeGroup.invRev (X ++ FreeGroup.invRev A) := by rw [hl]
        _ = A ++ FreeGroup.invRev X := by
            rw [FreeGroup.invRev_append]
            rw [FreeGroup.invRev_invRev]
    unfold coordWord
    unfold BeginsWithWord
    exact ⟨FreeGroup.invRev X, hw⟩

/-- `es[j] = -w_p`, right neighbour `es[j+1] = +w_u`: `w_u` begins with
`invRev B` and `u ≠ p`. -/
theorem minus_right_plus_witness {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hjk : j + 1 < es.length)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hr : (es[j + 1]).toWord = FreeGroup.invRev B ++ Z)
    {p u : Fin n} (hp : es[j] = (α (FreeGroup.of p))⁻¹)
    (hu : es[j + 1] = α (FreeGroup.of u)) :
    u ≠ p ∧ BeginsWithWord (coordWord α u) (FreeGroup.invRev B) := by
  constructor
  · exact fallTwo_ne_right_mixed α es hred hj hjk hp hu
  · unfold coordWord
    rw [← hu]
    unfold BeginsWithWord
    exact ⟨Z, hr⟩

/-- `es[j] = -w_p`, right neighbour `es[j+1] = -w_u`: `w_u` ends with `B`
and `u ≠ p`. -/
theorem minus_right_minus_witness {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hjk : j + 1 < es.length)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hr : (es[j + 1]).toWord = FreeGroup.invRev B ++ Z)
    {p u : Fin n} (hp : es[j] = (α (FreeGroup.of p))⁻¹)
    (hu : es[j + 1] = (α (FreeGroup.of u))⁻¹) :
    u ≠ p ∧ EndsWithWord (coordWord α u) B := by
  constructor
  · exact fallTwo_ne_right_minus α es hred hj hjk A B Z hAB hmid hr hp hu
  · have hwu : (α (FreeGroup.of u)) = (es[j + 1])⁻¹ := by
      rw [hu]
      simp
    have hw : (α (FreeGroup.of u)).toWord = FreeGroup.invRev Z ++ B := by
      calc
        (α (FreeGroup.of u)).toWord = ((es[j + 1])⁻¹).toWord := by rw [hwu]
        _ = FreeGroup.invRev (es[j + 1].toWord) := by rw [FreeGroup.toWord_inv]
        _ = FreeGroup.invRev (FreeGroup.invRev B ++ Z) := by rw [hr]
        _ = FreeGroup.invRev Z ++ B := by
            rw [FreeGroup.invRev_append]
            rw [FreeGroup.invRev_invRev]
    unfold coordWord
    unfold EndsWithWord
    exact ⟨FreeGroup.invRev Z, hw⟩


/-! ## The bridge: balanced configuration ⟹ word-level coverability -/

/-- **Balanced factor is word-coverable.**  If a `SystemReduced` aggregate
`es` (with `ImageAggregate α es`, i.e. every factor a basis image up to sign)
has an interior factor `j` at the balanced element `p` — word `A ++ B`
(`|A| = |B|`), `es[j] = ±w_p`, the left neighbour covering `invRev A` and the
right neighbour covering `invRev B` — then `p` is two-sidedly coverable at
the word level (`TwoSidedCoverable α p`): each covering neighbour factor,
whichever sign it carries, supplies one member of the corresponding covering
class of `p`'s own halves. -/
theorem balanced_factor_coverable {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (es : List (FreeGroup (Fin n))) (himg : ImageAggregate α es)
    (hred : SystemReduced es)
    {j : ℕ} (hj : j < es.length) (hj0 : 0 < j) (hj1 : j + 1 < es.length)
    (hm : j - 1 < es.length)
    (A B X Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hmid : (es[j]).toWord = A ++ B)
    (hl : (es[j - 1]).toWord = X ++ FreeGroup.invRev A)
    (hr : (es[j + 1]).toWord = FreeGroup.invRev B ++ Z)
    {p : Fin n} (hpo : es[j] = α (FreeGroup.of p) ∨ es[j] = (α (FreeGroup.of p))⁻¹) :
    TwoSidedCoverable α p := by
  rw [twoSidedCoverable_iff_single]
  have hL : ∃ v : Fin n, es[j - 1] = α (FreeGroup.of v) ∨
      es[j - 1] = (α (FreeGroup.of v))⁻¹ :=
    himg (es[j - 1]) (List.getElem_mem hm)
  have hR : ∃ u : Fin n, es[j + 1] = α (FreeGroup.of u) ∨
      es[j + 1] = (α (FreeGroup.of u))⁻¹ :=
    himg (es[j + 1]) (List.getElem_mem hj1)
  rcases hL with ⟨v, hvo⟩
  rcases hR with ⟨u, huo⟩
  rcases hpo with hp | hp
  · -- es[j] = +w_p : w_p has word A ++ B; LC(A) from the left neighbour,
    -- RC(B) from the right neighbour
    have hpw : (α (FreeGroup.of p)).toWord = A ++ B := by
      rw [← hp]
      exact hmid
    have hc : coordWord α p = A ++ B := by
      unfold coordWord
      exact hpw
    have hLC : LeftCoverClass α p A := by
      rcases hvo with hv | hv
      · have hw := plus_left_plus_witness α es hred hj hm A B X hAB hmid hl hp hv
        exact ⟨v, hw.1, Or.inl hw.2⟩
      · have hw := plus_left_minus_witness α es hred hj hj0 hm A B X hAB hmid hl hp hv
        exact ⟨v, hw.1, Or.inr hw.2⟩
    have hRC : RightCoverClass α p B := by
      rcases huo with hu | hu
      · have hw := plus_right_plus_witness α es hred hj hj1 A B Z hAB hmid hr hp hu
        exact ⟨u, hw.1, Or.inr hw.2⟩
      · have hw := plus_right_minus_witness α es hred hj hj1 A B Z hAB hmid hr hp hu
        exact ⟨u, hw.1, Or.inl hw.2⟩
    rcases firstHalf_append_eq A B hAB with ⟨hA', hB'⟩
    rw [hc, hB', hA']
    exact ⟨hRC, hLC⟩
  · -- es[j] = -w_p : w_p has word (invRev B ++ invRev A); the right neighbour
    -- supplies LC(invRev B), the left neighbour RC(invRev A)
    have hwp : (es[j])⁻¹ = α (FreeGroup.of p) := by
      rw [hp]
      simp
    have hpw : (α (FreeGroup.of p)).toWord =
        FreeGroup.invRev B ++ FreeGroup.invRev A := by
      have hw := neg_image_word (g := es[j]) (w := α (FreeGroup.of p)) A B hmid hwp
      exact hw
    have hc : coordWord α p = FreeGroup.invRev B ++ FreeGroup.invRev A := by
      unfold coordWord
      exact hpw
    have hAB' : (FreeGroup.invRev B).length = (FreeGroup.invRev A).length := by
      rw [FreeGroup.invRev_length]
      rw [FreeGroup.invRev_length]
      exact hAB.symm
    have hLC : LeftCoverClass α p (FreeGroup.invRev B) := by
      rcases huo with hu | hu
      · have hw := minus_right_plus_witness α es hred hj hj1 A B Z hAB hmid hr hp hu
        exact ⟨u, hw.1, Or.inr hw.2⟩
      · have hw := minus_right_minus_witness α es hred hj hj1 A B Z hAB hmid hr hp hu
        exact ⟨u, hw.1,
          Or.inl (by simpa [EndsWithWord, FreeGroup.invRev_invRev] using hw.2)⟩
    have hRC : RightCoverClass α p (FreeGroup.invRev A) := by
      rcases hvo with hv | hv
      · have hw := minus_left_plus_witness α es hred hj hj0 hm A B X hAB hmid hl hp hv
        exact ⟨v, hw.1, Or.inl hw.2⟩
      · have hw := minus_left_minus_witness α es hred hj hm A B X hAB hmid hl hp hv
        exact ⟨v, hw.1,
          Or.inr (by simpa [BeginsWithWord, FreeGroup.invRev_invRev] using hw.2)⟩
    rcases firstHalf_append_eq (FreeGroup.invRev B) (FreeGroup.invRev A) hAB' with
      ⟨h1, h2⟩
    rw [hc, h2, h1]
    exact ⟨hRC, hLC⟩

/-- **A Fall-Two configuration makes its balanced coordinate word-coverable.**
  Every `FallTwoConfig α` exhibits a coordinate `p` (the element of the
  balanced factor) with `TwoSidedCoverable α p`. -/
theorem fallTwoConfig_coverable {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hF : FallTwoConfig α) :
    ∃ p : Fin n, TwoSidedCoverable α p := by
  classical
  rcases hF with ⟨m, j, hj, hj0, hj1, hconf, A, B, X, Z, hA, hAB, hX, hZ⟩
  let es : List (FreeGroup (Fin n)) := imageAggregate α m
  have hred : SystemReduced es := by
    simpa [es] using (SystemReduced_imageAggregate α m)
  have himg : ImageAggregate α es := by
    simpa [es] using (imageAggregate_isImageAggregate α m)
  have hjE : j < es.length := by simpa [es] using hj
  have hj1E : j + 1 < es.length := by simpa [es] using hj1
  have hmE : j - 1 < es.length := by omega
  have hmid : (es[j]).toWord = A ++ B := by simpa [es] using hA
  have hl : (es[j - 1]).toWord = X ++ FreeGroup.invRev A := by simpa [es] using hX
  have hr : (es[j + 1]).toWord = FreeGroup.invRev B ++ Z := by simpa [es] using hZ
  have hp : ∃ p : Fin n, es[j] = α (FreeGroup.of p) ∨ es[j] = (α (FreeGroup.of p))⁻¹ :=
    himg (es[j]) (List.getElem_mem hjE)
  rcases hp with ⟨p, hpo⟩
  refine ⟨p, ?_⟩
  exact balanced_factor_coverable α es himg hred hjE hj0 hj1E hmE A B X Z hAB hmid hl hr hpo

/-- **Exactly-half-absorbed elements are word-coverable.**  If `p` is
exactly-half absorbed between two elements of the ordered state `S`
(`ExactlyHalfAbsorbed S p` — a confined interior factor `±w_c` of the image
aggregate of some standard generator, covered exactly by its two neighbours),
then the word of `c := S.row p` is two-sidedly coverable.  This is the
bridge by which the (stronger) word-level row invariant implies the
aggregate no-reappearance. -/
theorem exactlyHalfAbsorbed_coverable {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (hbal : ExactlyHalfAbsorbed S p) : TwoSidedCoverable S.α (S.row p) := by
  classical
  rcases hbal with ⟨m, j, hj, hj0, hj1, hconf, hpo, A, B, X, Z, hA, hAB, hX, hZ⟩
  let es : List (FreeGroup (Fin n)) := imageAggregate S.α m
  have hred : SystemReduced es := by
    simpa [es] using (SystemReduced_imageAggregate S.α m)
  have himg : ImageAggregate S.α es := by
    simpa [es] using (imageAggregate_isImageAggregate S.α m)
  have hjE : j < es.length := by simpa [es] using hj
  have hj1E : j + 1 < es.length := by simpa [es] using hj1
  have hmE : j - 1 < es.length := by omega
  have hmid : (es[j]).toWord = A ++ B := by simpa [es] using hA
  have hl : (es[j - 1]).toWord = X ++ FreeGroup.invRev A := by simpa [es] using hX
  have hr : (es[j + 1]).toWord = FreeGroup.invRev B ++ Z := by simpa [es] using hZ
  have hpo' : es[j] = S.α (FreeGroup.of (S.row p)) ∨
      es[j] = (S.α (FreeGroup.of (S.row p)))⁻¹ := by simpa [es] using hpo
  exact balanced_factor_coverable S.α es himg hred hjE hj0 hj1E hmE A B X Z hAB hmid hl hr hpo'


/-- **Word-free rows are aggregate-free (the load-bearing contrapositive).**
  If no coordinate of the state is word-level two-sidedly coverable (the
  word-level row invariant), then no coordinate is exactly-half absorbed
  between two elements of the state: every exactly-half-absorbed element is
  word-coverable (`exactlyHalfAbsorbed_coverable`), so the stronger word-level
  no-coverability implies the aggregate no-reappearance the Fall-II index
  argument consumes. -/
theorem coverable_free_not_absorbed {n : ℕ} (S : RebalanceState n)
    (h : ∀ i : Fin n, ¬ TwoSidedCoverable S.α (S.row i)) :
    ∀ p : Fin n, ¬ ExactlyHalfAbsorbed S p := by
  intro p hp
  exact h p (exactlyHalfAbsorbed_coverable S p hp)

end Submission.Nielsen



