import Submission.Work.Item3.AssemblyRun
import Submission.Work.Item3.OtherRCDispatch

open Submission.Nielsen
open Commons.GroupTheory.FreeGroup
open FreeGroup
set_option autoImplicit false

/-!
# BranchCaseC: `c ∉ RC (y)` for `y ∉ {B, invRev A}` at half-length 1

Candidate (i) of the `branchCompensation` sketch (`FallTwoRunNotes.md`): in a
genuine run with half-length `k = 1` (`A = [a]`, `B = [b]`), the balanced
coordinate `c = S.row p` (word `A ++ B`) is NOT in the right covering class of
a single-letter block `y` unless `y = b` or `y = invRev a`:

    ¬ (EndsWithWord (coordWord α' c) [y] ∨
        BeginsWithWord (coordWord α' c) (FreeGroup.invRev [y]))

for `y ≠ b` and `y ≠ invRev a`.  So an rc-coverer `u` with `y ∉ {B, invRev A}`
is necessarily a row ≠ c — the first structural fact the case analysis needs
before it can distinguish rows.

The two pure letter facts: a two-letter word `[a, b]` ending in the single
letter `y` forces `y = b`; beginning with `invRev [y]` forces `y = invRev a`.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- A two-letter word ending in the single letter `y` forces the last letter
to be `y`. -/
theorem end_letter_of_end_with {α : Type*} [DecidableEq α] (a b y : α × Bool)
    (h : EndsWithWord ([a] ++ [b]) [y]) : y = b := by
  rcases h with ⟨S, hS⟩
  have hlen : S.length = 1 := by
    have := congrArg List.length hS
    simp [List.length_append] at this
    omega
  obtain ⟨s, rfl⟩ := List.length_eq_one_iff.mp hlen
  have h' : a :: [b] = s :: [y] := by simpa using hS
  have h2 : [b] = [y] := (List.cons.inj h').2
  exact (List.singleton_inj.mp h2).symm

/-- A two-letter word `[a, b]` beginning with `invRev [y]` forces
`y = invRev a`. -/
theorem invLetter_of_begins_with {α : Type*} [DecidableEq α] (a b y : α × Bool)
    (h : BeginsWithWord ([a] ++ [b]) (FreeGroup.invRev [y])) : y = (a.1, !a.2) := by
  rcases h with ⟨S, hS⟩
  have hlen : S.length = 1 := by
    have := congrArg List.length hS
    simp [List.length_append] at this
    omega
  obtain ⟨s, rfl⟩ := List.length_eq_one_iff.mp hlen
  have hinv : FreeGroup.invRev [y] = [(y.1, !y.2)] := by simp [FreeGroup.invRev]
  have h' : a :: [b] = (y.1, !y.2) :: [s] := by
    rw [hinv] at hS
    simpa using hS
  have ha : a = (y.1, !y.2) := (List.cons.inj h').1
  have hy : y = (a.1, !a.2) := by
    rw [ha]
    cases y with
    | mk y1 y2 => cases y2 <;> rfl
  exact hy

/-- **Candidate (i) (PROVED).**  In a genuine run with half-length `1`
(`A = [a]`, `B = [b]`), the balanced coordinate is not in the right covering
class of a single-letter block `y` unless `y = b` or `y = invRev a`. -/
theorem coverer_ne_c_k1 {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (a b y : Fin n × Bool) (α' : MulAut (FreeGroup (Fin n)))
    (h : GenuineRunTo S p [a] [b] α') (hyb : y ≠ b) (hya : y ≠ (a.1, !a.2)) :
    ¬ (EndsWithWord (coordWord α' (S.row p)) [y] ∨
        BeginsWithWord (coordWord α' (S.row p)) (FreeGroup.invRev [y])) := by
  have hc : coordWord α' (S.row p) = [a] ++ [b] := by
    simpa using run_c_word_post S p [a] [b] α' h
  rintro (hend | hbeg)
  · exact hyb (end_letter_of_end_with a b y (by rwa [hc] at hend))
  · exact hya (invLetter_of_begins_with a b y (by rwa [hc] at hbeg))

/-- **Letter form of NoPassActive at a two-letter row.**  If the post-word of
`q` is `[x] ++ [y]` and does not end with `[b]` (NoPassActive at `q` when
`B = [b]`), then `y ≠ b`. -/
theorem low_word_second_ne_B {n : ℕ} (α' : MulAut (FreeGroup (Fin n))) {q : Fin n}
    (x y b : Fin n × Bool)
    (hq : coordWord α' q = [x] ++ [y])
    (hNW : ¬ EndsWithWord (coordWord α' q) [b]) : y ≠ b := by
  intro hyb
  apply hNW
  rw [hq, hyb]
  exact EndsWithWord_append [x] [b]

/-- **Letter form of `¬ endInv` at a two-letter row.**  If the post-word of
`q` is `[x] ++ [y]` and does not end with `invRev [a]` (the `¬ endInv`
condition when `A = [a]`), then `y ≠ invRev a`. -/
theorem low_word_second_ne_invRevA {n : ℕ} (α' : MulAut (FreeGroup (Fin n))) {q : Fin n}
    (x y a : Fin n × Bool)
    (hq : coordWord α' q = [x] ++ [y])
    (hNI : ¬ EndsWithWord (coordWord α' q) (FreeGroup.invRev [a])) :
    y ≠ (a.1, !a.2) := by
  intro hya
  apply hNI
  have hinv : FreeGroup.invRev [a] = [(a.1, !a.2)] := by simp [FreeGroup.invRev]
  rw [hq, hinv, hya]
  exact EndsWithWord_append [x] [(a.1, !a.2)]

/-- **Candidate (ii): the OTHER-rc coverer is not the balanced row (k = 1).**
Applying `coverer_ne_c_k1` under the OTHER-rc conditions: if `q`'s post-word
is the two-letter word `[x] ++ [y]`, `q` is not in the ends-class (`y ≠ b`,
from NoPassActive) and not `endInv` (`y ≠ invRev a`), then any rc-coverer `u`
of `q` (with the usual ends/`invRev` disjunction) is a row **≠ `c`**.  This is
the first row-distinguishing step of the `branchCompensation` case split. -/
theorem otherRC_coverer_ne_c_k1 {n : ℕ} (S : RebalanceState n) (p : Fin n)
    (a b x y : Fin n × Bool) (α' : MulAut (FreeGroup (Fin n)))
    (h : GenuineRunTo S p [a] [b] α') {q u : Fin n}
    (hq : coordWord α' q = [x] ++ [y])
    (hNB : ¬ EndsWithWord (coordWord α' q) [b])
    (hNI : ¬ EndsWithWord (coordWord α' q) (FreeGroup.invRev [a]))
    (hcov : EndsWithWord (coordWord α' u) [y] ∨
      BeginsWithWord (coordWord α' u) (FreeGroup.invRev [y])) :
    u ≠ S.row p := by
  intro huc
  subst huc
  have hyb : y ≠ b := low_word_second_ne_B α' x y b hq hNB
  have hya : y ≠ (a.1, !a.2) := low_word_second_ne_invRevA α' x y a hq hNI
  exact coverer_ne_c_k1 S p a b y α' h hyb hya (hcov)

/-! ## Candidate (iii): the S2-introduction rule for ends-moved rows

Machine characterization of the S2-realizing pairs (`/tmp/fg2`, n = 4, 10
pairs): every one consists of an UNCHANGED row `a` and a PASS-MOVED row `b`
(9 of 10; the tenth has both roles swapped) whose words differ by exactly one
leading letter (`W_a = [z] ++ W_b`) — with no uniform letter identity for `z`
(it is `U`'s first letter in some traces, `B_p` or `invRev` letters in
others).  So the usable form of candidate (iii) is the S2 *introduction* rule:
exhibiting a one-letter-prefix-extension pair yields the S2 shape, hence
participation.  (The derivation of the pair — the third-row selection rule —
remains open; this is the interface the case analysis invokes once it has
one.) -/

/-- **S2-introduction rule.**  If the image of `a` is its partner's word with
one extra leading letter `[z]` (and `|w_a| ≥ 2`), then the pair `(a,b)`
realizes the S2 shape: `ShapePair α a b`. -/
theorem shapePair_s2_of_one_letter_prefix {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {a b : Fin n} (hab : a ≠ b) (z : Fin n × Bool)
    (h : (α (FreeGroup.of a)).toWord = [z] ++ (α (FreeGroup.of b)).toWord)
    (hlen : 2 ≤ FreeGroup.norm (α (FreeGroup.of a))) : ShapePair α a b :=
  ⟨hab, Or.inr (Or.inl ⟨z, h, hlen⟩)⟩

/-- **Participation from S2.**  A one-letter-prefix-extension pair makes the
first coordinate participate in a shape (`HasShapePairAt`), hence (with the
dispatch) yields a strict single move. -/
theorem hasShapePairAt_of_one_letter_prefix {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {a b : Fin n} (hab : a ≠ b) (z : Fin n × Bool)
    (h : (α (FreeGroup.of a)).toWord = [z] ++ (α (FreeGroup.of b)).toWord)
    (hlen : 2 ≤ FreeGroup.norm (α (FreeGroup.of a))) : HasShapePairAt α a :=
  Or.inl ⟨b, shapePair_s2_of_one_letter_prefix α hab z h hlen⟩

/-! ## The shape-introduction toolkit (S1–S7)

Each shape's word identity, once exhibited, yields `ShapePair` (its disjunct)
and hence participation.  The S2 rule is above; the rest are the same
one-liners (the disjuncts of `ShapePair`, in order: S1 `[z]++invRev`,
S2 `[z]++`, S3 `invRev W_a ++ S`, S4 `W_a = W_b ++ S`, S5 `W_b = W_a ++ S`,
S6 shared-prefix, S7 zipper). -/

/-- **S3-introduction rule** (`W_b = invRev W_a ++ S`, `|S| < |w_a|`) — the
candidate-(iii) mirror with the inverse-reversal pattern. -/
theorem shapePair_s3_of_invRev_prefix {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {a b : Fin n} (hab : a ≠ b) (S : List (Fin n × Bool))
    (h : (α (FreeGroup.of b)).toWord =
      FreeGroup.invRev ((α (FreeGroup.of a)).toWord) ++ S)
    (hshort : S.length < FreeGroup.norm (α (FreeGroup.of a))) : ShapePair α a b :=
  ⟨hab, Or.inr (Or.inr (Or.inl ⟨S, h, hshort⟩))⟩

/-- **S4-introduction rule** (`W_a = W_b ++ S`, `|S| < |w_a|`). -/
theorem shapePair_s4_of_prefix {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {a b : Fin n} (hab : a ≠ b) (S : List (Fin n × Bool))
    (h : (α (FreeGroup.of a)).toWord = (α (FreeGroup.of b)).toWord ++ S)
    (hshort : S.length < FreeGroup.norm (α (FreeGroup.of a))) : ShapePair α a b :=
  ⟨hab, Or.inr (Or.inr (Or.inr (Or.inl ⟨S, h, hshort⟩)))⟩

/-- **S5-introduction rule** (`W_b = W_a ++ S`, `|S| < |w_a|`). -/
theorem shapePair_s5_of_prefix {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {a b : Fin n} (hab : a ≠ b) (S : List (Fin n × Bool))
    (h : (α (FreeGroup.of b)).toWord = (α (FreeGroup.of a)).toWord ++ S)
    (hshort : S.length < FreeGroup.norm (α (FreeGroup.of a))) : ShapePair α a b :=
  ⟨hab, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨S, h, hshort⟩))))⟩

/-- **S1-introduction rule** (`W_a = [z] ++ invRev W_b`, `2 ≤ |w_a|`). -/
theorem shapePair_s1_of_one_letter_invRev {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {a b : Fin n} (hab : a ≠ b) (z : Fin n × Bool)
    (h : (α (FreeGroup.of a)).toWord = [z] ++ FreeGroup.invRev ((α (FreeGroup.of b)).toWord))
    (hlen : 2 ≤ FreeGroup.norm (α (FreeGroup.of a))) : ShapePair α a b :=
  ⟨hab, Or.inl ⟨z, h, hlen⟩⟩

/-- **S6-introduction rule** (`W_a = P ++ [y]`, `W_b = P ++ S ++ [y]`,
`|S| + 2 < |w_a|`). -/
theorem shapePair_s6_of_shared_prefix {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {a b : Fin n} (hab : a ≠ b) (P S : List (Fin n × Bool)) (y : Fin n × Bool)
    (hu : (α (FreeGroup.of a)).toWord = P ++ [y])
    (hv : (α (FreeGroup.of b)).toWord = P ++ S ++ [y])
    (hshort : S.length + 2 < FreeGroup.norm (α (FreeGroup.of a))) : ShapePair α a b :=
  ⟨hab, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨P, S, y, hu, hv, hshort⟩)))))⟩

/-- **S7-introduction rule** (zipper: `W_a = Xa ++ Z`,
`W_b = invRev Z ++ Xb`, `|W_b| < 2|Z|`). -/
theorem shapePair_s7_of_zipper {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {a b : Fin n} (hab : a ≠ b) (Xa Xb Z : List (Fin n × Bool))
    (hu : (α (FreeGroup.of a)).toWord = Xa ++ Z)
    (hv : (α (FreeGroup.of b)).toWord = FreeGroup.invRev Z ++ Xb)
    (hshort : (α (FreeGroup.of b)).toWord.length < 2 * Z.length) : ShapePair α a b :=
  ⟨hab, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (show ∃ (_ _ _ : List (Fin n × Bool)), _ from ⟨Xa, Xb, Z, hu, hv, hshort⟩))))))⟩

/-- **Participation from S3.** -/
theorem hasShapePairAt_of_invRev_prefix {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {a b : Fin n} (hab : a ≠ b) (S : List (Fin n × Bool))
    (h : (α (FreeGroup.of b)).toWord =
      FreeGroup.invRev ((α (FreeGroup.of a)).toWord) ++ S)
    (hshort : S.length < FreeGroup.norm (α (FreeGroup.of a))) : HasShapePairAt α a :=
  Or.inl ⟨b, shapePair_s3_of_invRev_prefix α hab S h hshort⟩

/-- **Participation from S4.** -/
theorem hasShapePairAt_of_prefix {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {a b : Fin n} (hab : a ≠ b) (S : List (Fin n × Bool))
    (h : (α (FreeGroup.of a)).toWord = (α (FreeGroup.of b)).toWord ++ S)
    (hshort : S.length < FreeGroup.norm (α (FreeGroup.of a))) : HasShapePairAt α a :=
  Or.inl ⟨b, shapePair_s4_of_prefix α hab S h hshort⟩

/-- **Participation from S5.** -/
theorem hasShapePairAt_of_suffix {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {a b : Fin n} (hab : a ≠ b) (S : List (Fin n × Bool))
    (h : (α (FreeGroup.of b)).toWord = (α (FreeGroup.of a)).toWord ++ S)
    (hshort : S.length < FreeGroup.norm (α (FreeGroup.of a))) : HasShapePairAt α a :=
  Or.inl ⟨b, shapePair_s5_of_prefix α hab S h hshort⟩

end Submission.Nielsen
