import Mathlib
import Submission.Work.Layout.SortDefs

set_option autoImplicit false

/-!
# Specification of the `mergePair` / `pass2` words, as `Prop`s

`MergePairSpec` is (up to the numeric cost constant) exactly the content of
`Work.Layout.Sk.mergePair_ev` (proved in `Submission/Work/Layout/mergePair_ev.lean`), phrased as a
`Prop` so that the pass lemma can be stated and proved *conditionally* on it; `Pass2Spec` is the
content of `Work.Layout.Sk.pass2_ev`.

The cost constants below are deliberately generous (they are polynomials in `KLt + KSz`, where
`KLt`/`KSz` are the constants of `IntLib.lt`/`IntLib.size`): the top-level statement of
`sortByKeyWord` only asks for the *existence* of a constant, so any polynomial in `KLt, KSz` will do,
and a generous constant makes the arithmetic in the proofs easy.
-/

namespace Work.Layout
namespace Sk

open HvdH

/-- the per-merge cost constant -/
def MPc (KLt KSz : ℕ) : ℕ := 200 * (KLt + KSz) + 4000

/-- the per-pass cost constant -/
def P2c (KLt KSz : ℕ) : ℕ := 20000 * (KLt + KSz) + 400000

/-- the size contribution of a list of runs: `Σ (vsz + 1)` over the elements of all the runs -/
def totR (rs : List (List Val)) : ℕ := (rs.flatten.map vsz).sum + rs.flatten.length

/-- `MergePairSpec ...` : the `mergePair` word merges the two top runs of `SX` and `SY` onto `D` as the
`gMark`-terminated run `merge2 P Q`, with cost `≤ MPc KLt KSz * (sum vsz + length + 2)`.

The stacks `SX, SY, T, D, SA, SB, F1, F2, t, d, 0` must be pairwise distinct (the application
supplies this); `SA`/`SB` receive the cached key sizes and are cleaned up at the end, `F1`/`F2` are the
comparison flags, `t`/`d` the mover's scratch stacks. -/
def MergePairSpec (main pLt pSz : Cmd) (SX SY T D SA SB F1 F2 tx dd : Stk) (KLt KSz : ℕ) : Prop :=
  ∀ (P Q : List Val) (A B' Tc Dc Sc Sc' : List Glyph) (g : Reg → Glyph) (S : Stk → List Glyph),
    S SX = encs P ++ gMark :: A → S SY = encs Q ++ gMark :: B' →
    S T = Tc → S D = Dc → S SA = Sc → S SB = Sc' → P ≠ [] → Q ≠ [] →
    (∀ v ∈ P, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v') →
    (∀ v ∈ Q, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v') →
    P.Pairwise (fun a b => pairKey a < pairKey b) →
    Q.Pairwise (fun a b => pairKey a < pairKey b) →
    ((P ++ Q).map pairKey).Nodup →
    ∃ s' n, Ev main (mergePair pLt pSz SX SY T D SA SB F1 F2 tx dd) ⟨g, S⟩ s' n ∧
      n ≤ MPc KLt KSz * (((P ++ Q).map vsz).sum + (P ++ Q).length + 2) ∧
      s'.stk SX = A ∧ s'.stk SY = B' ∧ s'.stk T = Tc ∧
      s'.stk D = encs (merge2 P Q) ++ gMark :: Dc ∧
      s'.stk SA = Sc ∧ s'.stk SB = Sc' ∧
      (∀ k : Stk, k ≠ SX → k ≠ SY → k ≠ T → k ≠ D → k ≠ SA → k ≠ SB → s'.stk k = S k)

/-- the `distribute` word: split the `cons`-chain `ofList xs` on stack 0 into singleton runs on `X` and
`Y`, alternately -/
def DistSpec (main : Cmd) : Prop :=
  ∀ {X Y t d : Stk}, ([X, Y, t, d, 0] : List Stk).Nodup →
  ∀ {g : Reg → Glyph} {S : Stk → List Glyph} {xs : List Val} {A J1 J2 : List Glyph},
    S 0 = (ofList xs).enc ++ A →
    S X = runEncB ([] : List (List Val)) ++ J1 →
    S Y = runEncB ([] : List (List Val)) ++ J2 →
    ∃ s' n, Ev main (distribute X Y t d) ⟨g, S⟩ s' n ∧ n ≤ 60 * (vsz (ofList xs) + 1) ∧
      s'.stk 0 = A ∧ s'.stk X = runEncB (altSplit xs).1 ++ J1 ∧
      s'.stk Y = runEncB (altSplit xs).2 ++ J2 ∧
      (∀ k : Stk, k ≠ 0 → k ≠ X → k ≠ Y → s'.stk k = S k)

/-- the `assemble` word: turn the single run on `X` back into the `cons`-chain on stack 0 -/
def AsmSpec (main : Cmd) : Prop :=
  ∀ {X Z t d : Stk}, ([X, Z, t, d, 0] : List Stk).Nodup →
  ∀ {g : Reg → Glyph} {S : Stk → List Glyph} {rs : List (List Val)} {J R : List Glyph},
    S X = runEncB rs ++ J → rs.length ≤ 1 →
    (∀ v ∈ rs.flatten, ∃ (a b : Val), v = Val.cons a b) →
    (∀ r ∈ rs, r ≠ []) →
    S 0 = R →
    ∃ s' n, Ev main (assemble X Z t d) ⟨g, S⟩ s' n ∧
      n ≤ 80 * ((rs.flatten.map vsz).sum + rs.flatten.length + 2) ∧
      s'.stk 0 = (ofList rs.flatten).enc ++ R ∧ s'.stk X = J ∧
      (∀ k : Stk, k ≠ X → k ≠ 0 → s'.stk k = S k)

/-- `MergePairAll ...` : the `mergePair` word is correct **for every** admissible tuple of distinct
stacks.  This is the content of `Work.Layout.Sk.mergePair_ev` (the `hLt`/`hSz` cost hypotheses of
that lemma quantify over `main` and are supplied once and for all at the top level), and it is what
the two merge passes of `pass2` need: the second pass merges with sources `C`,`D` into `X`,`Y`, a
different tuple from the first pass. -/
def MergePairAll (main pLt pSz : Cmd) (KLt KSz : ℕ) : Prop :=
  ∀ (SX SY T D SA SB F1 F2 t d : Stk),
    ([SX, SY, T, D, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup →
    MergePairSpec main pLt pSz SX SY T D SA SB F1 F2 t d KLt KSz

/-- the two-pass lemma (content of `pass2_ev`), *conditional* on `MergePairAll` for the merge word:
the two merge passes need `MergePairSpec` at two different stack tuples (sources `X`,`Y` into `C`,`D`,
and then sources `C`,`D` back into `X`,`Y`), which `MergePairAll` provides. -/
def Pass2Spec (main pLt pSz : Cmd) (KLt KSz : ℕ) : Prop :=
  MergePairAll main pLt pSz KLt KSz →
  ∀ {X Y C D T1 T2 SA SB F1 F2 t d : Stk},
    ([X, Y, C, D, T1, T2, SA, SB, F1, F2, t, d, 0] : List Stk).Nodup →
    ∀ {g : Reg → Glyph} {S : Stk → List Glyph} {ps qs : List (List Val)} {JX JY JC JD : List Glyph},
    S X = runEncB ps ++ JX → S Y = runEncB qs ++ JY →
    S C = runEncB ([] : List (List Val)) ++ JC → S D = runEncB ([] : List (List Val)) ++ JD →
    (ps.length = qs.length ∨ ps.length = qs.length + 1) →
    (∀ r ∈ ps ++ qs, r ≠ []) →
    (∀ v ∈ (ps ++ qs).flatten, ∃ (k : ℕ) (v' : Val), v = Val.cons (Val.int (k : ℤ)) v') →
    (∀ r ∈ ps ++ qs, r.Pairwise (fun a b => pairKey a < pairKey b)) →
    (((ps ++ qs).flatten).map pairKey).Nodup →
    ∃ s' n, Ev main (pass2 pLt pSz X Y C D T1 T2 SA SB F1 F2 t d) ⟨g, S⟩ s' n ∧
      n ≤ P2c KLt KSz *
        (((ps ++ qs).flatten.map vsz).sum + (ps ++ qs).flatten.length + 2 * (ps.length + qs.length) + 4) ∧
      s'.stk X = runEncB (pass2R ps qs).1 ++ JX ∧
      s'.stk Y = runEncB (pass2R ps qs).2 ++ JY ∧
      s'.stk C = runEncB ([] : List (List Val)) ++ JC ∧
      s'.stk D = runEncB ([] : List (List Val)) ++ JD ∧
      (∀ k : Stk, k ≠ X → k ≠ Y → k ≠ C → k ≠ D → s'.stk k = S k) ∧
      (∀ r ∈ (pass2R ps qs).1 ++ (pass2R ps qs).2, r ≠ []) ∧
      (((pass2R ps qs).1 ++ (pass2R ps qs).2).flatten).Perm ((ps ++ qs).flatten) ∧
      ((pass2R ps qs).1.length = (pass2R ps qs).2.length ∨
        (pass2R ps qs).1.length = (pass2R ps qs).2.length + 1) ∧
      (∀ r ∈ (pass2R ps qs).1 ++ (pass2R ps qs).2, r.Pairwise (fun a b => pairKey a < pairKey b))

/-- the pure list facts (`sortListFacts`) -/
def ListsSpec : Prop :=
    (∀ P Q : List Val, (merge2 P Q).Perm (P ++ Q)) ∧
    (∀ P Q : List Val, (merge2 P Q).length = P.length + Q.length) ∧
    (∀ P Q : List Val,
      P.Pairwise (fun a b => pairKey a < pairKey b) →
      Q.Pairwise (fun a b => pairKey a < pairKey b) →
      ((P ++ Q).map pairKey).Nodup →
      (merge2 P Q).Pairwise (fun a b => pairKey a < pairKey b)) ∧
    (∀ (r : List Val) (rs : List (List Val)), runEnc (r :: rs) = encs r ++ gMark :: runEnc rs) ∧
    (∀ rs rs' : List (List Val), runEnc (rs ++ rs') = runEnc rs ++ runEnc rs') ∧
    (runEnc ([] : List (List Val)) = ([] : List Glyph)) ∧
    (runEncB ([] : List (List Val)) = [gBnd]) ∧
    (∀ (r : List Val) (rs : List (List Val)), runEncB (r :: rs) = encs r ++ gMark :: runEncB rs) ∧
    (∀ ps qs : List (List Val), ps.length = qs.length ∨ ps.length = qs.length + 1 →
      (passR ps qs).1.length + (passR ps qs).2.length = (ps.length + qs.length + 1) / 2) ∧
    (∀ ps qs : List (List Val), ps.length = qs.length ∨ ps.length = qs.length + 1 →
      (passR ps qs).1.length = (passR ps qs).2.length ∨
        (passR ps qs).1.length = (passR ps qs).2.length + 1) ∧
    (∀ ps qs : List (List Val), ps.length = qs.length ∨ ps.length = qs.length + 1 →
      ((passR ps qs).1 ++ (passR ps qs).2).flatten.Perm ((ps ++ qs).flatten)) ∧
    (∀ ps qs : List (List Val), ps.length = qs.length ∨ ps.length = qs.length + 1 →
      (∀ r ∈ ps ++ qs, r.Pairwise (fun a b => pairKey a < pairKey b)) →
      (((ps ++ qs).flatten).map pairKey).Nodup →
      (∀ r ∈ (passR ps qs).1 ++ (passR ps qs).2, r.Pairwise (fun a b => pairKey a < pairKey b))) ∧
    (∀ ps qs : List (List Val), ps.length = qs.length ∨ ps.length = qs.length + 1 →
      (pass2R ps qs).1.length + (pass2R ps qs).2.length = ((ps.length + qs.length + 1) / 2 + 1) / 2) ∧
    (∀ ps qs : List (List Val), ps.length = qs.length ∨ ps.length = qs.length + 1 →
      (pass2R ps qs).1.length = (pass2R ps qs).2.length ∨
        (pass2R ps qs).1.length = (pass2R ps qs).2.length + 1) ∧
    (∀ ps qs : List (List Val), ps.length = qs.length ∨ ps.length = qs.length + 1 →
      ((pass2R ps qs).1 ++ (pass2R ps qs).2).flatten.Perm ((ps ++ qs).flatten)) ∧
    (∀ ps qs : List (List Val), ps.length = qs.length ∨ ps.length = qs.length + 1 →
      (∀ r ∈ ps ++ qs, r.Pairwise (fun a b => pairKey a < pairKey b)) →
      (((ps ++ qs).flatten).map pairKey).Nodup →
      (∀ r ∈ (pass2R ps qs).1 ++ (pass2R ps qs).2, r.Pairwise (fun a b => pairKey a < pairKey b))) ∧
    (∀ xs : List Val, (altSplit xs).1.length + (altSplit xs).2.length = xs.length) ∧
    (∀ xs : List Val, (altSplit xs).1.length = (altSplit xs).2.length ∨
      (altSplit xs).1.length = (altSplit xs).2.length + 1) ∧
    (∀ xs : List Val, ((altSplit xs).1 ++ (altSplit xs).2).flatten.Perm xs) ∧
    (∀ xs : List Val, ∀ r ∈ (altSplit xs).1 ++ (altSplit xs).2, r.length = 1)

end Sk
end Work.Layout
