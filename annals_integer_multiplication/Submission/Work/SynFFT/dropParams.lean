import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs

/-!
# `Work.SynFFT.dropParams`: drop the four parameters left behind by the axis loop

`DropParamsProp` asks for a word which, given the stack

`w :: intList ts :: int sgn :: int r :: int p :: rest`

returns `w :: rest`, at cost `K * (vsz w + vsz (intList ts) + isz sgn + isz r + isz p + 5)`.

The value `w` sits *above* the four parameters and `KLib.drop` removes only the top value, so the
word first *bubbles* `w` past the four parameters by four `KLib.roll 4` moves,

`[w,a,b,c,d] ↦ [d,w,a,b,c] ↦ [c,d,w,a,b] ↦ [b,c,d,w,a] ↦ [a,b,c,d,w]`,

and then removes the four parameters `a,b,c,d` with four `KLib.drop`s.  Every `roll 4` inspects the
five values `{w,a,b,c,d}` and costs `Kr·5·(S+1)`; every `drop` costs `Kd·(vsz·+1) ≤ Kd·(S+1)`,
where `S = vsz w + vsz a + vsz b + vsz c + vsz d`.  Hence the total is at most
`(20·Kr + 4·Kd)·(S+1) ≤ (20·Kr + 4·Kd)·(S+5)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.SynFFT

open HvdH

local infixr:68 " ;;; " => HvdH.Cmd.seq

namespace DropKit

/-- One `KLib.roll k` step, stated on an explicit input list `A` and an explicit output list
`A'`. -/
theorem rollStep {main : Cmd} {rollP : ℕ → Cmd} {Kr : ℕ}
    (h : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k+1) * (((vs.take (k+1)).map vsz).sum + 1)))
    (k : ℕ) (A A' : List Val) (hk : k < A.length)
    (hA : A.getD k .nil :: A.eraseIdx k = A') (D : ℕ)
    (hD : Kr * (k+1) * (((A.take (k+1)).map vsz).sum + 1) ≤ D) :
    WordR main (rollP k) (fun vs => vs = A) (fun _ out => out = A') (fun _ => D) :=
  MrgKit.WordR_conseqC (h k) hk (fun out hout => by rw [hout]; exact hA) hD

/-- A `roll 4` on a list whose first five values have total size at most `S`, at cost
`Kr * 5 * (S + 1)`. -/
theorem rollStep4 {main : Cmd} {rollP : ℕ → Cmd} {Kr S : ℕ}
    (h : ∀ k, WordR main (rollP k) (fun vs => k < vs.length)
      (fun vs out => out = vs.getD k .nil :: vs.eraseIdx k)
      (fun vs => Kr * (k+1) * (((vs.take (k+1)).map vsz).sum + 1)))
    (A A' : List Val) (hk : 4 < A.length) (hA : A.getD 4 .nil :: A.eraseIdx 4 = A')
    (hS : (((A.take 5).map vsz).sum) ≤ S) :
    WordR main (rollP 4) (fun vs => vs = A) (fun _ out => out = A') (fun _ => Kr * 5 * (S + 1)) := by
  refine MrgKit.WordR_conseqC (h 4) hk ?_ ?_
  · intro out hout; rw [hout]; exact hA
  · have h2 : (((A.take 5).map vsz).sum + 1) ≤ S + 1 := by omega
    calc Kr * (4 + 1) * (((A.take 5).map vsz).sum + 1)
        = Kr * 5 * (((A.take 5).map vsz).sum + 1) := by ring
      _ ≤ Kr * 5 * (S + 1) := Nat.mul_le_mul_left (Kr * 5) h2

/-- Size of the first five values of a five-element cons chain. -/
theorem takeFive_sum_le {S : ℕ} (x1 x2 x3 x4 x5 : Val) (t : List Val)
    (h : vsz x1 + vsz x2 + vsz x3 + vsz x4 + vsz x5 ≤ S) :
    (((x1 :: x2 :: x3 :: x4 :: x5 :: t).take 5).map vsz).sum ≤ S := by
  simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  omega

/-- One `KLib.drop` step, stated on an explicit stack `a :: l`. -/
theorem dropStep {main : Cmd} {p : Cmd} {K : ℕ}
    (h : WordR main p (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1)))
    (a : Val) (l : List Val) :
    WordR main p (fun vs => vs = a :: l) (fun _ out => out = l) (fun _ => K * (vsz a + 1)) := by
  refine MrgKit.WordR_conseqC h (by simp) ?_ ?_
  · intro out hout
    obtain ⟨v, r, hv, ho⟩ := hout
    rw [List.cons.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact ho
  · simp [List.headD]

/-- A `drop` step with its cost re-bounded by `K * (S + 1)`, given `vsz a ≤ S`. -/
theorem dropStep' {main : Cmd} {p : Cmd} {K S : ℕ}
    (h : WordR main p (fun vs => vs ≠ [])
      (fun vs out => ∃ v rest, vs = v :: rest ∧ out = rest)
      (fun vs => K * (vsz (vs.headD .nil) + 1)))
    (a : Val) (l : List Val) (hS : vsz a ≤ S) :
    WordR main p (fun vs => vs = a :: l) (fun _ out => out = l) (fun _ => K * (S + 1)) := by
  refine MrgKit.WordR_weaken (dropStep h a l) (fun vs hvs => hvs)
    (fun vs out _ hout => hout) ?_
  intro vs _
  exact Nat.mul_le_mul_left K (by omega)

end DropKit

theorem dropParams (hk : Work.SynFFT.KLib) : Work.SynFFT.DropParamsProp := by
  obtain ⟨rollP, Kr, hroll⟩ := hk.roll
  obtain ⟨dropP, Kd, hdrop⟩ := hk.drop
  refine ⟨rollP 4 ;;; rollP 4 ;;; rollP 4 ;;; rollP 4 ;;;
    dropP ;;; dropP ;;; dropP ;;; dropP, 20 * Kr + 4 * Kd, ?_⟩
  intro main w ts sgn r p rest
  let a : Val := intList ts
  let b : Val := .int sgn
  let c : Val := .int (r : ℤ)
  let d : Val := .int (p : ℤ)
  let S : ℕ := vsz w + vsz a + vsz b + vsz c + vsz d
  let Dr : ℕ := Kr * 5 * (S + 1)
  let Dd : ℕ := Kd * (S + 1)
  -- ### the four `roll 4` moves bubbling `w` past the four parameters
  have r1 : WordR main (rollP 4) (fun vs => vs = w :: a :: b :: c :: d :: rest)
      (fun _ out => out = d :: w :: a :: b :: c :: rest) (fun _ => Dr) :=
    DropKit.rollStep4 (hroll main) (w :: a :: b :: c :: d :: rest)
      (d :: w :: a :: b :: c :: rest) (by simp only [List.length_cons]; omega)
      (by simp only [List.getD_cons_succ, List.getD_cons_zero, List.eraseIdx_cons_succ,
        List.eraseIdx_cons_zero])
      (DropKit.takeFive_sum_le w a b c d rest (by dsimp only [S]; omega))
  have r2 : WordR main (rollP 4) (fun vs => vs = d :: w :: a :: b :: c :: rest)
      (fun _ out => out = c :: d :: w :: a :: b :: rest) (fun _ => Dr) :=
    DropKit.rollStep4 (hroll main) (d :: w :: a :: b :: c :: rest)
      (c :: d :: w :: a :: b :: rest) (by simp only [List.length_cons]; omega)
      (by simp only [List.getD_cons_succ, List.getD_cons_zero, List.eraseIdx_cons_succ,
        List.eraseIdx_cons_zero])
      (DropKit.takeFive_sum_le d w a b c rest (by dsimp only [S]; omega))
  have r3 : WordR main (rollP 4) (fun vs => vs = c :: d :: w :: a :: b :: rest)
      (fun _ out => out = b :: c :: d :: w :: a :: rest) (fun _ => Dr) :=
    DropKit.rollStep4 (hroll main) (c :: d :: w :: a :: b :: rest)
      (b :: c :: d :: w :: a :: rest) (by simp only [List.length_cons]; omega)
      (by simp only [List.getD_cons_succ, List.getD_cons_zero, List.eraseIdx_cons_succ,
        List.eraseIdx_cons_zero])
      (DropKit.takeFive_sum_le c d w a b rest (by dsimp only [S]; omega))
  have r4 : WordR main (rollP 4) (fun vs => vs = b :: c :: d :: w :: a :: rest)
      (fun _ out => out = a :: b :: c :: d :: w :: rest) (fun _ => Dr) :=
    DropKit.rollStep4 (hroll main) (b :: c :: d :: w :: a :: rest)
      (a :: b :: c :: d :: w :: rest) (by simp only [List.length_cons]; omega)
      (by simp only [List.getD_cons_succ, List.getD_cons_zero, List.eraseIdx_cons_succ,
        List.eraseIdx_cons_zero])
      (DropKit.takeFive_sum_le b c d w a rest (by dsimp only [S]; omega))
  -- ### the four `drop`s removing `a, b, c, d`
  have e1 : WordR main dropP (fun vs => vs = a :: b :: c :: d :: w :: rest)
      (fun _ out => out = b :: c :: d :: w :: rest) (fun _ => Dd) :=
    DropKit.dropStep' (hdrop main) a (b :: c :: d :: w :: rest) (by dsimp only [S]; omega)
  have e2 : WordR main dropP (fun vs => vs = b :: c :: d :: w :: rest)
      (fun _ out => out = c :: d :: w :: rest) (fun _ => Dd) :=
    DropKit.dropStep' (hdrop main) b (c :: d :: w :: rest) (by dsimp only [S]; omega)
  have e3 : WordR main dropP (fun vs => vs = c :: d :: w :: rest)
      (fun _ out => out = d :: w :: rest) (fun _ => Dd) :=
    DropKit.dropStep' (hdrop main) c (d :: w :: rest) (by dsimp only [S]; omega)
  have e4 : WordR main dropP (fun vs => vs = d :: w :: rest)
      (fun _ out => out = w :: rest) (fun _ => Dd) :=
    DropKit.dropStep' (hdrop main) d (w :: rest) (by dsimp only [S]; omega)
  -- ### assembly (right-associated, so that the program is the literal
  -- `rollP 4 ;;; rollP 4 ;;; rollP 4 ;;; rollP 4 ;;; dropP ;;; dropP ;;; dropP ;;; dropP`)
  have e34 := MrgKit.WordR_seqC e3 e4
  have e234 := MrgKit.WordR_seqC e2 e34
  have e1234 := MrgKit.WordR_seqC e1 e234
  have re4 := MrgKit.WordR_seqC r4 e1234
  have re3 := MrgKit.WordR_seqC r3 re4
  have re2 := MrgKit.WordR_seqC r2 re3
  have hall := MrgKit.WordR_seqC r1 re2
  refine MrgKit.WordR_weaken hall ?_ ?_ ?_
  · intro vs hvs
    rw [hvs]
  · intro vs out _ hout
    exact hout
  · intro vs _
    -- the total cost bound
    have heq : vsz w + vsz (intList ts) + isz sgn + isz (r : ℤ) + isz (p : ℤ) + 5 = S + 5 := by
      dsimp only [S, a, b, c, d]
      simp only [MrgKit.vsz_int']
    rw [heq]
    have h1 : Dr + (Dr + (Dr + (Dr + (Dd + (Dd + (Dd + Dd)))))) ≤ 4 * Dr + 4 * Dd := by omega
    have h2 : 4 * Dr + 4 * Dd = (20 * Kr + 4 * Kd) * (S + 1) := by
      dsimp only [Dr, Dd]; ring
    have h3 : (20 * Kr + 4 * Kd) * (S + 1) ≤ (20 * Kr + 4 * Kd) * (S + 5) :=
      Nat.mul_le_mul_left _ (by omega)
    calc Dr + (Dr + (Dr + (Dr + (Dd + (Dd + (Dd + Dd))))))
        ≤ 4 * Dr + 4 * Dd := h1
      _ = (20 * Kr + 4 * Kd) * (S + 1) := h2
      _ ≤ (20 * Kr + 4 * Kd) * (S + 5) := h3

end Work.SynFFT
