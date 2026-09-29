import Mathlib
import Submission.Work.Resample.paDefs
import Submission.Work.Resample.paWords
import Submission.Work.Resample.paProofs1
import Submission.Work.Layout.dropVal_ev
import Submission.Work.ConvR.basic
import Submission.Work.Resample.pbClr
import Submission.Work.IntLib.Shift.Base
import Submission.Work.Resample.paKillD
import Submission.Work.Resample.paTapD
import Submission.Work.Resample.paFinalSizes

/-!
# Epilogue of the `Ã` program (`Work.Resample.paFinalD`)

This file assembles the delegated pieces `Work.Resample.paKillD` (drain the five auxiliary stacks),
`Work.Resample.paTapD` (park the array, drop the marker and bring the array back) and
`Work.Resample.paFinalSizes` (the arithmetic comparison against `PAFinalBr`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-- Consequence rule for `WordPe` (mirror of `WordP.conseq`); named `paWordPe_conseq` to avoid clashing
with the sibling modules of the area. -/
theorem paWordPe_conseq {main p : Cmd}
    {Pre : List Val → List Val → (Stk → List Val) → Prop}
    {Post : List Val → List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {C : List Val → List Val → (Stk → List Val) → ℕ}
    {Pre' : List Val → List Val → (Stk → List Val) → Prop}
    {Post' : List Val → List Val → (Stk → List Val) → List Val → (Stk → List Val) → Prop}
    {C' : List Val → List Val → (Stk → List Val) → ℕ}
    (h : WordPe main p Pre Post C) (h1 : ∀ vs rest a, Pre' vs rest a → Pre vs rest a)
    (h2 : ∀ vs rest a out b, Pre' vs rest a → Post vs rest a out b → Post' vs rest a out b)
    (h3 : ∀ vs rest a, Pre' vs rest a → C vs rest a ≤ C' vs rest a) :
    WordPe main p Pre' Post' C' := by
  intro vs rest a hPre s R0 Bg h0 hk
  obtain ⟨out, b, s', n, hPost, hev, hc, h0', hk'⟩ :=
    h vs rest a (h1 vs rest a hPre) s R0 Bg h0 hk
  exact ⟨out, b, s', n, h2 vs rest a out b hPre hPost, hev, le_trans hc (h3 vs rest a hPre),
    h0', hk'⟩

/-! ## The epilogue -/

/-- **Epilogue of the `Ã` program.**  From the end-of-loop invariant `PAInv … D` (stack 0 holds
`cvecVal (axisIter ss ts Φ D zs0)` above the marker): park the array on stack 1 (`paW2 1`), empty
the five auxiliary stacks 2–6 (move each value onto stack 0 with `Work.Resample.paW1 k` and drop it
with `Work.Layout.dropVal 0 c d`, whose `Ev`-level spec is `Work.Layout.dropVal_ev`), remove the
marker with `Work.IntLib.Shift.clearAll 0` (the region above the marker is by then empty, so this
costs 9), and move the array back onto stack 0 with `paW1 1`.  The result is exactly the value stack
`cvecVal (axisIter ss ts Φ D zs0) :: rest` with every other stack restored (all `b k = []` for
`k ≠ 0`); the size bound `vsz arr ≤ ts.prod * (2*p+8) + ts.prod + 1` is `PAVec`'s fourth conjunct
and the sizes of the drained values are bounded by `Work.ConvR.vsz_intList`/`paDefault`.  The
conclusion is the *marker-removing* triple `WordPe` (not `WordP`). -/
theorem paFinalD :
    ∃ (fin : HvdH.Cmd) (Kc : ℕ),
      ∀ (main : HvdH.Cmd) (p α : ℕ) (ss ts : List ℕ)
        (Φ : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ))
        (zs0 : List (ℤ × ℤ)),
      HvdH.ResParams p α ss ts →
      Work.Resample.WordPe main fin
        (Work.Resample.PAInv p α ss ts Φ zs0 HvdH.D)
        (fun vs rest a out b =>
          out = [HvdH.cvecVal (Work.Resample.axisIter ss ts Φ HvdH.D zs0)] ∧
          (∀ k : HvdH.Stk, k ≠ 0 → b k = []))
        (fun _ _ _ => Kc * Work.Resample.PAFinalBr p ss ts) := by
  obtain ⟨kill, Kf, hkill⟩ := paKillD
  obtain ⟨tap, Kt, htap⟩ := paTapD
  refine ⟨HvdH.Cmd.seq kill tap, 8 * Kf + Kt, ?_⟩
  intro main p α ss ts Φ zs0 hres
  obtain ⟨hsize1, hsize2⟩ :=
    paFinalSizes p α ss ts hres.2.2.2.2.1 hres.1 hres.2.1
  -- ### the five drains
  have hpart1 : WordP main kill (PAInv p α ss ts Φ zs0 HvdH.D)
      (fun vs rest a out b => ∃ arr, PAVec p ss ts Φ zs0 HvdH.D arr ∧ out = [arr] ∧
        (∀ k : Stk, k ≠ 0 → b k = []))
      (fun _ _ _ => Kf * (8 * PAFinalBr p ss ts)) := by
    refine WordP.conseq (WordP.ofWordM (hkill main p α ss ts)) ?_ ?_ ?_
    · rintro vs rest a ⟨arr, hvec, hvs, h1, h2, h3, h4, h5, h6, hrest⟩
      exact ⟨h2, h3, h4, h5, h6, hrest⟩
    · rintro vs rest a out b ⟨arr, hvec, hvs, h1, h2, h3, h4, h5, h6, hrest⟩ ⟨hout, hb⟩
      exact ⟨arr, hvec, by rw [hout, hvs], hb⟩
    · intro vs rest a _
      exact Nat.mul_le_mul_left _ hsize2
  -- ### park, clear the marker, unpark
  have hpart2 : WordPe main tap
      (fun vs rest a => ∃ arr, PAVec p ss ts Φ zs0 HvdH.D arr ∧ vs = [arr] ∧
        (∀ k : Stk, k ≠ 0 → a k = []))
      (fun vs rest a out b => out = [cvecVal (axisIter ss ts Φ HvdH.D zs0)] ∧
        (∀ k : Stk, k ≠ 0 → b k = []))
      (fun _ _ _ => Kt * PAFinalBr p ss ts) := by
    refine paWordPe_conseq (htap main) ?_ ?_ ?_
    · intro vs rest a hpre
      obtain ⟨arr, hvec, hvs, ha⟩ := hpre
      exact ⟨arr, hvs, ha⟩
    · intro vs rest a out b hpre hpost
      obtain ⟨arr, hvec, hvs, ha⟩ := hpre
      obtain ⟨arr', hvs', hout, hb⟩ := hpost
      have harr : arr' = arr := by simpa using hvs'.symm.trans hvs
      exact ⟨by rw [hout, harr, hvec.1], hb⟩
    · intro vs rest a hpre
      obtain ⟨arr, hvec, hvs, ha⟩ := hpre
      have h : vs.headD Val.nil = arr := by rw [hvs]; rfl
      rw [h]
      refine Nat.mul_le_mul_left _ (le_trans ?_ hsize1)
      have := hvec.2.2.2
      omega
  -- ### the epilogue
  refine paWordPe_conseq
    (WordP.seq_e (B := fun _ _ _ => Kt * PAFinalBr p ss ts) hpart1 hpart2 ?_ ?_) ?_ ?_ ?_
  · intro vs rest a mid a' hpost
    exact hpost
  · intro vs rest a mid a' hpost
    exact le_rfl
  · intro vs rest a hpre
    exact hpre
  · intro vs rest a out b hpre hpost
    obtain ⟨mid, a', -, h⟩ := hpost
    exact h
  · intro vs rest a hpre
    exact le_of_eq (by ring)

end Work.Resample
