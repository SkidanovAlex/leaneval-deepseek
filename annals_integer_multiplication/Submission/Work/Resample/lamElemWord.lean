import Mathlib
import Submission.Work.Resample.lamElemPartA
import Submission.Work.Resample.lamElemPartB
import Submission.Work.Resample.lamElemPartC
import Submission.Work.Resample.lamElemPartD

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.Resample

open HvdH

/-- The `lamKey` element word: it splits `cons (int i) (int m)`, computes
`lamKey s t m i = lamF·lamL + (1-lamF)·(s+i)` and leaves `[int (lamKey s t m i), int s, int t]`. -/
theorem lamElemWord (KL : HvdH.KernelLib) (IL : HvdH.IntLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (s t m i : ℕ) (hst : s < t) (hm : m < t)
      (hi : i < t),
      ∀ rest : List HvdH.Val, HvdH.WordR main prog
        (fun vs => vs = [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) (HvdH.Val.int (m : ℤ)),
          HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)] ++ rest)
        (fun vs out => vs = [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) (HvdH.Val.int (m : ℤ)),
          HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)] ++ rest ∧
          out = [HvdH.Val.int (Work.Resample.lamKey (s : ℤ) (t : ℤ) (m : ℤ) (i : ℤ)),
            HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)] ++ rest)
        (fun _ => K * (HvdH.isz (i : ℤ) + HvdH.isz (m : ℤ) + HvdH.isz (s : ℤ)
          + HvdH.isz (t : ℤ) + 1) ^ K) := by
  obtain ⟨pA, KA, hA⟩ := Work.Resample.LamElem.lamElemPartA KL IL
  obtain ⟨pB, KB, hB⟩ := Work.Resample.LamElem.lamElemPartB KL IL
  obtain ⟨pC, KC, hC⟩ := lamElemPartC KL IL
  obtain ⟨pD, KD, hD⟩ := lamElemPartD KL IL
  refine ⟨Cmd.seq pA (Cmd.seq pB (Cmd.seq pC pD)), 10 * (KA + KB + KC + KD + 1), ?_⟩
  intro main s t m i hst hm hi
  have hW1 : 1 ≤ Work.Resample.LamElem.Wsz s t m i := by
    have h := Work.Resample.LamElem.Wsz_ge s t m i
    omega
  have hPA := hA main s t m i hst hm hi
  have hPB := hB main s t m i hst hm hi
  have hPC := hC main s t m i hst hm hi
  have hPD := hD main s t m i hst hm hi
  have hcomp := Pipe.comp hPA (Pipe.comp hPB (Pipe.comp hPC hPD))
  have hcost := Work.Resample.LamElem.cost_combine (KA := KA) (KB := KB) (KC := KC) (KD := KD)
    (W := Work.Resample.LamElem.Wsz s t m i) hW1
  have hV0 : Work.Resample.LamElem.V0 s t m i
      = [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) (HvdH.Val.int (m : ℤ)),
          HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)] := by
    simp only [Work.Resample.LamElem.V0, Work.Resample.LamElem.vPair,
      Work.Resample.LamElem.vS, Work.Resample.LamElem.vT, Work.Resample.LamElem.wS,
      Work.Resample.LamElem.wT]
  have hV52 : Work.Resample.LamElem.V52 s t m i
      = [HvdH.Val.int (Work.Resample.lamKey (s : ℤ) (t : ℤ) (m : ℤ) (i : ℤ)),
          HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)] := by
    simp only [Work.Resample.LamElem.V52, Work.Resample.LamElem.vK0,
      Work.Resample.LamElem.vS, Work.Resample.LamElem.vT, Work.Resample.LamElem.wS,
      Work.Resample.LamElem.wT, Work.Resample.LamElem.wK0_eq_lamKey]
  intro rest
  have hW := hcomp rest
  refine KL.conseq main (Cmd.seq pA (Cmd.seq pB (Cmd.seq pC pD)))
    (fun vs => vs = Work.Resample.LamElem.V0 s t m i ++ rest)
    (fun vs => vs = [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) (HvdH.Val.int (m : ℤ)),
      HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)] ++ rest)
    (fun _ out => out = Work.Resample.LamElem.V52 s t m i ++ rest)
    (fun vs out => vs = [HvdH.Val.cons (HvdH.Val.int (i : ℤ)) (HvdH.Val.int (m : ℤ)),
      HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)] ++ rest ∧
      out = [HvdH.Val.int (Work.Resample.lamKey (s : ℤ) (t : ℤ) (m : ℤ) (i : ℤ)),
        HvdH.Val.int (s : ℤ), HvdH.Val.int (t : ℤ)] ++ rest)
    (fun _ => KA * Work.Resample.LamElem.Wsz s t m i ^ KA
      + (KB * Work.Resample.LamElem.Wsz s t m i ^ KB
        + (KC * Work.Resample.LamElem.Wsz s t m i ^ KC
          + KD * Work.Resample.LamElem.Wsz s t m i ^ KD)))
    (fun _ => 10 * (KA + KB + KC + KD + 1) * Work.Resample.LamElem.Wsz s t m i
      ^ (10 * (KA + KB + KC + KD + 1)))
    hW ?_ ?_ ?_
  · intro vs hvs
    simp only [hvs, hV0]
  · intro vs out hvs hpost
    refine ⟨?_, ?_⟩
    · simp only [hvs, hV0]
    · simp only [hpost, hV52]
  · intro vs _
    exact hcost

end Work.Resample
