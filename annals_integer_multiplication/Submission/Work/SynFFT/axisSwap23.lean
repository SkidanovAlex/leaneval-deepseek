import Mathlib
import Submission.Work.SynFFT.kit2
import Submission.Work.SynFFT.mrgBlkDefs

namespace Work.SynFFT

open HvdH

/-- Swapping the two values in positions 2 and 3 of the value stack
(`X a b c rest ↦ X a c b rest`) by the three rolls `roll 3`, `roll 2`, `roll 2`. -/
theorem axisSwap23 (hk : Work.SynFFT.KLib) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (X a b c : HvdH.Val) (rest : List HvdH.Val),
      HvdH.WordR main prog
        (fun vs => vs = X :: a :: b :: c :: rest)
        (fun _ out => out = X :: a :: c :: b :: rest)
        (fun vs => K * (HvdH.vsz X + HvdH.vsz a + HvdH.vsz b + HvdH.vsz c + 1)) := by
  obtain ⟨roll, Kr, hroll⟩ := hk.roll
  refine ⟨HvdH.Cmd.seq (HvdH.Cmd.seq (roll 3) (roll 2)) (roll 2), 10 * Kr, ?_⟩
  intro main X a b c rest
  have h1 : HvdH.WordR main (roll 3)
      (fun vs => vs = X :: a :: b :: c :: rest)
      (fun _ out => out = c :: X :: a :: b :: rest)
      (fun _ => 4 * Kr * (HvdH.vsz X + HvdH.vsz a + HvdH.vsz b + HvdH.vsz c + 1)) :=
    Work.SynFFT.MrgKit.rollStep (main := main) (rollP := roll) (Kr := Kr) (hroll main) 3
      (X :: a :: b :: c :: rest) (by simp)
      (4 * Kr * (HvdH.vsz X + HvdH.vsz a + HvdH.vsz b + HvdH.vsz c + 1)) (by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        ring_nf
        omega)
  have h2 : HvdH.WordR main (roll 2)
      (fun vs => vs = c :: X :: a :: b :: rest)
      (fun _ out => out = a :: c :: X :: b :: rest)
      (fun _ => 3 * Kr * (HvdH.vsz X + HvdH.vsz a + HvdH.vsz b + HvdH.vsz c + 1)) :=
    Work.SynFFT.MrgKit.rollStep (main := main) (rollP := roll) (Kr := Kr) (hroll main) 2
      (c :: X :: a :: b :: rest) (by simp)
      (3 * Kr * (HvdH.vsz X + HvdH.vsz a + HvdH.vsz b + HvdH.vsz c + 1)) (by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        ring_nf
        omega)
  have h3 : HvdH.WordR main (roll 2)
      (fun vs => vs = a :: c :: X :: b :: rest)
      (fun _ out => out = X :: a :: c :: b :: rest)
      (fun _ => 3 * Kr * (HvdH.vsz X + HvdH.vsz a + HvdH.vsz b + HvdH.vsz c + 1)) :=
    Work.SynFFT.MrgKit.rollStep (main := main) (rollP := roll) (Kr := Kr) (hroll main) 2
      (a :: c :: X :: b :: rest) (by simp)
      (3 * Kr * (HvdH.vsz X + HvdH.vsz a + HvdH.vsz b + HvdH.vsz c + 1)) (by
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
        ring_nf
        omega)
  have h12 := Work.SynFFT.MrgKit.WordR_seqC h1 h2
  have h123 := Work.SynFFT.MrgKit.WordR_seqC h12 h3
  refine Work.SynFFT.MrgKit.WordR_weaken h123 (fun vs hvs => hvs) (fun vs out hvs hq => hq) ?_
  intro vs hvs
  ring_nf
  omega

end Work.SynFFT
