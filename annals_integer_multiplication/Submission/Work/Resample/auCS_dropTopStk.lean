import Mathlib
import Submission.Work.Resample.pbDefs
import Submission.Work.Resample.auRoundAux
import Submission.Work.Kernel.dropValue

namespace Work.Resample

open HvdH

/-- Drop the top value `v` from a non-zero stack `src`, leaving its tail `L` in place and restoring
every other stack (in particular the value stack `0`).

Program: `auRoundPop src` moves `v` from `src` onto stack `0` (cost `Kc * (vsz v + 1)`), then
`Work.Kernel.dropValue` removes the top value of stack `0` again (cost `Kd * (vsz v + 1)`). -/
theorem auCS_dropTopStk (src : HvdH.Stk) (hsrc : src ≠ 0) :
    ∃ (prog : HvdH.Cmd) (K : ℕ), ∀ (main : HvdH.Cmd) (v : HvdH.Val) (L rest : List HvdH.Val),
      Work.Resample.WordM main prog
        (fun vs a => vs = rest ∧ a src = v :: L)
        (fun vs a out b => out = rest ∧ b src = L ∧ (∀ j, j ≠ 0 → j ≠ src → b j = a j))
        (fun _ _ => K * (HvdH.vsz v + 1)) := by
  obtain ⟨pdrop, Kd, hdrop⟩ := Work.Kernel.dropValue
  obtain ⟨ppop, Kpop, hpop⟩ := auRoundPop src hsrc
  refine ⟨HvdH.Cmd.seq ppop pdrop, Kpop + Kd, ?_⟩
  intro main v L rest
  have h₁ : WordM main ppop
      (fun vs a => vs = rest ∧ a src = v :: L)
      (fun vs a out b => out = v :: vs ∧ b src = L ∧
        (∀ j, j ≠ 0 → j ≠ src → b j = a j))
      (fun _ _ => Kpop * (HvdH.vsz v + 1)) := hpop main v L rest
  have h₂ : WordM main pdrop
      (fun vs (_ : HvdH.Stk → List HvdH.Val) => vs ≠ [])
      (fun vs a out b =>
        (∃ (u : HvdH.Val) (rs : List HvdH.Val), vs = u :: rs ∧ out = rs) ∧ b = a)
      (fun vs _ => Kd * (HvdH.vsz (vs.headD HvdH.Val.nil) + 1)) :=
    WordM.ofWordR (hdrop main)
  have hseq := WordM.seq (B := fun _ _ => Kd * (HvdH.vsz v + 1)) h₁ h₂ ?_ ?_
  · refine WordM.conseq hseq (fun vs a h => h) ?_ ?_
    · intro vs a out b hPre hPost
      obtain ⟨hvs, -⟩ := hPre
      obtain ⟨mid, a', hP₁, hP₂⟩ := hPost
      obtain ⟨hmid, ha'src, ha'agree⟩ := hP₁
      obtain ⟨⟨u, rs, hmid', hout⟩, hba'⟩ := hP₂
      subst hba'
      have hinj : u :: rs = v :: vs := by rw [← hmid', hmid]
      have hrs : rs = vs := (List.cons.inj hinj).2
      exact ⟨by rw [hout, hrs, hvs], ha'src,
        fun j hj0 hjs => ha'agree j hj0 hjs⟩
    · intro vs a hPre
      exact le_of_eq (Nat.add_mul Kpop Kd (HvdH.vsz v + 1)).symm
  · intro vs a mid a' hP₁
    obtain ⟨hmid, -, -⟩ := hP₁
    rw [hmid]
    simp
  · intro vs a mid a' hP₁
    obtain ⟨hmid, -, -⟩ := hP₁
    rw [hmid]
    simp

end Work.Resample
